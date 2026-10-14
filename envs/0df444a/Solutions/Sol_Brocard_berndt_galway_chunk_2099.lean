-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2099
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:39:03.053818+00:00
-- url     : https://prove2.me/submissions/731e7753-88e5-4d81-8dbb-a8aac8043de0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 377338129 ≤ n < 377517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 377339379 1250 377338129 377338133
    0x10c080a0509060313140102090d03050904150b04030c1508040308040203070312031a030f0601050603040c0905010929060405060d02070803070e10080f0a0c020c04060b040f060503010503030414030a050109 90
    0x500e41d02d0117402e8440064100d07401003945030502c03c8800c40d52016114112217030803901d003904c680d00440b03201c6c0d401607104c89150312160000f507070700c002a0003180c1c0040c1d1502d045090401c080300003900300710321501700d00d1503500d1401d4116003c40d5005a1501e4680756035907481c40403c0c1800a0385e80014100000c4884109484d605600070340c4980179002c002454074030a03802010303616100d13002c45d00826045940148850f0070000c0046034068094116a201c5542d42c8401030b0403544241e1225040c9a81c40c1c1642408881010454040045080c07640c4a6080c040001603060322883c850148202c1000420921201054043e540480d4009422645a18200c40c0240004880c0d03640d5900c54998000c800800c2030003240c103640180640c0400402c240d49a80c00c820060060321408400d510030740582007880d50b1680200400f5001003030707640b611640b03040890b110403481600315105229051006014039140001618211b90910030351103049045200441d0074500e00060103000340d4204440e13902 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 377340629 1250 377339379 377339401
    0x212010204061d0a06030b012003030709060513060e0a0302210c0a0b0307121d1507020d05070b100b03011706010e04050307260a020105160e010c080a05090603 70
    0x4200c803000e0312180d8483c00f03841d00701e8100c00d02c840d0320b16901111680701442824802d0707000e608010b0040c149081004104240d641d01c010040e21110302c1ca074000000c0125240c1d0104440c8014038a5040413410010128000342c654800d60144608014000903c04050343d5842c0c1c5c40340003580c001e450040180800380d10212403c00120020140384610288c025003405c0002c40c0c9001c51304a0700d0705c0d50440d26248001c5403810800d84081d40703400d80322889110164040b45000a0303c8091800412510800c0c14202c0043e0900928010941d0082c140102450760040100d450080d44103480381c03030a03031b201f0054402d02a4207402c000c1038980080004a44c2d0f10030990300ba00681062000c40b0311581e80c6001c120f0f055181110000c1142d00107028540010f050300002d00c1e0810445450700350184248000c6540300c1d0850100200140c4d11003040c45800d9a10002094000d0500d2410003010f0b0301502c000380910281c000024518100022150580c070721a00690f0b42050700104031640c1e17030400200c440 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 377341879 1250 377340629 377340637
    0x2102041b121104060807051e0a080702010c030507051614120d0f0513120c150b04060e0702070e13050d050d1a1c050309061207080702011e020a050702120102 69
    0x840c0c210310300003102c49080c03102400c1c0e8048460356980c10100c2d0381d581c001140c19420100d41065415107040940030951715540180545040c0f540d500f0300103141c40c101c02802c1d18004520340080c54940414041c44079401411100085410004800010440c1c0340c141c00c141165800300a81e805903050608040c0c9840008040d00b003280c06060000c5020b0000b070300110350702624503211031415840400001481966111101c0328141484140041d45807605a482800d40d171030341615030b40d00c0403030074510302d490700c00d85020f000b0a407200e4086142410300a903841d4410f0182d040301c07242c41000203240d41640e0400d80e8240794003d007610300c620300780c82c4090321581000c0b0000d52540c0c00c00c43d0742d41004104015145800c04010201c460100051020b03c90301c4844503000e80b6980010801c415440d1100c00041c03c0c1c80d03030140d244103024640010020312002c0040c0c403400171641081450102c4514842910382c2800c0302c0740700103950f10459201aa490300c110f940c000d4100c1a203210074440c00340198050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 377343129 1250 377341879 377341907
    0x19080d031d060f042d1e0210030e0111040e040f0f050a03090306060806090d0f0c0b0103201203030103061a09041505090f070b0f040e0c04050112062102041b 69
    0x514607085d41900740000891004001111061241c8046012881e4001442d8042c1e00c04c510504203084250041545401540c0d69400030a03103500140d1681542440380c01212210031904506090800c4514550300314040c1000d04000362281c100c00c10700c004c6090307400260750b00404036440d0054610300a004078015110030b0321068500000051081c038081030703191040300210083c0208049844096170300100000c1c40c60208032203101c2c000c0004905111281c041c5014078410301002e40c1e5004003174060300d807074241580685040c460615441a000050300c3c190b0b0f90018012640e218021035000c14108201805a4016290700c03d0200780802c410311449800c1e0029418480f590381c05020f1079071489040b118100765030045504014450140000d4000c0106a4800910749562071502601c840b8055401c2c28401500280810007036801011220714184520b40a00c00c0914040818001d800f46206007140c0e1401070721000219074403540a0318181d107164903088440e40f40c00e4401017101c0070315110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 377344379 1250 377343129 377343143
    0x6190801050a0c0c081e09150717090d0f080d0f09050601080601050d0312060306020c2a1c1407080c0a0806090c010f02071a0919080d031d060f04 64
    0x2c41d00c03c1070b02c079000c100b0400b50005080e5140c40383d00414001030b0803040c889a01e141c02c040c440800a030b56864074043ca00c03566012000e03242e4425040c140c24040242d00c401c001ca0f04100701c0401aa04c810400b188425006200084078084500b068000e52041d0341c0f00a280602d403003024070320030390f4951041091501070400c035643d0360b0700c1c0c564566aa980038082e0550003640003500350700103407140010384482d110341d20001c00c1e510ba881d40d40000740d03044904018a250054000c1d03019140700c42040300c000c403005080c580300ca1021000802c403001c80c0e103200210510940b020038130500c0b0041808040880300d01c0116041d03145e903030850503103984004055500c91680303900f0005070541d00142aa01511492024080c1d40700004015150004000110f81c15401040400590b0034034203000d0f40c405120030f041a07a03441045108000442112030610410091002c03003e100803840000d4012004525044c00112040c42d5200004000c031348007884e84440c41007004000c100360500e20260300603442811 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 377345629 1250 377344379 377344391
    0x304080c10110910091d01080d0815060a2c13020c0615120a05031201080307030909150b041401110307050d08040602070618140102070302060c0306190801050a 70
    0x41c03000162005001104540c2200b48424210307882d010010b184184001d080207041c60399946007403801e0314120200c011000045000410801d0424001075020001c5d0340303802e210038a4031a00c01560fa80ca0240754038000c0c9c5012804218217401038458402c0032400d0010aa016001203800100c4088e0a8a00c203000754070a40b61700b285110b0368026180d007011740d80003400580d035410030031100300740c240d580b0305902c04800340e441d92038100e061141d800c0203801400910380c0d034052142034800644041e440b00d070044e44104038050100740d00007a06030135180719030408180c210b400c00c00f0809041d4190803021146400190000d42d034114112400307400039087c2c07107034079902100201050b03c0f805403c00c060401d401c42d04c07071101003c0c80380900c190720500c600d10050070841c4940b1440100c6807034a040700804c00b62510f82d041413041c0d0003803112b04c1c2010400203618100d5a503800079151040601299220a0007001007155a612514200803401148881c08045030f030f81e40c0d805000e440199000c080c0545000d0b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 377346879 1250 377345629 377345653
    0x1120803161715030f2b09050d030305010f06080601021b0312120f0f041208070519030504050f0f03040b03090c032a09010b0a1b02091801050c040f051003020c030304080c 75
    0x41805120940c0c01070f403844641b5044260201110070040100f410014a100042115911200b11a501e6406982c3c0000d0660404e08540e9841c6c40e950400d900b4003036048104083c0760384c0000d0114103e414a80402c3e04022882c012034901411010820800c0201241000061045540c6148950304002120045443e407082950b59054241d40141c14100105528080d40303000d00401600700c2480d00e0440e10704400c00000d8a0100340340042140000c2d2201c00340b0061150401401e5a90454400034086130014001e20f295070388164401e520001c0804000258507040c00d11501c404100c002e81999400c107401d42500b00342011900c1c0c200c0402d501c7ca008182c050425001440c1618840c4035078510b44007407e402a10005211800004980d1015500c0070043e1121003180d40180d05140701d030315188120a00c0b0b0b5080d548010301c040d041c0c00b0b01b03004c10450b03d01035160441c11034400395494500c44c050500200d01034440d564044100d84400020711040110710001800951070020682c3c0c11002c01e1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 377348129 1250 377346879 377346883
    0x706060515070803100308040e070809060606090409020d0c0801020c060a060501020a0f14010c081503060405060c130e0705070c0b120103030302090d1406090601120803161715030f 79
    0x1d80182580c0300600c50301c40080c0c00d03940150340020048014070302c83c2d542c9a403803005c10350258000c0c58850b40e8010602c41c1940d000043c480d00135400c40082c210300c0c60202c01081c881c1c0100d10117a446541c64000c22020354076032082c14a5026000300da100105d50f220700c2060301075800441004843d100f120005011000030780b007200c0540f5816405080340c4a4282c6490030060b800400940c0d040c514189108100300e030900c81c0350143d4036589c6a034105490301c031141090b200c503418031480c002d41240040000151012480c10360000000404540301d0054500c0c6284034940e541104081f42c0010007481000c43e0028080c02a032845024610380d03564507403000791168001c3d85039080e80001d003e001800041d000750058681c904020307040480710074964480c41c070480b614607030410254020f08180520700400707200050150104441720802c41d030a903650703d03500307200003459605598040140c1c0210507114410315041c90021110601040c2405c22903010798003100e8400c10b00c00e1181e801550100303940 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 377349379 1250 377348129 377348149
    0xd0f050c060411040e0a03090806070e1507030507021008042906150d02120117030313120909060b0307020105010906060e400b03010624180b07060605 66
    0x10300019003595166543e91100f1141c0c401d0f25180d0140c0c0b50940e03841c155104205241c5400c0c0203a54a0306510720b011100380c140080600110208460300d5107a040540701c03000002501e40030fa014041c0d4800c1d090904943d68044c90600030751081580c0941c03022258081002400740d4050440615465041d01c41030070020214410510440341e100e000a00a160400c00645402a2109068a040d00d0180700d6170881c2e01180701a0060486600140450300d1034451820a001c403030700045140d03060004001c0344a682d0000001c103074403250b440304d01140d0f100b01c115000404100d00140025500c0762504021900304031042c000640c40c000002a81248602418045901c240c841555070700d86c060030b0005421000841c40c1d01544928208500304041e03405d8212440c07420050340b10b001146542c07840030744180c8910310b4030030f0303040c498148071041c40c2d42c0d113603007009814002d80c0c61751004034007050b00c4042d0103546400009409440008010800340018154036109503c1000b4090300c0f081045402c0d95 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 377350629 1250 377349379 377349397
    0x306050603030715050601020c0604061215080309061b0a03050703030b01020d09150c150509071406030601050304060b12010b0112060308040e04030216060f08070201290418050d0f05 80
    0x403104506840d04c400715030203590041c40610550300c004040502042196005600510010301032403412a1107071043e01c0380b440341510210700800220729143c40c00742c1e43c1c007440407060711514000441344640306101070041310b20b020840c01c0d41d204000605025140782c001c07140650210341000c40b00f400e2507101003100340407550280c031a880920704018090080d840d04018480501012032034013008502c1850716440a505101d00120700e038a44a048075040c24042d503c160418410408d5410343d950310740b01501c0e0301c104203281464499481d03080500207080729441ca02e8000c3d8219005040d28401034024080c501b50a1300c0d240388481002501c1c0c4200c0d003151102426156040c0014000700e400103840a07000790007441120b441c5030025020071000c0380c0360781c8100d01186c641c002618440303030441c0c242d60303205950b80020071130410f004025481c501d001112030300c070072240020540c24a554607070005400e4088940c1a0003541c0c10f038500990b5070200481403c0100c2d002d84600d00c0d980344501c080300c42d601 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 377351879 1250 377350629 377350643
    0x602031f03080711090f010608090f03070c03110105030c0d0b040f0e07061103040305060a091a0f01080732012303010f090b030307120c300207120807020315010e0103060506030307 79
    0x207880c0903c2203540c0e840c0580014a240203040305010042010005050070b0742c0607503123b400b441d01e18640780c10401c40c0204031506100d010710800030010202803e0740d446940d0300c1c0c40880c0c1c1c080c04400040c0103085070714003010280d182200070001103100058045c02c3d030310030b03460751f05003004403078040b0b80e403030145100040c05944814001074801c0f003d40c00060003140710b0b03480e4046003464100500011541110038080004104004010546007000b42c080140540d8048074018003410b404603041521520030301d00401840c19403243e00e039200b01c0c105081401401500d114070000074501c41100d03071080c4140a19116990000306442c04907104d20740c00240d00500541c6070048d180c0d152000814103030b40b1003090203142e03804500802c544801c99000d429071f406d40c8006482a4641d006a640c900310071090440d80a0b02c02880741c80041d00d0090405a0400840ea80b10300c8180300092419070030842e141d1600c06050300000703c03000084400c03416640b280200740469914007091643d60701845001900b50 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 377353129 1250 377351879 377351881
    0x30906070315060e0607060513112e120c020705130e150a091e0203011409030306011809061d0106020c01080c0c011803020d02280602031f03080711090f 67
    0xf1900400b40b1310010380c00942203505000460f1030310411240101c905201d23017080d104101d010040a900e1208089104840140e21200d100031506003c40b8165043e01a10722091109005203000e811050821440413034103001075070031120000d444445921500303000702082c1424041c1da80311401a80b009403001c4000340303641c13248060002580c080c090200e501c0d00f03036121101e502103800c080300490700800c00031052002c8034031441410300711610302c030856032094503080c14410030395804030490341c1050702440c4c0f0809805081061001400880c1e0004040c1e61034250005003580458031914500c2511201c00d1046aa90748000d070b8442170011100c50000d0700c100009210b0300d4ac03180c003400302050b4090000400c1c50340d0786031082c1241000c101c1034001d0b0b131103002203846943d8100300154050103a440d031929a426481c20088003984007170b034000d05c550b40202c0003038032000b802060070580d07140d6800b0080711a80d0340d00344219603911000c429a0201f640901008642c102a04501d001c5c210f810744282107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 377354379 1250 377353129 377353139
    0xf0703020304022b0c050f010903080904061d01030204200910090504020318010b01111c0225080705040c050d090302120c0c0f03150109150e040305030906070315 71
    0x75070004104a80c08141c60501e44c64488440c9141c00c41044192400ca044140c6030411115440442d030080e0700c101c000200142c0b0a0741e01400d0103045075070044c401070319103642c440010003034001c9811441804145080006404200303c2c0018100c1c0e0081e5410000d010442e84c00c040c14101c2c200482410050402c1800500d0074410b1a202032160140740015046071660009030507a4426074006007080346000301c84184074001c2c81000c0266209082c120417000862006a4a9004200f464412558000c00550310b05000b4071003002d2803500580e250300b150340a49585102c840541c05140400e10601c0b9010446e800e0130b1240c4420350a1580703605090220821901c8058202001c084085005490381010048012409031204031990800f60001d10342003001c0c00344e00821002004d11a910650701320101c491130b4043c49054404662001c10101140100380811030341c141d0044110308110380411041c564041d020f540102c0d0303c0c105842464032130010031020390300904151202a04c1c90300003045 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 377355629 1250 377354379 377354381
    0x40204030b15130509030711040614090c09060304200d08030c0a0905120c010e0307050f060d02040506030f04050f0601030503030106120f111201060309150c030f05160e090f0703 78
    0x280342d10002d00740e100d0788560101e0181602ea090780d4103070b21a81701142400811000440c0003003000c0003590308210061a05410101a01c4240045070007500048041400941a2001c036180e0301800b4000e00c4d601c2c1428940100407005482d280800701c1da01040607001494420f402d08a000e41080b00582035440789400442d040c1c1c02071103460180260150001020b466090040c4038102301240078118814141002500c0c0452500c0c003107200e0b41110800348450b943d100d0802c07409580c155842d549404001c60440028400c80d080310f58006004800c00c40703070301044520280300e10700c207109850305100c407040125921003084c0002042d40d00140010b00c46640700b1501040301001d454030103e880c6c94100b10b518111080e240c1c040c50702c484006108010a5420781002c0c2c014a11454200009100c0340c5411600031243d10f4070400c040c1d2030f4102c60386a80d109800921424801d11000c0040d410046c0c0305954488080e0440400314030103005980062500e0306409210f5805000d12048658640400f10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 377356879 1250 377355629 377355661
    0x30906040204240b0910020609070b0f04031704090608010e0a020603070212030405010c0e0d1e24090b012319030b0709180b0102031602120d0203090f040204030b 71
    0xf0340300c80340d52088014a60b4496851200901800b00c0c100c0c1c3c0c4001700c03001d01180350102c04103d01958464800d01080343d0300000e0a800300c80c80c142c446500c40d03c07003a44120540c4596400034285524994040601e40038010080045900c003d604000040c1da602446090302c2c100d00b481000380d0000d48450025080c400c00840d0321403901c1c81035030a0300c0300444481000381c00540c1d0549803a9501e0b5100031003160450044050b0403800c1f42e5400245140c0d40e038180c2130351103031800c070304005402c40e00301c400304240c1403e1030a0070700f650030000b003110080245003c01405a510150348900c480c000000d0500d412000410301d03080117a202d80d412849050034084c082c40f4036a4105104101d03003100001080c503c3e100c1c0d0740680c1d0340765180782010b8a40790070080301495400c450040e4915000b15104540c2e000021910030300c582442c8800c54a0603400050403854070b40150000d40e0080500903940113601100400c0c4c00c84003101d10b20b031804241000e1208034061400000d040c0d002031000701c0c0060010000760 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 377358129 1250 377356879 377356901
    0x8030a03051801090516080148030c12020315090c0706050c0406080108030406051b0c040e030a03050f280b03100902130c1d0118060e15030906040204 66
    0x10107541c203050000342e400c541c1c0d0484140d400340c001200a01004903c8080c02c0c0c010314004000f4002d1100380703605904600044060401c589103246d400c001c42d1103440004480c84c0030603414008181c0c0051001a016000b40080540051408100322180c4e62061096174040e4000d0b40241e03a0310143e020a0252030301000d4a90202c0b41c2060000ea000180140200342c411450300002d503031207c0c50001d01610036101030f041030b1002e410a00080c426251f00000b52000d11201e09205040045800e8490f41005000070f080d541103402e14007050001c14000006050303d54403645c081060303a9811a0500300340e0f00c140e0390314594901c0c91240d800d1801d44030060305113249400f003002a11090244c0044c0c038141d200304d40e15040b140c4414a14003580b50022400c02c400d0403882050240107a5140020700e840080d0910300080e01d540e419203103440c0d200d010711100400241c01400b20032525a48040c0c4075a00880c1e0082c414806400d451100d038024409480c0103408103c001d203c203071105d9080002130540c50500e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 377359379 1250 377358129 377358151
    0x1d03030601110c1507051203010812180a061d0411091017040c180218010f0c0209040809090601050c07090b1302030f04060b0109050102060609060a0b270a08030a0305 73
    0x5070f400907503a07030403052030983c150302142c0c2c1d840303903245040c5007800d10307620002c00b1109061004006800c004a07140c0c0c01d100a8800042e1741d100444000000701d2402d50180750016000240420001c0d08680041001c030f400804001c84001c0e2241040281c13010b81c0046c0b9603503c400d0100341e0b160308000001d0912400c0e41d080044c0b2428000c100c106103108129019034100c0c00310542000703103900c03074641f64044d03020900d010743c940400c0c2503c0c9146221001d40550400c00c0c40c2c0da06011052185106948160340100105036034201b9041042c25030700070040103446a12040d02040180d800791086501512144c0d02414003545441c1c01d00c3d00030b10340540203c0c2c00071501068185d28500301c3c8010f600c1041d03844000405030074103040c5130080f2121000003078107002c0c14500910081ea00085c2041e400b0008880c98055030303544601151000c0042d92200028010101c4c2c210071402980001c800703142d8400315005c0c04a0b400d10b0070000c08207180d201d1304856400810000030001c3c442d400156015a400c40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 377360629 1250 377359379 377359393
    0x50d020304061d0a02100c0803060d0c09090c05030c10120203100906090e070902040f05040f0f020c0717070b1206030f0f0102130f03020603192d1d0303060111 70
    0x1c0300340400e400103c02c01c01d1030300000200000c5143c0500c4180071284185002c0102e084070740da40310114032001c0c0542c6d100d007580f000c2440404c6107442c03045028000d49141030119130240e2805c201188002e00540d48680602c0d5000c07411810460342240100c2540e075501d40b040f105000490b0002d51003c3d040315101c0c01c003480c02080a0081c2c0c054440100088400014060104108542030004582004140074010441049084548401c41c41515000c40d0300003524404109104002c0c03403000f4480c2202d40c0040741c080d205290118950045500c0c00012108089900900580b69541400380201005042c0444800d14140480c083d500400203002c640d11912007a05c900c1c9001685192003045030740010340c69010100b0441200c000340440b5620090300c60550740042d81e64000103001d41e05407880d040340c032000d801c0035070031190841c008103501c007080d80355a40c007201a407046425040001800c140c886245000c4c01c0042c3c0d124000301901540c1562070b41d200440d920940d4998811369845818 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 377361879 1250 377360629 377360651
    0x1512041a0f01081e0309100201060e13030f080609160219120306090b030d05160c09020405010314100605130816030204060f0f0303140c0109050a02030106120201050d02030406 77
    0x2584040c000d02401840e401550b00d0281030528040048030035029002d1381c1c200c002801c0c0c50000a580c86183d0403540b0b4250b26a90410880c0102426400100303158034007014400c80c294280004000c050180da50a041030500480c15683c00d2020794900350411200c5000810b10482001d100b0b481d1282841a540c0010034100381d0070341046d840909582006103202c0328051650580724040040000000c1071020482881c0000d4075019162000c00911000091861907285185a070515076640109240c03c0c95403103003a00e4000b5080f500486010924012201003420f4400721902d204150046240310490b040c60012034071a00004141c10005000040c08550801c0034070071b199003415a04040031205245004110541d19190f00c060f1168810000600404500300303041e5094a402d803d050030852025040b011003486551034503a03d0754a404020001c200011034400005030080f0004e00c40c464031000c14021021054000034040b690412405402102c942c016603840b0340100000601c4c41004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 377363129 1250 377361879 377361923
    0x3030307020c040515010503040813030206040905091203010b09310504020f0105071703090a0b040f03030b03011a120a14060703111c0902040e010609020414151204 72
    0x3a184500560024030041045091611a10781d2001c45149184141c90b9080006070081c800500081e040c0c080001d034030888c0d00078a000700343c02940e014005955650f07452282000504017031f954501c943c0150004400300030b04081c1900c0c180c585031088603203051110b8042011841c841501150851010b50201403070200f8215110148a1200310118051400380b0401101d400f0008040e414004107003d0300020401d407020325160040080980380c3c1c5d035295907003e1480c0010305200103200405940412042110a0388030000040c82a2414001c00c010441054242c07152011030410303240f0164400c494600c2e160981c1004542404151030041100707031160003406002d0301030040c1d1580603a09108800d6458480d8688408021800301d09082c070058103140440903002c140d02c02e950b04c0d2800070065640d0b541c84829042c0e4460001c2014660b10342c569006504284030741c1404407e40200c5000c01e080006074000c442c045196442d01e00200e50b034852000290151095130f0f06000070700d0f04000700d800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 377364379 1250 377363129 377363131
    0x1006030b0f040e030405040506031c0f020a02040f0c0201050618060f0d020406030303060305100606090e061909061505040807030311100e01151e0611010b060d0204090506010503010f090b0f030303 86
    0x31543c0955a03590034403080c4402d888002d03003280c0c000e81c00141486280660079080d403508091500d0051507400c0c0301c960881c5804201440a07500c10b203403003984000c88c44240c0c0969040c1d45c05130001d021940d604801c11a40807c1c0c601ea0351009107802002608902c1c0940b0008000b00c0c004000c1e0360b210656401142c11141070b50011000302e943d0394002e0041c0031007001000059400c07150b0500409040410092214800e4031640c0c60341c240080100750350f40d84190b003070b806080408854429041d5034000d1000985454464402d4825801c486034143c2881402100c1c180c401d40c00003050f83e14615501103030108040481a5002c1c094000b8150103c2c02601460410484482c004500b05214070400303210034000e43e2246c041020f000704c400200c8400c0d01e842400702c407274500300101d903c50346a1245d4090001c180d1110351040c000101e01485105030350142090f65801b9004001668540006461911080c060300501160f005800c20100445400980b80000041c240d1403c00082e64007081c07450f04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 377365629 1250 377364379 377364401
    0x13011040e040b06151602060d02070506100501030603050c0f0d020306010f14040c080403030b0f1c21020a110103020d05040b0402031513020409110604060f0f081006030b0f04 77
    0x310072014003003400900c6a0751504024200c482240f50150902d0300300c402c0c461400d1155845149000c41010355a80030161140e000e030b82d44066594001030f150003038440404032a905554003000d4004a0654480e10070501529807080040c45202c41c041d040041702c00020340385a40c403001e1000c9220050700d01780b140c28024040c9000d00840182003900c2d1400340780546107a14002c501c1e241c540c88965500040380c40d009901070800040c81c12100010407a05407005407030a42110b0b02c14000c0880c07038050768041001d20300868240041940c1c8800586500800090200050348000d88c200c0102c2c2c408480e50a12071070504005103800d01d042d082405030b8070215021355510500c1001c10065007024403000c3c00036054409500d9107441c0c00f0314009918070500801034012580c400c008001c0168450104400c1800140401d803a10383c0c0710700c010030030f004402e40600000c40398606410742601403e1a54082c544042001010505001007200140311440c5200e610100d00e85600d20103454510440351118 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 377366879 1250 377365629 377365649
    0x3040302040c211a06090a17030409050c044505070f0f05041206140a05091b153109290409051513020103050601301104 53
    0x8036005003145001d22802074500402d50420300138002c4004d90340d001c0b46849204842107500da03540300010500d8954107800c41d440206842c4440502410004068411101030b81c50034801560380a02140490080c0d1090011301014141d542543d642011007004074415901220444851204013102003040c4940c51180401c1e034480510514503445100d2098200701c034181440f0400c6c480600501501c80c42c800c1502e03900035058600200300c030541180160380e000c0b01c1c01207403d00b000742461001f440f00386d4170707280b4a10a480515000040d1040344800001005181010828603c485464164422805001d1002080c005c501e40b83d9900003a081580c80c0e01d407504007c55052041e02d108503091490244088418040a601c107406400ca11051400713064802242601c41454a545807003e820660b5164102003c10440c8416194070504040b5000340d0702840640c881d6401568040001240103110450300200300250440c10003202c0c8103450350240c0040d0003c40c84858914540194010081c41 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 377368129 1250 377366879 377366897
    0x2031f06030c08131203020913050f22030c0303020306120115030203120f160503070b0a1a010306050904020111070b070302030c010b01030e0d031814011d012c03040302040c 76
    0x50f5030003469070341d011081540e100b52424040d00e03007501c0c0d0505003141c80c040540000301900320340c5070040b000c4100f1001c1d00041c4440e0400380a415082141110080c500c0d1050310300a045090009071003590558040d2520b404006a81d24100c019510090115070442c2d503050100c99070711424070400310750461203800f51002e5400c0d4410182000b000c078100e200d08402c2131151001c4404602d080703510340e0320303184068078240c6150f141181c20350040e4003001e40001c04004c100f00c3e0b40c7c02e454002c000c1c400c1c04403080480c0380c01c2c11001503007262118000c083d0006040000200154090980e0040301d045280454501c140e442c0e0046010b540089402c80050f000410b0384540800b003401100c281e03000908052109592080d2042e0341c81c5503000e003820416842d080c3c0c0e4801c10000b480040c140580003444079034003d4800746542d000c0c01c007a43d0b400f5008500404110760484041c4500d140101021302107008904003021044405440f0541020381070000300000030040c1c1c0d8512405410100e180c64012075 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 377369379 1250 377368129 377368151
    0x5031801030203090712020d0c0e040302070501020303040309060e0a0314031804091707060209030d09060806010e010912140a1a070507080d020c03070c03081e070c060302031f0603 79
    0x4081084100505050051060052030000441c00d00305980d0802804140340c0c480e4000a600d2000c0b120014202615030100806d003070114216845c4078074029000c448209982c0c200490703903440103c4000c0d0000b0055801444210b02c5541100c0782c80c03800a141d80046501c980303444100e042c007000f031010039500004004c0d04200c4400c440c5aa0008121000c0000c00c02544440300302c000340724000c50340c1003000030795001045498ac1c16200500000360480b08103181a100c007404240139400b980e03000c2040c0d400000ca20750b1041401102d005410795660b40a1890010840340300340c0d00344c80c02c881c0c800c3c2d0900b403c00707074079010450f410b1400e00440444003480c1014051100304030014002c0410045c0401512020450000440e405003207004030043c3d60302c01c00301c5914150b004940d00101511440200003041c0041c03034024007000d001c0015540d642250006282240388100c0000401c3c49121007420040c0d03a010b035010b0b55000719032150070b481c00b82d50f602d0045a50308550700f0440c00300342d40c1c0c2d41d0500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 377370629 1250 377369379 377369407
    0xb01061808010b0a0603050705070606291e0d02040b030a0f0612120c0c170a050f0d0c1e0f05010501081c12090c0b1809091504061a0604030503 63
    0x10042803090020080c2c9005840420a001300d940038990505480300049a400d0f4403030342c1100d04403074000b0410050380382c0f162101c21502240c00c81c4220980903402c4118481e992007002c0f5600e00206058002c01c0200c2040c1080b055005400300e00316065091100040e1044400001e40c0706030030303030140001c030503032000c502c902141c440f501b0000701603d0100803030380010590a00d240e0b2010280c108500300d0900f0349003080c1a10025040341148030b00781c68070510382034400110409020300c01c00c19076240c03c205600040d5544140759000000955840c00c90300850006840894032100000c2c0b91440c0e140503440700d500107000164103c078030b40c3d5694010040644280f14840030302c41c101d24008444041e104d4002c05024000441d10b48041d41d0740d03c00030030030070503070000c00c0203140c4501400d844407800c0c0003110124400e540000c2c0a42e01d0800050b450034030104e4510315550440f4003c80098a594860360010411035242c1c0701442001c00000280d591020042c100a501c610b0055540d00320756030180c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 377371879 1250 377370629 377370677
    0x406090f08010b100c1106040306021b0c180c0c0f0d09050906090118090519020307170304150c06110414120619020d05010602070302010206010b040803041505070b0106 74
    0x10070542d240c521603900726a15030b61040503020751407611042c1045181460390a02c214401a83e078060b10002e00081003002c16000780400b076a010f049080d840324050080303a100d0030082010350b8019650f060400302c1000080d111038100035241c001d1403e090107114414904000442c84003690b500641c030707840d01e840c0e02540d00c2d809818240d0b958443e505014003c12001074040c05186900d60100046403454580d41d402454000d4009080311844e00814104611860441c0c03003d07406030103607103400b0030f5913034404001c44001007017000214034052806031081d100d208041d4141080210702d00f203210120b9494029901204903404401359102d1812401034400c2414541c03080c010b4664030321981800c180424141e51140c880030120b00d900601c0304400c00284120480440f010f0300e00000032a00c2035000840d0020390740f007030302100c03c9641c0b9a80d038140d8078002e6214a58441c1e0007003100340701140581001c940c00c0040b50911300d00b000016a03560303540c20000d07004600000c11182055066901015200d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 377373129 1250 377371879 377371889
    0x50708010c02030a03110909010b090f040b0f040209030708030409050114030109050723061801110a051c0504080a11101701090b1809010b09060f181009020406090f 72
    0x70881480903401c0079440340240301a0109040d0b441c501c003101e40301410b0885980c1c140c02001142c940d030315800c03014413a4002500f07070350142100142021950600748101443c1d44401804003400c6000642040081c0d44070b104c4454241c01800000a0341500400c007034006064546d901003150340c1002c0000681141c50032a02d48a681400d4500001ca20040f40f00000d40c0c007038070311400f0200350f044a250218608140c2d21350f0004400180c80803103c110209683d00c2500036a15801451030b4024245d41c6d80c441d10001074410340200c0d00c03564101c0c406500422016040b8200207040c40e507207407012400d154404400399009000b000845041d8901102d00404200c02400c0c040c0010400540084500005008810310169105401c0c2403940d0f0308042c00d0301d407100300442c90142d17141c090031641c060044031071080e000c0c4d00c1e95070105d080c078030307050303101d0403100d04094420915207460743c02c003008001001d00f064015610411020404c0c0500740004d1014080f0b50f1142d4140d140f4010300945000c00f00d0b805 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 377374379 1250 377373129 377373131
    0x60712180201200304120507080a1703040201030f02032d100b0903071a041d060d0f02040e03030112020f0a03050331090506041a0907110304030b1305070801 69
    0x109014120011108010341c0d02880d02d144078070040b2600c01c6003848141454803a6100100d030010305040d100d1040c960043c407d0341070b24806a625090747c1c2d44d50451201c01045000c8892070900710781106000345600500500d8003242e0b283d0804040d8089030310540d402e04c803040034518182170305074602440c4a00107003901ca5080e003614000d6021201b074500e50003050404240000c1c0440b543d07408000e00409444003074031260403100d484c0c200c090342e98081c1c4103030042407110440301524150140d10141c0704040280496000d284170f0303961044031011380e450880c0d006035140d022401c420b4040014501078150901a561819401e0040000181c0a071041500c40c1ea20031405000041c070200503500c0003c01403a0300c14112000900c07407201014445800d0412480c0004001180007142c1c11442c01240c0c155410451800c03001e0510204c900e50000b125089440200070444451051500100b904103580a4074201030b08d81d41c41d42d04948094418a880c211020100302c00e1210510420b0010200d00300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 377375629 1250 377374379 377374391
    0x1401050f060f0d020102010b03100615021b060d140a0608070509090d030b0102031209070929060901030204050a0b0406030e0a0f0320010c02010e12040f1e17060712 72
    0x400140c01e0704202d048140103842c00c0c40b06408590007500080580745004013541e54140a4815040c010040d600c01c2c0000c005041c80702410440c0089111a07440d041c1c0c40d04400f400c803070078080c007049500c0f112239502015070f50b20401c0c1000300c00c90b11990043d8100800401c0305440e1007561850000180c00051046908030f0501c02c242c000052480c001045608003c01c0340002c0c107006034194010034a280d9221104041007003003032a008a2104141e603040c820800c00745032040000003812030b0800d0903c01014800300d2010051401c000900f42d07504e014903000d840d260f10344010a11800103540700090345800814144080c03074242c081c0c41c0f00100c03c0f40003001c20100c0e0380c0314520200c140c1000601403140c115403003048207d500e2113080c118001c1e10028000c8010140c00240207009030782d0100380c0da00a09000409140ea40740484040b60031300114010240d0a0035210640c0401c07542c102850301e4007400e8000385207902040b062003074200c01c3c4040c205914003860301610340240c450100240c28a403c0c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 377376879 1250 377375629 377375641
    0x1b051f0b01080115020f120a0f080603030a030f0f021201031e08190e0406080f120a050409050c04050916081b030a090f1707031e0203041815031401050f 67
    0x10042c0d0469565032111078942e00c1c4400140d0030b11401035444c90f00341c005c140c00605003a4924004210b221040c3c0c0c0c030a80211850352003190303110001c0e5102503040d0820000b0600c02031103900b007a40c00719400d0500140300c0c1010362240f401ca90012240480d0510b2a900400500070303201101e1094104202c80302d107074030301c5941d50030f0031600c17500c0d10703586003e1440c9a40b184c10314403c401424425202a10030440b1399111045a9980c04586125000610890343c803002500503000a032100f440d09502d0319401c203410800c540700a40001008410390040c24000010315a0b5080300190048058901e00d018200034040000c07c1c441c001401c440e00f400c10500c504106450304401c0300d60240203a600050704810915101d00e221000b0100a851228000c1d008075113105c542005140076031298548130f94600c440d031800704001c600d074030200015810500c001c00c12521f0115010b001c1c1e6400d2100051b0300380328241610000d03031568005a13524602003c1c00c0351160b909210300d90b00b04c400040c2c26400c1e46004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 377378129 1250 377376879 377376887
    0x1e0610030807150203151e01050405010e0117040b160c0302030a03051e042111071203021c08070306121106091503180106050d05100c1b051f0b01 64
    0x24400201580000200b40b410320040d401c4200340e0301200002555a41055902d034001d00180c101c3c2c4900c20720158498210690f2140304046c0600c90603124141020b15080c0151019200143d03010b06211010240b01148074105024038480c0c0d100b07085241060a02e11103001c200305140c00007400340101055240d010a800105481d0300480a00d000300d16995801400350700010240c8622010303821060a00c000c000d1641c218a461121055041d605140e00721401c65400c40c007800e4040964110f02010300001810007081800d5600a00403640c00e5010420518201c020200f80000000c0c90b0006004149525010b0031004040c0000700b00d9612007240c07178480824440b10b0001b0701c10030700028105000c0d21000d004201000720080c43c16101c0c504035140c105101c0b11100417800652070b04101060b5803400309840c0003810740001c010910704500d100c00303c00030411451a04180072176008440808064000c04601151140303004e41100c02c0d80342405d410030000013a400c424182441214000d990788 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 377379379 1250 377378129 377378161
    0x1006140f070b13210f0c0b130609080d1410141905040e03070b090703032c0913050709020301050f0609040906060608090c060a05070b060109080f1e06 66
    0x202d040700c4900d440340c2c0800248101c1c0598001c04004815000c4030300b607039a030480c441c2c100c2d419454082e6000c00248086500c0056040011301604440740800c41c1e07070920858502c2c1091141e400090000d140362074010032900020a04102151074120000008809000c3d407a0040103940c00103028600344000440c640321000c4615008a40d180005009288042880c0f0700404004d04104003010002070f40c607450303a002079010b0360891110740106e103078400000f1384d200807a48c0599030180644040714404904861301164900c1442101c020042140e5451034098040c000c8000280c101c80c8440ca031036410580c003503000c0c011003881880104602c1d142c585d900030034050111030030365540080300001001400c03c9800982503038945280840d040390420310007402024514110f911802c00c44041210030f11506003800d000410078803982001840108113160400310504240e2040da0b15001d84501d0a11140b10300c45860b400220040c40306000a03100342400d914410217400145843c08542500c850 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 377380629 1250 377379379 377379383
    0xc02210a0614190506011205090c120706170c040803040b070201030e070305060c09061e2203030f200d020318030609030301030b040c0b0a09050f030102130302120102070b1006140f07 80
    0x4c1c80e200050300d00da01c5081502c0c960802d0800801c014100030b0016079603143e0f13601081c1e00801d441c41c40302c1010040003038110116052541da122a0200c0740e44848940c0ca0081d000c0c4041140910000c0364000c41400580301510710320300c0b2241c48603100e0000400b03039048041d6008131600240400c0c00484c201240469205911050007a500c18842010664034850b03c01180500105c65007603603c801c0483c00200f10704c40901e10704500d007a80f440c21940d43d41c2400d00c40100800c04401045018a010b6442c680151038540d2001200510108071203040285081e1200d0042c2c0000800c41030100c50340d48000492001600100b090745416031150785d030380c8010b00010305aa00c0c407500040400130300d00b074054050140d000c2050f0310380900602c00361061101e8002c007445018038007090340c06405c05200fa03444088a4800b580001c51454007403100d42c0300d1901e40510360f55000c2010101003410208041e02406580d50390106246c580800208103a40d41180307042c10039403c1000070176410109041d201c032a0303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 377381879 1250 377380629 377380631
    0xf102016080a17040b010e071d0d080d1401061103090303070b180d09151704030c0503041d0405010f050702030304121e03020307030e0c010903030c02210a061419 71
    0xe001180c15280f0908180e06070110012240070041004200d552241c12502c02c1c4088040c940c8801a05035804009510701802c0c2c03c10000d1064003505c0c0444180076a907004040c3c5900e4040700c06402c0090f6203682203403e01c0080d5400040109580c03002444025a19040246041034091030000343c482c4129100507000914000c04901c02c0d45000ea60301c06401c014a0850b400035040b000007034220202c1788607030500740014071b4401c8002030084030b4494821564102c4044240e4807507a064406540042080e90244010722011a103240300e0644000003ea5281d80901145850303e8264207484003120820b208278200402d10581c281c0000550750040e6120284400c0121410412958580380403180e000c401c46050500e005640c241c0d0040d8000d040b15034041c0034000781d0680c1d066844001c108528006040d910302000801d114900c4200c40341d1004220300c2c03010b69070141500308080e200d00c404809400c10040b00081090700d10030001512102628000e05180104602d1070507456040c20306111 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 377383129 1250 377381879 377381887
    0x207140d0c0b03070c03030f0c0c0803040606031b140d0b06060f07080d0b0f010e01021e0c060705010c0215040309030b070c0b0a0204060e0d02100e01020f10201608 72
    0x4000e07498a04060001201c0e100d0b100d2600b41c2c00200001c034400000c0c0d000c40c0c034081100b0310624043c004c81421440b1a218031940e103c4503a03501d48264030050040c0c420700c2e516107000c00050703440b43d40d00c0340d1010a02800d0651f10f0404141900706040c000d040ba11486080010301c0006c0d00303410941d6031040b8100c840e661119404407004d00781307200303900009001010002c1c640340000ea450b1b104004082040e2950748071074941c80d00564500302e18011150140e880031881c100325810710b108117510210190180c5a0101052020030030310b8001d524112040d9449260820402e030703040100c08004040100b00301542e00385910040d02c440004d0101034040c1304560006040d0034001c01003000075a52001c9011054a06940004000d4200f0300030203001501c0b0a5034041c1c00d241260500d19034540080176007a2003001c402003a521508001009415401242107541c00c1450600440701c2100004030082600c40841150710301110740002a5514117506000100401c503185c2c07251b55125600c14141551 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 377384379 1250 377383129 377383133
    0x5060102123405010204030b0417090f090a0204080f0a2616060608030315090601030207050309120f030403050709050c04080d120f02130f1202240f031e06010207140d 73
    0x214080c40b0019100d036000040c0002001501c081051043c3d00800c00303008803001142d0f941105101d0020465440700d55240d44181a2605842e07140d009007501400520381a47c52038003d04110800300300c0c1c0060382054144405010400c070f4004da100303201c25442e030107504040c0b802041074003070043c0c0000103c0f540f40c031020402c02645d1000020b00019412a070b264a0b0240c0a20814a0909420341c02002d800000c500e45501a00a84001d113034000091400e01340501d0a000390130000d00541e0f8024480c540800c00062070610003007018501071030182000300d051607075900c16200090301c06500810100000c0000540104020703210740c00a240201007031186040c1702000e84040e001c2041c8d8180700040000100c1c18616540c030407690406103855030035507a892000781c0038095180180d084403080e80300500b01c1440c00320444020403104031075400c00ca15020344c001d4503003044a40300c3d10710301c420200b6101c102da0700c07145550240092004059235824251080074120048032003a0042c4665010041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 377385629 1250 377384379 377384467
    0xc040302150c010204031e02120304180515040905030d0b090403080604050a060f060c06050615030408030711030f091c051c050408160315090c03080a110a060506010212 74
    0x401540c220300c4045021110514078800d110751384c0306c109d1094021380a070100140c0c010090300c0c110341405151041101a00b07001002500000305111205180e200034000969140d01c205101140118001c48c2c980800111540031940040429481b5592010070040003d0f071058020b60710250a81d400f08090302d41100f68006030085420211030320740989030206406034403041d5031341d01c00d0140b4414001c640710181409100f00c40c141c003210f10301c0400c00008022403d15070086401002c9032610148800b4804152400c0da040b10701c84000c6054005810a007502c0c24400201d0181c2c548003003080c1c0b00305ca582d50745e03540e80c0205803d2440055400e80000f02700e405641030701c000300b50000a071180c0c0050103080f0103900301c007404200d4000c100448802e50b0500ca520411480d198414100c410460075601c5500007a0010110501008500c9a08894552060040030300e91889883e0200315401c1903000a41080b091103148651400244200c414020340d8a1404204510100500001d01c0c0104641c1d9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 377386879 1250 377385629 377385637
    0xe0a030206130e39070b07021f05160e131a0a05010806030a030806040b120a0b090607020706030b0f131a060703051905040b030906100b040e04030807030e010c03050603060c040302150c0102 83
    0x51b204c01002c0d0201714002e40c000c641c0c10165503e81c03d201d8410800244150104c4000f51100300711001002c0500701554002c0c03140c000076020043c00454a603403680360300419079120030f400d0428482d240d00043ca06041840800d8064003090810310042e18104020a54034a280302014040120550100342151160762000e0103c000142c000c1e481a401c1d410515501c203c8903608844844090000030050178000c2501030086140f6800703003c01500c3d26000710080e1908010340c5502006880010030103540c0c00300b001e013042101c00f17400304960700e19290040e00c414049030030703034000d130010040c2d040000d80c480201c42007100180050420101d80c0c107402c89880c05250025010700c1000800d1241d03030140011500d2050b030b480690020995250f8241840c030740164070608078140ca10398041130000b8021205203600200c9450001290300c01072018500759090301c04210003080d42c40e4280507031400c044c002581c0c0b000700e0031050784c5000c2c65540801c00b841d616195a10640d0b20108104120840a404032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 377388129 1250 377386879 377386883
    0x201210e10050f0702240901060510031409120d020d0912050c0f0a0309170a02060406050a140910080c07151a120d0e0a030206130e3907 60
    0x40e880303203a01000740402480b05403100700300c1c4212080007508080c4000b5844200304094000061171906100184503c1200a4001860307075407a03c0740880d8540b203903001c080c0058410b82c0e0100359111032030f070b43e1a0315000203400181c1a42045140220154540b411201410061b40b401691190a5090301d40104203448000f4508003a04140111455201000e031041a20354015030b0003503c820703030401c3c2c0e0325400c400f00180401c04a120420204a50b15480b40c480c15a040503500340c24081c2d0700164090b841600030202044011900c0188154003c0861201c028811b074020315021401c00043c11f1038aa03850b28a04000c55100041d9201411805407000300c0d83c84a070442000d000c01c000c110203040d0071f000c5944811100d11326a2642c2c40e0a025010b13a0f90148000340500e900c0b860700c211401c00000d01802e41155503602c1c00401038603920020049080000c5552507450309251a420600034050060103420360580d120364070940780115001c400030b80001403d04200000ca0302800c40f40204000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 377389379 1250 377388129 377388133
    0x5280905040e0c150a050c1605030f010b090403050c0c03150a0b09011d07021005101a120403030e0312010801020c240705090d050d0207050118031e030201090b01230d0201210e 77
    0x102e6400c0c040041c1723600c410b40f1411800c4e104e03226200c61f615070881d00d83c030010581c03080ca1900031802181c0100010540040204e042d50907541c4584003007482c04610701c2420700f680041a00300103000565210b061215001220103000c0c65251040044665580c1c6162900080c4280301084031540204551401905c00c4101485207290071030b10400090b4070b070711500720800145001125690105070494270314007040a0303c03902946542c4c030114005c14a03000340c0704061204000040b000809856028001d0409400160359038120001080c140424405102d0300030281850410f103102c5442e080315030240709484c0c0f003a00c0307071090f0001445c1450560b40180c014040e101849042c168046190000e4540a0300c4181c0341e80380010703d1a113050100c1c0f10140513400341c44071541851800c4e844103180140071348004114a00790391034600a03044203030f009400600900c181d0341502c160001d211940b01108a4022119110540010b8269030007190900b034507481d06c080c04184242d803544074102c072601402c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 377390629 1250 377389379 377389393
    0x15060305121b19050d030b0d060b030c031b040c21020f0f040b0c06071b0618081911120405130f020d021e030103030203090105280905040e0c150a050c 66
    0x484a0b0f00e10b085007402d403200c0c000c1c00c94514445000b8060400e200c4005444284d01074020f480d1803000742078000c070050b03042c01448441d80081e90100200b14560b9034420109820300070701c00c00c00044544c8010034100303200110401010565242014400a2130364490142e83c070b107001d1803403940c10f101d10326041e20381c80c4000c1000304112421718080c080d40241e02048070210340390000c0942d0081e40d60311011240200d803020000000d134598102d10303065004030000e0f81e0341141ca95030f802003030f402143c0b2903c4489610324107540d84946c0400b280589003c010050300322100c442032406010b2295001e241d000e00000802443c1c40c2044d175008031203910802d4411503c5030b40940030007001c0d50000001694502110700c3e00c2c40c4031481c200440c0e040740ea064005515040d03414005440c41d8100b41074554061048510004154001c0c3d1602000314420366940961103007040200002c89070f400c640d105007a03010403518039482e00d50030169040001c00d860044c1c0c13603406500d0f08440610901c0000886802159 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 377391879 1250 377390629 377390653
    0x1d0306070305011401030e2104030609052a03030909181b010f02070b120c070b01090902040c05071a0c040b0c0706030b01020f060402040504080f031315060305121b 72
    0x25001074182c2d00882e025821548066004406a8a9501f00300c216030b040551001044e42c103c050844000101d110403900b00356583d11080102d950802c01a503075600f043c011701598450a0303854110142800002d04c5040d5641004241c1d02d0040b810385d00c2c00740d00002c0120710b02003642032850f0030003c00d0408039403900072014130442100c4041d04941340400c8108113101c1d045130022030882d043c1d070b403034021590610b1010754603a03888000c0506680a1107108001c040041070040c1c0204d40a0300741c5210100b6018a103105000440341d4240818040050a110050000300755480e80c2001c034140035900b200e10b85401d0304010303083c840d580c020b858003000016070b20350b410808580da41c2201d80341d03101003101406200041e49c854400506005490b0842d100140c0140b0785640000d030418062885103081c00c10350700006200d98801da0b5651800d808038440b440400c42c9400507a00b0464401c00e043c01014075640d07440e90395811045050421100c0860070158014020044580d07002c40081140c1c0f07006449 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 377393129 1250 377391879 377391881
    0xa031a060307030c2304050a0b15070312020a1407031706040b09070e1f111e030a03020721030504170c0304121b0f090c0e012106181e050402101d03060703 68
    0x3081040c0c0900c0a01d4ac401100081c44010795070600e401d030702c1e180000311425003034000035400f01d00c150742841001806141223072541c5024045c079038401e41302c104a490720107a030301e4080c1c0001050603201e2400d1405000058403040c108642200c454203001c5c408009a50006200d100600541156811000f403900d00d0030340d120b42000d05103414181501da520344481d4030410034071800d40e01c04005520030404003261500c260300070b002041c001c0c0b6402c0000350f4400052200543c0c80050000082e449409100c240316114a214108810710103405240140661505442c0d026a1048018020305d56030200700380003000200368100020b4980180348a6218a8160302a001900564501b0380c5003007103484916000e42440070540c0b5050f158540000900195400030b41e82c050217500c0101d0b214180010035905448900c50300154a0350045041d1851900d40607100358215024941c0c541000f044c000907803540c08014504255519100e0b1489800900c00d140c03900c24029019018411103042206407541 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 377394379 1250 377393129 377393141
    0xb01030f020d09020114031302010c050703020405011d10050108160e09091c030209090c030721020d0c030b0d060905070b1908060d03080c0a0e0a031a060307030c2304050a 75
    0x400d807140003280e031403c01d41c10724a01044904c601c1c408e0400610401543c020035201c50514824000c4410198803507020a00381d440a0b070100c2600c0300940c0345c000115035060962039100a1070403004446a00e0140003c1c49540c01418114041d80001c0814424911840c4081072480010f40176040d1400d00040d10f40da160f071000395136044d08100c0b0b100c00308818840d000300d600f4040018401c240d2034aa08074000c2082e4009000902808803d20b0b05070f0282a1444100000126401005803520309401c40c005c00d0302c005c00c800004261a040d0380f1602c0b91348803141310010940085000410020510707100e40b0f0031442d5001400180408103007010350420000c080034400c0c8ca81e40e954620f548a04003401031240050074020007003041003001a04054a4001401002d2144c1c94071a20313524032603002c1485080c0d1a0002d8030414100300114508071000c0c0201074004405034020034803c0d1468580032043c0d8014002c80021610300181406e0585440f03030b03110010700004008001c0d41c105a001c040081c06 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 377395629 1250 377394379 377394383
    0x20307150e0102360108130201030c05070f210903051005070203090a08070614070b070c1118090f12071502070c1e0501020102031b161b090501121101030b01030f020d09 74
    0x4c0c6200040c062540318070006801642c18094260102c00281e0054001d8100440400e00700002405035001003520300c004218054000e00070075140d080d6221910080c00c2814200b1420301102c0042080000c0c030004039060708060303410700003c89840d161005ca0961150211060384000031701808507103864007203054800c8454680f10307083c80c42c804a01030f241034095050302400c14110100010740c9240122004a042072107642d10320550500107000071250100340c40481524200301041001e41d038010811410f912018600402014490f0924055148180a802884d40305c000c03403e41300403031709034040e10b84441d44030030004a00d030b03210b403a0811207080d2403e5407119100c8051300040c00e0350061080364000c1c607200d42290000d410309401101d85601003455008114928441040420011080c00c0c0d10158011030184405150605d90015210181c0049800689200d0160002440c8014141003420207007000719030340c185840160010b0600c40c0044036603a000046120f900c1b000c50b445240418 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 377396879 1250 377395629 377395717
    0x5030106080604090305040909150c020a020111150415140f0402130b06040902070c030206070501051f1401031d0d120e061302090903070602070501050105010807020307150e0102 78
    0x55a0030b0708100a945400704d0260106100300001d1001c42c0b03554004140050080048a10030b85060304180200e801d02d504010060700200741c0740045683c0f25249031852900d02004112a403050b172a5000544409400201101c01036510f50880817016044040144642e030401441403030500200303050000d01311022885008070386101045100644030301c0c004250041d15850405081001180c001d40c070084081e90802c003111400030043ea00e0038000d110040c812000031810303040122401901d003d440490100c60807241e603080c00384403018005040b0b030950900e800700b031b0490300d0008540e802c040e0300134110ba14007e4408504034541c201980050306c0503075420420900d42c0d09d0400301c1d00d0788001da40e8000d4030386000ca5200c2c0546440c0d54019040718500c001e81e8a00b1025580301c80403688094002c0720241d440c1c0740100555a0000145603001903140061850031001d41c0d608103c04030050910701a50b5503ea10840f440102541511200414060b031841544243c500000a120001102c81090 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 377398129 1250 377396879 377396881
    0x9051203130c0506070b1b0417070518070f0e130c17010915090e01020c0a1103120c0a0b07090b04030303021e04060f0c082701020f03090307030308040f020301020a0503010608 77
    0x90a254041710074054200d050504a619603100c07078400c4c008801d803400104001400040b4018844407a080c1c05002034800404242d8170340000c0c001c0240c190307035482c0c6141e407034607040150007500100d0b42182d0192919083e1184c0e60302c0f10001d240c40d403070403518225992410403c804010b4001000ba030908000034440318a60380c1ea81d156030107450145030340b10b80e10b00940c941000541e0b0f06030403000312408501c0003d401d03c540a10360b0f0b49055112102503d100b00059078144040c00c0c02c2c44580d20715034518005514000004002c25510801c1318002005080382400044030140300c6e000340400b0300300c200c819a42d195030340c2c02c008010350010b6120800401007164260111039042e000c8030304a03007203500d40804003c103520381922442d5041d5401d1b10850001c2102e9502e200031500b199607045203c0358031840c141c0c51a4002460080d4032040d20469900400075010741d5640000c90700308683d81480c0c02e5410b51b650f841c103401c0314411450000c2d05503001003030700c1c12219003007805141030740c0544e40d4410003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 377399379 1250 377398129 377398139
    0x4110d0b0f04060f05131d030304141b0108090a120201150f0503060c0a0306120c090507080c03060f0a05100203030f1605040311040b0d0c180504051009051203130c 72
    0x3126680d104d0b103100304400050810107801e04484640000f410004000303120310130504650f904a00d0000807403410b070000401c02c0b040001d410380c103201214401c8000e0410300d841d20343c02020750380e207848944c0c14069048006480b542040051a00e0146c0c44850054001d8112401a01030002140440c10304000e911300840d250001240070b104507040180100310315180d2070910a51a809490710208041d15880c012034114600704010103103d00c9148072881c0c03949003902c090111400542840f04100300c11081c000403080c440306481c1c1040703045a8404540c20b14100080d400d002c44c0d4000d03904000e00d489007600864010016512501e045851500f041c0c0d01d0000024154042404050100303200f40410f00114100703500d0365a41c000003030400103400c5520800611562800c09049803295400142400f03420300030745003110100c9003260107102c0d0741065952070b1380b50381510b402003a10f82d46d030f00c2414050182c20000b8a400322181c5e03030350720369034202107031790303000c44050307038000380c8d1108481100018 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 377400629 1250 377399379 377399381
    0x30c180a060e160309020d050a081e031303030b1201110403141f1a030f0a03140a09090e0307020a0b030103020906181f08010c0306080d05070203060f0604110d0b0f04 73
    0x1102e048803c59100785400c581d0010b60040480c0d0170181e800c06030990030000020000c001c0c444c1c1203409140e1854940c2107801c10403207040d191508a000b4088244140240304114646401c1c40585c1400d002c145625000d0100d45040b100c8151b604080d0b0804c6805254004810010701c00e91303025084459028100d000402d0751282015400d030341c805200c2c144030007006155400307051000084044040585804d0340042c0c600720410084003c180c120030f034004c04041d00601141010014a5400e40c10480140350240c140e240c18482c03a00d2064075104102c5003203205100b2100701c2503006003c00c80075911400c0c00112a003003400128025030303901000c101e079490600000708295505881a084c3d940d9441581080722075400144498003006000c00701d2511020300540000c210f140d540060010310b8081e0440c50300140300090000d2042c20001072001d030310301180302c81e8400c141800d819001d0302c0c4d000104d0010001c01c03507842c00482c8007107070868400ba0160010800860111900020300d00c043c01004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 377401879 1250 377400629 377400631
    0xb090301230c071a090c041b020c01050c0f030c071503060f0b0d0608030c0d090506040303200304030f030309051e1b0d021905180906070c02030c180a060e 68
    0x2958100107031000851610002c801000100d1007940072620700e0f8800185500c803040b05582d11041c3c1d03000320041c0a154101032164240e401d03031396603800380d604101e080044c0d26001c41070f00f41810844001184900c5080402213041c0c8000b1420849960f110448401038030b0f14000e0241d91402190446010055403080c024801540e809a40c1102450f1410546a0050b441501d4150210752103100010b40d0040620160501c3d9901202030102d0505c0f40c08020f207009034940056100728001e200510200740e0000100060490403680702144543c00c8001c00e266000b9a4801000701e10004110400c259068011000941c450b0b0201c503a082d80f01d4007a1710031109000c3e1078550503400505050307003109400712016440fa1020b0a95444980e0039000302e1444007010b00c01c0700003000e00380f0040185041032003c0d41149150382120041609005030456102c9001811032001c01001c0f80c1070500355901800984410f0740300400140300440d15018880f074515040f035910303840d41e00c2c10a0000352017032035001e0740b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 377403129 1250 377401879 377401931
    0x1410090e0121020901090b040c020a0b0a0b0316030602040303120e0a02100302090603040c0302180709030b070509030a03020601090f0c0801030f0309050306070525050a15020f040b090301 82
    0x69003603080c100e007802d00021100c085042180000c5000025840d140c1c141030190100c001c001c1451100c03c800c0c0404d40d480030b00c80400315440300345c011021a400681840e0401a0146d01144003003200c0c1c0040e1914101c806480740e802c0c0c5000002040007010350041084920a450300c104013590100380c4401c9032880c440d100b1071500030000e10001440c00c0c004d8100300019500340141080c0002c008038031550004c0360100c1d11154070070030501c15481c10f500c40e050507803250001505580341c0b12000615072034403031200400050005021a03c128001e00a440040b4005030444880b040d4904000399594170038802c0800c410725111004403160340600075408134140316103030150103034610359403400e5684400c0c01c283d0810505040c0455540c0d410300c0003a000700712550321162260900000003030703100fa00c5080a00c902561001c08800520081511100700d501300748840070842d030540d20b0304081d00c90394402c09858000003501003024184100a0441c08405400801c000041d4201a1a04643c44884 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 377404379 1250 377403129 377403149
    0x203030f040302031605010603060e0a081b0307060504110906010f0c112b12080402090a02030a111b10020307050301051c08040605071110050a030c0203090a141009 72
    0x54090200344101036042442881124038100250103041801d0f00d4450045466035102c81c030400c140107460150381c290410050141c0ba80220756502c4035180c0c407407205400b00000c0c1c40301504807881814010b440c0515001034045c0f145107041c1ca40907411303a00030302d11940b01d840e1680c003052041d44210360b0300180105035103910344141da4680307a90f403454640c168410303806401c80c140d03041400e6806045000080a400350303504414a946042259200803183c0c0800700a2001d003003101598030200f80a801076a12040165a80c4540c160304001d000ca4407012880b488001a101d01d040d20b0340310000030076414920a69503540b2084180d081a84400d0f651240015400e00c011305c06031405041d60305411100c110401b4445407542d40f00d90740c6ea0450ba0051021a10108510044c4150011401c0450301d003210345104800d020352000c0c00c0c6000c0c0303416410405640302200b0080c42d000f042101c5c048000107203203609a955030185c1e01d980f809044900c6003c0c1c044042000c210b503005030003003030580d91641d80b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 377405629 1250 377404379 377404381
    0xa03230c03193315020309040e01091b05010e090402130b030a0611090f0103020a091401091e0812070506040f06020f0a0804050c0f06070f0606080f0c090115020303 72
    0x3244604100c0c4086a1151055440100d009107203c0807103510007058540d015142815843c0d80a140700c0440e59100c0c0c40094040d000d00c83c0b40030780c040301f00c40c10314404803000902c001c4c03a84d64030703030040c500c4ca840102070380c45c1e81c82805400f1031404c1c036160858200341d84000c2000c4154061044840d42913030008d410609121403650b007810607402800080c54052700303c0c0c4000f500e1362500030544070202c803140c10400d00000e03104218208074050740f11410003030074158609204d1140003441003561348125280c4040304c80c02a40d45a1003006032000038208450034510030401940542d01c20015803103070f68040c2c40340902c1e44851942000903501040d801001500f42a50356850b01c02c1c43c1100c11800700d94a82c1e0030402e00d4400c0e118034001e40b03201c226a903500031851816142052600c80900e00040c40307148509a0b4100c19078504080b1610a41e22507045548424186000005800701d60000b4283c2e0107440044a403401d0300246000910f04200c17402081703a680c61802d0b03444400311400000058100300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 377406879 1250 377405629 377405641
    0x10c0c031202030702031207030506010806102709020d0212060103091203230103050f060f090d0c050312040308040c0b0405010c030513091104080708060709060c0510020a03230c03 79
    0x40d010315403084c0b403401643d1810070407128503410700c101200e070440480c1c3e03100107000c81541c1c0f0020031580010207980995010b840ca030740c058204200208041d5030b00a02c5040801003405080fa0719006200710802592901d000b0201d51010b07421650350311411801150010b10301e0b40c424004c030f240f52600400e9418502c00218411405000ca40c1e4120b03114680c0e4502d007100060560b44554000d500400140103200d01e8600c9140c24032002070300807002d4176031034004c1c450084c0b0301082c1c58011480328104250b088110f0302e0074a08500905600c0900c80c10300200700800e15411402c901d04c00c6110701c94000f440ca4944601811500480c09500d00154041c03240703000103030042e00208100380d40910000d40480c0d9982c5488240e5100d00c600d032049080208041210a03400c10101000e400d015000d801d191522600080c100311003445140c2c20041107804030b40c20b02c54288201131000b003c46900707554030400800f0160140c400c141c804107141c84d6a030589044c4d2912000100d0190810161503440e5032500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 377408129 1250 377406879 377406881
    0x210080406180602180118090903020f0d0e0a12110f0f0415060e01030204080a0f1a1003170309070611011508161d07140d1a03010c0c0312 61
    0xd004403071035981c40c507520a581c9090300503241064811440941c0c1e5001d1310000c0011901402c10807814001c182d50044451201032400d40155580c180380024555941d0400f00d10340310100010010034040c2d402705620103688484c184404140545203480001d030307070b0407084680c64500c0c0700142040c4d0070009004024030f8211800c0401080041c0600d50703c0c044400000c5c00c0b25018500702c00076082c07402081045039000040d0b207028130b000f42011801c151400d40e0250311080f002c84d0003091041560440c0041009991600d9542d03100140701c0520307072508410b0300e065103c090000b0340d0107410241d68514110484003c413481380000c00d01a012013031400201303413030307840d00c20b11080250f540b200e4208540501841404004184284c01010300f1800305880b214002025000381c6c1b0002d00d5041202c021001c828001074003c4803c1c5404501007040c00c8900186000754400c29051500b09905542d22a01c0360708a080701e00d404034001c105050b42407000340d58002c0e6510004020400c100311000b0280c3d65 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 377409379 1250 377408129 377408131
    0x705060601080c0c1510090f0b0f06181018030c061211191e05040e0604060506070312060e01030b07141602041109030102040e01031406040f06090f02120a1707021008 73
    0x89602100150b224103501056540e00840b608e40c8543c0d800d25405c40d80b034070716407100c1008416502a0b2401c40100b1103003004401c0112500d0184941c082c00f803070128440c00700220071070b1005c0b5404003000d842e80707007a406000c2d0610480b400200f800840c4050494148608292428a0441c242ca404184481c0c000b0520655503c0c0303007808240b1a1200f44c1050b005072802412a2a0b500d090b691b504001403c03a1000c40580001c0c090b5183c10024050754035950102c40c4000e0305418411ba80b901c041041030040c0245410140d02404880000001c0062142c0340364051001d82d19144608800120106224020540d10110502c1a038071a0b4000d801c00360311000d07403281801d601a142561000209007a40d000340d000d44069649100100107014418240021060352400901087d0800d51102d02211351284c002403c0d562b41e071150f4404002e40d6442000000f0f40c083c00310040d07040c0715401540ca50b14003400945000c1e002c3c2a0107441602d00da02102c1015a0007070194220850390901240c0c4004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 377410629 1250 377409379 377409391
    0x504030b0712110d06150e150c1005010302040f05060102060718030b160207140a0e13060f0509071a070305030423070302100c110405060a0b0705060601080c0c15 71
    0x74a0842d542d841c40700e01604803e240b089020f1a540c2400d020305008894007a405144003d595010a00c601c90f4000070340c403c0c100f07088801c4594540c03a44082e045600c40d100a42c1414400d00240c00550388850b0041c5d812a80203c80400c550441440c0301c00688108850050040c4c000c0c600044440c0d015000e40d0003840e62008000c002d1070b8590f0745060001c10162001807407010050100d02c15143d0400181000c0c105010641407082140c2d000701d00030f401540100044d09400100189820303c000b000c60701140d42020301400400791503460070000740000d88000034140a010008990703005003a00c00b0003400801c005440c901811340c1c50454a64201400850300c800710903111200181100010580d50364009002d0405c0518601c10000099080c1c910507041c421580e00140100d010011041514842628042880c0e941e2000160b40e01030241c022401100c0302082a00c2801000103005110b200e080c2c80c1e140079070300c841440d04050700540000c070304154091046d110f410700014841c190803a07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 377411879 1250 377410629 377410637
    0x60c030e03070b060f06040311011b05010c09090e120304111206090601360e1c050904050112051c020114130302010515150313080708040e0108030a0504030b07 70
    0x16444080d0707040d5403290a060300d01d041400c1c02d03c40d0074680b20090b00e007092412070300149402d14503a208120460500451810b010010a6101070800c001c00654070a07070780403008004c20700004001078403001c610f024001c0d03110701e40090140400c6001803084e86078120781080509550fa00da880c681c03c40400402180c105002d1900040910300c108142401625104064000340d03040446070189041035240d1500304800111340502c1900c04d600040f80b40c0081c600011602000044840c0d2810103128051504503007200c036094030456004020341101c1c881127030309021507640c600c007450419000900c06013444e00085001c0381c0710256200d04040d440022300020481052050524904080840b10f0000404200c2e013408205942803003100d6104031411490300711525140b010030080741c42d840741144104130010200311a40b0a001c500012240c0c00408660f0390030240c03030300d180b10b84c115206441b5040f411000201c9c1001d004420307240d0500c520341d40c860a2034515150040e1510700900028248 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 377413129 1250 377411879 377411891
    0x7050a05151c060303080f0901060e04081608040b091c0b1f211104050421050c0319121406041a1e010e030313150207090c030504030801140a03060c03 66
    0x1a103441e006a030019402502c86c00128584034801c0e40c80f10900401c1d40e4410791500e00c06100c502107014410b60419000302d0708549404400d041d0100f6002e94400203040144041000204000d1980040c2036000d820b031852142d010007518449207800711004010000c0d02140009010240140040309040340b040d00c040100300d541d070048040c15001044440020800b01018200f40518076084212800303050340c041040b0301e0680c035242060030501c00d240d20801c8080480c0d8002d14499020b0328103001000d800e50ba540c00e0812108021801c5100401c0007141c031104110711118007901c5411070310304000f41900d61542c0e0f000200070041c0690386159140004000c1140c1031502c0d9982c0e10480c4400b41003c06180d2668a000985064240b00426210350300402100c04000c0f00001d00c00c044810f48014205c2d000203c58060303042c210141c210101c010f10f00000302008950580016020f107020307480f0143d09036207420040403013501501c0c1c07840d00306603c0401000054055030181d03050007441e180000b00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 377414379 1250 377413129 377413177
    0x222d05010e06190903061107020a0504021b160611150c09011e1d030c0102030904180b1306050a1a01080c0d06170c09060d0605060a030804060201050907050a0515 71
    0x40003049803407000021300c0310b881402000001e1003500884030341c41d4030b40d034200341c003550003c1e41360603c2e400ba0070300807030300815450b058542c12400d1030284824841600c0080040c1030403440906007522a150004100081c00b4103031100c04204070030280d001d0303659604c183d0341c0d0110004082c1d11032448541002201c11015030092140c074101c0c650005155100202d0101e00c00529500e14200c50340580304c1d420110140c502e0340e800000b11b41802d001614089100800c00c1c4444076240a60b000241802c0140420046d031140c0c0040c07044445482804100000d484c0d810000007111250910414180c005031443c0b9925809600d03910751248009007500e00c0e01c03103a400b2100070755409512980b4a01e01c00c0c99080c1c03d460302840051403450054130340c0c01e04c07442c081300083c030800c0554a001e0001035441020070b0031900e07003041c448050341e082141c0c40d03600c90359240024002d000032183c0058a00602c5000b003028680000200c046410051034848011440e4a080409a102d244020800c0500c204032001c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 377415629 1250 377414379 377414407
    0x80d050c0a0b0a0f0605010f051b010b040c0206040303200301031b0515090a0509061c032d030506150a050d1b08270d050a05222d05010e06 61
    0x407107500e102c0b60104400d0560413035601900c1c043c0d0000f60500240d180c1c00c130701c00c0d0780c0002541c0318800820380201d0f4107420f4103003080c01040140000d41e001410507056800c601c0e00003400c0d41c0038034440d0380c080005040800d250841b415103000e0700100f04400300010400714110091464000c1d00e0388503920340c2141c9d41c50003c2c094084c031505150814401160300000c1c0e16100300c44600400041d1a4080702e03250000c0014810407010a008580002ca640c80f03400b85845410113004588a03d4a42058103042c1b01c90500c3d510005440c8400282c246000145617090204040c1c04480150340f0b43c03801d01c0702d00d000950701500482c0c01c000034180c1e101c000f500b14029241000341004403949900d244c0307003011800d02d00701c544121300000c0120341306444081540c500085a81c03181c0398a19146484194a103c1201c0754410341c10590030602686034110440b104c040c540d20b04a5500788001a04019100041c0c0d00042007400e10030403040d01068208155409140da40d05c0e06900185401e06d40320120100070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 377416879 1250 377415629 377415631
    0x60601020303151908100f020f0301060f090905010315060902210601031404080d18031205070e13060602071a030105330c010f090b0610090801090818040501080d050c0a0b 75
    0x80317154003441c04d80c40c1c03080c1e00c2d1148251058044a040d440c05c0c20008640c019440184a04410445000c03c0f00061a02c60442040038000601007031100756500c2c200f0510800710880f10b140e0580c03610390300060001040c4211040300500c1c5040311054000925080305035a00100018185038079a150941c10642e815042480b03640b05030b000d25103544010410408540c261f407108280c0d010a014401c0c0425040318501044414203100030500b5603460b40c04440c08941810450742001c12508003d110460903000038050380c03103e6003141d440359a926008403510031030340c403800f4038203000304014401400d100c06051407010750205250001c142a501032840301018450740d03000e604020440031050340b0280500c8121002c01e00050200314255120002150009403c191095180d240c014421030f008a9004009000b860b00803c503200e01800c4c1024641e101042442d86880c4039904940b10b8074080c400e10341601c0f01e010050490301118881559241e000c44015001441800f84181c0003070b4404642e1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 377418129 1250 377416879 377416889
    0x11011107050312070e011b0302210a110303130605060a08030c06040b07080c040e180111090f0616020915130e0f30040801060b0310080606010203031519 67
    0x310b40e00e4002d0101c03604543d201624600802c8a0003081d20026a480000000301c0160ba03404c083d20644580740c10780c50048941c04440c2c0d4a401a5960343c00840240042c01d261310301a168001d13140046a0890744070b100850340400b0095100000324007003903250b8403d5a00900c0a4440e21134951103683e4145541c00182c0c0c0fa45042c3e100200300010421080410f81c5c0041c0b690130900d60604025801da0028000c0d80240e601210f40342d00001c2541032660302c4050000e202d44001c101d600c02e86960700030164170060f4120702801e503104618042d41000030489140900c00002d40c0c0221704135608000502401404100103a02c6e000e4141020b651600d080c414880219000092032502c5120b4407800c191005500203205d401204540e4204240b2004e440a480c03001800ca181006014000e08424082c9070040d200d02e62030801d01003411814200250f00900000300e1440805964010075035482c90100c451500503001417020034403890f0750159200307840e0801403046100c41c0914076078502e0342070340e81d03c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 377419379 1250 377418129 377418133
    0xf0301050f1905010e2412060106020111030c0912070b13031208130303051009050a06082112060d150603140102130b03090f070f03110f01020a031101110705 69
    0xb0701000d681d00300e000418040e0020000e0156601d040c0d50700030015001024502c40c448506a43e94002604400c12071480c8002400007400c0303490482c0c0d003642c8200900039071000d0744ca800d0144a05d0b00b00603041e64481c0910405542c5400300500900c4007d40a080e010b0a8622580d20049415031615002e0305004425901d010060361650402c0c04c51988090300080c1886069070600c0006d0788090881d10503284c1609001c20603440d101c440301c10020103a488141103514150034000044116040003044070340960855001c0b1510241c540552005100001114042088030640803030f00c50701c8250380200020040580345805490340c140b854240b034140708000c2d40d50b00007482000710f81d900d88010a6400c4000710306100100564650302c00e158003440b0589103010002800c050003c0205480900315403040e1091244d88004041202585010494041007011103650b540c1c1070803003100f5030040c0140d0081451101a4a040c4d0340d060350046040070359501d030580d005c0040709040c01030440910802c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 377420629 1250 377419379 377419381
    0x90809121908070b0703090206070b0411060d060905010e0108030a0e040b0d120201050a0b18040203010b10020a111503060f010e0a1401090503010903081b0405030105040804030219150c020f0301050f 87
    0x14060701300c84030007804e40c000d040c076050b55400942c8503d400e42d003104d5488a0002500d80720740c1865040c500b0300303030040d035031017040050524020320990300000100c0b1000d503403e102c1641c0f41d0034110a9088240070b0031803035500c14007240031514400e6a21100103400900300150404034040416200041f603601030314104550788060041c1542403040c0c990140044030108a00c407400f80020b881a401440302c1031a200c80140890700b076540c00c0d4440060b010004000219500300b00c403002c0e44908045409035400d102c4250340b0426421320601590420075184072140c030b580e0300c030403c000102501000c002e04015215032021129118500c203e030160051a03042c0c48455510f400042c00306030142c024078001e90600a03a0f10000350414151a00000c414080314025083c0d81c0c060b100034016940301540c19030070720081c0428810300700020f20980380240d45a008510950750084d0b50085d1910444a015400303410f0900c44520803041d480328144020031580b60015100002400d40b2010741c0c40442c0410550 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 377421879 1250 377420629 377420633
    0xe06040909050d020c01120e0c06030414060106050705100e150906180a0213051b040f05100203161202101a01031b05030c09060405090405010504110409080912190807 73
    0x6403c010a400d2004205846102c40001c2900380392a205280d1241c984182c69210031040c0941d60284501804e007540341e10b032a043c500c400001c60203100f0010301910f800850100d1098044074042c50300f00b4001c1c07891021004854009251441c94862070f0f000e05203058032340c6000c9890540c040c40c80900101064140080d0700540007a8000c880c2e1901d61205d40311f400140c40d551414450580c100000084d603030b40f990b00c4058850981d44000c0010400050041005000d004000007522010b94002101f4000305030107903964403542d143c0200c0f05442d40c01d84800217080c00c4c0c0642d010708191058030500d00720240301005030fa0115040d28040061188a0b041a50341449008241c03e05140410f00b520440b03036000e0f02611010380300c0140d4240c0000c0d01038a6494010440b0000c040203040103800380760900b02035008110954003111070aa4408a1003c1480e05005101c4080d410400c8540748c10888001c0084900c0c0364448040d46010312a8507150300342e04030210043d40c4d4000d440d80303030b500d01841c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 377423129 1250 377421879 377421883
    0x20c1e060606072001230706140402030a062406200102070b011701090f03020c04060b1e090a08070f03060509011506050d0b0918010b060f0909070e0604090905 70
    0xc001c540611000c0c0004004241160004003a5482d07550b150051420040c00403a00e150899441c4140c1c00340300310b0340ca02803002a00041100d00d0003842d080001d101744200b200803456050724060350540c0840d41410118669074050314600032050314034040e511041211201d40b2200b944802c0105504800a8040079182c035502c00c442003010000b10f20745199071303807680c41c400b0060041c4d203d90003045c0040e280d000401d600038002c5981203240300318a0045403030000d43c0c1c1c2e000c01111500890a2040020744096010295481a0141407444041d044a0120400da58105282c400e6001103591000200d22000b070000e1000340c07500043ea51101c81c21420f100c0c041c2e402c042c0c00105180c3c98000c041c3d918100c4501040103030b8540340344c8a65aa000900207002400030490700e198030213105d0050002520300d08500c0c0032003907031780c100030300c6000c2c0c42c44200075840c0104040a203460303104001c00580c03450103407000340e440072050400703103800700701580464040c1d0465040340c5c56155840348550244001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 377424379 1250 377423129 377423131
    0xf0f0302090a020c07170708010f05010618080c010c02040f052d220303240810090b0105240d02122404051e0a0917040608060603040303020c1e06 64
    0x20b080c025454154a600a00c4d603601c000e00c654100101da071207a544000e60300340714000040003400000d00291082c03440050040c1821310540c80450a071802c055120b801c0031145c1d00c21144003c014080800564005507500d01a035401240d01507a24450342e2a00380c0d940c07140c18010164203042c42403c142400e0340381d04c0300782d1401d40020701018840c03c01407111090a0f0304c0d02d09003288015601c030344495141c185c000d01140c60094407102e00c201c018000701101c60b4800c0084078100c0084031555942c03008854101c80c043c0001030720f00c0070f54100500c0326040c618465421030f0444522950554000114580c0d03e0300b051104220f002c0d00010f81850143e0400041ca1b04807149407a40312286d0340101c40200060011004c80e0f015989580000f0036046183c0902c0107880c0204510b6041864240b514000034000148201ca10580306518084441100001d50381502c0366612480110b455840400c003003900018004c0b002c05400b0040020520b100f8084c41e441300c140711200c02a041c0203800e8442c01d02c3d02c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 377425629 1250 377424379 377424391
    0x50a060503090a0204090f051c0207050105130b09010e060f03060103050105060301050d022b08070b0c030f01090b03120d0926072904050a060c0201050408090402030604060f0f030209 80
    0x1070061100000b004544035800d10b5040ba000205145980f500d0440702880f03c070041c00a00030611403140e00501c4055803210745096500ba108081e4841e001918107001b5800d4848900d02d101c902440200f1b0850024441d00205043c240c003903d804200040855000200e0103a20301004010b0110b1941c16000341405040101c031240d0031981000042030400b0038002000c5d10618070621000041c5062600c00000e6001d43d1010440c4003600e401c00d140701d984029030481d5034400000001e0744c0c1078400020b5900580f0342c40b0b03070304c1c3c07643c2d18008a80c8080c00b0a1361085070b040c01100c0c403005801011800a0041040c03074030000c00d41c0752560800d00c2200c02c4d20000643e00780c422801d0740c000141414105c41c182503018000382c0404408080080e0705401c00f00e032400d40c503003030700c1c040c0400d0000000b15010741d41c0c45500144454070101404034265903040d2070080800d2400e1140007214603086c1c010719400350001d000014600d82c0d610301c010014026920080f8070110281060082d800c11616031a4420 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 377426879 1250 377425629 377425637
    0x110424211515110d2607090e010b0912060108060c0c15010e061c030905060c0312011d07030603020108271f0b060322030203070602070606090e0c030604060c03090516050a06 76
    0x50b82402401440412545d000100320100a0000740d000d40200454006403842c044c0201103980c44050080042d44203c00e00c1e840780706140c2c0710f80c440c0c903400100707a81a50b0f240001b51140f5114141825031907081022510b044e4007030800c140101a05002c4104d000741050603d0f0100e60500342c0a101c0300c803040300b00c4942e0040c0000d8201002c43d4200c44858219101510881d603142080460b8608601445088000c0703201c186000180d04500800036010034010540003005170344170000c0a4044074900d100082c08a8070440001c4d180c410b1000d80c070445041080c1c9102203840e1945521820b00480c815000001c908050035030300303452054410741c0f50100c0c083c1e84080c9141400c009a103900d409130340702100d841c0c1c015208402058821f0081c0d58410398400c40a44d11500e03245840e10107800d42e40a2203100c0ea1404000520034007001451341c070000f001a0190085403510f0305d83c2c80283c0000d00c0d0300410f1580710129000080d600304243c000310310080d05183d5130182010208144c00c1800d0348168100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 377428129 1250 377426879 377426897
    0x51c0224010e0606181e0a0b03040204050108070608061c05060f040309090c021207020a030b070306030b07052106150a03050a1b02150406110424211515110d 69
    0x10480d103058030881c8500c129840c40881ea1181201813186c511001c41d0703904480b2048000440d4090300f405103018903c212007e121980e01c803065243da5007910f20800d03001440410105905040c00c00079080349044400031013140c01440e03161203241c00801e940300c402a40c541010002416400f21390400070380030090302805030300c60000c0025622004407035a2018030390005115005c550781c055a02d0029907001503800b0092403e0780018000749484d20080d1014107030000000e20087c40b6000b2a14031484001c6680d8440d034601c1c40e49403070030400400080d044880c1d50900c011001c0c5020142c841040c0e00c1d60b022680d8901825800c05550040d15042e607600c2001303520304080e0740c02058500c5044205048a20b040c1e4a41c10081e014000d01e00c841070610f00c00250110304001c0840404558280b03030145000c0480701001e0403944003555a030703603a1000380503008040446601e508007015210304140120a0f007616104981d08012400c1954800300b900b21400919404080c86042d0490a0a04000c400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 377429379 1250 377428129 377428147
    0x20c030c0111040f0b0c0f0f06070207091b081504050c0702010909090503040e1902030c0a0810060e060d0b04050a090201020f03070224070c06030b031603051c0224010e0606 76
    0x1002e01380c01204000c60f80444c820102107820070103400c00206210840f5101c4050300710b4182c5403202075540d10014010460080b40b03106181c00b5440202501d0740c4046200751413200110741115014011087d4808140180b814541d9a4001d141c000c0c40203143d803035581c00320b601c0003401404455200d04803043c1010710140200b040401a80c04451a90344e00d540288d84a80e640c88903003440f00002482c203440030041c80b0403106404041d181488490f11740d00c901d03403210204160044014403034600062042c54842c02e480c00d091010b048100e84034100440e09207100400102529003c030f035600c40907075454480209569042110001c126951005945445050b030041120f48582d0084a004d46010050000040c2c010004546489402032240d01c03901c0d4482c68000d000e80888100740780300c0d10510689204003100b00c0e5501085036440001811000e00d40c00b920117804c02607003000025401100c903c1000071910318241402030a903502001095030400030015255400904070070300424050040801c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 377430629 1250 377429379 377429399
    0x20a030b19091e0c0905132003120c0109050304030f061d060402010305040f0f0c030b010b0405010903020f01090b0c01061d0705090103051515030105040b0d0b010312050706020c030c011104 83
    0x20026074090310000300742d43c1c500307002240201a6200724070851a0108000e80c03804ca44d03450703d21652241901c12030340803950310546220500d1700e407039581c5608403401c1c03000722008140040c880030368554000f0070050865203c21742907400a500540c1c10305280b00ca8141005050b2280c1c900385883c020718254200041c1c0314682e565800140020705155031080420188042544038405055000403401d108900e240303812070307000c0340500c000c440700c500c82c0380040b46a103448800c1e1000d98006a580f84429451030b02000b01690266030054144030407480c020500f00300c064010040240881e0022840c43e01d41140c00034900c050005c1c0301c00780b58801081c0710344294408100c0d000100c003403170007103440d464025010250030701e01105e05601403040750b0410b2402508101650495104480c02c201080116081c0020002e03d44002014892400300500c00511501c1d808250004a4607101c1c1c285019941c8000407a032200a055106500104680d0048079003409003101c00440340c21041d041070724150000c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 377431879 1250 377430629 377430653
    0x40f03030302181f0e040b1810091b020c03030405060702040e010e0d03060608060d03050f0c01020c030708070516080304050409060b19080f0106030b06010c020409020a030b1909 78
    0x408154002400d02c5280340200d0f1a460a6603008001c1c00d49004e1884024a22413540c5a480c0e0202c0da5644124200f0300d4a48a06109030714040c09070302c2030040190040ca441c0380021f14000e00c10050071000714004030181b04540e400540011051031050362200302a240102042241780309600421091002d6240c40f01501c00290b03040c0c1d00403d2002e50f0351001030141c4101d44081d040c070310070b50380000c10b03080d45600140c0403900a40c4600801b91035950600c100d4000703212018000c920200b1040f40c0403201c0c4c8008000c14840f0302d0005003000b007568800c40c2580c0c04000280c03100c0a001c9810350903c0020f0103856100d00e11100b00711a00c2c0e103480d1845480740070318450284103903070700c0b4404020b2003100d40103612000d20084c205102c00000704032401e81c003c40c501070004540b0810f0314111a900b4140308000030759411880584041c1d490070011595401f0000e41240c029803514800c90058440c00d803018040c5101c1d0481092903c0c0014400503001e10003424107a52501308080b03900481e0b1302a03818 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 377433129 1250 377431879 377431883
    0x703030c02030f01090822120b07091701050403110105060102070902090316030c090b011404050405040c090903020606011b030905060f0c060414010b1f11100c0302030a0b0303040f03 80
    0x894000415000083c02c0a0009800520650074404034404103c0048014025000d107003450890b8507085e07407516842c41304035029001040c03d4a01c40d040106509141d0a179001d40c0d145840c8041c0d50b1121401006011484041b02c4640e445409220170140c028002182a003c5480200807038544680000e40d2140244980e4008923800660700781581c03028448035403450098511040307071542c5c0345000024581d040c86a04511460500e0902041d03104049070002240c915903141c2c00c090502007000010040a001101d0f548540c1000141c060958052554500d000b44c010341f00d240b41c190009004201100c0d503480600143c1e00c082c00c00260089404c0c41500c00654941d51034452213040c41c070b114030958403051200c1c424201003200b048147c040068056031124028040b00ca500b00030300c5242019400016440420712064840c010f21480e00c0c01d02c501d080d03100300e42007540c2c001c1004c8100c442005500c400207400004100d0142241d0048111400d81075000f5480c0030302e003511298400703843e8040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 377434379 1250 377433129 377433137
    0x30c0c0b0a11072303041d1302040c050c0c010e01090e0c0d09080a0f03020f0f0304030e041803090b040f061b12050307170106051e0c0d02070501081008070303 70
    0x450041565036001c6160b2050308180107560700c0c01400c181c0700c0d10f01800300b0b0001074280030040088505012040d41c003111302c6403c07002c00b6440700c00700300c1c4c10741c0c14014600c2c030203c03141e85552170259545001e80c8000b00000d4859540d941c541c0007400d800c145602840718180082051000310741d90b40100b526044482c0c46aa101050b00c8889402d03047d48500703400d160006007080003940911000c20300034080c920b501c1d240c034181d0000200c0706609902807948200c2844c5410300c04a64001400002075a0080c400d207404590003010000140c211303004420203461084014036110105900042c165000c0d004035003201c2e003030500e40031070306800900a0081c8010010410f140f40502c0001c80c42c141c000035800aa441c43c0030514000090154100700e903480d002400c0d01741e603240041080400030b03050b500c00d55902443c268030303081030210001110203201d1007818108110922454180101200a03d055000d421228942000113000d000013030f01482c0641d00300d05080251003800240785044a5041c10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 377435629 1250 377434379 377434381
    0x3f122c0718180804080d02070f1d0c0909011410140d150b070302100b180c030c0c070801020307110d022107150b040f180f051e100507030c0c0b 63
    0x2071019140d8070b0100083c48002c020a010a0601c40491280418009079007115041e07561070f40345148c04031103841044d6200c0f0b03021091100041944402c99072103010381c10305501d0500301c400841c1d0050426884148800c50b40d00341009545051055003500c03007110324120107510307001e40d0941114400c0b45543d81d200e950707410790361090604440c8850010710713100c0b80c082e44034140350a000e9120710800f480820fa0900d0050421518a0400c00042140c200740003002515a603c00001c201c9a0001e485920300640a002042c090401040b005003c0c00e2440b002580368107210002400b03031400030840100d960084900c803c1000c5d800a5125242c0d1007404580c03030051440c44a03034900d4481d264021b801c490381c42d610000707410600d40140311407000c1075804101034021542510700300c03042c07070705e80c1030350000302040c81c00106070070361010341c42a030180c0706541002c03044d011500c601e02036807980c10b00c680e000340d606a010409540318041c0d0007502d50a0501411170740e49001010031821074001000100200 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 377436879 1250 377435629 377435651
    0x3020f0310080c010c15051e0406060f0e0c0726070311150c07080702150406020a0b0108030a0f08041118040b250c03091505073f122c0718 61
    0x230070001c180f403207030a80400a003040d0034400041c140c98020340702181c0c204580003c040e85038580040c400c0c101c04e10b105080002996440214107503096284081c480000140e00780c00480070010f0884034400e403100c4188481c016850341c101001d0f58180101402074078100301e055000b040480f0b02555000b0201a61070180f440054001014140300c816000c90200d030204080d50001a45408103000d00e4040c00a80ea0301d1070500e41d40c1c03040404800014582441c3c51003207901400025030403034400c802010107890903801003200c1b2450712906003100e41807070040c031080c82200d80c0c055802208030a80d030b0002c1c141406200000e940203a0320002000101103000041c0b5129400840c0904140e1110708040e520501d40104160008007060300c0400480a0003070280260381e1110030300ca00036a814803100c2e1303190300d25201d021070401080c6060141018000b14840c3c800e20401060809401c5442001082a8050404000301403a00c0041e43d220910901000c0e1421070184c010417103503c030109070a0080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 377438129 1250 377436879 377436901
    0x4061107030f0b1e091c0207030501141603020c060411010e030f01020418021801050f0f040b13080604030c200d08030a0b09070804021003020f0310080c010c1505 71
    0x195102410b02150311011104000c404211540507000a0441c0c080c1040a08112207030703011300f940e08a2003a48600d0340d0262042c50842c000108008500513204d4260780c1e510385c0c030300b5900310f1540100c040750780c0801c00c0982c1c4800508030202d800c45280c21800d0198101440da41c03100068005841d03d84401e0240d26160f00c03c0303402c18200700d400303002c1d1000c0c0442011402e0103900140a03408944240544030120042e8910a550b809120100d2283c0c10249400054486a00c00c0d851040b6542c010050b5034404d004080c010f100a003101c045403a136445201c040c809502d01b04ea0000710864010038244001b0950000d070f410703512600f0070524502000140d62845482889950040c0c2051301c034242c8006002c01c050165104044942080c44106d8646003084004402191690003156520021501500303025111103540d0485040c010300c1c081290101040682040340e00e0f4210000654090000050500090344001d40a00b00841c14140300c0c0e40764038003c21640110b02d1819500c0001540d00c0c403503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 377439379 1250 377438129 377438143
    0x9051303081303080f06150a09140f150706090c080f210912030903010f060e0a06060f1d1f090801020f070312060b0a080f16170603070e010603060812070206040611 72
    0x2010380c1c00c0348e54514804000e0007540d8244540051800d810140440302c0c2027011481a106c40000c00c0003890340741815107089260082c0760207407140c9940d00b5084002401e0090f040001c0c00e207800003001c500100c020f98518040c02901c115031440c1c04c0740000360702c00082200796808a00700b141c0840d07207036501c2c095a0b4558018854a80d5140d030030040c14065a1200e0362180d000d42d91f0a2001480d69a103468001c0251215403103841c000855619560400c24412400c01e418051400c284c0ba0fa40c40b90480041c094500c40c00300d4070f6601c0d4904070386464403a000300c80c0d140207003074560080d420012202010400c0e03000e00342c405014401d003200700c0c80c5071001e241c8c0000050119094110386407808802c004010000481b03141d410046007101180300360749502c2d8000110016603503035981d0120004014000e8050203004160144038600c00030552104a1240602070710069400150076407a200442c0c0c50304050503180e02040320b08000c00f00144e2207481c100c9040d640350341007142450030a819160701d8011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 377440629 1250 377439379 377439409
    0x9010912021906030c0206010803090d1506050402030708011d04051c0203120a020703021006050a06050d020913050601020c0f0a09021b0105040c0f150c0212030409051303081303080f06 81
    0x108006011a0b1581c0680c4034102c00c07030891b0b085400030381e2601c0d503050307880c812071455540c0003020880381d400090405840a200d1852888045113081e654004181680c000303485200100c0c489900500100e01c1c143e000350300c564041c05c5404800d0405841da035448050000b0040805402da555400e4103500070002c4440141c45100d03105000d10340010014000e4202c060b044006000342071180055200074010503058038802403070300007201d03e058815503499016415590b0b400c0e03024000c170007250350b0b0341c1050f00031400081e1021640e071030300c80d00090902d1104401d491085100b01e41c0107000c0c0e151003c06405903a040f420042e586d00c440044800484181800e4011540c20b103070410040186402006040f18410295140130945482c0c0078110b1407070450101000850f025085000340c82c1007180589441c81c2d0000b513034500350702c410a20302661411203043d02d00203005c082c0a410580d0003140c0710b90091084003918421445070f40e0003007041201030484140b461085001c03c6071030351040b2040d24803031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 377441879 1250 377440629 377440669
    0x2090d020901080a021009180203060f06030403090603152402070807060509010f080910090309120305040f0f05010f080703060b1b070503010507020a08070c0e0903030a0f020901091202 81
    0x983d460101507500c1301c030b128040740510a6288041181030103a02c40d4030075120010020aa584419660507009410041c48182e000e000103070313010100c0e254134006600890095454103136090800c0c40107801d40f003047c041c128006010340710800030703440c181002c1c0c050b0040308644034100719010b032030403803a094030343d000440d07a8090400d000072410b41000040c56210000e0700c0340395860080800580e4102c0007181e0b071708580d0b0441c44051194104660040003064441e0401503003044d2200b13514250740030002d600318042070780017030b050095008403000c2c8002001d0003803084c52417030b0501c00020160b60a26100005101d040b00115440500a0300528041d1124540d1241c860882c003844501c0b180b110280384d02240a0383c0c1c2c01050030306041c06164842c044680007420704c0380e225a6660342603444804191007220001c480494015018040140140010801180c407400c24585040403540c03c0306035400094070401c24159141d0f00a10710100312108103402003048001c0d4008070748010740c035403d980500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 377443129 1250 377441879 377441881
    0x1219060f1407022112040206070303110c0c040609050c09010819181e05210c07081f090c090e1f0e0d020c0d080a020a1e120c0b0a02090d0209 62
    0x550750004600400220456420740e200c130a441903d40c8034410000b0400d60001c1440000f03000d0309000c8001e1042a120f4038000071107135407000c2641c001d6040301010304040d03003080428010074035003406440050f055400040055041c54141d118081c0720b5a150306042c800b030040019001c1100c007071070a131015410602481b000c510901580c02c0b010381d80d9400c445400d02209000078a00d9003076011600190301c0300c02401650043c4e4003503000c80022040200d4800000c020000545c00103001c07000040c20640010841c40040c401e5811001281e0300c4408030842c9032031f1041001c0f840700c0b540c84003200c580810001d130702c0c00019082401c150464000c1403501e50324a60f0324044026540c0802c4060b00d03c50156a180e004203e01242c803142041c041580c00003140001c2e8011501040041c003030140180101d528021840d40c90929040d200d07021886010103008100051011114100740c640c9078910f0561100486030340d03100301d44480508880602903011480001545502401000c041d40040c0741c4402 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 377444379 1250 377443129 377443141
    0x6270624041d0a05070210020d09050f060708010b0a08060d020402041508040203010f060b0d0f0b0a08150f01060c0b2809050c040209030d03050c130303030b1219060f14 74
    0x12018401100e14600b0440030006994080c6441814051a410780c040c10b20384405032002c8010b500032504620900b03603100d0a00000440420440c5000b4820602400003483e180307070b000d407071100140d0009082000800c00c051286c6d51007414680c0c0b15104a60034501c440310b9002040090086402200480c01041c0300904e10540005080d8400d6100714002c2c010004640b000718240c4640e40301d24110201c09000010b0341c1000d80d000240b51142c021000100307904c09400017005130643e544204140c0e004005480078404145078481d9120101c0d110224070b9504d0504020405015004044d00c0d40c15028089030b07040c255105680c0515101001e81c8030300e070b480080684000d1042603c112254401e1000240d100e06190003500c1e9041d000502501c982e00c0d000009030701800005202e015004030802801001d011094100d001450007640e0004154400c0b40030300c4013032a44c0c04944001544500030043da00401d0000d0004070f1544818003046c80b5046200c9000600001010149940040000c102d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 377445629 1250 377444379 377444399
    0x703060f0207021009050117250c05010b010912021009150f1107062c0d0609060e06011a09121221061005071104050f0627062404 57
    0x1c2c103000f2104d4280c005200300043d1095a510300c940d42c0820203485d284000c0c252207e007040c1c1c0c4140d00e1a4005104043c0e0324002c424204a044944040795102a40d001484403d10820500c09402c1c28015000e40c18034540d03a80b10001030300e001384100000c8010042e06441420b80300000c0508944144540549000140030050704031078410014844020411580c8400900d003001c403000307516091041494212505a0000b201c40742c18171440e041e002139040c68440c0c2020302d10700c82c02540c0004001a45180000544603810280c100560140c80140241c0340b401100c41000f040c1041810390b104041c2c408242d00e1110450039500500034600040020302049000345001c1c0c0704080020203400003a02d00c0c0c42000420f0f15942e803c17001560901080302d014200a0002ca4080c03c0c411500c030b908100040e081c0c0f81e0841c1d01c83c041101038800c0c840303942400310301000608452a074084010060007103003820380320020b0800703111f0041c481c04009141c42c80102c0d11118688a42990b40e44c45c0c6911b0708103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 377446879 1250 377445629 377445637
    0x9010b030d120c02063d03150608060f1614040f141f080c041e0513090503030f060f0a0603050919050a0b060406170c120f0601170703060f02 62
    0x5030b40a410031110591891020800303034460031903ca000c081450303454502c0c485451007420308a0345080e010200d4004a0080c21644000714030034080001d12080c42c01c400c4042e1806039020b5080c0380d22502c280640c18025a1040c0d034004c400c40d60b800714280e00c20104840a880b03819440150620008000c290305145603420000d48041c0540c0b03100305004242403204038000da0781c1030215440040c000700b0910b07200b2098640c0051400c0d10341800d09840c5c0000301031044500c03020344204d001c3c03004204158140030000d240072040488003084132169a80720141ca9100c01000300720b20000410000c1d441d541c800c072000d05010301c007810a1020b16100d00d4068010701c0240c1c0d140c480d40c03080150781044103901003000880194002c018214000b40c40c0d851810101000d802c4962154489002090041858150710074140480e00100b12140300c0e402030141c7d070b12040a0009803908112411089980006602c40c112014a541d05040c0b44e1807030005802e0107080d81005080604043d9101000c0f24960050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 377448129 1250 377446879 377446907
    0xa1d0609060106020d0f030e011508011d010501180e01020c0d0f090f050d061a12070302181608070e1e09061906050c0a021f080a0902060f0309010b030d 67
    0x4031456621a4030607682c50305001c14000001e65499201e0074003074400c4c0c100040c009410400824421010690310ac1242165000340b03000c4c2c1c1d900c11b400481c0303100d00d6140b24801c40d44039000b08610f505140001105901090840d030f210707034a413410600ea03241d0940c100d0f203a00301d050040e5400f8138250301b0300800030592409140300080d445000801c891210301c1c18401120002006503007104010396440d00640b1481c03802c0f01c8000e00d01e849200d615140c081c00c0918103180316002d401002e0071032040040c00f5200000c0c4010081290f410004821030324400410100340900f454280c3c1e40d10303001c085450175a18101c040c0c0040c43c3c9100c8214000155168130010740046804c00500e80d02c42084c40303220f207111811071854007142c8904010840c0030300c0051485641d09000d0714006080d54010030199100c124005440c05162042900e2042d440441c9503004000c0710002d1000a8082c2c0004d181c1d4003e41412103e08038002000c160908001d6101700701040d400707403d540301c0e0622040f0103000840b00e0300303031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 377449379 1250 377448129 377448133
    0x220b100e0a0c0e042a1107081603060504051906050a0c0f17092a04050c040f0302011206121401110a090e04060e060108011b0503010605030604050a1d0609 68
    0x4201c05440d9800798000c0002503036079049403080d8240401015050700003481070400f8510100d20854540202c541d04407400b15290188160803901841e807404103036900000b0150009102c0b1f000603003030900004212a004032002c51591281e0400c5403d010711600910340000d59486940f0801c0596003005101d0390003400c0c200b011211100c03058550341107481090000807070440740403103044903d9400b5a00710002d0350031607140c002c200184400d91800f162101c001d00d5110300c030000803440d040c041d00d40d0000780700405030b0400c0e05c0d10114080701685800000d06008050120b80001c2400380d10950090024400c9121160880d0424a000e480c12000303800440d400d050409241c14a40411201d642c1415503c09110510b41034151a07054000b80040318443d403600c20003e2030354810486107000c1c2800d03500002e010f0085864040c805140044410706210303003400108082038120302070781c0d4402026240401d4503611151050001c0c102c4107916409808548031645a0f0700000600c540b0401c10a41 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 377450629 1250 377449379 377449381
    0x5070b1801080c030c03130501020904180606061b062703030e1b1c0602090a030c0608010510050301051306050307060f030605040e06180708010504032d0503220b100e 73
    0xc11200601c0115112040170a04001180034954a4400c4c86413045c040e600050401400400040541e01140f043e161070625a081d2031007802520300c1003500030142400d001080b50f010191880062070100d902400880e0350300c0c2c50084005515a500740400d811300062075041c0e10901d405401040c980448061500c604130070303c0800903403004810110580140000b01c40941000e45080d1925981c0080344c440382c00340821419a122400000069441030060794180c42c10f00a0050490714142e11952203441d414006141345a000412281500c405072824401a81d00382d4061001c1c107425440542c15114000000a065901c820000c4003407049650501c00c05550344108030a032250911401c1c01a002a0007242610811355451035a03408450b00b6101d806994041d41800c492088030281c010a504180049044010080481c2103d0703164041d9030419032074100041282c04000c000c03851103800301c1e140e01ca01e032503400381c001c0c14646d02022075106450709100c0f80240e84c140d803103001c0d00301031040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 377451879 1250 377450629 377450641
    0x6030c0e030105010f0911130b04170604020d02043813020c0622050102030c0414120a0b0c1c0923030a081305030c0a0308100e040f05070b180108 64
    0xc0203240c12980305001042c1c00e103040114001c010308180005107c42202044903101902d1078010320b03401090f81724003040d1a40d1501c408082d9810101c0e4101010b03401035001c000060340c45090017041030390103030303000252007412039224086000c2c400c0072402e6250f12950000401040080c030804140025241042001041c2002c402070f40550121513032280c0208001a503904405110411078040d2412a184201507a803205400c90b4003d031041803448030f00003410b0060070b00c10704c1d00f22290801658280f4964a906102e16128000b0002c003c020545010202e10580c2040083d60b400d020700d20589004000168680c40050640c1c003812038044d032851180b002c1100d90034500038203520080c00558a880300305042180d0111000346a8801c908140c140c0c540400c00c200007404140d06804c0c02003002040c142406010100007d080412010181009202c3d403521204480e03045503000700c44a0940c017041c6420790611016400c450040701c1d01082038002c1c0303983c6403118459481c003a210300c00c50b9113030304d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 377453129 1250 377451879 377451881
    0xd0c090c050903060c0c0a020d0b040303060b04080303070809031c060f0515041203050f040306090c1703090d0609050f0303010e0106030501051e0307050303040b1b0c0f210706030c0e0301 82
    0x40b08207181e142c0c200b140080c41d400c1c0810000c110442c40103055a02d091029800140881d400d070030103461a501e041c2c2080205605849050050000031a006061510b00030005a60b80300041501e010000408046148844100240c40154590040202c00c1c80e142c0c40344e0300c1c02400c1c280310700d01e880005103200068500780b1032880307400900141e021504d01070a00c1c0d108624951404007c50401c0010000c1c2c0e0145080840508080c510880e0046101c6e4110f00700240486c599400540d29000503022101e21000000f0803641189000e41d03a00c44d200d8100c0c10414000c000c1210094024010a4030380e50141c08040000e5041e01c04120a5024590320b44c40d04a0440d8002d004080c0c00c80c10007045117a210391802104c2480200040803951000e442d90042410340c0c0180e440500c10400101e8849102c000c030603d00c81204080800074030b600020341c00010070011244412501840c40d101c0740d4091124a4940940c40c1103400c01110a155034800000f001403c110340020300140d00e002c0c0c41d51541c501 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 377454379 1250 377453129 377453137
    0x161206050615120c07080403140c01021b0d0305040b0325080907060809160f09240b07230d091e050103020d0608070305070303020c06130e150d0c090c05 67
    0x4080821400c00c1050790215102c4038024080c8441320209000c2100003c180d14002c20240d4801c0705003c46025148180d10b181c0f1000304002c40c155080003081760f4050445803101d00046c501155071002c8801c1d14142518944915004007501ca8400400c220385164004030b540c03460440096001a485203000301100da82ca81a19181003542003281c0402c209881904081e8010118100b5034100b0031a002c040c80305480b203603002e1a40400820020000709209106411030640d100050620301c02d80050b160704043c140340181c192000011030303444180030729030340c1c0d0003504140d006c118444004141700583e074499001099000081400501003004003400244806140c0039641c0702d1200f6080c100150080d4109000c19541143c3c3d0b08400110b46800300304000c01103004001429034030341582402800d0061110040d4015001001035039820440221603000322094031503006c54603200c6041d4094100200e00d41d803030f4440844074105048c40030788210301d01200c80303801c0304105c0d0140120068440b400303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 377455629 1250 377454379 377454409
    0x40203070509090a020d210309020a05040e031903090206030c070c1406030604051807031a0a020c03070f060f022802010b030c0d111906090504110703050901021612060506 75
    0x403400c032440050400140391403000e48101400300704034541f0b80800e415182100119000686c4542808041d410040000b00103003406a60501500000c3d030a025035900c1200f80840d00c0051082000250912036400715240c00c2d8000e1816607241071424105405804c024016a00d402400c0310000f988020640003622503040a0221402c2da50b481c0c08120003000d0051107035840030018100002c0103007090007000041d603c200308441c00d5a00303010311060240b6004005102040c4100500c02c40d02c0d00020581d400740d640a10082182445454950050002d00006000e8140007290030410100030b800d10405c4038020106104652000d050200c2c00d0707500260446406403c100380c6910a0309040140c0240a8014100c00541100000220700000324030414160400c0070740b14144a45030340f1200d1030006000442d828030400319010030000c280c2c405e246000f000e00c08001249000c0d81d00a200525025201118029030b85a40d44644007800a00326002c55001e0b180c440010414035061a8400e03c1e25 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 377456879 1250 377455629 377455633
    0x70203040f06210509010204031b062102040b0406050306030f0c0105030601030f0603050a0302030a020706020c0901060822050f010f061a03091c0302281e09080a050604020307050909 80
    0x50318206095941d4145881c003a40c0002c903c442c0d00440781c42c0e50080c0c80c080d8461a0005a07650320b1420416507040b0a442d50003405401581c0400c0740c640d001000f200e800821010381e810428884286c00001e10542e0700407881c0d1040841c0000b8a5038210020794416407082c3e003a26035051850400b1511000421748031401700d242400484c81c00d51081e8413180c2e034040150310008085449448061405c201c60008400691000421064a81c0c5c1804480000c1c55a80002d0007104001d20004505ca64140139a5040058007400034002200d894072101d2200007001681d1080e00040c20226214402d45510800325820b01200906015040c0304003422540341e60003146080c030b61592806842ea01c00b619101d007078400d540d082010351200c203001015580503034400690302c1141080190071803480780c0b00c8821080c44000020300007604100c050380106050b500401090030080300c240d95901d4690400400c41c811403140c034082101c0010000d00680c002c40495100307580d5002001124030b42129005041c0d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 377458129 1250 377456879 377456909
    0x91f0c0e3705030106090f0e160639140d020c13060323060606030105010e0409021203070b01140319120201020f21090d09030b0c092707020304 63
    0x48807406200e2054602402480c000d990340da00002c1e095800340c0c1c21142415070f0384d540362508a00c1c14031844101202990281c0030917030020352140815000e511404091141030440c0e25000c10388210860041c038121001d081c0e1211248000c50001c2081490843c0d81070b1000c02d0a00c0b07244000240310b109056241c1c010101c5e80101d00500204182944080500300d80315103010002465203c0203080140a01c1c0d6400100002002c0851510304090032050142034200700500550740c0c04a244146090140d4022440100b20320100c1e1614900d10345609080c040401d040c1c0400c0040c504140c1203590700441041c240c0ea011081640f190900c8502034294041e000054002503688080c50086103100c7c00014140b002880702100f0315800702e4a0940e05001c5603100c16802119480740b01c0d00455190010000c2841c40360006d0083c3c90346000c090301035511040090302c10001101100c2040c01e0181c00b440d094940303c8000c00201154102c45191400358000080070188004281c2d0300b2100b04041441c51 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 377459379 1250 377458129 377458189
    0x406050a020f06281506081b0a092c0a0b180108030a1d0604060c0605070305011a090303090d05280c2303011103011805150108091f0c0e 60
    0xc00344280c55240c134a5071104007407a910b1050020034001080b0f151a640b2007881c00055406074800d0084c400207042c00184031103211254800c41000a541202c01500515041196202c030f034000c082c440980b40031440800c00030f010440b07400c11a49607100740c94a200c0728100c45885181108240645600d0ba4130500030811002c0c85482c00c4c9605584480c07000303242d89080c8000c2821940540c008102207800703900c1d03002c03c0240034407440e6445030362407404010550400100c9901c00f5030301e8034a0140044081010307003950740c0034812503104540c02010101030851034a0100c1d2070384008045c400c00015841121030b51a1901e00030546850f03888280340030420300b04a07840c1c41101813908000c1d03a032501410840c40c80c0c0c40c01d21400100c8540c0c410f1007a201d44c94080c0580e600724555054851b128241030511101030140f14007110143c400342460b64199991507000303407030a000d49404010204011100e01200c902036400700c1c4c0702c88125900c1c440656007410501403a090b4058002005c07203481044840 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 377460629 1250 377459379 377459431
    0x1030b090c03041b120804051f0806010509060c061504110724090206160606120809090601020a0f080c06010e06060307030b0f0406090213050111030a0806040b060406050a020f06 78
    0x14890b100748a8034401d180d00d817074180c2003000c0c0382101240c03520000030b0148800d14064046440e0800180c001e0007410003d0000180b509101034400c90601c0404500c4100a6481740113842c0c40c03080c043d0440300385141601149e90207916103002c0038016450300d01e000e00b850344007004540c42c10383c220034095560180020314902841c0251105c02c1c510351b03141c5e200c40046c0d88240c01001741012410120300c9400043c18000e007181d100d03501007240b45c4203100810380041c2c030040964152a0080715025855550000142d08002030480e00505107074a054800d001c0000c000c01801241240300100d0740c9607a00c8102182d01810180d801c00ea100c041800000d210301e100c2d4000b44142580a410003469014080214081c5c820a4118240030340c0c0215030300724202000956100104000d01c2e00c05400000b0003030072900c0c0d100300d800715000c010b0028001101611150441282750102511480da102c1d5942c000500d55000919003030014098017002c42449480050003a00649a0020380c00240f040c1c1c0c40c04003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 377461879 1250 377460629 377460653
    0x6050d0503071118070807030b04061a0c1207050f01051e0a181202070611060403202a0103050a2d0f0c030504030807020d08010b030403051c0b01030b090c0304 70
    0x40c0d00501610340c00b11103012012444d03010b804980c03035002c054200030401074161400c80803500c1c0101d00d00750b803c011111506100707001c00c8914070540303076550110718201424400010503102c00440001742c04010081c0000b603218030050a00003c020a0700d8490058010440e21000c2403c507443e020080340c000d414542c00103408807655030301c160341e0503ca980e400e030202c1009204000560007110040040f9504000e16102412950000d4007040c502544d010b001c14550205602240c2c1c01d580c2d007542185000c000051481300e100b14842001e03640c0210140c2140301240150380041d0402c00440c000e00200e0150454541003603240364581071615407804001106070300240c614948070503001c040c480851081012a804c680d031b001c119441c01e0f0402801411024204504640c0001d10300b41c643d943c000030b1103065a260074a02a80da44a5003412101c1c0e0103030303802400d001100361101011207141c4e0b40c00604031050a88041c0203a11112007002403041c001c42c1c3c0400719280c200002800070700000500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 377463129 1250 377461879 377461913
    0x1060e120118032f06040b060d080409150512100213090509030903070b03040c05100512070206010f06030204060e040f060f03050d03111810050c15040606050d050307 73
    0x1c0b03000c0c001210b0640c01c078441c0002e03004105290340501304641a6004201d044410004020301403008030000d50780d4580080c000f90041c280440800c1103a41c8080b040280160424150340c0c4454a134010301c0d0003451a10104005501d0100c00020207060180d4802c030600d0303180d40541400444028040c001e5480f0b4410288208013031100844d0688151080c1e500541e414001903844400d00702c1410301e80101d81c0c0042c41c28100500c2000001180300301000705075242038900c01c0108541c1c40d0243c546000d112252001d00c1c0000c0708208030301c3d9000070300b01e0480322540403c02095503a40016022840390340508400034210340940e400300d08140e040880390f10440d16001601c035590311110740380e815071504110f406401080c20210300d05d9240c01032009890384d03240114a0050022510022190700b1345800d401a911102d04009580c0500256000544641d00780d444a4803802c100290300c0d02e0446085031480d24005000c101c41c00d0030120040096407103002540f40c0840398681902c4140800300d2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 377464379 1250 377463129 377463131
    0xb010f0c170d060909020a080705060301091a06160c06093203070e190510120f14010605130c0203030c030901060812041d04150b0d050106030503030f01060801060e1201 74
    0x808400d01035600c2103000800044c8070005030300c2071602c10014640d0880d03118024650249006110551700c080840c0d04680103502e0001d004865650341b0004c008561503030580c810000f240f1400d54100302c50414031b11710710071090080640e407101000c1d2040071310f5009480e08041e060940255450080d4061080101d4690b6407003421000800042e02d410070541040c1d454400ca2820303c01c41d6403003105849260780107540207114604c3c200380c000c0041c413403601c1494100c191000545043c01190000d03031003151340100c90401111440c2040714040c200d079208941c010001e2410102c944200c82c459010788025540c041c610350b403541c800c00d449540014246a00075503a034200003940d440b0410172420a00d07403401460b0b44440c0340120003500c0c2002940d003920302000344403c00002556840003004041d0b000d85001919503001e4010812044084034024001d603c6d2082c08010700c81d00202441c0b14048801e0030308136507138980e90100c1c1d0516082c450341000c20440b980c14401c511b860f088044441e280f000c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 377465629 1250 377464379 377464387
    0x14010e060f041103131b080a03080703020d05090d020c01030b0306040b190c0e0411210c090d0b0609090a03091a19030c11070305030729010303050903010b010f0c17 72
    0x54000f1942c3c801e42d0040700c548207030400c03c002c20401111202c611a05000c0071101a86040d001c5600c407032100c90024100040040010b1880f03009034180e865010007a2f01c204014a001030700e50355183e4105901802601c40c1122900c40b80d8428010710501e010054068002a00c540d81c410b03681800c040c002d004601c1514844d00d40f030741c0540c41441d60004496480c0840c01c4010014001212100004160001c008006211034105552801280240a15525020756130f49081c015600e0048039989039015011a0701d18081c000500700c81800f03003c04491790910790f212403524913a20702d402c000003408200300e00820400c19094084c400c0d070021940040340d151810004070009248a141e22450200c0d0755001402c20083d8030a4141c0300520780752000344507813030454540325079a0144420042c52118010444586200c08101440c00518510111261540c40e49000303480d680ac8004141c0c0690718000080f03800b076200f04180404c01c1d601e5200c240b42d01c00651540c41c51030104031034500382410100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 377466879 1250 377465629 377465651
    0x7060906020f0c0309041b08071116080c03010c0908120307120e010510051518060d0c0801030303110405060307110f0613060608060106050f0d0e070e060414010e060f04 74
    0x50014080a52081d01442e0f840000c0c0c4200b004032000f01400f10700c2c0c141540381f40391105802134180703070300080c15050200006031101d03245860310042d0104070361850300c6010f00264001000441c4102000114024447e407a8440c078200c400c0d00103407080750030b07550052001854124802004507082405850852909078880c0c109900352150318080ea0b525130354510405c811541c41e07405400c00380004403400001820310306036014940c050a5030020300c0103008038503119260b4032201120b0085400c02c03070911401a4505d00178140307040c00d10003600840c0c00d06401e9509440c03250111026548000c03c81707421030b194440110341c4156030500010700d034411003149045010f000c103c00c0d88200f0b00109610030b0201c0d58588142034a1580d0b001206a602900c018400f0030b4214080d035030315098a4480d01e40307852404208070301600d48581061142d0045120200301d54510003c258031030300042d00d080c0452052035444082400091060100d032010345c40110780549417401c1c28500d041d030000c001240d03500f001703 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 377468129 1250 377466879 377466907
    0xf08180402030412030e0a0201080105041e050103060507110109021e0f0a0801061d01030c0302010e0d170a1d1008060d0c0801020a1b05060c032e0509100302060706090602 75
    0x3c0d2015140000d01458251416a15000f0f0709855260709014150090070340e40040c0c212001802050701c00c5403180c86540700c001c072070a0340c01c4800a42100c02d00407940e690400f00010b210586910001800050801d24415014040c0c14816035014105040d003004451081c441d940d4031a5400c2d6004054030381000c0140c1e00c000e804d030007030b16288000003400d504d041801d01403d0b000003e26011007013400010404100c1c2030500c442240e8080c03c040c00c400c1c00c0381c0d00003034034007038190001800540609452520310381c0d1503001e44015040f03070300c0700900760854114a00403c442c2040f26070f8410b40460707009840c18410718078542c002c40301408404e1080301a07500c2084800c40394002c100503a501090074054150300c1281d40c410a69032215880b00c14603d82c80c0d01d030321003038000c11680707d0850010114075004c00900552400c1c0501d5048284080702284502c7e620402e1442558031498100b400308071444d95102c658403c03030b64018821890210b0554480004d049080002c0d154030b0350034800b289901c441 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 377469379 1250 377468129 377468131
    0x3060a03081c05180318060903030c01060608060103050f07120e0d050717040503060a02131208070c080c01020307030c02030712031110090218060d081605190f0818040203 75
    0x909a591000e0102e505505040354001008410031280780400c0700380408003c800c40b80103030703030100c0c102d030718030341201d0215040b4840da10318582c2501c00016410f400040660200c1d042d030b00180d0f80c0c101c040d2510f070011800d8940544a0070440140350380420001405060324202000243d071000c2400b012000e40740d800c3c0252200c440e80402ca001505108101d80c4e01d211103184c51a003c1800e0400b4205070100307942c2e40005088514180d80080d04170200d140c8100300400600d6101941d030001280382c900b40000d03400404041710078000401002c038500340b003c00d81882c4244181d00841c14074206840481d115400500b0507030b01801444000306004a005024441c85406034450000351005540c0892130070042038a403609403440c1c03044a07801640c65908014403140c0002000c00d10b62150b80006403a030880510081442000040c0ea001d22006c1400942c0d62600420580e011240028007413440300f100010002c0c48140d1802408000528680144c14800c2c20300b00c0c05d10f940700003000031500301c1e48 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 377470629 1250 377469379 377469397
    0x81e1506040e1213050f180105060d0f0906090b06040e1b01110d08090f0a03020a020105070203100f1b0c05030d020318030c070f140a051e04051021080f03060a0308 72
    0x252544e0140068185001c0e505a41d4000b50707100501107000c1c91407044840d01c18040c640c0300d41400620f14040210542140c0c1004a400d801004000c00710b160980052150300000c8036030180003000280645024400c0ca507011492101030071080c501e840c5181c10390300d01103100905004044084455258080003500100100b548400b001800c1c0366507102d140c4100600d101c4c00340c0e401489003100081e800b1500c4911a80e080c20034680f41e101a10000382480d03800c0c895500b03c24902514200c1858046d00000c150908030400d20301407a8158508850682486001901540c0308000c00c060300c511690080d039201724141e01c101494010301c01c0c454115488000311010b254804041404a8007200034070400500c0002c1402c4a190000004580c021400344a00f40c40b60640c0207140c4081800c013014292080d1000340b0401607071804c5015000301c01d115001d2100c10301c4034034584165100caa01d8980c0c0d203440d00500031600f00301c194823010081c0d90000f05059000f140c6a1000400902404080c0400348 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 377471879 1250 377470629 377470657
    0x90506010e0c07200a0b03010b1206010306181d07121707020d050c03101404140319090f050402030705070b07022b12020f090d05030403020a081e1506040e12 69
    0x480781c24100319400b80c5c01d030481040118108010868900700204440c1c0e0b071054a01d0080040d900c1d50016001404a07900c5600b044081859084202040383d000b030145580c20640c07444e080c890344030030fa41d8420150042c090400c004484100c0810032150b51404000790709100c65140c50038031790210b074060000c48401c950592022060440350b00e0240400c2440c0040d2003c00c00000e08040c1400d420840050030107001801142c6190303c007480300380b084404800180700c0b025543c05c41b4a10083c142441407048102c419805900840c1c1d5240500890307010390055038800e8145126510362182c3d000300540754000f50700c204802034521b08251a602c809591240e034030246010381b07202d4083c2005201e901c0c5400400c4c4100510310380d5100c404140e5181640036161400845a646082c900d548142d42010b584000114000500b8071000140441402030784481c03010a8100c040c0140d5446540d00d00308030a011801000480d503040561080245440941c21202c1d40c0c050340200b020950b1154560f03400c0b134 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 377473129 1250 377471879 377471933
    0xc080906090307020d02010c0302070b041206140103030f3e0f120a030c0201060e0a020717130e25030b01020f030c030a0e010c1509060f090506010e0c07 67
    0x96041840615031080114000d10b2a00c055540068180c04009400070305100004203440e06141c404c01c2004050100f00e1602d503559603c43c050784071101010b0350b08641c854103203284681c004d0004030403241266496111f041e4200c3c0803020a0b00c00e550f0880e41490301300c140c0b080c03c0810041d14034003011540300c081031024180056205950800300e40c00340746001740e809204003a200341003030411030b0190300703161500150410b031012040740548100e50002d001e0b01850014040c4801682d030083c4082c034882c03901c030401d10500e00140c0d03140d070042c107401c508003680612040040035036a14606511010b401942c482600d09101000c4401c054071000c04006640c0b00501e81155070100189045080c0f0880154108080300c800c43c0d81d24422240c40c134041001c2102114240c1e401003140100780c2d03601089500fa91f002c80500003009011a020a69040342001102541c800d064802c03042d405030408046c1c4626801e0010101d010b070006010590b03642001c0000901140000220314202d00707030300402901c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 377474379 1250 377473129 377473141
    0xa0b040b040c05040209031e031201260706020a02060901030905030a030603060c0504140d02040b090718140f1e04020c0102030609010b0906160c1d06031606120f0204090c08 76
    0x14500090f00450f001301c0c410007050149980c0040d41214070106031250318800c50040317104a00f180034013210125140c404200101c0e0b001000c034445404000000240000c4640c18150b10340d51321407501c906009604075407181000b504115008146a0310b041c14007003a902c2d0560369403840d5a01500345000000e564500a10400031980200039481045182890415040c01501407602400c08860f03881031102c01c2c1c00504644483c0c00c0310040b0750008100c10640c2c82c103106d029081c03018201d28002c00c038042c0c0101094111751210794240965010f09415102502c030750a01c04504400c1000a0300c818000d07064444544d120300042000c0d000800000d62a41040c40138041c60f00c034107800c0303c0075030081444112501c0d1a220281c851264495801d00b84481740c07810001c518000603080003c1c15680c1d00300405c900e0764103000383c038040c42c410f8084078107007601031701140103e54050080030002031070b0491003000980950001c0c0c48001c0094030040c9401c0d07507009081c049500031404080465400010410 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 377475629 1250 377474379 377474393
    0x1020307081305010207120c1403030c0d050603100915050601080c0403060504060b0a0b0405153c03100816030827030304090b01170c19050d0e1e1b0906030a0b040b04 73
    0x1003e09c40480110704508211304104100d0007500e0b44003031550342e51000074040d07035400c000002e84000f004504004a01e01403c040780d030520900d12980c00c3c00d003884007042440d4414100750344242d94400181e81403a080d0347e6800d0203098081c00c10f41e105c0e070311207404014941e41c00000000820148104a03900c6207820b041c0035018180d6600d46080e14030520061112604114054292800300704c280c901c1038852072041c20020400c491071003144203000c001c110150028000701010354111408072001e64560071000c05541485000003080c644040c8140d48640720350400b00ea810707501e6524122600c150001c0441c1c03454000d6400000c0d40c1307854102c2410740756080f07810b401d00700040c46030302c0c100307032a1030a404080d91145080c2804104202105522158890400c0e504400541041400702d240440340c903c1c0d4800c000907000c00b03d90003501c098410b40e403000810818804081403150164503e020400500200c020000e41d0540106200c060003e41e143da02244150710440003803a09081c1410104 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 377476879 1250 377475629 377475653
    0x5060315041a030d090b04060c0f061e0b0d030f0e01030b0d0812011203020304061805060d0906050117300316020c0a03050c21071205010c0201020307081305010207120c 74
    0x18070851000610607010f01e40c0447d000d6500500700418503409600d421b0700c008225001c081d190b107192148541070f40d09070100015042018880a01030079142000700540680c42d518010041f40305109148545030152000d1036102105042c0003031186920340c046800c2c0d115911088900450004021070b008074014002809802545d40b014440141d42da0b020303640740b180d0f000b503905010340c05010b940c40b0445001a000a4030014101360b40310044105800301410050a084414600307101c00412810080a148812401150018072008980f20000b00f04640c1c010342c00381e4000c01c4591b00c01c0e03109051500650091440d9030b407003d0f1055641b0002802c1240340e039036a41c070800c004c40080001c20000225a0240030084441c15560103c00300d00320750f45842e81c0040201409003a1000410310904809031401c1405000284140340500404038200d20003258400041000da0011070a01c81c40d1504030035169203c1c40005143c44515290152880320b09119040043c0c81030581004018141c9544 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 377478129 1250 377476879 377476903
    0x8090309130b040513080a030e0c0409050f0f0c0d150914060103112707030b040f0614060c07030807060f1b0216060905120c041b2705060315041a03 65
    0x90003110006a80e01b02841c072411210b103003090703201e105007440188203100045091200038420048515285022620349050710b140b245180901801420ba40d9404205a40d15406c006e064610800240c0d030340301d014242c0000710b0704029644da00d042001480190560304004440700c01841998998500354826101d0701803214002c030481d0a4140704102440c0301440d501180b415246d030966603503041200103092041c1c3e466803042c1090a0800450300607408203056403841801044003028200900005104e00141c00100c6d610a8000b0004101b6500140888038401c00002c03852480d4103254000b551607480e00340c1c03505400148019401d40d010826520902066100c10060074030f0075801030a9100d4078801c1c03d000d640c1c0c40c0498071118005000a80060070000d0040003400d0801d060b41103075240071060403000c52605004e10307125802d990403119081e501d8081e40c1440a042c0414004181c1000c3c01810706803004c8584880d85541e9030007481e64503003809030510b603104601d00030186801054624 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 377479379 1250 377478129 377478151
    0xf07330c1706011823030c03030901181d0105011106040c060810051509120a120e210c040510030c0302060304050708190203070b160308090309130b0405 67
    0x1120210680240710301c0c0310000a4000c1c005940e42e0000142c0b001c3c0e11442c4c08038910242c1d6400400c010503000c2c2107490142840c0400700868500506040e95204081e544552550082c045200258410040050400240d02100041d02c0d034446200e80040380442001f1140201d0600501c86541d200c3c0301e08401d0144400201000d080c6901d40d402c081e100ca01400d0b04110036000011440d89440003290014540540200c040e5485030030340803402d07005501c51612880e00004402d601140018282c00d049402c80140c0c0c3c0319001d110010303030300c3c42420314120b50009854500304004860300800311603690b102c5000b0b000f0910307102d4200000c848009207116002c0301000030500c0840c244000d0b650940c0e40c16a0720302d0740ca4035903085c8207107400340607840308805114408002e0089540c2062030b064043c420303400c5404c1c030354981a00c40d03030500400d0025070f85808040b6901000c40d121b00c46040c0c00c0129041501d14050b050780205804c0e81d40d100500d40c403651182c40003011820f040c811a980b101e03110341 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 377480629 1250 377479379 377479391
    0x3090201080c040e1b0c030f03010305012d1503121e03020c0a08030a090807050a0b01150e040f0b0306070203070c1202090402190801051501180b03010501050f0733 72
    0x103a003855803000b41072800307000c0c4940194501c1012040451b0b0728480000e04403900c580c4c1a00000801da402400115200c0d4240132154016440b1400e04d8510040b010400d2102c1240700502c01c001400e0b000121200c800420400102041500560076585a46135680c50000e0030704510703409015440c02540f004161040003989501c1d0808100c1760f50043c0d10003c030a61300d882c1e60846074007620002c0401380c81c1e840000f9090080110024072215501d125101a1425030fa031420007608a03002c00d255400459003102c811a0240b42a03408103143c9641610700054100340072001c00d02d045400c071200030141c0d02c00140354082c80100500c403001403030030170170302d0217180c10560100303003400c10140009020b003400c0b4441d00350840c25240d9031000380964600800a9180c80c007030351111081162502030106840b81041c0b40303484c100329069001d0310120032a02e45942d10700323801100d0b80e61160054408440d418004c81002444138000c1d01d03035900c1c05285041004811008040c0300005140c1c281e90050301d801 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 377481879 1250 377480629 377480639
    0xc060906010b160c03060614011202030702102a210e030405100512131a06010206010513020f120108010606090806060411040b03070f120b01020a0f2103090201080c04 73
    0xc01101d060f02d440210b22403000041c1c0c50480c0120166800c0141050304200d404600061414041c14084000360b9030500340c0100e40700e00301e0892005031f8100005070424080782c001100e4580181428801c1e0200c1500f101c154240d902d40e006030f199031084d0020710402002120f100311a1500c15a8061038181000303918403840c40d0725901d2280b4841c05015102d222030b80e0045500030030035034941e5032088698800601d4240e2001488844840040f00e003084024548850f0003411110340307100d03c0060f0001c01a50342414100034506a00c1d03169409041d8003084a0300825000e840a01038201180e40408620750418880c04c2c292011a000082004003030803003080300c01000240c15400000c15500001e280607104802c2c42135109942000101010010920030050b03440004007003400c82d16500c0005102e80c200c0c294045d100b11012031401a80400c420a002c20b690b692861102d80c450a0700d0505405001168031104040c15102008071343e403450b6007400d6580201e8241c0c0d11022a40d4000e1406080c9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 377483129 1250 377481879 377481899
    0xc0d0807020c061c02040f030813171e030f0a031a041b0e010c021008040303050901110a0e0303090409050a17090d0809030a0b010f1703031b0c160b0c06090601 70
    0x644400461101070f1642020130308465041720040c1c00c0425141c40c5982c0c49041004041d806412071112406201600051046400e40c40301020030346180605403039840c58640425013144880428407034041000007048007160300d80180418034075900c0114416011216450b00b40401c0098076014030b040042e2180501c29405980b6000300ba03904148450305228001200c650742813250080d08050b400c50384107c066000b40c00544264400e690500c45540c540c0c43c1e0f6402d0f0b601a5842185000052004141c0f0500441c2450120880070307044906050f8810001010784a070124251101d0300041541d0003401a86400b250180003081784291520602c0c0010030f1041d030303240c00c001d840388901007054252680d06001c0d40002e1500607880c0070184d40c40740341100000c207a5104ad400c46210381441c8244043c40032090302d01c215440d800d4200e9200702e0b00540482d0340c0c000c00b03090180d40103a15450030014141c28529000c0c0c1204200b140e16070264040340c134503005001d803000c3d1203a0320040040000c4004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 377484379 1250 377483129 377483137
    0x702030c1e030616020a0320011e0c210b040b0916120c020706081312120b0901120609080729010905060f01111f0f0b180103020d0312020c0d0807020c06 67
    0x8585088c0a0760301c204500781da4500c07290481711801c0d50a100aa401404d401410102c03a1078000a081100310058101070f18102245400080b02c9080da000d188030310580f95028003044000980040365082c003040011310000c008582c030341d04210507a000485102d5015403009000a03074172008101c0c080c0f881001940d128140e00c203070001c00c0040000240c050040e07000505519a009150b0b401c004107481c00a001c0801034504840344918110103c0c106241c10900d80f41210f44002d8200304100c5581c44100150201f50002e80301d0040c1000040002174000790f40d442c440654031620094050100c10442904006134410803015090600744401e41d0b49003030034100c1c0b170b81003420701d100740112011055007085001012400c00a5012010903124802a00450340c4000b8043c820440c28008804100303c13200c0315a5184550743e0710500620043c14641d280c1a5124000c2c00d1021010050450035001d99011924800c2c0617001500105009908200c8240c0c119941f03001130304402c10f00c01c0c04503059000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 377485629 1250 377484379 377484383
    0xa0c0e0c040315091e051204060503011403160b0706050a02070203061504290405160c03032d1b0e060d180206030127050408040b0702030c1e030616020a 67
    0x10143c030b04820804651014031900d512070b08503a10101c41d00d00c028589030901d08240e49a0069100502c05c143d40d00e012201640c0321600c9190440c0d0824114032032030031102d0010fa806128281e107010002e643c18030500001d001c0c081d0b64075680c000f1f0f0300c0d040c0d00381c40001c0c051682050050040c100140d90120301243c0c814120f0000080b01000c13240000d011301403450009207510200d00c511610b504050b1440500311400741d6060003941c5902c155500314000c0070105400140b000000180020301c01d401240700010200401100152a905181d401c002003d50007045a03a65003101400d00d807c4840380310f00b14940741845c2292490000100d05148500c641500b00d050f81c540059441514191070f0b0100d558010f001c454072980c4602c120010b8407003113402050010305c54070340c071106046603016080c461540030074160b050a00d0514450400d8105400c200c4e450300a588611403542c942c1680d07900301d80640d440701c0c3d558401c0c6c4024035003442c6000e040034498a5140b10b00d6280c0c0c540004d50321070466 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 377486879 1250 377485629 377485643
    0x3090809040c12020c01020c0606030c090403181e060e040507020318030102040806040506090f06130210030209030d031e2a050d0c0c0606080a0c0905090309040e0a0c0e0c0403 77
    0x60841c216003030f2020812140d500751002c60300740c6034604154090001ea00410040350300307a1321b0780c10030940d0304c840c0c0c4446550301c12003010009000901c03610011079000b00030b0f42d141c942c190b210001c28980845100c4064244405544100040c41c1c0c80040456240b82c1901d00700460b040a0200a449110320f603070001d8444200a66080b55072801d5048030010a036910580e00d0a00701850b000343c803280c0907290411507201d0210480e840075000b06225009a90203440003000c00c01c03540c24441030701000d524089c1415424012403100c1e440508c10305c1d0043c40c3d01c3e03400154010200b038040f0407107020502c0000b00c02d85013450b0300c040d00c41d10f40700b04107400540b10707500341e40d8420003a4219400d2041c400100145405c18049102283e08812007100b45803041e1700502c03000b6207a62503c0d6a030558880f01900030303665020100849010342d071013160800380300c0c0262480c0405120114040d140c20400d404010391041115509100b4400722a0001d40440184040c540c100100b01c1016401396010152100c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 377488129 1250 377486879 377486891
    0x10e2401020a050106080304091b051207030e010504050c0103050705130302040f0608100504050d17190608030a0c0605010501030203090d030f180f02100806010f0c0c0f0e01080d0309080904 83
    0x1507802040b245007295400740090000648407801e1503241e810600c0366109003814414940c024413900c103016468012140d44060034178200f02e14a804502000d001e000c103165642030410507801081c001c541c82940a50002c001c03078490a0001411110001c0100301003100501148501e11002c4d8110801c50b41c0456003c959000008201001020300d540225440d1042e050b511603841065085588039a0144058611400f02c1c2e144c15581c81d507110b1035481012102000003040c82030b28040f050051201d21600162407030f200c110b41c030300d076600002070080815900c0b007a0700204003a44c02214058142860b0550650824400e0282e640244001c05020301d519a403034039078400f40c6c40d403080305040105900b480d142003450810b202c04401d07d060503409070b800080b2101401d401514140c1c042c0d141030b034504180040c4090f04861120b003017101201c800c90f414500046e000b4880c1440c1e4058440101c00028551610364114a000007010b10f0009040c2090220004a45000c043d1881400143e6011580b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 377489379 1250 377488129 377488201
    0x2150406020c1c02100603030e061309021803010617060601080c0c0714010806010c08041e1502031201080a230f0708010213051f0c02130204030b0f010e 67
    0x280c05864207480d0b55110301c2c038410f9007100b1059080001c0040d15000d40d111507462010102c107580b107034040030f0003060b2102200909400d00d000289081500c0000c1011100d840b24140c209a82c07028894440349200321115041900e42032150000800948407042251070003400d05545514000f00400d050019500000e030740c1c603480204032089001b52809130345407503894076010090182080c40b91400240c01400141c0300f940a110244c00080d0409182c50805144c330507460207503810b1030080d440f00241c00c072000810750342c00141041007010a0f005191501043c000fa0100e08e44142e010754841da1000070941d02182962458050f6115041020101000384d0501c0d54500691040c1c800b400e40300d007800000d000103042d0b01404258003030309410b510302c0b1f0783e8400700018188000e24000e0248800c0603452480e0f402120700d084158030142000d04201c1c140d112900c1247c11a60060300c0c41071400c0304014201c0d501c02c41450142641340700329600c5082c0080d030580c0e54464004010422280b00038804c070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 377490629 1250 377489379 377489381
    0x5120a050409050907091b0804020f0d020607080714061504021810090611030c030f090411120702011b02030d0b011b08090f03010227011704030302030417040602150406 74
    0x3010b0141140305003c00c1c10028803880e0f907814a4810800d0841c50210045101000c0c044000d01965581e558180d6645841e0204410345a1100c0d80603071080c0303140d01101c010b840d5800500690341c0191031198861011342071003803400301c502004a000e074001404000d031540f000072000b10151400c3d140180c80d090000203101507400580001135000f0902000b0104896004402d9820798140c1c1c2d81c0c2c2c00303205400c051410703542d010703141080d0703840e820501404900712074000243c040150020300204080d190b030805800e0b29407102d00c1e00d0441070076200070820f80f2038090150039541e02c218080d80b0f5240001c000000d48a010f000681c5403002d407100107600070b03607110f1417800d990f41c8140d040c1c1081440d07152401e40001d40c4519002401012107000306041490b061003030380c1001c000c40141c01542c07010b1500309103140c44400d48103818014165100003900304282030304d07071145200c0d03140142d03030b410281401c02a20f9420001040801d100b0030051050725808901c95030020003201e10440e8a444d6450204 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 377491879 1250 377490629 377490637
    0x70c17031b150a020306030705010e0a06030f140c0c060108030405010e060d1e090309050d0201080f130507060c060b0d020f06181215100b1806090414100806010305120a05 75
    0x502005002c005200300200e45030b0003140109011400c55140d10f60354401942d181c01d1801d040d41e40400f108008120b614001e40101c0000da1000a002032600c0ca1074900058a00f42951403640001000ca0a40c2c000901001128050b00302c0c0c100440c18030345424002408240600022809620003046103501c1031926000159011801001e0a01d00d641520300300340102090202540003401604000440307040801c01988115010b035a0031406130b441c0007081c0002c0da00500015802031000340d1210105406000341e1000d0300c415554400c0300340d110300300001a51194400140702d9070b010384690005035540302c80440c0d096010307182c660301c42000703007641c48001c0d540003180c3d9042500e1810151103080049004c0754488108082c0c0204c45d2290611842d008c2900d010340c0c0200201005007255008400030480700c00035005002c14907150054001c02d099400091070300081203440020b000044c1c1140100c880a8107180c0d0040600d989142c6403107543e10010501d03250401c0d0300042003642da0303125404075 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 377493129 1250 377491879 377491903
    0x60c030d060b090a0b0304021c03020a08030a02041805130308060609061204230631030306170102180f041104060801030b0a0207050a11060c12070c17031b 68
    0x4020342582c0303640341c5010340d000700281403080700c10301d40c041080703203e01003528000c0340c0141c841902040241c074031403a0124210400d40540c422030300c448001840004c01507103d820706580140e15a40703402d00303640203010040402904103051000704650944107907901402940c0524111880da00c81501054080c4242e10348960404e900140d6043ea50401e00380c00c85c01644120b00000342404803102c0e00803486030441074802c10303400c080c0c003280c001b509500c50210030070700c2103c442c5684d17010300b01000d41103030304031000301d0100ea1a4402000030041d10b0000113043d22908000b035240c5030170401c05140314205038210300c0c03007940e084107907007401e8840d603100b5540350102c000541e40c2d490b1a90b6020b0888042480200c500c2860310340010340b401d03014000d607a002984100184006505543d80804c20b04d4002000c80c2c05c0138050041c1001004208140940c031041000056920595030800300c0607501d65400c28500e100c90032498958410300001101c91000801c00c25110f12801004500d052141c0c0741c0c0c40c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 377494379 1250 377493129 377493131
    0xf180306060f080a0c03120525061b02070e09010f090812061e090604140117100e07120311030a0f03050f1506070501060906030305040608180309060c030d 68
    0x2004100540e8001e800762414082802c07142e07030f42c440c5141e81e68605150300420301310100741d0400000e42c90909005103c000d50901908081034000d00071000000c81000c1030006a0301110507080c40024842e13125242c10300c1c2c9142d140c032107442101a541f003405204a21114034003000042c0381500070f41c0014101c100006050003810043d040100301c1d030700000140401200c204002c00e00d01e29210200d14840110840480d0700d110100c800c21112400040880d90010386074000400348a0002042502810510f078071820103003281100380d49440e450a621811040c5040d00c0210029000500c21044659110210300c0d54003080c40c0403107084c10f200c81040301c0d030310020514400d5250005003506810714281c6d01040300d03580d0112044080d0409580e480400344a188141d0a682440c40040948a0040c00003140c40ca5407000d0706800c40c1e0080d882940040d4000c581800720b150720200c010f0300002802041d0b04085201e0b042036460384114050f103482200c000440c0d080d15003045c015150080e1440750 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 377495629 1250 377494379 377494427
    0x50a061a0a2003040312020604020a030b09011418010c0503040b060d050a12050409050c1908130b0f15010215010509040309080615040e0a080d050907030803090f0d03060303020d0f 79
    0x1150b80d0760760401d000884501c00d00c0035003000d58034400140745110701c1d0000e02540d6118550f481c1c00640d8107002d4200b420302d540311006402e1811b1010001c1c2d010342d440c0802a0002882c08a105003191003100f1000100081002031002143c20300101c2e5800c00c0040b20100101d1809103480c03850083c1e9200f006221006051006440c181c100340074008031100b012042c0003d42d41d110154500d4030400c48400e04a00070703240800080c610501140c5c1e4070455100c1c049542400607220316070007220883c0d50300340010342c0a0070001c1010310100c0300542c1d40c20038001000c2692418461000d0200140207060207080d081e0009010301d840781d000c400040c120b20f000c0d2080350424004001c002d8041e007454602031400c201600f1021980051800b142d217400c045400d0030b042c1124202000341c04068081c000c184641d09000c0003089a0304000e40c0640c0e03451004180d1102c4414640d42070400800010080c1071410b1b808201017600403030340060b40c581625003074885110201e001c0c0c2d0783c851900000106920062 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 377496879 1250 377495629 377495687
    0xc09060f0a05030d05071e230c04020409020c0705090108100b040f090615050303030712090c05030d18080a11061b0708030a02060c040f0b0f1c0f050a061a0a 69
    0x100081c40d00c0e90281340380c01f0484125480700a001a03207401d0080180610500a50b15081c04a803080803014082064840fa0f0000c00001000c0e40c100e9006080c07069800201c80c050620300300181c2006140a40313548255600d050903c5413903079003001000e40340c035884002e04070700d41d80d86034041e0078082071038902005180010b081900c0182041c021080c5003440c030304070115140c50f000084d00d2080c04980c1d10525000d50352040803000d8209800d0403500c2403240040030425030707000e00c424103202009540310300000081c0b05411a0a9841d81c1c0540c005130070080100c070201d0800e04920080c40383c280c408603038403400c0701c8042800c03d040c000003d03002d008244003c100c41e000440200303034280b129401c4903443c0d03d0703982c2c21084034070440c031858441400e007060802c03c1e03042000152480401c103020703042c181540c00c4643d4100e20840001c0040e5a9550a007504115079640b007080e410488518007041000e041114a071520003070701060000030313440401d80ca1402c500c52145211920301203201e07281203c00381 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 377498129 1250 377496879 377496887
    0x30b04020310050906130201020f03040e1605090616020609040516030f05160c14011803031410031e050f100b0102150a0518030711030f0c09060f0a05030d 68
    0x5940891003402200c2820100c0080381c01480d008480d44030207040581c84180c0f8102c10018029022410350282d610024500d500a0014000400b40942020068601b4880c400c6030340c0d401c0d1408a0a0103000c0c8100303083c6031500c030140c0b4404206149402031800381400007071014015650456449802e08081001e0a4105008150f84000710f8505124031000d220006096503021103c1c4004602c17640160b00340a40306401d010f00c071a01925880c5215400108400d09648415401d511016403241d034820400d5810711401c02d01100c1d0345040286401c048c151000c08030b903903102c09041c1e00c100200c84460200f420390200c10340b5921404036a42461800680c40e2a80041c03011000c02520b4915141e80b294004070307441d4604454500900082d035035141844004000260044849441c5400f102038204410001001240e008102d187e04001f0b042c0100741ca00300030814458103e4102014185e8035849071003c60350442070132178850b03045200660200e5010382155004591510a2904c4003040b2908 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 377499379 1250 377498129 377498131
    0x4120c030615030203100c0c0f06050f07031103160302040f0306060e010902070c06030509160602151012020d1110050c0d050a050702270c22051027030b 67
    0x30840082c84050b501c91031696610300b80b0301c00a0340640008a0007103041145503c02200a40b843c181146201e2480d200c03c018030450f0740701100d080c0d50f24024803101100c01180141d1207045441e05206910154621410780e00010b01011a06000c3e00e881e555214065010b45001d80844140d117050307a980e900740040902600d118114400d80c0c0c1c0d00001c0b07030205050086481c00ea0300840f0030b00c40355182c5402203008110003002955103001e0b0091404c07114100014000c01401980c0c01402e4583c101c040049002101030007802c103418411804206540030f109244040680445105e00042c04904021440c11880544264400d0860384c0303400109800001400c10304042d20100ca4081d02030450a80d49031080c1d1260a0220b0401e002820061070b2540c4840c0e481c440b145901c0020104401820481c0c3c6002c0c2c070380300b800b11000b18901c181080c2504c030500102410410a05489141c0780101c4c82e44014903c0710400c12a07155010308540d080d031354402c608681c0c40c0340c0b00c03500d240c3d13241001d841004d8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 377500629 1250 377499379 377499383
    0xf071211160608010b0703020304290d05070809340b0d0c021e060402040504050a1401051519050603070207150e040e0a170a02210306100c170f04120c03 67
    0x450f200104081000c0c01c1034445031613260700254602820700211490302d110b16154646000c0c800e8402240002c0c03182c0180641078900c83d00850070303082012002d0050000103100f0041740e881900c400710001d46942c0c1c243c1c0c0c5601eaa09911540030a454001c200380c0307001e40c125110441000408445110982d40030030217021190382501d544912003a92040c00c4206111080c031680c1c4554081005031030076510441d0484d06c240c0c1165050011607440041d14005c1b10008029a55103100b000249a01d4441c01e0130001c4085030101002c18501180a410500301c0c004d00740101d50120004d002c46008100f004046c00585003095907201c2c010200030000701c08514a2806107051400207009500d0010394600c005a002c00406c0007500c03902145401904803141420843c41058654010504460610850380000071074207640c80c41d19100703004100c1d50303030420201000610b60001000c180403405103c0822000d4844550300c2108a2250072070380503e4104c3c40c1c15030303442c41d48901000382c02c1003070200b1a8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 377501879 1250 377500629 377500637
    0x7030c06020d0804080915070209070804211403040201031d0c041103090a030c03091a030103120903051509010605100201140709080d0539060108030f0712111606 71
    0x240400b141100d5404080c0c40c0103040c0315051104d49058580b82140300084c8a06040d0941044e079140c0004504d4038082e1010404a00c605c4148814080038001c10401d041c0c14400054501c3c40301c1d18020f040a4000301010740405000c0046021a8170a030040e240070340081941100c0726845103034141d200d64210b0030142c4543e182012100150000d0720541c0c1c410a542c0c0c014180724601a181a00c2403040b20f082202009500a0701050b02840c4240c0b4265000352a880b0546941c1585000d18110400b024407105203e42c0000400c0041c0000a0541d40c820006441c620709490b401e400d94098251508a241d2014000d00360910995055000c200100b10484242c0d1998492000503116440280507158442d040505440303205400341d0002d003c17580d1140441c10304d074500c802c010400e80700c00c0e011180440f141b022619a581404202040c05840070a000c0c5190071501c8150314424451100003c001448030a500d5001d0f030301504084500c41d60b258283d8441020ba00a86003ea800700e0107460007007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 377503129 1250 377501879 377501893
    0xa1a1c2118030b0403230f1e040e04080f0705010f09030f0c021f1e02010b090705040e040f02040207050610050a0b0306030d051318050f0a0203060307032307030c0602 73
    0x650746240e46031080300e03044a00c20845032a161002c66140d002142c0895001071a900c03011100e0703034284001c1035455a20482d50791181444007801c0c2d80e90304405076025100405110600012100c1484c2a07001170381300112070f03954000120324038000e020343c6001605552900c0c0c01d240030a800e68021860346c0748295100038200076019415160018003060280d0424861103900c21a9103200c0800c41c0d0309007142c10421031400040040c5c1c40c1e50165a5400b400603510349961200d1400c044269070307001852400c200b401c2034180a124a0f000c1e030700900140c080611110084203549071a811110074942004c203694ada0301c0d002c5026071291040f40300d0140540a100310009400c0c0460040c3c0e07004200007800340443c844035180480d0303160450070481491940190000601e428400d040034040300c0050070100c1c82d4541266603c00e0280000c020280701401081000071958001c2801010b0f258421400140030036030f55034038100c43c1241c41c0104920310030910003000b44420030318540f0488420354212501 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 377504379 1250 377503129 377503157
    0x909080f1e03100f15120b011116050307300c050306040605090c010e0f09090f0a0b09011103011401030908090d0506010305101401060e0d06060311090a1a1c21 70
    0x2030503d20034255400038441046e071144950558100c542140414903142c0e9040105559142c1021031811242ca424402c0f80b504210600301031119200030800ca1408d044055400e190030400f81c10452100f501640c0140040c6040081d20300d210f001500307020741110b5031403502c0d140500051506540c1000540b180f6803100f134003507200f42ca80315074034900903101c440d23056000d4061000040015207001401c0c002e660494000100c05c101c00b4101c20b0103805c40c007085003001c00070a070850f0046c04004200312000c000604c4400c030141145441502c0070700e400100c0741a0303414182314601816200641c885802c204d100144a40061110306a90003007050741d40c00004d082d040c002301d44210904600f0b00d00e41e08010400304d80221490b100010000d01058018009652020f00311070580e00210303800c0e130072440800c0c010700f001c2014681c0141e40e80c108004802d032892a80c0c4410500014581c480c90700684d41c0264160031484081000d0b80c4110030020380340a588450200700541d2240070001090b22904600e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 377505629 1250 377504379 377504399
    0xd14090301090b160e1504141503040b0a0c030c05160507090c02030a020f0c090c0a02010b062115090c0904060f150f0302040506041203020a0203100c090909080f1e03100f 75
    0x1b410803902d005403490075140042c0400d100f50441d06a40c1e008071403100341000301c0040c00095101d1889610002040d103442550082203400d1000e4540030980f500c040c0500d441c3c1c1140460350310b80c22040090a2503055450030525101580d001700c03000d10300700403003184190f4000000d4517441142d6001c1c0d0381e000c880c20984a90b902e010710401ca40c0502983c6c0842e0314034484c500100603c00303103807002040c2ca542c020049035031540080c1401714041c284802c0354410998001c1407036040304a2800c140c03115250310740015207403800648031502610b400034110159031b1b6580e000d040104a00c908a8450560b22002c1051001d034004a40000c03a6076044003100c070b14070910031581980e100402c1c4034181820124031810a21441c2012400c3d072040702d0340e00025070b904004816581c29815404520458103160050001c29070b507100920080c1003d240c840050004800d0700e05e081d1641c80c50320340b03a807600801c481116400740034100344241d000042c01040b24a0104141c25140109500340c0c1465947c182c1c06 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 377506879 1250 377505629 377505649
    0xf06181f0917060406020a11070f030b07020d020a2d080307030b010906051c091a060f01022409070f08060906070c020f0405060105090613170d14090301090b160e 71
    0x60b4103034111000180004000e940075103114042031809043d02e648500206260510940203401451204203040041059258560382d0000192020b442104050b000180d5a171005d00710003800520719a40000104031940486140d0740349070b000d02a1413201030f040c140d4440d0300a13580003000a0501060028550040010208442e101c0e5156032400345800741580401c0e0070031504411031a1a6490f0320f001c514041c9401510b1429110ec2c610076003012410071400c041c3c0b805000707055400c141c0d00305090b249000d160b040c0c8807840701c03888c0007a40c0d207205915082030200c0c0c02c800c2c601040c801c008114a10000703241840b50f1608030454001c0c1d100c05070103581010b05094002e500451400322428103007000e81069800840c181042c609181e0017a0002d05140c010b00030f0245802a5888108141e01c0c0c070003211502c04080b40d0140c030300608a0100104030302c0740030076001c3c10080002006c8034107403025070150010940003507020501e81010340b2a40d0400e11035484010000d4810070384803080e450301c10246 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 377508129 1250 377506879 377506919
    0x6050109110403060e0712050c03010b10050d020d06030218071d210c0604090b03070f05030c010c08090603070306050f01110c1002010209030102070305031807050f06181f09 76
    0x11a04003407031562413102070300010103401428061400c0000d0800b0004070100d00907440b0300c0150202541441c00c2c03500b120450001c2d64810302524410142c15900481101c4001903050409a62844002060300203400f040c1d00080d0040e2101441d1514440003281c00740c007411503a926921400e405561140034044a0b9007401e5000e1406440540340b01807108000340541e404005442e04150035000240c0c59810960041d1891f40d02c03a07480c0c41443c81e0038803c400142101c8250091b440b42484042569030483e00c00d05c5050050403021101804003010594076448001007a01d680d80c905280000c0c0945014413641f0300802e0040481d144560040d02c00411400d032000090030400d45035001c02c06018050a441410341d503007000221010745007030004150441c042d84405969003840c18018240240712401c200d0941c10041d8240702c6503552000201408108644030f9880e1401000d41c9400c98021340710141d405042c1c40d230440c03440d016842c020f044404443d01d9005005a4905c01803507210039403044 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 377509379 1250 377508129 377508161
    0xe1309030f0f030e06041407050321071b0305030415020607022d01060f060f0c03052b0203190506030d020a12230408191a0a0f02070f06050109 63
    0x107501d010351040900b0082c008191501294032000401c8107420a00c0c140c506603202c0c8600094001c200744100f01e200d0080505900408503491040748101a01c080303c0c42118126100154403010700c4000a503100c070908030340c0f0220044550368500181c0e0396200303120b1500842c840228541a450011501d02d114011640180031900001c1e0850704556070b8000c01a00038a40030011800f991000348144006050100807001d1000e0500c0c10140081c051500c1c110b08000c8650910400030b40d0020942c3c55201d0389035030b0703140c029424002ca600744c0c08030101c00641300c03880401040140c020a13800340a4150a85104210640700c80c0b0170716403242c00841300480582c2c0300424a400242c4418a0340e031000c8a1458410880c5030b0410341130314001162501041d00030b101040621610301c040c08841c0707a20801640106c11440c103030744c0380c44035402050f10505032125084005154040182c0284085100c461310856031006186803507015214070141c140c40f054500400820900c00500c9404200c1c441000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 377510629 1250 377509379 377509397
    0xa05040305191a0601140703030f0e0a050d0509030c04090323180f04090b2419050103020c0f060903130807030201050f070c123005090f0f0d030e130903 67
    0x8051851a600540007034100001c011b80c0345500e880f13440c080c12170f00f8841d95010039402e002c0880c41055400117054080341d0b800403555400010781c0002d45005014640c00c00548400c2ca202c002800c04c802d20140708c0c0c0250400d00083c08146d8130099800c00002801070b8a00b51305c95400d000059030090341c00b200e000140e0690411032a180c182c540748103000c001880469940d0f855a40c0019440c010b0f940400308001d440320f02c00704003d4003002409a050103407115641d0894825104500100302d108060600d81c0c00106903284c1103040c030411110300c0d200e8040307030101d0400d01ca111341e81e603121280c00002c00150340e1000c9007406021803d0070403640c05a40311030510040501c8032189500c440000c8a070040e00d544001104a08404603d0289010f00b14030400a949014424118203505030340704d0b80000c42e408104d03071064011080e51101d2100380e41c168560820180460841ca559280c0342d50b0240c20b030110a400c041d4025551004e0407021b4405000c1001802e1090f010744110080080c04243c4100b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 377511879 1250 377510629 377510663
    0x30302100b011b1e0503120a090206090d08070b101716060302030c070b04121e080117010e030d05060103060509010303120f02040e070c110a270209060a0504030519 72
    0x10001d89200b402114100d48442c0d9400c1c4000d25003600b65800c8034a5000843d280743d0002c0030f20103048d4401c840820038041a002540060300760302c19944844d01c248840003420007844100010f0350100c41e8840080601424025011440780401d80308400d118a007201ca12401d240000c554001040c5000c1000d009282c10030b9410b901940004103c542c020100340180c00c08074040804540c0190302948029079100c0603240028561440414000381444d4040c4ca82c5602c0756001010a04440d0b80c000e01e00401d40d50074038540d000d0804580c2e84d0b0f02c1413001055800540b170243d88024090f0400340c808005050f519810300a020009200140200d0b40004001c100e1051340d404c002592030041100502e00380e12040b0810741c41c0d20586001c00006c0e20b89104a040005108812616440407181914094a000c1c505007600f08043e10015810103090314141680300e80790151200303060010612501c50501c440b000b029034010b844107032510301c1050450403910801030401854550030000c0c3c807034240650 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 377513129 1250 377511879 377511917
    0x80a0b060f060f0d0c0504080c0904110a0306051e0108101109130c12050c04092705030309010507030b0d030315051c02121b1e031204030302100b01 65
    0x10521030700040004041c0d11281d4428000340b883c0c103040300d0742c1512044046014000c45c0c8000c030b0243d080c028100001d200c2d8450005812031440401c54030300380380d96120318007040b9600c4113041881e001005c0440120400405400c101c0c800d10f90000c90000a45051820180e820420320421245812016010300c00e6042604114a00e503620302c6102d182080386008a05d004140522003268250784428054078258001034511451042a5050109080030760005001e8801c0d4428284602c3c0c0e90046480240080e604064000203408001c3c5106002810800e032640c1c012601500d265180900082c1058002e00c24078594204c09800d041c14020142d0303054004150034030340c1c02040c0410400005050b40da407114880c1c221440031b80f0003400e1715540b040c0f101c811109940020b16400606d4020841c20340d1402428005004070b03080080c55201c3c00c511b051002000c3d045980500541620f080d44000381030080c02164030a07822502e00400401144c001c45030091052400101c92a207107150010310 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 377514379 1250 377513129 377513131
    0x3040f0f0f080f031503120d0b0103060b120601020d0309030c03140d0507020d0e061602040225060504030908160b0307030612050703110108011d0a020d09050c0f010504080a0b 77
    0x1042564079009551038680c210a50031882c00c031100301000100b001382243c40c408200c2445041030b0010081d02c030703450005603c44d00032100d628001c00c0c0c0d42c1c0c0700e0b04d500381c1c82030700110000d2180700b02160f0344a00c4540303c480c08503001c81d40d40d4058803613081c0381500203100340b0441071540e4040e6180c125200706a5011255060710a4400c2c114041c10b101017500c2041601c00e05019030082d400506502009610203010803802c103d02620900c3d0501c55482740520170b0380200900383d81202c00594600e030000741202c260b0103240c4000302800f2804100e00c1000040e80c06540500e000b40c41c1c0c0c0550302e40d510041a074984142c41040c0c1c11010212080280703144141c007840d006002400d02142a0382c881d145400c0141d5807007000d84081d40510010401d1010710000d0300802c0301d0038600b4213425814000320300504034101e5603c0440d6900440044c0c981181c55042e00c0c0307203590042c6c083c41002030504200f079070348905128041c0302e40079605601c4003540c0610104c4084a0224001d4150708640b91030b90000c40710 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 377515629 1250 377514379 377514383
    0x1170408071403210705040609090902150304050d1803020d11030102160305070b010602030c19030302040b0d0e010605120d0c020d0b0c04081513020613090501090e011103040f0f 78
    0x40507120050844506101400131480041c01d03001c1c10300300001d050518842e02038254000c1c0003041109110007030340140c0341c0085d140b07480e50200f0400380e01d02c0401c030030740d10400d01071210f061b010040c0b00c10842d010400c4092812640e5445c1d2101c0018600ca0314400c0b05844025401a0b403600341d03000094114552000382c1e64000d00050616800c45000c0e05c0448400f40d0032400900d000032040d003009a050a45405000030340300071820280710302c0c510f40c0c3d40c045e0101a1000c1d0b146400d0b140080501c00c0d0102c0700a8483c2144141c0c903500c0d824194000303000e01400030f006950800e8004100350408000641c124000c4000520241c4180c484c25124141300744002c1e60440e8800e4006404950000d030000d00804d02d403005190340c0c92400c000642010607504208400035010800e1000e00b481d03203250030340042d80444003242d50307140c2d40280e0b01004405610130311242e4100000090351b844035a00401003648604020b00c03032040b20b40340c0040c2603c0102c50081c40c0e1546c02d54260081403503602c0d2241900c1c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 377516879 1250 377515629 377515643
    0x5130b0a0308030106091e05150f04150801090e0c0102120d230f090c030a300302040501120519180506090625021209060d0e16050117040807 62
    0x7a22501d402c1e9a55000343c22070340104000031000c0016140c50011003451000308110404501e050000080c403050384104414660880852400340c3c008545080381c0060901102e0145584441803000e09083c1092041da000c031482e1854513071031847c011840c00a000016030285c40001851345042c056500001c0c41c0707013070003503450800b0031a400000e42c2c25403040b203068a40000030b01c0d042d070380484a410002e105201c03a4020f0700700500191000122a07500561152442800082a24041041d0b40d4400b101845010b81ca81c551003009816900403c2552000e0341d035000c041c007201d1210025102d060b01d807188810b14000820b103501013568417800c40750700c16500c1c0e0408070a03140c481525110007a203018640707402a80a01851800c41d40e03002c2d4030801e501c8910701442018a101a4846188240c03601c1c40480c001000c40304c940c2d80311b003100c028201d59441005140801503280d170351524091070880d22098841310110306036000b034148401081d08034592010302d580302e695048142c0c1040b5000c0f9081 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 377517985 1106 377516879 377516899
    0x5091303090302011b1b0f0b04050a031106040305100e0715200708150405010b0603100311180c120106051303140703050706090807050a05130b 63
    0x4940900381700344030400303400b11714110003011040204024820000c00c16071a134818500c2e0190b462080048407280c0c1c490342401c2143c4918000c40f64003105078007081001031a211008006400d015205c281001d0381c0395a0149000300c14400c1d03076141501c078600c903110000d04100030b10040c6048103065191b043d642d08003a0810503251f014880c5c0701c018410030403003000c040107210020031404003100d0164000150700e00d00c03598240c404403019420401000200c0c0340220680c0c0c003510904191072462440c1d5610019001413005000341c0080400401000302c100411400c0d2144860000c0e032681c80351902c11880008605030800014400c0601925800b0000821038400f50303603102c10541000e818044200c0d192003e42d6000821034032989a000c031303101d603000c1c0c148401c031200c400489849686074410000584114018250003800e0040182040021a000b0445010003e030001c2c0312 = true := by decide +kernel

theorem cover : BRFrame.Cov 377338129 377517985 := by
  have h0 := BRFrame.cov_init 377338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 377338129 ≤ n) (h2 : n < 377517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
