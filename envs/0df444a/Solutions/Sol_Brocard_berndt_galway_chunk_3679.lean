-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3679
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:21:52.957139+00:00
-- url     : https://prove2.me/submissions/57c86c26-6b1d-4731-bacc-ce24e57efaaa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 661510791 ≤ n < 661690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 661512041 1250 661510791 661510813
    0x30601020a0b04030e0117070f030b01030204081903140f09010302090612071715030a060c140301031a16050712020c030d02010e100204180b2407060c020c100e03 71
    0xc2c440318040d074420f07140c14460000300c400050085100324800380d0040050020311a00c10740110007410842220301c0c01280420309030340140c01030f2280341e004620500c5100580101c0f444d01c0c965100d4013500c40c0e81c0c0c0003054107221107005124060700c1c4110719403400400042d0421740c000c0d4000d00c8144d01c05808170781040c07901c010b000340780c640032603000e4089010480944400070618603901c0d4007501400051410418440110341d0303400ca6040014540d994030040003803c6402003002d600443c00409095503690784a142c0040f80d0f10135800c4903842c1691380000b0601c00d0303440b210344090380d041c0c81d0350b190305104064503001d08080307036840301800b54040c1d00c40707120344d94400b804001103465a5400120b6240c0c1040606403074924081c05130800c0502c140405d0001d1810410b181201508000c4007107115002c5400160140910008030000039240008003001041c282000d000b0090150004000301d10070481c060761142e103082d002aa0010300080580601030045400b0000c080c0c003e0300f10340890a00c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 661513291 1250 661512041 661512053
    0x1090b09040f0e0c03010f05093a09080c030607050d05041403030c07021201051b07080903191a0c030109150909050601150c05060a0f0f15062d05030601020a 69
    0x222150300c0300e800c50313030b8107442d1820300b4060540710324408a410000751418111950311011308060030f19107000e02c40b26120b144c0082041c0081e51545c0c40040e045ca079140000040c14443c00b81c42102c105000f040380410181c900458607a1142c030b5a0f0b01c07824a000364030079104005240c010005c4a500b85814201c0e401080300f00041c501c51280a00314a03a2015140100000070001141c0901c1d20780c1410200102ca00c0300b00711400350408000345c226103590007840d101c40c081c042c04084139014842c0520b00140d213204281a21412802034581c2c3d06899041840441c0b400d404446e0b02825610410042140b100c45621031080c1c50501d0a502c43c0d600d4032540e004041c0c23860300c00b09032030960155005010180002c000d109c1040011b041c156006c0e00e5582ea255112040184440760607551044030b1103502a03241c000c0d22581c0c08005041181800d882da060042003424050000011000300e40c0494610150190805034181d04040d444091094013080b115503000808050450040e00d00d048009a5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 661514541 1250 661513291 661513301
    0x90d020d14062a090423040b060108091b0f03070b07061401060903050a0807020f180901110901120b03070302060304081e0702010c1202070b0403140f0c01090b09040f 73
    0x6072803014110714180000341c2e02c15201a44003010004600803022000b01103001d04070f6028000030380e804203001d0141e009010035400c00401c030780846240340041004014000082500c100001d889008454503400388040e500c1541304958a802d5001c1a400030051602145140400c40000e00b26074900d070700c5a603e80740607040303030004441e00ca072942200b4034a806110070300d80c09004c2c2440d000000b180395485059440c440312002501c0d000300001c070203007552202600b003003001030094840f010384201c40b1591030041c44101c9205d803481d441c00a40c0c042e0006560b00f01e415070700c0140d484a0007007200b030785a2401050900c060344d6052140200010041e00c0380d4000d144101e0044445580b540f44002d904803050502040712002c81804002400040c2e800504000700142c00031454030016004050a0385001c000d5007082c1622500840d0020421100b1540a0f60784e98440c1d00b910021000b0415241e500d0b40380d2140e803404200d40403814090310ba45000500b01040b0000e10108000c4503105405049403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 661515791 1250 661514541 661514573
    0x51620010e0304080c041103070305060307050a03031d01020111070201030f0f06030309030b01140114030709050916021e06010e131208150d0803071d0a0f03050d080103030203090d020d 81
    0x2c0c0020508000d120401d0055840890069406010444011030700545130300c8004d0610041c036941d0004256580c078104110005001c2c00303840b01c0c401c0340d281e04020b00100f40720341500b0a80c0d10100403030703840c41d40b06002d03130024005010201d50605000d5401540900411082a0b416035078501d40c1a10851036801803200460027a103500c1c100908504180404a0b0705800c1080d01009401210700140d82c4041005440701c1840348070340e266150400100c4120006038401544140800180500f40c0312510504402c0031030f0b50215035504a03000f4110310a0031215804c9491a0003590040080d080070300721140c1c1c8903070340400d00105903400e40d032600005d800d5100300c0000900004100800c10b102e40c843c0ca0391903032003252590851b20482d9201c48117448020900001c010095600440300c401c00d80e9940092800240700c0708401c0d03240c2080314030b03000c42c900c03080da070901c605100d42040f18098074a1038180c9400d503010b580790800107010310100480b5018100e8000c01580f580b01d000c204e01e062104014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 661517041 1250 661515791 661515793
    0x1061d0a0b0304050d030203010f03060207080d0903030b030f0a170703111203150607020f040f09021c0c0b0a0509010e01140c070f08150114010302040302030f0f060a051620010e 78
    0xc1e00740313420014503040e0b690001c0000d2610400060182c0306c003043c600001c0b607502c0a8050781d100703428906419079000d4a9140400d07103050040d01010560180c00640c140241501100e4445c2011451299150540c040c0034049410360400314829030303541c0004012850003420080d25500b0320070906072030620a0582c00302da011000c02400040a075000980d1115907085031020b00b400d1903a00000c10042c0081060340c4960350f06c40d10424041e510741c11100c4140d03001071424400b0781d41d0600902600c2c2070400125800008114040346a00e0307008251b500d94203942c0d40d400d05248800c00152114120582c149042c40410443c42c4400c2c0180c000510012007010081c001d504d1400d000c800c0145c0d4035400041e20f035001000d001a00005118445044402e900840c09501d402800160300a10031500040c0d058000c0141e1400c0d20040002c441e0f010032000b40460307141e0b0351000181c4044410075200d41740501d00c5c00c4a0b815586100b4042940309154032419842d00c2d8450404040c00c5442c8007a2801c22 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 661518291 1250 661517041 661517047
    0x70c0909050c0904050606010c11121506010f091806051203131710051305160e07090e06091803180901170705090a0e03040b0301180605010801061d0a0b 67
    0x1001400e00940240100070703030f00100c02c1e081542d102c80e00d480300100014100407540111501344041c01d607410203016005090340c50601c506031500d0381c490416540e40340c13860540c08046649544201c4a6032010603907942d0f4014454182240d514483d4002082c41c840591510b10201d40c0390b0b17501c0c0841010f201c61000540c0c0c3c0c6c44c0020b81e17180c00c00c00e0701e503c090b0050300814190b0883c4000441c0500803051075610014159030350f03d0b240c3c08191401000500a0f02c00c1e00101e0620040569602e0186d81c059076028056558200381102c03240004d0003001200c00300c1c5808140c0609117255015000201c0e4030880e07400e4503648520914641040170000805003c0240e62404c82c18100c504038090014019a0341803900c0400740d5940d100880d120740c60140381000e0010b081c00b83c00c3d61120103d0b00310384044d00d40d81c6e43e84001c03480403500203014010b031210010a480b4482c60b114400d00007155010b850b6001103030310b0503a054a0003906144080d080b1400c451052805076a1803041c170f00542951034059032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 661519541 1250 661518291 661518293
    0x11a07200909010e06180a1203060e0f060a060507031b12090503011521050d17090a11040209061b0d030e0706090b0d110d05010302130b0f15070c0909 66
    0x2070071180203884a000760b4900340350440d10040105640340c0c03040c1e0700c1e4500c148404c81c520084d8901140c15002502c1c000c40e48208049a90785500f21000b210f00d0300401664544039800004060318007500c101da0f01400b5490100003031070041000d05170380d80c061304200120420b81100c030020301025540032100501103c00c501c0549030003a005a003d403609400030852200f400c104403602450318010a4088120403505900040300d60b440b00d40303042e40c00020348401e4120300502070300c0b108141d0510303059100b8050005d000075a00094050915400c182c0954540c0150f005102c0250f20550229812120030003082c10301c80d25480200b0b51110fa9003000748003500d0b011000034200c421180d4043c1c0303a0b030000c0100300f06040c0d1000d120000e03504050040c0d6551078503030040800425a000a9503441d41e0041a012802201640028101c03802034070356401400c1c000d25044102c0c0e980306c0c40700d5800726000901c01014207011761200085000691014640711482e1076100c241c4c049988002801d80e20303110100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 661520791 1250 661519541 661519549
    0x2030a0b041b05031515070305130509091510080313030203070906150311090a290c280611070c09020f030414071e080f0c0603011a0720 60
    0x2408002c240c4903840044614194020464800540320218030011140340c441c1036501c0100240541e0345c01c054640e5100f80625020f030030f0f6040f4640089005101400005541c00c0c04807400d44900d89020151180d0711402031350b000c84040280101e4000085494082031820040009107440100030a83c544101d146104140c500821504422241400c003181000440100508950003080c6418041880c0c4442c2034040c07607901441c0e01c141c0d0300c41e6a5110001c1c0c3c000543e0454900a40d034901d245141d4003480c840c4055500c104801d10516920491a124810341501c402c031040c841da14040d00071100c0c5584030541a20501c0c10b85546003000000c924080003c40b000d4000100700da100e007903050504418202c40d031404000d00140c1002d18401c0e6004480300144000d0b8013406041480303110084140c40c0145c0792100740e02400c0c0c12807041c0c00a062a0080005000052600082c2068510fa00348001214154056984042c00c0c01c400c1c01003000103203040780d80000854400d80080c800c00d00080403c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 661522041 1250 661520791 661520801
    0x120c030706061a0906030405010b040218210c010f0207030209040605011e0b07060f0f0501060207170304030c03080a02070b04080c0a05041e1a04050f100f0f1a0d02030a0b04 76
    0x1000c3d661000d8502d1500d00c4441c1025190f0a04084441540700c0d580c40c281a400341100d281f01c0c542c080c0c4001201407104d40060742d8050150340c2a90219176400e09140080e0749198803a2200c0f803503034060300340620f1a42c4a0b00041074400302c9881500c0b50140d990380403940c800c9064404550168070745006004d003240010344d02c60b020000e01810513407103103841401702642c8a41ca03c081d0400341c0756540103034900b80c81d40082c101c584030400104420360707450700002c1d223603801401068000b014503c502c01e0190f0740041a42c0541e5042540582c00525540d2508116030044441c40154040c0c1c0c0300025032007a4010180004000040140a000094104000d02201d031034100034070a9140401d6a01042c41081411888030f810900c0021f4402002e034000ba000311000b1440c03035009007400c0411900d10298161640220300d00e10410aa59880341c0701f03a001d86040380210381d129500184100403800c200001500c4642028000c3e5180820424105060342d20486681c1440394803940d2911240c00c02d4030417 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 661523291 1250 661522041 661522049
    0x20041509060c03120b130603020a0b0c0303010b0c0c06030a09050d0311190203130807030b0c1908040c0e1f0608010f050103150503030403031106090601060e010c05120c03070606 78
    0x2005440380d0605001816003001c203903010303003041a50211054034400341d0784003114805004101030408880d0324442d10140c06035010407070180b02c0d43e000000b51030308058156003290000101542c1180e0802c2c001050b180c0042088410512a5007940c2c0c0b0035840d130400a6014034140d050114250040d410706615040c5124098000c1614003100315516251100c03e032504d82c28508003e4644082c1d15104a00d58060003069212032910300c900007483c1c2200203064021644290075990265940e425540b0721401130803e00d205034101d980c901114184950070b001d40c4244505880701c0307141d07150700c40c05035030140881c0c034000320300303c2e410610303610140e6062814018615031401e00001e60404c0c10060303a104851090b0350525072982044820004403200321009040c0c060112900d441c0d0300d0a0090080f414600520603901030f42d00030411460000c40d0f1241610107940710041c401d02c54000444480d00d261000b9030312402004030b190746034000000100306603003680c0d0003142c8071200ca044c580c3c211481a40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 661524541 1250 661523291 661523297
    0x12090706050702010e27090d02060c0405090601050a03090b010e0708060406052b0b131b0b090112150b0a020c010e090a020304170c1e0102120103110103200415 70
    0x40840184c2c1d1040840b004c564054500d1b48094440c0e110082c8004142c401401c20000c0c848204880c04600045101b0003140d2582101c9450312842260b103590f02c501d00a00e03801c004038000040b0154043c07001001030000c00e1a0000b1020210344803000a040281c108081d846034a9080c0035603181e01801c215041031003201c0c1040000e28000018000c044200340300410290b42c1000741104081031491104410b40220040d00325281105100201c0415200e045a2000c0c081154801d11401041c0400596410090075468884002c0065507078421a18000c104075898402401c2c03a4079102c0c030031400400d22945e000b510b40ca01000040d0401925841d5941001150b540340e40313980d690100155000300500c4e40040c0c1d640c5903801d003494904000c45102c180c3c0980041d0600f180c0703200041a40c2d4115180e00011448404407405c2c1d400e070311071182d888106075003c000605c08039050300d07191840b00744141000640c1c1944020302056035440220310246141d404242040280e0501d0110a030010304d0786 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 661525791 1250 661524541 661524547
    0xb092b0306050f0d110103230915010e0c0d020c0313030204050c0f0f03090c0a0f0501030f180201030b0a120b0a0509031c051332010c02030406140f1209070605 70
    0x401080e4003402d0113201402d5541124201c9107203900a50003501448030181d20300300d5140302d40e607440c04540c505840e00203d81c400c0f8505142041280c64034079050303d0303408003899041d446424428035140c0092210760407442e400c01c214820235100f04020680807680369031220a1510b035004001c210303040244055000c18041080303014031002d160803100442011801592031780c40c0c03900100c0c54011000c82c4140c10141504e070104103059407948810403076100360303030038008418a0305403041514602c3c00c0c0507030344621502c00400158081e810401140c400504400c1d0710507501c0c0c80b40510700884000c269031008203401840141c1e000c50040a5002514800035407602135910a121011420400b01007455030b914008503888080700910f04041c150042a81c900d1050401240031281020703510600c0b0940750078951400450060141024602c8950081c500341480d205094482003842c07011008410020090025038404c120701414203400e003941da9851924200c04140d2038039120b60005000e101d424 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 661527041 1250 661525791 661525819
    0x23011b090506040501120e061e060f10080a0f1107110306090a020d050c0a061116150f021f270c050d020f040504080a1b0507030b092b030605 62
    0x140440f8200c0e002032a2240243c4200c4d1710b05001020f12620510040c0a90b40c140324010800400d400c41000d40e4404403115604c0b00030400800c1d5400071409034001d07040481e0050078074080c0e00700f554000da02e41c03030100b00086003480f64411601440641051800081907030001d108103c0180d01080d4420f800800e00c0741441904256103c0076800000c0c8280804403140301003001c18032080d550000050301000b003058541c540540400740203042110548250802c1c1c0055105101600d0103d070003031a27140c94211000c46044640204100301041584a030cd01040e0080c51401d1510b040d00076180d400184a440d41a641c1c2d240c0458048143d0499201540e40c0d4045040308100104032041120311094810f954400308805915001210303030700500d4a8100418881e88100400e504d88242d540c0004455020f9441c1040d500c2488028000c1e901815051000410755075409410000e0502292a090885008598100e100743c60100c50015010b8091a9031a01802018003411040f10004880851 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 661528291 1250 661527041 661527049
    0xc0d090c080708160b0307111005011404140109020a05070b160801450f0b0901050102070315020702040b0909072103020312040611070b0f0601020a05150423011b0905 73
    0x1d203003c0d10000031000004103200350f014810303c100e200004d80540b1508140350440758012b000c00d02c141c1e24400f880440c03140721881d083c822aa00c08130842d50b01d4109900701902000250071035040c401c2030007070811140011921502c07130035110b994001940c035621a4030b150010100403042e800703d071545294049060302104204c54820350410f4a41480e95888032890b01c0c1101c3c80002c41c1c06441d030515080b5a101031240d15002001104001d641c640c11990b6600700480e543d9690b0320024003085600c039900218442e10742c00070100315000510229000404030000750401c501910380d110ba0b0344c401c5100b049020f45064442603803043d10b6014120031011610f0280d1a441498800c001c04000c200018040120321703440b41013204907416803541c031140350f0b1805103401e0b501a28010850ba0701100050b4440d80700181b98921381d40d00002421140c41c072113518400e0030300054070480d000c4144602e11462034016200d414502d424500003c43d00141c95070115001c000c010070301d0340402c0a078100034082c03511 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 661529541 1250 661528291 661528333
    0xf1e050103050d0c15020a020c1009051809010207020315100e040b01090203100816050f0901060504261c08060d0803072f0f190b0606030c0d090c080708 67
    0x201c3c00e010740c00784013520380003102d1001c010541039050301c00306100c40b0181d400101624082000c2d501d0311807013408000b040d1008030781841a1507101040080d0748440c1d41000150a402c007070640005801c08480ba400682048082d40e910201c41102d1410004e40c04241c9c201e030001090061002c019504054840d170076819014001e403824240c000011410703800440030980d00501000c2c0565104100c120008110190107101c0c0324030615075001050094604540103604851080d121a40780c1031400c0251034020010f002c04c049010540062400003000501000460008080116100303071205100902501c03800740c13056005200d0b500e841c0000648800031640c00c401e003420f080c5200550301094042d40801114000c02000c0b0082e078003010070900090420700d2070144030989039054801004090340f11559800a848400346901080ca01c0c10040010364001c9142d1101520f441e040f810602d00750744040784200c4459500520070083c00600b4004800504601b002400e007003074141c40c203046c80c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 661530791 1250 661529541 661529563
    0x90f0e06010f1808070513052401090b04060302071e0201120f0b1206011511030406050d0212040c0905091237031515051207120f1e05010305 62
    0x20802118038801036014495100784148031104004542d031311107500540351080792061601a424100e83e0000c0080c081c0070b80340c842c03a482200411100d030490089002da400c1090458180410341c50082810304c81c5e00c0042001d00920340b0050b070f407100c20f440d2103806511021001c0c50114100201c41c00140c1c1d000315000ca20800d060004074130070300c4108200000300b80a40110354007000031905286080004594581201c950303e43c44540380c4442841524000b0b01d103844e41100f5082040284071183c001c00c0a00b440900d40b003401420040001d0480542c3c0c0b0741510150740b0642011802c00072040300340285540005088054121031a10001c2d250640c014403c076400119070f043d00d00c0d0080c40e01881c0420b81400c500b00500402041600040d00901c640c440505202151460100341d858180000003a80740303182e5152468003a84401c1024140c6002c0c2041c001c10041c800c145a0b680400d000c0d5042d5541480303800205941180e0104504680301c10f10400a242803400405c041503010400c0c0d0700304 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 661532041 1250 661530791 661530797
    0x21e2b02010f0c391410030b090406020d020d0e0c09010504020a050403021c02220c02030712080a0f1a0405060a0b1c11030106091d0906061302090603010b0901090f0e0601 75
    0x10303d001568480d03850409504450342c610340304500040c00060030361901d003071901c156202d5449403694001101a00d023410710142c5c0103440c1d1008540050003540c002c0c0040511080010b0501c0010308050042d40c40355609841e081c2e1083e1540c0c00c5a140240c00c903401000b044404500d094000c400c00750040c00389100c040d10a9001c100c3da81410802c40c07200b1000030b98014100b9990403c44800308224204c003034000d00c410780c90703d00360300e100e1400017048482058000c031841d50380c3350104100b141c002d04010101030406481c0d4460f1501d25140340a070b460024002c0300d200a51216540c140b0089410040240e407203598a920100114000703402181d94088809003044244c80c46980e0b50009040d4000400d403028100100000746e0700e6101c03441c074080d035101d6075400c14034504035001000c441c5420740380b0031000c0d041070300030902d03514103403442100351529248051706003c0f4840c0001c0c3d06820980c0460019080058640a15a400303d005800340a442d1f1f000038900b4113000000c51507801c0205010b041c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 661533291 1250 661532041 661532093
    0x7171303020a06020f13062303040201030e07030b07140412080a0203070b0f060901140f012714030106081906090201050405031c0809010603021e2b02010f0c 69
    0x1414030a00002d00066000300e4155900c1c40800700558981e44250103041c0204200314011490310f1007850490140501e145955580d440d030a9030050496001030070880c141642d4032840d28a5080c02d004d00341c02140144e0f61102c60b13150118000d4400a91b80c4003003051068200014060000c11041e50030085800c411442d4a4080040080c0d00d140309514000c4c040340b980100308074110f8542d000c0940b150f107050f5861809641e039200500d1107100352109450740044200c1605009511440e544038807081e085d50b500c6100070301202140007103003040c0c1024130140c003c4000304426003024064540140394110052204000710180b40354030f0f81c1c840c2802003039603460b2183c0b4410f5a00c101c09540c040c00004056800d5001c01e50760840f809064084001e011a0030100068010441807040c2d40c210394014002c0d42036a412003010710308002d80c90170800c1d8860501d90010303154001c0c00745900350800b0300c260300303c0c0b4042c4540005410844160b141034200b145200101000812002290184100300145442c2c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 661534541 1250 661533291 661533293
    0x207170304051e030d210b040b040f1d070f0902280c0b071d09060612070f0e0301150b07020a0e0a091104050112080a030e07030b010509071713 63
    0x8158441d0b9440150b1004082d0200701e51181001040b4804003000c90440e0381c006141c00c0c050f2000c0e001403082100041245201d44007498983d0041c0c0200600288001803222201d03001408440c2000c06000845076607007410a071124501105c030b022201b00380e004240c084d00e01100204200c80c940501d0f9000d907004504018800d1003440444034001841c0c4816403640618035008142d06081c100541d41d05503007034003141c1001e000b2080c00c0c051240c82c00e2860040c50144003480003041c400342130180c20140c100190042000040344150281c613041c0c0e1070145503247d0305001010514820740700d5103e039140041c000c00340e8040e05111f104540d980c0302e1070f640380c0300ea500000f03032001fa05a0144290f41d041c48200b0181e05419840031000500c1a88080685800c103020b01045901c01d014050305581c507502141c011034001d070050010518246408038007400702c80300031030602c1030303992003100c90700b0212005202500e40b403081954040c100740341c480c554100321070b40c181000d400504801040410101c1400c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 661535791 1250 661534541 661534543
    0x1801141605280302070b150a06270b04030c080d051206030f010e0c1306030b0406090c08030d0b0114160305090103060306020f0904151206051015080907050d03020717 73
    0x20b5a000308049052000e01003880c0050701079030045004a9441651a0015000c1c200c48600c0b0f0040e040060402c48595044c0340054850104614100b010001801a05035482070203080034000703409030002d002c0d02c8901e1850078178a802c1040d00309201941010a628104641c030800f601c0c2d44580c1c0c43c82025407600c80c0d001180c02c3c10540a10b1307003065424001c0c200c400340f0b400100710303084101c240e400d958406c1e4031801e28002c951807808002c18000000c00480d0210346603030000c808040c0160910302c0c0f1325a80b03c44840ca0340e844100800e88860301e842d25610300750f0700b08c1800429542c5201c030302450700854078000044584080c2004017445008a440f12083e40710380c1c8108043d541c0884210755840100c850401d0580021500314440c0d4100703c0c2402d0000107060039a000c542003112580005005691204086e00c001800d135002100e00040014111419000013030010300c26490316402070034030315981d600700241504440d0160184011075000694009008401c03130303007a01004403429241410300303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 661537041 1250 661535791 661535827
    0x2220e1b0f030403080601080114130507141306080f06060a03111606062c0109020a0509061207031116060f0f0603080c071a0405100909051801141605 66
    0x440030503070201c100020590490401800707400242c98441460380c0c0d0302c1481503038643c440549500258084000940482d064100300c1e0011102c4c205442003004040082846070080250364600721902002002055080140203421820000191085140207804a8101e11980030b42c0f000300b66a0383d2080d06003509080603202c481ca02060f48034001c40172800d0510161082d0700607031041040c01113101e01515542c1e51101c1c0e40d40904451814580e1802d06030700000c2d000042c8401c180700c2e080000c02110b45e1600010800c09906d045000440e092014004007240c0000440c81b21810041080d510241c104416a804480d40300502046001d2448003541c0508244010240e0304c5041c450044100640344018045050070182154030310380c1d0710b03045583d1544124141180d0440d08000600043c1880c041190a400c42418500c55181e50354401c6003c03030314105c3d0303004c5065825030f20141c0814400c2c0522603506000c8030320008242800742d90040d01083e000710b070206100c40050410080d016442503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 661538291 1250 661537041 661537057
    0x31d0109090608010603060f0e0601060f11010501030b01080c0f06030606090d20131b050a0309050d0503090c0409050c0415030f05030306120f0c04050907050d050102220e1b 76
    0x410b001d0b036961441c1c20b5001e003240740400c0b6200e03400e01e02100c0615016100e12011a5200c0300100301507464000c0c155405000041ca200403c40b0b1103040e142c015809019060082d40b148084900b1503242ca80f00c0c80c2024010101244515443c103031003155a0784030000e407074100360301701d030360715603c0d120000080d04c600c4441e4002031404001c1803016030004891415400002c1c01a54602100b03146007030f644085901c1030030b21003c0c0070410425100702510610192451500c00d040018182450b600d419107000302d80106c0100041c2c00204004401105112044a28800b620148074210060b0b641580300c64140d500a40541c0d0780d03181c410940340d05800c0c114000e60b08886907245a203402d091064990b0f01c101c400c14042d00811184055103030001800256014569020b40318070034041040002518011300810490702c19500d001ca081e903951100904c41d20711550006a030b231070001c200780c402e036000c00c0b4541c000c0d10001c4104022211980072010350041c42d02c5c1c9240da510b4038210b10b0386102d0085c3d4071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 661539541 1250 661538291 661538309
    0x90a1704081f20160f0602070506041104060b120705070b010303020c190503030a0c0c050a0e0a050106111c02100c0305060a0e1e090c090c030f0c07031d0109 69
    0x90442c00084894070240030900901802d120545212681d0541d0207900d280085141d0710801071050741c55595007194070814400c0140d01500c28540e2510030a03600804000d44203508440c00f440104001c0c0c0d0003102d2420401c0d03509008252070220f00315001d000f0307891820618081c1d4800100224407610843d84e1050b4425003051031547c6a040084d0b031f811100d080345005083e004240785960303160006140c112400200258507003080319508a882609400040303450103020341003c1480d540384969080501145600000d0615212b03134281c00341c2d00180c1c400018400001841240810702045502d8001c81400c00201c2429221a040340ba0018040384095000d1400c0d04001096516070003da0040108442c004051911100c2d021240c1c40161912070720894036826070403008140101c2140e01a00800948907030303607084000301c1c14190f0100c580104a22000081005401c40400216008000760110b98141006580d01a000f10600c1410008403003003020f00f00541d038810f68011000c1c0c440d0403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 661540791 1250 661539541 661539553
    0x3010602030406080c0f0f09010e030d020f0c120c010c14030d05010315110a0e0312040312020712020a260a060f0b0301090206071b03080705070609080303090a170408 73
    0x15000070344030b030801c0c0520000120560003003201e002000003a1001100f650803031a02e058030780c42003030b9111760010304003605000f442c91980505503001d010154400040c4d401409802144a2400c0e003440310680041e840780c078684601990112f40050515045002030801d0801c0800c5404c00e00221a40a020118540710000307030300700e0310012600070504036403141c011030881e04803241c81e4005544400e290031800200600c0405e644902c100d0940f0500d01c0084e003a0b170140710380c00288160399801a0020341d408880c030590708402e2941001f01a00a0000b5000140c020f10f4550000d440103c0c42e110b07210034a8807688154540c14186c0901d4542450304000701c807120100d510780a030141001600300d1510740e14002c0864854101802000c503031702e0380106010324010007540c4000c40c011010910300291112000c0c088001122803004024040c000c40c01088400c0c40c2940090804480e40c00c00c00349038205000b07000704a00d0016003070189660110740444c0d00d076100c02e400080745c0601d83c0460741e2031180b5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 661542041 1250 661540791 661540799
    0x120f021002190905060717090105120c1b06220c09050411010906031109040c0512040f060c2c01020f1608060c04240302040317091e060703110f030301 66
    0x100000c002d101c2980e88604443d15950400c2180398044c401c4003402450242c0403210700c401da900300801c0c1050050401034100072888a454019000841c0c40141d41880010703c6007205285c02001951000c50b000180701920380301c42a04140b85555594a541d0b02c0c2034004042002588807a5070007a100c644410407113031030300d42040d181803030308071445d103010480350400401c0380b9220340110880c0b0300756003281900e4081d000c0280801042e82080080400109001441035040c0c00301c290b078003941c001e0740e803028104e01d1418180c0413200900410030074002841d0701060003081d103d4101100c04980c3c010325082c0d4117a400140d003424000b154040050088505085c0c800e0704111050703080d2b13021003044503843c0e904c002403100244610301605903540d003420a565403090240c108240444e25515000d81460342d02d6071084140001c000700410003550104551140f82807560030034620400600d00d0004400c1c1c2040801c3c4580705000010b02008501100d40060300000c200305409118520201d82d0399682d2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 661543291 1250 661542041 661542067
    0xb011209291b0a17180d0504090b030a0b0106030504150507030e010516050910030f180219030c15030e06150a120c15021e0715050403120f021002 64
    0x1040780c80c0040c03060b01c10302101030840030105a4101c910562105801e40d0042c151314070b040b01e0010068968480700c08244140c0d644240000780d1b8074030b90303031711f82c141c440382003000391001c3c1c480401d251402a4000c2c621040032a00e02c0c1003150440f03905082c00107440d219410850b1071000b200900f4118103080c1820b214a0507031590040c0310110010008010941f503041c1d80102c8031810b20203440c00101d040c808140503103451070080300c50f02d10600303001402d03200101c0c03030f44143c1e8601c0692915009403e201007055061410580e04d400100140044500c0e0640da00e5407a185046e001e056483c1400c601052003090007640149201503110003103032128a000c0c860070400504840c2028010600550002402c0c45040340c3c0c0c40307040b40e1112006000500b050181c10500b5007800a00c8110711a891080c41004110202e104020000710058400c0504109000c485810f4104200c03003005400c00041020440b1914412200f038121310f813602c6108854a0120f2030103000c144014419840001c41d011a016 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 661544541 1250 661543291 661543373
    0x114011e05151932030103021c06060b04060f0f020706050c030c0601031104060501051806160f12080601210b0a0e090604050607110d030905120a030605040e010b011209 74
    0x413000d0002000b00310300c0f001804042d414152212107210007800140010702c0c00340080da2004504485000c60010b0a0b281c607400c1e9200c030751090b2055240000d05002c0c0642c4800d0030940184142844035007644031140096460080d4030170f410402c8004070740620310001c2401101c02d0944142d0440304556102c2c01c04035206902c41e01802d10840c90203100003100c4d406541590b81084a8032604c84c90302c680e902c14010580e0101c5102c3c5018140d800a020000d082507002081050042044a0452004410280004802612481c103021070b0040c08803500c074404041c101d48130624100450006d240101140d0342400c0390b00a01c131101101010040305400c00916580310341e0091702103900e44e44442c001620f1010030856103054940188910914190094005080051280e4100d4034940000404c040c66508003004800c00251614420012464540603001c1c011400f9802007140b00301d1040043c2c86241d50400074810140c641a00038180710740000e11602d0111107800007400c120075403110403c1c0074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 661545791 1250 661544541 661544567
    0xf030405040f050108060705030613050f0703050109050c1e12160e0910091806020a02070504060503071215020904060e01050118180e0a0c080114011e051519 69
    0xd80b4080005811981901640d4102c2d24a4405030502e9214440c048a050344000d04450b000500400c2000d6100350610a00d44922105105002141003000d4010191031040e031110403520300305018496a030a600b804c030b4122400740604010190070300384040401c1d0040b24551000390320301e4800c0291480c0c41c645c082040360640d41ea4000c05139484010060489400d50341e1510820510000384046500c95000c0c8804500700644a0200040d9a9507901664080c0180100603007082600f0402030410b07010f110040c0208502501c1914240811101d090a0b070b83c9020b408001030224003161561030303904030340c0c100740050000d2010342c0e101c0c85900742c2440284074060008d81001031041e68640b4411580080d1040214030720f14140501c100c2c0d0002e409141804402809186070f10800108030741c68100c01001000c00104650b5034a00158034078580503400105c400d1000c1d04004c50504400c018101940c40072250705450840c0c50815480b1406098645541a540c0d41421712820b50400a014850 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 661547041 1250 661545791 661545799
    0xc020d0804050a0803031006031a03100e070501020604080306010c0f141507050a0e090c09040609270f02040c050f0720120307080d020702031e01050c0c0613020604080f030405 77
    0x25640c4d264181da81c402200c2600009421407410f00595210b9000864055211035001c00c0f13211070840040e0500c27401c40c8208950701c1e501c42c404d41e6061410302008000f07100900180c0000c0c545500d030100c192100074211410040c50003070140c10007a003241544202c41d0030030f070004000181880100d0340e44400300340c40c4108000d08400512054801c0003194241245a59041d031603180031001d1240d6882c020740900b0300200240541c00580d100c600c540801821182d41c04502d801841810890500c8210100d49201c401800c07904041000096580115681518001402c04d18284211042e009449802c511150700040000a0012007604c600842034407031803181e603035142c280401003401960211140e0940080c00440f000ca045500640703034828408030b000d407400b41103900180c14007090035810300c2c8628441d50365a003400c40910035264014440038000b480c008000c2e109035a54280180214064000103019104540302e000c283c0300104510000c5030b02112052601a44a803c903006050003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 661548291 1250 661547041 661547059
    0xd0c03020709060501050d0e010b060d09060f110f03040f020d0317060306160311040b0406020d170609150d080310051504060f0f030e03030712050f0702120a0c020d080405 75
    0x50b8030058030455084450585580346007062081000c009001002d003000d606540c0c44110000546600c00103008140081e40000b40c2d0780711070301e40b150841e503400a420360914503046c00b00000c0d842031400c4800141d11365003581e407299614545101c041f204d0f080000e40000408241d00c04240e0045d110b80b8401e141020201e540d03643e24070034555981011070302c41000820030040001151300030390249542078080d0002c60b02d40703070b140d50012025500541c00000107030300c000f071074100b540d5020b00c0d940507013003001e800c0018030700b00100000c0d940800900107402c0d2034880448181603964444820308603d40c4003541648918180f65111040d0120748a0b40d406021030f182a0300345075614101b15004c0c1d070007507154040c002c080351804a614101211214040c180d45502e6080e02c008100042c46c411000c55030740c80e0509030b0b4401c040040d201d001d0103145a00c0f1000d403c0c4008242c0100d4246181c2490b41e900f580c81d40180b0100715801100104040c1d0080040113240007070280c0360000300282c0320180c0712a02 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 661549541 1250 661548291 661548299
    0x21c060c0809060613060803070c1502060405030414210d030b0f1c03120204090b040b030f06071b06050112050114010312211a040b0607080315060c0d0c030207 70
    0x5007000d040700d40d0109034000d40300084141c42d040c56200c400e091040300c0015521344400900345140d200c4203041d13400701d45040041120b041c0420070300c20344041c107201420f00d50800e40c2c0c42a42c1d80c001ca0044c01c202410030420608241c40d403002700840b94070a00e281c0700000580e084550b80b1100804140c40003c5e0504120700c40714141200c040458500142031540d14001c2080145001c1e98494004c4080001d00300d0341001856a5002170310241041c1c810000340c13269100c0800040710b0510106601981082028581c650004544203030f0154031810b080e8401c060320800c40c084980b003d000140064500000480d080205d00f29a42244d4400d8000b08403a4600740c240b2100d0500c00d00c070061040365501170881540c1c5c4260050400401c144d0041905450213a200070180c500003040221040e0072144082220b1a05010315a04a8010fa034043d242c00c400382c882ca0fa09110040c811518900071510102a64640004642c00c4000700300996004103002c2200a244400c0030506a00503c102c9902107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 661550791 1250 661549541 661549547
    0x1413051c030e091302090901050619290c0102040b0304060b010908030f091c1a060604060e061312050a0b011406041502070321200705060c0109021c060c 67
    0x184281c0c00d07488201540a640741004051500188010110a00c0304d002c2001030300d503030b9001ba0055132098004104d130324284081c401e404440040320091200010030030024500c41484892844030004040079800359031707400c5100700d0310079035160b02000e40c0b0000c3d0014100e00b400f0302650242e4400c031414080014035800444090401d4020f1408540041008601500f000c40090039919400b500a022100d02c1498102c62011700e6081030381c2e40d180c004506a081840c4509081d8001000c41d98035013064100301000b0841d40d407801c1090701448001a0302041024644050401420040c4410840c01c0c0d440c50086d4503684910004c544407900d880010030244164040c0312a40c88014060b241000d2902700e1a29100c20841c820700b0640c025400d01002191000c00b503002002d9030103200480c0100301302d100402c0c041c0d030042c1089100c0c1000c0b015107601031303010501c0022940201c030307080d80310454481610300500321500c0003540f00c548081500160803215a12580403070003108200054030761003002f9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 661552041 1250 661550791 661550839
    0x110f032d070308160f02152d040614090904030e1002011a041a040903020c1005040f150212030709180911011d06040915060903050a020907141305 64
    0x1001100203004034008880300000b0890713024040d003d601c91002c4990049910f001c0301141c00d1200c80c80010f0301040705c2c207201000303060072540c3e110030090790707c521a540e420324081d50090030200f045600c01a074003c1070500a07182c10f01401003200303406007810b1501500000d103021b600780c01001109101d05556006105150408a01c1c824a0304015810020000103156184114050188941c84191a600d0381d1044600c603070b10907001000c000154004110031801001c0d0800200141000144444900c0c50041c10031034540c6884644030915090080c0e00b818420340002c941c5040120070849001d030302072101400c450303c0d6040d49110300c8041d0601c0701940d103010006002000100080242944120014192207001405400034810304000089542c1d00c2035210303081c801d48806103c1034001c140d00403800245914204200514551b41d14a610703040c46100c0a845446104001000b01d800303a091030b030743c952007080e6250b510329040107882c011400c0ca0045a000380c141e509154000b154000c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 661553291 1250 661552041 661552043
    0xf05090106210e0114010504060902090a0b09030f0a0c150504061b030e03190c080a0c030f03031b0203030415020f0d0f020705010606050d0e0a020607110f032d0703 72
    0x40c03960300d050b0300d000000441d0111441c02e401980e40c40503244851400e104010088000b1904a002545042c0800056a0b1190064141107104200c0f558566803030202d58402c65862901c0c1c0c94a5010a0b4002420886420f81070100c6004000c501810003486000013000d4800c01400d81d45044003a11045581d8052405050085000030904406100400c29100021403080c42c0c80d007041505400400e0070102e100d40269088041041c41004210b00c444403000540742d0100100365044a0b03489048403c4154031000d1308072030318800c2140516200b40c00013030b201100c40742c45111140d401d6400950b0b0340d000311410f8401c3c40300701e0a0043d0500c458000c450760141035045050034050f040a80f1801410320070b80484180307500b0008280000c00030302075840100407a84070543c9500350610310501f903800d46907210007960000c5662900613a113580c196071746a500703c07146500450641011556a0301c2041520350305205a2102d040040440c4803130f502071440303080040d00e1030700000140a41d0780c0c4035408 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 661554541 1250 661553291 661553297
    0xa060f0209091f061d2e11010605030309010f050f07080304030905030f07052404091407110303040b01270e0f15060901031b09020304120311070201120203060301060b130f05090106 79
    0xc00210700d2502c0915550302c184046c2c1140c0e000200d0480034280418154840e4000c50b00e44100300441000c01e100b214006d1405901944c0f074446000c00080c8503801480f000030a00102189100c00300980d40140c1c1c80003584600c02594030700b024107001d021200c41d441102c3c4a4031136000501c4984401040500132244040e080b00b254403c00301048007046400c1420941104040c03000003034000240c011030716000d261481e021074030304020340f008041140b4004041001e610030400e000002c0d1010640504458040c3c507155000300100c3e440019503490900400b030540d040c4440401005004903400281d0321003001200e004144080d80d5940b2444100d820302d9206040c0c4004001181341c1e01c111403003904201d01c200f0032041d2a00542d0f0100c0e001501c0075203410a45403003090681d030301031081e0880310304c001d40e003141401070726070000749019680401486419008000b0882c1600d094100c50080d040814400f40c071062100010b94990f0707540e114642c81c1c5156030100080c18105182054180c507a955 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 661555791 1250 661554541 661554587
    0x30c172a0c0a030b060a0f06020c01031d060a0f0615020a0204090f0b0c0d0c08010503031611030307061401060e090c2223010305090a060f0209091f06 66
    0x25010104000140c24003414040c81d1407070411030b0365101c00c440140d0721035146101241425410301c50803040a40003c440800100c00501000303800144113003018800746404502c4154401f00800c1b8800c4403080f10b802442030b4070910100e05a1a00181080982c0c500d08001390740d030b62820701440c4040b08030341d003016070080d42c2d0040240c202031304000010740c041d4110480d03016450f96465003c0400700c459005005021404161151a034055042a000e040c6000c0b4015410b00f400640c4038070903551070900383d0424040c010104045d05040c0b550788000102178036141c5500c3d0601d0400341604400050f6801350080001c1807450060442c0c0d101004003401c0702940d40d5403007503906416403000c418880340d043c0702820b881129421001090251101d0080c60340011905060307000008820f52019040c181050108006103030300040b0741a0142c1c1000012581d2501f40809200034403c08552980121208e02040400a94480e0956a007445255001300c2c00382c0d0ba481c2228906245052018560404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 661557041 1250 661555791 661555837
    0x5060316090213080312090d020d080c0705150c070203071d0c1c0f0b240a23030c120f04020603060f1809010507020c061201060302030907080a030c17 66
    0x154003403d00d4900d5003040200864940c00c600e0715603080920b5a42400a181e010460403072030034000c0140c03400480c0010b090f03c6501d14406800c0581c01091042205c00102d207034018030004001e00325410100e0107000806040c85481300b0200d9208c150142d01074402d03000d0000d40c003401c520388144000c1408010b82a45d45035800c468440d075010003c00c0036406a1031074a0000d1202d18410a00c0c184205200014403480385400d11058207400451034068021403180f0b441852050320440d0b84c2000e880c5040c0b180f5400c0c504680e015a00410f0a6912140001c0100801ca144083c0104040d065540081e034035035451034034a845000040314001c0d0090000d101142090820054180292400074101c1b500750312403404840b28150300f1501440030f0f03034684081c000348030740609c0081110401541c6c001d241002c0c02c1c090100010046c072607001059400000911180341c1807100d88090710090040e174200e0315481c10002c0c41c41030807110a07141080c00346046410035020208544007001c00c441a0390080b801 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 661558291 1250 661557041 661557059
    0xb030f0604150e10050a06050f040c020703030e040e120a090803250f020d0c2405030402060a09120302010f0c051602040915060f140409030203160804090905030a0305060316 76
    0x200c00d070f04801034490031901000340c00c15401541e202d002441d90000c1c00500d0001001805481c18000ca401240303011149101d05d50b0104948003541d4240c181507444008080209004001100301980035029509840c5800e00803100242030035000f0703584450180d9240c12180342c8074452503804424030780800d8600c000d0310b0a00c000f04400359010354031800340a13040385c0110750301c0b05040740304580d03c90342040f0074030568035400442540c0b451140f04050800c5400d0b0300140482c03001410180c401c2c0300c08901c0c100254402c1d081000a460141c610a968a600340740c040d0203400c00414041c0030754105641e20b03820b648110150340c001402c941900c1780060054082c04003c10128400f40c80c0d2840018104409007030300c3c00f6041c01042c50700800b4a0644c503048004450705100b5581a110b5410040510007085d0b0010580c3c0700c00c0d6070201c41d5001303402c480c074121740c25110355070040791550700b403030b070450140480030003c0c12001c655501d081c032032640c0f403c04064480e4446046401100c0e0410b07800d0050b040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 661559541 1250 661558291 661558301
    0x60815060c0f0601051e01080712021b0307031106070c0213112701020a0210050d060503030313050105090312010e18060a0203011d04051f02070c0f050109060302040b040e061c03030b030f060415 85
    0x2b4900c6001403620790303280340d400340380202e594161186a10001e20001010303800400d04161a0600c40a0010703030900000c02043c6200c2407201a1141c240b034000241000d070300707a002111902d500030307595070789152000b20b010742442400700c5541c6806150502c0c4440d940045401624154001d045c5000805c00b95001e8905401c07a20a900d2011368505000c20207032004c00040d4000c503004001d001c0c0c0341d2061b180031800e582004041070000e03002406900411100f80008905543c06070820074103958070214a0f0400c0344100c1d451123500d12805042c40489a207039070040d41038542c0700100140c3e16044c500c0c08503e20006440c010f01c25800f80c10300c8070a07000d21080400d415450040003518000c0640c8030360300c0d406c10302c0c2c001c00d09406483c4400c0281d503810030400401002039040a509040c603041c0035030643c0c0240d20840a81080e010300250140e5980040240311000404a90a410030300b410024018445004154000d210300d030501d00e9070322000100036120f554003200f0008440c003d401d0f100301801c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 661560791 1250 661559541 661559567
    0xf07060804110d030e040f020c0a08210109020421030c1b0806040b1f03050d030c1403090f010c020a081b0f060702061906060815060c0f0601051e010807 67
    0x2e0085244074505035503507451182458002e54520984011500c1040111600b411a000c0300c54810041c02c04200702c007043c88001c880d0080103035911a2a640365098003441c3c11202842100c000c400003240d903541d0341d07001e002a03403075542da441c600c070301c07a0600d01040d5075400b140603001c81c4580d151880010903440c00319803020b80130005480b4265030b860565140403402d480031610300c0140b1040140001400b0201c000e00f01884107600000e52640d15070301d0300c07010030b0201c0b10205a201c1002211031801480c0303042d100022180000d81c0c0749840e0030301c84d4641c0d40f86024081c0300c0d400e0540c101003052002803402042a00310005514156421070310300d1247c0c0c1d040703440910900610040c140e030b241d42030142500c6540c1540242142c4e207442140c1d400c5d04040241000c1166260641c00d0003c998004040355101050180c5080d101c01c0d04800200f20740a4445507510300e200d08103044081708004114141200c100760360452403402c03840214040244183e4180b4001101080080e0741340c1d101b195680020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 661562041 1250 661560791 661560803
    0xf07081203011d090f030a08041e120c21030c0e01021f05220503030106031103010f030b060d08190207140f101b0606060f170c0703050d060617090f07060804 69
    0x5e481c64200c65085421502d0b000000c01c03800c41c01c1000703004200302e4040306004030200c44c040f046606c1e0b03203078041c00341584014820001d0290401c2c0811032640044048844c400b008185c0d04005840c0040c00303041d09054980024446400070442035000040d441101d000c2d44a1446d10080c8400c03180008102c000e0810114a40701202001801003224408400364050b4002c4c65a035030410f800036003550704106410856a40400c0100801d84031090f410007645c1d4030240119082d12000b0020741016012f602c05030682070b0000d10303890201d2514040d020300c0344054080c0e40d0350580d142112490703044c02c5c0400c1030b000081c50b41c2c6041c582c544044482c02e0143ea9050400c1c0c11164a0400b0105407100d50044400700d564000600c01e580e00059032000c11146480e00f00b1040700d890007401400d59020b8000611403402146120400d0300a405582001c09076480030041540e0351035008111044694904112005100c08900c1100010941981c0598058010102640781400403250040010425148 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 661563291 1250 661562041 661562053
    0x41e0c1d1509090103060b15030105100c03030e06090d0f03021603080903041d040201080a09051018170a08010501170103120c02180405010506010e0312090a03050f07081203011d09 79
    0x307980c1c1043e11070103180600c4e00001e002544030305003c0740341216626040518401e000420481d40e8072188210155628030b0042000c1e0f181e80f400b40d01a00101180b50700c00d0141d17804020364070a0004855241d40180e603100750529500750781c16422803280b1486c90131000746961030303413000c01d0240e040180c0065030601100d240a0742e981c4003402141010180c081d1822a42c8140000c0d580c1c491031041e0440da144108200c0008940ea0b219680c140c000c800181a644444072070010800904040c90081d170800441160050f0354605504d039940080703185000f081d031110010a455104000850700039140807403240d6940d0035070b120b5041d0010f0302c003800e10802c4148009800103880f491a885c0f00e803640ca00c00c08546080c20318045096680003010300c0e040004141107064240d41c001540056800a00803641d6604512804280260240e03040035209200c0e030b60200760201e60008801d000c440c02c120a540201c50303c03107003c0c02144828880e61104180318040030003030100d090b2050303800030200003c4403c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 661564541 1250 661563291 661563307
    0xc02040c0513080307060f0506010e130617100c020703020303070305030c070812072312060d020a030515070c08180406150201020a090f030f14010902041e0c1d15 71
    0x11000b026504040f6240d0008551002005041d000300b01c6182c18001003442945042800204400308000c0c00d144a484002c24180e11070b501ca90240c0c000d888540d60080b51007200d840c0e20b5595007027404031140454504901814445d00c080384c440c0580f5401005140b51010b01d40302240c1640003d0900c1d201c2d40c1042250100080d0080018030289403074000d00d03d15407414502c041c18148188603c40c0c00038803a4ad880c00c042d0724548040303541003000c80c80c65440d00e03110003020844040c00d260b8000d401007842c0401105020300000e80748480e0222910a6185d41c0d0b0300c071001c442c20030856000414100301401510a101032001c1c032000f4038940644000f80c999518543c008900080c080100c0150358000780101810303912420b04006030110082ca989910b1465884000c80c008611000e0244601401c8114070920203400c44012540c0051090107207605c1060051003952205000785a0145001d4040299501601c90325400b5083c0d04501c010024149092001b80d40344105500d900b044e08108503d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 661565791 1250 661564541 661564567
    0x10608030403060603060e0f1015120b01081c0801090507261605090a0306020306120a0305090f030c090f06060c0106121b12060b120d030e0c100c02040c05 68
    0x3004502030f10002c2011482d50806404684803010f10304a645c1041102c4020302d0000136010a440c8400400000c441c041000d1580d604022a04070700048a080c5e10081c042c0540d0203038441c180c41c48001542e0700341d00b00c000103040d00354003000e100011a0a020040000500903408254030100c0d07814040144199141c120702d03130700603209888e41d1815446040c07051800d0350140d4900380f030b02c81d4100249080c05800014613242894400180300a80000004c0c045454400641c140c9003019411100c00d46090b24025007950040294140202021840080b407440c00140c18581d810300030b00074184603100e0a0f4a910085c0e00200340c1f50301701d0400c00c10040310100c248182c034002d14030f010103072044544516101075440180149481141e40481c004e1104440a034002108154401800520020140c3c0890141c10441c400741170300b401296400309026030580c001500c8030b00c1e81410f40e110b880384081081f17186101c9840e08000103241408a2005081c41d600800d8500c90b58208203050900c158905 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 661567041 1250 661565791 661565797
    0xa031416122003090a290f0a02010c030911040923150604021905180901030807060b03030313110a050405011205010f11070224130e010b0711011101060803 68
    0x14800a00ba82644640006100a808100325141d03409545081250340000350504000c0c0100044e025004840d04690b90351100410300392404548130a0310b40ca8154150005a04000315180155007400403c00219209200d0004c00550108006140f10090f0713050100070030302e44400701d4030301568040c405024011031a00754645080c400007011921184104040a188003034012801980180013070702024400048421040b4074030f1400075200da4120440100500180142c01e810048840011061000000040814901a00d17040c0079045c0c07030f02c0a0680d60b120854404400c460034400d5000000c0c00e100641c50258401411490910f880388000b81c200c900a074450200c0e05540c4110344108502800780894807641c41000308542d400d80c3d43c0c1001107200c1c04500a101361400341c0300c08820340c10701030a17403d40d05582c0b0110f900c0700c206901071155045c65008240c0b519202100000708107035910110b900142e402400b2402603203c1000544042c100a00b00580359502c50300e022402d89010070207 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 661568291 1250 661567041 661567073
    0x1c17092a130608100e010e070e070918050604150b0906090604090509010509060a0b0a0e060612010806070e030604023001050403020a021e0f1005120a020a110a031416 73
    0xc3c1c132160940d50300882c02c07600344074184880d69042c2000c09200f060081042c0003210648156094a42d5417500304813244429600300f010964440003a0004100e5194406c0744514003c3d94200180320101449503807685140c41a41c5100500700840b0354142020000b600f148807025002d40c1c141525081584166002150661f8160b9562810091001c900300b00c00380e000074178a4030400513800d21b04081248034866000300600c1102181c0821101d844840483c0c11102c020b0740041140d5850350422900e41c9829140c0d4800503120308941a111726021810600541d4000c010610b002c021158100d900300105107028076080040710302c0c2c2c805181c01e01940348268442e601403c1558118410060712403612161458085480307050341c030b03054a43d80e0740c81c840607800300d40f001902006a80c04171894810509403941024601c3c0a0141110554000e851002400d4541912003e6007042480da2500c03540d40280001d00c1c0f0170624100c0c0c240083c002c0444403807409602542425588424159407500c41c3d03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 661569541 1250 661568291 661568293
    0xd030c020a02120c0f011b02061c020703200f07090e1f141e0402090408090a061101060b0c070b0a0909050f0f0610021e1c17092a130608 60
    0xd0301145141c00c00700a807000d074090030f0a220101c03840e900126150083d500090044030300042030880ac80301e56242440704554407009641c0d0392210b1600500841e0308442c3c6007413005004110218180000c1001920400c40f0300003441410300d01003041025010608011480b4010b80b04040c50751031015420285007196a940440c800015807100307004c0000092110340311a14006201442d008035000e255040703501250408030790b844a05100c945481004071040e40502050300000c0e285410120082d010741c03501c802006420b81e40c0100f04824400c42001d41d00c1030704803480031b00101501102814014440d4640b002c80d0986801d00d080407298251041041c64102000700103040500300a141c1c0e00036401d442f501080381703031040041d5036000440703141d101c20b0700061400581000c04102e815100400580680c4829900000180c40408007000702610442d081d0b00107a41c0d03510003e0040072540c441e1200b03509100c000403800206680c580c8a056214004008017131407150640210405004c0100c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 661570791 1250 661569541 661569553
    0x1b060b0a051816020703021012111b0c040e070b07080c1203010323030405010320041502060a0504030503070f11011104140901050603130f1202010c110f0d030c020a0212 74
    0x10001054070f00080c4880b03400c540c070000c810300060302e8003481c8254000843c02c00b04680014081d0a40281400c9140d90001c0f810205000c4c114004c1015181d038119040f0059550f452400c400f8001960680d9100d0002c6901c1810100200011000203100f100d0103640410704000c080200c1034140301460021002c5c0346008401030003402442c01c000d0100d4690441e045194100a104035901da0044e8404e07507041c90b03580e80704d440ca03607040340303003a41482040d070761646550355224100842c8012058103a50700601c070b000d00080407403086204160040c0c1d0180c440a0441da40d40c0c404580d840000000351040012800c80901c2c903140074007504e1056840003500c180c07140d0400b01050071808180c011304c2d11a54100e001002640c40c1c0c3c0c8102c03030300b0000460803080d50340c41505010701155070541004001001c080029030202d941944001c0500c443d070380c0c402c0200710b10f01042d00c1d59900e81210300c00c132a8002c60050420240030364040400c14800d401a1001710120350000341d90440c104a400c040b64010b0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 661572041 1250 661570791 661570801
    0x501050f01030209060301090b0117160305010917040f050405041e1112030a08150a0f030606091803320c0102070b070801060f0305090c130e06071b060b0a0518 70
    0x41d1541c50f45c030050590081042d40920746804118441c1803050009800c034030103e603900344400b880650001c01c102ea0303203061100d90f02d1400d180280200345042d182110000340c08001d02d080c3e401110211500309082c01640f07414002000014480500f0403103ca0101068050f07c0c0b6000d072038040901805001c118000381c0781001030009900c0c160032a0506900204801e1111740e4018950581100303081210b60361030394812000c64200a000d030000e04159031003042c0081000b01c590440c03400d0f03500b11102030103d0300c409200d5039903000c009003000f0b000c0350075500340140320700c0d00d6070008a21401c04201c20520016000c0002d032154800036002c22145d40014444003889801e4111982024061401500641c03420300b0040012a801c0899010940c841c1c0100e01d14120400c015000c0b00c200800b0220611340c202e00110007401010303d58046030161000041c039190107210070400f4250000061440d8980c00c0d56064010100107901992143c5070401c007150b00e444014602d0501142c2c81f0f81c007120780c105 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 661573291 1250 661572041 661572049
    0x8031209030901091e09020f18030304030b010306050405010b06040b0901090519060c0c080601090c0806041401271407090e07021506011b05030a14070c1a070501050f010302 76
    0x10003006000c4560080100b01c07926680b050350182225065491585100da4545140d607038584660310a03071003d4000300b140c541c0130714038100400c48200782010501e0b154005805054690240d444040c000c03031010380c01080450a01e410684d80180700d2030001802d01c80f903d00080480d000754002c081a01000b28680c1d500c0d58001c52114054007013100c2c114001c82002098070150105070240f00104080c081c0d20170100300d00900750001804601050351155a10f492400d0010600a5500000900b5020204415042c1845800c204010050806489a00304000e14001140b01440700020386490305a5868200a5110f12032889600100203c00f60415100061044445400110024030803009100308582c0004180d549041140340c3d64000343d440e0001030703600c680500c01c60351814415640c400c003004030200041612071455202c00e50038408200c04180c2034010301100070290384200d041804158001d075000520f42504040c904d14221440e6105400d40307406481c04481452860018021490 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 661574541 1250 661573291 661573327
    0x130615050f0613140604030501140a0606030b010903030e0d080304200907051204020a15080405070611070b0c0307081c0f0218121e030306190e0a0f090c0803 69
    0x407044840b14103080b20303804040700ca0700300303072151100e6050000d4459542e40c0b51813090310001d6410400070080c002d046014502051021124402118505207001c03c620b402032044211460040c0e44440c002421940c0a41c0c03200444440194020078404102c1d0000710944000c510a0784250b815000100c10494464954219480c1c41c611483d0200100f0a00d190700ca0103507410740a501100102e180c4440c004181366500791340186000c03008102e00c3c11011138001484c0c600440c031400c201d48149550740c0c0b00310f901c080104c900d5611500032070010068440c0e0b00c0007415a29580d142600d03e0244a0b0761201a1503208800c10205204c440d0505541c8540a1085c5c1600d8484440d01f50310b400513100140416140307421416208128219000303200540c1004a003184280700f01c200244140c2d4001c0d1960f172500708480c000c0c800e018620317044060721502d242440407180da01100c032076103031201103450003d0210b40c0902c51a6650f00e03504c1401061202112400411001c0060350341c0c2c218440c01030120380 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 661575791 1250 661574541 661574569
    0xc0309021503071418040204060c11030105010f030201051c02040f060201060506030f160c0605090304090b030a081e0f0409050a0b01090b090103020c010e01060806010e07022413061505 81
    0x400184200000c07607401c41c408041110050390b901317554208441e403002800c2034186000307400910110b800301b011500f00d140400c02034000e4540c1c0a07080c010b40c0030503007a40c0d001d00850715000c56440003000154000d1000d044144001007240c59000c0301021039500300d03001544039800c0c10a003858204050380c2c082c41010064041590000d2440c642005006074171403019058a840c403140342c800d030200743d01c54440c15200031380c0018140500c0c145410081d0742e035001390081089051800090041c1480d00040c8402d4a0b41e0162245040964500111340100160849030313400440c02c004910380744011400500191590180000340c500f480c4460748100c400c04403d940c1030015040050050303140100c05d4400900c0b00b480c01580c0c80114011050141c494004514001d40c01c084002c00d0002010800606a0b410004500e21a07622507900f00e948d000c0c0195031200c40f0b4243d85048842c0344104000b140c3c040342c42850205042100d58030002190002480c00d024841a100140032510306980c41c00c50315 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 661577041 1250 661575791 661575829
    0x3010e070e011d010303050c0c1518030601081506010c0f061a03030306030a080a030f05040c080c03030f041509051f08090c011704020a0e010b0a0f2a0507090c030902 73
    0x4101d00f541000e8042c010f000140900802007414050f0580410400701c1d4404017503e024440c8003826040e50050f048005594545022018510101c1c20002401e50403100b840e0024541200030140900d0005000b9043c14100503095181c10085980051064a01d6200305400583d402150350202c00001a8203070483c070030b0f08104207000e41e60794000350a003115038012071480c1c0d4450300040160018000d14480c9801c050602d4204000e0040d4001c00000302c420402c20b890244590400f0586c40784516012040d1410041c00705100e50110b60143c006695924140300754401c1e1540c1c00285c141d01b4080502e21141c1d2500107800c5c100d60300c44141030700926107500819204090a002034501001518030160082e030001c00a0295034407264800300510800640c0c01c03c0756101c89aa20071a03100d0356124000c65464003a00b10341c90301c240104100b0b400608106503002980101404000c005070f1410385c0c0500c540900440c910f80e50f48180e421000940c3c40c0025803003001c2c418081e401c6900684540c00b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 661578291 1250 661577041 661577069
    0x804120e01022104090e0705031204050604030b130605090102030907140a0b03060301110c030c01062918030f010c12020f0f070312050103030903031803080904090206070203010e070e01 81
    0x150740c0000d40c14003007140f42c903800ba00c4400480b041410900403039020b07600d16400e110b81ca900c250b0f0b01103419015160264184d640181881000b60700d244540c0c40f603240c020b5400c02c01080460300c06021580c100c14440c807a98120109900c030581a100241c6210040f42d5001003030206140b010004100240104101108960314a00000301021480d03c035030f13080008000000f50440e6400c1d400311a107c0c00d400342d101c1c1c0fa1307071001988503541d4019512154a0b586021008100c4400c4181181e81e1454150404040043c481d0320010864200c0407641c1c2c5103076401030620b0b0503540d0602c11030320098403990001400d190550002016041303000c0308400a68810050036039548030441c1104d070001d104090040d0f862301d90b8a401c4505413030080c10789440c149440d00100800d580161000700716402a5103046504040b881510b0380d6410a200040000701d0401c0b042c81542803d400200406000610190400d0619000701c0d00707407000e9580c043d8068000040c00d101d041d107010005405407111400d0009 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 661579541 1250 661578291 661578317
    0x3060f090607140a03230a3303030e0d060906230f010e1003050a200118030303110d18060c2c0a1d0610020f120d09050d080412 56
    0x200c4e10805506a00b0140c4034200c40242e040c50850f400b41180300c080411600b45002d03004030008000c404040c101808400300e0405540080c80700c6150b4402140c01044030b6140b55030313001c1d100c24207480340e51b80d0400c0324490080c001c200940b0a01c00c40f01e0280b0b502081c820b0b441c403074010401440019541c16000b03004e050083e0406c100319030a046d10b540050310966030320741c0740380000d001e40158030090440c481c400c075000c1007040e1007112040c0d0111082004200f81c045200550301a030144102c0c20010340c0c0440108003091180d08040c4242544183c254508070810600700152030504036110782d00f00041d44100c00300030b07441c402d04280c62541d18011740c03098410340303200c0091542000380780c003c3d05007500c8510140c0e44440c0d50704001d0a02680000e00009220070000317444500300d80c4288240c0004c040701700d041e0b0000c80c04695642c01d8502500c5030852803d50940340b600010118a00144e0350151980091400c001e000c40035070454940d61107501d440d15008030007030300c54a50700082260030b441a407 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 661580791 1250 661579541 661579577
    0x1021801181a090307030803040c0303170702060a150b0406030603050c040b0306070804022b0b0906010b090111030d0e03120901060f0b0703030e061f0e06010f11030903060f090607 79
    0x2000440c00c11070072030750343d5520800285030481d5a00080c0c8490300000501041080701c4888400b2a4446e80703034081c043e20044121400103104581d250050b070090030025518000e80d41c0320703140c2203c0a10700c884645031201440e440e2900300e40c215201103076568101b401404802c0000c1410400116014401200090046911844080d01c01400e0040040c00325085584400503070342642d00d80e031148001c00f0040c0d0380303102c808240030805035a9000b4803004a00000c40100303c0300d05940c04141040e207854194001141c254924800291240c0401d10031440c900403075001d400400845a002151207070949201c40f6601c480281044086a14004082004241401d8106c0c229445482c1c06a00c60303445003070903409052100021082c40c002c0c8401c0000c0e41080c19200380380c6911071040d440c00942c1311400b00118200c15100e0502045646c01c42c256040d02c221499030101d060801a079044c5004e0b00c0119151090554a226543c001c64040100d034800400078940d00c5046458240310322081100d4178 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 661582041 1250 661580791 661580819
    0xe162904080c1002030d020f071406060109140109030210020616030b0315190e0f0115080c10020f070e0414011e0b0604030f08090f10080619080102180118 68
    0x82409803c405445126850092080d2001e01c0c4100c04103540c2d510701d80c442d00c081e560128008444240703040756a4500c14000150b9548a610181c54183e607881c24916040f9420502984107810010011404001070315210030700794101c203081d0020609820104c9603500d40a201400301070806150180603103403a980002c3c1d01c09002c8104454150949803050412405c4035040d208030f58003410f0103581c190352a000600300244106c40e01c004c0112b08810500640347d11124403a45103564000c3c1d0300c90036a850708030210400004a401140c981c9039810f1089030070500194046d540c0f1440c1d180c200000c1c044a10311704800040c81000030410303801040260215803140c92003200304503684944140300e9848040c1298084d540202c6a40d050b0280d618014206a000d803090174041c9101861600071814405888603031010035031a04d40c980c0d600d003c01d02030303141040640b007100d1141d9210b0008a4600070320080203071000c0040d00d04604010840003400a0340010050350710940041c03c20070144c0012842 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 661583291 1250 661582041 661582063
    0x90a05060a051b07030e04051014040507020f070e010510090e0f0603010e030c160e04030c030804081e12010819080f04030b10080c030601060f030e16290408 69
    0x290a842c3e580101c01c003840c90300c5654401c00c10000b030740c409145e04921003821086048400707001d0795882c80700380ca10143d1a4442c80f40381c2c803410221224240303010b40040b50700c0310703c900c101c0300d038040960056440e1220070b80c4100011244900140242c2c100b45447c02046401030402d08261854019103403d14040100383c5400d261050b804162141e03800e42180c080d801c0d01c80d007282c0d114000ca41ca80d940b6840d5112000e00000409513001803640044003001d4400d030703059280ca10601140741c0303040c1c520740d00040c0101c44905007044112102c040302c1c0222120301c211864006e8441000004180d010201a0013a6825030302424822218904007800d04071520b03800f01d08152106018007908a50340500e03003000741043c400e6010800f0140100e8100c100f2144100110b1f80308088010925446060a01401001451409920703102c640640c000101b8030407001d00316a907014140340318007484145500684014100c9000b0060940b080203084c00d800c04043d0030042c0b038246001040f940c1c0322220b1740 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 661584541 1250 661583291 661583311
    0xf04062601090b060409030e04060f0504050105040e2e06091d1b0f0d05191b0326090301050403020309010f1b0209100b0c0a1709130b0a030203030c010c08090a0506 72
    0x10b079501305031080001c6070788c80030007420901103143c85482e1100000a41d00030a4003651a040c0009814502802103030003a038030f070350023400f5450700c4034001e5403c080030141c02403900084080c9041d0400402d00c40c900051554160018181e10305580604d00c00300083c0700e02c09030b80e100c0c0129240d00d0070b10401542400d4003c0780c10741441041480451245102084c01900f14041e64a4081140000c0380c0606041803058170703001000e000b00103e00309104d9440c0400741c90f02111003617510508401c43c00c10341140d200c0b03421650034200708400107801d5950885040700182c101052060f1a075030081d560b00220f00f118200402c45903a4841c0d0f07030f0742c11160040040c1c424610400800c841480d0201c0b0800500742d0000d0341d5030303078002c2003010703035642d00840804803074199903068000c48000c0c410054500105000309045007210040d001003018040b106540d96005001e04000001a6010001000000361200012401281520024202c154010400055904681010b00003d030001c52680e9104c400c1e04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 661585791 1250 661584541 661584551
    0xc390d05070501050c0111130f061404060f1e02070f0515090f0111250b09031c2c090f091203040606030c0e040606080706120203060f04062601090b0604 67
    0x5641409041c61011f104102e203000550402400d00041409056854100071003040b580c0e84c0c2e400b21500347c2c0180c0a02c1800100384028400c842c49403000e040c02d00030516061825010040d86410315206101c40803025a02c281020004055840343c030070003c1004a0718101c8040418408044034425100c03e18442d0f80c1c00c40307403001540e00504800800007820401c41d00b1640080d8400b0102482003c106154010140f00024003c000c000484901e080060041d0484c405e48941d11031100000c0c0c06c2100501400341c183c101045001032041410b20070030740c8020895030103038050100041002c0e1016a048000f20100181c2c0781002030443ca034245403950707590707072581c807424440001e00d410f400061165980c10800503844203043ea005029500600c0100001642c1d5014144e0b1882a0711032400031410315145d0300348030750960b4003943c0e001034083c00907d021054540082d003114207503084440d2103003921001c1200c044a02c15007407641103902e0000c102222f21512003100341030000340400d12031503c803 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 661587041 1250 661585791 661585807
    0x30312040f0c060809100203151210050a02040609080c010e1201110a08040b07020d0219051e010e060f040c1a09030a06050702150415020c390d0507050105 68
    0x40c808218010380c02810702e420464444074010041401591401032502c00c480400c88217011b94400c030f030700591841d02907401d110502820301c11800300550b24100c19000d0380004500d21011400b4440c8149a03003180107a03200d06004010700300303501c950444c2020381c0c82600000319590300441081c109040456a0401050003580000c0c00360800c49030102c6c1c52100032403401d0049070400f80040c040c03032041241595540d19540203d0386d820042c050200144e00080500403081000c403050203106004000340c451203820400e000d200007446440480060399580c01f00d03105d0040074440180c022840005149450906448480c1e4115580c000c04500c5100315180440181001c4200c413090f000180680b03008a8803800d0440051100710341d01c07030260040e00c565030100c01da42003a0b80e20940d44407401c2d036811986605002c0003500002402a40c41c03042040b42080fa00c00000c030614071010500c1d142031004060a105807020042442c0309000f6401904d03c0c0000541c08600002611000e1808030303110f80350 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 661588291 1250 661587041 661587053
    0xc0e040804090e030d060e041a0703020403020d0b07030e03040810020d0e0105150f0a0303080c0702040b1206070207380d0e03040305010606140d050402030a06022d0903031204 77
    0x2154000c0d51500e15103443c03420f603c00040060325441d0f8080d0003c02015580c0d18641d140c00c04103c4000300f041f500c1001000d4045010091650044181c0c9401420551030b5400b00b144200342030400c0d240c1d110000100014540c0c140907c00c020000711019505107494401001ea5814461710804122900800d00c1b40c100ea009a11108610900f80000d00003410404603030300b110003030b000310180100c8541d040410f0504148002200300d0350b056035038040940e5084c14040c00d503000041c04980c0151200c08038191565100032140f01180410301828250801d5900a45402c1003a4002e0900350b180300349200c0c135080b9070901801d41100b01c0e0100500080050b00212240c81400c01c000c080034506078056000c0c0c20000080d10649115500802050b51522002e40d10207840d03010104030714030708000764410340507103411841e0024409000c442410b80207a5500b0143c1e088a802103c0030754001c0d590054104200c203200ca00340000300090303881c01c500200484d40702d204426070f05103014070b120041802c1204d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 661589541 1250 661588291 661588297
    0x8060c03280903030c0e030a06090c03080406080f0907060c14010f020c0102040503160f03080706090b04081801090602071403100608010203011e15121811120a0c0e0408 74
    0x20819401c91488149040d00800740070009070300091408030030360001c500913800e800030604014000c00312600265140e40c0589100c2c3d40c1160b100705481c40c004001401b850207000a03022540310105945050007094500d02c60061801510764040c03082000121f4009000c00e590719008440c40c1001110902e500f0b014200fa400354a9a80b440001d44183c9490192701610560360220152460310241090b80d0180210758000c860104014001c00c10000d52103a0080c0501c5110700000300b004070060720354108420007160700b81c4403e6000035401c10720403071640c01c00e0b0700d40c41c0c00d080002a40f418404d000b5030f56a43d5010b4405289039041e5003868555040121000001d02e4a2090180c6030b02c0e1714809010350800e00c6095844402200207a450080d07503003091003030b5003000c0c05000c06010060421034034030000e001a41030a82c3ea413440c682111032401204440d85001c0c1c5010050801d5907414000b0003100c81110b10301c10340106c60f421002a00074031509085695200125801d51101d042c030680a03c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 661590791 1250 661589541 661589581
    0x31707021e06090a0609051305190b15030403030609050901020c0a0b2802211e070e06070f0506090c01080103060e03130602010c021603030512040809030a0804091508060c03 76
    0x10708240400540b0546c02000f03242074031400e840c5140c0b8203444461000544600f81e4200c00389600b00410000c91452903480304800f10802400c0114800307186800c60600e80c4150b5040d00040c0d160308083c40003e00501071240c018060030002c5191104444401c6e48462020000401c4c40c005807010504c40901100d1112a50800c0c040c80400e9080005041d0020341c4801c147e10317580d00c40d00c9243d1566442d030f898000d00c80e03400c4641341d124a00c000b016224040e40014503402c20722484e40002102602d4400c0500240c1d442600480c0c00b00b1b0403818024544040104000c2c1161701c0711f000820540d80c802c54682c1101d51240340801e40035802c850f15821400b9152589902d101020300c0000c1003071b13054104040980701038090300c80d0802c0c135181e01031906105010150208104001d96003210000ba9080740e0321a009060560400b0000c40003e4203123020000199002d0002060a0010134041e2042540704982c00303910102c903d2811101c1a11914000c1018040c84000300014500e0010000062110 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 661592041 1250 661590791 661590799
    0x20d1103070e0f01090b03030d0f0612060917091804060207020d0b1501050a0c08090301110d2004080a020d031e09150807080a0e03090d030306031707021e0609 70
    0xd8586030407401e5110221060080f01040b9000050926624820000710600c05400345140c90030109407000900151000203520070303a60200080c14036400c807e0184120b2181002090f01105070400c41011021f101420810803010440344002e03545110100b22510902d04007604182d40d5828480c000f80500d51000e50460b41c440d806408000390359594038481d41140d032503003030403c13070b410011107003400703420905808281c1620885000c05ca541001d0080c00b00000c001082e043d1080c000c50130581c100440342c0b49069141c00f0000320321f03445000c0800387c0480001c15503041038549141c482d552062000042d0113000b03004072600500d03200e0b032043e840b00c4c003001042d020540c0c4804002400e10340389224600403c0c421412000c00d20748a44895405807005540d11842500c483c0002401011a6a13000055102c01c0102e001c4030f8680b00c0c1e04110f00c0d0f004e5280002c055242d402c0404001d00642c504041c01c80c020804500140c1e60307050384056108200e030501081c0c2c02d003480840d00b40d200f0101e0040d44 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 661593291 1250 661592041 661592053
    0x10515060a120f02040308030609010f0305100504260c0f0a050a06021c0213150f120b060c0f030a0e030f1b0111010509062205072d14011707020604020d1103 69
    0x144000e100003580030b2710055840d114103a99441c0181e60140c401d001c010301c0b580145a03a9040d400c280d80015403c036010314090100c031404c84140380c00030030040e0024100003401003400325410340240f01356000035a0020107001401400d6a031551a2140300c00020b0032258045400410940301100b100d0718000c0490045654070854000d442801009110307041c2020080c80003c03d080740303e110043c601e110540c8845002203084035000000e0f0502c2458140c00060034031001486090400a49601d45c0d51240515a10040c507a0000c11032414500c14a0090b4807034a2100e00d0711000050101050090801d59004451b0b844012500e0485010324008558240030500400300c03804a241030140484008010244000d202e50b99030704500e684000d056500040c4c820000c0c0c40e001041d400350104550003c1070600e221014001076528503400074601c000f5203840e064006d50700088003455210441514030b88600d0100402942c980004000a01550722600c911003000510040b502d51101d0081c1643d01d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 661594541 1250 661593291 661593293
    0xb041106160b0109090f170910030605090c0c070605090a051e03010f112a0102190f08010f060c1b0b0a18080d0f0c02030109030c05010515060a120f020403 68
    0x403034558014251100c1d10303800000541107500e4450798940b01d40c0060000c180e1800c1f501c50207140303442c950000c0740080040145252690750342ca26181040320399100021440e0500d014001c10320b200605c01000b01f0410000c4100040000502034110ba001c0e2500342c0e6078207980800f290380c41c4d05551041e6085230724002440030a510b0355050301808c440550080082141064190054a0300c08100042001c8100a4421a0340c80342505000210011505030401031140800500320392111340c4e01d601650000f420982e850fa8000c2040000300320078507085a00703506044450402c0b000a1040c04240108035126100304a150244801a40c1844001080150380ca0014441c0d44d48130703108030300004003107200d11300c51300b036403101380708140d03901c400060401e4004100e05882120301511010309120300b03504c282c1c0050387d0034024502242e21a030b0350181404402d1420a003950300142c180243d61100e00144000c1391a407005483d08510310f8507008482c1c06070303400380388020041e01c81250409800010040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 661595791 1250 661594541 661594567
    0x9070e150309010c02011a1c08040305012901020606210106230102030c0309011412071211031b0a1701091d1209040f02040e0a090507051206040b041106 67
    0x241c42035003940000d000c144d40042089013220b024203100146880354042c0d001060030100e031040c4201140c0000002280c0141e01d4445c95034001c0d60084a8a80d140c0390003039030303003c1c7c41a4088850440d0900989a0520a00010b512014000c140902401500c4080f400380091f549000d0309000c3d000c00204042925240320003498040d40440300f50407540d520f0881401c0d4800400c803025821104091400c0039079100045412105101103001e55010038404030401d0f080045055004240381d17201c084050420030044001c0d00c9419803158800c400c103004200e9020743d02113910308000c40031100c066540320040030680311000c103e103036a4002c2c1c045000114050840780d1040700c412406c04070007540520314040c490307600c00c038114062070300130320912444800c2e0401b80c20034007404940d98809402d29440e0400d407905904100c500549150729000200103004003400460081c0074182c0b007940c0c03c80310603c0840d54803440640010080240840007805128501c0280034035004024000c540c1c8180c0440740c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 661597041 1250 661595791 661595797
    0x302060a12020705160f03020d12140d020d0b0405190905250e061f0309020406050d0b04030e030c010f050d060801051806070f08010302010c05070803030a0608120405060909070e15 79
    0x2c84041100040c01b04200d40004511421241c1c0101801808001b585d03400000402c482c122030203200483c00441003c0e00e920f4040d0802002800340161203044a4640c141582c81007904c00340100d1500d014000491100105107650001008020544d1600c0780360161038140d80341819240420324603160140c02501d515014110740640d04443c4072a11420300304003008510528200c101c03100190344000c1607000c0d4006292150008000098080c1d40700c0c04200c40e1410914212180310a48041004140d040b410b40720140009030000c0c4910540080080d015004540030b0740103008021805407411141d50700b08034041c041040013807080f070500c0c180920010340d601890801900603040099440c40c4280c8603005040750380c0e178803440795900c0c51700196098424072a00340e50783c0c081c1c410041184882000258080d1345200c1000030681d240820f82411300d621030800586542c01000100281d45d1403200b5a0450340341100c42890b217896904c030aa03002c0c2c080c00c0d45645c0060302a40e12100c010020409 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 661598291 1250 661597041 661597063
    0xa122009090a1a27120a03050601030c0207030b151306030614070e0102061b071b090b010219032006040813090504052d011d190c0302060a12020705 65
    0x2010078448400340722142081c03086a00b4501d40c04600b0020350113103000483d40c0d841212080c10f0f18501940d40300010402c2e0b101d02d1040c4040398071501440b12a590600c00d0501c85050391010300549400c5d642c50340608100a44206103080100c5103001e4666140a05680880b40d40c07142001455603c0c54454060580d00546000c1e15008400282401d170244802000400059002d8140780c0e40d90b5803042c80c0100060200619400c060202030000750f04810a03484801a54a5a0700c2c56032030010908280d0741882034150440d0404015403030040c4440c014070210a82c1030070f040c40c0d2000100b500d080d28004814000803a885071505010602080c1c0004010020700409109001600c504445080c0c0e44103840c000e04940c0204444029440e99001030803000c11a61604440d4400800910382551411410384800d582045550785480310100a25001c060f0706a0003206030010a455900842f1030501c0040e0088100040600380c00748159200303414082008000c54980d9458145280da460b19060 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 661599541 1250 661598291 661598303
    0x3070e040f050f061f0c11060c1f0c0806100e03120a03111804050709120c05030d081b0f0d0501060e0f0909030a05070203070b04030b0403030b0a122009090a 69
    0x2ca1000c2c2070240c0058450140202085c8084194000856000c2c65000b070a880328181d089060845030b031800700600881072034400604401c40c10401c00c00c0c0110103200410740321450449010000d941200d052540702c041121040810124804141d035544400d10040341d25004603682d032003203000198060110703118140e50801090b54a41c4201c2c500c0d2140c1018144200600040700a035460a07801c4140c0c42842440c161482a40d102602e0640200c4044212002684a90184281e0608110011045450b89031101c461b040a0f24104140e00381240d200004140002d85154540340903400c031801484500000c2040f581c0d2124028662611943c445200742c21010140b0720901d8030701000d40c01150712101452603c202031006442551140801702d8160207500000900440134078042d10096001e80f455180500d0705140c02012600700c1d034000c9100d03448118050103401c5884809400d001d5120301e04802c20340b01030442c05500c0c0082030015a000c0103210802440d0320020400a459602c202 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 661600791 1250 661599541 661599571
    0x40e0105010207030f060902130f0c08060603132a090c030e01140c16210f0309030807031e1d12041a0906071502030f0f06130203070e040f05 62
    0xc0c01240c48001038880a041804507400c0342000c90b000f0f600c101d04c02480107000840200c1000740c000c1c26500002e203061030861b919451071108503004243c0c6980004201c441a2851034140003003512101c5600d001352404081040c0200c074501c0c2c045003c14210804065641e07059038903003104004e0701008285a0000341440151016207405000e400e580020000c10040241d58441032501a5000400c498060005040c45500811b80a180c1e221003085829820001b240804002400089884542d0000c041c43c10041c503004c00d6121000e150032007001d00d00400c2c80c2a103490a0015003000c4030032020704600c1c0c14910b00008500c16680601e562914040e0342c00c1403c6210160058000d91042905030749001c0071820b1041e030341000500d01c6400042c41c0300c5c1007126980358101002c080c01c803080318060f800030600c00c15420580b11180d00561103a101081803508802007084a8002d01180541e0394000c00801c403828050000e10300307404000382c003c00441501540c440094403007910107485d103803410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 661602041 1250 661600791 661600799
    0xe0f0a0f1104090302060a0b060714030a08010e0910092108100807050901031b0317070204110f120a0615200303040201090e04020f060f0c01110c0703060509150705040e01 75
    0x600840f240d05401d600548500c0d03517a10a0000504006014140d0081c402c00045000900e1542c5c0d540c4c0040c103c000071511030820032409000a007040e04101c0c5a031444a04224480100040411070481600d9020500d9a03840ca000700190071400d02a0080b0f1405c800302e055810b90000d0b006108646203070000c86030558851259841c0d441501480b504081a0380042c4082400341004491a00c0e0111180f0400c954a888095040744e014a290350b40c01c400141e41015850103000b004e1740c4c01c94011159141a0021116008920560010740ea036812048000303010700b10140e2200c80180a8403071725042d51001c50000400c01004032181c8100780c1002007841802c2500041501d1180345d06840d9000d00b60304200d1070654400000f0002c0703030722402080a0362126114030000d86900c08158200e640c031810508411030075185402644641d02e60309200105004400051038001c03240c2002c0000342c1a12a0104241844405c0690b00d280303c000100740a0b850f50b0040041085694146403107103283d0721 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 661603291 1250 661602041 661602049
    0x509010806040e070e0c0708040e100b0f12280b01080a09050a030c1b0b0c0d020d0e040f11130f060207030819020309190513021c0e0f0a0f11 62
    0x3d9a60081c00940c08200280400181c3c4045a80c210004e0410300c2c1c20006256241480c580c031a0700611400e03040c0405210b1851050ba009001502000d114507040080742c6a07043c43c070340104151020711003401400700d60084240410f40d0300241c00e180c1c040d00e004490041000242240c01a0180082d0707003880020520032041c450780400c264411b0203442000e600f030700e0403184842e40031416905600c50240844400d5122a101c0e4020000e1170100d5031103d90036070f0028144840c0341c502d4001d54010f80c0c04404419800300c036a207145d03c4201c90010306506d5603c01c143c01030004a11402c0001c0002404c000445000c40b04001155520220109000e0300c851040742c0700c11891000402010007400040421140b9422000c1c10520301c0c412a414400702d10700040c51a50718415000f00100c0c005014802403d00d1060360032140c0000f10254508140c81141e40d5920350011601141c0c21356403020020061028401d008061021a04440d400c803140c0c1030240e00c15414200480700d403a600500843d290030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 661604541 1250 661603291 661603301
    0xf0301060f0303050c0f010603030c020a170a080d090b0c04091118041805160303020d1107050405040203150a020c011808220b0d0510061b06022206050901080604 71
    0x81c88201d00001c0a242d0381c2c05036200c3e00b00d0b02c0405418040d24107001542002486000015406039880e00f802000300d00520504034101d0300107403900e1854048001c0300c002c000403030301c05e005c0d800302c83c482c8d0310f0301444c0c1070500400399440c0081013401d000f420700030009120800307001a50070784032003040050010000c01d022440f50003d64040f414811804242d1841c05510000042d14481caa541c103c0c0b625650701c0b42000c7d80120000b420480e0b5150600034154108080341480680c1e0919404044408425075a141c040b481018030441e11000001c007152401c3c48031001406021300d24501c1400c103500c0b030002a41100c170214299620f06a800070b107240056031a82890f64100c203205141000340c0030998035038110007900159000c00c4010001c2d0700c0f80ca0000800c0109400e030350004007420005481d0000280c00d40c8184208500205540c0300503420212030031207958881401a685c4021010310b01042002c410140c40d452100c207000950160802e0003072412130000d0b41e8044c4141d94420070842124 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 661605791 1250 661604541 661604549
    0xb04081606090e04080c03040e090a03030c080106050714010e0d0210050703330806090f070b0c071509030203011a01030f06080601120602070b0a090b01080d020325050a08090f030106 80
    0x3030f586000b29011810034401040b10314105801d803442c184d110723601d2900d2160252076500c81e640c0050380900078103600d0301c42c1c4030a8a0355031501340d106516241000b40b9502851002920745080c140b07150100e84000d501c00c80030b418052055411480032048040e48800151100c5c0910740d0409001403011b178400c2c0300c0c008602015000030f007a21072800000d02141141c20000d0108840c42604c0841d54800410042d4403449000c8002c15024022160030b9061010320b0f880880c5821007032141420541000c10000c050b1401d541da00ba00b5007400150480c0d070070050b0b0344041c1d059440c2c000340c620146054407030120000c43c02e807018001a0601c1018a084500901c1a000745030050300c0103204005800c03150503e168001d203000b5043c115140c440da1801c0c030054641040303a90703440b0681030801c1425921180102a4000a0b040300b5200c010080c1d105e01c22825665114092112080413001445c03036902c0e00d03541c0020855038403020510b0b0400c01944a00f8501c0c2c492500040e100c401440c0c1409440c05036 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 661607041 1250 661605791 661605809
    0x1509050904080a02150c0c07090b09060105090a0e070503040606240302030709030b09010c030608120403111c05010b0a051c02060a0507120f1409030c0d0c0b0408160609 74
    0x29a181d440b2454180c020355041c10850203849204d215503210380c82518058920b0009251f901c180c0840030601c1c20347d643e40035101290906002c20160b07503558480f070790301c10000c0c00c0840e07035054034500140500309690400f101003407070345c0f090098550340b203005948190b01c20841006819119200d61151000b0321245e102e0708281182c1071102c0e070b40321360060364100c000e60074450303020354403651911f9a41c14100c0e4085080e1303648413100b050185c1e01d030059030000c01100002d8101d07112040381c0341c0c010f1320803400003910007080102800c20540300c079480c807641951190002c160240c01881c04501800d001c903281413042844540205451401600307408a0800c00105980d901c40141d003441400e8104d07040040501400380030190102c2c0e400180350f4241c500565808e6800060f100001c1d001c072075020f0384c3d9102406c1c01c1c040030440351000182c00f100e010b0125199081c000180c900040c09c443d023908600c620801c00b003000181c4c0000098000b402c0d514410501c0b04041c2c44a00840d070b00c6095206100c1d039 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 661608291 1250 661607041 661607059
    0x501050921031b09060f0c1005040c030803100b160605060f030d270314120306060405010809010902062b023a060b040509060d0209071b06090804150905 67
    0x20043c8003010140244611042c1003405581c0018032a401c1880301c805150b1000429000c2001c05115503030682c00310394010042810551031350b9003050440e020082000d00000041404610010f04020082484442540d5a00080d102c24000c13500c884004591190514001c0360030b500d4440c071100325502010303000304110030711620708540c0040580c0c0503081e1201071040c001004603078495400c2c0554043c0c109251440342d40d180c0103207490090b05c00800b100d20148280a41952400300f141c0c110b60007481e0402d4692503910442c0d004100000c0002d50044c40040c2490450024000ca403009000306528031940d000760b9900a01648286541c8008000c4c80451401040782136005020030f02e03a00c002c0c41c0500180c17107a03107401150b0080d00102522100481d0030450f074900060403070383c01030040e100300b4040c005550218140c0e00d00036040c1700500c00100400303004103a2a9000a00701134001c03205002c202084e04002c00c2a502c14082c015034804041a0050b55a000c0c640b2242103a801420100c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 661609541 1250 661608291 661608301
    0x110d020607022805120a0f050301080d050d02120f0709050306060a17070308280c11091315020301060e010206012306070818012604060906140103050105092103 70
    0x30300f8220002c0103042c003241c2c0300e840c0800310700c081120840000c3e035801c03480c1ea5a0b1400d44068035803207807140343d181002402c10050181030720121304180d86804500b0301c20744030000311440c0c401170b000f00c1a085000100000c104080c200d1a24440c41c0529600d441d0300100c540c4810501d916003d08903a0315800c180e480e80300b0450070b105501002d030035403051819207600035100d0741c4202c1703e81c1c859801410420364003602c884200f200c886010602002c90306101c2024462907413408440003403c01d12030302ca00940000942c41500f911540b5040c150b2108154030038241d6075031418001c0d0000c1c09020f000030104217a2003825400080c9041c140e0b030b48a60201e5204408082d8580c45803d018002038011005104280002d0034050250004142c40000c10b83c1e036000b0308000501180b1880208040321613004188120301211804250700250071040120b4424541c0c20124003402d41180f0681030b540c03000000009219065020034082c000480985043c3e81c80c81c880d000c0300800e0042031a00760801040800c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 661610791 1250 661609541 661609573
    0x7090b1602062205030c0d050d0806060d020a05031012080f030603161202090f070e040b12032d12130203010b120d170c030c0a0e0907110d02060702 65
    0x80244020615840c2a8298210000460007420f6100a0030410710382800a443c060090421450094481d40565078450b00e40e076596081a4190300b06104004000c01c1042e01c480f8102c0315824042d880c20356403400c10a90007003603035104560800c0001c1f9a0705002c00d903100c01c5403010b420380d50015506401c080100008614551001c0c141c00d500d4414040c60101040c803001c000c0c0001c02054074a040190a180140f10f0000d00040040340010500c2040261560f004441ea460f00c440a0711f000600c4000c00300854081c80344a40520024071010810ba140b40c0c1d411000400e03030050307041d41e04551400c0540440d006010b8804030803411603200001518014a41104010f0240000d0003c50764020310008501c01751511081d400054000100040382e9075086004c038102165540030071a032078502544032500c2d40c0406051458a24000220307900074600c100d100a4075036030010150b8070542400000074240225001c841981400b82d840075180041c000300d1a40d02c51490b580250074800481c035451 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 661612041 1250 661610791 661610827
    0x102070e07021510031e150e0313090b031c0f0c0213050411031e19150c09170307150519230f0403140f220e07090b 51
    0x400218403030307401a240703220385080a040c081c0003003042c0c039039820b405c505000c0d90901e22201c540d056806c5c00721003c030025000c84504090008a002c0c00100d924020341c0300760440c811040c510000d611511030124000340541c0c00581c4003034084084901001d0007030845010ee000b44000180410648183d12410780c1c00381d041001c14a10080079a02c0d20340d0001da800d011950300f9034064030314040d048210302c0c0500b020010304945600c03051303001e280b0f400c03135180c06655500940c9560780e074443c8000c124804c0042e14207002100c40e0758550306201607a02c0400061000d400b62040d00c2089400d441100048100401180e16890b04550720030010a03210902c000030f840040d100e4004103d44042c5641c03403105030710400f03122089201c40822002c1e8800c8180004a10103810325409440d45414440002d400c03030b029000f500b88180c103680e15158403010756159405014503140020110310840c0358202da031000351710123842106a520565440300c41c0125680e125a005003841c0010400403680510306000035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 661613291 1250 661612041 661612051
    0x3060506130c0e0406170c060a0201150311011403160e1306030b0402040b180103120c0c08061008010204060203070f05101104090f050c0a03020901031d15010e01050102070e 76
    0x14050401c040800d010446509406007400160714440b074101914140c017940006002c0460081a002e906008580d00d80b0f512038a041d1040000090184a1a0003034000c0050044810b80d200383c060342d01e01704807007481d20445403076001580040c840c454400081d0300f0345e03001c0d0b0072040d502e248010941506031001555400b000798065210390703030744807414058014070000d1442400e800c412400c1900c1030205803003c01c2c08080c03183c50980211001e41041240da18116500024800c684400c150025100f00c1c01000c00600000c40904000c00c7c00840003d64a00515081a031101c0c10f0b07607101c6069080380258026130006030010445c01c00031480000e5002d20f0580130303800340d420180e54482e54104944c10700030aa010300d94040340800124a03580b1034101d801d4525a0207029a147c0706001003000d10407d07442d0020305901060b161180e034030030340c0301078040c05e6000c10000d07510301e40e500d0081e510070480c07000102041c0c020340041282507410010034103ca2040c1c0080c0611400e000100c400e803500242 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 661614541 1250 661613291 661613299
    0x4204090c0e0106090824060102160b1b070b220e01030308010e0a0903020705150408010c020c030f06070f0302031938030319050c060406200310150903020301020309010c02010501050a0e0103060506 86
    0x15041c10f080500300141801804403950680da144c429204ccd54282e01d551100900080d044920100440084401103810b1440ca0a020101003900500000c03072090a907001320b40041c1e114400801003507002070700c00741a0f641c803801900c2c1a6550725022829200c45c02c0004006803c4500b04110609000c7d6031840c95003c015880c13410241c075a104182140c41c00c01000d40141c0c010020b41045041c184510b0780800b07140c0e400b40501c1d2401c030070040e00d2106031001620030903500000003101e03580d200d82c054920b00c42c12a004d10040320349100441c80403001b04d008203054401d981d0f06a004004136102031a10300b901401131410998914104a08c200e105082070041c00010014544010000e00c842c0e880340b03110391400030720401200007008110940c1c070302c0a0001c940400910000140c1c9828110407111901410031300144000401c441d0615698002901507001200303000d802ca00c1034000d00d140118980c0208116a611010814800200c1c8070311182c800ca003c3c01030011a02a80100da405100070b4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 661615791 1250 661614541 661614553
    0x912030c110a121e08070818030c0a02150a0c020405061206011502070e0622020c070b0301140a0e040323030f4204090c0e0106090824060102 62
    0x854001c0c105050100100c4070001e8400c401d03482207130404c8002e075440603100742d00d034045594144003400d40036002d440d4509021010000407100020f08100300b00420f400c4082d00e80711022004c1d01a5101400c0718101c1c49104641c81003034030301b1007440944080c4a142d9680810a550769000d110040c400503200303640000c02072524180240c02042002e0003440001c041c440385074072201c1d0007070408020750429248460390a040c0080c580d100d0710021400200082e00c5509000c51601c1e520081c8100900c0811a005503880000d4040c42c10b00078504840c8060460000c01c9800e808001e44180b03e405100d00d481c0e40100414042071180f0b100d007102c51800001d412031600410b44080c150b400031070790241d031071455004100c2185144061400c5044603507480c00702d680103003245d0b00d0f10040d207518003d01040e074040d40c6140030b82d01d5400450a29400c07140300700d406525601d40d002000c809020300c40c007081d10240001080c1c400010704098030003d49101d0002c031200c03004110f4045401400f1117045100341 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 661617041 1250 661615791 661615817
    0xf090f04090f051f0b0a03020603070c0606170c030705060a08090a0b0c0a02150106052d0721140304110f04051801110301031533060e040912030c 64
    0x8015502c0103010b40020000755507541900092403c1c000d00041d507407414403012104584903000d00d00d0039203904071410f40c1c070f03982c800d01e00b242d0384100440060803c070b060000008849292654402c0100004002d481c0410801c00506540b00c4482c4241604040200250b6001510582d4441e03000f07200d01065900d010743d1611703400001442600d03200b860241c00500b140100390100300700c01c4002d0292865182c00d62505e040074240d40540f4604403542810440200c4040e6060a10000084000c410350740d1244154180852030800f600702289008050a00c0514114014550803e02d200f402c540180b0b1071b0352310358503c5018082070b403045400070000d0045e2001543c881c05001d100b180500001d005803e40c909050b420342d000b0050f03003100c0c0c100c204010300100d40200001c400c0c081904501080e0400314960b40024100d502003010030030503004507010400c81000c480102150241e03541c07020701801c0e080810046030000900104039101410403112224060340203281c283d0b2290600252130201 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 661618291 1250 661617041 661617053
    0xe090a0507080c040609091101050c030706180311190204180204020703032009010206040b07110303010e070e010e0102150a110c06010503010606030506011b0c120305090102060c0f090f0409 83
    0x4507411038a25030700a1001c10f0b545041034402c100050114410500034250035413200010700c092542102c0c1040000102d09880403010400c55003200ea025038204903c428287c124520900c0c0c00d80100c000603e0015840ba031043c000400ea01c8a0640154840c0e110607150b08100081103e1007030600009012400d24000d03944d01d00c01780040318003c2d140411031a034245000145800c1241040b5104001800881d515990026006901580c001600710301615006c0b400c1c0d03612000e002070904035101c00030001c92400b050700c00160044409407101d40301320500d00019150300c10420949801a804038010400200b41400304580100e05500300040e189501d500e011242d40c040302c00040140e0002004000c60b0078240300d0040144010b07c1c04000900344000003e20312200886410042c18040400c142032100a580d0f62008002c81520829a020146800f9089820841c0202e0250080c00d0005076000c04a8003110000c52184a1180c42d04915404102240511403005504566114140400112 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 661619541 1250 661618291 661618303
    0xb03070321170a050709080102130e06030f030309030705010609110d0c0e0910031109060d020d061806060501021917130b0f04050a0f0503190206090d0c051503100e090a05 75
    0x218040410380345031172500584460940d07480994141e204101e6018201700420542c4240e81e003d0011a1041c0c5034040041d242142c03410030141a1300001090000350a400001403900c2c1c0d2081000340300c0e090780c8441043c100c0300d01402c004441d076400c0048411592456101c5042d1056609060344507507580008030344041c1044441c0c003800c690150080c0180112000034240d1504201d1f1222446d1620070081444e1100c110380082c011441c0e26030003070801030385401076180c0b42c403034001443c2651040c0c242400500101c0c4a8240580903e081c1a031011144031480c030403064208111f0119000404003545039640a44520200601d82820215a0110344001410f02c0b82a00042544460804040020040d4280d000c074030b01600301d0004201a860125284081e070380110149448d0141f9800459198420105072951003070305280c18004104020802400351003044d100e20040102c2d0b445842d40c071b4441a200c240054646450402110343c0341200e41f984116440f044c1e456200e540d56510345011 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 661620791 1250 661619541 661619551
    0x903120504030e19050d12090305060a090b09010b09150f151810140f04120b04060507170f1008060c090f010e061e0c070801050a0b0307032117 63
    0x46500501c1109841c050f2001540500300b191124213582ca004005191410100802003580d08907401d03140070107000740e00315401160400b060741c0c0b8130300d04004840c001702403018084945001240129170690030510581c10350707600c060289540780e11a00c80100c2141042d450032503029218084000c20340d12851070b020118018180756585461300140080300c0d5107210800280076460004500c160b140c3d0120b08500c0c0d0f0a9425041c641e5000360204106d2640300b903400c0444c9100c0e40401b03590422031903600051159000708010032a41c0c44400c82114141d1b100a4104c119000010200710110b415050085d04030700303001c0e0313a102d0700c40e48c0c0c0c44c2031800c0130400c0340c603102400008509000c8a050040b05581c03010024600001210b68040c001202405001e0f02c000c10341400c140d404410001700710448603141d100c1012942459525803683e8080c01c400c890400166040144041150a00098000503650f00c0301400c25143e400001d000780001d4000815030030020780d480507030600711103800700d40d00071 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 661622041 1250 661620791 661620797
    0x1090605040209130f06020c031e07211d12011104090b2202030a0b04020c0a110607080a080a02070605010f141206151201060608100b030f01030303090312050403 71
    0x241c41c0a00400505003001445032101c3c10402c1d00c0440056103112081c40722580c4004c5c0143c403220071041c19855400b556112181c9084500e4040d10400c18a40240c03a045101c0d01114480f4181020710b03c0c40024460740344004076040e080f18034517134245071060088036400500000080f4a40c0d55015084d1340c0302c8440701c4070103200020144200c5c3c1c02c0f4010300403008000d982d4070b80e020003502000b110302c007201c400d03104000e5804030201c0ca500c03c0d19002100c500c48010070a64071000d15800d016195a08190f00f04c07075800e845003144006040100c1074070003040d00551903900b804809441a10342803070081140c4581c1d503081100c50000754540c1324240c081e145031030030780d00302031305080d142d8150700d01203074600303120b404c07910390f010811403000403600d0b80490000100f50f1345602c1c4c40040b614010015054400550801101180b110303444140c480c0300c0c80c61000540003e55862041c14001e1000703480c0640120500c500600c04a07009410403002e50f4400d1030034001510321245030000700c480542c0c0c11000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 661623291 1250 661622041 661622051
    0x503041706070201020f190309170a0f02010e0c060f040e01090609050a0e0d0e01050715050a1b0806040902010509102f150903040f18061520030c010906 67
    0xc002010000c65a1180c802d0008600d40b00901c2c1e020390131801742c494840540d02450280c1c00c50184203801c240d00441c2c2c031081888a00340c1c80c0402d40e00b544c028144200000e101c05c13013100a81ca1050099020140d260300107042c80035402801e111081e0f21525410346580410800000c0b503460040708140240064580010300a08044502d8280c0e1005040401c40c242806400540040045202100d910300c0381007121015400c4401610b044c010a6405401495000c2c01001001540d0f00010301c11000ba420030003640d85102005260b140e0041c03c03002c0091842e0000520340d00309580040711050050402034100040c22002030f0b40c0c82910191900007801c5072002d000803f0007140380005d90b9810b0a04141d40580000b0b455682c2c0508054055140031400041200d07100c0600880e00548404501840d40c1c64569240c0d40c03219a060b0b00d0345142d03500d0000002003000049010340ca100c203480c6d03500c05103014841001200003840c2480340c00d0b03e010400c01d002c0c1c92902442112001c9100e9580841c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 661624541 1250 661623291 661623329
    0x509040804080106090515040b0109080a0317070c0c06120b04020703050a08010603020c030d050406020f0c06090d02010603150903030e19030e03030405010509010f0210090c03121d010e0d050304 85
    0xc04c0d140560303c5005064184401c0c04081000c580552203051000ea40004214006800403070300603205500c40d000c2030142000040a0651191001045014a2001040b242c64000c0c0841c4ca50b4400030300a0240c8250402c18466030b031207400c002c00b0500c0e04101c04190344540d580050201d0380810012404134400040700e04205800114090040c62103003411804c090f40064042d40380c2c405e00312050b41e859a40c400090402c090ac0e8140e81d0309400d01d55401d901d8003402610696148420340d40c40344d1038414081c42e901076a00c1406040c0c1070300d0344800d0540322205601420000342c0f88000c8124245915203052030061b0008020f8101c00000c4c42d0000c508100d40c905000c3c000806060010b03019800400c818040e13660440129100c558080c0303441e500480d40b0400403810981c240f040d1040e49801d0004c0001405103000a000650f0301883c0340d403210000845041d118082084040d04603440504103507025980541170031384200c032018110f02c3d03401003d90766560855000d40c110155468003020000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 661625791 1250 661624541 661624543
    0x50403061b2a1403040f21030309150e030904061a03160912050a060f140105191d0106020c10020709021303081b0c191a04050904080408 60
    0x11001100803611500300e004002c008403800b0020315640c02010164101000007201e50048542c0c00010b01c6525290001809807258001e00c144030b0790b01d55500000c0741200d030030000c200c000141541804030748002da550540290580704015501100c0c08141d012210440303029040c040190b040c040c5640e220381500b0441101e2054002156800c803102250b0405014141240e4100c50703011031300404801240c3c421039125510740c0240d1546400c0410f90b00400c400000d0465843e0b01c6202d06000c0441c000310118115141ca11910034440325400040180b070401140d011100454035200d00c1e80c05844180d2405602080e40c414201c021114004200090f0305202440c6110001c40315101d42c41c80320b14000b5950103d41c0a9849919800a4000c0c007006004d454040156800000951500c00071400550181c000140101d9035004451a403041854140900c424880703607d501c1c000101d00f0214001c892048440d03503680c445200f0071000c100303a41d850020a20031403203001420f50340c41c1010f04003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 661627041 1250 661625791 661625801
    0x2130209280f0e0a1d030c0307150513060c0e030102160b0a050415020a1205010603090303060509070512060406050a03050609011a060a050901120f0603050105101401121b05040306 79
    0x8205800c90301e10b001d010000714201c03a90340091502c400803c045030440a94041300b5079808948125200c00254403c8440780400a420f2890181c000142d541c00c02c600c0d014241c1d2812116822002d13054018030001a0f04d41d0700505248001e03140802402d034001c00401e08aa02005100250030720702240601005010624198883c03040c2c034003440b550420b0799800426503607024105c80120303008608000038510440c1e030a449031081d49814846540d48040240040c082a4819400281403c0011031a420321480c164016035980e03403000e00c1c1048000c4890380215010304100d40c00754071840300141540e680701c6400007a40c0144090210f5081000c81182101c0c100a050b8800f00c91179000c4071680d50b150000d890030000181042903032220780b400120303000500120300d501054940782e481c03140c81c141584070809030b034420f80c000c0010340c4400c0e500c1c161303000892264220703a138101c4241003010f51080c112070082c24480e1101042035100307104219480c9600b0030151001603004102001031107464011 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 661628291 1250 661627041 661627049
    0xa0207050c190621020409020301081b03060106050901120203090f06090a0b06012006090d020d080103020f06090a0e04032607120509070503061602060903030c070213020928 76
    0x4103800d19409042d81145402280b191009100d9a1034550303034100f0310143c8640340b01c044a0800c44d51541c40380320040080d003080c080c411303443c03203480d240990103000904050300010004000f071078030340c1c039055048400e940206e01d11410824034002d6601c440c3c406002450241e5120070240c20400318a07032070a85000002080c9406907485403a821022802261007207800c24003e00c1c040c00a40c510013000314211010000f502d209100e0b43c8100003010601050f4805051601d500740c80054440300c000b01c0b84280d0a0001a6002a0340d01c1140254603005005004002c005071960b0300300c540d507040a45025800310b8003940400c01c10b0100c0c030304408000b02015051041807140d2940b90400401c02401e4440c804054500c5503552004110076071010040d0310001d220050403a1054030b008200800c84035a101440d10141c850140440e10440000c801c0d01c0c0305040800019041c07460a8003000444c81c0d40c0c0307540e20340240d420000003100341c44c3d03504110100c40120003013208444031b00031905040d01c0b040d48 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 661629541 1250 661628291 661628299
    0xa0308090a030618330c0e1903030e0a0f05060c151504050604050f0a050703021b03120702010501122a0e06210a0303021305060c1e0313031b0e0a0207050c 68
    0x1d100160b116074049040594000a10021b8841d290704e50070796651340078500c210303440010501e104400b10080402102502d101b50780e5071800c94042d10900480012a000c0d41c1201041004240b0113801c199000d0401003150350202c41d00781c0c40c002044c60014500762a80b05125160f0074a0781001d080c24000c0c1d507085501030f82c04010a1030320459950b0401c4c0301904000110703442e003010404003440781e01076404080c034031102d01061b212641d5945550364010b0081e03941c0d901805001803800c1d401032040c01c1c12101e40044510800c40b0981e00c1d100919408141d8000c031703c1405c540030220a01c464400d002074005003101443c0c500306201001540741c80845c46118100c05000e980c1c004420104000c40810361508016840721425240448800a02d400290304800085a81d411600000030307441c0381d0072a041560b81700c080a018009071a845844110030801d140308804100050507414003145041500728402e404540765000350703820320300030b840c24201181c01054800c02d115061003075103001c4108417 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 661630791 1250 661629541 661629593
    0x203041a0906120703060e0c04030212010b01020d14120709081504032a0f0308060901060309120f11010e0c0414010f03080a1709060a1a0a0308090a030618 68
    0x10005030540c4240c2c81c1e403081807000f01c40811040b130300035040032000d00920344c6103140da85088518441c19811a110aa1144800c5640b440380709106205009040300c041c2c0c007810300a10380342410740700c08808112a50b0b40c130008100043c002040038520900802d040e41d100781c5614138105e82030389020002d080068000b0450024000040d0700321010100300c001c030500c3d038080d01c501c49000803011401900042d000d45007140340c4400300355004103004d1207464119112085a600d40c5802c40844061140040902005a09e000640d80c0100500d40c00c141041c0750031801098054041c0c0c0c00d4511440c03005a469001e0488540b0314a41402102000c2101c0550440c03698541070382d0110180c11840f0280412200081c00e000c007620404803810440e503404150050723824a403050941e10201110380b81c6505143c0011000064a51074516491060003080c00d4985411920b5081e4190700421020782e1040c3c40110000000c4e00d02c0c001c41c80c2080403591021095105414400f81c0c3c41c03010400d1b03071052484c003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 661632041 1250 661630791 661630807
    0x14010509181e010608030f071b030c14040b120c090a02160609060b031b090f090604140f0a030c06060f06020715030f02030412030b10050a1b02100203041a 68
    0x1825000064900803070050480251103142d004000d1904070b180ca078000002c821102c04003100007041880d102710504401c14004520070340c1300ca00140402003040d06528000c108010b100c070103c074021000108002001005080050a039900420001c4901c0d002a01c02c02c04624240d919250b000014207810342c0342600100c50903407a100d0f0b100c002407001e9550000c2e0014081b02d0360210201e204003070202c4260001c0c0744040c03480d01d010714503102d10460540000500d0004100b80d41e6000391480d10080c21035465594811109403195250a0001c1c41200443e090108003007251480d01b40c003d0715260044144e03800c080f0305481d001c1c0c101170103150407580701f048550740c00103044040b2008410f290184260f4084200c0181c047c034a100001d041c00031007071000340035001000c1071041109443c1000a099003100748440000cac030303d02c0000400d8041c08480580c0b4017420320312842d8002c40000e52110790541d400140c104019400e09001a40701140c140202104802170090785c2e18490000707800c008903 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 661633291 1250 661632041 661632043
    0x1526010c1b1407080105190b010309020d0212121909080705010c080703050c0615030114011a0a0e040e030a02061806010b1b0703060507032301050609131401050918 72
    0xc820007044000d11002030942c4803014841d000181150a00030f0029080c03890010500407001c0d4218002c8a2400828221a41c003e20501414070303405030606c079924143d81c08014496008040864040c02000030094400d20756000078021082e116500e080ca074120200001c005c40541d801c081c40075484404180315681e00075030301a00b181d81c400201581c900651404849a0040d00044641ca101e038501f4029042140940402240c02c150020442101c20349404841c5510a114015080d103c00906242e40c50310714004104000e42c904002603040000e401003001c46a641d0382c0052a03400206004800c65410f0107101d8000c01c3c00040416541014001a034603080b0603c5010850700c000200354900da41c09070105a000310a4100342c81e0507594034241100508011121080007929090703d0101050341c03002205540420545001c51507030030700302481025440b280050380e00100c00412014091030070b002c0e02480d80d1a002d00004154941800e00c204440c001e0180503849802e80f02d40900d4840c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 661634541 1250 661633291 661633337
    0x1061d0f1507060905071703030f071101020705030d02040e18030a05130e0f010e06060a0e0d082b1118010c0213060602010e0c03010c020607031526010c 67
    0x3000c4441c9410400140710140151003040001030071207003050345081c20300001180e040708840e4140c44441e900b030040d440240c0c41e48800c64442110042d100d000c1054035101e50900020311a44070300042c40c260441d02c2d540d140d5000041e461400580010342031100110001c5003d400030a601541c019030014a0401501ea02441480004215000c6070400121000f0174481e801841801c001c0d0744542409402c246000d0000d00a00d140ea94004001c00c0303c5050030740c1110001d000d15a070b100c644180c00c008018038440505001e0700c2d801c0003880400e01c12034035440100044192145014408241102954240d46c0c81c0440030000321003d10414104144804541c00584000d2900325181c01461001a100c0000c032190117800a28000d001308034142c0551280f1665405141280e0107520311030308060985542d1085180140c0003400850b04c0c4d02d0094103d00200c400700c000c080d031216158420718800480419443d2681088001c414402e205d080c031410190484500d0f102d19803401941e51404004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 661635791 1250 661634541 661634569
    0xf140a0506030114130501061a090132040e09011103130f17130b0309150c0c0a06020406081b0910031515020708070e0a0f0902030f030301061d 63
    0x392034400003a01e95500307501c184185503040030250601e00b04041d40c0f10800000d083d085405603c3c001e030203d00c0f03141010800c488401c01702c0002d072400825000458401c11a145101503508802d2619070000144040070003010483c0d000c2240c030b540c41c01e6031440d0b4644001e080d440c1140d01d031651006032030034000f080b00da01011030400e0000f5088249007821403d80d54407409040c81e0741d80c400c455041041032005141d01c9084062241382035490344044101d80c8425a0394041d00d504c01401e0a655103070b10180c1c9075010105500860403d01070701d64190614035020b0003103a6035a4005410711819401810745d6812a003610a0300d5071000b007109545000c0d00c1462442c920400c1c1d003403d034114062080c2c2100c41c1da9955a42d440803101e82d100d0051003a40d900420760405401411004243c454000031140b044a2000c5c1100c3e00315100c480040c402802182e400000c555218542600540c5003003090340b0000c60282d00541c1e1380e62401c8001418400c4c22035040b510041e03230004204035076844075400c8250b2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 661637041 1250 661635791 661635811
    0x9091104090b01052101050307050f030d0309030c050d0c12030203060117090c06040909020a05120c011d040c020c040e010207150c09051305060102190b040b1807180f14 74
    0xd0b031010300161401e0240c2c2ca00380c0d048401c0003410520481903048018101c42040d1b00311103070542c03104200301e4000000c00915070194841d44100c90081d1280c0c00408030761f406420100f04410f0184c50702400c00c1c0d01c02d6903404c0410048401d242c1089a81d010004450586142c1141541000c20000b000070309042850303da0460808081055400c0c24401550700080c000d060311b41c1c032695441c4840240c03140380781c141e1081201100002e0103081184104482114040151000002c840b006480c07040c10070102c0b44010142c0502201e154031284a00d200c48241034004180c455001000c000603210000d400c1a030590062002c3c00000d082c16009642c0105035100c0440d0340b158176102200e00980b00d502855100c01441422203032070000354072840c05401c2c207a00f900d240400d00380018804018040009003011200c000080100d60585515608400581d4610403600e12000b051031400c07186411200041c00715a030b01c0d02c00e11a042c494520090100c0000b401a09000c4003504003424004021601c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 661638291 1250 661637041 661637051
    0x803070f03110102070f0c0b07022211160212210f070501150e070801030f1401091203060f0f0f170f0610060e0f0603070f05280909110409 61
    0x1014080c4040808800c0200000c45d01c501d000c0c24941d00603c22a03e0948480c1b240510210f0a0b08a003000c8030b50a94024013100190b40c5009581903800742d50714a212803081da14413400a0b03081d00f4500030640050601d9100304448841e004008800100d414851015403180c40c104507024a005200c01448a00356949512081202180c20207485915402401d95103010403510794540c1c81880403050302c046040d01d402d250b540032415103600d81d0078000a02000740e24030407040011440d4000207041d415400012a040030a59541a06440c90120300d00210384c85400030700000510201503001000b41540c4001201e20300008101000d040d406000c0c56901120041a500c2904001200800302150100d601510b08030f2200b9500c200305010faa8009201c400c070740726140c84d250011204c02c7e031005141d6031450300c4140c000c2d92902071686848091000c01c0c0805141001007240c04241e21115134901c40501400c40d00c024284881074020070615072900705036100b080020010b42c1c080d185030f03150000f5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 661639541 1250 661638291 661638293
    0x60e0109081809042f150c060a0506061e07020d0c06020c0d020f28030302010203010e071701180b060d061d090613021807090810060e061c120302220803070f 69
    0x5521159030407040c6e00503071044040400960488010110361480340c098502a80320840c552080d548140c400560058051041180004003a02001101d105491900d49131010700d81c081412030041120564240b02c03007080c100071564040c00328100d0000102c84080e00c441859001801d0443c00b010800d00a4510b035030a071100040d00c0f0980038480b00c03d4400208019070b2031400031b01039442400f800345809a0724001c42c0c0c038035001c2d00861341040412212110070707a0130000b101400f404412072011000b5129a2001c10b08d0302c0b0700004001c0d16091010102d600c40c1802c0e1b80c10120148880c000c0d2007000303100b00300610000089246600b1080401941003181c0003800081c01c649940000c0c552080015400d2194083c0c0080d41d070412225600252038641c40d9403042d1100700e0301281f141a1180500100160083c500f00807184890304400c6070041240c1116101c00000000500400f00400d1740001c1103541283c42103600100c00002182e00d820131800d00704880d0b181e020b0010010030b185882588a4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 661640791 1250 661639541 661639613
    0x20c150c010e2a011e030e070b0d090506150303030c090301022a060c0a0f200706020a1a060d02060315120c011e08070c060e010908180904 61
    0x42621401080f41c1c0303c1c44070000c0d058440f0756010b640c1c030500303d005103008000d94040c20401c0600c61540c00108004c6980308820380c0600240030b100780c07050041040204080c400c1102620704680400800075410900303107451031034082c0260458021048602842000b41cac0e00004803035110002c803540d0307500d50320b400b00441d019000300c20030384601840c1e00002110004003100c0482c00c01c02400111250b54840b081b0282451288840b80000560b50341e18001c10240240e003840001c1b1801ca40e03005904291a44e520b041c10b240d90040f00c0142c200c40c1d5401d0500c030400c903610b08807003d2405661058109280041d01c0781a110350000d0142d51b0200000c0c5103400c5030591001c0d501000b0b01070700d10f403015612803e07440b840c1d01125a404190383e0f9401601000041b100305400340c1482e01d5000090b180d9490903500d0310044201265a240c17905404444486c2c00c3c0503210000b441801c2c4940c0f121008058814001d41c5400740c2802003e000302040f001c91030002404054070700c2004400003801c0224804 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 661642041 1250 661640791 661640801
    0xa020c040603060b01080a15120804030510150605040e01060309030e09040b0a0e070503060609091f02030115031b0e04020f1215010c03021c050c011509050601020c150c01 75
    0x10036403003460944000207128007500b098644603004d0303941d00380c240d41e41811202152446aa20410201c0480c4180454480800e1101c036442c0100700302810316580759181441d01520300c6264140c6600c80380458800d0013003c080d0000741a00e400c010f03040505101c1213001c0c1d8501480b501d403c240e15404200c0a240c000c030741c03480c0c0c1118060300c4120107241606040d403c4100940340c000d0b0349407a207415500102c1001c1800e001ba5074004002d01490f4880404109030b642010f4003018060041500b0001102070404003204120035200340940c40e50325000c0c0b0201d4100c1c1030315814090609110000b10603107a0141c2038249502141440c01c140880d85d030109009020301d440e4a1010700000411070803030641da102561103102d16940300303141c07030110b6401100c1600303154000600ad64401a074400380d03111002200e0116505034685203041240403540759087d00c2c0101d10b5280c00090000007803040c18507600545511000a0000b4944007041c5404201c0303052006030a030404c400c1c04560240b01000039040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 661643291 1250 661642041 661642063
    0xf0708060a03051b010e12060f04020f0a081507050a050909040501020f0a18090b090a05060d0c1202010216050d0f020a03061e0b090c191701090f0e010605150a02 71
    0x4890300c0d065000358043c03100c03504c4090503010400c6e540d03a84150b80780105c074413030b50101c90344064000d82d101da100c0d100140c8001b400c1241d01041c030400c0c403621500c55000b030400400404000382440505032a60b0b00007024007810990422504006807150385801c50100d4001c4001541d80283d20740e594281580240141c0c04a40c01641002400d07030b070001d40c0a8001c072091002c4800e02c9403003a0707481030490202c403042240e46810a440c00300080d520001c1e035100302c2d40808051b06d4880d80c0345583d59081c02024280e003104840d6550642c509040d964100400980760710b440040199250810300020950440e101c4014201c00b0702c5840d844c110b48034000c02c08011940100700b804401c40140090041500400e01c1c3c58145191055170140e614110030001d0040d107030880c605240585000d4007d0b03a201031750111400b44810400701c412024054036005000784094803001038801c6040d0003500599040000070b50b802d03810f040f4280400e5070740c0507140880c0c0c12501c600c256561071004090341800c0340040303 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 661644541 1250 661643291 661643293
    0x1005161e1d241b0102070c030219080105010f060e2b03090806011205120f0706050c070203071509061805040c1709010207020f1009141206090106050909060f0708060a0305 75
    0x407030045404401c0d005000400505010f1815418900524500301c1c0205207020f0800d400010082015040070340103145201d4281c0b000716951501c5000300e9003928000c2e80b04076843c2c000c89804000150703001441c4440750404a0340701700d03c10b1032002d0310710542c1d950f82c00301502e501c00039000504050049000b14001d090b01c3e03095680302d40c0c3d20b008402c0f151102d440d0540e81c2e0b02401944c001c46c510000201c41e21003001c00741803414072042da01c43c0e00050a0082500c0743d03480f01007064401581d02004000700501d50800414444040070800800071041030303003c94103002c20660215802aa4840c42c8402da80c0c082d140010100d603c03180c01c8880d401111f4442900c850b00300c0c20304c0221941900104842c1c1e0007568100b1540340d4490a100c0301201c0510050001105e080c0c0c140022000c03c1c5030040310100080890350138118804806052100550705c10b204d0369550401040349040c6002c05a0f071040c1c50038081c00325031415001a001d4000c0013407002c410002410300244150b55001035020107903800c10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 661645791 1250 661644541 661644589
    0xf061c0e0106060f02071d06040905030c0a060b100804060203070905090903030601021b01050d2a050c0c010c021318080409021e0306030a0809031005161e1d 69
    0x520854028442e500a40300040c411110701d0b9041030000843c98120351100b28444000210f960044803846406002140d00c1511281c20801051080000d001c01031140380141031040316918020080720101110700740180340b0f02214940c10350700700c0134207036106812040159403030341c0f281e1040325855180e41016a010161005001b50f0000000265100758000e8085800f640d81032503080540740040080c6900280003000441005152608030030760280c1403803d0004004016000c00c1c0d05000071030709482c0010008601e554442c4820801e11903644020b090070b1780617110980100c0d14110030341c3c005c007074a60340741c000b841c4291207104040782d03440c0d81000c5156112510390b024413020b0751168a0b66000e00908946920210740000112406164010004d0003801d2003603807140500c1c1c010b103074250f81c14081d22200840316401d07030040510884e42c464085004098400d0054050540000e980051041107002d025519401000c2511500c01c00c0c0d0b200241110040001000d44056561031304010340b8034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 661647041 1250 661645791 661645811
    0x120308060609150a0e0a03110105070c0314101d06071b02040615110c1309110402030108010603030210090f11041e0b0a080619050601090308280804020f061c 69
    0x2d0005404801d08035900c144821040004111b030060060001a015001c54038002d4000d42c0103070000c0c6050345c401c2144003a503556039128100149014440c00a41d60080602440204101d10490500c2c00191651024a0704c81c000343c03039a01c5400411310b20520401300d581d00150300b28100000d2500c0d41c0144140036060300c2c2c45409070101882020360021485045111200140100300c00809c400080c20711140113810241160142c880c003441030715000c040c00e0403030415407900e0004502802030340d800407410b580b0b1813030f0081c5404240c0221110440c50314160000040d41d482c80d542c40d8507003006407240076680c4540060020040320920000742350001c90441034400050308003015007101101d10340c0302c0b04d079284d00041d1a0b400c112404bd1002c1c1c034000c0300c00f4101c4243d070300194102d5410301d40039a0341c03a103aa5803080a0761024081441181031807003940846880d01e9840903811200f03140400340d40c01c066002c00c0c1400000755205100d41400b088011b40c81d02c440003080e490780a0640705000b20009 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 661648291 1250 661647041 661647079
    0xa020f06161b0f02270f040b01081506102c040507090e0c1b0a15060614090d1b2303010e07060e2e03050709120308060609 54
    0x11003034800c40402c519142d2190462800c950300c0c82d449410010894400f180c0e80d0811030305014103990420b801c0c5a1900216180305402e600c6031161105442c100d64506060801d102c030050161702c1800c035a400944090b0f4241500c03254aa0020800e0312044010135800100b5a0380706090750520512000c41b04c05001d40c00301001e03507603029650030b81341004240c40302841164060400c0c01418500301c41400411010840340d4024070341609200c04100c02d88424014590804220000551f10103281168006558440c0e00c10f000040030141084100b0710103d500c0c40000380180400984201d47c40510700d02030019200c0c07409c1414004100c1c0c000a1a1038201c03440700301000c6103400000700b404082d10b03192130805109260501300100001c040701807608004458402d00c0a203415017160031003500150030350094001000781c45030760f00c401402007180c1c00700404540b0003c000d0020001c070420104016403c804c482c403041e0750180741c0345040395110b1000c28071a105007998035400c0640302664040d134200c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 661649541 1250 661648291 661648321
    0x30a0b0f0a0c09050102030403031b061d1b151b010507050a020601082803030906090b06010f080402090c0d06050604030c03021009261f061811030a020a020f06 70
    0x448001c00c000c800d0608204460b036640500516015038405c00081c40030901440c00d00818080d41c40d010040424540c0e1004150350503246c0c00c040b42c4000103007085903000240081040f1440505600c20102502ca00042c61460005000780044400045c8289121092079080f40d0043e0084024056400c1c00c00b030041c01075104240740390040c010403001140503040440c3e03c0f100c0095005614020b1406500d04d22141e108040003101410b0317449030010300041c040d000303141443c0e0180c0e42031040c40ca0300b1800500345401e91901e00c3c00300034141080200690724801c25640003580700368603645440c100c14042d030090a80d81c014640c82200854004208011301058109807482600c01000c0420880c4054654029902440c01200741101390b0041e454140000c850038a8691000ca03504071420980100c1140803101100c1c1440343c5820381400a1148251090107507508914104490098100741032010302000c0e01c210411500000c060130440d200301b0440300e944407a034080e117026080c4101c0c0100c48074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 661650791 1250 661649541 661649551
    0xa051b0c090c0309151005122806050603240a061a0c01110c0706050a09090509010608190305071712010e06040c03060503032d071a09070f060c02030a0b0f 68
    0x8800c441c21410049202c0c000203008116a007000380b8580d0507e02005006d100d00780c1440e446205491a0181242d074581307041103c0b40b80d44100d114401d03018284501030301e1000302218001e07030120f079002c00894100700d601c00044003c50a585071540b6624080005403007158010040f40318200000094490b03041c0084c200151424000c01c036048600604013410b001304404501103030818141040402c0c002c03030003805545410b00c3c02e504007a88440401c002c840c0d007075130b143c05581c0d92400d080c44034031000c0021031413042e40101105c0031020103581c000c02c64405c4001c002c205002e223440344910300111030140d441b0002c50091170350b140e41c1c44030352070711404d4011a0700ca071246050005044845002c2c0c03040405a0360042e010b18a0b00000200003440000d25400c006100440c07181d00d42c0b903406a81c009020b04920030303958080c1501641002d0007501b01c002e4403401e07454000304000c0104045410341e4100303c84103414503040a00240c00081d04208841001401c0028104c0c00c001c42140e03500d003440d1045d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 661652041 1250 661650791 661650793
    0x190510080f160905010b0a0309062c06060a05060d0b0d1208070e0901031a060d1b08060109060509220b04060b01230a031e0f051801020a051b0c090c0309 67
    0x2990f03124058290f803030038031035440410300401403050403074807903080000261b006100100325540f00401a55100f60188245000d410081c0c0303031002c00d0755040c48660f8120508440b114100c238103041c0020700b54440c00380400070307035990740f410f6642548903800000340283e04483da0f40340507030281d00c001c0c0600c001100c410300000c040c00d079040102d01e0410361081c180c179042650302074501c0a020000d10000701c094001f9a00290250302d001c000b0798440c005076041881110301c46109460014000e24100b0184c012403101d41c2486000d0120361105c0076040c1c0d01c4440d6a0380c04107901c0e00030f400491981da100a000c4c0030a0b1801040005205164002d0240d151080e03a654541c44016a10381c144203d2180b000082644204030381104140720b81c0029078914001486440741140703041d450400c4801461800030041e4a8400304015410011100d102a01c0110300070341c505603244100404078454420360035601225188803900c1203000b044034482c1c25202501c0008641080c0b05a0f600a82080340d0803142 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 661653291 1250 661652041 661652083
    0x1050a110a050115180501060203090405090109050a1b092307092408010608070c0b090f011b02070f03031202130e090703061a09010b0a021c08070201060509190510080f 74
    0x2169a175124481c1200c400780e01035820040c030039040101424018181e00c01d150348802c219404100240186e400c0188540703550209486005034500d801303180d9511007059a0300d85020380d01249190405036844120703403510349156550320306040ea00020175030080300401c031014000c150403042d244040c007000400c0b919a0030b140d070380e955800c45003250125003040009203000391a20000f90500c582d20b41100d450000e40d04400e960107512804c64003981040722881042c0b0b410142119014080304020301110b8920b2840d150030f689001d0039980c03441c15240d0b0740340e41c00900d504001c1541360003100541907081c0e1241040c1011880030360b0341c402e940810754100f031400c0f01410300c000f01c0503032040e8681d5004d003040711070360b01c0c00d00e4054964102d0386444043d8001c0305d0688010b6154040340c82080c00d4035072900c01d0342d0b00b0008002400c40c0c4480e000180617207010400c1c000a200b01c404c00c80540440000c02140c10b0350303940e200b036681ca0a1a840310000b4072403054661900440803694644000c0b07078000c0421 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 661654541 1250 661653291 661653329
    0xc0305010906030206070209070306150206100509010e01060518060f07020307290f090d0c0e06010201051b031003120f0311070c18202701050a110a050115 68
    0x401c07a02c5500c80290300443c200003903001806d000d10101d6014426041c00140a6503e1600540c024070800c0101d0041e0402405c0005001c2030352400005410107581d861b03681e40c10038210805a01040c01900c0501501040c081e4000064514840c2000000f81c58103480d100d00780501005a040544124840c2c010345001260320311960000341c1400100d1410203800b201c0f40d010789002513000641c0340103041c0081145050984800c0215200d02e803044041c444c0451908100039003622000e088641103905200903c44c030020716034084107811150407103055481d19048080c1e00c50340300c80d5000400007840200d410a241d134214603040c0b40b511280d1801d000380103510030f42091030701c20f01400400c1c3c5402180107111003607007000702d0b0b8902030706400002484100d8403080c0e0b0f01d0000c00d031181440c20b0300c0000ca400c1103c42c01190340c06681c4066072403070520039a0350700103001400b45c030f10000d0801c01e00300c80c0415003c0c0100309000e80e0780c0e0403400810144616582036810384243e40512a60b42003546d45800c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 661655791 1250 661654541 661654559
    0x1b2104030b16050f0d090b010b19050906071e02030d0503100801020f2208011b110a0c0501080c1b0a0201110303090303010b0708040b0a02011409150118060e0a0c030501 74
    0xc20a04416503400d40f6002104c0d00c5a00030780c201002468009070b0740d2a03007400080318942c80d540a02070b42101252641894100e604445541ea080320302048403d22003404203844010684401d180d1100c030402c441c030080500901d87d88154180039615104400301481c18903000001140644900c9948403a0103842c0e094090130b03845064100720044030208400c504040b0600803a101e8480c0d054005420705540300941400c0d03c201b80001d0b281c0b4004100000c02080d003002a040001c01d01201030b02010b00140c40c3c2400c2c2960902c529810302607480c0020b0804041001200e01b02400c1c104604140040300101c20360b102d128103801c0740825000703003800036000b200009403441086941c00840c9942c2c00c2c5042d040803034018070400c42c2e101009200101e0100000e80180030060107580c000900d010050f92901981c1c80050181c03001c81d00110000910002c038846150706445280440a0b000c0c000d01c060103004040760fa01c40500c52248005008189055400440744001c66035070074000b40c2d032100002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 661657041 1250 661655791 661655821
    0x71a010e100e040809030f0d020115090513060b01030e01061205120705060a152304150b040b21011e0602060708040f0204110d0906140c1b2104030b 65
    0x40b0600100000150020300281c1c02410100b00140655200c00465080f4500d00704c2002200c8001d80d4440e41d9050b640d03009102008010031030020700b40080d09140440c440e0001814070041d11003a20380c980100e04c1e0740203070040c0a40202c030000030007290350b507a0300030403031105802300c1101c2d54000d03021720300c80040603101610071035908480a4000b030384071703c0c40003401000c0c20706000ea014a200d403400208000d440102989042c850305050003554032140c2008211404225803010b60b9640400c14032001c9030000548080e52022880c03190f48000102c2100d40380100d00c51265010791095001082414002d000e8440012001c000c80385143d48441d402d81e21100c04032072800000b02c00348006400300741802903541c0c60071700103800003902038943c0d8504e5506a01c4240c00b9110551036465503000c01801c1c3c8500e48540d00907400281d481c1c2800d4540700d01e1841102d090117641c1c4c195071980e01c0e200300240003820b141464680e02d61400c2204912440d25070704244401e0b241010100001540031420b500d130 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 661658291 1250 661657041 661657049
    0x30a140c0a0f08070912031d01030e0705100905030601030606061106091b040e0105071107050f09150307080106030605060406050102010507020a02091018060510050717030c071a010e10 81
    0x40d02c1d0320b1610388901124031101c0180782808110b0000800035a81511100180c0e01a000c1ea076105e02080007080c05401c140b20b45155281050b10300350b044001c1e05c1c2c000c03682006480c030441d00490b0304101250708a52544882d00300680c18014007000204100c415800718080301d02503240d001c000703040035003115146e4004444500503a00415400140c0e125a10b8100302e0070000204001f40720041e5001090846000725034202c0031a1380010880c0b003100003081604018101261015007810990010421007072010304401440810b0301400c000d180d50078403000c000780890380002c025550352414403401070402950a0703409189001c0000c01c81d54418000e00344600c00c10780003401d40b01c5083d400d00c204d2090041c4200420b000c01400031504410b0706900d0740c0d881c0809000403c0700e50a100410001d050414200024010b04000d181d0004055611264580c40c0c000141d649942d220410b1203120311441c80018101c2800140d090b002014940700306040e161031003a03460440c1d4903000351017482c4c1c8250213 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 661659541 1250 661658291 661658297
    0xe06090111120703110c0316050c1014030405010603020d0c090b040c0503060d081b0312100e011208120a05041202030405060d0f090507080a05010506150f070c0506030a140c0a 77
    0xb010f4a01136040b04003000c014014151810880b001c0950541d040940300c1c07041050300500b81020301000300301492403070742d003215142081000c402001e00f500713a0b49045051140008000a420320800398031200003103401610f420402c80d124a80303002020350030f005a0760740320f10b0004410041d0400748034043e1100d81ca81c80c2c2c10b1554a4940820016000010003241c1102d000c00c98503c03100c00c0040d6103880c25070107000030b40d01c40640c0804610311250082c10380043e9035030343c0420003c01078100000c40c1102d20811600c071940f002e504051170380703110760101825040303030050501400c0c5060307500c068461402010310190304118154100c2c0c0b244564825550b101409020124413002e141e1302400015240041c00181c0d0462035480c2800d0583c0c580c0101c80d10f4000c040c0c001c05006081c003030b00d80d1122040302c0002c204a041100e04400d4000c106000d1001c00001c0759500811402d210068054034004040c1912441c002d0090400342008011141751203d150011070099203462094aa00650fa03403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 661660791 1250 661659541 661659577
    0x17010b0904240c0302040923010e0c19110c0406050609060c150405010504050d140409050403050c1002091008040b011203020709140f150108160c060e06090111 70
    0x14807821001c545040e00081c408144591001141281d0311810541040b1071314056100d914240b110b10440e074110b40c03280303062910707030000c41c0a10078000903031070550b550034080c5141c40d02c60904404403400f410020f100850203403401e11a8554100d4000124080c0410031940300007404c0d01400191040c0c0e104040e04444144101c5400346001805030400780d130141e0444440c1c0701c11000344207a17900c2c10745098a09035901c4017800248103041c02040c00904860606990060516407080b055204034820341c1c196640c0c40c1d0114042600ca0000c40328007554100885240840e0602e42030000c5d4410907a1602c140c040d17110140390305000c0c0303444600c20360300800f400c0080c1e0f280254600b906d52a400341102140254a0082050700092044041540845030105075610303200380050340c01072014011113540c00e050807c10391a80c1e400300c200b40d4003c5800f8a48202d0b20700008042c0d8a03800e40c100007e0559080154202d42c29400082691003203c2c418000c1c0441392010411140c0742c801c5245840000d1100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 661662041 1250 661660791 661660793
    0x50f07320d0212030901180606091107080904051e04121d01050d11090303070b0417030f1302031e03030f0c03010b0a050a230703090510050414030a020307030302060117010b0904 78
    0x11001131a4000c080750000705142c80340c000c4820304098003500840c0c085980e0038080c04000c40d148a0038981008601680b0f1402c00d0944840380c0c2c5000c2c8189051003991201d002a404056006c0c1d0034100a000c1d40c441c00c0e440c1450701e0291120420740100b075000815001c0c217000303421b1045008404032001030715003d1400b0541f9040744082c2c1424152000c24078010007020027540c40401c014000280245680d20071820301e0314108231608034403500c0e03001006081c814030082401301c1500980000c0380228800790f004035440400c4c141000c02c000550822040191400c00040110042d0300c980304854685200355035008015907580401c2c0564004014207110806034903000b00001c0407850301c1800c12810703102e601c40300d0000030389500c7c0c803c01c0004001300300350040581120364040944822100d4155114103100000c0c540d000301c0c440c42c0344e640c0d0034809003900ba442c00e01203481216009401d40b0b081907102d08003e59074100a100d124400d40c4154440042c9000600c600c0000300001040100700361a2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 661663291 1250 661662041 661662073
    0x108131707060b010e3f03220f0b04050904060e0d05091306060e0d0c1a18030703210e180718050607110f0d03080a1107050a03050f07320d02 62
    0xa40304071406c0c80e02068000303c4a040b0400c098400320341c0840c0c4c181003040005610072040c060584c408009440080c5003440215000d07000d42b0151401611040380f55584e50803d10054040018845010701030101424901503000000740f0003680e050740c618480c03c0c840c51451085901070300c10100060550b4541440500d424594185414011411895499141c14032040c429021084c03d031051140018400027a91000c0c9410a04034401c80280807442c1c40c603200c400c030f50166075030000c0c6c0c000356248000ca10075024507a0802419030191055480a0f5240c1c103151069906480c0b11000c1508040c40a902444c2506064240c07500600146d051280035034500c4010840e210008c0c1d440034040c84411550348034034044a9000d80207654104040c00e240e00300c441240c00000131100c9400c010443c0c0303030126100043c0c4841195040c0380066861085218440c854000d90794000e104114049420142021821082e84191480c2e064040e060b000c480500d0b540c1d510520b4080c000d07030008076001000800d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 661664541 1250 661663291 661663369
    0x2180126030f1c060f17210c03040b031e01051c03030b18091c02010e03090906040902060c03040320010807110f070b030f0c04050108131707060b010e 66
    0x102c0e80d880783c204074040482031040c0e90712900040d030006482d000411a9000c908103043c10002d402000d4500886112400e4024801c003480154403c031001070364800300d19041048030000d040e03d02c078031074480c180b4000000d10785151b6031044982c811080004225031038090308002020384200d810f20010005940c2c103a01820360030039226481640241e84525003401041914800c561280103040c01c40015241200340850850408045a14000507030742c0c400300010894100200494148000c2e5981e140014040c15141d1002504548045a2a00c1c4414004050f00c1560b1080c40f001c20085a001080d603080840020468001103882020580b510b01442030140d0600c100016110001c02d04000316241030041d6008182d942e5000007000b003540005e0843c107800c030300004001c0d4545803030440020405080074001e0907150540b020b0b11400c0001d080300080000202c0c4501c20f03110a00360a0508c01001204c120305d010485480b892143c603d4445008158068000c854006c458014103003034603508 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 661665791 1250 661664541 661664557
    0xe040b370306020304050f1612060203040c05190602100b0a1205010f02130503010612050a120203160804050108060901180b030a05010207060e070902040e0c090d02180126030f 77
    0x62a680c4000c004540350707000540c810340c0034200070305110412078403580c6010b481d5801090064611a07091140d50700c4403040320364640d0401405a10303501c0f5820613030340c60f480d00d500850740700c0a410101742e83e40c100f044800c000c0355155002d5a0502ca0404c8035030007550700500420703500c46101d120a102e162543c036003026a0394007440000030070320034a140e070504a90000d80c5500414028290420003031900340681c0c1c000e07050600d111384000280d0750f00c45030b40f9561003c0c0107110b08120310040800510800580324020582d000321824204107040c080740a5100d0300174140004d810720002030700ca00b0007064550480388000f0a101d00d40c2d4041ca4480020100468555454040d0b01c60300310108a09001525030240680c13800100d00010010b440d245c0389650b401440141e0050000b009102a04070038540c3c04402240c20725078416a01c0e0001d940c4800720300780250f103c05807440744d00f01d0018a00344075049c1e5210f00c40440b15121341c0102c00741500040c801e10329a0380c0c001c001007207040b92030a019001c10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 661667041 1250 661665791 661665889
    0x20d030e07060f02100507030f0c050711101407080706060602030c100f060306050c040602060108060f04110a0302090406050f0105030f07142b1104090f1113020a0e040b 74
    0x5000d003841d5682640d005541c5940049e0b15141c02c404504514803443d82c00c0c21490514501d061400d0307071345c13a0342c005115000381d11a0321040207660105004803007c0b40a0020400b10941d9000585403d400c01c1d0030007041510203501e031000105089000004440040d80290b00402401c10981007e401400c803c00074501d00d6a280e1000100088450041c1802140710b461100d80311801c03c1802850808140d0100006500c010b0070703c9086070011003c103801941000040d640f0070100b10228229046540c0001e4100c54002e0030401844500d0744498002c0801104040caaa40c3c1c0f90304041ea11115402034030b040d0b0700a00e000b00b040300180744010980d61005400a401ca817040340c8042c01072041d1443c0400d21200e14910b0328100146500030820000301150100b0600d9000d0b04d40020310380550300001d1259050180e010615658440c003548007900c000e1003503556050719100200035105c0c0000c0c2d0360103a03081c09c01c681183e20f05220081c2d08481e41c420038035100035a0b65143c007e00d00445444141c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 661668291 1250 661667041 661667053
    0x7060e010e0d030f0e030307090311010e120d030c0503011805090109170408011104030c090c0c050105090c0a05043810090e0f010501020c0103022512020d030e07060f02 74
    0x105100c18801c4000e07640d21902d00061113002c5074400004e5584a404c001c2e8590810010400c045e42c0120303030603095039007000f5080b03c440c07000703c0113a800070f01c01c080c0503501615190b5141c600002c0084ea0316041e424940d41440b028160030b0003510903010a001d0310601810503103211040200c1513002c5980180128004203819445848007420280e80449502001400140501901c0c900740102c60302c3e01006401c0a160510315141c01c80c20b0412400344800390b40d110400604020305c6041175001541e0450002c1000c2c2c209000740550300c4d0256080c09019420607c000a018074062040c0c40040701c400c04401410465045101ca041a08941142d000310100508861a4407203003ccc100301c2c444181c82d0150f0b901e05010b00d54682c1c1e180240904003035592180103121a980c041650a0f1207402820b025881300301110315081e001c0406100b8640c0c0134442d82d02007040c01000c041d00035040070240c0030364010b500201c03c00c0b000e44a10314144660b5520406c41007200d1445101220b010740300078410740f0700c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 661669541 1250 661668291 661668311
    0x9160c0f060603120206060d020402030601270503010609050903040e060a0b070b18210f070615150f020d050901110303070c0c0b0c060a0222080307110a0b07060e01 72
    0x50301040d5442601d074156914000c1c4104650182c05031000c44980c001406945040c2001512080c2c4031040240103070740110100b0f8403a4050030307036201c501d170900349101355811610450f102c4071505403240510030341c209500028071498038460725005d101c0c228051031426042c0f007140f0400d02d4001c7c24a5070040402a40020341c002d845014141c964480d1044441c10f041031108000d81c00c00c680340c2030807a504044856403699009844179443c0443c09484079448005116103030381c0340e018650010300424140500c11290500304901041560013600c084240e866602030100c900111141030000982e008030000251a40a00050030703c103a01454051200c159070013600e81940c10903500c11001c0303420700c14213904121034003601c403024001044c007850426020301e010f1561050054104001c187c1d001502440c005408503288136010040d41c500c01005136655140c50340c9a01c074001c00e580c1d4410854034250326141c0300391158201c40ca00504a400e02e42680ca50b10700800444c10760803103540da2400828 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 661670791 1250 661669541 661669553
    0x30106031e021c150e0615192609031b011d03030a0f140c03130f141e0c1201060902030405031b191104240302212d01020409020c0d0e09160c 62
    0x4002e4299510141c150588100242a10540a075030105034010480ac11070700000000c203581e550941204112550384103130408030b004001c0d601c5048054400301c00f00c642410320010095008400c011070070400000d101c44114202e54108034112441070500001c03c140e02d5241000d540c220420350030004042007250f8503140c2c42520844105e80038130051011004602c010f10105402d16046810220004000744503140c680d071100038090b1141e4280341e0400c00401003540054007602594104643e070341000d0a0856072a0011620f04103d20305555407810516004241c15901c00007508a86c004899a5611180600b0241700e4903134009039199100f9049021688100701d8813042d050b440100141140103101c0f46c00010b140d110024031420300100c48800002810703e07440201604040b00c0c0c0c021000307184040c541d02a000c4002c83d800890041007103501603008020800340b0104451090a82000c00d407900c411407403200c2d9121030400001640800c80b9405201003502a00c2c03c45011002541e8030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 661672041 1250 661670791 661670827
    0x50603160f0e0414061309082520030f01020c060601030c050c01092901150c020303040f08070f05041a01080a090f050c01080f010308030106031e021c150e0615 70
    0x40c130703074080d411801d00c001828004240c10140d19611800e00c402c03407080c2c6481c040c0e8480c0020765201400c11a0181a051400559404000da80300040c16540c404201031800c2c120510040103100e40950754030100500c0b014404c80e43e0165281c00a030071190b40b007500660042c00c1e94600030080c800104005a1404000c1c82103014841c8121103200c10f4141284d14034500110340e5204081c01640e41d0014030102014500f2004420014504503080240e14400300341075004039480103409103070881011440e000c002c905601580c800d401e05203882039485d010002954011030f1029905400c00a40004a520807202d45a2100202d01c011900414581c0e812054141c500780940d800c0c0c1015002009642e8000c0c80785401c0303007054172091413035415921046170900c010301c0307003c0600d5aa0001100c21210b00c901b0100b94542079001107496840d00702c2c0242000780c0010034808014030b0418250f03d039020a049120a0b50b490a40408069031400c084c40322101d00215100200402400188405d840c200e0780 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 661673291 1250 661672041 661672061
    0x6091c0309080d0c090902040f05120307050303040f0201020c0621070201061a1806040807090c09030b190507030c1b14060c0d050112031b06060b040816050603160f0e04 74
    0xc005114480041d008040e008203400602c1b50500400c401c201c088824240d03034080c0c0f41c0407030301d155030040200821403640c80f540e1801000fa01011080006000303e10200c1c2150900130f8087e142001f08000c100030702c504c00c409005040045c9403a007a240c1040d03403184198000701074000041c099403103042c01c0b02160141d51080310002400a00300340c3c0705890945000c1c03540d80c10ba40142c10241003100300da481da950750050350481e55841070142d552030b00c6000f290004580107a8403404c1801d00c4030810010425120032600f17450709190101d010306210344101681400c0e141c0d111240d070342d811402c1c0401c0184004c000d03255802c1011010421b910140000b038010341e1000c107a00c1da100c24000c282d4050341d10580c0400615040b20700d6402c08240c0220612000d0b29a0003480b2441602526040000b050250040c81801c0b070085000710303014400140030615403214031329459400f5910b0041003001e1104a69003191207240782d21582c101c0c1e00174800d1400700350160800d00901045034011404481560748 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 661674541 1250 661673291 661673317
    0xf020d080c2d03030403050a030603060510060807080f3603090a060804052d060f18010e10020f0d020a02030706050108150c160b04050d03060806091c030908 69
    0xb041200150050280e480154030020507492400c0d03214184645a000c0104040c05106000846054040c031135030000c40036540c8020200410300b0030000c8041ca42810703005040204039900301003608140210a0544540c05154800820b50750303050080328954003014074100f80040000a44500ca03481082110703084140400844d114003080040081d4000a40e00c150309000114ac148401b044000c14032a08015000c030b011011010307400001d00100e00c80413500c0442c1c1c052017040c000d10703d584103052401412156400d660b0200050b041c2402c0380c000000c11040356005803e42d11880c64a50040e00f810b50803029100d04082c2011152002d990140300040f006030000a08603081204c94455a070140030035400420600210007407040d01d01074050101c100e840310100b88490022110420a1605580000c11406900301494100d9444540c7c030046004a4100703100810f1406001070f03220701c1120740c3e0b001040c1d01d50030001d15a0711202515605c50800d61603819080207d69207200401403202c2400d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 661675791 1250 661674541 661674553
    0xf02030f04050610030b070e0111010507170c1303020906120f250602030a0e1f09050301050903070506040f110d0503030a05010b0a050a270807030c080c06070f020d080c 74
    0x101d04141042c0f002041c42130203120026051001c5803111104070b503c030038103040c044000e0007501c005844010306120104215030800c410085103691040300d44112840716600a00d45485400e503c24290184040c0500107080f9008100058680380907640d8001e00f0240140d903128804c403440f01d0410621400112143d84040c0c2400d1760318158201c2988040201c1120710380503414940000d440c2d20038901e207070040280c0030500e5040703599480e0b0b00207038250190800441411700c1d03074005440540e4521507070388254a0072000401c080008030450310540d50040c0502090b40e070716910500540016001915440780c81c1880c0d0702c55031030303c1d18000c81c054006e800840d280c0c6440c1c03031400240c0b40140c21050a100040c454840310680041c2514803098040c00c20700d000d050303040c0041c013290703052450729540802031140c0007a401c4400b14858064070b0146614111042d03e4a424075580d40d1a2104070740c00000c100070b82c4011030142c3c511125070074401044d1600c0d1444a4503281c03070680021a030307440c15806c02 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 661677041 1250 661675791 661675793
    0x304150203090a1704060905061b030c010c021209010903020d05010905100e0f0115090e030c010204120b0f0f01090b010e10030c03061a2d0a12050109020720040f02030f04 75
    0x1301804115040301407010720b81420300c00024003014131031041a00400b0041481201e015030518461409100031041f030ba00d030380c410512503000c1c186c4c18150f0380145c0101900b20301e03072100714021600d0015068444000c20780c9150700740403071a036002e24203840030756945600d080020b83c140411004c4255801d40400d9001d01140054140a80b8416010444c2e00d803040e0240344003100f0200004803003610000007900c480714000309081d441280100c104a5100250100c0d008039014003500d0100e000f00544006076445e0140c2a41c0342e03006441034502030a0720401001416190380008030454010b1421542c0001240c020401201244140300b000ca6250020000025414071404d0000c02c2100812014000c4014640710349103c3d150140ea21812400c81000c1110304410b925940420a030405075610020110010031080c00c044000550a05200c00018218014003c2c2c90041d80c20464070f0106141480d117900c541d61501c407006030001e490381d008110040c0360303101551044018950800c014030301 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 661678291 1250 661677041 661677053
    0x30705071203050105012c01080c0903071205120f071b180509161a030402030111160b06060906090f04061206060510020f1c02150403020312070504051003020304150203090a 76
    0x440f02c0e10700c5c0e02080100c0480103907003038104887c000c0a0902201a84034040d201d8014414000d0542e014800c04500180c0008480b07151447d003406041607a9a215910034400560701c125a4008802c00707040c440100410140051150b60314a082c0010015580e207040b502950070502c510032078226500d404008004c0700034054040e031740504508aa00382c90034200e0310044e450b80703990509000ea50120020341152001d51000c0d0f850100b4016084d03c0d2010412200003040d0880c40031148440742901095550074038105444900100400050400c5004001e00c144c5910954106a119482c3d8600260500200706540c128034000c2c1001b203040c90816003800214220780c600d00d0219804800b05c10348051000c505031004c407090b506007a141106e010012442c15444942c0b210045504200b88010940c0020007070041c44d00c404620700c1030303641705c0d40286c4282c01a845030300d41104401c60301c02c050341d1003640110380c003a124000c0d5002d6041900d1181c2c4c100d0b002141c800d400c1340c0c03041c5a00c800b40300e0b03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 661679541 1250 661678291 661678307
    0x20a02010b01020309100c06020c151005010903020f12010b09090124060c150b06130512070e010902160c0b030619050a05010e06070b070e01122003070507120305010501 74
    0x1600f80011131601d10342c0e0020030b101080100c0d09104100748503401400b009850f0301112072070745407001100d14107000701c04900090001501d94100c03509400b10006aa54001e140140c02c8075001400858500c007803405000082801011142c80341d5661211070409030345242e103250040c00d010300001a5810a03816083c1c14a2880040081801484604212260b0304c80d0034500c560750f020403031042c608101c40280d0054280820b00d55400b1002154180c507440c2081e00f01d40448034210303603403568800045a05a03c510160041c1012074105800500540040d42c00500708054282e914030a518400c1d241c60201006a0f00311300e440d41000002c1c08003a14091641000101d02c1c440c0000601d85802d001402c0c02440d84200c90522070889a40307651a9291003c3c0c0d0311558001c12907503068030780040018030f810215000301d40440c0401140803000482d5201d4034031104140c0c03801d08260b05840c0925800c3d81c1000300002e04000b010804180000e000710301c090f1080b5540d0718045a50350600001400c0070b1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 661680791 1250 661679541 661679561
    0x1020f03090d0f080d06140a05010302070f03030e070305060f01030c150f0c0602250311010e030304060b0a080717011b0f030506043c020c060f060a031203020a0201 72
    0x6401031000340950b5075452244101c0e2a030103810342d002444285042c9100b40107410381d603044079240010005039425210407142c0c400a0844040e607105072980d005408074007030880081d000c2e00a025071300d00000d00907406104401c00f54400c580c1d8507036030b07687e0f03c03480c1c0001140e4044001e00c09800410401001404d9072000e030009031000400c441d41000b0042c04240f603400300c4c8013000403580a4078140441035045482c0e501440c54a00c410b2203802c00042c0b14006d5901089000030303403603e4004007454043c8990212442000040d61550701c650b1506400740281a8007964480c0038804001202c0300100484401488000141258401c0e8800d00500311040d900c141040709441d807000ea4141c1e0340c40070f1320f210301c940f8038200001c0548407039000c1030040014041030140207000c00104114204042c50003284040c10811070342c501052818400242e014808080780f10fa807005c000f04604c50045506d40da03100d50050407151265582e0346424044081e120411030209031300040c100052582030048030000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 661682041 1250 661680791 661680793
    0x9040606020a0f15020d0203012607060903020f040b0d0f0c0e040807060f110f040f090605061603140a0c050c0904030e04020a051908071e05090d11030a03080601020f 73
    0x50b01d031600d94001c1d5500d0814000c06040700508002103d11042e4140ca0003080600300071900c941e1500d0500c0f045c0842e0084c01e00c04038000c12800d40d0f00f44030008000c0c0544809954001c062841c0d42d0074000400414640307258429150140c82209880f0050400a2240111182c0d1140350341406d00c18110401038003c40000100b20080001040c10007084600740707540b10b000085c406058000e150000c03d01d48483da044004005000c1805a403150090b00543d0700074494008580da0360801d96048400701d2091542000b02400400032580c2004004034003903000381812000a035800300741031140e030700103801c0c00c000c20101c80c040424048200b0600d510140180c404d5016410301c3c2d01c0180c180340d00c425840e0b01c100d800181c0920654850420b9800300550060051008096a003014240d100200c41800002d24900f40d410b41c1340c0300c5404084024500303a160149403142c0c0e4418032221040008054030701884030501509240c90030003034011028020340d1584000c3c01d000c0002070a1a149985041003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 661683291 1250 661682041 661682053
    0x40303050f0717042306010603020d06050102160911280801060e03060406110c0304090c1116030f020604080d0c0203010506270619060507060c03020c0a0b0c160501020904060602 78
    0x3800343c1001180c01c9a0002a8100203501d0703e800b0f0b0030114180704040f076641c003d5400024415030140c0190502c11851001400302d19212001240d4070030703070707449900c0c9029850fa0b8108415261a4840c40744008068070440c6407039501b075100840b400140f164181c1420403400203090007988020405e02509140c5405035020007902c0010740e9a03000600050011951b4004203500038101c04104c85410001d0401e8989503580c034598000140941d40c44503020400e4400c800d00071003004203006c25181c807540300c0c6180311811a1a400741e005c4841c68100d8000004210100b02000d04000c0c403100840703941d4900d40c10407402d20606080d190003402c0d803030150060210324420704c03c4801e91601000c904031004101c0c3d6641c640064641100000703083c0351402c1c4100c01003a500e903c01c1c01888400e0040308140607551004500b10121700c40c1c6201c10006810003a03482d030004504590700343c1c100200c0080380381840ca4200c4208680c1401203011034580e94001104902d900389400386000529072030010b009 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 661684541 1250 661683291 661683317
    0x30201230a1d0d080103020a140d03051305040f02031603020c0709091a0f0f070801060f1d1201020901110318101e2007211703040303050f07 62
    0x2148041d00d01c0ca03209840390008040c420402d0402c2c40100d20503030448440508945028021440070300069004001440c000b04218100c00c80c001c0e50140301520604111451740c8080b6619084481503510880e48a0b83c0001c05a4440c00b400700028416000140c2e00c1c03e22409818207044804005014540123004c05851900085002000c0b1080250040f5a80d030443c0f8200b403144034a0500f40d1024080c0f1800d00900c0020075141e0391040c00b900369520341946402c030094561070800d129480024030921030620070301d80300f04240c14004418421010000d1090300000303481070030328007074488580e6000c5020f007001d60344080c040c0140e40d41e8a028500e0310182d19071085089104c1d1944502039000d05110480340c3e0304c104024411030381e4a040d4003120301901d0000804090b4040300925400c003d801c1c00c0302c4112001700b9800220b42050a0855035170142401a800003500e050060303a20882d00d42d45165a0104803000307603c114842c1ea40001c1501c2c040501c05035021000d0040c20420444098240c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 661685791 1250 661684541 661684601
    0x603020307210b2a070803010303030e031c052d070305070c060f0615030221130b011401110f03030402061305120c1f0e28030f030201 59
    0x1406a403032158150b4400b07981c54200d070310111141e10008158100d40001c00030380b850314040c0050b284403030000401444040021944c954000e4600c0030b00000303810801000081e010b0782c44955007000d035100f92810040d005008074803030b250104c0c110b0011503c1e40108800c8510311030b8200c0000f62011000c0c405903030b0814071446011001801030061542d90008100094040c40c034010000b40d001006200c0e00c0d5240049901800c1d092165041703100c01220f281525074003d0080e03039804c2c00b41001c01c004110403008094030440e4041c0a031008100c1e0480300300f022680c20340e0902d018000b41c6103140d5a044008000511052441c0e0300c0100640120a02c7e00404802100301c0750000e0b01100c2680c0c035010031040e101c24070768070f59018551113141507071200c1c0540c00100b001b0740031400c1240d2280040c1c4000c0c1e81c04840341d462074a03901c001114000f070124a850401c1ea201a0944c0c1c454005041c1d41922454110070825074205645d809080c508810400d5424040d01c000c14001178060011781d01540307401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 661687041 1250 661685791 661685803
    0x2714030426010e07090c030b06070f03081b0409150501030e07090b0312120609102909040905030c21180d020406090f050f07020d1803051006090e0106030203 69
    0x1080c00c1508001d03844215009400c82c00d041820501920003840d50348411070010300f1940125000302e410510903c07002e00c0c01078265601c454010030302c603548803050340d01102c9000c4001d00d494281c01c5650342264135404490094000707040d180301c00050001c03540341c2c444002d500d2a071040707040605180d200300d114840855184200c8140000101d0b0200c02c160010341004191140d04400341d1001c00c00c402e00d5181d440d0f0b103a0140341d060380c42c2d210315198140d40c06c504261038003aa1405142110b9403004a14103241101410303411601540e042c0002e80000809462046405441c55031011a00e48025001130108003030340c3c03811085188401e01702540340b01d268000c40d01c000400309a25074001c01d054903461402c00000c1da00600801c08c081e19102007100412403072000321411440c110020301c1d1a9000d5015078000e500a0700204001400309000700c40d40020014504112100710100000103030301044850110040004041804ea040080940442d10450602d001a80c145041000980c42c0032480e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 661688291 1250 661687041 661687079
    0x14030a02060c0c031909050d030e10020d020c13060b030403020604020907052a0a05010f0c0905030c15090303301303090306050705041208180105040b0d0f27140304 72
    0x1400150300e01c1e0981034803086d05c250f0000d034008111a2142003015032011f010403000408503600c014042524100326520720080d40303101e01581c444041c00c28589820181550607441440b004240e40c0d44980c0c09a05503002030b601100940d12007c240004c5241003000d641d0300061511349541098030040e8030054165001710a0301311201d4001c0381421440062142900d0540c1200080c0008816000c154004054103810b4000003001000301190a02c3c01140d44802600e00800724905603045401c0740c2034643c01030580c036034188010441100740c05d07070b200070703605000c02841650301240d603080d200101802d000621000c8101c441c801102d00194221041101750703a0450310008803a40c0b600c500b0b4030301e44501d4000044000b0480005003c2100c040300a01500b4503942c200c3e80106071400054600e801140a4142c0c1441c09106072020014154422140e025012101144c500c401c0451034107041c6030b031012040f500c8034901002041c010010170740c1c614000341f00005c5150610f02003240340c0c201141c0e40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 661689541 1250 661688291 661688317
    0x70e090c040908160c050111030a0503060405100e10030b10030209070e01181212030513080d0b06040608091c0e130e0618011a06041203020a14030a02060c0c03 70
    0x1a40180703c9140151642c840400d014851181c00508145440c6982c07072042c3e6000500105c00e0104042c00841915208281a00c80c0741c1107448000811010f42001412102210b50030000020085520b070010b900800d54010300d6a8079504600b01408840d100910020a909171140e0410041e00c0302d04007a64480f0302c42ca041086c290a290040b19030070840a043d00104250003008210307035034116448847c40340708602c00303a041c007050401a0182c0700c04865038a2080c01281004012841000040c800100c1c030400010304c0c4d03160740340011419041604050009084a010400702100c03c1155031303e80c200103014810001d0043e81c3c002c01c036403c000d8986008210840b03250381c8005154011240030303408107042d41c001d4900920250007030381641641d848550300b004d80150001e0301c69480c64020704805050280b421b801c00580480221920204804511441801d070f00819282c3d61502d2300c446d40e0401442d61040f20810017881d042c0d01404022044108002c001d4420b9000021101d0b030f09200c031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 661690647 1106 661689541 661689551
    0x804170426010e1510080d030b040e0a05060c2808061c0c052e030b040621060b061b0a170702180a0e070b04030302070e090c04 56
    0x10f100103070700004200a681341c141075049a01482064203070208039660346a207131405400808610000e980d440300b03048113161a004401a00c04140700030300b914440d03620f03010344920010f0321118101c480010b4407a0240340d560b540000c800c43c03480c941280172a0f5000c2c0500016400c4a500e80b0032a07040d408a04102c1208903041c0c2c1d10340c1c006181c0c490850906052041d280c520406404201510074262601c00c69003c0e0f0900c48282c1030b940200d201d1524100303210a41d1401e401080c1020121194010070100c0402c0020405801c030b40701240f01c0841c00040307501407040902842c405803000c09120128100000c6100c2410b2103200e40b4031102540c00300c954014010000001d43c4200e900d40c129001c044140c0c1503070780080d8045d0b000900898070701c40881c0380211584c00400700030400b040c10400d02d901801034200a224110840b20309103888101c8076258980460814480c03a603034 = true := by decide +kernel

theorem cover : BRFrame.Cov 661510791 661690647 := by
  have h0 := BRFrame.cov_init 661510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 661510791 ≤ n) (h2 : n < 661690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
