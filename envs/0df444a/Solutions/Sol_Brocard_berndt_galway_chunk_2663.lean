-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2663
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:22:34.282775+00:00
-- url     : https://prove2.me/submissions/873a2436-96a3-41f6-975a-96c1db98107d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 478776978 ≤ n < 478956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 478778228 1250 478776978 478777087
    0x60e1e1503041b09020a3507020a05010f0b0f010c03090b120103021801080706031e090f12020c0a091d06090d0306140a03061512080d11 60
    0x3012082006000e40c0f0300303000c0f488980103000d0f142501c1d12820060101d009001034440020944101d80b816072800d1000500d02030440c004034942541c0001c3c024404203001c86032000140c22403520981000000d028041c69008074000034010012101c0100701c1a000c00c0e100f8604001d40c1050060616003c4d00c610005000a8031401c6e50380c00d806031004607070500a2104a01900503c241881c0006040000c14103984002d8045d21005250041c00c501400c0500341100705106144100c514034416441105525481850500801555420003442a420b541d10710810354120300d0080d5001e51343c0003003203c1a2844942c00051500c4031030702c8230300d0084074070400e610b071403040c5414040c0803200040d50301600c84d290b980a01c8000d807201241c1c4000b90390111183d42040141d00c1c240002002c41e0405180404480b00c407495141e9650740318415903c070b00000340d4491600250031441d01406029510400280a00c8107191240c2d418025034500804c40d500c41116581c540590813560341080302100f98203 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 478779478 1250 478778228 478778269
    0xb07020d140f0d0e040203090c060306011206152d200d08100602010b011e210506180c2703030d0204150201090305070318031416060e1e 60
    0x107290b80c1c0309603100328100851002c95006031400c0389510b414022684141001405042807121000601c1801d40000c0c00c041c0c11b0003074a9000b010012000d201b500c000b0305601e40600810070388030002500c1c1101c941404144c4c00301415041c42c5600303140760f9001200490b0f29040801d9890442115521a2824456203e0340980b480160384181d01a606600844a902200c1071095940c04180e0813200a4046d05010401b040211070500c1c102c0c3d005603102c68030302c2c101240a17000c1d02e52142148201c61703850091035580c034014000b80d410134095821045085003461aa03c8c1403824000000d80110064008007032614030700e0350850038540c0c809910b0f0b940041c0c122030322820030b51040c0002e90018003031441c088000c238a80303800e2944140a070641c221b4054850300c1c41c10246403012a180da02004402c400320000b0310000001a19280203a00a0444034000d01403015016180c02d0901302554070183c2045071400c0141d07881c3d60b40c0d01c001d0300c040b000405201e006d00b8015003c1003c0340e28240d4800c1481 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 478780728 1250 478779478 478779493
    0x50411120a0b130b120d0e0904080408060c22060507081e0309152d18100c18050604260307030504031a0106210e0d030b100305010b07020d14 62
    0x101c3c5820031101440d00700c03002e442c034100500615075503c415074070000010301140c5500809007404075110341c009015242481c80c0c1303629000810701c0e06505840d90004601d0009840e030307450049111465020710340c405a404040c0c0341100050250146510141000100281c06039500560400100c0c1c004140504d8603140d1a00401154075003034100043c41c2c1c2c030703145e400c0010980404080400c00780511003402845c000d080c200c4000034048000d10070980000f5079900c80c000a0020850f40f001c02a4841010803440640b410080c10440709094640318811540d000348401c0e034400003034070162540820700384110b41b400d80d4200c4448a58102031002c5010008040040c55404001042a02c1c01045081c0c0905205050707800c1206003440394600040075200d94500080c00e1041c80d003101d0541102c041240c0d01d046003011b04215100b007201c40425510400f8204608118014140000050504101070362400054180b51312581900038440c40d01c0c1c4208204002100361802c02d2030803801c0844d41803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 478781978 1250 478780728 478780759
    0x3070f0605070905030102030609070507080c0f03070c090c020d050c12040320010c05060f0403170a0c03051003020604150201060b07060902040b0f0d02040903020c040c02070f050411120a0b 83
    0x41c0002e4a488000988690010076241414001c0b40c1c040c210140585485a03540001290310703820042d011150b0030b104001c0000400c40420540a02c040c0e00405103944090520b00040110f020f503201442940c14428150005500464400307181121411300070342c0c03544e03072040480c10700c842114807607541000440e011080c04810036400306030302c4c25200c0650508005800640d00041103490081450b48a040007801100d141005140c009220781000d840900540c507070143c104071f0841e00e01c052a07558090864406905004041e0801c003203280c003004050860700402c0851255000d0300c54620300410b0f400302c40a10035800f140c0102880c10304503480795050328040d809020821420380c400c5041c480341c1003117407500f1980d00b028207c2c01012841404403682c21700c40500101d9405806600980222070003030b480328000d0800c1829958042d20f20742d81001020706004102e41c100c6802189000b40100e040403418040714045445602d4044895031101010000f410354002129080300355140c0d00d0f4413 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 478783228 1250 478781978 478781981
    0x15031014011502030903330103150501171020031008120f2205030316031d0d0b0c04080a061b030e0c01051b0105010f0f0605040f14010203070f06 64
    0x142c8522041c22120b844042100b04d959019400741030f54560000104050700940144450340440c1c00e110034012014001610340c500900d0990081d6088840b40183e80180d045c20301c0303540c2c0900350589000b52514105020169030703007004580c811030990343c0c016124041d030b0300480ba0a442e81ca4040401d6076443c0503140c00c0c0f801c00b003e100700142c80c49036a880140550048080d40d0100d00990b002c10b080c070800c2c1d02c5060340d00548100ca0044502c01c00030200c0c00d0786042c13006003040741080703500e80240a0036243c01001094800000d4050b4803101004042035a01c8200e00f095039608032100817071035202c80c2000101e500c42c07070340016003510841d40001c0412929800202e0340300ca224207101c00450b8415015004e0742d06180301030400d60881c6441e181c80d50301440141041200b01041240d42990038141c0c907086a2082c1c000005038030040804104010780c258010b400380c841480c00c6130500380707170403029500d01200340a401c8030481004100e40d100d0b40308105588241d50400401d0b8001c00d02130a2040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 478784478 1250 478783228 478783231
    0x70507051506010f050912010f0515090405030906090118090617030c10050a0908040b09030708030a08060405061f1806110c0609060708030c12100e15031014 69
    0x641500440e5520991824926401ea10442d01030311540c4c51140f02c2c1d2400c503040d900205966522a200d1010602d20700e109120316803eaa0f0425400074213420f110041c1460101650f201c58803a10120341000300044000c0243d40c180341c001e9901c991200d122600503a050400c011109144010455000404400c070346c2180341164100c0200c203d80405101c4503507120702ca4541844642d43c00f003000c50442660550003a90300002d4080d001030303000040d50310b007201540705520110500601084103480751505204080080500400640c5000072101703026101c604020b08903480345682d840081c44d143c80d041c0c81160784400405050100860214000e0500301c0c42c8088400040c03081503010422030f0041d0017011302e40c0170f014020160500f400040002d1035102001d0f2940000080c010705001a100030060b6008030808003e140c2c80f00340c3d1000c00502c005004208090440c1100c1003000305482982d00700d0b400c02100241011000c4482c00868a0300b0085840365072030740e142000382070090ba05d03d00801d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 478785728 1250 478784478 478784483
    0x2040915140601030c3e070e0a0209130e0a0f0602180a2909100807171012020f100c020f0405070527040507030b0103051806070c020d0b070507 63
    0x10b034903180011030859000d42000c001184514480d0550040555110001d418200030402c800701c140c03120702c43c9070041d42030b22840c3d00d0340140002c1c410680024603080d4000c224040031401c003500c040000303c9000c107130074078911030a544402c0c800d041c0d0350511524503902e0b0082051031041d0141d1804130000d50008245140340c000380507040c0c80d18a0284111421502110340703038492284110a000c246100840664501040401c0401015100c886072101e5001103503d03681c4d56440d01e598040c0440c0d0054003c09140408442001540040303248030740c5c191030403c03001c0303038010000d413021030b00c0441780a4400d40d00448804410b40403550203656600c00b2442910001405078611043c0030660314283c0d0500003040003030000b074035900e500142c103683c4501000c0c2c00001c400c030082c02080c00ca92003543d4842c0082e48a18541c081c80d41c0600829800c0781842c20146041220758080320f4036a42c028161100f00f04080010b9800d40d640c2c000e08500030754020101c0101410480c01c050701c564001c0a04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 478786978 1250 478785728 478785761
    0xb0418120905010807030b0d142b05160302160905091905030706150e010801020409061211040f02070503040e010e2d040f060e0105060a050d08070f02040915 69
    0x880a0452040d9561802c550041e154000d02da00d40303220640141a081100903001246d620403080031031051401d40004003131070720190446101082003500c20984070342101208000d18901444003982c044119140566080906a104983d0780b800700e0038524540901a100d5080c080049204010b5a205034000c3d035240f401c40e803008a00e001c925542d811054405080e0760802d100b8800840c01d10b4004030062110325100f4182240c442ca8035241d45002078020020300da602060912100381c0c144910704c09001c2d000726000c42d13102c8603519400c142450942c0c0c0307806140c0b100d08404880400b40c06549a080c1e0040076203494680704c8007854095202403041c00c036810b4101002c2000188514080f13001e16003049200c2c0f0f400f44e038501c05049000c0000d032086907401e042e200e0ba4070114640303100364081c00640c5030001c0740c282060420040040d645420003407040e2207041c0c0d5840003407403d8041b1803846521461200304100c075400000d009000a090107444107194a0645100348500d5004012041881d00c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 478788228 1250 478786978 478787003
    0xa1103041211150105090601030902090406270b07030c0207150503100b04150f0224150907021905010906090308040605010815010b03100f0602030909160c020d03030b0418 75
    0x880b0f035100400081c6001c983e03940d400510182c1844071500354421818140800c1c001c140340c0c046400c0309811681510281d0381e90a400340704080410031100b0181d405401c050030f00459495100352008050300341c0c018140e45e901407040c1c140c02408008020021030407248503241c4840006499a801103541c3c010314030101002050020421051728140c82c0b000a1420796500c0d00c0708103403140000110090203600c20340400c0c1403192210440684003210b004e407c0c40682c205101d0314030700320700040c800074031034201c000801c428150700041086040851070f541c4e0180b10f8190502600400c0301d00c40140c029402c00c074488050580000307055004602c6214100f0050781d03503400058544003481c120010880f0454010000f9140301005550889650074403841416603590800ca0640300c207034881000750b00003040c0d483e00d91401c411055404000340201030300828000710014003d181c8040024451a003c903244000e15120782e010707500324003000e401004241c4070465045400a0741c0c00c0c088803401040c44 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 478789478 1250 478788228 478788257
    0xf090a09060e0d020307020d05030f030a0603110301140a11280f14070201120e0f0705040f0506180c1c05010f0501021915090803010923070f03050a11030412 69
    0x340b049903003140d42c4c091402c013240b9070308000b00f0940c0d90000750791610041c0039102000911748000d5000b04801c020000c3d46d10f00d14a8681022400703800c007984240d1401404007015100301242a0f88901d200310001801841000c1504c614007511104441011880d41ca51403016040781c503c0003462440d48035085200780300352040b503000e9094a069062854140601d4006500800c0744001c907001c441c2020501401d41200c65250008107644011143d210040410070f07070800c0e1182c0030100c00c0d100d1050000786400c102064940911141180b5a018680002340301e42c40c000c03043d100043c503070303602c45014050801d84100203840c080c00ba00b20000f0900e0704c009501c2d800090317040d0440740c8401f030000c804400d030746232a071452040009882d001515109003a0000790360720b0066020b08911103001817924101600c0420807012114041803441c2d041080c042c54503084089090f000c0c0c2c1c4c9140101c1d42d42c0e1000015000361041030090f404044011041c0020003240c44001c1460110760354450108a0441 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 478790728 1250 478789478 478789483
    0xb09031906151505040620010c03150915050603061f0e0102070b0a020d0c1b08060f060f03030d1817090102010e0105010b0f18060f030912091503060f090a09060e 71
    0x2840c010700401c038100170404c04140a860484500c0c13503a0034001420380d82c5001081d09464540c9640000291382c0e61112060100a80144000d0300d83c0705402c001c0184000c030b480c5000c049901806110320300200014000303070b807026064600f083e5404a46280c04014110140c8107840f8424081e0150141080110348000b803031042c2d42c1c0c01100d41d402130003015802101074400521281040c1d816240880000002540301003c510041c856200140362901d040424a03010b801c1c00380407141315540c4115461029507001090313a510000c0c80e0307400128003841c10b207420b0000e00701000040132824160012a100c50400001d443d03403000c02c0c1c009109403242030060300e0884200b4000d00010640600c03101404220030805000b040300c800001c60071036004a8006440c542184449403407160340041084100312062201c3c62440354801d2031076090901030000503d81142051410000000200028404d5911501c10f0190304401418110f46820400f0700140601910402a10901c0c00d0080400104000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 478791978 1250 478790728 478790759
    0x90e0c040303030c090806270d08070f030f05070f021c1d03030c011508100908070807020d060603060f1508060c07080d0c030903081f0b0903190615 65
    0x800580925007411035405070b008081c42e0b41008208407203400c0104150108022160141481159460214401c265000c80d019051101511160407000012403441c1d080f00f4141d0b0851000e04003440031400c6840c040f0f0040503061062041941004280301e41e154102c10460348080007507003174524044810460013900184c49004100182004401e070f41241980040c03080800c8008040e03074549400c40c6032060031b5600343c8195466680d02400c0030441c110381040812040600c003001800800420344070002c10b401001005040440c00080c1c1404559503010707104155035100d4010030038140c5909040004180d811a0886014545070b810b0141182e20150402111203950041400d0b50301c07070b80d1040c41608001d8040703c000809211408400141c2e005180041c0710703943e0002005071342401d00a16102001d00240082c50381c041c000d050f14981c080c9000140d0310300c401050f0341c41c410000800d142c40500f40f01c200b045101e2200443c104619900506c50040070180ca40d04419210a000f0100d03001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 478793228 1250 478791978 478791991
    0xb010501082a03070c0503070506010f05150306040f0f0e0703032616051e030a050a180f0804091a03070512030a0e03010603020d0501050414030c12070203070902040e0403090e 77
    0x11002c8a1002100c9100441e0300c44811320780240001d01c1d65a50614540002c0e100721001e410140041c0503da01c04846480200000c4441c040090040c2070010498480178103c00c2c0559103584000064005540041d90b010004241c1040840703c0400255190303c014081200055044842818003010a00c141e03091304404442da0741094485a00b460081c11102d01c404040c807000b44104000250001d190960328241e07020380607a640b911820913821110000c0c8103944640c605104a00c5419641c89800049680901e45100002d0740d400c0c01489406564829504107003824007038106425000800910400160201e416450b111002c202103040000d102043e903a005000715034a161080700007060180010340005900341d142e40104443e042040001d0340ca03a91180240010082c40c424540c1c1941c0c0000013940c1010007501040e6202ca602c000d0042440301d0101c0c0e08000d550f0103200c424000c1c00000300c119a520760383c181e4a0b071090800c4900b903001c24208035001584900014155100e4203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 478794478 1250 478793228 478793281
    0x70f0c0b03090d121109240a020601030302060708010e060f011107121e0b071404080715080907051f021006080f0d030203040309270e0f0f1c0f0216030b01050108 71
    0x345001d001d000c0d180c1314103440325981c42210007c10b84080b0700041a4525695000c1c00f003943c114100685400b401825180411400e00010030601041003801a04507400300d580c9115040208012188a0500511501e060140e581c1c0055980c0a00400e080140d01c2082c04e01d10801e5178045818000d070240402400c9c2c51038403c0003030300e030324031072850165816840d1920b14181600c1d404100c0c5840c1d0681c00028008050880c82c600300ca82080f003041c0e10400c140c1c0200040350606000c180c909039405034281887c200d41825400c000c1c000d000002600340000000c0003810764070850540e481051006218460240e884810301c500d00ca8002c90303100e07a415842d9041028500728861850018004038040a0541080e08100c0701c0d1007405102220311042c0010669501c2410205081c414565031300c000c2e030350140100345128007501080c500090403505000184a179101016424049041d0292401c0344801401004000000c0c05c10707410b842080c0e0f2069643d5881c0540324203444665058200c500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 478795728 1250 478794478 478794487
    0x60b120c01121b39020112020a140318011a040c020d0c0210050c0a11130c0e0d14030d020a0e010527060405130b090a0b06070f0c0b03090d1211 63
    0x4501402200e0510307004420f041002d4214142039100d8480300e81c00516160701c0c590700340c501750760b1321660300000005a40e404502e8270401080241815140310072502d080303040840000c11a54500c104104011a1000244510303803400f00f14001c400912407129200d50719101d2107210b09880040c601c1c082040c181c443e080050010380800140258002100c410408104259001c54006001d1081e80e144a00981c911500540c410401c0000081e0a0245da072480d1051380c94000c3c0c0c2c080c03245070000d88150740084a880d440e003011108140512904007031440300046020a40b40154003d20400d046603561a13106050440110780c6881b42c1281c900d98441c40b001ea200e0411030041020fa1900c100926142c601550740e00403804100d035607190b14030707481d0352899441800e04000411380e50103045800d0803c01c042180000440900500301c0241c40d41c038034520101c0400c0014060704018041d6040d43d50340324a084100d185c0e50714900f0840100003241d42c01d075031000000f6402109162701e01d08034200e041 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 478796978 1250 478795728 478795781
    0x2130b031504060f1424030a172b0f0501030c1512051f050d0206040e09010603020402070b010819020901090e01020706020a0302130e010e04030804060b120c0112 71
    0x50031020b00300b41c070300aa9903203640140300c1c1c491207450101c2c42e039040700c10600c0c9425002c43c0c010801846041d14481c20070140801c0c3d6a80114484046d80da00800001800da41405107103480d00810983c01051242d552a040d0000c40300102004801000b604c140300050040c0b052100343ca070288001019444065400d1100185601c1c942d00b1103106c80c81e04203d9144042240b0301564000d640c8281c01f603c1a442d003542044440715118054071044d58a0b022456032940070440340d11641c4140000344216002280c20340500390482001507400a2040d034136141a801c06035003809083c45a8142407043c96012820210f910382c55880d0a90010401e205681ca0316a1f0300b0045c088200d160a450356080003410001035062000d8440c07a10f6a0390016100c0000c1b00140d404000a0341005001c00002c4004200b400d850320300f030307691056252614100760f80f0740f8503040016140c81360250b5800803011078400c0c2070b40d038001000080b180090341c41c100185d00c5c4100803401c5904030000c682d4601c0303200103840c0350b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 478798228 1250 478796978 478797013
    0x1203090306071124070f1707030216050a0803150d0308180708100212060118031104020702090a140a1505100e0a06030b0a0501050a080f07111902130b03 67
    0x1044003940c02601d0990104c01e5000099400190f0040c07080c0200105000d4855072101640c0d00c44582c0c0c2c10300b1540b10705008091114040024554030801d500022000c00c146007402e0b0f8098011b40c0b10045072a81000c92800c04a5504100c420781502c540c03896481d0007a1800d0b030a061416a05915118108d4a8101291071310300c100f00f615080b81e02c035001c00001c04100c200602140400c0003e0010384815100c14004070801c0058000303410030003014031841041c1d2129035020212a80030411000b01d0300b0031400301d00a07006925001c1c1d8010308200401101c401a038006541801e000040b01c185a620100b044044030080d1590a550155502c014030203400c0c82420641101c0c541d06012541c3c2302032a001400000c503d070409000252184594501d1342400c402010240c0400d08109013482c140d140000c0c000c0d040100000905c0f500c040204000340e0081202c4050354244c04c054a41122590354007044103141c2c2001240601010801c202c1d510700280310341c03440e5080050260070072500028a084 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 478799478 1250 478798228 478798247
    0x11203030b19030b04060b0d0302250504020a050c070602032b0204091811030705090c180a0902041a03040f031101151212020a08031f170c120309030607 67
    0x15081118803402c410585031644080004610a00c02c1c2900c03480d01e89010410b541100d0316290064103483c5803840001c1d00842e5240c44100000c1442d25803c40408a003843e030506940600e810510000d43c881c132240c0d0000c001c01c6120400d6040fa4450707541c0300d004980c5e038411220450481160a59a46200d0018401d190f64059000001608040d02d4a441c402144c020704001e20b43c41c0059502c15080205007040b48040342422005090340a10748000304a11182c0184662080480002c0036070b00546000c280012082000d0035144140d903c41c4d50107c020341c081e004508461800320101f144401c0b448084a10456000c28254039141240d03400f50781c9a606401a00055504e07002e8104a07441d4500c078450003000b0f40d210440104415043ca19000440c65420004641200c1e41c40408070b0400422a43c00c4078010296951010f8502004070461885400c075060000f03072070000b500e084d00c00043d9805045000c543c038860900c4001d90341c03035172031003600d00103074058100c2800501440c4c010111007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 478800728 1250 478799478 478799501
    0x100c050f030a0203100b1920060c03090c09010b1806070f0b1503060f010311010e04050c03090601060f021009020604090507020d030c0e0f060a02250602010b010801120303 75
    0x16824034003103520040c503540040b075510003525400f01c2003044000300d2a2002c80144010703441c0a18181f1a00c01203507034422042e1800003400700600541c40e0307803280c0040c0b0803004032290b015210f40e41030410f260070003903000390f03034a0b03486214024800b44c031894a00942c2c1d04032190340c00c800d850846c180c403401402c260110032031030b80005d0500c03c0c41d022410b441107192807140b00300c0c40500da81ca401d028080b0030661021034240258058001c0209c05d140d40e4504034103682d00010001140015040102e40885140307940a80060600060080ca120907102450003248408181d405907a00c41c8400c5500d80e094880300790040e8400c1c0c3c0b82441e00b50a0703030b103e010503034006000140340c1515005950191601950f40c00016840003007151103240e498800c1a010b00c2d900c1c80d01948484446000441604800721580c0c0f040c2000900400042d008000300001e00850341c2d582000e51061b240d42598002e02445110055402d040b1003424543c45004114140c43c080212000000780c0d94501702d00910702200e40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 478801978 1250 478800728 478800737
    0x70609121a0115020105070c2f0d080415020d0206040602160c0b0c0c010323061216140103020a140d0902090108010f0f0605031207050a170d140603100c 67
    0x1404400c07400907001400382019014000142015680c001d0840b00003c02d00340030001072422440001d0a0240402c00030205240101d0702c160450500300701d0624940c60032584501107400d030800b0462140c002d4000c645810220200b0170381807190a9881ea44400d0510b4016001100084c0004072650702818207640303554400760074078140c0c1ea12030581410790341041c4584c0001040415401d0300c10017003500108000e203428440907032040107042060029000c10341c140c1c4550400521180c440340c0c02080c50030220b004589000a40007000c102302c60003401a8080142c0c58500c1d528a94007074001c481223503042d96035580e21410410049003082d040703500f80c0d80c481626250302c01c01507911080658040c0c8001c2000140328921801500c0440744104103208201d801e12408000c0d0396004515248802184042c943d5148032501d4440d082c868010310003001e40c032405001c503000d10074100180580c1c03000700303204201451a030280f9881ca0f590413a111b5a040c1d00c440200101402e4541164603e42e032503081 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 478803228 1250 478801978 478802003
    0xc0212060f0f1b0706020c01150503070b090d0f060c0207090506010503340e040f181205040b03090c01030b012d0513080604030314010308030f31031107060912 70
    0x10b83c091a03121010a0340c000e900841c580c9502d0000384980c80e200c0c613511518a0810385001d010980f180507520600c51448008a10f070801c50300c5d028001c9403000e51200c0307120070000c0c1760301d00701d4024614000321000500c10a0004680ca10851040740d01429058603540c0c1160f46400150740b000320078250302c44005a0414070190b144240040f44c00c0151004d4a0700c0c800985410b0610044843d50181c3c107521606002c0100262405070102d1709d03850b500440403500002c6440d2040d10300e07100d1503110071403690000040115490300880c0e031545c2c2c850241e03002d2012040110044400111280004070100042d080e0341030045040d443c44010034989042aa0a1404420401081c6195580b01100c5174000e0070030041050707810f2050003481d580006e40e59483d54190f45410302d250000a0455403c181c151001c80d0600c0b40001703068040104498407601d04254141c003546842d851502c0031030104510801242c0d6074240030891005413411680e46c03203081c1c1d00e007040503d000c1e10340100c03d542d05004540d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 478804478 1250 478803228 478803271
    0x120c0308070c05032a010c03050f0a03150306052d0a05250914010c031d01030b06030c090a050312180d0b1015030204060905010309020406150c0212060f0f 68
    0x2240c0200e601c41403046000c048040c0c1a5005c44400a1300604001c4111300b0b100000e6040300560b08580010030500c1d0300c1380b107404415070080c4006158041c4c0071400d150000708003d4950042d500c203076010140d1444069403020700145800811240c148031a0a101c0000c40d814071700d51141d5400b000c0540e0220006542c1c400e02c0e07492003100c3e0020000100d141c40284441803058254452543c1e0a180c900614a070a880090000141d03507400c511034050106110010380c4641c01c40290700e440105607950707a042005603820f080c1c0c00b50498a0107945100c90000c0c9600d008658800c6c8540a00d003050b01e00202414041c0300e04a110b00442d60081c00b000c00100410071400039107200d55003c24098140724109001c41c004560607008120815004110074000d6591101640c3c0032900c081c05c0105941e00c15100190181240b50403014101c030382e42c15129a425404902e00280500945090f0700d245180c903415503d0b0700302140c44010b074440b03d101190074505e41110599000d0003c1139425542600c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 478805728 1250 478804478 478804483
    0x50714030403140d09050c10050406080c131503050a060b09040f1b090501120903090302101707020c0118030804050f060408060c0702090f04051c12110a020106120c0308070c0503 78
    0x4a08403845c2d60f00341c603408002040140c13200868085a14510301101c2c000001c05078455401380b14100040300f8007203188000114217560000f404849003c01c883d8407141c0c4102004001405140085d040102080080c107041c460902640c0c400c64040d860081e4002c103104c0a840e02144400d0500e503194003c02841042e42c082d0718400e100d82c0c0e2110041807138000010003500946a001030110b250040380c40c0000d4000252400300c0e607060780c0c00441c18006400035a210640c1554454490044004010209601040c80c2d6a05403090f00c940c001c01403420349078000440540402002282e00b00420b00181c0b5142e41c1c50b1a2401c0d0041c2160b203040c0e142e001c014207090056810021040c40030074024114500813000c0e0303521040454920f903940c0742c03949601d07070b4850041a90344643c10009000008007440390543e26101c04028005000d100341407030503041c1681c030015444005518010001c0340c004001c1100342d94017500002402049030560310303070070500d82c01200708441c03281403d58009010f0314207 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 478806978 1250 478805728 478805737
    0x70e0702030c1501030203011d0613440c03030a0e2401031e031b02010306150504170619230f0a05100501210914100f05071403040314 59
    0x1064080c1c04e524600c145400e4410036001c03218050075400f502110440002141a804000255090a9241c0c6820b01d255825481003100c400e2560700340030700151135210903041400c1c81c51413640f00c0d04040c642140c1010b0f8016941c40c01c11030381041010910181e0b080d0000b07452040ca02c4240e40380040d0900d038407035202501d01f405007001e03c03006004205110715004000142c81c69504050840c8405e6500240095030504404400410064104040d644030f80d002c4000b5003640400d0802550800001a000d904288240d00400d4243c81c0c4425603c80c01080e00790084220b41e004101805d480c0c4240406000400c10001e402070520022640a020308c1c202c0074011103140c290002981030520103941582e074014207004091003403500c10045079a00030082c0901840d0020014074045a0003410000740070511800b81004143c8220880450004a40000c1c031007007980080010b14808a5000d09841040302c0c600041000c11905d15003603a051001580d115100e1725200c06605a443c0c07a840c80b0b60403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 478808228 1250 478806978 478807003
    0x3010e07120c05030403230406020a200a1505190c200f0103090f060504030806010f0305040302060a23042609060f07080d020a05031e060102070e0702030c 68
    0x901000380416140c0249a0100d607400524042c0451015850060b00030f11001e0001010400402031010314594445070a08081c840081030540e07403a507648000355640c1034040180c986000503506511305800070450120007000150011108a00d031500024501e0110070541c1d080c032504008003401c0141903840540c2d1261380e619007624146440c2400e1a8224040c40b90705081503800e00302400c0d40d80c1d648046c5201140034600072811100d1894020310201460074002d082504041c00d0004040c0c01510345c034810407080e030320203080d044d140f40e084040e207005a80180158000d9008504006e94541020001040d8002110f51016800c02005d49011040307506803105d1407012844107602e000b0f540c0c5000c2651380503400782d0030b094400d0002111803045941894074a00000780c080200309034803043da80000b6080104640b104a00c450141180e4002c03120702d03007402c41e0f4407044c10b0044a03102940b4002d40040c2c0c02040507034140201c60704a800082e000360154403062002c11a04c07403042120004a52 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 478809478 1250 478808228 478808249
    0xf061d0d090e0906040309050405060f0406090f050c03010303090e040f140d121104090f06031a010810110304030e01140c07030506071103191709010b0901050f0f01230301 75
    0x2898103550b56800701002d0060000c0350403180600002c83e500549031002d54601f00c500048a03202c10b00080c00c0c0b80222000b058125061510005800e00c15920144c56962141d0003405165201c402d890000d03c000d0200501140440c50184041f06c5650300710380d4018170900200c4969082c5840e07036800856224032a8889a0010344100c0800742d000303445240b00820400180300b101100c3d103000600d401680150202142e40b4050709a85d86c000340c01a800075a0801480010082400542e43e0000d00900494941d03100741c8410f080b00c0b00d00c6219004071700c4040b103070680c05e686844d03030100c41c1007000c6007031241004080c40348242d035400c2c88001840d0041e404402804180c1c6549440c90403c20010000070a01131101044101d41c8008003c03184408449102000e031401c022009403030b18041410b2000b6511540010001850741c15480403c3c000300841b000541d60380d84508101c050b040b03921040350000030203409200c2950180c0798803140500c010f00045005d1039441941030031a002603001e4042103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 478810728 1250 478809478 478809497
    0xb0a1a030c0708040e0f07110601121401020d1104090605010c150f0e03030c0901170c070311010e0a30050d02070c051503160c0317090c03010e030406090e040f061d0d 73
    0x81d040b114801c440329400300030b442a5890715502f20321004000401401d003418100c000e00b00359200f94102c0d010350b803640104100116460107054081e82090082c901c40e1860200045103560044d403102090030b5000144020480c0004500ca000e440024840c400301605c0345c4200603070a00a1018500c100d0501a409840c1d0a80c1e0000500e020f50300f480610b01801603030107201001c01c1d110100c5240e650141800b60a0420740301c0213900510391580c02c40c0c0540103524042042005800c4250241c001041e45500d0030601d800d100c045240d003c20444c008514108a4034003540000d801601441c2e0240310158142a50b400104a1a0710401c000c100c19030340000402a4049907800303080007181c0a45054900c0d003015503000751800340c1e00c020041c407079a80080011064841002003050001c1d024009011010641d46880e55a07042030082d4004540c10700c0e00031601095524840c0e10507074009104840c04000c40d10740d5001002c40c400002c1a95031110091590b8840c1004950756042d815529081c19 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 478811978 1250 478810728 478810741
    0x1020c010501030821010f03080304050a0c03050313061d010e0a0b0d0e0d09121506030f05060103050f030c03090927070e060405070e01030e0c130b0a1a030c0708040e0f 74
    0x40000f04415403000080540042c0101080d680031f8000f41c031f9200006542e241c41e58205107140100704040100326805010700401000300210103850400d500c1041041e8558440d20250b6400c402d642c52030780c0c04030180c43d0402066103e0140b2001070300b4080c0155511740c0d1200540b14850b4849250161116200c0d1014000e01d0030401030842006454544000305a0601854100340744800c0400381000341c051240344240d00340e5510490003180d001c510410014098076005031240e00920041e120750103000329100e410b0300c01004031141d100c1c050300618035184200c001c00800d150040c01494149c12080b80800e080ca1621080e0a921100080148156468441038240000303000b410705e4001c5080c1820700c01d5058100d20307d01440344090902007a0a8a40c04010b868601c1000565620100c0c00c074000489043c00d034050102942c05540000341c407511807861200b80b1204001c00d00d1580e40410018591141500c05089550b1080d050385151603039640201c0a1f400040d203074034420725500801c1c03001c0c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 478813228 1250 478811978 478812007
    0xc2102010b15040609061d060414030c033f160b060102120313050a02100f17100b0d110d0b030c040e0c04020c0a080c0703030f0908120c01020c0105010308 68
    0x311006114882d4a001d04069008114400c2c0d4429401401802010710b034a000310024012040341c0007074a5652076135038070b00c10385150390255002113019004400642070740f810081504009807118007800c000000c078440b00100800001141c01310f8842c0c070800031210804444000b440c01c0030092804581000d01400c003c012410f01502c04e07415580301e0640e04100740c890409995000f003101030743e00039040e40382c1013a0f414142270070307402588601c0d10f41c605206c90340c00817103804039002c00d03990703c0c42d10348804914400d08600c20348420815010607501008060180e200510080c040c1003c04070b070b0710307403203007000c14054210b070150390780342c0c0d40b0b903408000281420400c141c01400700f01c50501c0f140700a44041c80d00e9092101d801c500542e00044c801000450030000400d00c65401080c2e0b5640d20710910740b1588803145030100b00e00040001d046840018841c00b118400c0c2c8020b1000b410540c0f1401b50a9070050340404400082ca540911060840311028800d1364000d50144420b16950740c5031800300700 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 478814478 1250 478813228 478813249
    0x90106030515041805060a050117010e10090302190b1501020c0a0501110a0b04121103210717100608060612060402071407090b040b0604060f0c2102010b 67
    0x182054034000400c070881003000070200d086401580c000030100180005064040a4410042c1c00c9104601c2880702c0e060895116504035003040050000d0414400c603000e0076500002d01d403190603407000e01c102c20502e18561204e0417061290040301c0e400d00d860151001c1110701d416003501d928005104010480b021041d1000030114244081c1464209400000e407100d071580c00750b24100143d521124002100420940000580141164045190524180c0c1030042128101000a01680740c07000c07003032500101ba99503034080044a9030b560a030541c9075807520740000b0440b4080120b24580b001c03c00c400680c00c1809542204c018800b00c5040000141c904d01006d06141c0c001d00d020840b034400c540c44d103040f00350461030880340035076200c4246c14100da0b81026044588074500458100050f0061551702c00a0844010794090010241080c2007001e2401a4480d1001295040b0b1410500c588030701c1c24500c95a00c1b5001d2144800803a82501c1a1050701e441080c0c0540c1d5504060080c6291108484 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 478815728 1250 478814478 478814489
    0x3050a021501051c0302010e0f0304180c08010308030a0609090b07080f31021002030c06060a03020a0b07030c081803120a052719031406060603160207050a12020901 72
    0x1e03205503d403601150380040764002e0711901821003000102054803e401201c40200101d04540303c1c502d81e542e1654881e40280705107080380c840c4c0201c0607261280d60040352409040c40d129144680c0c610346800b41640d0004014010f4503988580204041115104e218505400b8000d9013586141c501c2300a00600c20207420460720304215420080407840790041c1c0d60030601003001c50b90121290504800c4071142d0064020b602486e030a40b90351500b079002011704044500001203c026499184c203010204020340800f0f50054101c41c424001d000d0720704014410b0900c2440c00c80c00c0590035441ea10b14607004407000004100401e0740d0400149001c03c00d0030fa021207482841e5162503402c0d40d01500323900c42c1f500000d2048401400c8003100741622908824034000181141c603200707c40c0030f19681d90712050702044800d030300305a10075040c0300c0f00001c541e4170900c00503207c6841c0d40c80c1c1c4002200b0a483c0b80c8408801c41c0316003400815542c803000c2450f402080f11030302c00a00c0035490300c100300507110140c021 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 478816978 1250 478815728 478815763
    0x9010b0f07240f1e09022103071e0201020a0201050a0c0606030804090b0913032007060206100605070f0b060d1a01050906010503100b0702060706020a080a0e0313050f06120403050a02 80
    0x402c0b1400121030007009106144c00203601401071000c10030b840543c0c608180f0a00c1a580111003000d4080001c2064522841412001c5440401e5031104500804400ba005a11810101005500031002007030000b000307080c03058501316269285015170310b15810440d844000231a0400030085240903000c5158401c0300c006105107455032801740002d001301006410042c00403600d2108200c41f0828021301c0700d4000549102544590029645400a4640c0c40c7d000540f040001020b520407010b41700c0d2964440d0101001800720384500749041005400390398440ca11002c0680021500c021f2516841c1842c91070604640c585010448500001805207061100c1001086a84004040a102a9180c030701542d62200600d0010440c2405080b100034815480000c0e1100b40c943c0190f80307a07208101412040c0041d00420082c15140c2c0a44003a2409406030140c060019140070112800e100101405003400e10804450401c000d80c002e8909030040344002924881d0340f40c1c1030044010080c0c07680c51 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 478818228 1250 478816978 478816991
    0x171f06030b060907090e1003120f1d0105040510080a060509010b04030b07020309100c051e031b1c0909050f01060804031214010807061101050609010b0f07240f 70
    0x4401800c007070014960351084146000050002e4045c3e18003402405000105141070f103000344000c2d204c02c01d40e02003620249142da00314055a48142030b44a600396030780e41c40000340b41c8a00c1e55a6400c603200f06009042c8002800040b40540b100c10800040b060383e42e0f10060182005001c0c0001c032801d07078100c240a40d002100600a00c4405811a0b044a901c48603000d0540d44004040f815401071882041d8401c5425161220583d4000c1d829403c1c0c0740907030156030000d001c0d04000c074100b0400c01888095500300b0b10802440300340030b00703050a01c842d0347c00c241c1d20300030650b03c25103140007915064207022940d60300d010300100002c0d1081720381c000b00b83d10000f1415414214050301036a0000c000600300944544050040449900800422291200b084c101540c60b100c2e09a16140342c0c0c041c140000310000c900003400350050044e540134602c081c180c480c05908200f6103240941c007030000716400207401c000203c0018184000303100130903121410f0442c600303c206401e8003600c041c070100c0c03800c5a04080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 478819478 1250 478818228 478818233
    0x10204060905041104030b0a150b07050c0d11040e030f040603060e070e010e04020d0b100509120a020d030810030c08101d100f0617300301051306171f0603 68
    0x1800c44040c1e9070090032103007652307981190035000b90000310f014030084a6025000210a2001000303002034078421410b0341c1c00396800600707104890304034200160082c0c030504003c5100d0309280d8842d075501c245070340c2a2481c04000040c4000650f115500c1600040e07a15141001000001a0595042800e601e070041400307403a40d0000303111070075403003201d84240e9000400c1209180260300c040f600761005000c581d03c001341d010000d005034000b8007003903000300c51b1908000308000c00812400d4503142d004100b6442200c41d81c40450301600700400b9040a0b0030840c01c040007080c071500100c0c0040414900500400c2c060740303541c1051740c1c10701074550315501c0580d14100301a00082080c000070f8414a2000500c4030148175164094601503016440e5801010071410300c0c507501203040c2c21b10044415543d66501d0f5012003401e403075421003400f1a0f00c050140300510052401642102d504034000c0400b050150711078540d011400310101070541d40c2d40c08418040108582601404d5035003914841c200300841c03468 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 478820728 1250 478819478 478819511
    0x2906010c1212061211010f05040308042c04050a1b14360420060307031a21010c090602030406180806010b1b030406050d0f1d01020406090504 62
    0x5808061102c01440481d441c001940010300810320003548222003140c42c01d00301d01e0f095802c408680001d41d102c1d0b0210b00c240c042d0301210222544103107403901e0300d840c0030402280c074510100948020340d11900125980c0303004070305250080c0d0180c00604540c01003850004800c030043d2454100c02400310700c0807c0850501e2001e000d04100958480079040310312404010f02d4900b90910450143d0318950a405900012150501c034510450b48110006210b9946212483d078a808c0c055000100b000082c01c214421340108415062003030048030300061000000d03150154152005026148408417008a43c03000d016084c107400b680d091051300345007801402510b91141c0d025000501200201c45003003640d064020304010103403e4182c40043d6115a80341207194020720314444003070403685400c02800f10200841c0c08880707468469074034103124015a4406081c1e41c1c200c0146103582e40c45421050010050148482d05c4403000059443e4207007040603040051a4000500847c13074a003420360328040b407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 478821978 1250 478820728 478820753
    0xe0901060c111e0901240c140712031b03091a0706020d020a09090b01080f09010212092508151b07030509040b0102191e2906010c 57
    0x80e00c0c020340402000e0a2903850b00301402085500200c0a00d40003580d480501d443d10030100781100c000c0400d0340ea400c0c1c4d8a00710b1a194001da50119014580040c44074040c12961110384d11400305410020200d01caa2800d1800c1540410f241015040541003011b40c40680c851302203000180081034408103440c010070f074200a007d17400a020741202c00c07001841e0000c0c00d80d040554419015503680c0d4519442c0f00280d000b052298021502c0d401740440c10251600410405000c183d403904455503a0800203202d021024104600556080104260441490710003d1284589000920a41420105c800b40c40b0010101e108240c0000c40424045035002040c58031850078281a8480300c0d07140d10500ba903449040c078080c009444800100d0313000305900302c4050014038004407810800d15900382e006a0f11205454206120003040559140006641080b0840e1400e00481e0302a44071410b0390720030600703104c08ad002c144c0f40300b03008190454004180719020781c0b0090031f291400c030808041d600c401c0320030070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 478823228 1250 478821978 478821989
    0x60308030417030f0c0c010f020c010b03061015030c030f05100609050a0501020318010513120501060b0a0f0f030e010207080408010e030a1d0d0b010b130603020c150c31060e0901 78
    0x17030000d0500900c12094100351201c04500c5030465a840300d05071014000c1c04050020b03030003030003148000b90040d80c0181da820211603216145113014001034404400402058140105041d40c4840380450042148180c91040e04009110f800450070098080d1103c2d102e43d1040e4802c02900d5030500c91640d010003900e03107402011024010030314070400161035500495201300484105401d00051415214079920030850141c00208242030b03c40c1d008404034414102024041240219522602485442c0c0205440514070380081d040c8916403500c4d0076a40f040030182c4030b0110105050103841000e118040082d0f40c031500035807038405840000740c40c5040d4a90985002e40c4114040700b550b07103443c40c139041c1c1190f010030340021541c3c5901c0d07005000c1d00058521070140125800200e61140244201c80c2c0c40d11101005281c0310340b081c021413049160040a103503078828140031410800240460001401840307200109401c6055800e40c0c07080760150340400100610041c0e1210075031a004074040c19100c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 478824478 1250 478823228 478823251
    0x13090216150b09040c090f020a090608100803031302011202070c0303111002030703140f06032d010216050f060601080606030402011b0809010e09190b1201060308030417030f 76
    0x101c41d110650020003401c00d11940010a201c20003041101e510804002d5407100d07942040120faa00c2900c904900451a0344408151030400a10a05008003042a40300840d01c00e4010003030b48503036105045400503a1202c106201c142c5c40c01c411907801040340c540c0003035500021800d2840544980d0b607055410b1001500788041895000b0fa00c0c072092007103044450004009550700d00b00711800034020192880000505610080401c038100c00c40e4020754003a89000303004045141000450314000c8400c4880100d00510001800c00a51020300150080d282c000c0211003040806080c03c608140c80c0169400701c5401031010800d0a0b03030400420343d00000152480c1d41c41341d40c3e40c0b0068807081318071003401c003e01d501c011100d810044407500902a00500380c5c4c0700280440d00c24140044520150f45103000c0510101d46001003000b1540a1590618010605210003682d14116401c507607603a00103a4042c0c7c000000c000600891041442c0b034883e21075061461840c048050000b078200c040c10225006 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 478825728 1250 478824478 478824503
    0x90603040c080d050a11010507080a0509070e09031e03130f02040902090f010302040606090503030306040c020c06190905090118150b120105034c020a02010213090216 73
    0x8160550648040c207032107000c031008942443d002900715049485ca01e000200c18003980c01003124103018150050743e00f070301c0d91150340d1a2241481c0c040c0000070f00c800c2552044081c001000c208203a40c19014440c071801542c0e841e21503400c03401180003502d6411440c100c0801c00d000f0200101c080000045401c1406120144a10f10009005d450311140c042d50003806402880000c0c601156100c0c1264401ca8041103400d0b500d4100396a40340c0f803071158681c035810500000e402d80c1042e4205150649041c410b50713030302d10740d130400181c100c1d080401040d810040c412103e44036284c1040084004d132038116074a582d150316140e0003611110002000d443c2c1036403108031200140f84a880110f01a080125540c0d80380d859025000d0716442c404d11a0070f1281c440c0300103c0071060454242d4420106030070150082185000e0b010356002c82c2c143c4501141102c009025034074900c810b201400f1880950384c000350f901d416694503091b03503071107981080e1080f520401c0341d106503140e104000c0410a501480f06c0520 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 478826978 1250 478825728 478825733
    0x2010c02070e0c0d06171605060f030603030910050a020f0a0f020111010e0105070c051510050d1104050a0e01150612150b040f180209030303150f040f0b010f0c0809060304 75
    0x10781c044d0b0031030b0140365400c2080104500b000c0302401030200c905031085840c070000e40054038030202c4491040e207800c8030042044808c6070010000960b8041d5001e8116450a04510041a00348502d261004002007000c80c007000b045174144564092100340c00014403596040c1d855040c100040c482c00241489804166800400d00c02e40003040101c0307100f0002c10982c80e201c54003604cac800d488241102d041c003c0307480d484412074040c00900c1c000d41c54480c404035418244000c0c048909940c000c191540c1c460101d000c10665914040d162190440c5000828100c992007100c9096424171803461440f41c014040074040c855200041103442c207007114002c90b0000c081681c1400401040e00502d441c1c250020380410117550b80d1503017070101c8205850b004000c07034200c0c06510881c02a10101341d81a0420030200300b0341d20034100744100c8040e00900019540c6242c81c00103044a119420342881d258492107141e40399a00540703c143d00408908160f4038800301c0780ea40c030712540321740c40e0413600ca400044003240c113 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 478828228 1250 478826978 478827001
    0x30103051002181905011119060c1b0c09060e07080a0c0306030b042a0803300405010b09011d1617040317061815011b060e0c0102010c02070e 62
    0x982c0d0340c018151070010958021078002800b545d000b0703e4007150201c8040030302c0d03110000d6042074055052a8600e40f000d030a0742c5210242c04103010b00c1d003c01000c0d50716894900c507911008200c540c46a8000c121503440c02002506445180d0700001c009940130301003004403500303e901c160380301c4028040018003419a11058000701181e0304003038415400f880410041098100360f00c5082035401c1200701c25010004084900081c3c0c900030f503070301508148484000c000f403180c00740100d4000303a0340385ca0841007440201c000b880411201660313a81e45030085c0e0f60700da0400702c1c00305002d82603803603a5120700a6a1207000d10810750240106220810350200c407800c02d446800c600c4200c1ca09000c4c8010389041904000700f80452041043c6200040761000c21690b1802601070700c0c040005104550059841c00c5281d00c09a420941c45030520194404520341c1c221b102d0b003261402840b46000007901000040c0c01407400c5c408a600505680c075100b184042682c00041e50300032503048110b5103050365a540311518 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 478829478 1250 478828228 478828267
    0x5160f0f0c0627020a05030c0616030509060c0d120b06040b0d0b030d050301210b0c03060a030507080a060f09050a0f050c0a2409061d01021e0703021203030103051002 73
    0x90f111940038104a50610314980700301520b90003103071040906919a0100760710f40031108001da134414003c1040c900850651201c03544c4840c064241141440e142d40b0100d035456000c0c007241100c0e600b01141c440c070b0a6401c0031f009900120501d5080110300d5141010412610440c05007000f118404180d01c6006082900403e0644001405940b1020070000c0301600030b800a02500c0c1120303a59007009107a00000071f0703281e0030300c0b50451f41c5404151228451351506a002401c031913049002c440010001c00d00400c0780700010000d41000308458220f0341844c9048440c0e49901d142154203003254600400c80004515090340c1d040ba40c43e806102c040d241c11803070b10200110389074109a40890000c0d00d003c0b110104614041f6400c002611401203d82c00c44050155000d24008105a4550300e0010040d80103000340070034040c011a210748162441c1000c02110710140d001c101e40c011602802141443d81480c038425242100450940d41169582500e078001d078142402a030340d001c5034800e4440190700900 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 478830728 1250 478829478 478829501
    0x15070309051c0309020a0801020a0807030b1f0504150e1014040f0b0304151401060807120501082808040501210f050a05130b040f060213060305160f0f0c06 68
    0x3440140030b24071019001c2c1c00044800e920900d502030001030382d20418001c480c01c40c0b0850b070f038440099803074081c180c004048442590707401c61840503000d800c0041d00c803035201621000e80c451175140c500d00104c060228451942110821922030800f081a80710a61081c1c02c54080e82042000c03095030b208858a1030045a120f060302011241b40011641903100003140510f00410022070445900ca100d90f00b03840b09070541c52610103111004000d0184a101d8803034103e403070341c030301102001c0e0495180000c1d03071800c1c2c1082c05a6041600078203520540a0f8008101040e0520b0311a4422a2074941c81d6685c05640302e06d81c140040410711403040141043c00b4a17100d465500304101c0340d01d00300f404000824045500403001450180400c2c0d0b42c01d10041512511a800707049040d1a0f80c035680d94030090040000116a902e400340000c40060401e045c046001d0070341036400280074603104600c6008183d54420003c24807541090284000798030030440100a501030410444800741490414003e0000380d140 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 478831978 1250 478830728 478830763
    0x20a0e0c0c120a18050f1201061724070503070e0a030f1a0f060310020d020d050f07080105040606050d0504051c021e070501020a030c05101508010e1507030905 70
    0x22a00b010a50406440b400b1140d42e10b034281891342c410a2921903850303000b540d60250400e40700585030b02c2c0034820081c40c00284030003c10481e6a40001602e60514482199941e07000042c51082000602d114031189c4d80108030302c110035003002c01d8040d103a07120180c60403081220009a440e0583ca540701c8540c021603000c0b070340c42c000440303504150080348004050100c0a56454020816002900c04000d018400007400381114514061001009500c031058030002103030240410b850081091090900c82c07281510a89104c0c03400c4500140b1758203058000600c03440c030b0101c2c14403a25601009440e86951035410000d2661694240035207440500c0d180b69003040c00c104070420b521a80400c26803003240484c550106090741c151101c1d5110001d034001d1a005a100060510200348030710340247e0903d0061701500c0340161800c41441c2569400c200d14880c06841540400c02450709204003507000800720090152800c11040b80f9220440203800c1000309502c480003202400317000d1003884011156402c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 478833228 1250 478831978 478831993
    0xf1104051c0f0516060f020c100f1803050616021203150d02040f0b01020709060803030a02030705070b1608090d2f0118110307030f080f0c0607080f060409020a0e0c0c 73
    0x14a901100d4140c00f4201c00104015140001c0f1b500001d009241e149009000c481e0b40c42c0e01b0b2208403204444080b40800308070100044041099034110040003450060018001900d05100c05a000c40031a69401007103512450344581c0c5c110503401035907002008500e42d82e20761903100700000e00c41740748040c0180d4483e10b0203022100c441c000da8044440b007203003a003c0d1030b9820345e82c1101b00304603a110b00c100c0d030380380d0010400103014000f0340e8010340e4004280d041082c11f0070708648400084d030b001116003000c010300d80c2d42c9201d00c207904480d9059000e00300e50010a40c2a85854004190f0f003240315141f6003070100520020782c0703440d08140c200e10340a0000000c002c84110060040381410700c0050a550301d641d204150052400d010400340192508105010101d080031350710400280e021150070148084140802c5980b100240051802220680d943c3c41007400d100c0c00702c0d0a0315001405141c0318900e0202d034100162070742246036080312901814002d550b03880e2a029410f0384508003d181c846d025946 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 478834478 1250 478833228 478833253
    0x1b2f010e070509061909020a2a06110c030703080414160e060a0e071b29220201030b0d0f0503031008010506130f060e0a0f1104051c0f05 60
    0xd030801100c40c100e400103d503031601c50520000f030f00742c040b140c012410804410b00c04528150010071500e400f501e80f60711841300d44c0c810210010300e1414035405614200791000705211050149400700d5241c2c0030701e24903080c91400d80070350fa881040e50060500240303500240511813514010040c90f860f0f4025203428441e10102c030034460034680640e0444207000408254241007100782c00c3c0c1940d100d0561900607441e8110103860000e081940030740c0d04129090b4010004580c4e4a0124400c25250798048a1000401d130316003d080000f0150850b002c07884d41c562822003449414506220740a00f000a9070602203401b00c1e49102044a01402c403003c420300f8003040010000046204035100150f0390111521030218030b0a036082034404543c890502c86100f10207608a134031001500b070241038005161b80e5901007601c04640106c4141041d540c1e5400a420f1141c03d078003400451501d010704c80391400703080000159180c0305900c0c0340e1840c64071400d09801005008801c21840c1c0d50010b040321922403114 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 478835728 1250 478834478 478834483
    0x4150c11040e01060f150207290d0e0c0103200a0917030406020d0504050108042a0806070306080a02131e140411030c0d030f02070b04090905011b2f010e 67
    0x1d1042071110300e40c8000001d10b041100001042411b0260b002e458814a00690103000090b030905c80c20402801c0015011411212001868104c2d03000f080415609100b51400c0c3c1000711101d40141854240841e0120500303403860707010460918044207030b4451050040480c0c2c80740e0035410803080074410840c0468a5040000503108030342c010f5007113600d07041800008072954091440703480c0c0401c20071000318002682c038045240307600071203980c180d03544003446c03200b05c3c60340c4a681d000d50001d0300083d00344465281d250003020080d002090013480c3c5608241e0108225040c00c0320765051484d642d08a81214540040c41c02d198407100c1c0d101844403500054444800e2981590101d401180300c41c07280c2450304011912824040c1c00818411100c081900c0554040d5a542c4404046000742c000103d0700802020280020b4880c2404c0018000c400307180c880d00b1500161401d4560064a580428120b5480320403044500c0c003042091801c0346440100c56407442c9000c001014550130030380781c50f4450b41d00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 478836978 1250 478835728 478835741
    0x1812040306060f12050d200303150a0602010e032203020603010303050a0e0405070e09190c02070302030d05041a0a0302040e010315050705030702030706023103060c0504150c11040e01 80
    0x3c01d4a040c1502d50780c1a078442d06401460b40102660001b07080d011415000b00e86080305000307003211300c081c1001f40100090459104991864000c004000c0300d080074181074020381e0251580b40000c121600700034050701d0ba41c0c000c28408807401c100036000909e4250841c40d03070400940d070240c6019101c0d610f82c03a01600d15007000b2000070020320141c010260303c0c9407a000c0c503401201e041d04c4005078400618144045000c00510b420001d41c19130300c40d03940d2441d103031007205035000b060f6001e020b2541c01c42c8100341c105942441403c0402c0307400e000c103011080c4441d0b4182e10040f030604002c2d07a50604504150080c0c0165802040c00d0f1404000003c1804080c2000440d80124400100b00c1d5980c0c0c110151654002641c240005900600c0000001a9141d00800942c40132039110001607403501c14901158842c0b91684c0032885c1210b9040040003130500602d0160107150034141e00742410407a280c401032200c0b2041408010390003100740c0a00426051030910b018010b0800d008040d55080928003030b001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 478838228 1250 478836978 478836989
    0x8060108011505130207020123070209060315010510030f060605090f01140d18050703050d0810030807060245010903020915120a050114130308181204030606 69
    0xc01101c0090041c0902c042e9082c1c0d41d000f0b007074035264480c0200d0300c2c00a400c0762100300d0620060601c08211800850806200210340c1000d01d0f80d00d071014418481c00300340282005020703501c1804401c0d25000c22a01d2641540c006907800e00b040f8101d0b070342c218003070442805881c5107180303842d40114803107500c1401001082c4055520710360081002c0011074901c08504041c80400005001252021180d03030010f002c1c00c02010b20040040c60035131180c80c240300c4103134030483e000c0d44120141c00849030440680c1d68041c044000544401c0c1c40c68407210010700c00c1d41402405280d00052100c12440b091035903101c80f1200755002140c260740d0f20388017a040c1c20060303420003540c2c8020711403000d41d600c201561300580e640035180d030b8419160f00c15086011007110110684c003808413192100b501e0020170454600600510022a240210005503000080080c140000d851001510480401d402031074143c1c0003019011021990490207541c182024078480b030015034450700160020502c81c0303c0c7c12805c00d40c0d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 478839478 1250 478838228 478838231
    0x109141e0a03030b220c0905010f20010e0627060903040e06120d08090f0c1507060219120f050f070f140406031a190b13210501060b090d0209150306010806010801 71
    0x180c2300c10056801c0a004012a000903005000100311100c10380380c41452400b001d40045200c040c1880c0050821100700e1b507404030b0003285846da02c4000845040400b42c018110040c1c40c0a080401c80103071280b24600031184015007190100c0d1640c0c803500c00c50718607a2852001d0304c1d091038001c0d40040c245d4006030b43e01c0000703203c2c07200e0070703801080c0108075840d006000030002c60300110024000380c20364200304826646a0360070700880e444422441c210600600c501da03625800400781d45504002c4612030740b441c08402e8a8801000303d10311113045907603001031090034040221000041b080752034203400321001d10461000326000690940641145840b401120940001d01c0000c4041c80340da001c0c1111800c1d411100e044040000401c00c3c1c0080884207a61400c040030b03d5144c840801e0815200c010750201161341c0007600051000c20722a11005c1c002041035035251101c030000080304100030050180c41407441d440170400803910860140c0d544a00a01610440d6941e04005502c2d102e0074802c103001c65 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 478840728 1250 478839478 478839497
    0x30803090d17011409060301090b01121b1202010e12011d011a0d152903060709030309051005070b0a0c020d0203030402100518030109141e0a03030b220c 67
    0x201c1804a4141d401e00103504d0312004400301000052580908140c1d015541d8074040c1d0082000090782134043e00314103240c4502c8095500d013818010f012400e9041c00c0100c42c0c80c09000190382d070b4444528160b024601100c0c0d035010000040e10004071144180065071070100c1c0295400501881c1500603840800208a60118007800e402c4c0c0b45400b48421358407259014805000071050440c0d01110382d0135400c00682c0800c2e1000c405200d10812024150645440340720750450314080102560001e000d00d407a24003240b03550740241c0400c001d4000c85214038007154000304454030841c02e45500942155043c13280e41000702104000307261134541880107008940100401070b0002007100e0155601511a11030b0301c0101004481c10341022280c0500429181e0745402e039942e0900610040c03900400000c680d10f140d04030396070700e41551020b19003005103644000c807481c0c0c403001c01e81d0343c4680c1e058140072440096039000102148680c124103100c50a18004114084200d98841e80310010f250f201c840c2c4c513 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 478841978 1250 478840728 478840757
    0xc0c130c032901111c020a02090c1c1806060902091503040f0b040204060810150f06051b031e0316050306030c15041502060906010f050901060f09030803090d 69
    0xd0700309600d0000340010060241d621907512594608250310403020544481c117190605007109074145c0801c0f100140e00600280c41540307860540780303030060350740c1d0380c1e540c07400054030004010a00c2c03c46826102d250340798200c2c440804c9580428a0b01507100c14104041501c580f09100250840a00fa0307004034801e042c03005c40d64450314102c0380aa47c0004180d0025280e9540355600f0782c00042040b6041502c510000038440c50800041d1103081140101250100c46000d8100600341c495104c4071699100d65000c004503500841100c0160f50b43c3c0c0008040d4524900d031951440c0714113101b501c0d480c1c0240a01a81d55004000690b0180f604613100f42c0300d406072400c048030240810b50b640d59044d00b11211610640c54100c40c01c42c1001024007044d82403d0b40c030b40d5180c0d00d5950401e114005038109000b0421152000d202442c00750449d40310110031941040c0100704105814000d0001b8480f0159a11540c6802042014015540b01410680ea0f2804c1400d042e25904080304032004183c18807050100b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 478843228 1250 478841978 478842011
    0xc070e0a060806220602090607060218031b04021b0624041103150a030605070323010f03200a0609030302011a0306070e12031209100c0f050c0c130c03 66
    0x4003580d2280c204103200c280c84c40310300c09035a43c0080320010f50800c110046525040c002e48002801013000684456500849100c40d0824500103032083c1c110310260700791150304846101c201d0328259401a01c560f07a1050360400b15a48406040710f522601003040000e40c0910303180d840301401000b588540c42c890105100a43e6040100c01e1040c060900005503400440c4100d2541a0b00c001c14981d01181e86e40c0711002120000d8550000081c0c490354a444510f89403044110101c1c01c0b281080d18540c904007062488410600004003030040245803600c441d01c220050421002e4010610710038540e8030f08010f0041041480300f01d002d942400440c01d4000101e4020341003a01010b0301401c0550f440c4941221035014000e41d90303074481d5241c001c428800000b040501014000303005030030814103000c04014500400701514018031b50030b00c00c401c02031a034400400f019900e0036081850f15103040219003410700c01400c04040d00503d262460082c18040e03900518101410b54070100410341242204a4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 478844478 1250 478843228 478843231
    0x50c01120e030a0509040f1401140306010b0901030e07030b1306050a0203040309140406180e0f0622230c0123040b0304020a031406150103091e080c070e0a060806 71
    0x1c0d03042408409002c6009500030300d1121802070002540c17800748000d174800c58408039503d20603510700c20014048070510007604040803504a0040c4825031600401045500c14078640504254907070329190b10444040080c000619407020740e903065403514031241e504903400200199802c500701408908020039501c202e90050b030301669020f19150070440c641c1d040029101e540398000c0d60740d20b80010aa0b000c600c500c40e0311004a0004070f20050303489140b610704008003184003120b421240030b00c40100d010390304d4500d410007039a48101280d0200c5c1016030b04601007030360300b9044e13a203e42c04081031807002040303a0303046031000d80311409011540d00d0480c034004d000030074904021038104014410800785030091036210f48003c0100c081ca0703490b85d0314900361400c10020030000750b02134018048058180d00400c0c542e20803c4c41c04016910040d1a05003101c070352001d1014104c0d0b00088007100303101d07101d01290401020310041700d1000b80d45818090428000310b60f200072840c60040c4c003181d100404a82a03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 478845728 1250 478844478 478844501
    0x50a1b0509040f060c020f24010f0b0706050604140405160e060d030305130606080a03081b120a0b06180f040203010312080c07021c0201170702031602030106050a03050c0112 76
    0x18906014291384c1c610003002c0241d0142c0552158540002d01a0741c10080c1c12880c074200301080808102052000700701c1c50341a0050b45001413009000c4c00b4441071070303007600e4a1640040d400701d481d0300c4060100700201013030b542c4000106800c80822003407190014504100010300110011010782d0f400800580310b0050b101e059010b01d02100b0440828441d4028035005405903c55a04441c55070b902e02044861650003040d580d00500140e07014141c200103030340d5010b2804001c185040900884000240c03003400301e03001548109030003040c0c0c062039a0b07000001148014007103a5a0303116072403030b0404d41c41c0b00d04120340c8608104c1b060040681001d000b50f83c1281d80c803034442c0c240d0303990840d8240e503030420007429414140c03014440d031005696902106000c0000050100904c607a081c00010000c95903020041d80081c1110184800ba980c00811101000304d00c81102d00c507030200d07200090141125500c290352000c0c5625021040c441c01040a542d410b1742620b460100c50540081d000981c0c6501442 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 478846978 1250 478845728 478845743
    0x611102a0e0d03110706050a02100207050c09040602130b12160216090204140102010b030703170c160503010c080906060919150512031e0d09050a1b050904 68
    0x211148500c000009512440e00d81400740140c024003000c00c0b102d0003101c03403e0b00003a002d0340884284460070700170358024060528006141514204021f036840c50446014031a06900084603014000180012401840d00078050109400d081c2071501c081d40001d4510f0400103904000081c680c10301710308441007045d288012800c1c50341c542c8d0210445840390900c01096008400030b80450f07241505c0f40f0b80203404048001601c8070300300b00380b1101c000e400c010701074190381c500740d01014580e8000070640103c95200031414269088070f019550b0a0040a03888401441400c25044451032881c2c2e2000989038150003c00a408006200719001101034034200f4058000c0700c0403440c2403c100300b625501a41108445042c090b4607000101110302406d410501d140f2048400d120525010100c10301c84003134a00150304280349101d603074400c0182560b9542c0da0480010b11402541665008000050b8100007a00c1c40b210841c2005505c0c2234900741c0f610300301d001c200c41c045403515200502c64000c41c0c00100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 478848228 1250 478846978 478847021
    0x6080f0c0a03022e0801031205070308180115030515060d020a0311010201090c0305010912092615090304060314040b0105101713030314071b0c0f061110 67
    0x4d00c074044030070030326640703c140b06001a002d00c01da031803603103e00f06000c5a40d807900c030f50300d14140070098192004120003008001c01510022030303440304001ba00f021404042903048202c4100380303401894001d89803106813102e00c00020901c800030071002c1904155150418103030b034822040100410858500940c002d100820600100c2c4c40a8205140f03400c0600000800451984890519821035482121984e44840504013003000000c1c0180000d141340c10040401c03820711001e080812640c0d44900702d0345441e001c0421a070103040000b40c501000324244001a401c1116882e0384940c414011600403a0911401207920600b09084512541d0403018a0300e00740d081c4820041038058210790501000202c0c0b0000c0710082c00c1d4280c25008002c00c5018640b9a05070386800360a583c507002088004c103859008100354036030441d0f043c12904c030420250500c240c801d45004208081180c005100c0707400031080c00b080040d081000c142c03015034148100c0768241e41054400b401d517408152a058041450342 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 478849478 1250 478848228 478848233
    0x20310061430030403080304060c030f09050316021c0b2a0d050403030e060702060106020d05070b06120f0d0302040302130b0d02090c09040212041b080303061e1306080f0c0a03 77
    0xc888032000850b0064a10b031694a4554000d550001d450a8440c10b5585000d0010700350548240701341440303000000d00650100d41c64440c1c41e40130309000d03e004c0c014403020f203000319074850305441e08800e0485140900c9100300d0400e10480101140d403820742c1e204140741c3c68060f950b14034414086080341c503083c62901007140d14002c09001c02070011000e040d02c40c0070407071b008181485654418840c9500400e40d03985451002440c02d6a4080402c0622030200011404610002d00c101d42c42030080e541346031031102c22a5105c0c60a0710118416090340035441d501242c1c0c650540050046034000c4803900101c803248001c5100b00ea4071008000e82c400a00f40b94030005052500b80203610100201441b8101f40d00080030030300b030380e100b40001d01f040da100c041003000704001500b0302d1b14441c04041c0190310580c00d1075855543c0f880081c005510942c101b01140c4d03000c05038800e10540300980a82141d8641501c5551407000c1e0026015070400350003840e40003030400d038002070880c03000d07071000b44180071003460358 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 478850728 1250 478849478 478849549
    0x90703061503050a03020105070306050402180d03050c0d0c02010f2c060f0d021e040f140307030c120b0109020f160515040b15010503060f0402090109030203100614 72
    0x21101100201c05101000002c10b01c2809030700c032414004e400120305803071712600040c104d541d5030700440c1c461441440f0541c2c070146000501c0c0030822003568080c000d40d205040903180d50180c0c0071104510b03c91002d103074922992103020301c80124401e07200e0110074080c03c541038030f07000e40c02c103601d150764900c44450400001500c40d003003500c86d401030402d900d016402403203510240e202804644c181500094200c29400c820240310030350940d00b20009051500305840c4d4000040c90307100c1e92221281400101045581c14410b1400031980b0040001c000c9542e80c0103050411050f0384d0a03505140760070000101003801e8001c541510706c519405038640f01098460000d21100c0c603105450138812030601b400450b0a010000d070040340940d000601c07504d000242e241d400d0312005e42d8541040014418010389484000380105880400c49000d42c0385c400c018012600c502650b0b0020307606100f84c029003c80c815060344960143d8070581026590720310312000380a00007108407449c11490705407114188010410 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 478851978 1250 478850728 478850741
    0x2010c0302191b02040c05180f090c2b0e1c0806060c010908121603060501080708040206070b190c0306050a1205030d0204090f0f0b0d12030f020d05060a060809070306 73
    0x10015481482c03030813500420308a480b6000c8200200b040040c00c5113065203900416000d1a1040721172007095180c09d400b00340c0c501d502034405a100300c00030421005031030b00c081c050b04680081403c44134890131118103180141c1011402d200b9a4019103210501340440e10b50782030035680c0940c40c1d500054855400780b28160b809000701324640d568070340d1450000b520031400bd202a41d0607135101445410004a0007609054002c040b07414585820001c001698114000750b0348190142001e15607542c69002141c42889050b0303000b005041100f082207030407660088802c0c06800c8501041100b1a02d11500b98101c0f807140c016940d0244101ea001c11183d41003d50880d101441201030b00e042c2580c800d8a041681c1240d0004015281c48000d204410130083c030480100030859032082c0f20002d1a08041603520004801c0607109402203a40f60120314081d401103640115456011590341903142c004c02c00030a030035074407248240650f6200281c1e182c03043c0011406115460080e0103140e103190f440e04010b000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 478853228 1250 478851978 478852007
    0x15120f0b0d030e0112060801140108031309050a0b06070b0f090a2d020a0608010503060f01121709100c02100903050d080a090b0705070606050301021603050c0a2102010c030219 77
    0x4140c04140003a000354001d01b0028071b00d980c008282e10f00c84800201c8060300c140c211309290381c4180034614030040203400c81404c03a42944400129074465400f840081c01c00d0240880e000748000594008010100c00600d10444d880c0245c05201d403201d151080e11411180e0300a420f52428018415119a80151155a0708032082c012141d81c81143e01140044d9411350150020590110040080742414016140c0c007500012481403190f0402181c0d551003902d0000240c030301da040c1282d800e036204980c0304131400460003c4ca014003045604c41c004280b13a25482c8208d0060151000140025004588075400e0700d5120010305101c1142d00030888485030f00621044200d80c40f0107603a0f02203516210700c6800f0303485036641e0302d5a0b40740e103043c8003082e15000da0299029030301c10010170400c41100044402c03416030600e00345907a004400c05003850a4002c910190a0801d109803038111a810721106100c8848260024050344800100503400c17401000c0070301c240d0f01c00701203800030b1061041551007568071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 478854478 1250 478853228 478853237
    0xb0a050a1d030712050f0a020d110120010902041112180109021e040b010c02010f181a09120a0c030f24020301081209030a11030715120f0b0d030e01 65
    0x1030140000b843c040741d55000300314200b40c0707120351010b00109100559551070317803100401c1f612055a0106404100020010b89200d8030800c1082180e0320860b0409103645202c18800700180c94120501e0080070020000c80c85a40780020b1014070782c0301c000680d200c0c400740e0742c2c06070305c581d0f81e07145600c0959000c07220010b815581c1e03c84060040c0d9640c4d81c4c6141219400941640c141d000c0810b220881e10309c454120305005141c81c031000140c1e8452000002d45a040c03070b0081e1518580d0400c00c07030107907e40d00100c5800c0742c240002458500e901d0094441d00504840101c2c68034000ca0125485003c038810141031402c8541040c000f06095005c03400201f40b00c0c254a105020f0b001940c003200c1340403841c0a241003a000001001119410000b110b40700d40d61181c9203141180c1070000a5948008420080400e00010f03004d03803040d913083c481000140108012a8040111120020401050004911801403070401c18007200380b0180320f180f0300600040c000d000940602c0d1800c2d1141086140c2140c1000f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 478855728 1250 478854478 478854527
    0xb0409090201050c1b04060e101509170c1f0207210605180d020106061e020111040b03010e070309200307050604120515061309030903200103060b0a050a 67
    0x190313420009207020f40103004260b2501c02c010301c1000b003521241c3d40300704040e00e9490184080c400303100178040102d6100380d5111402001c02902900d400750550f1110703805a0308030544602c0b00202103136800f0103040484140440383c0c2a9200c540c4c200451856090059100a100303110401c4402c05404010b00607155440372003c2d5640d038041501d404544020308102a44846400a10100071410301d60079203000a21800e0704141005007030340a4444401c6e07092b81201562030300c0e02e0003035000ca150042d11402540d130b00c039201e50b145601a07000b03100300002c00170141d0010b1440c2d0b22901c02e80844c02da0002d00c500c1c0d0319800ea040000c0042d90310308003a034140a18480002d482d80c651009000900b48908450701035402d50a00038180329039000888410041141041400e582e1660708540388442c0322000200c0b1122420300300c03140d888035000101054500c4001c0d20507240445107081c04080300340e8080c8042515080041d030180110100800441c80600c4000d9009004801401e002e08880d07035080b00c40c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 478856978 1250 478855728 478855747
    0x6050a180f170313031416151506020307030e01030606170a140901060306050c25080403020d032708100c2c0102060705090306070302030606090909061806010b040909020105 76
    0x90354400c0e5856458210703801000020545c00182061b031001c50300c4000c4d801c00f04030380c443c01c000d4412104003e009540c07211810303103008541d5011000355511100801c0741c030f41c0c03560001ba45c0e80d80446802e0b40401c804a040030429071007030080400b03550305a03441e00c5100c62500c895804445e4050082c0c04107a840300840b04080c0300c4030381010311950751180003040302445c50074070100711403001d084110784c2c1100f040408610744541412070041e40441c004043c1c15a02d5040600c1c0c28041c90b00004e5201070402e000c0302c1490b13400314107044030901c54264041985110313000c3c448000e105104a246a0704900c00c00c03c40e44999900081c0b003580079040001140403143c070944034424544c0040641440c0d020070801107940c0c10068541c3c000c0003401e01c1460b20300c810000981c2d0301c200800000c100b64001002560315180d43d41a9006c444000e0074542031410280d007002d0f142c4004850180300c204c101e0301c00845405001818604079201852400d2030207040421110181c0102c0d8411b038148102040350521 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 478858228 1250 478856978 478857023
    0x1080345120d1e02060108030306010c03091211150a170a0b0d081803071d04110d110112020a05120c070813050a0501030b03031c0b04020d060306050a180f 68
    0xc4180265031a140f1003c40b602a0010700300301c8a5034502154042c2c801071014002c000100c03604a2000d00707142115004900d812a81e180c01030f04041550081c0b504903204005a017940a000d9400407101d01c0c14584040d001580c0c1c0b1301a42c020071001540d10a40703800241502c90307440da08007030340e03001c04101751005402142000c0b407500702c11070751a01d00241568510f17400c2107490344075020840103811038034504a20701c004d01010301c4104802058007404207040294000081079400342c0a01000300c40115824445070320340003904135502041c0f6602041c41051024804c9421010442d294541045100001e007007030a0700051885100d02d9040250303401150055000d0144054074030f018511103801d180621010318201e0740b0090506003003141982460358040162600d91001645140c00005410400c8000e0809085460f070003505c00a0300c1040c200d4030b030b00510183d0b4010a810710985c0c603800309040403a05659042d240088480f01c031840000d005055408086015592105203003100495944 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 478859478 1250 478858228 478858243
    0x1031d300a1706091936020102010c1404120c030f1401110301050d350909010b040e010b03070512010f082b030e150108034512 56
    0x1010901802e03402928141c0c45801542c070050594000007a810400c02080040c00c181512084c600e850320701d102503610404886a641c0e03810494944090303030140c91981114803066405070b006500b03240780803d00b1809150900710741c202801d4120300d098500100c448115088080c05c80d00c096101000202081441ca00500300c1405500646101082005c0c10780c00c4822401e87c6130103803801440104002e54030424040b00854004039000100b0b00c601d00000340c0c8110304030441c1e561490902001d84820705400103441052410ba030b2000c100d03600e0320410f107420b0155216401e0724511400040c8540d945a402468000d0100c1c00d280e400d00c0741c82107520081a009800039150140c8513482004070f018104000a4261010030b50b02d10300440710050450320a030315000c0c0800303042e141c0c0b02035452300d50204501c4c039290801d5078003184196100e5454903125800f01d40c2a47c3d003614402c1c0381c0d1030310301d000c00061403444600c180b200c0c401c003420500203219405e00d840d4a0358031000c3c0d1051312000d402c0034440c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 478860728 1250 478859478 478859497
    0x109090203030c240f0c16020d0209040b070e0108090715140f0702090a050720191101080603030c0a0f02060412030c0302250b0c0102210601031d30 65
    0x2407000682a08440c041c1c1e00080c901117111108505014050260070102c8007417843c0398a40303000044ca00e001140003828104c0700250400460380420060010a0001038024403080d610400b1800043d00111141c0b102581c0e003081d40c0e0000309c01040404403800c08102804064104950021034020b251001500000904400b054001544204510f050b10340e4a900c4003100c03000700214140b0404c02000c0c0c00e2072320200c40c0c10347c04142d804418281c00b0440146980e200711405841c0388060b2800c0c0300d5511811060070b020030390440106e24540780200554001c0d0b0b442900401030036181b078403000f07101c407034072031042c0e030840c0c000c100104144140318005140c1d0f034040e8451303203011400ca01d0000d1a044603100f02d400050160440040423904180a403012a500401c120361030b00710250f140c0b4020b110340f20280300c284140d0010114003443d000081c51140038262010000e440c0c6039100c0003082103034001610425000000101c6286101c89084a5007620f40003003080c112035a2161000c40e540a40360300d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 478861978 1250 478860728 478860763
    0x6280203070306080f0312240405070306080a0302240403050a051806040303030203041b0b0403080318010203012c1005040c0309050303191a0d0305070602120f0106180e0109090203030c 81
    0x7a06801f40301904031600041014414400956510f00b450400012814030900c0f8984520104200e14401e400c550081c04a82d02035860840f003d141c065510038103d07140038024441200c106101c24041002140b066070191142c52412960800c111800e81c400c80c00c1040b6403a60103103400746e60311007201030f00c06103109482c0180c0e6130800f0b0030001c07061a0040040d1a50742d05e1303000b017400b80209540955045a030300c140076a45a03100c49030803040014010031403010340c0d84080000140c1c0700781805084801412204140170060010410000003e01260759501c03a035141c038002c00c4141429400888002d44034500018003c001c0c0c0d450a08541c42a1611502426400807404006810703102d000500603a1000651241c000710004c114010558400501800400b041c840240300c2503070121a42900684058030341407508407001d0181c01028000e148c00603c03500ca651a001d000c108240d0103841200050241a80c83d09101c030020344003400c02280c140c00709000030701d00a4002c0201102c0c3c201c030300c1c60 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 478863228 1250 478861978 478861987
    0x3040206070b0a1b09060206130519080912010213140108060f03030c1e010c0c0c0306021b0a080703110a030206150a0b030f06040b030d052d031806280203070306080f03 74
    0x349008e4002d004203980c00ca90b2030a0b00005100007412080003501c400280c14000a0b90911006502034a00007039000000c00007a0410550198014a01d00041c250300340c880940b946030403114001001c080d603012600d000b01080c41e030f00c1c220b80720322021180242184c1c54900d0601b42030b8100780c0030442448200c0e0a611842140400038020581404898906800021001c0e01c8580b5240c190384009001c0c00da00042c0554200e0078003007207103442c10628048841d0313040c40d131402c0403691303010b80c03003e800207407035441c3c440301504000c25207001071030700366004040e2170311244804900c10302c10582c1c0d187c6c890820540054070040000103903209040000f141851440c01c40288016a00c00700d0070f0343c0c426008556a0a90713550440d0039078091b004c001c130000f40f90044101061a1041c0e0261000b00643d0010082000800681701c410790114502d409070303401510352081d0034003a00804a82c03d0300c0d020032409800c0c60341e4020b901071a0f000341c0902d00465540d5841c13403101d04007a18148122a00d400014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 478864478 1250 478863228 478863239
    0xa241d0705040e030c0a080c161806091b120e0a050c19082109040906150f0f12020d021008040c06080708160e030d0314060603040206070b0a1b09 64
    0x115690ba583c50b030f007001d0744c9011604c202041d01c420700514020102800496a15501d0b0341c00c001400600414902c040307040341c4c07104050030311112000c842c90030341c5041c94404a481541405141081201e6544164142110303c0c0c082e40c40000c2c495840a94a660780850184d4050401022180c14003420142031600b0520f014030a9405d026611000c800c02c810004000300e41e80001e4003d1a001419100180724100c1c07682d880d02403041480e07480d4070038182240201800002c2c1e0083e0300c100c2078040001c621b151744e80c83d04100700d420f44c42690514100b9030f808000d0001110b01074605d440c401060704160594590026803a1496001c42d02c0001d840c0000300000c200020815070040c0003e410458440d1801d8070000303101c0c07c0e008106044000040c0f1083c203107540680e0090351141001410396400c00071071003005000f0402c10041803903488081003c6803490a0003000c0b02d02454001d0011464030401d6200c40c062260054034000426035955401141c080402106112001023981d0f401c00b928a480c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 478865728 1250 478864478 478864481
    0x3090b180f06040309030b191406030c0a03081e0405060f0c0d030213050d03020a0501050a0506040c21050c040b03010305060406240e070504080102160b01080a241d070504 75
    0x280c0050740580c0160305020209801c8400142100e0b03000c0d014503220b940c0c0d01c200c030390300502c081e00d150001400c058400740c88010038010688034100039000c85400104060420040c1519131001401c00c0104000540c425001d8096107115120700054541ca41390359a004540c1a90140f00c02090f811030100da00c04421005002d41d0b070071203406140550811460307084002a410030b07889118411228850920101402449000c00131900100204040e00e001d00c1510f0103060700715000c600c160b03c0c0000c0d684425016200100d007800c123281c03682c4440c115640c07100c40249800703003042e40304800a0000103079a01281c0015130103140300300044c003041c4c02c0a24012060380e6220302c005803a040c0360341c01c1e0486140d03aa0a03800845a80303c0714031800d51a203900075911840303203170004078895000185040400015180c28003d1521130310b40341d80e250b0f907241e9115807103100e8504000c3c049074040d50082c08a090089000000a10300c4d40c001130740d81d0034008c1c000a80c02a46c40c1c0e61203180c001440800692405 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 478866978 1250 478865728 478865743
    0xe03120708180706030504030e04050f010e16021b1206100608160e150c0f0a170a0516031725030c050d181407080f071503050703090b18 60
    0x2200a82d880c900c0c6414041e00e803880d030300a00082655a000103014940f180c2d800b60002c01010b4003c01c51420307d040c40140e8040e09001e1920881140744c0442c21800460404100900d525406400904290440100780d0368040b00c003e540300380315880340340000909100b02409225480300100c0058541a0003a0115000408105504020309104040260050051408004125005142c403120740d4a0f020f014000c80344019414401c0d00c882d050040000030713440303410354060100c0103a0b400c1c40705020042486013000c0c0c0380028005201b4040e040605603850159070340b1030700384544541042d01c07250700c1c00318003103a031440f80020002080f0707425154004204462880c42c6001d0180e209a000c02800a200d40140c900509680b01005132400000c0d54092a126901607100c0855201d040455a6100d0450140f190540034504031a1a1011b0008466046495064072403400151a401c203034000c01c8024214400d058070381d0110070004003880c00d010721514102c510304039400e141c102c865142055 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 478868228 1250 478866978 478866991
    0x406091503062403151811040303020c060d20030103140d02060112020f1c021305091509010b28060302041a0705030f0a0903060506030a240e03120708 66
    0x16220701400450000e500080703c190000e0707681814509800021401444220100f1114881140340807980c0340203034500319081e01d103060040c056160119420141031150b80302c0200035a000420820312810003802409640c1c024410009504c014442c0d6100c58010035030074134810072000401807080251904500c80d02000030750003403a4400300e00300c01039590307030041c040c041101c0201c680440856440c0ca00d04942504054000c9980c00a541300500b00c580603118224410b038550b4005010f49110352060503c9801d0210041010200703654950007120000350109146540751303865800c064650142c1c0c0c3c0f000c100c2040341154007a55402d8417500c0020703140c000d8001c06004000c1000b03801410aa00c08012841c503c00782d90310a0359245c414030354440c00c0484e0000000118040c2c400750342016403102101c2c043c0405110641d681020107807982c10310880106007035a080401e5525100d00c412411a140b140040010806074900003540b40d90840000c5105001444003009861580b0070f0380e0715000071 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 478869478 1250 478868228 478868231
    0x1203020a0807121e061706041e15150513020a02060a0e0c030a14010501210f0201020f071e090902060d022101030b090d020f0309120a080406091503 65
    0x50a58400401d42280640080100568422200701e0f4014940c488080c0e000498032004008407004100c10191845106a00480d444007006d00035201000c103d0b01d1140d540079489c0c6034541c1c155046851041d800e0307a030991701c20300c4441e41c68503001c0f90303440303180340b0456000000081c0611308010032421103006482c039410725005002c54181d254000982c0b6401840124010801c00002a200703480c0854cc10710899241c81051214014400342034400e19410038104020302c01c680c2c84040700c80000c3c41584a00c150000f00c00c241601080128010701c0d8107074414030554038803981c503040d0185410801e4000025543c00d00b02c3c0003042004c540c000c0760003030040240c144401046070700040d020740a07d1001d52010b940006060140c456014076010f06c04917910380c000d8043d40c60b414411200142214110020b104921090710f0140c000601e013000d910040005529010800091014118800301162050701c1f4108007600001e080002a1001e40007a580c0e0288207840c040701e10b20160541400d000505 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 478870728 1250 478869478 478869487
    0x60219120509010e2107120f0e030a020112020c0709050915010806100b0a0e03030f07020909120d0e0109020402070b0615120a020a02031c020c010f060f050909031b0109120302 77
    0x7140215041d058010305d85d107510000f02c0c42e40c01c0d9000501c1a030600408091007041e14221003070704500d4062a5600a5846031803983e41c60302896551008604041d000c9110203512001c42c5003590003c0c0008850801035801d000d540d11450019180290b881c10159046404010710000035040f4250051100a0081440e410441005101c2c44110f00403400f401d0000203410180a00902650a6030180502182d13950100380200c6030603a0402e610407480f540d130002c00701d1201c50380007416143c44505090401c1c80c0610540903100240700140320b0008654944010b10056565803001d0304586009142049407032808004000700ca0000d503842c0501413109002206948051f81d80302d540c4820790320001a50703032804020584c694060b003904180c105d01003201c00e802c41c2c24150042c1c80360140000c000d10002e82d0303810440094030418040d0011a180d0a00200010320b0100d07000c541000d480c105072071410500080c0904114006c401403000c07a174450742807200b00200e90511040c0940503142c21400c2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 478871978 1250 478870728 478870751
    0x12170c030105011808070305031207020609100c030605031006090b010f050304120e061b100605060d1808070b040308060909030d0b01020304080f0708010c03180602030406021912050901 81
    0x2603000600078641003101130000641e41d0045541c8410190080364200c0718241c0d07680c6080c45d40c0707900c0249402e0400000341d0101d0505400050018020341290000d09149146c200800008040c0f03056040c0030107440f9000010f640c2c906100401c2d11417040c09011508600b0f1039443d00c00c1c1c861440405042182c0c450b00052035651100560750029800507600711b12642d000000c4519800d04807103158450400641c00072041625020070f2003800707209040c2d40e5941d840038400c0c0c0442c1c0300e82c450250090700401c04202000d030141d10003040c042c0750085040105546480d400551b800040c4202c808081201c14042811340006021394456000c8805000e40e160544090380c480c02401541e20840f525050341c81050b038020300c185c0340904120011501881c3c41c0540840d543c001912880d01d55500e002a0040c01034070038014a007600c040016505100000c9a603500d00a500082013500c84035800d0007040540345041c580c516000780103544090754108101320200440e00080c060106c10703850622031401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 478873228 1250 478871978 478872001
    0x1103090703030c0615080307030305091603030822030c0302060615040b030910050a060306180b07050a05070215042c070518040501060309120203030702100b0607020a031217 76
    0x81d40c0e0315150000e0081c06034600400a046071108800c4400c0c0c0052000ca12800d000026094940c020b40d010300180d1189003082d912004103180c00e030602c104003481070002c6030041040c40d4200440c3c00100c0c0480140042c845d0307a80000c1c00f000c400168120b2205001e1590401c445d6400140481d54070340c0c82050401d985207288642e2003030807004c0c04044000b4050803428000e4004654400e80240950320703211403030350001d0050340000c0b0f6601e8030705450300d0080300c0b890a0204400b50f01c03003c804025122400f080e10306801c00030001c803c1041c100a8100162078000400e20502d0f00c2501050325942065103448000c00800c0210b081544034044007550025101038403a00001a424100e80d510300b201205800c4040f0319400e103070402d0400b0000180e0035455800f80004034090503040b95400c5462504a8a034801920000016841044814143d0005500c85240d0400c018041c07450810594003003000551294015608400c8010305001d41d07507041001e456400c01d40040403402071603da5441607 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 478874478 1250 478873228 478873243
    0x8070506030118140f01090e030c03030f04140a08030a050c070510231501020c031605011d3a08030c0306040207140c011803030f0c1b140301110309 65
    0x2c500f03501e5840210000d2510390f1000c40c0c01c45891201481034a08001c4408002100b8801d48031281e00c1c2c03108500c2000c0c804402c0d1640d0080041c0550320755103403010034241d00b140190040e51000041540d02403811010042c444803180b00b41182c0d62640340c85c04099007140c100031b0110799a0b0b001004032070000356010404588100b409540045c41c01e080071200c4001500a000e08413030003030f050003400a00801d6580c5400b15003002d03400c0b1401c05038000103140d2500d2030080d215800203e122014490f5601501c10041c08460383e4003000c001c1c03850b4400054100300350b180b405503d5015840c40d083d92001d401000140f944807032550a500b54003139034a42c0c81502c0000d202c07100000000c80441ea00750740d030b601250101500a0f2018441000304e4030240d45400b401c0c440e40d03001c01c0c200c0300c1080c45110310104041c100d071341645500c000300d200300e1015503082c41d0125084039540c40700e1070075100c0f2050319040003000e01040502e00d404019540e040c1400c4401c2d1441c002c884080c14410811850380020703604 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 478875728 1250 478874478 478874489
    0x304020409030509060a0905120d0801120501180f1208011d0a0e01020724061a0702011806110c040204030b01061107080a03030203040209060901152d090501020601080705060301 78
    0x3440100605049030103004e507441da650300c80000184180e084e540102020140e0304100c0701e15a140c4800046544da8480e40860000450a464010800299211868401c0f0360180001041da08805d454925a064025104680f1210703440715031024000400f0f02e954040015003025060307035050a60184048940307448000940d02418000b505c940388a401030004100140006e544a906502d02003060403004041c48041080080a000c3c01700c2d41801303042c00b15050384c845070201c258001c0000009503c510f00c140c2c1800102c4e600004108006007480000302059915010240402903c1c107040924883c0c080d0300c100c0c0184000d20126403008070250454900e424001aa0985000480c0c103045142c4e0242115001d8040c40f0b0090603059002075114034130031503003160309545580c104904d11100703008050000c2c02c8008075049e040d014403441000c200d20360307541030488031043c002401d401c0102205c0100003011201c1c100400e58040002c0c5024043d51700c050451907042c100456901c0c081403045 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 478876978 1250 478875728 478875731
    0x10080a020a0c231b0f040f0b0a090b0a06021b010e030a0b04050115060f08011404060b1b15090d1b08030901052706040219081009030f08010501020303040204 69
    0x820001d9000d10040414181c1c0048241ca140c00f400004120511040d4102c4541c0e001d11180b03801160320450602d02e0301c401c0180403040c56031000007071000801501c080450126517a045181b8140d46240f4008002c2c040258045210304064060000c401c00541c13001307046d50f01c942c8601900307003850895425641d600b071030403074800f449060006e0718110b02860058202c07011701c1c00340012b114043d00311001860b031210300b000c40290785840c11180c11482094444c0000c6440700140400f1580d40c035412101040100041001500c41a580c055a401840a81d00400351141c0d80324202d0010320420b40c14415802d280a11890f01210301d03900c2da50140c40700020010703802000c00800c1c0503041d04000082e0080c80c1c1589034501545064024803043c1c035141d03034520040441e480b031049000c500c030f0300340c000d1080602040c2d1a550f00f840400351a4824801c1800c0c883d860100e0480001c005041c20341c5040e03900070a450101e0f04025101000580b00f100400004a00600441e40c00000712500103505440 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 478878228 1250 478876978 478876987
    0x9040210030b1e011404060c031409060c0109021e06030a24032427020303040902070f1103030909131103011104030506151f110106060c0b0610080a02 66
    0x71402095102e00c8654090140c0b00c1100c07103020790103100c5080500c2a280c0b481d240e06088034103101070050384504d0000914070115680000d103c1e01980c0303984202104441e0500c9450742c0011590740046030801800d079500d00c80c00c415450043ca88140c0b202d08294000c060301a2400400c40e148002024022040c0e11000c14086d40c1340019200501c0003250140814519220303c3c2400c04604c1d02c0444c91694400412500c1d05840244030701c1c1d903c51358024861001e54010604840c8140c0901d03000d90380343c00240000030311507615000425140f4403032441102d1251a500e814002c0e0780e40d10000c14045e030f0003406400740d544c5540504503040300e00760f0710420103001c551070301080542c2c00401c01c6805508041912050141820140064034032601c250b400700d5548500b90000c1494000e0407980c842003c41001d4076400005400980e09040c40c500009050314544401e800e4600310352060b4000b07505c2103140001e100f1403800e4241c00481c103e9628004150a003030040244c240504031000e0240d0006 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 478879478 1250 478878228 478878259
    0xf05070906260a02030603010c0f02061308040e010806060114070209010b07110406150f080402030c010c0821100501050c0d03020c0a02120102070308010806010e0a092d02040c0e090402 81
    0x15010030410b00c1d680c003881c1c0079182a090210180d00281d802600075802c00740ba13010381c0ea0040c800f410410b240c0d03a004007107e958a0610341054000c0d190107951740201000f0100e400201c2c190702e035000e4201c0000400c041d040c03e5000403c3c01c10031860710301000c48140003000043e501d8080c140d04440320401c200d5120011400c1109000010310b60043d0b00c40d1401d400001e08272401510011050010f40302c4d0315201c0c0019406a4400c0012030b0000d42c15042880c4c031202c01d60107881c2d01c0c8001802083d40c1b5090a40c01488403030042d100c11000c0e100c4603000010000f0540490500034040c040030b103842410300500062140d079415410814209258000c240c64205400c03c000ba0111150002d103000e0401d22a04d501754000e42c81081e09a000459030b50010820030360000700300b8100c0d40c418a00c010300345d82e031040c224010300c1c9003141100d1103603200500040d040d01074555400d040b032007008008000110b52042004413003039030589400340018044424055540c030083c0541c030603015691144164000c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 478880728 1250 478879478 478879517
    0x3040f06050612010c0e10111903051303030804050c01140306120c04060905060f04020715020d020d0c0e030d0212071b050307030b0a06060c080307030b03070b0c0d030f05070906 78
    0x3d042d403505540c078040c824103c45611000c001982001500c1c0c0318048288100708603480000550203000030791000003003223501d020402c3c1030030000b802441c09600b806050001945006000da20036000640703a0414401031020500540740a12002d0034140307500d06012407040c40c00d0100910580c45191855a2a01c01d101d00740060ba660400c010420403c058641007141c0081ca006d84039280501108030b9001c610f070519200316506070340c000c8444500301050000701c401a40c00844081ca003c0c3c3c0038040c4409a110f640244207421740142c41e0410f06a005006251070200c05107040000c5501c0346035241701070701c9500d0807600125080010740120321100c116144180b040c036440b10784c00d4811900d0000c00d10010b080000d0040c3c10407282400b50b1652410102d034100c013400c401400c0001e04001190406020380d008034065080581a40c1c41346645450310340042e04442640c00554010b0a1134403007050b0b0602c00e11035260000001001242003400f0000c0c1807402d81d01031141440803410b80d055905a16 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 478881978 1250 478880728 478880749
    0x5091503091c0806090106181707080c0307050612040c030b010617090c09130206040e01080601080d0206090303060904061506030c0e010c0f0303110c010e010c03052409071704060504140303040f060506 88
    0x610130f0541c4d0342278035010b0240d42c0310280d2050265601a0b680058102d11303002c5680b008030350000780280d0501c0200c2d1045850f40f000904100d07207890214600000050407111024000d01040e101c42d069202c0c14400d8041e5a14002c0c00200143c010030460701e655900c980400360000f50402c40d21054500c135202052841c4901e40207854400e0140c0f0000641000004019052750441c50a40e4804a80034138180c0e41c9081c2646e1880c40c980082c400166541400d0b5110756100703000da070000c00c02241c1040305844284e4182c01c2140081d0f03c032451180c060b90000c1c0d960031210303420329042c03003071004030303126150140b002c100028100740d1286007200c003041d1210243c0381540c800d58004c00c290300c1443c011500a10880c000d62012030b040400089101c40604010b500203065175802000540d5280100100382e54000c0c4802c090006104841e80310401c1000020b118a01ca00000103940c100b40c10000760481c442031100318103610410402000415030440042c0456101e1b2000c1010f4840100043d6001c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 478883228 1250 478881978 478881989
    0x210b010620011d07170712030c080d050a050903040806040803060f151c060e1314150108190f081e0309060f01080d02070605091503091c080609010618 66
    0x90850464003c03014059020040140c4011104425544c00c10b26040c080300e070801150300d801c001010010700300f4010400900c81d109141c101c40a519654405019402411050f403003c1d17959010008101300c40c0c41201e800600b0240107605052600901341c1d81c80400900c000c10010700031020415907128441a4203110034001c004124204d01c00d044018a0303082064409081042a003a0a1620000344200400d9969195803041256650002004445190b09088070030000c0321222507071407001807000c40c40c840f1540e5080c49503549020501803401c0441c603403c520700c42d21541c1e9400028143c00a00c809141d01c20310300c580b80c441c1c2c2c4c03440140a0f103604d42052843c03080002000030813180420500d01c1214110000b1702280d80303500d2032030303910260000d032540075a004000901c206401b94018041c0500300034089000096071405407902904141ca500b000d641c006040480d08a1000e401c40d1404000fa1800d2121403910600107048904c044c462141403003030210804607914040004d0350080c02 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 478884478 1250 478883228 478883231
    0xd020604080d030b0405240109090c021f11040e18011d010e070506030604021c090302010c080c0f0405151905040617060a0b0a02071a04210b01062001 66
    0x35034a0718110b8407141d08041910000e031038003044524034513191140c20f0213500b0264811103100c00510160084c001c00c0c01125051050201c00081c1c1039200c0d001c0e0551002403076000c0d2070076000c9400800800c1002c00401444030f0305048070802c0481c0c0354002d0310211010300e41182185d45640c0c4861240c4c44141150340d00c01d50800d40901c0900e80801707035550008031440d000708401804003503e80d4a81c03d9501800b68000810408240a4645900036001c0341c62540900200c2c02c0480f94481c0850744510307400c42c0580d4503000c49101e02da4000410a90001d80741c858907150068808144000b403196002c1c00d03100740c1050410010b030340d58101c1a9501d1041c52004c840010945ca107001d801078205101d02c10008084c2128004424140101030340261006095440610304188544440d90021a014001c40c442c001e80098580c0e5181c2054810b501d084000d640c0e12410312101203003204c003a0303004510006100300c00000041d89410002e045505500d42004051001000303158412000c6280c99a00c3d07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 478885728 1250 478884478 478884487
    0x4230c130623180703020a1106040c0509060301020417060906010611070302210d03090b060f0d0b09011803081005040e0a060c09050a03080c06070c0203030d15090c0f020d0e030d05090d0206 83
    0x2c45e0540d00801c0030082c65114200020214003081b5a034034802c45005003046403a030310070000c1d81060405160482070040026060580315840c40300035580c08502d007a072650000050000340c001c14070009014200d60b1070a60f040d201040040340c1d07a4441880028001d02140c800400105d00d8961803940b100e90320410307200480f07200a4010f02a040e461000d58084812a0200728070741307070250f64410071640117007154440340400e03150360034030b108000d0060b03405540328a844180e02d22840c001014052184d101c0c090382d41050114003151400a0300450700592a040881800101c001805509181e0000c4e010909510030401243e00d199103601c0117030040041038012003044145000391046c20061317021958240e96501003114140207450020790550810090103000450603005840d8014245282080e41c07580c5540b110f0486550001e8400095500e16031812101e03414048061408640d2034117500380620b6a0001c0d48404910490b1420700ca40012800c21f5a1504030080c1652600180200e455 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 478886978 1250 478885728 478885741
    0x50f0408060a0609020307090338190b1f021c021b03010501211a041101030c11100c2006010302010219050c060304230c13062318 57
    0x48090603550640b4180c2004000301da0322800b44207032440346041f6650f42038003600d59110403030b40c84104440303c04154082510840100720300c6151414041400540390118036242024601c20484030782c0214840e070a1644103050760b035600403912000440052a1140d00d202c1400c103034601000c000343c1080d8040c4810440d15031070380200c0c0d01c0907005020019074501c810520708040c02c0710824000c1c0510301e00c2094112049880c0c410b020a41940b050680491345103222031003024038101102c04580f4054181c2c1d110402c0d5905000c0c0074801d190a0900140103500c00101e41c0e1510215003244620940c0d070401c0c0303441701d441103412180000d1150304000ea511043c080712520f5200900059002d445019020004006030840958002c1e821001503e5000300a604014090384060402d5459056411040c004100007000300c0c40301515620041c05102e00640a00c182c00946071084090f4a217421010448031006880080c2ea01003682c0b00720f40d296569500094000d51030f406180311400004041040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 478888228 1250 478886978 478886983
    0x20c01050103050708070f1208091c111c0b0f070903021c120507050c0d15180303111c05131b050913151509020a0e1314040b0403050f0408 61
    0x6440b40001520000c1361101d041a5503100284110040d034100200d80e200442c40c500d0107003e0001c00181048210500109403078bc100034001002d950105103011221064030f8600d114006e001c9480704104147d69050305c4041450300024200e02480410030006566644140880c5028560060601446000080588008004d450700880d102440310168030300044c0190250b136100b560040040c11002110070030302000c146000022500c0b5011402000b1403908103001e111112100d000c9402c517441c105003401025038038980e488000351a030410070710354054500e05031440f03141c03501c2402150303e4442000c000940e40002101401c10100408030b00b070f890000c49510704c00c0740c0c000c4810802c0c0c2c1e1140c4002289001105900a06000358060f0300c2d80402a503401001c016a424922072240c20359130035008050ba44a078102c200051181420449145000210080041c00000042040c0103a05030310840d032160140c009402c220207071000408141c030460440d820b10a43e415682c0e02d46560300c0d50b565 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 478889478 1250 478888228 478888243
    0x9060f020f1201050102160306090809090106111203010609030b0c07060e0303010905100b03071b0c09090201120b0a0b03090a150903020f010c080c07030309020603070905090c0a140d020c0105010305 87
    0x10b203062042d00000d501d61000400c0294031004000c0003181340c1c5142d0f1998010f002520f0102c490b81d00c14400c6d80d2b419950480c0c0c6a0003491262a19221113583c03558590034440d602800408656040c001444040e5000c410401900e602076140e0309035844944010205009003803008245c0342c241815a542c52001001450480b201500c0500c000d8035528280c00d851704007401807152108041c0001031820b40302d220b0914100c0000020003003100182d03200c2c10304488264219000300c946441d0710780210350740072004001070701c185070041020200d800700160a03140c2e1403180c4c42d41044003001090340c6803410706c01455041e610003845140090341011032400360100380030a4001d402000d1746004120010300905c1070b25441039803607040355691500e819049030041c031000d03000c041d42d80d106500142c544a0003503006000940302c0c000000c0c03400c1d00300084450000c14401d050101030080e10440e039005801881d0340b080300c034a9580c40308010000c0c0c170000d0043d042045d03659030900c000041031010229084 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 478890728 1250 478889478 478889497
    0x3021606051806100303020d08070e0312030114120d032007061d0d090302010815121e070f1203140706090201021218190807080309030c09010302100309060f020f 71
    0x120b583e0741d60b00c402840342c51400c1c44003501503002070080a0703009101d907000c150300013180e09245078180048030100b03152001000c40000070010000052081124038120300d070030800121100003051021092240e100d4500d10081010726403103812a40c40c0008e0881e01c580c0300015501056201d1550b410010042e0881d4107416001c68400c02d0030780103541d000314105034400c1560310b4440e041c520b1940116251240100440e44030020303000300e1400c0c0d64a00c0c003010703800e4020100030044030103506c0740700240305901c9000c0c007115131007240200b100d00c401d240075408440d810550102c0c4c903900f909081c0c0e40000f00500300b40e950340c40010000304001c001c1d4041d0f40424001c1e42100c001c0e82100c00d42c401684035158054649045c940700114080c54886003c0107030040d4401884801070b03681441901c2e000039134100000a4002003a40d01160404208404040404481c840c24651543d000f0494101304114814101611a08800188041c0c2d40280c0c01400c0c50407011550345070810f0a2010941000440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 478891978 1250 478890728 478890733
    0x70e16120501030807020f03070b1b0106060c050d030209132f090a030206070204090501090308040308060d031b02010c0b1303031104030201080117010917032e06030216060518 77
    0x10315003001014494075042c2c0c1c1e88480143d02d000a0f035002c2003152690103d4080d0706126260b408602c601404010b44080c0c0c0b003000100b59281603001c51517003514032503000402044a10080d050110b40001940d1400490314100103a49104003008600d1020704450f403a0304250070100a0f907850780f0400210121401440c43c200e02c10f11414420031010303c2103400056200d07103050000c1c0094a06280188842840284001010421591940d0a443c44040b061b404128034508020034990040d0100790b1040c0c0032640e011070700b40c00e40d80c06040b11030755025480c8a1180b224070f5108690107941d0004a00d41c1011503801e00346041c0402000d0450040b17402c800080c100ba140083c07000540c1c0c20348041d2641612105040d80c24202010501e9181d941c040800d59210f00a40000c504462400581c02000791181a9070b450502c684189204540c41704d00d888545e1548940007400c0304002000c140c3d5140e141c00759442c44010102d03800b000d06207101814040c90174082c030a604202003131062003400f0304c20a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 478893228 1250 478891978 478891997
    0xc281706060409200102010906050a0605100f09060309030216260f0a06231311011b02010807020312010906090c021204060e04020f070f0c08010e030405040c02070e16 73
    0x502c0241c5401c42c0e0002d1909000e448260343c01c548070303040500511018800012034040f50380b5440c00380c4105076000300354036988041c188228208000c1100300c180c001d08040542108602e40205001140d20071303101056170302c10301d06080602c2400746d400c040385d030a2080c00e095a25140001c12a02c004444051080290001000f42c0e140105e4451088900d03800500b2046040d5200c9a0103803051401c50b1036001c03000795040c101038010400c070038003541c100c1b40e01042c481924601002c250801000a0341070021186000c1c0100329094041020580c0c20b182c03840450b11114401d81c6107000300f648545d0340310301207030000c1743d1150f51781e11410031140c2425013482404040342003aa124000c224245624207010072040c020240140c0c4280040080a0070040c640480d0541c014143d4004210449225078070050a100f880300b046500000b40030701a000f00200000860002c1d0b980c41030b8130890740115100c090500805001b80044c1000341040b00c044509440c0c502403a04280c2035048014010405c01c1d038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 478894478 1250 478893228 478893241
    0x4030f030612030917030c03040e0f01050906030334050115150203040e060d0b09060609090313120c0509010b0307031512020d0609080d0b120f0c281706 67
    0x503090800ca60f010f032544006941001079045040300300c911245024031003002601303038424007000200000c080440346850707142004211003a030f405042c1d2103a4400c100b508140011035402000300e076030f03890642c0c400c40381d1140c1c0d0385082c4c00f220110f0012501340f00c3d07205010005008042d08102040800c4c10140c41e01c4545a81e120f00c10060100200300c01a030080c44148850010340d01c02c2608034400400c10302101c001d95540840b210300c1180c00c0e4110390071039024000c0a0412a00c001d4011403120302035414982d8580c0ba641400c01544191450b01010720b00700c0b0f0034800c0b500c004801030080a48540341d5583c480c4003801480d8419600440080d14003448070072451484400801503032403030300201d15050129003c0102d2842a0041660035558500e5482c0c00079400c43c0091014051019001c5100002c0800f08446118100c5000085403c400ba2101c807250307001c40c801264a00440e00c0700803890086180f0700c0a030001e491560b981c0300c1d0904000c10311301c500a500d9100810b41c4021145540e0782e00303 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 478895728 1250 478894478 478894499
    0x12010c080115200c0303040906051e030c10031410030b0f0f0411040e071428030b180307050c040c031803050a1101050c0403060e16210b04030f0306 65
    0x282c64400101c00000f00400da86010108580203100319049441c240042d10003c1e040d54002d50207100d030242e681604000b10b0030b017000080e0400000212402e80310143c4404a0303241d00810018030f00c150781002c1c014013031034040c1c0c0c00440020030401c109501c51600c820b120703100d8000c0b1f00082c5c07107483e5030000083d040244007044070700c5a82c40d40010202a259039480f480300a07240941c20b0703402070312000c0d101d104910030040c0c240107150008407111352400b05002e104408045210705100f40b80780242c000003001c501c142580c222a44461204910b40d90f111500c4401d20700600080700c4c0703000010341300b02440400100507800304030440f010814000c040e01c0550883e00d0715086180310710310089199011a014001070070200009091940015115400850850354112045240d500e004203042c0b0501c00c0340d00c66441c410380d0003002800c1d880b20b0b4003040c00030306055206080f00440104060a0100b448141c070b450070356400002c0d07000038102860080d14034008401010002898a84c0000c0c044050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 478896978 1250 478895728 478895759
    0x219170118050a14130201110111030c03070c05030d0f05061008040201030e1e070305070603020a0c1b09090b0603010c020615010e040e031303060507030b0109060c1112010c0801 78
    0x38007000075800d10001084801910700184816400c035600c2c60030000302400641d12520500100da24881404010701c0050300071083c441c10303c0381c5a07141040c109420b4401a048981140400c1c1d03510380c49558140302119814446c1500802c10f00020841031018015500403540c0c101000c4010f1010b65075000c05c5c03260310056864a0380014071000d0110f00554026840008a0100d08007a1400220650a40d038075440c02c0710080c0c90544e01004082082c84000e01161000c0c2455240540c86c002080600410144000d440900030b4101000c0d0540aa1403a80d01e4600038a10f805090084001f00d040140c04000215030b0725010b0350802c039a070040c1c00d1000c6009031242e11172408510303101c008000110f80381c81c4c080c05003580003948c1c9c2d10b4000071044100043d21103460200c1d614403100d0b00754540070085d40d00140c980400d15042031040840d41c5c0c0c200003810103441842ca0074419205039401e041a100c8800364240b81c0024154160444000040d00984d41008036501c074203541c3d0340c1e90000f03000f130400c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 478898228 1250 478896978 478896989
    0xa0804030201030926070b1302010206040305031018021801030605010206071b1703100e0c031305150a021e090904020603060a08061609050d02010801151202191701 72
    0x80106000560203a404003140f2406a50304200480ba4540a03a800b25034036004011040c60106e2a03000300640e01500c503038440c4800885000420703075a40041e540311009403000b0300303100002c4005000540f42c40c10000c028a4001ca04520b100c01742d0810000a42c0301e41d00b20440384962510015065009004240884406a00405041e41c40f030b54201c404030b00131a0503480c840b001880c00400324080040340e035020044641b8a9a80c0d0501440e07020203c0c00990001840305404410070a2109800040d2540501d0032950550a40d005240450a0910151080c030501c03070a0001e104590340c40d540a0b01c0f00310700c0c45440e5400e26102840e1074607d80103c00c2d00340d03400b0b810003002074018100440a15009840540b03403a074455141d511050500318100c0b10010340c1c00481c4140300398113620900803c0101000d9440003e42c02e016000208002c1d41400303900e07003440162070a080304074420130812010000c030f4501191a1500a080c0b01c0c400481c482982c40090a04140b08180a2110400074102c44 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 478899478 1250 478898228 478898243
    0x60f0e0f0a1a0d0615051906080c0403050604030c12030209030712020109051302031006050c151b070308010f0b0a0f0e01021f020d1d07060c0203030904110c0c030a 72
    0x203840e402484003411004180b603004803100028180c05469203a01a14414824080410210807000c405c0282500310b500c010f210f000082e10101000110340c8811007070300d1040c079002d981507840350b030800200c0c0300d43e6100500c136103c0c602c100030525038044070354003070244036400344104199402d07012826405481c0c0d000c2e80c1504140c1040003606c079448007100b166441070500e0204541e0717400000c2c1000040440498105800000704240003c10705500c9010340310b142407260a040807a6183c0b5602c103a40d00c04000c1422448000c583d0100200707911207409240d4a54855a45c600c62030010b2140381d00380300d400004000c07540042060206202652aa41c0b09555070410f58a000002150302c0030000e201035056004105441c01004030342c003410140f101e039400340960740d803040c0349a00040380c9000b840660440300a1000740d1841401007117100c00c444003460440e2054200d40002070840c070a0b003420a90052500020044911400d00980300e038150700801d4805802c050000d0544688403c0b10061041 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 478900728 1250 478899478 478899481
    0x20f0402030108280b10181b0809010615020f0120030c070804120606230f04110903031612080610080a02091005181504060503041401020409060f0e0f 66
    0x104c0c80403c0301003010440301101d40440040d0340f80c041100c401a5800c0c03200152200b02032102003134450040886054800003002015909083c0d450031100d03215a6600f00010a0041000580250400405440c00300780e101ca0050440501039030f00c6103201e04d038140d0f40d400c06010380c40019204d10b124002c850520f20a40c0365955a24407030f0400c1d0301104044411407018040801e4074182590314540380d074400d400000310b240c02c09440c0c3d89400b03852000c8546408403204101c0c41030301d4001036010304440907100810504442c043e00001d5001d00035880b5050b103c0070036194a148240824543c03100d010381d0507080400108d001c1143c12480886035560014481408195158464200c2561062400b070005041041520008400dc105200c840b800203101207400d003400b091203501c08a41d00c104a50000c900d840d03600f000c410134001c6210740350078405c000c030020701444150303484000b990b05008000c40d6a6074407050501c00411a074012f4000320004e000c40805c00c0c0c81d0340c0001c1c41c0151108081800f05 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 478901978 1250 478900728 478900753
    0x110403080a020f0f0a14010c0e1228121b020f01030e06070903120201060602070e0c0417151b0d05150a030c051005040303050703081314030304020f0402030108 70
    0x21035110701042000c600c21010041c420080c24003003a400000200050721010089040c0380c855040040102e00450b4501154005241d0b00001d502c000701d0b509403694505404500a8541800441e0030410450710210803211030021504890000c40c3c0d114034a01800f14084201c121115440b5032441409601c1c1c0e07150000c050301d003030b003408a03141e2f50500d00458001030150480d0300345a020380b11003001c039024003014010424110704400d0340d00c01e00c0c40200101c5140040003948d6540714855600d583c44800c01050070359a40070f0480c1e0140403503804966070b14004040240c0d45200003018010004282c40224030041407401c0240c008880003c0c0d09800e0010190364800140000f40c10b0401e1140c02415060680d00d4072005c0f00b005500811a070b050540c60700051141860b42c030900039041200400c01800007a4205054804079505480e00c0101c50355040704a080c1c020000101038458000422043c04c3d03a10008001e41c070807031094507400032400c0440c00344402d0340000e004540c815009409206003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 478903228 1250 478901978 478901993
    0xc10020d02040317070515070203070b1015020d2c090a090605150a1a0703140c0102121e0f07030c0203160b040b280f0b030f0303060112110403 63
    0x14840c0011200619003580c0c1da40e101d8188098a00001d5902030104580c42809000e00401d06940c00341140304810b0300d0324410081d102d202d0803400528454440b00400c0c044031245100c80003030000c4e1038958901d402c03c0b00003c4d503180c5a800155000031500b9139800c030700b0b50281da40460b0218620b440c0444803c04002001410b0000510504402c0d54400100010500c00c0c0a01ca00071141d0030540d084120401d41030081040a507005441d000710b00001c01905090f00804031035072682c140c0340280008105c107d1004031880b0796103401245600210b20f401040c01207810950080d600000003e4003a0a401d182d4030000318210344464200c000303880041e803c3c41c00f03034000c070100300c00d5441600e01d040e04003945003803002e10a20003583c400c1038190400c002c01140280701c40c0c01900b02c11154030340c0c80701d0400d21864650702d43d1035070400341d488060302007199905800024203000000c040e524900710460b03105903242c00480304036001071142200c458103001c40340710f20380f02d500344410090714081c10f6441d00312 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 478904478 1250 478903228 478903237
    0x302181602070b0f28120b030601030b0619031b23030d050d060314070302010807021c0c030905132702030304030611130b1e0412030806040615050705010609020c1002 73
    0x6618100d00d100c03c0301d05c0450821210a0902c003500c511a04003141710380710084070012010305000358481001400814083e080b42c65000c0da045440761301c2c200b170560300200000c0c0c16600041814540c45010a0a80308510703400041e80c009042445480680b4070131070103200c0d5051070046d05904183c803448001d5106500030f0040c020041c0300854115500c0d80c80480006904090701d0154000f0321051045603402407203240c00c2103441c4002d01800c0c008482200800c0c02e1040e00805201e04c1c02c01c060308041c05041c14000401000301003003a0b01c10275281c1c2c02c001c0c0444148002c220600645480c1c00f65071110450102281c01074010344c1000d00b5075171040300900b0a00055002c9141c24407120a046003100109000781c0007030186075441d462941e84406c4c101e03140303020907100590240014400000a500c041c511280c051401d80aa9150040403c0052000d0b42200404c10031040314614525008002008020303c0340008202c41607403044510200d00a40458400617040b903006101c0c0001350750080d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 478905728 1250 478904478 478904497
    0x708180a0522020c0d020309090601092103020a020d052d07090e0307020409352b02042601090b011206061e030219050307051002070302181602070b0f 66
    0x10f10303020002c0352562800000c01d40c80401a030001500388c456043c030a5100e90481420b00703001c140203040c0409003042d0740c101d030f07852102c074542c2c030840d941814801c002141c2c009402800112413500c0600342662211081074600d000f251100c5a00700071022603212200b0700300460f8000c0c01c2c1c2a030400d1290400340901994445661200b03004450150396240b02d120302d143d200c0c03c640030700f40050480e901c03441c61007c460664192a0b65000743d110010740c50407190300d40d020b0003c903130f02c032103100302590720719003408039480211440840d01041d5200c04003902c51443c02409a4100f201c82014180c03400e82d1041b4070010b011518113001001600903149641180321300c074034008100a91100002e800c0c840c60802a13178a100001c030010025070170400710008140a1070541c000003903090802082d5074415500c01d5031b000b24206021400158070078088240650750041c014220910300940103d0194400c1d103003201da80c41e110490480c154000181301080300d1541c40e0060402a500070141215001041c12 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 478906978 1250 478905728 478905731
    0x3061903020310051009060311040504022206050a080111070605060a0e0702060f010b12040206180607060209011407030e06070c08012c150123060708180a0522 70
    0x3100595050100768500d110128000490317190a40041c40c03030084650004018600d040400e001060350a07002161681c03061702d0105190703c0300c1c80440c07412010103080c0254031091751120108078030540c10000880c0c1c030880e8456580303500c80e00346a00300d800320300074903410314810441000024107a4000030360184000380f40381c0b0f01980c2c074044200801002c540910058000c0802c20021030311b52000d40d80904503484a1030300302280d5440050003c00050401313442007401050044881014040400c2e00d00d07809415140c03110701d203180c140701940014810303d003ca503040581340c01d03203002e810580c0d256035051b9540c0c60000e400c80c0d080c0980341c1e101040646100440358004070380008240200c000b000400a03041041403815a241d0348004040d03015880140c00c03150150326294400410035040d1003080851101c1c000b41c480100401c541c075802d1050300500041910030a0100307500c040c1c082403049500e641100b044520030410450350b40d0085560011585840b00d02c1c1d032014514038184403249250 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 478908228 1250 478906978 478907029
    0x29030f090c030a0302030c070608040f150e030409050f0705281206030f050f0303090c011803140615030712110a05090910140702030406050715060b28050306 69
    0x20a05010710f140d03064004d0303440002c07040d0444208010500040c54207180c400b0107030600c1c3e40d070042650240c80024240c40c0414400402e440b2150b03101544000c51001140d9031550385280c110085c0c00c00b254011100118140040c1400307001d201250070300d581c545840b0700310015603040c07405820007203250070b000c01003d84442440e40869105001c065809071003072105892443ca04203140002496020050307800610a0203004940000c030342e42c90400900301669032100d060707405c141d1451241e2000c0e008094601d08000180408194203000e010b8196401036118000000d042da20040b0744562030a090f400c1107464086603e00000c9230349554014952105035690348005650010b05a40c1a5a5074001e82c0340d0000c2c6440510802e5000c0701c9038140418503103401c82000e0344038040c03442071000740180042c4c05002c0008140640106100c000001c101403521502c0c44481a0096441c5c407088400c40942c0c2010060220490a0244541e13a0f8451540e580c0d002400108503100044041c40c0c500400d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 478909478 1250 478908228 478908253
    0x30f0f06091a150f0f04180219060206070504030b270a060209041413080f040b040e06101704151e1b08071704080d0f0629030f09 57
    0x10103018801020389240b0003410b2440f800d1403800900c98038640b0404202515000c03c0d00d40d1400000203000441e40043c08070320003c190003035443e44d020002d503c0080b602c0440e40741c00c1c0c41e800a00598102e035089030700c203a17111507081c3c0d65445140070180003005600c000075071204004203e40c01903110b90001d188c410007d031a03142d10b0582104000c89259070041a6140207041a01c102007002264002172356190510b0306107a20380d16580b000c0540061400615000180070f404119401408a03a0703111780d681c0c3c0d40b503075106084041601d20385d01c240703c0c603000203490328070915113184030044191414030142c885035034090310340300b0300852828000d1b02c031440c0401c2c92a1400c6040e00d801161032010031450003071240721004002540c41c03901441408005e0000e0700703600065566201207030441c0010a61102c2c00c00c503000c0c0c040c03108904e07012410801180800d5a0a40180f8202c0c0ca00344050001c0c000703480415138040102ca905564128004c1c40002c407140c601d4031016400c402510260b418110100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 478910728 1250 478909478 478909493
    0x10e010b0f2203030f0c020a090b011103030702010e070e04110f03120c010911031c05030a1514040c0f271a0403053007020406080609100e0601030f0f0609 68
    0x2084a030b4249200807800f00140341e04003080c030b4600d481510b40041b070a00c4c02d90014040c0d043d03d004015980d5941c0c81c60b55a50b90050103544080c09914003100e440340382603d4024040c01015146800a00a0a40008070b0203c0c60b51940e020750703070003e80c1050101c0d6000c14050740d218040d046990501c07845071042d41452580c0000d00e405000c07800042861700c0941060080380400c0034096011f9030000a1054040610002c84000e181503844e00311b540f03445448080d00540000502107001c5543c8005c00070340400900c0d0a80030f41034042e00d081c0b041e4a188d540c1031390700e5080140c0b914041031001c0c21000032040440b0340c00b0030078005040002c4903e43c80e90054106500c04040c1e504a1041c00035041c0280402084007610b1060050600320360540c7c1d08648003603603042a01c03013080e6440c003c501c1000f156030742d4000700c2c00b815500701254000d10f000c05400d80d6541c5010724070f60100d8603015400702400b10100da00e9040c0e940001c02c01c2d85c404c0b40759035500307089c8403028000e55400340d44106402c00140c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 478911978 1250 478910728 478910767
    0xe1909020d0e12040302060715020403020910060f0905010905010509011106010e071202090d020409020d060908031608160c0804080106030f060f022106010201060b2d03010e010b0f 79
    0x354000210b00c0c880884071441c141a440001d410320205000400050392100304030760942da84040903106020a1140f000c003c0d01031034100a600910340b208204010300f80e9407502e01119a640e4441d0054016040166490501806007500140035203009201550080c402052002d0703040c0741c144c02c0e40543e899000e00340117003030300f2001074041c01d070043c484000e03403003131041940e0010b274001180b0f80001d0300005090380641040080c0070302e40301c5140070700b59a03c081210850a401040621403076100e894031720001e030310440c2c00e4042440081c100940d907a21800708584910700040c1080099610001e051310b9100d24001e080314203a02c1000003049854081c090480290301c01c10229610b2003840c034003a4250303685000e00c0c2400510601202c0b10903500d501070070500001c0d060010b48641c40d00c00c0101e0240c500740e080303440075110000704448098403860540550100040490f1101c0105e1a07820030310303100138440d01e007178150b0140060041a00010041c81e084d40b480450515281d4400e100d0030120702d2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 478913228 1250 478911978 478911997
    0xc07030f0c0501050a02060109230f0a05010f0b040306090c08160503010518060a0e0c1008061003060302060703050c0703170a02010c0f02030a08060312130807080d0e190902 76
    0x315896181080000e2800c00e01420090074945d007801881c4100a40c0e8200500c100034002c6e8507940c210142000103445040e441650484047c8281342c43e10b07484004d0413060f03411402d111b25000000680c0780d8101207010584a50000043c80c09166454180250041e8242600d07000340302c09000a9540d130801c42c040e22041d45c140380801c3d0502c2c0030201400c49a00034002d4a6054290302c41211828011aa099003c0540900007c1444101051314500315910507455001031003100301d42c3c0c1041d00030704480c2c8500d01c00c907551000c04000810840070758003140310094000c0418080040042d0280016180101407002119106952901da000e11682a00340421a0003400902004100d0707083c007440d11200c01038105402d04094a600c000d544e072041010a00030440101c0200340785075400e1140d0704c200c04042030b01684403480c8050410b045081071080c3c1c0344910400e4000070f8443d8020070121469052038499508000c60081840080d410701d00e06c0c1b8445501440c00822080950700c040c2c8070741d01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 478914478 1250 478913228 478913243
    0x307050a0303050901150620010e160503010c0e0d0f02100f08090a05060a090312110a0908160e09010b22060b070b07050913020a05070b011e090b060c0703 68
    0x14450038081c007207800150000626074100001030b204c003805411040211403040c0742000300045520107803258a680c1c4010f044555080014ac802446000140c4d0f82000900034408207100755288101400c0f215045010400f0400444150115241220072044804e004050310311440c0010f500144806404890250204210522544041d81d101000075400303503519004206e002e005440c0d50741e48280003000e4250003501c07181d0000405100d0060720401d040302030010b000424880503040d1560b0007400d501c00008140c414006081040003400b407030003210b08040000c7c41400e081d4412849100209628019034941141c000551542c8009032189031452044443c1200080b00d07902c241c40c110351144490810600040c004511508209a0404041c4c24880d64034420200422083d807030407190350082c0ca1001c242c098402d90071034020b0000c00d111755441c0030180e0b202e414000c1c5541004003a0042900d03000c5c41840311075807036807042081d0079005165500b080410458031b0b2900c0b1460b0000c84018 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 478915728 1250 478914478 478914493
    0x11120a0305040c0e06013e1c1805010507020a05101e03020703020303150a030c030b0a0c0309110d02040b060d020c010c0e0306220f03050a080105041e1d030705 70
    0x110443d10540508105510f4060340c1c1032420008005c414080718000c00ca11403560030640c107007001c2c9100c0050852070703030b51000180c021110844d01e80c1820b4030948110404000031030891403150303511624060b03440d0044918282040300455054000120880e0401545040407503641d403401c0e000c034115070659445000480c480462174030410a50030750700e0706050041c0424800031b9004810740f6800710301c00e80c80e2010001040c00281890182c1d601c0070b42400303e0054040107020a07145142d214841c07602c8244801410010210111040710034050610004018000c10f1840d244020303604190000300045030b190070300c0c80000c8065000100300483c4076400100b600c171112003030040520044030f50400d09002d840e07003070110b900c2e128001c20310480307184280d0b00704841c00e00c2c12108498464006003030a01c070304098030700036020b90312070740348900800d030a01c0000841d440e03c0d01501c209110700b4103c807500c1c000075401020103410b2100b020b041900326038480e290391030ba00300080c05140b8003890051105 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 478916978 1250 478915728 478915733
    0x14010f050f04021f0905190f03140105061c02040207060f0c0201020c0c09060904080d021c02040302040b09160e030307120302030f0c030405120c1005040b06010e031501050111120a030504 82
    0x902071000000c002c1d00c0c0d684c20020310441e0b0442d81010440342c0c1a0760801007844080d42030040941203030400640c050a5070004800e0202e0500145140f254541c0204081e45070710ac100300c00c05203140d000002c841c031a80502d4005042680113025440d100704808240364002082e81c02c280c900c1802c0d44001070b0750101304d40804040410000f28a00e0050ba05e5620034200000407480600c4000d1014205030000540c02d203014855a04503130407415242c18506100c1d0303003c00404007030b50241c4800c0e131050781085140401e0b440c10b050381c18055504000c0034800b900120900740c1c1e62107108103082d58140030030300502000c141c1400032416135802c503980041e80d034900301450000050b00640000005d202c01d1040000003840065010300b50740c212602c10fa00c80c1c101e0b00202d45441000340528a01a041c03409102c10410b92580c100e000315002d032128203c0340026024542c0d110514100b010720010300b100100240d5015a062400b17400d6940300ba6107000032008040c4240d0341c01019100c00007680d0700100001e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 478918228 1250 478916978 478916989
    0x103020d0f0614011d1f0c08030103060213090b0d03030c02121303060c0c0507090b06071406040b01140a0e0601090302030d050c0705060a0f0305060f190302040c0f08010314010f050f0402 82
    0xa240b1050170641e40c108000b0041443c04800418003440300c91000312100c81640204010020b090348203000d26660b42e1a482d0060282d04a2100000000c070450300200300c0c440c060144050440001d4401c80d61848251001c03030182000d40c010340e0542c003030408000b2596030141c000f0051109910680c1c0f50345861480c05501b20340006608404008941c00700c0d03c002240840c1e10f504481c5e528001103078042c0701d540041e01c0c621a050006102300c400c585410b11056010030140d201d02e0243c22015101c0e0b903909612003141c5008010319070b1112681106103c0070881182c041d41148061400750301407920380c2d01091518260301140000301c0c0c3c0210b2a4070f4507050401145001d81400d4a4507270810403190fa0107841107540701030090a05486000207100d548555404e90070101c0010b00248040c4103600b12150f4015050000703078002d900b0f184980c244180103040001456450317503a1722119a18544441140440450140441e952240c0c0380300c1200d0780c40d020740c50141e5201c0341403943c1800e10740704004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 478919478 1250 478918228 478918247
    0x6081008120316021c11161d090a0b07090905100614030a090510020406140301081c0c0f06051602060702100218030a06061e080c0103020d0f061401 65
    0x801a407212040700c01202000064940007040602c0480800a04500507414100155103400c40c00c401e0f8030781310a115520001301003184071100192080c2550f184640364181e0040e000b020441804038aa0030b104002078141c4960050b0300748241c1d024201d1942e21007603000703401e6406030000361031440f00380401400e520800c1d40014004130309440311882d0420150024000040a20448202100007910840039070002c20107190b004082c0c0d09040034a4100800a40083c0109800101081c020300495555070045a0580700c1c404000c00d644032209500c4450340d903410baa100100328581c148070340080d20303d59602a4580c17050101041c1d602c1c180194501d800c0d06c03c0e5480045501100c284400141c010a40c10959a000d03100540d07603a00b680749450b15500c00000194141c4200d051503000d11070b09502c40400c1e103015520355611416408100300000005010f02c0d401c80d0440c1030744151a6009074000c0260b40000744011500d000e44991f10412901503900c05440e01002c0c041d070031540e6900c20b0814 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 478920728 1250 478919478 478919489
    0x207080304030c0512060609072006160906030506180405100f02190216030b060d0807050102030a0b0619050904060b0a0305091c020712050f0f2404050a020f1306060810 74
    0x41106d498540c0c00605050005010701090128240e04100801ca04192206204e0031000880f061803c4c4076840411010400c126000068990307400412424840e0181500401c4010402c0c20101241f81c4001e100e644064803c551034840d8200c8022402140d014401100c50003503401a101d0610351610000d005071280c040c421504850001582d140c200b007110410b581d000906d005107995290007103104d02d020528041c01e001408901881000015001107104115082040c044006a04103001d854020f801c010382000b0f68103081c03144554440d02c09441c441c000200b0202d8003540d0340480c4111640400c61100c0080d4841e0f0410010540070026252645500c101100d107030068594000d454022a001d544001442119035009003d020844005210040c0c0c1c00d03544442c620b149016928500000d051842c907440c260340064030746074090100d10807508103000d0190200c3c194201720104403030030101a07218a488500304003140842c4107182c0a4803581d00c41418908061a12450f00441e59209 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 478921978 1250 478920728 478920733
    0x3020307090203190c0504050402180f030307032106170313061805150c030301080a03020d0203030f070e030a05030a0216080c1c03020109060504081903050c16030207080304030c0512 80
    0x14003480c030141c88005078413a140b2040005d04642c002000301c1e011320a9500a80e802800807412034403000039008180c00c042000c9440081e0007030348030145522802002405401300d00106040141c00c00e2110280c8140c1c07058490008181c0d4807608842c21000c2c00f80240e040952020880300740c100c0c1c0702481d10000d411503052000403220308031141103140d03016001d42d0f070098a00c403080c00189c1c050307a03050300c0120110800352074aa6071541c000903074400a030107084c2c00603c03c407095500302500220803240161001c3c2408040c681d50f0003000c2e11900c1c944c0301201d4040c0700300c48100c80850000d0010b003c5041c4694040e021304c50311400081e6048405401c50f00468111a1500440d6038404081c91140c2e0400d8540c4074040c09036040a1b170040500c44030280440307081c80c04000c204804040101070003100380680300c840e1244e02400702d049540c12156080f00d50b104110185602003204240060036109104541c107044c1c40d2551a401d68106900480320030302030318000d0120b0f10f0080314034141d0140031b100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 478923228 1250 478921978 478921981
    0x120a030b0a0302060d111b030705120c031b0a06060605090f01031e0b0d060c05040e0f0403020604030e150c010b0a0e09060112020a090203180c0d03020303191409030403020307090203 80
    0x41062107000070b45007034591b44024285600e10b5801c1a607030060f034480b085070010742c0c01e030002c0c130b0b12a0b2004c0310465060040414030000b64a00c0c0064417075280380c4a008506048180b824906000803540c0e40c04607034424180e100300003a0590080c1e0b0087d08040e502c6a403180700302802e0180804010070300e103040c0350821110140e07442a280840c46c04c562002000b2550b0560017011450500401d800580f00600f0500800c10b151741000080086404159051101d980d0341d0079488504041507030700a0041c0c01801c08100440e1003514011100747c80108000051046600d0302c41c0c5a502800301c145e0540d44441504000d031074007011440c001d1143c1060754040b85807521b00300361a00414080c0100401c40090308006540b6241001805032620070b43c110341d00d0424a080984400301584211030038462401031001c90300704051000003860b070640045080d0344401841c20b110540c014502d0f102d0380d684018484078408004221409480a0781c00356551340d00314010715060911036001204441d00410 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 478924478 1250 478923228 478923233
    0x30e030c06030a0b010e0a0e0405070b0f07030c0813090b09010b030c1b0705090f1503030a120b0303070b070c030801080309090a09030c050709061701110f0318120a030b0a03 76
    0xc00700c9034000c908440004040d13400c2e01c01a00d00382c4c488010b058108198410210705084958020360217240644221540e556031280605070b103208400380c1115000090040c280007a018020502020f446030a01506200481c1010a0b00240e150f002d103141903140d03600c0c0100b40c02c0000c401e9002d400a02200c510310715210b200c1c01c4291240c105003038100c001010040f00d1008041c4031080203000b0041820195080001c4000d04003081546c061070125000c082583d010700c3c0000c201e4640c401981c644a450641a403045002401142c00980d018001004508002004800721500c210070b80d03203502d161101241401040f500b03050f00001350b50382c8104140c00301d541d034401e52640c0c408090300d07010806c0c1c0c1d103c0c54101c45401320f21200400d903200307000f80420403400f41d8010702d051700c21078008402ea10031015a00d50980e5601c1c0c0c1104040102040054440354180c001142e00245042c078101404030720142032450080d901c114110380709004a42921419498003031400d200c4004c50b0321440050958 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 478925728 1250 478924478 478924489
    0xf091512060d0807051506130618020a0e090112140c011b05010e120d0b0603011202012304060201050f01080c180907051f0314010f0902030c04050616030e030c 70
    0x1600d01d03840b8102d540b46000402980c1ca08894406901c035040d00c0740c035030442c000301c0c08040c001c4d034060b44104007a2030503c8d64000703203109600c201c40d4440751020510360b90b07013040b44c0294824580340c0100002100440c625844242029009100300d802c011100052403c0c600c80c8104902c1080f0190b0300b00020340082a0380c00f501034210034102e20309032038002d1450300d422801865040c2c40c600b030138012400c404258081c010044c0403911917442040c84900004000c0000a1009000b10081710443c1200f11000d54881c1c02c1480750504280c0000c008200c0d038141002c12038005038403000051391110100500a41d1030420385004102c41d200909070000c0c1600041c4a2340c9440e441044042c50b40c1000411034502001002d0041c40064061440f544400051354008204001140082400c00d1121780858045000032030403280c0c5040c901d81d4076401c000c6031102075070001d0244004400280400701e1a0355401c0010110000b2408100902d6000c5240281007010308091180c845c5e040b4024010701e64588 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 478926978 1250 478925728 478925731
    0x80703120509030d030506090705041d040215040b2a06150a09152907060209031623040c050a05030a140106081b070c12170f091512 58
    0x4525031801012034100211014003682c0401030341481504a85042c0c0c5806900090040c0c0080e01d0807aa10361340c601c02580d491107244117188940355102c1040c8014103903e40001d4120b48000c00c0c503500940109009103954009421150540400142700f1032240d600e242481591401c3d0119426501a5100302903126100103080a00c465075501d0040255078900320f20030701914891504120380b03c01196200c011280e640502c010010300c81209001c40c125103541c40203021600c9404c1480c001c5540c2d00c2001a4010410164143c4180c0c0903902e944917400110034050001d40c0034a100c8180e80f421404080c0a03000c00c0180664030303111144032401c1d03000040f10319000340d500340291769407100340818004146a5981e0010700d40b280001144e0282d2001c0094081c880042040072640c00c030040c211410702c54160001e0501c517100a040051100004144103018090010900074140741d05000d42c4942c0200700320300203208006842d480701c2c0f4001c0309403500c41e0041d40105051921403031410306400d00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 478928228 1250 478926978 478926983
    0x91505030a0e070602030405090c1303171215030c09090c0402071e03111506030c01110f0d090602070e01050904060506031c0909061d0c0901050f0705070806010f080703 74
    0x1000000100c03a01090b4105152461140003200c106603550b03600207440340c01a0240031f20030583c08000c241c0c2c8001120a0b180c030729450f0b0740703030211542c80d40d42e4803c26608001142c034015002400001003a040018503144150515001c0d4401812804101030a10321a040214070404561040c00306207113000500c5609a18142c800503524072007030410b070b1200281714030382a0407048140a81000c141d0701c00c0f480025071541c5021641280c085820303100032001d04584080c2c2581c000c0345480c00d907610495221603810944410b940c44a0380006649040034000561100481c500e01000c1064581c1003011800420034100d0f244000d50502c070010791003460180c80175040a0701c2e02c02044d8a568144041070030f20a000906242150281d100a000d5072614418010190b18280700000c0303030310010752408019903140e40650307844c0d0388444032201c298020031416810841c040c0044a13803042440c0c010100b080c0510000c0c52401d01d0700700720b54076210050700428940c0e080310004000196001420906607035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 478929478 1250 478928228 478928237
    0xb10020318010e2b021512060906120f0c1302040503030405042a0e0f0915191701060314070302060d0e0111370516020f06030412020106060915 63
    0xc1000050000c01429044c003160000d15407111507003040c1d4615141d6aa209541801c1d45054200d0f01d641607004510244100c009410006885032070a1840319a01c24002030000c442c40d648805004d1502545000b0300d8144e5111000c0108140741000300c0c80786141200000390301e41820103000c0b0b501ca00852003803901440c0c843c268156034507606e01c1440110700c0a5203482541c1c041264000b81448034000a0500900703860407641001c0c104001360900c1101170b40c101c50702e000044414803010004ca400720b05400104040040b03040c0c4200804400003414000000c9140350850800c503690380541c01550000c2c1e4414402000181c4071401621908001e00c500058002d581c4c1982c0341c090808400e41c00c00326031000442c02082944400d20640e03050001051640039108c00d41981c0c030074a01c10042e10041170301408046507070540c002c0c20305205031000e00304458529600001c6a030f25001a80c044817100341ca1182c4002a0780d09101302b6009103034514122705641d1402c1c103d8014488034004580400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 478930728 1250 478929478 478929497
    0x61424010c05010e01110406090603020f0a080402030a05010c121d0604140111030c0c1b0a1511030c07030b10260307050a050606040b011e08040f060608010b1002031801 74
    0x3080a510615513058404000e1000c10941e00090402d540107005e1800841c00c0a4000b0030494424800d80e0005664002c565180480b402030641d0400c00040080b0780c1845401c100500040080c000d6800c003a000e5101c204d407008030b2480d800140c071440092800059580030306000300d07041c00a0000c0d000b54001c101c50b83e00303030210303030702540545100642101603400c000103001c0300d482d8090040c08507100040564001c01390020005070200c0c910362885a0140460382c05100e685001483c040c40032066052006991850143c0c1d1402c40d0054405035429420905041007030142c21210786500002039070f0985002e40c00c01e00c2018045544100140c4c2c14074000701c0d403600000c0304008850750720360000d0440d8400303101032400a5807000c0c2151514050740c01c2051104407940141610303110300c0c0d410000301c0c481e48944130302200c01c0c92004105880700c0c42301d01c0c8400081340083c0f0130000601490400403c3cbe0140b12418004490007000e100c00455000704498965004004880c042c40b190918001d0802c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 478931978 1250 478930728 478930733
    0xe190611070f0b0615120411030102041e0905060108190903030e030d15060e06043c03050c1203090f06040b0418050603030c070b0f070609061424010c 66
    0x6a0003040802410100700095507024003c0c40c440c2607209100464002800100c146040c1c0e0060250316994010b45001c80b0102d03001030340c0e03058189800103010780018109991000030b45080010440c2d82c4194818001091180c00c0c6c0c0c2d805040e522910a00700800c96092020131030919540d18100f000380c05955000400405110b900001d502d5a030701000c4907200c9109030740311002000600c482040c1d003200d42c42c000814502858489054075030041545040501d0708d80501440c1c103421104000304182c4200041000c0349a071125405414250070070201c403030a502e0311500c4c01d1501c42c3d44074455031a04000b018105800030403603a8408095400c90783c80040b0713802250185c050750700714080415021030003050750b604200100100c500702602c103015680760700381890b440c1e104262940c40782e500821001c2c8038510072180100ba411a8281006140000c0c0b600c1d1101102e00086040325400e03103900c0c0c040503900710500e055400102c0c402000d0402c074020032051403c0d003150703001d150601014038100c005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 478933228 1250 478931978 478932011
    0x1314150c1504170417150108070e0919050a030f03050c030115031e0c090f150f1115060910050627120c120703050607120e0d030f0e1906 60
    0x10110341e80034407139103443d140c00403000d15100407048407406104124081035030b10075a680090407122014090450b0904004c40b00d01429001400b104040c030410341f1095800e808140a51005c5005002500709070155142c01800c503808181460101030800c01030200c8040f0241c200c034110754281050804091111b102034001d131012001c41070b0040941c2c8540ca441d5185608003504e00d5415036160000a6120540ca01c2c07900c03420b00400300c089803404d6000700668000d4210302e240a900381401c0c0324024401e07000500c0c00f01c1250210003039050100a000460404160b080d80112500741c444000c14100740103d8118003030340c0702050300d10140c1558002c004001d41d5104c00c80c100041c0403802c640324440e009660b198107200009010300b1002c41030040c103040228618040c0d075030000181c0000e44400780101c03610324402c280349140ca81d03505c499034036141d020002c0072103583d0a62404640301d010b18030b206041301c0e14070b042240c40b50441c01c0d100a5080d4012240c6900329400403002401e03401c140741142 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 478934478 1250 478933228 478933253
    0x509180a060906021842040b0703080703020a020d050a2307050d020d0c0222090c21020a090213080d021b01030c1d04021314150c1504 59
    0x405040c070b00342108051002d103400904801280c540454034508441052240d2854035003030503500c40c102184a5290712601c10307409611b02552080d00414100f00210300341c1540d00036400710650100001e0660200368001d01d40b640d000b0a00c0c00c1c1141042c2003100040c8d259002000031108100707001600d800310700c2c010021548007095250384c00030003c88641c180c20150b40402c40039100d5110fa5288111301503c001040c0e000c2d03940c250740740d41a100c00c503403d2120710b01c031082218400c0510040b81941488142c1301c0c900e80980030303e881c844940e192281141040c1c019405104a07100c3e910a00c03000358403010450411101e41d18401a81c56081040d652680a03541c0c00841d5070307000710101094010360000306100d4184000c41403070048a0741500542c00c59a001e0701c0400801c9406261078603000404401e540781c420050f002500e0000b854000110400d455002a52507184020340058641422190302c403001300f01024080c5040981800c845c0d40303c0c000040b01003040d10b058002001c011007083c02c00d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 478935728 1250 478934478 478934483
    0xf06120a0204110f0a0215060a1809020607060207060b01172818050f2401030305090301091e171806030403020106090903030b0118031104020906040f0e011508010509180a 75
    0x90301e031503017900c0003502c401d0725204456500c1880404140340380340503280102292008000307802c04582c2160440c2c00f82c42e40800c00d99020405200890202e13045000800d04280724090008a00d44a40009041042d0041c01060b000c0103120411805c08180c1e040981c0011002414200901008110301c000d0900342c0311048400f03848001d1841045000035056414403500780580320030340c004a5006c01301c080c0c4911801a4406c81030010004a40220010700f58400c02600102d51070740c20741c440e520b40380c0e080b03d51054403d60a182d0310050286040f6013041d6100480005450803c2c00300b000b40d41c48001d149094407411000000c0b50406000f540907070010900d00100780288201824094000c1c59000ca00724041406d40c441d250040c10118039403000d50350b004010018400000090100940003401e0950b00810100000300e01c044801401c42c00800e000c01006140c1e60418404081c200c3c030f40f505503800c2c440401e00511441d0f071403e5960f03902c0ba084d0020310800450607800d0394038000504001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 478936978 1250 478935728 478935757
    0x2030316260316050304020d030c051e0c10030b1e01090305060a051008010902090c0a09030209010306020307021501030b06100306170f01060b04030f060e0a0c08060f06120a020411 79
    0xc1c80705034a051015511449500c80c00840c07180c0e100005507240d00c03003210b0003544200c0f4040300b00700081c00740c0c1d05442c00074000d0088401a40c160302c0c2451220344035601081c6644c0c07201410405034500100c3d42e400b44507540c07806001020386640810f441e156001281a45049100b11503000369200300240c0c401150070030b0864000c2c1c100001201d008141c203440b44d0812803641074000c647c2d5001400741a0803154080e103040300903510040e0809142e000f0f1403100041114142c00000580d036100d002e9800307103002c1c220060b41d0f41000c56020345081341030046200c00c0c072000001000450014030780950b10070340c00d450201c050b040c4814210003c242a410214155681e8119440d2404000505032405001c40c0e000700101a1240c002e83c071503000340d00c0700804854040c00b1b100001307891074100c441181c21900c00c0310410b5955680d084014011a00a05015030204040020640a151520307402400a995540c4101c620381019030701d44403082e002034046e54a41e00702d9150007002070220b0b660398030003042 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 478938228 1250 478936978 478937033
    0x1050412111c020102010b0904240b1003020d060f0e04030305070309060e0109031808030d1a04050118050c040b030c130905010f06021e0a0201320c150402030316 71
    0x1041003180b49007080980c015842c0c1032544400d800c022111500607504482d407002844841480c500303500008ac40354200c126240e80b600d802c183c4600b11b13100900c010035100580c4952450402000315030300c5601c9008524080c0404000740442c03a14042d03001130705403a012440b5134444606801a000142004241c54a003104c0d48c140c8803419480708810600c030303540315000c0c9450603c55034805075140c041d0700034580040010303684032203142d8446d80007620007252103451601c25000203004c980c4268006521f1001c404000c0480079410320401ea8000c280d01c0c5a14100340c2420344c9550103000003000b820704950f0002d000e60807c0a8041c108005000311141400f10f583c40d440c445090141038810203015204402c101103480002c1341d4400800302040005010000c02e9400448101e071002640324038140b00d6032004d140d540e103a055030865a00002200365990b40d08500d10514007000d04250111030403400c4103200060750040100c4090780d02150003039000001d00d0428040201e602800050746010544 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 478939478 1250 478938228 478938259
    0x50904061d0129010915030213170318010c30080f1b1b0705010f030513060b220507020d14030a0c1202070c080c0a050105041211 57
    0x8000000040c100d509041d900c064280296080e250392107180194898039044980e51440b59495850800341d0525000704c4090341c0d60b414091040c2041d290b640001d400042e01590b034518040440010018642c808081c44010001c1544030b0149010802ca607404240c45004107038401e0041188251304041c006464003600568100c800904112104c15404282140301c1c0745801aa00e079442002c14001520882d5211094050665561003400d1404241846003141586030f4005811540742c1c1100107018050034a0f0014280c20f042c0d00a07082050304050402840c0c41c1c042c080601c0059201102142d03074007000002032a42c0300181c0f03031b5030203005890f04c0e142c126100b2030308054007416254003504c4510710907003003c5a40e0120079101d10200f00c02000458000b14840e800440300780264600b40c0070078415240d0610503a4009282590090a0640240040c00e81403004400954040f12543c0303400c1e02e0440080d00c14022880741036801d40c14031860f002446102e10203c03c1038440185448000d01900c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 478940728 1250 478939478 478939481
    0x18020403080a1d180f0a0e06130b0a0614040b06161b09020307020604111f0804021504060c200402070311013b010e0303090304060311070f02011805090406 68
    0x2060541c0030240c1c4035600012504184e4503d182101c614001d542080e9505002190119000381500c4645035840440d1522104c080c032180d40a2106404500c0700c004403070a0862125502401008403145064000c100b2070b95548031503985d4100039600454000350240000352039000d0001020998280d5020f96000c00c00444141540b0002d08050032020ba41ca42d200b09080b07000481e84580560700007800308010440d010741d4084100c0008009180b1083c145210010790300304210803e0124144030144030071813828601c3c070800c02c48480451400e103458080300401401c41d101d00500440319221030f008a007505081081510100a0425503a4007801d160041510199450524040d443c11200c1c0792038103400064417003445140250840c7c40700e070042c0b80740f000c00c40c1c00b0a1003241e0b41d650742c0d914901c1c0000b480a180308ac04034001940e01d440c0b80050203020385e41b00d039643c0d811401c002c01900c0001010412005152902860005481d11290114080c41c0c0030740c3d001a640b2000040c2000308000d83ca = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 478941978 1250 478940728 478940747
    0x90221070c061113120302030f031005130605011e08011a0c1504170403020105030103061d010e061009060b040905090f0709061a0a091712030c0901030605030a0c18020403080a 77
    0x60440081e01551801c410101c000752085c02001a00100b11400e120172008000d55003040481c001204419a103000103041c80403901c000052041d01c0c1c000400144da040921412400c10711048990350218100c0c1c001d09920050084500b414840c000081c18201584140d9a496043c10215400414014425100303100119011220039564580100ca840c2c5943c0c25241102d5060b111541541d085995407070242038440c520b0400c010345418600c1c00f03000c1c2402141103c0300c207040a0412418071145c2100c1c00b012a03000b43c07a44908205080060980400440e0b0484e40c600000041c4d81e140e1990050909281d020141802d01c5560380108644000345d1042086070740c150b01d11100ca9043c1160410240104099100401c40400e000c0184401c1c4500c0240d05003490307020f0700c41070b0300c2c00c180c11815600142c1d0503201300351020034904900e50701441070300c002c0c200490041580003d10f80d41d00c00100210f000381d0040d135034201e50131081c0381c110f84c064502465006180700d444001030000102100b10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 478943228 1250 478941978 478941997
    0x309081602030610030305030f040206070803160801080c01090504090f02030d020f011b1e020c10200f0a03110c0907020124050607031d09040b07020106090221070c0611 74
    0x1e010045044c895001c0c664104480e8591101c0c0d007195550400c0e034658520081c4181c0c0c04c8401001014005404000114400e40140c80140011020420024409601600180c5c215449100c0d031046036130b0050041e80441d40c0881c0c0c0443c25220f13178507002d4641805080c0003509031245c0c15081941d00e80116070003242620300d01c020042c0d0002c10010151852544445801099070342400300f10f81c1c507265241000020080c0112145003078a9404940d9458100004000040441f224032001c40803800400001c48030000c003e000303091a02c800181c4410304014002c050112602185000000a0101000d424002800f9210a26118502901030820301c4001601c0200501d021600b0306101100c00301660700140c0380301d00707100068ad800d0b2401103900c0024003d550303404480507000e90368441c5003031290f4400c0c405988582040d10019081d2072241d048802050b0050222211118020505103911440e5a02400182e10340c000b05490100102e10054001030502c0c100e659034600e40001081000c0307 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 478944478 1250 478943228 478943233
    0x4020d1b0905070c0308070516150903090f08060c07060b0301020409022104080d230a0b011407030c020609010e030607030c0e0303040302090a050c0d0903020d0e1e01050a030908160203 81
    0x58400c80d00f26130910030030100801048154000c600c4061040f0040c2200014010010700d000410ba00d40c3c2c5200c800075102e2520702501d0f09860003c040d44609080001c240d49c00d54005c2060802a500d5140d000c01040d0940b043d0000c80ea5405002480d0001d00c4d401101900856a582d2107200d107101a6019003440b181d4142c801e080e10005000390303400c142c804d030f400c00540d500304544a40e040000c2c100c0c1e0720002d0b80304003c1c0c88581c0d2203800403840c003a00440040b0380006050900d90005000f1600961515420745418003036030021a0704a41402442c9904036038481e0746101a500580b03032082c4529070650548a21010080c406070543d00c501c1c804040c80d1140e4440900c02d8003059500d1007140402074001c428007001c00c3c4204196084990440b05403a4690308240c65002000111211200c0a03001603020400415a8617004043c2202403113003515000c07516480009642c1e051400750561a04200f0006001e0304154420382c02a440c003980b020555646280c0030480b92020700d2551016031090 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 478945728 1250 478944478 478944481
    0x51e01050a050c07020102100b0f03011d060106023004120c240c060e0a211701270b06040b07021f020a030f05090a0e090f0304051804020d1b0905 64
    0x703000c0402644c204030340c1680103226414130380c4101780160940c0e10280e0780000d01062a1803079980d080c09401d400c45902000100e000d900c010081d441c01c04180e00c400306640282c0310210120100b0020030700d105903516503120045030700d821442c0c824800d5a01c400c50300301d0501584010010300c2c00c081800c030f41d0310000e1441400c0c84820014440d0b08400792250114100c5803280002524a40000030081ca422040d41c00c1e4501545400e5192039820b69109460b941401d80c0c1c3c440705401480c1191498001c030090302c481d6043c030f00b20801840310303903240c44040904841800031514443d0004412a50081c3c180c58603681d5494881003680c001800891003109034180c0600c0c1c0d0505500c031600c0020442c1e008001a94540e14151112942c4903020310800408000594054940f4050701c401400d221081c0e540600c0c005000f01c2c100103040c000007a0700c0e08200410013030765865140904502508a0500800343c03a01d100044410390f442030020210800c0e50302034100203260b080039404035041000d02780711a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 478946978 1250 478945728 478945741
    0xc080106050409050a0e0a0b16020613030c0c09150e060402090a1715070903060b032d010209030d0f170402090109051503010603050d020d03050c16051e01050a05 71
    0x14240184000110144010495403c49800440d00a54200400200c2e400d81c142000d080c0107402e0001e4071180340f00c03414800101240c0840c11540c10346803020b81064180000c5c07882d0000324400740501002240e03103462052012001103000103199108041084c954640c1c0340c0e45500009200ea2a0000c03a070b04005421400c080c000c49141c480c008000d071084500f409820f100100c80391700400c0651082c0d08010f05c0c406c0d055201c03240510181e882d81d0004e14034618100c0d0035106410000e40c00380d0000240210729603001d0000010880c0070f000406082d102094199009000350125154540b00d9001004e01c0d59410141104a20185540704061141803e440c2d03e12043e0aa0340290049810001044401040d52000d82c0007200c00604506045103180001c0c2580e0b00c079041a01d0703981180002140058041055006008060406000502e0802c0409009010b2100c940ca00483d0308000c8404024090082c1d08403212041100d002c5114007401090003800d045444e00c000301d142c08003240780e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 478948228 1250 478946978 478946987
    0x904031e021e01020c03040b0c070e04111c1101050901030e100c0e0a060e0409080d1d0106060c0c030b0c04030506040501052a0a120e1002090405150315070903080a050702040c 77
    0x1251a040300111f1a2614002540c0701c3c5a2000d4003003403050103542804581c1d90311003000c042c0a0307805920203900c0441d0001c10000f4241841d107903403003008244000300c0c3c0000c13031032883c00d40f811400b401c03c1ea84507100e010058000c2c00405480d030680d0b0040e003401414003003a652040c2c03001c0c4542c0c3d641402d010004820b02813010800d0103034001245003a042d40e40d4501e010707004000f1407446025800d040c81070300100c581c280c802407070341c5018144042111000a90302442404020185403404103c0c040c8951600b08084030b050001034440c000717020008840e5101c07542141d00a40c0d020040b91031034500781c20850300800701516044074003c0d0090410b03210455030140c1c103203480f400300d540074a0002030748029940405020448903806840743c51220304c516050050580314200a40e006d44d076285c060b0100022100001c2c460f000c00c220503440e51601d030f2400640400a0940c0d264a0601c0383c5035024140c5400b155035100500e007000000b0030205403584003001e888000d01c01c0d0b60a000e45140204140e9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 478949478 1250 478948228 478948237
    0x21305010906081b040b0a020d08090c01170405072d0501020307031d040e030a020c01030b190308071b030c030308100b03130c0b0a020a14010504050307020904031e021e0102 76
    0x2580400200324030110f11600304007450078040a45203441c1e0f4a082c000f040350440e1171f1000140c3c1150280c0e040c40d40e00015080d5000704c0e880007a002683d107034000a003003100c80d02031780711180201034002820020200b00320740c09480301c5500e58001c0f002d001e64101d40c00490303080c0c100c101500e1600005442d40000b098906059151f202c0000c01340106003038000b180c81e080c040b0360b80241c40f805042c064107000e0004080700b901a50181501d84580000902034517000c2c00380c14003070700c111142040c0340810715a8107800e82e030340302001b65640c000c5800c04050b000c00c451410500c0e81e00d0301500204101d611849241107a200e45c17641c1000c0e41e00c601c00e014924000f0310448042c034804000107025000080458040c0c0ca20402807040c00c00c2d01ca88241c1500d8004e00301c03030000340c2c0c080c00c81082407000800301594218080c500038400781ca8940e0310541c59020326a0003c0c000c170804004502054011007070912240e440101100c1d85901c00c0e031700295204800d64650441082850038490034900600845 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 478950728 1250 478949478 478949489
    0x12090f010501030218040303090f0308090d020319050304050a082709090c01030e030409090501061403030703050a03020d0f05090a061a0a1403150a06030c0b04080d030b040e0703060213050109 84
    0x22200042c60805c6503010260060044080544d1a00500000348019209405041c0a80d94642e030601e0041404d501d00081000310406541c81070140095085844407440007504151410070f40300d4550745415894040020001022840045151150300045441e8409164000c0b4180d0705080380c60014031a00341c9060780c601d2002e0300410440c01d034650094001c40e1045802c8001c40e4a8a40c0d502c503481c0444105034070454169440d01403c1040600b9404034480c02e02d01100038504e45111035401600c50701c581c0e000081030680106110894508aa009900d80640c1e128240590310f030800205840b10700484045540700d02d000b010241089186448a90034000a8612001681046403080d0f0701031547d0101d581c9071050141d1480c807900861011800f80c410340c840030515a00758601720b041c611032034001030002001880704001c0c0840015804071000704074200010301c00305803000b10f800713014809500c078054030900d180082044140d50041c100c602014002c1c105254552004444000342845203 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 478951978 1250 478950728 478950739
    0xa020a0e070c0605090c03010c080103050c010f0c0b0a0f0e0303161e08130606121515061b080f040302090609010f06050d0e0a2a0f1211030312090f0105010302 70
    0x2802c00280240d2049400004410484000e07494a000103425501401e0720b000004030322030300400422008210340080c6003000d003848504000c4d040801440f600c0345120181403409214080f0751060380c250300401007045000400d10403060500c0030306070f4039030007524401e1503500c400d02c0d440912841140c01204261101114010082030f440003250f04810182c00040766001d40a028000111284a2080100800140c45d072609045003454034404204401c0411840d040100a805400b1410100310588800c1e041c00448020000e42d071507120700d214680100801000104989011010130181c01100c1c03089070310240079a103039424400e0546080c0310750030070404180c8041c0442409007000d0940d0143c01c21000a1450010005901d040e041386030a40d000900f9001d165865480326556952901890490884480c40c0a180700d0300d100d4507100e0030482800c5c8480103020021a802c860500c460001d08132500c2d195074400d0391041c0c00c030a49103500c545c428003415000014040c0901412643c00510 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 478953228 1250 478951978 478951997
    0x1b0201060302030d0c06060b0c0a0c150f0309142d010b0a05060f120a021908090c06090102160e060406120b061e04020705060f09210705120403050a020a0e07 69
    0x1091703403c000101ca085544903151400803d00f103103900090321510388010010069040c0a00300060082225041540d050440c00e0380000c00039004404218030280700c3c500082d11a0780340c105460b2074098003400310207900503820b0480800808182c059150549031285c442c86101d03100300907003201c4042c8107043e00240c1c1c85408121514042024111802d12070820a1070901082c6100d0904141140ea040c0300c00d0740810401442d050401c00318205a0140c18a0360b00e0342000d18406d0f41d48c0b01200301d00303407003508000340200803644244164468081d454158041aa44a00b600305001034101e4600303025074a40800020b00030750032401d1142c8a50080313013814281d1594014401500940c800b91008050290300c03441540d00c4620062a00300d00030300c0985124200005c20a441d48401ba19a03240c540c881d0743c1002c03400740400f603505107200080f02056911201c5180c018100920410540da031800045000018010f001c110010a14803c90740102c3ea01e0300d444031803219400a883c1280060401c59 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 478954478 1250 478953228 478953253
    0x607020a0507172b080a050405210c030c0105191b1412070203070c090605060d02071407180606050f030c0c01060e072303070507021009030807061b020106030203 71
    0x30702d00440312003580309813040c1c0c030900c41d4121000080b0743c0c00d1500584119480c00c14469002d049160406000d12003400b5900301611015503515000d00c0c0e800c045034810328210302c11000142110010041c1e042641e444200d18000e4a000380360440d0500100c3c14074252030340700c0300f4451249503440500c0050034465040b09850440d801e100468222040d15010000c0d00348402c8261915403082c00e603075008581c3e0740701700e180100d03d90019600408039207082c100184a950b0728002640c2c485030850400680b03414007410300381e140141c2480d122000340619600440c0d006c0000e200c0000c0c41e248041e0520440d5690802100c0394840e003451031100040a00104018100010080032052280030010600680301ca00045440c84155101004944241c64142d40101c012243d82e00202c0600e092504600d8940005800b92280c2e1400074416034a220100101c0390250840c0302c0035507000421551549020719019004001c216a0383c04040c02c0e211100311783c144140aa6000d0703e5020f00500080360658 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 478955728 1250 478954478 478954499
    0x124a0a060c030e03011b030e0a0803070c2901080f0f0601060c020409230106050609090402040209061b0307030e03160302040203090f030c1005070503011410090506030403030501080607020a0507 85
    0x41c0c012010001c00f80640010750340d090240e01c0e40e1241c1c414088180f000340480141c01caa090241c0d2002d69000601c204001c0f807080010390707504c50810300340000b111840b464848200c2c40141c00520204000301100f80780403520140550503520600100e0340e090260303c952941d90344400840700a1a80301c5d000603c28a8403c107440340701988080d101091601c1d5a41d213046200144000315800701035003001c01e0f00700c1d110074082d04000b40000d03500700b441d2000050200d00307881401480a40075a8001540c05419100d04085503640c140c0034442940e80421001c521380c5039444010f0507400902c0c8000550414580821041d00d1807000c0c103000d201c651314560a03c0040c0d0401413900409018140d40d480c0021000e00c02000c400810601901000d0413003007050003140c1c0060000401c102c03080c80180302d000b02d40401d06807129801c40300d04500490b40309040f980c241c955041607801c8000031060104054160300614142d0300b555096640e02d80d0780e40006c90b074503188410081c0250348050410041040c01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 478956834 1106 478955728 478955747
    0x3110903101a011812051608010903030609180b0a0e1504021807200111040905090c060a0c20091e07020d0903124a0a06 53
    0x2d01e28080c2500f0468000e08203908005d001c0b00013401000c02a100b05046882451250302d502d8070f001c00e0281140c00c4003203002ca4202840424249e0460291018090180003c219020403c0c1c503120310795107014014401446c0e4401d82118510010300220388607aa00111a412504242c0f0501101c58204000d4042c0390b1181c1051001d0039510061510410000e250b002c00500d035485a605d0050802c070900d0007a180700040e002403040342d1030304183e214003502c0c0182c80070b542c80384040c09031030b1160158000c0044c0c10f034001c503400129205c0000c2c0c1f20841c20300c500303494184684c01044c05c0040070341d11030b14080a01228901c0840300030811347e0f0f0150283c0f005d00403c08080401070040111800b008260407030614900c03002e036102c0d50800351404149007811611041144620607490011132508800000852084c40006603000c25100c02d520050134211159144c02d40480f0f240c1c08 = true := by decide +kernel

theorem cover : BRFrame.Cov 478776978 478956834 := by
  have h0 := BRFrame.cov_init 478776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 478776978 ≤ n) (h2 : n < 478956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
