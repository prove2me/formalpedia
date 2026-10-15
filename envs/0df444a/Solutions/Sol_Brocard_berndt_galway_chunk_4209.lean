-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4209
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:52:52.946604+00:00
-- url     : https://prove2.me/submissions/bf186b99-c6ef-4aa8-af9b-05b73bee6f85

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 756834532 ≤ n < 757014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 756835782 1250 756834532 756834557
    0x209040b220b0a0c0c21030b1203090a0506040b0f0f090a080d0806040c050a110a080301081006050d020f09041a070f020f0708060403050c0c03010203180610051e0a0e090706 76
    0xc500d4441918020a103101030b81b0f040040c0102c94894488090a034035000940c1c200410110700410b05800011055034004183c8804500d402c2008a010300020384510703040619003c2100c03510302410200812101f00441c0021400c56110183c440c000700080041003140e5130340c8051078031001c1031a6000d002034010700c0003403490b0070b140c001d070032400340c0725036485e0f282802030744040710078020100c60082c41d4054080207202040540700030f58060000c4e40081d1120203101410360701100c02d80c0d4000d83c040c3e0004421200569030300004242c4e01401034076010303e142e0700c03841e0040510f001c40700d808420364452030134440c1083c0d000d2850142c001d04d6400300d8500e0070507299215aa10782500c11011a82c0c03040740000c0c0068410800341150078200021100000b46e031200003420b90b0411180107041c400c1410b00c038444c8a20070020250001e061110b403110040c240742c04a10a0781281c0340c171146011042c564501e180c0c03682001c09000342040c0074800d02c030703003001881d03151500e0451281100055000d551030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 756837032 1250 756835782 756835787
    0x50402040c0e0f0d05030d151701113009030901020d03060302091302011202030c13060c0f060510080a08030a0606090b0919082d0a0209040b220b0a0c 66
    0x32420114000c2a40c1c00714940c3c1810403a1100300f02d582111640418010926482074074002c4440c4414904040c00c049401d00b006609120048100142280e04003080ca0010b01d0041c011507d528030742d510a0746a00b490542d02200c2c46041003004000401e8210420001d140048003410b1403c909901b540c2d14019805811001d0302d12502000c1e6028080c40081280707900743d206007154092040c100700b22031b0788450f01e02c54102d80048409458004000443c3c90f01541102400b4018058908000410003c1d0351560080044079540c020000c0b607580c1c02090900c60141c8100f4002e10941c81280e081c0c1d40c5518240b03905400681e126007040303003059400b01c0c400b405189190190740c01030034218104a240c4080142600e0002808042c108800c20082040b10090100072020780b0310040600c040503c103440c8401e881d0340ad8400f0a2543c00400c04100140d903080d90054004d82c220042d5400c0da11609880c08440c402c4400b4072021401c0755410720100f100414165101317112a820812000956042c103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 756838282 1250 756837032 756837047
    0x3080c0d031d1c03151509051203030a0b4204050d1b051e1008060d020d060f02070320010501060c0605090a0c0902040f080f151e0109050402040c 64
    0x10b42880c0d08002140000b140400b1507050712500c0300e20b0b003c00d19403401d03100d0115001c0c02d508001c0c054080c00c0d0032000a160000e4068006003002c0d142c4010b0814502d40ca15100e01004d008018599151030a1401030341c1c0c0c0101c034811b09007500301002008908070841803050070200c0b2102d400024040c12941c4090901c030140c1c2e0449401410741510500e40355030b01903242c14015840c0c038411242d8807005c0303010788600071800c0d05002454505510403110700c0c10414030401029044c02000141c901b004040d4030ba00c100300c040c203541501c203c0f000c101035290140c050305d9171200002d543c5102041810616a01002d01c031341d0280d50341140e40350101c0c0d244056090300c80034041c90000c15a808450750024032985c2c0b01640c024003400c255020144c0e541d488035140b18a0780e10a50a55401180c140249101c10082100030300b0044018824107501079003258a407240c10b00e100716428071480010b1141d2109641c0c440c00307a202017000031450340e194400b000013084140c40c04c0c0e020b02c3c90401083c6e4514003520301d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 756839532 1250 756838282 756838331
    0x2220501080d05040b0f0c0a060b120109051905030d020a021e0309010e0d02060d0603110f09060d020123031006080f040c090c121b08070503040c150903080c0d03 71
    0x2c0390343ca001d05005d000d9800f50306c0b41402c5a00964100415042c009051201d00c030340c41d02c50351001c600d02e100c45042110040807600c0d0b60819034507203040030300011000149014180c1d07880c021001802c4680c14041d065008001c0c00880071400001c041d004030342e01140c2c1d094840ca4552000701810000091141d4074003c40008a001c0355281c140b07040f052030580030f1190f0b1140b005103214640002b4178141025500d0341d030700c12140340340b90025111540c81c0c035008a01505000341c580c1c802c2d80c03501c50001360709028403a80c060f060020079030801658102c610044203552003105120f640d2030405124a8014900e070384503500001d02c18101043c1c02980800d4420b00550304004600800c500b050603031402403652184070000d00940707070041078005081c2d001d015000d0002d40c0944100e42c0311404c0161106600400000410004104010024020501d0401642c03d03604070032003404202041aa000384890304090700f854408a40440340c6240000c1949c030a80460350144010b1403203028034242c03c0000c92 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 756840782 1250 756839532 756839537
    0x12120709080d090e040212010c0f08150f0d02061908010906060e0609040f180c030203150f070804060b0604090f0f06080a0206030c1605073b090a02220501080d 70
    0x180130031034942040e81c25a0050b000400310081805504601030866007810030000200d02c85070100c0036115000230300c10741d1150751441c40150051042c40083c00140c086c1d410144950307202d29807841503444817019540c400c88052000c05210281c1040548840d009100748881141040b00205555115242c984501c40c405081142802c0d21b200070400903101f4a804600000d03505e8050120381d900c44100014a07601600303881c0500e500758018541024110b01c1c280072000c80f02c005001d140c0180c0560740e584000b6a02d064106900c03246044c20280004150300c1d0390251000c5004a440c40e26503000e07004407810713500d04120740036480b03580c08151016803240c3c07222504111072810250900400540c0d0200c0c4c41c080b02460009070195011401d0307031085055810ba4480701043c4003101161000d0fa1700718141d0b24420b82241c40c040d4520240b440f41c0d4841e07001050b4400046645814200b04000700c03d40d0050800340c901d1154030500b0410745c520941d0440e1542008000a41b419000c0f425035042003459 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 756842032 1250 756840782 756840797
    0x904080d15030b1f1203170a02180301020a081b04050d11120105090706031e09110112050606071103010f0f0b0a063f060b03062803030e010212120709080d 68
    0x2c00d01c0c2c0202a0b01c4006e4051115503446034100100c020403580c03289860b410300580320100c5d0b00c0145041c2c0845414540603a2040014803481900080000d070711050b80907460b502c0030798049400b0298003850384800e40003046450359800304a0b0901310002a10b0064404601111154a6041c00d0315810b0706c1910300740d040000700788411886a017103036112071292400301026141c2060060708465035001c080e20f0810252185500359a440014000c14020f408400c1c0194101680010594401c0081c0140481000101c1600d1501c083d0410003141c900900200840300c01106614054004441414402e00074100e0100b01d20380515014000c82086030030340f00e41c035055503800244a030390040d12902c0c008800628042200c5a0b80135600241a01c9019162030b0b060a1081c00304000404a000802003900d501c0c1d2158104000307050400c80b07415141a03141e510f1180c005070704214600500a0200d80c1c002003010482e9014203502c0d00506c641d6941e030000b0303591001010740b10200294001c0000341c02 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 756843282 1250 756842032 756842039
    0x6060424030209060a080a290c0910030902090703050405010e1b040c090b0a05040e060603040201120c051e090f10050415050d1b020c030d0c020904080d15030b1f 71
    0x1c20f00c03540c0008085c0c990414581c4485202d0300c0c4c80d034811411241d282100c102ea000c101d0040485009410705030a2181c0c160800071301d111043e025019410303000c2d00414600240c114030a8114070350303c035006402203140341048000100a800308a5041d5080d600b0243e0807461408009603503100c2c85004028404444403203002c100160501c5e001003030402c00d1640d004185046504010840915942c503180c1d0340394a00300790706000e4940109402c0c401c85e020700401c070240c4d81003039a500f03101030780f6480019a240c410704151801e00841e0442c003076108a8030041d004503d9404c00800c0200400c0703849440c55215074003000a50548240c0311000601c0a100411640c415100c0506000c009410814201126410050112513400602c4da50000c1588504204540c051004811040c8240c000d08009140008064041c020b4400001e0288802000042c107104190b0255286013403207a006001203a4500e8a01840050070700040c0d6004590b4800300d80401411980ca80d42c01012001c0300030b20030314 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 756844532 1250 756843282 756843289
    0xc0318060e12010b040e1f0c050d02031810020904050c031e090321150102070302150f07060f050115080108060610110a03020f070e011d0712020c060604240302 70
    0x1503004482d00d640d20340551042079607850040c00980010b4400524504e001c03280301c2c4040400c28200b071018a440e0424001c46560700c4000c40d113018030844000760f540d807100e0080c0414050b90483c224110b00518039425080c0c0b003590010114054100c80c01d00c1285c44280b4840070078402900c151541030003040c40c402801207003c83c9154482c1c1c3e0001030b6414102c4103c0074032140001c4910418009619808120310f16002c107100340403803002032005043c1541140d001c034040151003204050800e50100e5a541c18004290403145940d0303000506010041c9e07482e4299010701401e000360b1540b4a072065203c0c070460721680489040b40c038003000600054031900d05000010400500041c02c2000d0b2160183c402c0c8020002c4490030342c0700c1c0d4010156400305002e0141041d550784c0107035280c54150001004059208550740c080c504440000f4072054030b60344e4094907a4550700300440b07140e50022416440840010031485c3c440c041c00e86090122b2843c6000d03041c030352880e400f5184c0c8103c0320a0400e10150a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 756845782 1250 756844532 756844549
    0x1115060607020d14030703030b100509090601031a0a0308120c0c0304350a0201030c0507020307050f060c0d030b010905060403120e0f0303070c1509030c17120a0c0318060e 75
    0x501404d8103290390702a440b103043c1140d02a40090b0003080c0c44002d0031107142407a500451094402e49002818803107076100003007030082e003c2d140034100768a070b5208051400781d2240c8282c0d400c400034609401651303030340752403c143e8100c42d070303000600e170115800a042c9030051400ca40e846280500694605421b000200001e000c9210103400c0803681a41304c020004001e100c0d40424808490040100c441da5100060564105601020400200b4070982005807000100d40c403e984e000c95045000c2a160408210980a1003101c4091b42c0b041d03400b0020f0f00d54169011902240c000e070b036000c103095154010b01c24544212321008040300c01e91071130b00c5440742c42a2140c01206400030500e610001d0804002880d41c0c00440c400d0b1488246014200442403500040000348091030030072a40d113501d1a1a0112210860310560b880c1102608020170030490a00001c198850034042d8180c6a2401840c000c0403408071210480c0070130f554045051a1445400071002154110740d104a1002c1d105400c0c000c801c1c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 756847032 1250 756845782 756845809
    0x1140c0403030c172209060501140d0f14040302070605030c0d021b1b0109090506030304180f09120f1706040b030a15020703080a02030610030908070c06111506060702 73
    0x104540d8200e01000110b0024010044805d070240d800d000c132800100d1a81025601084086240005c200041c0c1d8010220b02100e500c0300610549a01004c0302040241040b14950b900c00740c50b05941800c6840b005e00514019030103030742250100c9440c0c034030070341300c9100c142c0e16020320b110248410070310298540c0042845460f0b010b040d1712040101805140b50004500740c580c55141c5281c074003d03465a0210700780703000385140041030200e0700b00000425220f1085005004990400a03500300c000c400a4005041c0c40481410400c2400418100707503c0f50710402200000141400910b80b400342c0c07040c80c09924120242c1d000d014a0741b02d2404200041011150164041c0a0750210f8800716058441c40303025228031031009644c0c3c45107072034010b00780d000c001d050301c19041c41881803100c1c0342c0726a5125002410a402c00052a02c1d03503017425035640c05212401099503100d904045805a48480707800580c214040807103172030707106440b45003d1202c0203c40310358001d10140b16110252602d10010b9001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 756848282 1250 756847032 756847043
    0xd020904030c0c030b07030b2205070c0c0806070f110d0f17180c010513030308040c170a05060a06030302150a24030516050f241b01140c0403030c 64
    0xc0407550f58034150014400e07401982c003410300a0822040c10340500a0703141180c41281e51100e80c94450760308901d102d1440e0000c0e2009035603100015100c50150400840d02900701d42e1070451103a80d00400c0340e4441c400c13a40c500c0085c46400b01100f055000c0e094504078082d400b4080e102100000604484851508800c04204100d4010141c03210072030102d510300075982d40b880c8644100d41c9104581c03410348821005810480d0402950540844444441c010f89034103241030308070fa4607541011007003a03115800c51a10a003491042e00d036299400510039000d10f10441c180d40680c2d90708400e4900729a4544009005a0000c90448404140038442564080e02c000c90000305a481c2111103c8090f901c4003100d15110a0b084040c400c0c09400c01807801a114220300084d903503401e10012412680401c407456002e40392141c0c020141d14403a0742d041c00c15a001410440c0c0b1400d100e400d00880a044103045440340d40b138001d1a282603002d40110500c10403903440d4444c0740915503a0201ca00c540e82c110b00f50344 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 756849532 1250 756848282 756848297
    0xf090f04020d0c03050a0c0908030301031101091a070b280209030307050703051b0301051e09120315090c07080a05070503090901060f3e030d061e0b0304020d02090403 73
    0x20b40c2505110b4441c0c00740d00360f0f4001580345080d0032202c0480b1000d1000a0500207040c00c00c020403500001100d054940c808220b415036014040141e4200120b50440c1d152101140303800c052461050000d800481e015503524038547c0c54240c12001c80c3c08512034009818154400500e03190049a0018000001e000c0c00301e80c5883c400351103490500c0010f400c1100c0941180c0d5800c411340040000351120100d0480082019061070151a02c2000c10700000d251203200d2000007810103041400801900181145d000d9503900d0b00d4460003510031409c111841c4624406008103075038a1581054070f0005600140700381c073308103070301d0001c4e52950000c1004807500e1100b044210b40c56155a80c0590082800da169501304034408000901000b84d41e08240880b000c07a10b807501198201c18000b403c040350080345616030b1a09a0301c0341e40c250b101c0e00c8200c0c20602d003080c80020744110043c1c0209000700c0c0190141c0d83c4a5290301e2403040310701c020b0320301a605c0071442041402600d0304001d050703000340c400d081010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 756850782 1250 756849532 756849547
    0xc0c04020705010905060c0a02030406140714030d0f180f0c031401020306010e040e060610090f12030e0307030b011a042409121e14030f0702040b01050f090f0402 71
    0x10181e80c854141100c4694480c0441c908020081102c1508002000350407401c0c100e500f0f50080d0349000e117115010030003c0700490030210342c100b0002c480903250003600c80b844411002411343da9961100c0031074000345252040051110304184205038a40d180d00c3c014900e006055200c0f03000d4071488103c1174500718a0090000002101c40c0322881c030081190001589a143c07900014068080743e0781034600aa0418901090a00300400d13650b41c090b4003164091070b41e400400044880071096008801040300034000810305000c8480740a113094402e81c0c07480d508810b140281070300c0d41804d210081072100407100500c104c01c0a4155041e484c1d2034a06001e08041e0745841c0c4030302002c0c1c0e1170b0003100729030360024289160a80c4105111b010300404481008010403d6503007641000d5511064a240d412780d07400300e400c015103086a40b107813002a00489444400c030320122012548400d108920a900c3d00c41c5101441d4098415200740c09241d00c0c1c03160514003441c0c1404540c1144a200c598400d80c01c00c07842 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 756852032 1250 756850782 756850789
    0x1a06010e1801030c05011e03050a0b0d0b041401020f0414030109060f0506040e030a0221040e1e090d120f060e01060302070645080301240f050405060c0c 67
    0x81a01e00d81e003040d408465145040c10b10400c001c50f08064104901240d460300b103070900265044080225207400502c95540003e10401010321800380e5a0001034440035105001850b5040360040f0702030f00b24556460110000076080344900e0310140408181030104100c054540e41c00301c071a107900a400440d80c0621940d82d60219200520720b2605186e0b190b0501400b8105449203110104110000303515048820a000e5503e42c3c2c507140402c00008940d05001d003010300310040d1001040122802d00303440c10109040090003031a440915034084490001689025000542c241c50784400d8441d080c40648811214016080da003d540c000161112000128004040407040c0200083c0d61300584882d21860100c080d600004241d0300581c5581450300e82886c05d038980944603201902d444000700b06a150780322200d00e140c0c40c02512284020000040c220b00115a655203183e80d20220402c20034100d03415644040e4050180000071410b00062000381011001050703141c0c9844121000e820300080007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 756853282 1250 756852032 756852049
    0x1080907050d240c0203090607080415051c09020d02010c05012c0c06040807060c021906030c03050901050f18030c07030615050105030714161a01030209090a1a06010e 73
    0x11500d00b961200d280c01d2401d052060000300107910070003070208005898001b5902d0261304c403d5441454005403807410820703140103c40c01010880450007640840074006000360300120300804170f0800e00e002114000105105120010b680281040100380680e001182c100b080081d0840b1290341c0c0b4a005030041101c1081001c0031b1000341c80002e951038456400c00d080440760440140110814002400001e40224000c01918584d20304400e4003a40c1d070000440c84010140d0503100c1c20241e02c000708005070f041d040424000c01f0342c1c5050100b038031076014240c220b40046131407041c00381c0b560703000c28050f03c1c11400d0f000302d014098045034140640750483e9814404aa8002c40305540c0c1c070448501003148100f05400141001d01301142185000c3c900640600b0342040303a0144c81c400002c42c110014550356694910039008a440d150102c15200340d04100c400a01041e80300b110068001084030300c000500050207070340003004402c0c001c042c0c420944910400341200d814070030800024811502d0341d401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 756854532 1250 756853282 756853309
    0x603050a0e011503050f1f0207030302040b0a02010213270b030309030115080708030f030403110a0b1807170c060d060506071b0b2b0920090f04050c0108090705 70
    0x41c403c042c01d01d03500c0d00fa41741217660021754031036400840e0443c50903041c4c81c601d14141070340b03100c0259441c801d0f03140403002442150440886010003240700c071035071a4158060000c1d440104040c8a010351110000e60048590321b884041c1000e56005c2e0700954102a04885101d500260480342040c0e40c40c4c0000b825100c0400a0040c40f0b66007890400903450100103110003040054041d5160048026400205200007031015092003840345403003084500c00c018500a06411802500540c1031820300b1401120f0882c40304080f91240450200344031300c0400c600f5480782035182c0100f00c01e01100c0188030254100e40c6803640403a60301e003400155a00c80d000282140c920500041c0e4103c6405000f8466690a0340c00154154034240b20804504410207031102d4030b0030030f101085107554035003051000a03010b0420020040341031030b00321a110780c0042000381141e117800c40e40c88ae459a540d0708140c45220046034003a0840d17004400c0c0d0306095024560042d0404004019100403540b140c0105c0c07944140c118 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 756855782 1250 756854532 756854561
    0x60b06041202040b0d0302070b070503190503270705012316020108100303051b010e0f01150614040b07140f030a0e011707050313021c03090f0f0603050a0e01 69
    0x41010704600e01485034400300034088424107142207258800035510030340d0f406000d104d10030014108092000420650729260000740b00c50134440c502940040098006545011042ca02d21001007a024186004010800a0032000707001940c9030900460f40000024170307810000c012841d0315441c0036082c400900e0200d44043c0400340761013140c030004012942c0204030444240012001340002a404011160f1100a8a0040500d107819803c07250041c9451072011032540300b00540d08100d00c030190003c541c0a00ca2070600651283d4501d01910300c5100340309080f02d28101000140207800c05000600700705800b456644080c5540310310098a05a40540e64450581c40030968804460703128080006170b200c00c0ca441a43d090900c1000040924013078880814008044001160540300359800c0c6a410b800424031415560090b9010341e642920040c00e400103180140c001c03800341e1502451b60121880401b541c00301d1850007104030000c260142c0400e8829855260401c0b40c41c10274002d040c600035109 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 756857032 1250 756855782 756855809
    0x100e0114090f0c0702040939060306060503011701020708040f0801110a120c140a0302030a1802130c020c09011e09052a12010e010e071b020d060b0604 66
    0x104104004070024080c42c11072401e0703001c002c108407502c1c080c2c40000d5810b8a012a110100f850000050140c1d028141e21000a080450030400b4880c0c900c414070502d41150b0703030700154a82100703c050f20082e01a040c08550104010400c5c2c4060641040740c9100c4100014280040c5503101c031740325400344c0c0c42507080c0000a6000c0c4840d003028402d2a90400042e0803651609032a0200501031100804554080c2c5a035032151035490344c061700d039030b01010030710702801d983e40c184c2c29a020b0002d400503a4920f0b015032500c50508180300c4080351200380c0316001001001740c0400420034002603c240603616045015284819605442d80b8540c64042d2600b40c1d080e60708001a54800600782c4401d520117040030342418140300065a24149040c85d000900000d88000c4070083d201c05040d2103000e010310004011000000740070344103c8100d03410784000b46600e004648810b10100c44812460001c0e10301c1d4400140744800510b000392545200c14400c00000c207444445000003803180e041913000e400d060f41071 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 756858282 1250 756857032 756857069
    0x61d0106020d022a040912051c0504020102060f0702120f120a090201050409021803030f0301050a060203030402010f050307030b1026152101090501060515070b0f100e01 74
    0x1030040c0004588948000c02d010035810740070343c903e8100029a01040803c4c031080c10560f0301e03a6002409103d800055402001d000d8004c02400c6034040107040c0707100070b510603220b05030101034011107028a805034010110b54454013900030580d103010b00208154451100c6c0f43c443d40c003403440548034101c1d11001c00b584541c41c0042d104900b010003824180541d01d000017501c010717a041350030340741034540035000181c5981002c0d41601145481a861692502c0089840c04403e090440203606a40007541c41d0200240e03612030a80c0e41c0c1c0820b485c020b000c00c60100026040c0d078417900103154407200510300410704000c80c1c2d000c60000b407142000040044d00558003041d0001212902c514003030703c1e0030a623030b006242c4201a0810b0159608500c1d201d0b0055040200300e171208178204036100c95101c0e00800c0b01e0805031610b603000345128864140124005510740c169036803a9829039040303030307000410981c2683e51205005ca141c04001c1540e108080f03454004180c914004e2a014040d0140700c4040803107032007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 756859532 1250 756858282 756858287
    0x160305160f030810060813170f040e06040c091212210e0d020c031b031204080601061409010c0f030912030314060d0812060105070b0c1206040e07050d0501061d0106 72
    0x10350085c90174810700505000100c22003040f0b91400941040c040040810309866828440c41002032038800c59134081008100c6c00104543e050064004550030408461417a10030b0b5a00d01d00c3c0c1c810030f29941e5151910b2808662034604007600248a4a42800b0801d003040d140c03d00103115101d06411036940b4031481c01e100c0b40070044e8601042540c002010030810400020369581000c3c26000784031032a00e1040d2a9030f0301e0802c8048001e4001d04043d41d00c4544440c02d55a84035424814800003441051042140001e11000c450081c007060752041125205510b0f1300c550a0840c400450800c501d4090003d50040940d881040e01e0340b1035640840e0844040c00150b080c0d120140a8500c100d410010f0b5800003a44101103d081062800d0405541d0f50f942006035010b0045030b4014200c0e000100821207285884000ee115031024a0182e02c2a034440c1c00c244012100d07042060130719503100c03480c00d200c05e15218914000092041c0c2c0042045a01d914a1000402c0428100c10709100800c0041c4010364 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 756860782 1250 756859532 756859561
    0x603020903210f0c01020424030f0504031d210d0e030f0715090503030415020607031a130207020301020d0b1002010905100905030d051f080102160305160f0308 70
    0xd100000a0070302040b01105000342c0c424040d0b0802c00040004d8428803500c02901a00e0040403c070121010801c078205c400d0785448540000740d0002442c0511030005410203204560040f90507580d10080e0700740030712140195030760030140c00c0d6020b081c0300c1c007110f00702003a24070078040c422a5a0181010301c0d140000035111485042200d886600312109944c0790741e5000030090211440c1c009000c890b02c1c4801c801b07480c504101c0d04101d4144c08001000b040c05007205d100c00015040715421915150340701541101115a98104486045c000099100d450720304400301204801e0354020040c50814a68002800c9138401d44c041d284140d250900c01459103882008a03a80c1e0b10b90340020b1004420954559849075080203151724441e0b80c2d0101c000900000b00240c0e007114a208508005600b85441810200203041f140c10120412005000c1003058040c020340c0d10724000c0c2c54100c29100c1d12650107aa41e43c1010080c041000305100c0f09901080c070f000000c1a01900a407a000c40070b082000a240500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 756862032 1250 756860782 756860803
    0x80c1209040c050717131508102102010e03070f09050403080f04150513080a0201060503061b270a0e010e0709030b060f2106090705030d2a0c0603020903 67
    0x441480310401082111508000c150a40c01d21182d480c2c1c40010f95049103020340d00b14841e92021010601c000c0354001d650b0074001c00040d1040b541c1c440e500d040301420490000500c05070b0164414808ac01035000365100c05502e0310040a8902c881c0d22004403013148601b035480100456254810701051507001905d80e41c001c4c0b04540c0f01e00d03d603e07003034440540310700780581611540d66580c00001d034040c0c151000b10f0022070744914010354a02201400902070001401524480d0066201040ba22030400c3d82d101d280400f110116801c114050700800d0712920600c200c2812000900c030400303007959a071544d941c06400030000b40c5030203504120398200e0010009240c038041c4101c0a200344040384100e00156030140d41222848000602980468080c03007240b8003441403121640f00c14100000081146c601c21078046048070466030303a42e003c050760380952030320007004500c2840402031940600040120fa140d1800342582e00710f0020b40d113902d040c15055000b440001d80c0840d985e02c580c5001d00c0261080b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 756863282 1250 756862032 756862037
    0x70504020705010b120102030f0c03070e10020a05070605091020010c080a0c1d040f0f0f0e2b1b0b04030903060b03010621050c041a0127030f080c1209040c 68
    0x390302c0c0160383c1031482d1270051b2415129040200010b10303082e1080e00c01d00403403c0b0180c0484550400002c3c06581c54031f880e0b90482e1140140c68001c41c14601c80c6050b5400208010b000500c83e0075803e40540360190988030305405071040100400140d18240190a100d014540e2212614500a10074008564901e0140b20410079010303610062202c014500d00391032401201c0014a189181902400600142c0b0095082c141000000d01e100581036120200040004040d80c5200200402101040c00524035400e02c0b584031a202035070311032040440040b00317015a1200d561044442e1107118801400300c2d41180020751071041801000359074010304191842c150700a010700d900300100c0312a900c001c0400701e60100e000750030003002e1210400051003443c002800c208011140e20300301e01840d0a259141a0214280d0400c0d1003200e1124003540400c0421840b03904d8102e805c56072100c040040030141604d4803402032113802021102407249045100c1007501c03859880312080c09103c2640d00c0002e42009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 756864532 1250 756863282 756863287
    0x71701080c03030409180c0305070501143f010320180406050c0405090a0c0314090d050d1b020a0311010603260403050a050609060112110111070504020705010b120102 73
    0x40c42e00c000056400342e03504000c000c504040710040107104010043c0f405421b50100840000034000003007240f1056032400c1e40c0d00d10581d4040809075082d8481d4580c5403455a0b00180800304c03111070103120b15500700851142c85c514211059994054010a130003d595045903c0619a610f22031a03914100c5050255242c811344000403590524000300100040e01481e120707000541804001001c440140000a103000124100a014a8001c2c000c81d0f6131140441e01e0301d1402041d450f5040c0007503100b044480300030000c0313400c0385034112640d41200c1c998501880d150448032450a9880840406011285d401003480381c40b0790500510f40c02500880307000b582d1400c0018804104a443c3e580c84405080c00c81c880c06203410042c90030180715a52005c2c01500803010700c90104000411018040c44004044a20907602c5120b002052140644014240409140d020040754001c04080d04d40105500540d903004e56180046002e80e80a00022030b5583d40d41d4258260a19141100700c0c101e00c5080000c50 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 756865782 1250 756864532 756864553
    0x190b09010612030c11010207090c050415030209030a03032012070f0914010e0d0609050a1104140a0b040e010c02150a020f04120f0f0305190e030c12011407170108 71
    0x801318689500050002030076503003a281964000c001210042c0080d820421402c1500100100300340c0041c0108460060b510100300c0e00b0ba1b21034002c0e00d02c1128010050301c640c44965401b44c0050011103074031010700c3c07013031409203142090725000b0b02071110303882900d0310503807070b0205c8000c20710918807080c2c00c24042142402d10607a0101c5540782c031903043c01e08194400028842c001800003282807401070103039050106a9082042c0440c800705080e219805156010300401c0400041c1d518081148014181032400964850b00580000c4c3d08080d01600015030010035030100f500b942c00d107502207030242c0d0100404031031401d40c107400c40e41d00a08444e4114240700541002c685688218850b801e5030180d05071003c02800640086201b609900c24500400c00c030b590f00d400382c110b40054048a2042c6022248854094054040030081e4031008014009110b580010842200396262401c40d15641e41d554a100c00c465070b00d04a80100c005403a10325200c5140c180b52409103105070020380e40398222403150b4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 756867032 1250 756865782 756865787
    0x50a0e06090c010e031603060605031011030a0c030b030f1c030e1b01090b16060e0c0a090e0c0301060e06042f0d0b06070606030c0506040308120702190b0901061203 72
    0x50040e5082480c0004c144030000e070001e1b140200001c5001c8000201440010410010354006000c8440540580300c4041c1c4020715402194007025240d41100003c000184149071164402000c81c05030b41000a008400b14002c00d00e00b040d01080854a80e00030026402d20180034113140c0160501c80c41c080c401441c2140205459480418039044040c04101c984246680a444020003402d82d04d0010342e1a1b00704001201484050300d0825981e107071070100764821650010890380d946207400384c031880a40386030203034000003060005200b8019001e04503040015640038080c100060440202c505070b1030070040d080100f1501a800f0200e00100300b0800061005514080c1041441d0000c810540360f45803140c0f00c0e000b5140d001c1149500c804001641e40410a05501460540e80250058041240c5980505c01c86215500020740800014091007058140042545a0207031007481070b21014640a1403146444212050417154a603402c0c0401400d0402481440010b2440022145004e150368402 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 756868282 1250 756867032 756867043
    0x302161e05120c090f040b070c050303150a0503010e060a0f0506010f0507051e031b06010602280204060f090c0e0609100c050d0917070f050907120f050a0e0609 70
    0x599026280d10041c0062a92003804030308407100e0050a2500ea918100c170803d500000204c1c0c003142c44142c0c407408100d8091152014072002680503000314907507100c8241d1009400140f01d00c2c95441440c804000c562510203014900020386c1170302c01080c440c101010341c1015104e011000c074403450300d00701c10014180c1e40804c10041e030551505002d9598181e50814038140aa4007400c4640040750101d000d00e44c85c80000103001050501c44101140286480d1407920f60300c0070311807000140d00440c0f1305680403644940704400d20f050314102c02c00014140c2d0100d0305030343c0107600019a103003090204011140d0540103500f00d0082c00c0c81c210182500400004400d405564100741c0125600c061300301a0721300038140400e07001e03049011036006200c80074004044413114000c828107000042c61100c006a00010301400b035500790700060074411300303041c184030401900500b003404000c1d4218182e10640d18520030120011255440821140f40400c0082d007030320b0406044011a40c8441c0401601e0000444c6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 756869532 1250 756868282 756868289
    0x120d02010b0a050f010c12050f0f0309011803021c02240105010f0302091302070204090b0405011d0c090105121002040902040e010806190b040b040e0319050403050a06180f0302161e 79
    0x8890b1f041401d0000480d02070060744003404842c4030001b614004814141c016510450061000f8003010740426030221280101c124000c0260b48503a003914500305010070f25210600440c4126010401301c1d8000401c44540c08440d0588043e0180040c00656440381c00e6002004070340c1020751500b881e100106485900038440c0f0b42a041d40440c480c000c6561b1a0403501e401a081003030741c1054142800c1c800d00078130b58140c41ca481021451000e035211900030400707009818005000905030f0f844c00052110095005800c1c41443c0250021048600c903180b0191020700300b1900c0043e207503800c001c94a00201010b80140041e5801541001828183c4950002005a03540d2021030303031042400200e0301400800c070444d640b05007007803c0c410340000004003810700c0c0c1a810013821200301a01500b5201403003140005080740d042840320320b0101d0405d03042108000d510034014048030009407500c644041901c0c5045005800c1981444001c0c03003500c40e00c202401c00a0801d04007a901c271001662407003400d10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 756870782 1250 756869532 756869543
    0xe0412050a12180501230a06081b120601120537060b03071409060405040b150a0506071a010806101a0f0f0a080c03070e0d02120d02010b0a050f010c 65
    0xf5a103454111000d1104100551010080c880603c1e24141050084655a1040052034070000029442e4806000e40002c540e00394010b4810a5240032148120303440490455403c0f40911b600b103214900d04115032802800310160b0302e410091245010b070f0925624403218809030000f0550b4a40c58000c0c001114180381c81c825000c0d42c0410350740303440d00140072070121007a0700d80128100040c1e00e20000002010740c20701100c001c0f03810b9032007900700300031950103031809405090540d0020340381000c80c3c0401c4411140052a407814283e8034400070f0025402007600300c80c1880c43c0c00e8840e25840b203000c0c895024100380c501401a524160400710710030b40031442a050b8002c41e0001d07031001c008140741200e002d0a11564003c1ea02e07104501402003a40c41000e003035000421017000600c1222440056034018262030b990020905000f074100550a9140310050740c2c0150203048407100d4400400c00202c0d11031443c4c0010510608a00c06c220459510341e010a0061050303020071030b116030b0b000c0c0c64603903070a5000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 756872032 1250 756870782 756870791
    0xc0c060f0e0f0f0d26100807270c1407150f0b091e06130f020307020f0d020105060121020c01050f0a110c100507050d060305033601110a050303010e0412050a12 70
    0x41201b50580701154030808080c09018404a0032429100018010780400c01d0584803d4494860200131526582e400e1000a49250984090505044014000c4034000c030003a1010195020b00e41c021a000202020782096440740241c000b420301800e056030000300703015100d0140c50b002c0340c0b0080d80d120081c0018455050020642d01228440d88465540c5003002400c541324502103034003a41c1d40c000c001401c0f41512501e603000f0103d07072050041900c505030680d1100d10000c2028030410304c403221610701020694080c0182084d0301d00034801c091040300401c1c0300c64040e00b002c140c10011124007218841d0005810015040400780018400c0f0945141c08000510b5640f031040c2100c95004909143d10340b0350400c1030020501c28000082c000107107002e45090b011441f144184111841c401a64410a0307020980e000b4196000d000b8005032060294260b032402080d640d14141141e00036040304038800140b905120074040f0070359010629514a007030281c82c120b0300a9003c1c0c10f1010002c88190425240c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 756873282 1250 756872032 756872041
    0x20a030905010e0f01061a090d0f050a03120b061204020d0201020c15040e07030507170c040b07050a05010b0609030a110112060603051501030c0c060f0e0f0f0d26 71
    0x19500c0380c024140c028008209209001c43c845450303107200c0c00160165030030003e010541c0d0700f4002d8400c08445183e0b20b001d192809480c1801002c6c0410a000c2c0c0b0408900584080030038424881e000d0035900c265160021500308401c25400c5544035004140513180a00803a80e210681c810b042e90041d4044401c0c5060302200e2004070b01c0d01e0380c001e2100d908034621862203440c021000d030141087c1c3d04440c035071660b00d42d6280710072011910102c038424002014881d220420950041016400000e02d940c1300c2c0c6001e4943c4143c0c0c4940d4403030801100d4036071000701100207001e828821480c5018080301c802d854181d0314400a80c1c2c0f0042590054021000c140714884c290703029203e04803400c01e43e090144070307180c0e49040190040104840d030790101d82c0710104c81c00312503100384551030b5a20714a454440c0f03c506a6250b86006018406001182030390341d0000c3c400c603d208024a0104180c00300050102c14500100389040c00d00e020009002c0c412140805008ad030400040c01c80702c80140819100d0950300c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 756874532 1250 756873282 756873287
    0x14060403172a1308150604140103231b0103050906060d02090901200424050d0209060c0307060501030201021b0604030f03032306011413050405100e01080a170703080703020a 76
    0x78141c20480152106030000440d2500420284000001704442e240701d80d982c0f2090000780d0300380381c41d2121340702c619100501c00681241c0030700100450005454030a2152480414540520583c0d0703581070410a0300c6441c000c0d80d140c01000d5011613420b024100600700600860141c6400e000024807900c51480024548442540981c02c610b6652139014004d140c4041d80c41120340c058058100d1001c09640c240e0324458481030070b40381d0300d40c1d00d60f1018a41500219500c00035003040180e40d500c4141008840c61440d01007000d890030234018031000420394510700c00a46820446202003000144100b02d08810ba076945040d141100d0304808402482c94140c0740c1180100011014140c800d031480864070b003081c61007100503210390400e8a40044000c0000013011040c001c0b84500407041646203001c0c010381c00c103608129000071102e103000045980b07810b40024410400d801c80841640000488400e228041101509440c50901000d103400341c05d40700100002e03002010034052603000103d441e030162 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 756875782 1250 756874532 756874537
    0xf0e061203070c092a08070e010201110c01020d0e0f070e060109030f0b0402010807110316080403020907050c0c01090e0a1a040e06090d0201020910080702010914060403172a 76
    0x241c1c0190100e8815407140304440080c00c0b180c0d141c03400e194400c844948001d6080b80c00c4c02c0c90945c1c03900c840c2031560710710008a991020801501d4119500c0c0e80032490520b620300090201148100c0c00035071921a504142c004031014074596162941c4100050700c046c540206400e03003550561458403060351f80381d02c016039410000d82d000a00c900300c41c0f2181d0040c4400d09511b01d000305e200341e80d100d403075854242086a010041090904081d04104010505e24000c20000e01c00103100e0041e046c2050b942e034000940008085901c0004103100054081e1014420701c1443d100c4002400c04c80031042c1800c0b4036030a83d04004240382802c1c0d0340e44e001080c01c40d500b580489810040180705000ca58100c05509881e04001d0b01d10550500c600c0008280700c40c011b0080e181d883c0d002070490a012484000c0403502032002406507010341d5a1f541049003c980d003811000841c510385c4000b889035043c6442e00404801c00d80784111041403c03071082c40b1420078282124012184c00070064181c0b401e10200910311407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 756877032 1250 756875782 756875797
    0x90b07080910111204050f0603130614090f071206021c0f06080c090108030a0c030e0a09050708070206160c05070b040312080901020405030709020f12010803040503070f0e061203 78
    0x40076030011036401c1c0d43d210980e809400110740607900054040a2203c40d45d0145000c1c41c1d500c031510304144000c50410700003865200d45016904c21034110541c540d00c0803039a820f07005151280d100b40401c10090403c1200c070a000c0c609038000d101c124a081c600300407031560020000c0c0410b0300000d0707030341031042d85c0303809c0d010051002041080b030546081101d000402d154800c0360454003a00c00c141c0094508448058100c80101010f5850072600d0501101d0561410b072040b401e0105a1499003ca501d980000d80081c01d0740746400581c609000300060a0420001c05d030108550104041100060703c00b00c0143c4001d00c94205111021300503d00310b4106412904040e80c00c6101007000028455050081a0032040c2920b440ba1341d6100c000c4078a090748514010560540c2c884d880402558030300780d000f040240404c54010f41802c00314a5505881c1c1c03001e900900030342c0d2011506003d14907040c859030001717120540a400400d442c0421403902ca5900a110502c9012900105000d0403818800c8403c407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 756878282 1250 756877032 756877039
    0x3090904020424090b0303030108070302040b012d03050a051611031204080d110415141b010608100b030a1101030204031e0302011a01020613140a060209040507030606090b070809 78
    0x1403034500500804403860700c80c486104d410401284103608010048a0680304484080d21610b030440e020b000c0a0650514014108590300090b13502000465410401503000c80e07400200d29012010002c003964005020031346030920f0b280502480400c00400d140350b01c0c60030300300321100ca00314512550441c091a101510146180b030200300402003014001d0802207801c02d010030000703100c2203500c610360159003d24120346200403480c00389280261201d104c0c40524044580c40d00d00361521000c00078081e20030160700382c1c0d140c00007031140c001c2c00d000f10458403121000400043c0c81080000313a4900d810b84000d003200d501a0740c1500941d110340c04079030103580c201c41245251417081008a81c4032100090980046d4603061b500d8104940680c250040010141e000b01302e25152041d1882c601c80c0c120200326800041d180c40c40d04840810303c412250039005800060b11030710100c003404181d50000b480340c010585881c800f441801d401081c00c4041d501e0101303199490758580c1c9030035001032052080c5a5403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 756879532 1250 756878282 756878321
    0xc1104061211120a050a080f0f0c0f121c0506060705010c0908071a0406080603100c12110a05030f040c03200315070206070c0507030f111908030909040204 68
    0x34452480d102e840c0b150410f8848150490b50ba8038440d131102c0f04e042000f441034100c0c0048801040701c440c050800340d180e86d80203030b10b4203501d803c2e0f00e0b00f08c0c2e000009201590700221290a1000020f10072030460440c0d0b41020b41c500386a401c04103100f84007444840c48020342d40c00c0403034040e0321a1800e03200d0746079010700200600b452600002e0705000c450300c9212043d103d208004984403040c80c03003114200e002e12807800d04190600d0015120700f0001000250035114920308019008014000c1030352120040c0c03615400c035030056010ba0180c0314030b458419411070040040341c0310303143d0110840c2d500a80c00781522606440c1c0786468420b000a0f94006042c14201014040101014014640741820100e0449400344a080890888901c04403019030240c0c11603000117440c1e034080c1103525451480740e81034464887d203a944103d80b20180c0f07001650f00400c01410040340382400421440c1c01044a511032181c1840c3c481e1030340c0c6d6485205540350045844001150440d01c880e0008483c687c10340e1104030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 756880782 1250 756879532 756879569
    0xc1704090e071203020703020f03030d060f050307080705102a080307032406140c070b0a0212030112080f1b060405061302010e120c06030703021201060f0c110406 71
    0x101820710003031440e030349010305240002c0a0b85601803c8030b45940c160054406945540c00b00070401c10b440324000d405000820445078040c0b214402e0728043c0c821108000c200600b0304007410300d49201074128503916480340c10248650303501e503026400420100d152540c0c40100910340001c0e282801c400d0700004000d403420030070400080c000a1407080701969010004caaa1004070000a40c2525406283c0a488003109200052141d0201e90012070301900342840d16a18103581441c00714140d03c40541c491b4049214454640e0500020103081118086141117504102030400f4107849140c008004050005686064542c1c50003650413505100d58000940b141050600d6281d0604031070885060080c0c600141600c451662003011203601039496442d0f880c0c6401c24088008820000f61989101c0d203030344861540c2d10b140080d4403a02c82d60780c0c09a15240c40f00c3ca00c003024001a00084103001c8545545c840c2181c3c0503a11001c4140c102280340c10480381e00c008680145401d400990000801c0b40c00301 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 756882032 1250 756880782 756880799
    0x309030f0f0d0c090b120c1309050103020a120816061d0a031403091005040204060e0405030a030c0912060b130609240e0c0a0306052e020604120c1704 66
    0x402d12448018000d028410000504442d040d5082c050301030a22418040344900514400046074800c0b08000c20300d150030821404c1c442441740540c085c1410a171600c00600440c106022124000e04100f0110521070080b03a903221294080c161184400c107500801084c203110080c0c100c1c1240f680509000c884120faa80d00d869280c210405041d004102e000b00581d0444000c0e10813203200303803807400152201144400c0024043c247c0074000382c0e40141c5506001c140f010b00c003443d140c06140320b24015551016180c0000d015a8000600c0505100351060100480c91400c01c00901c0d1079400640040c03000d00000001e8103800307035811500c14440c6402400311b24980c1c217038410b955074900b410014086444800b5000c0131040d250040c216913028400c0482c10740085a006060405101c0c07d011900d6520360380451000842840c0d8100c0f40d00c1511612003003081241c035100004146440030300307041d2900351079200c1042d013030702240c604001440030713400c0500450040c244219003181d0b8180d41d40307641d9403091 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 756883282 1250 756882032 756882037
    0x603030f08060f0906060a090308030703050708160215130b0a1e0608030f0304170d1b1b0305030a0e030309030a1806080408090609030d18080d02060a020309030f0f 72
    0x504000c10021800b081e03042c80c1c2402c100040c00c00003000784060780d540d007052003603a030845d1501c3c1091040103c00840020b64140c065480b4070020313a4005214a0903403001000518050060f0b50242d0031070041e1450140c0c0450b03040e0250f000c000203204191581c48000c640c480c50214041c01400401c07090124492180d0848901e1403850016405200449409070007181c0e141d201c0c07071449078020055018160300083c080e551142c010041e228250600c00c580c4c1c0f0712980a80080b640007540d4090044c8514580e00302c1c1c08505000b4034011201220010b40e0f07034050949503801505008001c0009010311080d9004045008841c03420b40b600c038101100e10030380c2c036001036406502007506440708080340010000d00034101c031942d50703a850309070322a9110389249901160005400090812200b180c54508000014141d000c5c3c0d681c01c004070250088186140885810001058014050362001668005041030b08040c49550042e581c0e140c100d00f5501c0e5209462a40904010100b00b640074425010301 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 756884532 1250 756883282 756883307
    0x6010b1b030c0d0906111b010201020c03030f190b0d2d0308180f0604140313141207050622150801030303050f0c120403020703060f0f0e0c010e1210060303 68
    0x3140700c4e1403a15400156290021100c1c044180e0380020b1130428810b80b9001c0203114414180001850040056110741c2035502c02c482400d034178052107007400360060428810071004811244100620340d5810300090310030490b1207018080343c0710400440d508840c40002d010000e480c00e403520941c041113281c0039006080484400030b4071000c550012080700c4001c102104504580340140106559075600c0303030382e03a584007810b80201d0302c82032100c0c25034075440380001c10151001048424602420a0400c0f60f02810f894002c002500010f0040042c0e0b21080242d0300010443c1e0389500c18540c0082c245118078070581d10100d000100350500c8061141c1208559051303e010355824082a42c1c3cbc0d02058110742030645010805420410501829510b0301c919103802030300c03074815100203d6413922890269901c4048085106548000c21395000c000d0f40700e1012918100c5014100903610400040c1c1100ba50800090040c1002442d1510302c81081c0142100c0f0310060908104a58a07414010940c86075800c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 756885782 1250 756884532 756884537
    0x109090515120d08180709060f050f040e031608070203151008060601020a0f0501020c0f01060f140f040c170c090f010203070c03121101091109100806010b1b030c0d 72
    0x2480d42d80d18400411000781110301d54450100548544088541c1c814094919000b40d00a0f014081000031103409020000d0011213544803080d800c0c401004081d070f00b002c43c0d85114030314180d4071302c107075403001300a40d01c0c85402004507040003011814030144038490200025410f005100580441c0440e400ca5140100c0700141c00d040e006840c0c035400c90381d99002b590124056401540c0550004000d88402130320300d44910000f500340544c80f80c03002d01c0c007228404810b407284d44895090144100d0f000d212002032841c00600e2140d00352510100d00c980c120324035814000d030784408240d40e26500031340250141062600f100507151409507201c8209400080c4118410240141d21144640c8000203541c1007030741049140300441d00d103655001001390f03510344440502000580c0038114070002c0c42407210b82d40c0500d07400640c1100c0c0100300134444100034076a080f091005203061020841c000b034020b0545007203100041e17807151013064100403108041a01c4005100c00208203440350f001280101962150342c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 756887032 1250 756885782 756885799
    0x15030307051606140a0210090206120f0106021209010e0f0102070b03070810140f010804170f1c05040305070f05070f090b04050702010e2d010c18090c0801030609020109090515 77
    0x314481c1d1040c03040811704c00060b0f010245a60682c0d00075405002c4662008011614000c81d0b41c1c511400550102c408a001640c0076004002c010b40600c03d0764501035552240919028501c1c0c0086c0c00496a00c030441d001d690311401d40348484c0d00030003400c8081c00440c0d0000e9183e00d04070038000d0410104441c40d500c55000604009415402e0500308151010010081d004003c4518011a44d10380c00070f00c180ea0904240014518460f9024010910001c04048903907aa11005010054200403507a050310814038240802000ca1f034803509840d1501c1e409911200390b07032100e0038404e140c102c031034000882c0105a00310010308103100c3c0e8050701e43c41da0300340d5045c030140c0d9038441c0c144d08a0301c0742c408400701a001058030002c0d40c07a03010004178040c999200d850900c0b00140c10a01d00711103d00c06210301084514518948044564800000a0080703800c144128241008010400401032000900064881c5101000c43e03004d5480034002d486403800c10807562903c035150380510303100445694084c4c03001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 756888282 1250 756887032 756887057
    0x110f070c0e0106171312020f0f121b030909180f0a03140d060e0901050709080a12140d0c0801090b0411042607030302070303200615030307051606 64
    0x21401d40d1812169a5251040c1c800301c1c0e0006007000f00d1008181c081e031003148020440000302201c02134030421a00d6801000d001d480407504d01e140204095106100d42e04c08084140d40c00f00310412120701c200f0f540e0302040341c00350015030301d031460107140c2209078440443c030104030a0a022000310030409090208680345008140136558440485210180000c0c242c09100f03000e83d0100c20082c81403d04803c00081c0e00781c0c3d1026178505102094611415594480c1d0070700620690050210028000e44405422075204940e601d05906d54100e100c00148008540220340c501154016036015082042c2d080c0701d0888280380c02441c5490034020060700c2c1d03140c0b41500100d403c15204c0c2c1ca4030301640113011072401d42007000c0c05500c4020403000300000c5011868400a017001409208000d5200c0d4005010302400c600d40503018403101600c0200001580c0e441c0b0070040300029226802c0b940d0b040f561a1220a9030740440d085108640c0098083c0c0b25010154a04013280c209803800ca801c5d0355503a040c1e6081 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 756889532 1250 756888282 756888299
    0x11107080d031a030a17040308040909060606080c0307030c0e06071406090102071e06330b09090a0b01051911190302100b061b0102070b150a18110f070c 67
    0x55a02d929505603000400c1d2400080740e040d050511b03052000c00043c10682d8940e180318065002e600040486900c8410100401c400fa00950b005403c140c00d000465180507000c00820b030100800c10310070951100300c0006440c2c0134000c0b2055900c00076090380d69548007403c12029650461070281040d10440000510b00841031099a07003203135010040240e1540038403e0000d05070805001526100d80d5441e9003001034000120064920340b44543c04200c3c1c90b6540f484001e0b03403003590700002d1600e03810007140d042a80d8001c02140d000340e0802000600007100001203401e4013403400c000c00d01d50301c180d00c0c2664498100c16809000002901101d400a03103403100b00c0c440ca10343c603c000b80943d00144103082c80d80b44a0304410005100070301520b09040751a00c0006540440d2484107165035030000b1f07407200788829403c01c40e500000c8254002c25846901021902c03103d404d2251058085012900710160038080d04180c1d50700c1d00480031903499000e144126103256120080481c0c00c1c4c4407648001030039a9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 756890782 1250 756889532 756889571
    0x1503060f1c03030515030d1d010302040608040209100b0a050702121207140a0f0326040b060616080417060a06030b010b0a05070204060f051309020604030f02011107080d03 75
    0xc41d080c641d60301208495a0540c082d040103000b03000102c1204030b544c00b141d24100000f2007501d40720396402c0002d40c1c0900c040520040e01040250405004210a10100b07400050081d007195055400310400e03500c0395601e04280c3c10a82040805000001c0c0c41022180e12901a080e035030f000700c0d40205586040c54000d43c1ea81804241c510781050103000700303800b00c1c2c611b40008040007a03000039540c3d441d84030f80e10044203450405c0c048010030715045064500c0f0000060100c80f4810a4451407110704007030702d40701041c03200140014821000082e111203a69044032127030412650180e02561a20b885411941c13095610b004024103034031465000520515a90040c18100d030341100c01ea00d060390034207060080c0c40d8088080f5109002c0c0420840c40180c03103034401c22000344041401c3c188941e003070400308410380c8078900c12200081d0078480b100c40035aa6483c01c980407664490014402c000c11803006890b1555600c100d54900d005030100080c03e00c1005c100ca9003e1011035804004110000c007903210b445 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 756892032 1250 756890782 756890809
    0x40e100e071e06023d02040f12022b1202030414030f1b030a02120f0606030a031d280e100503030f09041e06030b0c16030f11120403060e0d170a06051503060f 69
    0x5404840403502c4bc3c086c200c01214a0582e140c0d03640103135a1a5100c100c1c0a40c102d500c480c005178000203081010800b400b103540200c002c04c601600300400341e031059554601aa485203400d204500210411944d003c0180020071130780a400510002c90700d0a5564030791008403041345950041e01f00261045c0b80100c0c5c2c440e21141d01d80c072500c940070050244100b0403049449181d401000c241840d5000482903d6040c03003003412070303d00d00f04a03418a81c1d801b4a07100b01400300441c0662044c018407081d40c021041c1e4a0f96484501c80039201d034000741c0003402810007864400200da50f0604120b60701503442c1c110a003500d00429100311181c451101c4095103114902c402c04014811003c1e25000070301c1740080c0201070502d41790140c1000c011009060502c03004100d51000c0c4ca0002808208008650060090050022000c0c006001592380c019003046030604011090703a9084002800010850b0f01410103010082e0004560034040075002000b988185c4a0511490b0100f9900f6a2031421444c4400f22 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 756893282 1250 756892032 756892039
    0x608010b090d0206030c0a14040b0d051314060709050609060a0c0f0501150602060a09030e01050c0a0501020d0f0f0b0a05040e100e071e06023d02040f1202 68
    0x2a8038001103418640c201e001042d60046040c000c503000341e500c0802540c010028020007039030b2500070780d402030840c443c00601d1142045060204000d903245007000d0300c020704043d800c04512a5210048640304140c00c0038020950302c4c80c1c00300c010a400300003a59622031034140c0ca403a624142c4460801003903018407000303190710180c00c000800c00781d0303c11502401e0b041c1c8100741040311411682d68013800c0d00c41c3c007120800706a582c0b1904020040d810000305810500000c0200007075851070f14020301030540001807505000c400245a1076800d07040200b0110740d0340000007191031b5003209580a0150112100c541c2500d824915040c0360544a40f003078600c0c00400078441e041c1d10740382601b40406000d0b0011401c800c2d0064400044075142d0030300818a24264202c09030404904180107880b003240000c00303800342c1200c0010140146030f00050040507128250940c505040131903a07000c6042c0030038000301d41c0701d480404044a4801180d8000e00709035840310740030488458495004801d58110304078040e50 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 756894532 1250 756893282 756893297
    0x3020406170606091219120e0405151c170a030b011106220209011502010c1b08161506050319030c080c0f1506040b0405130204110c01060603021207050406 68
    0xc8904d020044100a1119403003070710f1024592002003c1c42c0c06841000342c4140e0510481f00c580640d01007039880c03128034112010069030602c0f8860900d1240319a0704680a036800d86000040301551044511403e07901c20300d04034000c7c0039032034840ca060304510000d1001c03d00b00028030b0b94560084592000d2075190303500420084d5030324004070502490340318544c07241001020501d409600d420529030f000c2c00304521800300c511090400242110607826081e000c00403600200c400044480c071250020980001c9200e072280c10000f14600195600310004001500886c2d0043c001c000c04e8012f8400c5401c02c03415035568050305c0c0d200d0f01c1a03080007070303008000600d040c048000040010002d801a0300840d0100c40d40088140005494000ea00e400f488548001ea020840149862701444020340d10030303a0140628281010039100b2101507407002031107551102104442d0981c1201a6405054220001d000050b0340d02d0b03001d0002e612900744400c100d0b1121000541650041045030201c5400f596003a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 756895782 1250 756894532 756894547
    0x1905030a030f2c060604140711011404140610150305090705060307170c130b0a12110c1b0f1003020c01050406020301090e0f0c040905010905060703020406170606 71
    0x40040c90a5240340c038a50380e8500043e1607540c41c0f07089404a6014550000c0c00048a082005242c80001000148154140420325a41c0302181080c150004c0e00d80c00c1c0206000c008181080c00342c000007021201e1100d00350100801d11043e601354203a00201002a10705980350224800c51001c072601580307694881110341c0301c0240b41710f54000f680c80030709a025607482985900004403503910582c2c000c00020000d0350350030450600d05030b01030b401240078804035143c8100c40c01034485d240040d1140740021440840c0000960740501d840101345c00c000d800c02c0201b1654000f8001182e00141040801031107003180003041c03104440341c2c0b81c8100074010031003070f0012920000c11400c0c05caa945400200340d003d2003802c0d9900824011705018078401c0c20056100c0d81030070414001c88400411003034031343d400900444101c81001c0b0f000c0741010016078002c110744280342030180c050b00201c0300c004c0c100e2189134100a4107540c10341c041c20a503207943d038880092400500c0c440045080075510725130700c1386007000500b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 756897032 1250 756895782 756895787
    0x311010309020307060e0d0c0303050a3504020117070302180402040f050d080c0d0c17030708010623121501090303140d062d08010908040302191e03051905030a 70
    0x11503002c6d2000300b000d11803101c01c0d80c2e502000b11007035000324003042c804120b0303040140d000054542c050000440259120000c080d140c140c02101ca02420f003500c0c4004046010b59100b8117584d8401481203610600307078144000020002d500c0f602080d0b0b040242008555201d1406008940458078800d101908050510082050b1007102030011542800c0c1004810803505003801281c403024866107071100000760f14206005600d05084800e11200d10800810258540061750181540d0325031401e8010340c411800c00014040308900c034110104008a4008449c90340525250700c1030303041d82c0d0b0744104181e070000155601081800002c02141c00c0720350b08542d60f601400078140c003d000c0d01d800f1898a9130382100d1910b52a194401038826241c4480c400b07841c1d4440140740c0000d1030000000c00501c0c4c0580c035000c409004a0000030b1103011070401180a5201c030711000030140401280a260126a040e9020640005880100ca00740208002c100c14401000d01640425801c4000b40d4a00061281d04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 756898282 1250 756897032 756897047
    0x4060b0103022a100212130c05030712060b0904080d053318010b0414310b0105070f0201030c1806090602060907051005071e0606031101030902030706 66
    0xa150406500307202c01da404581001942c030400711540c450101004012540d41c2c10301544889192500307004001e2004030310007407124103500c140c0c5c007080c0c2c149103451072814281d078081c5540026854450311001050240100e00d205441c00e10802003008400c02c0182400742c0c003039017100c000d0000e00090100c92500341302c54002590200100043c5103040c20310005a900c080190f50700c0742c9850f00243c40c43c03110790801c0c28503182900040c080310501c0b5854450920389500c910701441c1d006207090201c0007100e88071400081800030f44600501100200e007480050003c03026002d01c0c00c0907041000344595035005004462805803c04000d5507201002c1e001540608001590f260411040741e200c40b0b6600d21740c0e610030010f000700c1e584500107140352a100178a0904080c00c4009581c000b00010861036807440244400b452903401e201e910f509030342c20000c00e035117800c6c00c2808040380184d503082c00b00030301a0f0000041c0c074850354009031048d01d600b004400f00d64003040000e4042e400020180500c1d4015680c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 756899532 1250 756898282 756898301
    0x18010303140702040f05090610050f12070306050a1b080105060f28020d030b0102060610030c1106040633030209100909080301030c060f020d0806130e0c041a090406 72
    0x507498070705141c59012800b1140b44001c60302030b0315030f07031010710401000030720406801040e00c111110340c5600740b2001644080c014119248202821041d011a081041c0401402540c0124041009184c00d034000d401628440030680c01007001251440d55042c006d401c014103880000d84100e0405400613040c0065511a44010509491510a81f194204000420750701d8820316809400c080f180190041c06a5064000c468195013041c420481c10381c0300c07803a00c104560110728003c1450202218103840210f00c0455084c243c1c0a03500c100401d02260f50801a554160800d1000c010b415001903452202c141d00010700b92110b100c101000545080c001c0e082c0c01c1401e001c000b08030250348808040484840b044111403007030b0040300410900c5a03003440900100001e0400c100c2e522040c260094844202100280a0003d058081400c0b81c4450800c040306426800082240b21108003025959014115a0621507070030a048041983c051010030000c0b000e0160035141aa219503580f0b001400c074464 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 756900782 1250 756899532 756899567
    0x80603070311013b132d1d07050a090501060c2013140f061513030b04060203090d030e0d03021c060f140906130902030c090c0a0e18010303 61
    0x4151054100c07004110a85a086480d11020030349909411700c030041c0190510500c1c10342ca0454000d10400324001110311940d109101c070b0000074558040003005200c2c00c0381c409060180d01c41c00741504c460000b00c40042d81e1045032901045581e944101d420348030700340660000502c0c4500144005100c09400e03000102c1301c0650410300003080c0d4082002c030304210440009003525510341212402d0481c03890783d0003825000000c2c03260714152010030900070f1600f0202244810000c0c62030500009050200701840e1f0045914120b42081d04121010b500140c0307810016005074607401401e14001d00c034104083d500d4138003500b04100804000c0c0e00035004040008200c10b55510744003101406841200701600d5449000200c0da070514150054041c4100482d500a00c801e03000d0003004d69401590b0442d1404400300402d519400d4804682061009031041d50400c00203820700030400c03800b01c0a00f414450a54524404540d20320812624028042c3d6100c0c0c03c20300000180042442041810515076411 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 756902032 1250 756900782 756900827
    0x3170d1b0f0e060703020601030f210e010e030a15090501021e0a090602010207171c050705040626011403160306060501031112060603130b0a09020108060307031101 72
    0x1012040302040040c0024000580d4a10301000d00d0b0307000382d004070400d00240c81040c182281c80e42c0180d40c894040c00042c0c4840c0e56089600104682c403c0013459070a62600d8198800d100641d000d000c0c11710918565020407117079150075010b8140000c10070001a00030100e010404003517070504d801449080002e9619540812011211072400c1405010240c0108505503032180b000b6070041c2170704d070660450303070459004000000101c0c50100448044a4060121a90f40c001011083c011140b42d0000707600d04504080420100301d410002138000c54040c3d4589035625240c01e0740f408803811800000302ca84a0548005100c4800b9540810424400141c211503508000c0303624030700b4456142c0d1048843c50b403200d8041c40103503850300480b401d030310307100d42d170641000320f07003204525508401850346008440100014080c10158500544c6190b0400390079180d604044500e4800385c560700e1000e0740800d0642d00400c4490500158950031030350400840c0008d20101c0d001190140c100e503501c80c1000c07024 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 756903282 1250 756902032 756902051
    0x100e0307030506070809070f090c0c05060708040c080d0507060c02010902030307121403061e031009060f0b060a08040b0403020703140c130b0307181506210603170d 72
    0x8020320406540100010310452a010100415180009141c61a185c0001c48100541c0144e500020140c4048080110304152109011151208140d001501c10300c07031501840b4026400c000d040c1e00070342c000c0e449080b02540f1901c12a9803080c90319400c3e00051402c01890012070069440032a8201e1144000300306440242c00192560300b00080039907a220700c0301d6252303400c0c0303070800203c1150f4009401c1d010b00714640b400000e040f40081c54000f00c07800490f00800d4040d6070307050100380c4182103c00c0d000c002010007410050003c10040041e07082c05071401c1b050610a10348042074a084030456030320480595200c4e52122141c1d1000b80044065228403000400042d001030140001508503000604107000c046080080b07190004004a0700b1501c1e110340018240c07808100041569a03081c409080201c441804070010410142c48041d0180c080c00040764090303201c984502032640c5003540e040b1043d6101d511008a80142c800104010503c20b42d5040178240c04019105841d8540300009103070b0507 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 756904532 1250 756903282 756903289
    0x1260d05071b171c020a021309051e03071505010b2a030f0c0607080103050303180f0304060302092407060c0c0c090c090f0b09090c251709030c100e 65
    0xc1840d081c5442e4100d0021404034000f9020030141c07031384040c03004014070001c3e0f0700842c10b140004401b8020703060f100c14605042c81420415090103119045403843c2a045200e6030036181d4210b030301c048034810211ba50880e0703070700c081b40107250503100411000c2c1e10300088850001800b1904199004d0900b0401052107030000301031006c2c0c603401c2c21025a99540b4490000000c0c01e00d64000c3c03200041c04000401800414030000c26654011410320002c00032811682d103052030b0030101e110303414040c40006408600e03240d1540140480d01030989180300103444900c1d03040c2c2c00c00e442980c000b401070317424040840400c00c26008181d00821034104080001e2054661221a80840e00701803001521039802e48030841c0d10403c0f4a004003100c80c0c030340c20103d05000c0c00b03800314810310032000d1094051001140c011000e036000c5501004c072003100000c00400384000c0011400380100151a0440e200c4141b1078070351034480450307618680042c050f2201c00d401c5010001c801c41403031100010800d002401090944 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 756905782 1250 756904532 756904559
    0x2010207080a0b01500303030907031110020d030506061605070e0c12060d080c16050103050745080609120a0813080d0501260d05071b 59
    0x240503a400030202e40c10f00910360480c00100c03201d01c55450942c07001704d46410186602c0401c2c0700045d0082c0d081c40d00032500c0484c2c45040e000100b640340c0030000521905440c001060000c5910030440c2b800040103200c100302c4000100c13540c45000d81c0268680d504418841c1d407001c0d0788050001d00301030405c40c400c88100000c41501908440a6001840a014080d8000e402a5000c660760100500d884145140310b15082000f4041501800c80f14040c2d170100020b1400f6280190100411940501c2c81e02540f28400842c81c482c81380800d00e0070703001c50125072144d00c10012074034a05143d1503105541447e032040107540400c150310b8407031466039183c04407110450200300400808009048504048004038104030382d001e03606100320010800aa0503d801c00b101951090a500340050080110b060400c80c43c0705200c9050342c003620b03140021900448911851501020300c4014804020030210a180c0c1c401d10010b400000c68801c1c0200300c000b80101001000c043c440b0390008079420ba45900303020554 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 756907032 1250 756905782 756905803
    0x303020d0e101407140f0930070f03080c0f0f01092f091803130311090c180d0c0801020442051306080108100203061c0201020708 57
    0x150095440000403074010f00031900c40c0d00d00000c410050341400c80b00584901c1004500c2400084041010940c0c1d41410003592800c001c0036100344480340085c2d440703010000016030745a9403452032110241303c00b140090b1240c06da9042c0c010801406003191a46801c580140c800040d643c4103841030009840c9081c450050256003101c004500a811460b040f40b0252407058505030024071910b241e200e03131030b50340d8100a00c0002520425900c1e228080000b600244000010003288070003c0c8200e01c43c032a04680c003040b2070003001c0c85041405a001005110300d41070300c039800c40040510500c80240c0d8038a02002d101c25000f484000202c20550b509642d060301070b480341e4200e075808901006002620350154680711701031510040703004000c1c0c214988450b603084035000d24000f0304040203112800740040783c0129020310518658140c6c0d40c240200183d1090245400038012151010703421a45802a80e0107020014541c401d6407040b140342140c1420128000d82c118864040700240704401406101d045 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 756908282 1250 756907032 756907061
    0x30a020a03082515020f0f0c030a0e010309050d0e0102150118060f1802034c0f030f050a08030c0315010819050a0213081e01060b0f070303020d 63
    0x1035a03c1c103081c42850803600300021480d112009040b00015808480340b107018038984100584540464a00200c280110944542d07024070001c0c8034081c465000000d0803200a03c0d560b44030345100d4440044082d1442420014035a60020f04541d032601e0282045203606101881100c50401700d45000040303004007a44008524007114000f00c0728829580035120107000c01c007040c0d9140c1031802c0a5040701400c0c00e0a680b02455002c0003080c2685291036500c116030412140c42c5501d482c0e00e003016041030810048407448480800d000b001440c40842000003100c0d080e42582c51042d1454860704070701d0951840450743c2c1e000e02040c280008054001950242802d800c03100e03224a0305088060503003015a40c820305004d1060100300351005080500b00d1825030340d4070045050780340c502d1410041c0c0924408590341c003811031004942024006101c001c5221034845010301202e070301a40e80d080350002c0c000e1801c1210100b10b0500078100c0480280802413091900618042850703103090304a440a0107103040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 756909532 1250 756908282 756908287
    0x6120e0f101409120d0f061a0a230d0203150306160e03031309020a031e14010e04030504170304120807050f0105070801090b030a0b0411130605010507030e030a020a0308 74
    0x55219401c4242540180d008005003500c60b24944c02480a005085004643c5074889030506055a55500701c40c00400400b905c1542101c2445888030b0141c002820400004840558003888519481450030030142d4007141d03246004404556a00650310062641d4440a9170221141168034200045480317106450404041c411840c030000308800d59100c4268480d9005002024a41a88541020494903002d80050756003007143d005401804448a85c1009458000e038143d5003148103801421108510325000303207407a80c8441d01c1100081c03003500c0180000710140001c7c0282d00e41110464110350a90044030f080c550344034011010b008880e2001c5450220200c1e1a40c100202000840210403041d4000c0c4000d2070002c500070004501403040a803886d4840460705a00d2f00c0c01d01c401c0750032a40101d20901b8a1400b03042581000005541c01402a61031100281034040c81d84078020555005030f40b0705140041546040722442400089107a06000e030480c0d030401641c88520010041d8400d0b001940c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 756910782 1250 756909532 756909551
    0x303091703060307060305221a0c0405010909090f11060c0f0a060c0206061f030f021314011701051909090f050106170703290c09041506120e0f10 64
    0x600380195031744100180350502c81031000400a02800d5880790300300b44007000e04401c03103083c40140031100540c4200541e5514040c8444842040c2c024070644100f80c80300046243d8035103c04003280c1034680007034050003616212000080c000068401d0070000205294140011408a5800c0451180b03202800360b102001e0003080000d41d0144209042c00d500142440b8034003000480c1304001034413100b06010b40031125100a042c0a0340c09120142c0380c048085444007489468501060a80d01603101680c6070015501f20b198810300c1106900702050b4060121640b9040511207052403416000151482c070b0700b03001c03e50741141c0c17151107041801b41d08601d80c94502e0741040740c210781454004011102c0175601409041c4030000b428000c80354030900c1214500101f1440001003d10321b00d0601c5003540c2d1a00348003502810b40701404040d04122410424404081c01480912585108002c04507008064582c226001e584c41014030040380300545800408052509003004903003560213071100d60b901000f9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 756912032 1250 756910782 756910789
    0x1b030703030b060c060601081f0617060a1505030c040b0a0513090c050715090b011e060305071409182706041a04170d1a0a0303090909030309170306 65
    0x1d0b030300080203407035051400246004554407240d009001506010501001c181c0086101858484440d01d0b1014160b840b91115801030124800492020400f40760402144c554580040940b08072817058250b1403030700038120815541341e00001c0c0f409105400a01001a802200e4402010000782c140d031003580d140d400303201200d2801b11a030400860241780c451454050740d0030000b201e51254203c038461045c2141a0701580140083c200001c00501c0701d40000120140350201b503c95132002a040700500035210b100440847d04229a02e50018224074501c24100b4004001006010409000c2c0400348110501040d6001d10581d42013601410030740c052208000b4143c920403110a171040942003a05064941500c40700710040140c056401e4880401c041103d00890740c0070f685404040e00e926041d040300e16100070407e154400d0ba0340029582c9404142c03034500401c5c0242da40c1070f12503036242030424000d1001002ca1510071014580d0f9000d000000c1009284d4003c2c440c0c103040c0200d0b40c0c924000050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 756913282 1250 756912032 756912041
    0x60203041101110d020607180506040f1701021809060102030d1e0f051302091e010303050702122409030f03040f05120f0d09020103090218040627080a051b03070303 72
    0xc52a40d80c004c0c00601d4881c80d4040b51558024003180b03800841000700020b07480b0a8000d5a00044c0d000600240019071040d4446070b40741222604000d04c2104410f003c81e26090b03108011a05018014070600c0c001d4030328103c0d00c2c890300448103204480c2043d0841c6551005c40390000750207030420b281103108202103842d0f0700441c0303000448203406020504201c03c12403c1d80700c41c00c070000c1c4107602c410300151014824505c080c403010180004038555503540d00300070708076a021040a13405006804c442a2001c80c00090054a40703c80091442100098003842e0b680001c01408c820000e0108020615240c0c80500245000303a000307a44c0f1241e810340e40d29000e464982c0607042c81c0352809050094030705c1d0b81c5581c401d640c032101854101241a08a610049004104c0c188000350300803030140b40d19043e19487c1d0b104a00c1644500810000449003802c003014a45001c1c458100c00d24888243d90006146200a0000100e1505000317003000c0982c0100810100074520304509a84041406824954103000c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 756914532 1250 756913282 756913307
    0x120c0b100b03060d02011815090506030606030604421d04030309030512010909110f0607082a0a15020a0546080a150302090c0403060203041101 63
    0x40c4101020324124810382507000080109100d20f4290400c038003564011005004410350400e2481e540980b124820556121840d618400042051901068509145003100c9c003d25000340342c00d04542e114410080036009980910f141d00727001d120b1102844080f541c00c0121514009440c2070340381458284480e912585a1000d240e26070400080c0c01a8040100c0c030070b40068041c90040313058141d80c00c050300c80d4402e4240d0740d81c00c4c03c0c101c00001500002648030b5500c02e032244100140030804101041803200002d05110350140e4200858000601448010030f4601e001c40c52200e9640c0da0261001e01560300c0c0e00202166410400f4008200034a2203030111041c3c400050440c02d060383c040e40244940035485441d1000d101500d0401c0c071a1002e105240340307102d0001c40b60451641c03030781c11102c40c608444ca844400f203405040480e5009099004210283c3d00744134022035840e2075038007000a090005008d07182480c508100110100c0e0080c00107510681c043c1692002c05241240014400d141d10708 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 756915782 1250 756914532 756914551
    0x40c09080f150f070216170d0f0e0105070510060305010207050d090807062f0c030f01141f030656040605030a05061006050f090108040f120c0b 63
    0x2481e84403a1058009a40d001080308400c410f60395146103060b4035048a86800906502903003000181e083c00d9202c020645200d1042503c00d1404124015070303000c003140a0503004545142c01800d0b255120350007800300c45000300c049800e41d01108a0701011500c4039042035805075000900c500a204080045400c00040d0b850040700c1180b800e542240c882c00d40380034510400004e00f0031101402e1903031780140600d12160301c00e1001204000c150ba0b82d5041030507038484c080e0050f40c4da0102210018411403012041c1108090705035a24505032400280c242c01c003952801030b05a4010010814501c0350541f13501419410100380c2d443c19484d054140918012200c0c8192290101440030110710f40c200c1010541c0d118841408100000140c0504941e42281d07030184110100c280070310500040d080c0c080e5219040380f00445403124000c480500c07500030f48181c0b61004024540e015446030708440c0c0d01900500d6014800c0c0e101d96100d030b090103088081203000446a8501d20309118035042d40e03e80204021 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 756917032 1250 756915782 756915793
    0x2090f1b120a090303020d05130201020706050a0918140709030203060a0c1d040b03030d020403060507020604020a1205011d060a0c051305010318020604170c0319060f0605040c09080f 80
    0x5003103034203011030081003002c06640b100c0c4002c04142c0240c042e40d44000c80080148072514040403050100c00218000307030b0052280450001e1041d0290044074000c117001d41c0e40c103501908100c2c5554403c42080341082e4119642e21191a11501d004003407409160541d40301c841e150710f180101490003401401400c80140b42240c410141500110001c0926040510321502c030079004001400410001c1851034050000180100f04005290b00801c00d50b8030980c4204800d03100e243d0200c1ea102e50454009400110304030041c008182200340c90b5110305d10410010600301c024494a10b04000c0e083d00280c640d41c440d00030312801d00024025145100c01506d443c41c01d050380d0344403405039500300d803007845d050541c0c850880210b0214030200c425101d4010380010f54480e83c8140800d01e049009001d10441d024407480c010080ca4040345807071a140c04418110000c04d47c5498250090044070b00e42a400d80d60b4510010300c44e125030103914000b80894481141a510300301195003050240c48a6a9813500b00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 756918282 1250 756917032 756917047
    0x1017030f030105190305030a0201020a090905010e0c0d060503031b0c0d031b0312050c0408070806040209070f0e040f05150405040807121206080a1403190e0a0302090f1b 74
    0x80c009490450ba8101e40e542c0400240d03c950038500d03140c0e03400150403400001900d4803180e4054000341540380c41a034030040304590300c3c1c02c42c5080300c400380501105040c244001c00e0304a82803401a12030154924000240d036a3b40740d00003850f41d030000c500c0300603540503600010050581031054800e080b07410341da080001511551700070017515a04550f0380c070360f084020300c240c00e04d84116156400308003582400c000a050440100c41260843e2003a40114400d080c40810500c10200e4480d010740e5020382690f1301034549000542d43c282c8044400300c1001300c480440b132041d0740c036805a40c24100360b0320000a060308201c022900c103516031458460085040c00103100015001000700c030344258000e01c4007694002d00e80e10480e18000892481d40c0382c5c90415002044018000c1081210300e441a40340300a400e030707c1e294035900c901902e84c190035085000620304407110b005090010350354000038001240d25890b64002a900401a180b156500c2c50440400040c030000140300f2820f851004c42681c1080c18 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 756919532 1250 756918282 756918307
    0x90b0703060e072001200702030706021b09070c050a1518111c0c0806070801050f0d030809190501290303040b07061103040305030f071806140c0303101703 68
    0x14074540350790381c4c1d149500c009180d4450a5111400004a1980c1e6601e0200301d03000080081c1c00c0644141e06c240100840003842c40d00008a140719080d42c0580440c04944040402441e180300520500500c00b11090040000f1010700502107d148209005502d0203a00d030000011140c03440350030000c800310349071440c011514907064218420412540c40418010141d01a201d102c92000010010740c8400c00108001b403000c20058851641c0365a084510b23aa03500800100340b264451241d088411444d9100101c0d101b5001144d002030840700b10390103a035201d124840c0c040d107a03a4065400e40d640310400e6402c1104481d051008000f0f00007015030540541001035181d10682c0b05038200c400f00003548004000e11a000407840c12041c200081e102c0c0381600713002d0081d500c121201e030681010400002c40c21405120071a60642ca076170311050b4014100201031b262080c0c81c1c0100c1800d0300c000c0c009803c680000b04000d51007580704082c03c0b481d8500d408428207088480c1400e1803c0754109001404c1e00c0d91 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 756920782 1250 756919532 756919547
    0x1020d05040e18010903020a030f0e062d1606051509160e031f0b040e060a0905031201090b030d020304031a070e12060709050a03050a0303020a12090b0703060e07 71
    0x141000200c07445034031a4001c14690f250b280d440c0003032550070510304505054000c04d648a07002d009071900700316840c902004a030b082d4111041150b119400f03004005a8006105682c5280400701000e9108100d601e1142d2040d038010b40034150004100f04c9185013048441d00483d5007210818003101c08001202000442030031004007216030b500700c440c040c50700b002e2003046a070100042c0541907a18241d00d12242440b0b1040c6043c022a4080c10b12030904903905080c0708105062a00340090901511082d295001903e14000c003130740c4600c814015004812540020709000384010034001541e2007414040c103040079910180e01c4159001444104007284141d5101c10303404440e224041c0071543da0120a0f170b9a020703000103c5800c490240b05403150101c00050690082e20750307450700030005654030208a070b00c00703660100600b80c4d000301d412040002d00a0b009401500d019042c443d9841075600740703400c1250007e04007580c070f0580d0070007444a1980c051140c94043d10071001447e0040c50240400340ca4207 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 756922032 1250 756920782 756920789
    0x23060414040f0f0314030f01060305010b1905033d0b03040b0105100504080a03020106080106080c01050409200c07030b0a2d0608031c0c0c0c23041d010b01020d0504 72
    0x402c1181d2001013014410070480840e4010000099100c0c01c001c6850034008409004044c00710b0314203c00810600d0b000025106560910300201c1c01c2c54428400c221015007001d8031411941f01c9284503130861001c665030601c0900d100800840c842c22810070690102c0740564031410012a00300305100105808903d840e042d10019207160412200507481200c0300e100d035500a80c0d142c050040500304055041d0064022280c04900078404a502c590340b8640b100b641c80305807408508204170401150029402c448011038015251600f189850221004a54003802c0c11141c9604261418001c000c03400c03a419130414051030040010a075800d00b04940d40c01802402c40325112803400104d0415881d410140207400b2440c00e0720345441818180d0261078041245107d01c46083c40041034a20384202e065901c81c80c0c10a1040542074640051880d6028002d040c54042c03840384080b180054649004015400440304101d0701c00813200804203003100d400d40f202078115008001304169480c2d209090b1810b9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 756923282 1250 756922032 756922043
    0x30e031203060109140f061204030206090d0c11061605060a20030103060515040f06050f0907082202061c0b04090c0501050c0f011401080d0207081902030123060414040f 74
    0x41ca6805c0c0c0029012051000b00c0700d5100307000080741c61b00c0c400c080c0c1c0c41034013851003502141d585071600310600d80c44501060100b400201c0e810450703000300c2e86600c0e024500304400350400740380c800400c20740c0f510000d00543c1910305a1080c414070020810340c1c880d20700070701440c0591800120b1a642044074031b101c188070103801aa251000b089840184240966070300000501c2045104503201d50200a006184140d0744980004000042740d400d000b03590798841c2025903140340c20340da0790302d401144610304110300c181841c40780c1d0052070068903001c000b80034004014a80d01c0aa94a02c0f220700309644044000034011810034040c08000b40f08150310f4010758509081560f00c914480716014540303801902601c00035803c0145002ca8840703000c02c00780c10381790080240c40a0190400c6c0607a0703140b05606c0780460917400841000c2031808a0f03c43c00184510040022549000c500d02641c62100007400c3d0341051400c0e00c0903c07400745464030a59820091b10b05000500d440c1ca40c5403000390340d00700301c4003401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 756924532 1250 756923282 756923309
    0xc0816201005180d0e0f1c05101b110c1003020f070804060f050c060c130806100f060f021f060308191206120f0309080a030e031203060109 61
    0x4009a00303110721001d03500d212404002902d864100221500ca84070320980d8107009010020182501c00c072141070044c80060151300100040e0001c0c050a890b2040e40303040c600801010042c0040c1c020702240040d00c04505002c1120007424003a241c01c2c17802c01d4213034003e00c0200c00186500100100f0f214000000031183c0a4103203250a10580c06446080c00450394000009446000c11030481c0240069800d030707645000c40d441c03002d0350640e041d101c0c090100d00f00768019070004910808030300003071100c0d2402428901d080d50317403842c000f8a8101c0c1501c0049401301082010312070070314254495401041a45040b100c10386884a0107511201c2409140d003000403c01c8003406420411b03080300c0015688682030581e00c4401c06030b5002010303808241d002c0003692070400c61094401c2c40c05924240d45100310f2140004001e0390310000d803062010001c1742400201c00d0005241c3c0307002d10144001d1802904c070308138400440380401d42401200c0008840030381091003844050303644051000260741c81d2143e6403e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 756925782 1250 756924532 756924587
    0x18070203040b040b03090c090103020303030a0c03020d020318100203070f050702191d0c04180902040603021c020a0807080c0112202512031d030c010c0816 68
    0xd0462149410581c6204400180000d4040018004600c150042c40a0b01d00304a046030410000301d0080c40003940c19070090010030610b01e0b481e800042250540e0400610305000340b6a0310050303800460f201c1150b5041040c20269a0740c2c18481c05011182032070086140d841c3c0150080d0002d01000c8280c03041210201d41c00b000c544800301c808003c8500c4c00031840b511580c40b030340c0d5510030356080e0441001454850210780c68018050035101603e01e0040342d041c0700c850f4041c00900820b400310082c0c1c0c1c0300f500c4400002c003503203501e00754161018000c030889260020324014092802095071000c1e00c06c1d07112030000c101d481d4010032a51841003091034050099407050030144003a10503040149081c00c060110f0840c0401880d00501c01400060f0b10016075001404000f00240000340c4082c0000140021f0f1703411746842a40203000161416820311151400d031141107185400041c00720540360b41d504034102c1c0c910381016000380d000300c42c01c003824850400844000c0003180c0c000f80b00380101703402e4450b40c0e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 756927032 1250 756925782 756925787
    0x150b0310151a040b0c1c021f0506060d15060e0f0d030c030c061a1c0c0504230f040201030b1002070b0d060b0720030304030228080d0f0f0e1807 63
    0x11002030200420494896000781031041c0c542040c4001ba800725500302d10f50811960000c80c80050810342503a2804a0b103001701c0d4400b000e008010641527102e001080300200503c40c0d8490066280d80700040e900d4100d0a24034090301903d000035046114003042c07480d03503090b951001100f20420342d0514007014038000c5490300790345640c03011a0040c0b00318100103650311400515501400c04070002c4039550034145001c10b00130ac041c842048090203101c4404414030550030700d03030002040003203100785405014034100c504003080c41003942d411000c01001804e1105540e0315001b035480398501147e2510140d07100c07a80c060b594218600c40c0804805002c5400340c40c01c00319500c10001401042185503071016203280c03005000e00e100162030740c00c003070440c0680c0450034000241d0f015079601034039120105122000d80e256507503c10823003c4200c1c806501c04100307081d06200f103144000482d100c14003003101d41030001d011480d006410208001c07040c625994256a02c00210405c44500ca86850380c94640c100c04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 756928282 1250 756927032 756927037
    0xa060c02030f18090601210e070515120901061206090f061a040606090b090d051603030c11010212030705070f02060318120313080f07150b0310151a 65
    0x41c4442c03012914406004004501c2c000820040321205201c0d9a100c0c0151414402005980142034582d01002d05130501940004400d000b9002114203503039a510000c0c0350103403240307800c14100c080458054419034509a40541040c80309009000305810f0120310b5481014800020342405e4171381800384140041c81b0f4000d4401900301106108a0850407001c068044041040b60b00691030a800011114890301c1e0304019074240305041c0f4074014010040100d401c08866041d40c0e00d000c0e1090480644a110180780001c1d8403944070800d14003450708081c02a00c0c50402c4040c159044100700451588881045a0b800700c01c600781183c0321030076420302c409612100b0b4002500140300206001d0141d03420403101d8142c80a43c42260348100d07140d6588011400203840354150050810440c0c8008ad2400e0041c2181c41c3c5180106810000c160f11040b2440c1e4001c01c451042540c1d40d0584e07801070400380002280c014015205000b02820a5500f40d080c810380d124450300c000d0a880e0041030800b1038000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 756929532 1250 756928282 756928297
    0x120b07050a03061a0405100206040b01050d020a0b031015080408030601030519050a0f2405121612060b0405040b0f0c0d0906060519030c091a0616050606120a060c0203 73
    0x1070130200e400c5407005160264041d0013124810030b00f1900c07001840b440050000c0c4100d510401004d02c030391070321013405441d46201d00120391144d0400d20100703031210000055403183c44001d07404140300c1d2a02c0485061040744a8401c420001405c0800010910703410469420180a180025041d5900800341d1420840320b101120041e05180c24401d01c20441d401021034580b491404008012400f0b81c886241d080729582c00c01307000940441081b180c503094070b4196901e0910005e4584030140c0043c00d26000d0344580103c3d0190040d031910400b844128824140c12020a0381d04100324103140d200c0100070b403030040115074103002d9400000c0320950740300152040c0f4580d400040c04024003515104000e00364070f00910340075401091041c02503081c27042841e41142e0b0040b011328481406c00444c80050907811018800326541e0040b99022a1940002031481c2104132107002d20035155450418242040070b89158890400401ca4505480010441210455110400040080821a041e030641c0079400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 756930782 1250 756929532 756929549
    0xd0f06090309030201030b03031c1a1512010e070206040609140a0c03050f03072d0f050d0e0405011d13061508060a020703050d1a060d02040609120b07050a0306 70
    0x1800341081603000070064068034802d03241800002d011405243e940e010b144d2110302c122a44050483c01d0003080e91002c100000d4903445008200000b0001c2410380000c440300014450000031410700300698403007070b230340900b0030160345826604000500035a100030180020b0700c6242c0e01c1e103420007082111803100800c1d00c0c4103c150380703880303203d820904c521412502c4243c8131070003010300e0038203c02000300484a045a1211016071140710000843c10101c150540310a1001c4096810601180080040340d140a02c1407004060207440740310010315103800e00080c680213a013000700500a105401160082c02141c00a1207542691140c3c401d04002d00c000c8030103040c26143c02d140c1083d200c144601d080c1a2803403181100d80d903849802c00c410881c42041005000a5000c2c40780310382d00d69183c2c02500c41510800e03032202d001030300c1d50b0009040b0791000c245101d006500180811469411a131880000c10496902120b01100da88890306100750090600d010854005400410a40680d005001404064 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 756932032 1250 756930782 756930791
    0x60f1707020a1502040b0304030818010524030a02091b0d0f02070c061701150e0306070302310303031e0c090501080f10030b13020303340b01050d0f06 66
    0x161000707500c584070240c064a101482c0f880c58000580703280210f50440364002c1015141d03984a0301d046a2009001d4003009a00404070412024040e00f405800d0181040d00c10b00c00c0c581000100360700c03000140f8010303d4000d40006034028003580d204440381d13034041c040e4030440103520002c000400c40c40c03040748402c01e012403501c04031240d4210315602502c0e80920806100ca5000e0b240c90043e540340511340c40c5400301540401c01481602d240705801c801031452400d00700169050140001d0604008441c4038001035070100304d0385034518640110304e0040140c000742c00b40030031200000400d2144540805018191034400d80701c804500c2094001d00c407075842200300000500d003007008040c3d44192182c02d00080d02d94021031400880600c01c1d0303000c3c207503a2065030320302451595000b00b82c81c0e0042014600c000e50f8400c0d4009610140000d01000300403c0346140411548003100c0d07508c00c0c01c0755203500030000b40101880014045040e403415918122540e4045d1500342c580400b00b4080c03220000c101500b413 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 756933282 1250 756932032 756932041
    0x1101030e0a050d14041e090e03040f03110a090212040c12020108060603090f0601060305040506010906061b0c0909060516050c060f09100905010e010c0201020c0c15120403020a1416060f17 82
    0xd0541b00410344144071818015a601e200311b1aa890145004860140f1100e8004000242c15420200011100a002c40c130500c0da4800c4074000300d812400d025420a811181040308100003450044054942001c0450300303500756800081403404000e110b2802000000f010a5035140b0400c00410040d0384002210717030070340e100d04000700075000680e03045074944901000450340c1c0c00940503803c241d0341159a14001c080200f141c9418091411070244c824141c052004186180c5500410f8200350091034045540d0030608143c0c1c80803a4482c800390100715003802402450300c00850390301c3d040810080e14000a44442038000d081207003408118513260b16110301d170810820190042007002c07207202e000b005420065078040e030a0b0711500c0700e09085500280603d02c061310701034244200d8031010b10040d501744252035190050201c4141c0d01500035a210305602020864110510602020b000e006000116920300a21004840c9400741000380f0000a40c2c1c440d07003d10071020005d020441d16080083d5041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 756934532 1250 756933282 756933329
    0x307081c020c10050702010c030306081218060307050f0c10020d1d0c0a090e0307080a0c020915060403030305090a020a06030e0705040e030a0f05040905041101030e0a050d1404 77
    0x1204105016002e007541c01005458882074040000100d0340754545404500c0d4011145420243c108400741903941c03401141c02003081044000c0344601c0001d0550310410b03c440ca500c04c0f44101c02003441407a0800c100304203150310801366540c101e01c0341205500e5420460b40641049004040740040758400306140f42c442203250480c801c00c030100f20001c0842150b0795401070701c03400d000c04003942100d0403250030066100300c0d0748811440d00c4100241c82c10801c241c2d803240e5060307000f088039100084030441203406620b40f660f0f1441e0084021280310062642e5039021440e1801588006000e1503522000075107828404d00c507001016a0042402b45101e4071340350007400070070070785c1a1203046200c1c2c42000b14540c1080c1c4110001c805c1900700541c02e020705024103c1c0d420307141a080e14200002030100180d541c04600645c0c0c040d80c8a8506031740c5d580c610b07100041c21240329001c8518141d201184a0001c10000310f000710402d8030601d0110501480607030400824840c40c0e01a5001d100d18030f026414045 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 756935782 1250 756934532 756934573
    0x2a0d0c03021803060f1614210708090c0906011b0c150f0903120c0803090d020d0309020f010c03030e030f03090f03210406090c061e02010204060c11030708 68
    0x103000520035003424800310901d582c40c08200d030071801c008620070101b480e43e0070468503104284203501c1c0000100315800f849105541003880300c0755081e4440c0c0c900c05203030419503101c941c1c0206079203041510fa2900101440d074601060400d01e00607a03010012a23401d901c07681d0840c449001050303803d950b0042c07a1400002145041c072898040919003544072601074031a180c072031014152503540c0c0c1102e44c1151074021802120f0742c00314050000c00c25401000880c1c04010b035104502c1c00340a05042c03102c13130001908054070b40788030718209031030701d1407100c0142e0b20022045030042080c80c042460425501d41030f8024a03d64040141a22012400381406890f9800442c403038407844040e1f95101c4801c3e0b0180780d0300e009140021f0b030903102403040e421018010302c0d210303540580240800302e5802c007a41c540401d02d8106401410008581c0a0661010221181404581042d41c0300862070a4648030340184003031107a120052155141c0c1d042d10f08103075810031411015005a50a03507a489542e00c190302100d1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 756937032 1250 756935782 756935797
    0x31005150a030f0b0f12010216030512010f030210050a0908010216050c040b030d0c0f02041a030c01090609060c0204021902061909050a02010837060e2a0d0c0302 71
    0x64100344802c3e0b11a00c6074018001100c1c000740294140c56444010001c110705074048118040d982448905030540c2404d868443c0d090003612000d03561030320346400000450341600081c1211600040070001a200d02004504000c4e0a1403e5500d8082c007201c00c072103c842e82d6020000760b40c00031070104a000c59608241103a588030340c0440320741d080100240829101072001166060f006018000c143d40d0080b06941907280c46075552221081c3d880d400101158104142d20f6085440d040340b80204c0e0a0810813410048401d0030034021440c50400020440055405032904100781d40104104545464040d0f45c900f940108402441802610000359209000c441c050b503001907262a0014204044c031070380c0501d940100c054030b040982a0015290440098030341c2540030fa000d001c41d500446500f00180072400e0380d03403006554103c190300400c141d0304240c00c0b445100340f0500c1884520141c0b00c0303140c959904440860201700900002c2c51145010784451450168101816001d0351545a801410702 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 756938282 1250 756937032 756937037
    0x312070501090f05300f090105071407050a2102040c052703010c0f05120402120109060b010305061e0f030f06070504051c1a060f0d0302030c07170a08031005150a 71
    0x1480d001030031520f2005009400e181c5c48204090103615170f54500411182906060103490100326076107100200d442015040500e4003d0301c018010380c5400c0c0851b100030041405000c480c421040b00c180c07000900558001d00c07541d030300c114151a41c0d02170b034181d9941004c80c1d0640c11aa0b101e07003403840f55252051030510702c030394078000710091110b0140004111041c010380d1a00e06101c000a240080808060800c3ea0b00000c40110340300402c009018403040d00e0b100304d60100340c840d2800005415210040d040510607000c044d0b104840445841d143c10041000312001c5420500e4400420306180c40700c4020b04c218080c584c104080150040b0041c01210410b9841c0078030030880c6909480001808d031700041c0700654419a5200d11103294508030340000c0000d00400b0442d101400042c501c40810070203e000d030b000400e0480510300244510801000320510108200c00104080c586500d25014028500540400402c10200c6035807001c1010b4000075108410030003054008018a41101001400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 756939532 1250 756938282 756938323
    0xb1206040b060c252d12140d030e0c1c0503070c060f020a08030f090c03160f0510140d0912092303030409200d05061c020312070501090f05 61
    0x1d84a2076030540d086405c584c4030f8041980d1030818400d000d0b07086160741c4d11012464003021035070303400d90307491303000c01a04c01c400b406c490355101100e00d410070032070b0b210220500d072600e011070a2258000c0b80e07104c640881140d00404c5125615540514a00c003114050045c0c440841c0700810030030103140e0314064075403a0b19094004400d400d0103d075200d602c00c4004140342024008200060b10342c000c1c840e001000001524001035034030700400c0c509084401984049a41c1250070090703a14449210006810161845885da9824800291150a504042c2c11642030700003400200c2e05155170107100f1f810742c4041021028003003040c0082010449000f1003034a10840072448030741c0d44404a61840714480500510708051070030305c0440c028613003c05140d8465003041d40114125000d1001080e0621080000041da030030301070b040c010440d190469010085108288060150343c0000705465103409071305034543d54160b24941180074004007000106806080307001c1004005d0b0210b00d24004c891040c21261 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 756940782 1250 756939532 756939583
    0x10b090c0a051801170703022508030402150409060303050d11120714070b0a15120c090f140405152809050c0306010f0603050a060b1206040b060c 64
    0x1052803050045800100b8002c10403e00348904080c0d8942d0b1082050600c115615550702c0020342410302151604000b942c000f40d4861f1070f811015a803800c1044d5040700c050903442c145c1d02c818913440301820281c40765485202040c0c1050740d88080b036010340303e007050900202e0795a00c1c02814070340051148109240c2414202101f91087c00c003695814420f0b40d50b02c1607562140803068607003440d192421b440b844410455a40426010b40040b03008080c100380c00500840107500c000081c001682140320900701c490017103800720b091945108161044490300041140345004844010321442c140803014220751010802030103800300b0f030003100300381c49258229150381e112186550798180617104884505000520070207988a07034049940a4840c07012038402107020000285482001d034440e00c0e00903403102091206540c5406042d801c2841640d05204c0241032113018020390062240d28001c2aa90800090080d45c5941103560325640241c0342c1c41e0745446a0320546d0322158207040d10f81d03480e11401d0700308 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 756942032 1250 756940782 756940801
    0x50106020c010c02030d030c110313050f01050f03180304121a062b060b0d120215070507080a03060b131703030610050705160b07050c0a03030509060a091205010b09 72
    0x1022104d900401601c10090640c030250020304161144c1401c1181503c00c6580060082005042c065411600070500300c5ca0402000b044070a0440c2090410600f4014050070305220300640350030100700d0074280d84881c0400d005c40d165005607800000400c40d0b041c80705050091800500b60503042d50301300301c503844d40c441003030148c10744003560f24402100100b6082c02e5030380012a40c000d42e1a2088002003585d440103400100407660016094034909468600d0101903a010000c07030100c0c240540da801598540104081c040340a0a68003903c0340c1800100b6840c1513100e5401300c0083c00c41d40e4421a110704035920300f1510317404540640c12a0340100c030440d810090000096038401c0d10300a08200345088032043c01c6800e41c0140d8011105480340c0150f0342c2c07080c1f445141c180d02400e0500d84203034485150381003032131600d0081c59804e806100c070641d09201083d440821500d8244050700d00b56550720407060304440c200c58982c40310700c0c50b0203c0b0088604126064010701c880d20030440712082c940c1c9034010b20 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 756943282 1250 756942032 756942047
    0x1080c1c0e010e010b0f101701060e090a0c0207050d02060c011e0644070b07150b0f1012050c040e1e06040c050d0c08010906060906020a1b03080d050106020c01 70
    0x11035500204801c607111036464215580707040c01c0701c075141020041c04900e03c040b144041c01c0c0c00041c040f03400c06007181c2f02c3e03041ca000d064ce44045a481c3c02e03c0b108000d0340000e511421180945805900c04410f15010354440000b1242806c1185008020699041d11742c0110000d14426410702d00c0c4c2001000918409074454103280042120410042404002c2c444101c00340101d080c1d52882182e0200310040700e1060001c40000d00c85070381115590841031400e01c144001c41e90740b00b8841454004031422030b858018441d0640b20044c0c403c0b02100800c820103449695030700c08014400c50038402040340ba000000c01400468500040c015140c1e122401e80303d286083c1e04444004141046001501519198100050320902030809038a0b0a00c03050100c82034072039080780400071403000c10042010702464490743d40100700a00d041c240070744c00c01d800251101e4284401030700411a43c0c505155088000b02c19400441d80005410b03038a41407441a4806010244100405402044040102540100f00d03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 756944532 1250 756943282 756943301
    0x10807030b190b130f06120b0604091103010903090e0a0204052d090c180a05030c0603060a0807080d0809060c0a030510051e0f1e01080c1c0e010e01 65
    0x10010355903590142c10390041d880d012848400035440e00c034443d80300d49407080d007900208003000d00030a801d524111004180c07440e0354040b00d09112001c6030f03100820307085010a50400c0d01220041500301d200d0400d0008100915522581540b07004595400c164200d0b081408488200b590f5484c0c43e40c0d509400400c030300592081c160040100c402241d400b604d84d1b540c010840302d0041a40c400700b1014030202da100c0b001202d828814403c005202c0000709500301c0d0414060b8002c9a4a0110368144001301c1d455011080780140582000700c040b600070b6580d100080041e00c00e003400c8800d09991582455510034081c20f040011a42ca2008a601d80c000800c0140c81007005401c0949002e4048408400418004000d03540900c507204000c51281d6a181003140400c01088501c11003c1c00702c0100b00c0701107034018401d4410030041a440203c12200c00005036407000900f00320415941e40c8808440d0b07846400700a03d040400c030038140c09210388942c03085611524203002000100f407a00c0305a400c85500d03c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 756945782 1250 756944532 756944543
    0x60c0d0b0d050a12170a0e0f060603030a030f0f020a0f0906080f0c0f1605010b0112020702090a090812130c05032e06090f1b0c150f0b0315040b01080703 67
    0x301c00c8404200141660001040c0614040f0102c50641d0100c41070300d807041d5800300400e600d5400f44030041038204023400403c12020081d00060400800180e0b407440303000f280c0c0040c140c4a41c918002e890580d4884907014011007425952120310460041c0a151018800004680e840c84080740e814452081d007031040340852601041502c0f505005402500040614a000c1c8810080342000c2992411180082032091001041c038194000002d030101c00302680702040d66105100d024050382c2c4241000d41c01c21410040010300380790368144984640300d1340c83c0e40804005000180703c2110600540010100d0290800c1003a10b5142c00406031104032450700c4050098250300c1442c01280300413108010743c1403804001505564801c1034109480b14090740e6202a5500c032040c481044004448010690300c5142c8124154060396420002100c68060f807103801d55030b101d40400c000030503840f00040c81c0700141211414807640c1030b480c005010848044454540707040002a10740d100003000019241d221 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 756947032 1250 756945782 756945793
    0xf04050a0605042109060f020c0a0506160c060810050105160b22080c1006080d03051306060e04050d030b031519150f082a0a08060c0d0b0d05 62
    0xa844a5000d04005041a156401d9050780c2540b0f540007904e42c0460b140440e101e0403640c501e00b11002c0d0030480c1c1c0403800402d54001c50b14030200d69a6400c0d415082d40c60448400b07032980c502c202e10f030f030b80e10b680754100900d1a032030190045103076a04804500d00c00e8458031080010551180011605800360910019014a501c0f040f40d00280580011580c402e0704685404c03074610340440101c600c0c01148200303851512000601d8203080d0f00c10301410b441901d211f101405014546000c040e521740c0b454601c441010364400102d84c4c403542c05804d0808103500148140708445c0c4a040c4482902800e0340c04543c035124404174802c00c68002c0c016130000c5a0014050701e24850703201d00c01a28031800030103030400e084039256400b0f2500311512030b180400403240408400301c1c2c20034840a90103205500f2002e03c0d5842815590f000b88500c13881010442c26481101c4810b072410400710740348008680004030f25001e041c04100900704000041c00a940714150b040c40801244c2c001c0c85903415000c600a400364108 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 756948282 1250 756947032 756947053
    0x80118020a05010c0632063304080319020c0a0317090a05030d020105070f08060306042d060b10170105060c0a081810110c0f03010b090f01030b0f0405 66
    0x181c3c00b28281ca9001d0000414480c01d800010980002d403102d840303040c1b014140716040044180040c0c00d43c0604186c1c5c0304940c0d1418015021980e600003600c511010168080c0380c401c10207c1810350b0002c0066070212510303040c4c0410780b007100034966920a00184955006850940b0b0324980d20021240c20411680408100191035040c941c8000b41c0c1580280104c400024141c070700b0050790040c0c84007903000040b24107106400411005a02101c00c0802c000c0905008243d600070a085d500294480d0017a100d0031500c100341d04c50342c94043d40344001960748400f25024051560010200030034201c0d451042001c1e83c00c0140d810a000d62221944040007100520090401000074554041030000311000c40302c1c907550b0358480d03512000d00c041e90007580d441c031080030303083c80c2003260b00724000c0d810283d030702c400a000700660750329120900070310139401c04129203041d4a081d0b02000300b03041c0250000149180c100300c58042941c080c4000c46051102030002a411103250300082d01540e0700c540500010300c1c9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 756949532 1250 756948282 756948287
    0x91503150b101d060f18030f1c1421010f0807050f042007050615031504020118030b10090902060a18150e010e041803140409060609080118020a0501 65
    0x40380c03a05107802d07183d10124624181c2d01d641c0541300440140c0f01a941c3c0d156410362844000d034078250710343d01070360002c441d400039100c012480d4801c0c06d480c842c42180c03c035016001106c40095000c00120100b2001075903021020340c4115003010800b00c505010503990740c42030f500012407454825064941c004840901c44c0d480d1407020100c3c00362000b000450301600c03050a159aa00c1c510301c98075140280000e450b0100300381440942d43c400c1452091003034041c04500400d1b00c031440f406030885140281c1c40094110b80c0100c203e040a210040c203c60145916890440081380c401c0d580d9184800f000100004c3d5401c40e4010030840c00d6000c1c0c1154201402c0910645807a88209201008000190b00104100e0369888002c2c4084c803450f9500700301800c00d1000940100e81400d0a540514100101d2081d81c89050300c130200400e6051502608100044004032082d01030b641000c420389052590014006500605100641e1040750007001030a0041c9035509400c1c0c1403140085d00304200ca4420407030b0b90b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 756950782 1250 756949532 756949547
    0x41d062707031b09020318011b0c0f05011d03091e060a12060312050d0c030506030316111f1e080a0509010212010e01090b030303010b0f090109091503150b10 69
    0x582c11030f21041d015101c8100350140d8100f00c55565681e9141f2030340c0344c040308090040c1c40110085805104142c550407900411011803050043c1500d1804000001004400d40c041c100c0c0030380c0210348a0120f10f5290105803a5440101c2c2580701e69001341c2c8214002d2103410805d840b120b001803055250512440d4140c41c410f00e1400c600c049039984400000100b6818230300c603401038a00341e440d103a0b50301c0000d480101300e5103a0001102054a0b001c10049151000412991000c0170a9800c214003003285c5410a60034500c100321903000300f03c621340f071402204409026524103141d902c6824960f40010071000c1d00ea092030f590180060001c00100312405983c1c1e10240e0042c1c0480c00252803d40c24126100c04103e007070b845803214111140c01000b080203a4413a9041580040f00174510719450003085260703a01030404c1083d1414800950305410383c0c02501000020144186c0520050081e0481001122224401a0b8403002c0f6000c000c000000e44e072241500242d001082c5501020203100225860f8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 756952032 1250 756950782 756950813
    0x6141009080f0601031703061e130f02030108010501050904120e060d020a08090c0d03020703120c0b0a091a01080d14270301110f0711041d06270703 65
    0x101200304003042a040034000080c0001100000b08029451031414040c03804a003000507030520010310601500d6511444032010350210001444c1c05000d80302c1c0001c5240403902c0d02c3d440c92a252074200c20307110001d03801031412102240001c0003d682c1c0d410521003034000840d0020a44001060384d0b60105000303507001500d4200280159040c1f07590309000508a038002c1d50034401041c01c5108018103204e0800c1841c50f8400c1c142c80303004030200c1541e006955030400f808020070050407002e5000b50948144400105c441d082103101180382030060004009110700350007606d8189114041c15015440c2000481c122110a070061499241c420f44c00ca41224000c02d003501c40101c2080100d002c202104501f0258800321640c3c0390720340d040d4804042c2150680d170300050442c8424807510810550080c2034840380c54000c0c000704443c200040021380281801a40f8010103170034800300000c04540014000c1c400d658004901c1011002107038583e4560807002944c11080d8400c2c003080c00011245da03e0403015 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 756953282 1250 756952032 756952037
    0x61a0304120314270309030706110a0206040b0d050a110909151f09050306010e0c0f071502040531090f0507150206071103040317090a030606050a09061410 68
    0x483d1650300d021400f00b0800e885004202c106110b514100040c00400c0d07401c04800701008500d04203007000440d460700c010b0301c01c400a006800d0004002040244807244031154001c0c2034581d129110045e00303030300e604081c0300801450301d004000742c500f000c40d1240b1401300240400440c10719181c5810002100c070300a1440c0421503654070f100b840383c5c5179041c0035401d200c41d03800703080d41c040340c0000000d0a8441c03da00c05840b1307078080310040201c19060704a0680000320008080d90301c94030000c00c944144200c2c0001028110107401d0801090b180354060026540220b03110300100400301c1c002c1e900540b2041199103040a014010300c11034009a001289c0d071031161424001b07020341070700c4550a060090380a200741c08040750150b20511740c1806200d9102c4060305066007600d407520300c41c960302d018600009008018070000160309003102c0041d01c900140090191240315240d00e4a070303003e00054451180a05102c0720082034002c3e49004420660f05042c01e00d20318411240204000500021064410b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 756954532 1250 756953282 756953291
    0x1909051e3906210906010513140f101a191112030a0609060b0901020105070c030c02010e040921030b0301090302060a090f02130e100b060a0c0813140301061a03041203 73
    0x200803035001c60303944a0030706034000d00415850700c404c0c000218604182e00a1180ca042c0034130301ca2070270107051540c220281a02d01403a543c2c07444c4411010403007540083c05018410304607410f15000010043c1101c4a414070300c1c2c001d220420b03106a800c2c002c009a800315541024a0401454240f1005540e0049030040c0110307917555901459811a6034a0300300440c41180054807007040e50302401015084103807031a0a5011054903200100880c1284000904000c010f00b00511280d84540020448982080d545070803444410012741c6468854043c0c0c8000c64100421781e000c40c541071040f003203d107070180c01a0503a0759a020051008000c2c00c2003c8a8031000385800b0360168980c002c030300c6000480142c000401d02c0181c039099160407000402410301d141011101001e5464031025992021300501300b282040103545010000b43c014280c0f400703202161614002038405003a007041003400400c0e802000126140d03040e43c1065540b1116004a00c1c504002041c0040c012900c40100007070741c0d14002a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 756955782 1250 756954532 756954577
    0x714030f0d0615080615090f060406020f0717070e0417040e0114061306210e240106020304051903051006030b0f1909051e3906 56
    0xc15402004001c10300640d40c060030300000c0b03151400d440003440942040c040d031380b52180c00500c0020521980c540c586001158000d81034803206040d00c03100f103000300b26940b00c40d10703010001e50754640c0d200980c86a04c00c42500051240c84655050000d41102000d000520f040500c08400044082c104940d0020010381c8001608008800b07800079041e44000b00d2441e524040340c00d100780340d4001d00f0790300c0b810040040c4660500040304210480f040f5007845407102e80d005100b4010780380321403007a8401a081c8901d0700f00403180403d2501d2404286401400c2d0303401c0e0b0a691040c00b8500340111405640204024050b81c0303420101804c2d007903420703100c112000761603a0356141060480d000080c4c009440700070070310070010060159603200065400c3c441441c034000c03403100d1100642d2030f52280030390355807162030040c46424494407283c40c0d0074042410300e84022141565881e0038882e4001c0003000c10228401c103001d170403081141d41340c50800043c44103402c03031810080d00303070300040054802e0440042840c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 756957032 1250 756955782 756955807
    0xd080d020f131a03160302090301061404180b0c0714030c0607090501030b2b08160203011d07050918160608060f1c06090503070507030204140903071403 67
    0x9103540110341080e540c4560568074410800c2d851a044080c01c1c500d00d58882c00454810016030b503001000001c8056041801e403820f400034130803400419090b500b840f00c003050100301071a4900810b80d0030789040149403800b1109658000c01410001c04045d8590b020500750450100545400c4d07010b0741c0011000c1c0e01044a1601d0750388440071000064010b001000001500050b06070000c05003030038140600380c0400000303901036640c0c510039907040900b15240e900f0801e0011a00b0141c551100c400c503507500d480d0801c0405540100d0040344651709010000400e0f0483d0010300241c404482c00800000d420f1404200052200820300900c00d010a42d00a18820080114800d620981d002c0c820b03282e410284c006025100c000c00181c00b030502040c200401c0c0d12000500700001d00105a4040003020380e145c0303400904501c0c1c00107007542c4004a501028801c01244c103078101c0348221000c000004440c0c04015400c0e4003100e42c018035030070901c82400810425106109030100c900e0a407890010000c026 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 756958282 1250 756957032 756957037
    0x2b0e2d070902070629150c100e160602031818040305090112050c09180c0a0e0a05030a080c0712021c02012d030b030f070515093a020303090d080d02 65
    0x1e000204d2110f0310140c5c120b04100c100c443d1071288003080300e440d0030100d00d900303665041107018040e0103d83d81c50340c0102080c420310000c1c600755441d11030440300c0d59851100940d260095562410491308001d0031030b0452a0100340c001c94241042100c0f0040ea8443e241a40c00341c0054100c14180300d085540c080f2001b13a24840c0360f00c500740d800c45058443d00447d050100445060300003400c00d441850a1200705006801503c20b0300d4654504007070000100408a6024501da622603074152055054110030400c4400c040c0004e02200ca08580216946004070614080f038540040d4020552158240310200c00c40c0011801c0d078010b0409201625111860503e00c41708640c8106e80520b54032642113030198075001d14041c11408800600d84070600b030170304503120314942c0b00d000d10407940038621941c01488041503c00003080103000c100b818448490030300c0b03205540d0500d41c018000411002801544501c2e5004fd450b8001e40203500f000111014040074102c40c80007a6400070b0305101000124900303000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 756959532 1250 756958282 756958331
    0x408090d06141305070b0d060e010e1f06050d0e0c0a180b09060a17160909140d08040204020a0306080102070507030203010e122b0e2d0709020706 64
    0x6000000380180c01000340700034007a074141ca4991510f000100300b00003401c80555541107407855540924016400041160b0ba000000c0c0303000c4c01000090103425480900e00ca50f0000c1824203501030015840402d9400034052480070400600018107055010391092145590040c1287d0750780c0240000600c2152250344a40d40c00003452220400704030070380c0070f2016030840aa55800c0715090800008506400c40d0049070a4000c40150000e00210100011046210383d0989405c0082d140e0401001a060152068074841903492160050000001c0c03820074000c840d988a00c4030303854907400c02c4083d40c0002a01001c041d103601e0007241225080c402030600a104400400740326103184141401c2d00d03840180186150403103602c0d00b03500c0d4001c104a40500301021401a07845140240e080d203541141c2841aa00a250200108c406031000400c403d5208032503c919101c441c44001150400f05011000030083c2c02150041060f007099030060b2118510800c408500c4084607822109044000c82 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 756960782 1250 756959532 756959543
    0xd020306091b04091a040c030c03030503040302071401050313150f060e07050c031804091e03080105031902010809031e21040206120601020c0405010602030c0708010c08040b0408090d 80
    0x40c41064410002450036140307060a803001e1103000483c1d00c07a090005c4a001c40d048080c45d040000508102e1030500441c095a4004900b807010303901e9040c01469500219411005840f032031a000c82d00f800c002070700000f9020143d40d950721390340e01e1280b982c18a01c0004400c4502d0032071004100c0b4040864020040000c2e1800c000180746c40c9040c5111109c840090072500500c41d00700b00d242c2480d00c000c811114200044000c181241c980c410114004040607134000d000c82144541c442050381c0801503041d25035009a6464045076200c40c100f54903130030011741c050f0481c56100302d8040154020101d03290321288900a0341d00300280e04c00112051800c0740780e4113401840008901d403c032b0152828030001e0307001c148081015848c00b94081581e40c0304021790100e40840c91030000c0d00581c4200543d0a641c50050020302036546c1d69031020f540c03504124070000c1c0c54001c034140481c1c038400502c11117038203046641d00d1000d1902c0d252141174403904041c20a842e604000c0141c6540794803514000b0038105d2081 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 756962032 1250 756960782 756960793
    0xc050f010b031002041d09030909151f200304081605010801121e05031608090f1f03150306090b010501030606030516080901181109090d1d0d02030609 66
    0xd010107060640f900140d050061040c8024010030074503046c40d4094030920004010326071240040f8030710b10700504020560000e180e4080210310f0402d11544000074900380d4100d0520760340c000c6890b05240c03003850742030005150200c281504c0c1d0000101c40f15510400f20980349001d0700d40d0001805e052400102000381035015a080009580c00403d0328014059280752201d02c0c5e40c0da80d501c003140d089031211405540c42070150030040c000f003030003100c043c00c8502000c1e0202c50307401c0c82c1a0b0010740081c81c3c03003032240c0b1800501041070306192440551442803d2085c44d010010f0003801c1c0c0003088031940c08040706a0603100800016114400c81070b5881c085c3d515410950b140a00040c180c89a40d08010209800c010610201d00321911940c6500c2c14141050042070741c50101d0613006000b101c14043d0103102c200030400511940707105414044030207640318043d07540c0c1c1e00304403683c82d2058401200054100d240400c1484150b52003a8030402004010804400b240d400007468002e0568001c0f0158220 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 756963282 1250 756962032 756962051
    0x129040e0f0729040b090a0b07030e030c06120a050907080a0b160903020f0f010e06160501060b0a020d0305040f02220510151b0f030801080105060103090c0b0a0c050f01 74
    0x3810072a01100c00407102e0507850800c0900160341c00350b40b165188191010406e0326a41c0e490b41c04d680007620780b0062940d2900c401c0d05008001d417400c50001d034060700500c0103802c1141000340031038081c520f0010204501ea203800c0006001801c0040041d4882e0055071400300e8052401e0004043c0e55010300801d107041e082c410400300351075010800c1c08091003000d9030100016111900c1241100c1d0048400b44000250344005891126080080e6648804000b480c250b4601498091508403400f0340000c1003411f469028101043c131800c0d000703101582c0420f0028170024802c1d04160383c000d01c50080160011025800b2480e402400014203080248c9100740d640142190710131315a00c8103040c110070f41d044d0700d082001c90703a036500380902c04200300700601c10400401249a40300c1c0c0315a4405880050101503050040045030280100111942418017040d525032090051006064014440324242d0b86001c1c00f0045a034080d80c20320040c0b020b403103000c00100b81d007407085212012241c400820103010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 756964532 1250 756963282 756963299
    0xf0b070506010504050106082a040602010c140909060d050102160803010504050708010e07030f180521070b070e1201141501090b03070c0314160c080129040e0f07 71
    0x5050704030f180103500d040010000ca030b600803142ca41095032606500e02185c8035000000f0300030315400414002c42000500080c9035603056001c9007a0200d240d0f2182550a03820307800c0141413003074000b507030b6002c25a0000b00b40c1a140030058180c8440c41a00010300d070085e00402000454809842640d0011b40070004100c2c90500c0e004155001a41d850302410741d604045a1004141e00903084000f015900c400340c081ca4501540201d024106041c00300080301d14600d0b02903607401c00500b011488140303171840000079180c01426550b031540d01111154559031010307000c544141080c05800d0b4401810000010045028403420800c0c02d0004200380a5144c1408050203d14030004428104003140c03004220654001c2c09490b0403040300c1c54100e06042460a080303ca4440800b059841e04000040c440101107140c980504e026200b41e45035420f0700d0f83ca0890318209d4201891401d026400c0150400004600102c0c0c1402c40200510001d09040c1803034802d460482c0060b61260303254082c6500303106510 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 756965782 1250 756964532 756964543
    0x2205190b0a09120f090512060a0e060c070f080909150a05030a030903121809060609170d0807090801151a0c0d120603060f0203180607090e100f0b0705 66
    0xd000d0380520181640e95986203c082000c03e0040c100000703400c02d11351417441004c01e40c0007400300400700310300e94030081819500c40200340e0b01e00b00f10524200b500c290300c1c40049801c2e449001c044030b000b0b007010403d480300c4c00007101d407110454040d0404c0015088070761311501868016001e1203a0b010545001ca8203110030352005802c411304c25880507800000103540024032605880d070020486c40c40a0000806864540c01d0b00ca00400c6a6a01e02001c12581000d60101084440070780d6400340c1c280d500c0444600403034145102c0d82051308444a400400750040000b260040038625140050342d0780c880700ca60849000905a82c4105c000c4407041010720002110900c0d048110786401c0e00d891504900c1070b40e15102141c03030070244000e46840f0348101c2d1455100800954100e07500b480070303240200060000354401c541d6540100441180008240302c0020080e11138031540d01c4100d00281071180900503c0381c02000d0040b114074110020540500206203003000300462a050750310b03520a41342450608 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 756967032 1250 756965782 756965791
    0x2010f0807170403120b2b05010b0402071412091e030c061b100e030418090605180610080706030b04021e070b0c0304021809030930060f2205190b 64
    0x144847c91800705205010422008483c180d6031320070308100290320744180900180d81c3e51581c090b20102c0c3c0a002c0c0942c08903800920181e10b401c0c1c442511102500c0c24480c00741c15038980e00104000056282d82000c001c2c240386005009049840d0580c49000107215a44015207401203100c00c01c14114010404202c440086207401e803003070120442d011144e9503a40200d20900b900d89440c1c102c0c001c1801e41c954001008181c04c254180a186403060a5580d41c240c429120b900512694000514042c0c007400150305444890000e45004c62400c00120081c081d119070059000f6401c001c80c040c00c09400011440595504c0e003681e0b210400c40c05d141032060030033008240d005404104200060b60303000f5a0b9540040c03030715003020050703e45440c803900e54000e100d80c00340c0281142112040f101c20740b000c1041c040318022007591100103401812178444106136006448061410f01040002c1c2e94081464252080311041c03e084810070f031541403515140103117561a12803820005814440100d00042c1e01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 756968282 1250 756967032 756967039
    0x50a0f020307051917040305010b0a080610050424080d0f090821071407080c0f01080606070302030f0f04052b0f02061b250302010f0807170403120b 65
    0x500209480302c0d6191807103407074400c80c0e00102d43e48440c101700f40400d0000c035654021401ca51542d07241c0c585107000703040ca041038510800045078002440300000036950301c0760041681c0440ca091030002844080e02030a400b5a10306180840220f001001501081c030052880c000148405040c0b0040900141c2007820f40340100407040b20140b1100d20001544c100d0000c040e03168072154003040da24000c25004405e00144115036803921088440d500203120010b5505203400d0390800f0000030b0030460f0012405420501150b0240b002849a1800d01c0182100718000d0050301d140181d181404820b40e440b0081c2e2401200002c00e00340b01504003c101c000500b019081d280495000344200421114400c0000409111004c02c0c40c004540f1428181c8540b9542c20b00d07030001424202010039100c1c0e81d41c41848200300c65000050312145217440c41c2034200e0341c041c3c454034041c1c0c9a003072040342e61910040ca0001030000e41e282d5030550101e07017030f86203101e14001c2c1d0b100802e941c1501140c07019200843c0d42c0510 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 756969532 1250 756968282 756968287
    0x309040b091b0d02040b040905040b012921040308090f0111040e040f080415030b0f01140307020f06010605120a110405010e03010f06030803060a0608040503250c06050a0f0203 77
    0xc0d650003000c4260380a4542c40d141603181c164142d001d8010348a5a00126607828010600240e0021540c0005016034400d080e003502e83d0b80c98600f680740704c58100a194006a00e4a80200300d5031ba5401c004191031048003600307403440040d010240701000d50546084000070401d2080040c48201449640d10120200c0c1c0240315088110300450100d000b64040d40503010280004242042000c1880040140d40400b656480702c1e0b94000030025071000017101d401090078000b400141d803504031401c100406050b100ca00c0c81e621680d11590b500c1c0c000402c18001d501c28815182d001185c2000303aa4004c001c2640d405984108010b00060140f070040c0100140e541072200300511180d071341060301d054a60038030b8010f1180c3c8a503000280074108440e801c2c1062031501d580841480700d40401144a900d0955002c90140e0f69140c00702c0d0500800c03070300036000741c0051003401c0154121418102144051002512404c905501c504566802e1030b401580820703400103c1842150300050980c10403981d5001860 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 756970782 1250 756969532 756969541
    0xc03090c1e0602063c09030306121501030f020111060405010c0f17220c080c0a0e07050304080306040e010c120501090b0114131a12061c0f1509050309040b09 69
    0x1424905600e056501000c203040140e90485c451000700c50359411102c0e002c15400c00d510b500762030354800d884850040c1c0b4250881e080d81e41e80010f4100000c0ea07501d43c0c03103001d42c4c41c580720400441800c000803410860790403210341203418204003050056000350000180b46000700005400300c1e07015148001400100c00c900c28002d058441000d51000011380d1041c140f2050107800740502641c01c100404800d2101004242054001400c01d0015002c0d100c01064540752200c484200780b040f100103000942c1000010000350b03058000e5a08160050004140040214519400e594405202c180001c0b801e4400c0b4100641d540102401002c0c1c0c2c880c00c018507100000000c00074100b6040040302d10303100180d40c8801d08540c51504c402000b1803000510710740311a510449855110000800030101c003100414007a1a011402e500031010190241c007030006d4640d268200e9103841034083c0c0e6044c54846042819218038002d54040074410301c040d40c0e449500c0c1c000c20080320b50704020203024040640402 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 756972032 1250 756970782 756970801
    0x30a08070317250c030516030215010e1b0a0311040e041b050114031504050c030403030606090608060d060f0c0504030c0920031032010f020d030c03090c1e060206 71
    0x80c03e482c0303010b2800c601e040c001030906880d43d10900e441100c402d25409220010305501007188441c1040051041281c0d0b40d0b034101c41066600140e81c542d1a581c5008450b03c400a9070600916104081341004250701c640c481460040380c00c140c2c8a000c80c8031000c1e0170403003040451200e07040c102c03482e070710804800b906040000780790034003d5104a45901000012034902108980f66490079a0018420700203864002900e95594200b5201140403904008000c1102405584c42c0c200ba46c0e01c940c1d6a04155032544200302d0300e070a40303120039284241e8401894080150600502540c0344494560542d100d166140c50100641168415040e0078a000d0b410340280d100c1c040608499150010002e0b10ba0301d6000c011030240500b0fa2080b500000c00400190604940121419071000f06049218114808000540c0c0a10781d5049000060300701a1051250fa406503004041c100d070b251400040800d0299503501c01c5949a4108602101c120b601811031400c502a001001c0c08041c1302502160900d071202 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 756973282 1250 756972032 756972091
    0x1b0c08010603030806091614090d080408030c0f1b1c15020901020d0c1a060307170a0218130602030a060e1f08070b040302040518010507091511030d0b030a08070317 72
    0x8401c64460006102000c1d0740d40d8ac0545e080254200c01e540d80d03203a68520911303a40f079000c1041d0360a80d01421400024085000c9811840b008280b1346079940032038140c041000380404a8541c0c00048400c44040000c549010314054450254007001a42d07061407030006032404028108c0c883c20044003c008a00203a522021148441090003034000241c135290002800c0a0094001510100c0c21105c00312152a00207110403d239070003900c0703820000c0201005c1a00d020401c46040441110341c240d44c100103103e80e07008540c008680600024007540300e0104128241c02903c804c280101d00d0303d01e9a01d68865140403000601c0c260f03000340a0319107000d6459207180958030011344039503692000100c0d41542100c64080c80f0281c0300003005140b800c00409040b400f014041e00381c5450300080d0b18044d80e030091094244c2880c0c0c02c1d005500f0490300040032009001494611070b05800303180346000002d074111002d80b0b1528866110001d42d00c0c4800141002244000c004181000300821b41c0400344400c0d828 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 756974532 1250 756973282 756973307
    0x30c0f080304090c0e060d0c03110a05030412020f010c1e30021e0d0c050c10150b0301031a07020c0d06090201020a0803010b120108030a1b0c080106030308060916 71
    0x280401d054013044000e80d10912980440b5030030400000d000e455048aa074001c08540e401510100b10503104c2201540140c01261070380408110300304041404200c036050719140e43c05940c41241c0d03040038440c0c605400d4546080d4020042810b00311018914907540440007011000342c504054810030740141c1460610010480114101041032410307a0880240c04546c51140307804d8082501d540c40810307107912075011070014500341d450402002d80f07a62060080b9900c03100300800a20101885581c0c070001040c420300302c010100f0100740c00113001d41e00c0c4030241d0b00841c019008080c040300d0351111490304640003401542150401304600c1c2e0340e0b0781c4150f40c40329900d810032800511070034184010f07890301c518207d0160009401100024880c00050f000306610b1030700c90020000d40c0d80e200c4029650b070140d42e07504004690032882c0f0150030342801040c505500e0090500611482d6641949401c50340540c009500280c20802000042c3c00e0900200d50452403810500d10301d0006400000c10842c820700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 756975782 1250 756974532 756974549
    0xb03040602120f011401030605030615061209010b09010806090715180803090a080705060708250507090e06100b0a0e030f0607090f08280b09010501030c0f080304 71
    0x40410140012039041e20080c41481d5801100c40c240f0410100c654002407080010104e0034294214465210740200811580c010b00245000d4441112400c0719000f10000310303070070030030621000c000c104448803160301508804000103501c0e8142c20078061101c0d01600310b880180c0c0140c080c0541140c00013540340840d9080000f160f4039030b8a00a0441d0104800c070002c1e6400100f40c4804070b07203203c010000300300251084a40120540d40c41d80260384649852041750b602c41c006000b44004076180400400c1d0450561f00e402210043c405a12003c06070701c0801650254800c000c1440002414400d5040300c0d80140010406460185d46001f4080414000e0b43d841d01c502142c130342500381c001c0b41c00d80385c1c2e160003c041e101448054803206944003c112202c00000d511070000107244458410558291003124000c3d0445410007403088a4980c46403404010801c042c42e18400420310600030b140c0205c940000106855140d0f04005558040a4110400c18000c9100c10421044004103c0e001c8840c00e1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 756977032 1250 756975782 756975787
    0xe0307030f0f1106091c091809060209130f153f0609110109080307031b0606140f010219110f0a0602061807030b0f1f140918070b 57
    0x554203c2d003c42586901180714807401e814402800408105840041c941c1d4a50700c20f400d034040d108407000c501c1071140780c07818020f8070013482180d507080d000751140a01501c3c1c050b18218296010032040c8080f840c22060943d5100a1126411081e0040b03c60100210000028040c02d140c40740c0001c20041c2405144501d1503402143c000b00680206141c0d408201c4141d40b1084c3c1d68201140034100302d2108031040b14560310784900540c022042c0c9401d480030107000b1418050603036400d4400340c0c00040e04111802c506042040003403502d0003000040c0184003034140c4000500c5040c80078000c64840300f541550030420b01c0706070b4241039443c20b01c140d6400c1059282011002c0700804c140c403840010150700b140d02d04001260254001034498090000b0b0200355140e04001181151690f440b0f00005004a1800003c105011242e5080356042001400048181c41603520040341d0410954803040245101718190503151400d400303000da0104000030300d030060340301c0f9007581038035022180190561103802 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 756978282 1250 756977032 756977057
    0x606140c0703051b1201051302220c050a020624190503010f0c020601170d03020322110a05090615070516030303140c0c060105040b0418080703030e0307030f 69
    0x700180402150000c05445214060071620790b03c00c40680c44035405284421450030000e941480303000e1180e504010144500082d40d402c2100c1110005900c03c0c89015114190888100070f01c036030600b4286e2600c9245e603030740c80c3d2007004e424030000812140d8411a42e40080f1149004140c255030290300c201d030700c030041c8801524201d00e01405500a140c0541c40d040110441150a600807140802c0a03000c548203680e907040c40440c49000c0e01d605000581009040c0710b00f542c0070380c01641d001034030700598404107100509548541c102500082d1041003001b00c20104505020320240b01411050322080c0091402c140440d66450740c000c00075100c000c00080e00340601100307000015201114905000400b070b40d80c2401405400c0d112007a98030000c2e00d1011407081c0a100d011038100241c0d004c0a003005a20f08401c01000b4511201800d40181d2100c18200170580b4a01d0303c1480d040c070401c149500c6841e9070034020115501410120313041d82c01000601c000c03c1d080407024921145034504910021b50 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 756979532 1250 756978282 756978307
    0xb150c0106090f02040819050309060d140403020a1106070f020f0a0e0901050717160f12020a02030d0615140304020a05060f0d0c0203130b1608030906010305010c03060614 75
    0x10030340c0070a402a107032040403250480c0f0354006204540b480c0d402c84002d240c40b103114241c1c0d00400d4400410a50040109000c20b007818400b821890203107100011340500103044420303040b4400c444c00c1300140c1015080a0810412510385030b46141c0030346c1c449081c4019591001d2800c0444034000e03100e595041500c20031030342c1d9400c0b08009401200c5113159070f424a601428080c000a0b030340c02c400715000072007040b0b4946021090911480c5010f1004001000710300056422603c142c41e503008004521900f2501c0544a000800007441d080e4021030755010440b495030110782e055000070480b40740072100d00d448564803814000384049140011a960349a910000300109203d82c88550880d034041135800400c0c10b05800f03002590341c40d401c240000324401000304e0702c03403155510002e03c05d504400203000c3c8181d01c0010380350103040300d8804440c0103410303122268280c104540c0c1c00300c01c0d48080c1c01802040000e0013900000e0450303003006d014040c106103000d0b101c5100f191001014802c08505001201c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 756980782 1250 756979532 756979541
    0x7231606030905210a030606020d050d050702150c040303090f030f0803090f0d030212100e0a0b030c0d050703030f0c0317130b04080301060e090603030315030312010b070c090b150c01 80
    0x601001c0804034802e9039113400c15078015040724004240740c81e00004010313002190380001c03455995a40380c64581303150801c2d0001c04000d00204110b104020b40c5003246412800310342d02a004004009403101d10b103142c0104403460503000065603180c86407080001804810710300209a501c94030317942d04c80da504d44c1f41c0c0f441d0031448200d0220900c50391108403034580e00750b40100074034544040014256601c0d0150140f540c90a4071405007800300400024101071041e0384a07030140d443c000d0581c0c10349107080002620b05140d080d4151203541040004004164101d00c1c2d042c2c1d10811030800342d11140748d644003c0d01c0000b0906220408145000000d43c2c1c0c550001192000305a1044c0d404446042500384540d00e90000d0040701c01040144815000b240b0f4802c8586115590050085d8a9a0703510300b100340507180c0d0342c08420342601c002d12407c607a0304001c0d1101e6001e00160030001d070721002903080c0510381588603403010f0251072411610318025101c003444d22041c5800b40d8100340c0d503110525034135030041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 756982032 1250 756980782 756980803
    0x42703020a1a010e0708160f1b060203070e09070804030e0f060a02060108010608011104050f0103020412051c0e0d030c03050c10060314060606040614090607231606030905 75
    0x303071140c2000b4103211694070005040e203900014420a9a032080b2003601c02c000c1c00d4840120100318400c090060324412003010800718180d140c2150346404520114585100080b001c4500ea0f801004011002e035100c84040d54001049404000e5814800d201400c050b4010b031001e001c00c450140040d2541d21203c2c01c03410208005003440f80e642445800082d120310084c001e412095081c1800000e100c0c10500600400001c00c030030140c41e142c039220030030910f44960380c181410300d5028400001d84c000203440703006210b07025101070308144a0059082c1d40c003410103400b010030310201000c061025110f0bc0100c0420a07814140281100401c1c1025503480c000c076400c500e61071040144040d4883c5039a00488212403081708540c07215205001c0403a202c3d24102d82d410303007101050204100c3d2610905050481016001149280014410105140780d0000300300341d980d4944c20600416549424443c4c1c0e0075110b07518007412580e141e850ba6100300c2c4145100384410591260040c000b440424000612003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 756983282 1250 756982032 756982043
    0x70b092a180703021905040b040e090a0804231507060207020310020a0201091e0512071406010605090112061a0c100c0e030709050105010e041e0524042703020a 70
    0x79807078421001006944001c0ca175241c421841e803013140180d80150159402d9403480022541824200100c00c80080401004000341c0c1c070503c002040402c2c00d00d401080604811170b00e1030320401038111051618103072001294040c03603680b501d8201040c607100640d0101a07000c10050303929421800064940390120210701c000c14030000350211280d805500450b20140310b05440800e025074120030704a00d22128a0144c00703500103003038940c440c4c2c54030801000c07800d100e00c1d8001104c0c0c0c0403601e2180380c07880c241c00c103402089001414607450368001812003001c100c00301c014400c2c01d051804070702c030180005142130140f0b02c011465014462081c00400d82c2c03140c43d5281080011241c42c4001c00d0031341002001c6010b401601d81c013240e07400c079900031181682c5040e1102c2c00001c0e107150620004008001d0561000010003800c1180d00a45008190203408219540954441c1101e100c4075400880d21a8034880ca10706141040c1d14210281c40e10b5103602c00142501d0070080d2804d081c0d0074001101b100a08 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 756984532 1250 756983282 756983329
    0x1021201140a0501110a0f0c180204050112020c0c040f0b090c04060e0306071e030e19020102070f0302090414010b060f030709120302060a090c051203070b092a 70
    0x303116000c004450521002111141210b50343c80c00103581008100c142030324650041c2c0201c01c0400c52030840c0608007440b4030070700345119954800d022046200d055507030424175000a0100010b69100400703408400c00d45c1d03421440c0c014101400c907512000d050750039008540f1020707081c0c85c0c00c0c0f5650102c40310030f001a2a5106600d422041c880d090340c071034028900400d01102e842020340c100011258407400c1141c0300e024405c5001c0c4014100c0c4010811010b00301501d84e059400d003034074103008440010034070ba503114000c00114400682402c0080d04130303007100d0540c00020805640c4034500141c1103074110801c109a1613890829902414020390001c1d041740380041c3e080b01e06966000251300c1011030b60307103c042080c0c5886824020002e000c0010f001a030094022a0180d0030550018118034403a040b00721486036160089454001c0c0c0c1a03070b010030303908081f8403172040c05440d9880380d03442180c19014002a03080707012032404c01c43e0b04250509059040b540ba201c041c3e11882da000b17000c0d00320140c0c01d00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 756985782 1250 756984532 756984539
    0x81002030a06333f0504050303070c050c0a0806180d140c01061a040e0a0207020105030c090d0b091024060c050304081504150b0619031401060507030207080d12050901021201 76
    0x16650304038140584c10008981d42e14981413019201d25070040ea440009903103107031500c1f20f007100d40e01c49904080d10303e802a090038803010b580e010a8180240040d0018000b20f103440003040c92400311500360681c40d6005a0610b100c6154000c45802440345495030881d2107100000155005069540040c0450a000b100c2c182846030a80050812203800000543c0c155443c40e12940c168003420f83c000340802c1c01030022485404205001e4a4284030203405903054441c0d030785031101d607400151100390042e00704855070100ba1140303010b68804103c154450b0458150341c64040d408a00d86445020100b105a0300d000c001c02905004480041200b101102c44016034000203c140c0b00090758112010004a1001810009c8901403030b07540010041c2003600b008601c601b0b0304400e1514803080000c05985003000e500c0d505405061310b01800e900e0fa100d40c0c64030040e24010b481c0c100e0030740262384a507001c4503030080a07652106a803c202d002e00400030541b0b488005507a80640103000340014500701c2c0c0b40020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 756987032 1250 756985782 756985847
    0x41e080114160201150b07020f0d060203090d0c0c050906030313141f020709020c011e050603010b01090b0a050a12230a0b1c02010207081002030a0633 66
    0xd8000d20800c2d1020400c041d45603026801c030b0358440544060360104482c1000248030050285c00290300291225245440600c0002d50180741d104048034107075804028800c090404021804d6551034031b0a0407240c0495940b07501e420f0409602c640c80c483d007080c40c0001c80f682c9050003541c904022805071171080545484a041c0080038410200340201c420b401661280c100b1101f07824040c0429401402c600c40c1040c000304040c0d40901300d005219901c800101b4a1403074030640030918601a14800206410060b04241c00e440d0341d5885541001180f48041c402c1c0341e00001152251070075410b01584e01c80140d6401d0307074a02e034078911424106182c0101d2001c02001c1140d090007404c2c001000605030b0303941043c910201d0b41480c04c80c0341c001825022000315000a01c80b01b0fa002c170300500403944036130b603600f010030b1070801c65907c01c04600740c01106002c1c1c52045809070001814031040c0344400c040c2c000c0d1240c60502d2040712411400c001c3e035000803c425004070150030ba01c0040c10350421410000e003041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 756988282 1250 756987032 756987071
    0x4030c0203060606120a0506060c0312010f0e06010203030c0c010b222a0309050102040b04060c0c0501080f0f0402010309170408060c030408040b030405160315050702010c05041e0801 80
    0x203a00034014240001c0c640d140240072030350306500c0c00d1310700c0740789407a00b03119000281001003130503411031020406c00480480400103400c0a41c0300400c14807240d0f0418220302c0720308a007980311142d07143c0020148002c6170380100070740350701c48070303e11070075072500d015002d4240548410410b00d60005400841607074901980070a070a00343c54901c0d410700c030070f036842240300000001000c2014940845101d112098521a030000401c0c2030081c4005803e00e030303c1d480c001d00c113684154058004146841203900c100602550a240144400d081c503001a1030440741101a0301c0000f8242d007a00c0700b00000081c11a800381d4007042100c2d810100c0f07440c840e800301c0305000d0f441e80325024401451041100003148160880220b0348110b5010368050b040030b141403190052504041e108880b517003d040481e0600b080c1060b0440c00440c0514210720700d402982d403014045482c0a481d06c0c2c00c5905000a40800301e0f0400200c4e000c6901c168446040305410200840d40d150964102c1d22055081200c07101ca0200f04d00403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 756989532 1250 756988282 756988307
    0x40b071803080c0c030a020a12020121060f0b0307020303070503041a0c0912070b07020405091e03040306240522050c0c0105060102030301120b0c0c0a0605090c04090507030807020f090403 82
    0x40356a00c01800c2c4c1010380c0c0341e48407103009500c00c1003240b09008c6481d01c0b40c00d8104240c41030400340c0034403c420710aa0390390410b42500201c03c2c0d507500b200304401b18001e80260000d210f400d90180c07650404450080d1280f100400d20002c5c07140c00004641040441d070b000030092540c0e0f840c03130083c50401c07641040d1a68030540001d403007141c907200c2003a401c500c0401c515017102c2040c41c0c218601203032a4248001342000400601160148100045c8414081c400c400618480c1801a565450440c41c00208450300503440500e6090110714400300349000103180300550310f0444004040d00300d00c6030700b1003524607200401c00380d16050000340240501e0b41d5015140b42c564060080c0a01d5465200482e0351380401d00c1000c5080c0c5a010344000410020324400350002c2110107074524000c4090200c074038080740c558007200d605a580040040d04d400038404010400d40843d014843d03030107180c55544d075840c1c090002805040c000205e03070045550740c400c1d0045c0b103800a8810140c510b40750078080c082d10107881 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 756990782 1250 756989532 756989557
    0x19090314071b051c3002071802040b220915090609020a020d030b0a0e164a2107060804030c2a17070902070209040b07180308 55
    0x24003003514070b0140c003c212510a101c0c03046403038480c82c1c0c44000300c5a4292003002e10401001003255150310f800901c0c034085c1107080d001014420b15100c0c5c20980e03440c1000f600342a4500c10712041c406c0310300c074a0480d10894801e00685800074054a07c80b5080301c099031146a00501d4400c8400010528507401d00880d1200e44042100b203503619100826480385502410058221001d62203200b4040c3d03000e4804008003a16451441d52500c0410303685007016915a6000400590480e01c03940c2c0c403991481103241200083e41018540c40a66001801300c0c40919a1a22103a41e440c2c11034044150780c1c2d00e501c0030003007000c0615415182d00c10701007842940d5000c0d02d4011503a000c81c0a60184e64610700071545a950b2018001158031504807600c0c400c26090031290340d42d00605100d0300c404005502070580c54095113006a8103500041c50540554000d038280c90040c002103015a56140e0440d038000c1c3c000e04030301c15940e104c20045503001e50740050008071a040e00d1000c42400b2072100901450107001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 756992032 1250 756990782 756990833
    0x7091202150a020c240304140304030b07030b0910180f0209030313030c060c020603180a0b041b2103051c0207050610050d0f11010e1815091909031407 66
    0xa80e038040200c9100358500c88401d208101180004103c90042c50700e030b235008010380c0d05240e12a0f03190405500240c40b0080041d07120410318105c3d00d0041490f0740c0024004044007105407412980c28500c02d014000044a1a42c1d00d85401c1045a00c2e0100c0c1c500c010003d068a0b40c80404103009816842c072070000761400b40c000300c0f01042150154018080c215002000c40741503640e0340c5418041e20b07289030b004080ea40582e0021000086400c0b403550301a81c8a58940b2951411941045500840c0c50340702d00c6418410b0f60700078020300e10070341c0b5180d140342d014074100b5518003440302c03000d0390b800c80304501194091001648000740400417a07458041c680c000e02c0001019590410062904404070000e0041d40e4054510320019000310400001e20006040c400c02c80e4030f400300060050018144440781040c2c08804108425a045264800070380084555410f2420070701c200610341d1110000c0c225290740d84010100600d401060400300c4003240112240d0f41e6a85407030200c43c03034400d1841001421118 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 756993282 1250 756992032 756992059
    0x30b090f0a0615020c06070303060b070b18010603080313110a0306050103050c0a0303050a181a180d0f060513060f02120601020f0a060b040e01060f15050307091202150a020c 76
    0x401003180c61446043c0d001780300c802415801c0244580c404401101815074507100020f88409402c061f0540c58040c0002804034a005205901502203240d101d04a5074074200d0b0070300c00150b6000c241d0303410100c59a413100c2d0b02e0820b4580501003020080d5540c0e4080c1c040080001082542d41181781600c2c40707041074920745243c000501091860900004011170402c0c44184c208902c6480403841e224113608890060311740d100d030088209129031621011814002614590f48080b462400c90036600a03034041c20b20b45459106d44e0b00c14022880e0081c843c0e511200070078a20005042d204c00d401e030300310500f0403102800d203030000003c0d40b1250860804105020002e5450340c004201850111015005011807510a0341c4020003082a1940550310564031240d07903010f10800d02c5031801400d0020090b481c0c5c2e50a040315220340c0c2840b0200301040160030001c10280030341c0400b43c00c00711104070242088500a51002134440d000c0055102100d400119a04041c140c0c00280462481400e50341c1903d140300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 756994532 1250 756993282 756993299
    0x10e041a070c0609030e1005130e01061b03052206030510060203030a0f180602031b04081b0409060f0507090e2703040f180506040519020a030b090f0a06 67
    0x3011581000810075a4046002140f442d4100307034807582c8240b074521070000f01000040d1559108005140c00290f02181c6c010a40c880313602540c010b0309418014061661601c2c000804103840240c403110740c400140c403040100f41c09071040d00c0340501c090220010729001ca80c100b24100703d95201c0c10000a0a00011400c03424484003c08162a000c2e4080d44c40c56441d4900c141c0500310103904440ca00c2d9417080516248146440860507080c8508800b50392400c0480840301d8044241e03c00a070141010001005441c000003898500c911000202200002048000400801c54503401510300b5003402408403880310654406c61140c2c0c501d03204c1e1004a40c0301e004440313550a00f00c40311108501c444120032102040d0000c0c09000d015100c0c1103920b07240e1602400c0c8011080d41e402044850548011201048090f009980e4044800d0340c040041d031a00e00010b814101c80100000e10503a4000f0340441c1c810701c607820000607490041c20408040c108221003004900c0c007215404080c51918001003174240c0e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 756995782 1250 756994532 756994583
    0x909060b18060907020c150d0b031f0c030f02031e07050c280206070b0a050a11071b0519030203010507020106060c0b090120070c060207180e0c0405010e04 68
    0x90701400345480360b40d0710030038006400c401034088000c2d40302d1000c0d101d44950700c0d050300b0320b60310032030b090940c0e101c3c103034500700006841d1050f8845c0e12035003107001c408082031143c00780541d42006541e00031810312000482500104440803580012900010801c0800e0511061900c586648008001c1c01540d40d00e104846a000b20450034405400001c0d00000c4050102d46010440c283c1d24241500e6007240d900144081e4031a1f0801c0b2900107020040000c01c0e0528030032207510449440c02488200840102842103201c0c0c0351004100341c84007030500030444201030b0110060500a0f0803183c2500307610b10070610702c14543c4001ca10a600300340010348200d2040c0941d80c11aa50b6441c0c085040c5070a41d9844c8160800500d040780d80d40d6100d9044081c080049a90031020420200182e9100121300700001d4403082074100c141950301c401c00c1000400a00d60302000c946449410001e400c0b201c228106007070802c50488954054100f41c0086090404500024041e92054a5101c05000f502883d4036081 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 756997032 1250 756995782 756995809
    0x20310090515100305010f0b1c02070506090601080a121b02030d032004030f020d03030f020307091d01260106030803100f0e070804030813060615030c020118081e040909060b 76
    0x9203151410012658440040c10b03141a211803a40c141025000400300ac0360800c0b002600c15038400800d204a62500744846400340101ca405843d80300c41c2610703401c1c1c00c2c03441c240f504401c1027515000440c940240150010b1001d0b801010f64007010202c080c014064400d2402c909200d10602001c0220410b40e08111011294010715020a081c40c0340c0821040000c0944240d06054490650b6003441505100442c071452090710303420f0109007460100a44080145201006d800803980103000041c425800c1c5600808403526200001c42541c01e0f441c050280b9900050500f00040207202880c00350480c1141511254110000610340e5510029115403084da4442c0c042030448000c100401d1051718000d41c0000e032441c4000a518065465401719440340d401840c010b0013400c1d4100c2a40d506026407404488244004e100c078400b074804522485c150300744000c100d000000307180a1071b451204500e1110040300f0740103607180c1342c6e289504800313051032100072070389070340b41c940f44246c0d030b180064400d403c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 756998282 1250 756997032 756997049
    0x9041b0302030930090d1703070e0f01080417041211010806030d090303080612060f04050132040c030b070203041a0a0806010e19060c11030d1202031009051510030501 73
    0x3c420f41c4043c04000c0d80d05c81c6150a03003002c2d0150005000c00d442c2c00a90020a0b1607864441c3d0fa841c0406009040d0240e0b0100d5900c0307450a91a04c080a0380e211140d150801d411540b58a091a290f1f000500f241c810703035011800a00300c211684040c090039201807a154002070300c5104883c0da8880c101034559800341c060394080780d0302502c20300119105e00002d40e4131901c090840c0c0c001c102e100c10700500c3c025044907004c0c54410040f08110400000b8041c05850000c0030419840321164982c0c00601701622490307041d1100c00d040b00003018015101030940007544c2018203001d050400000080d2291300c40e0003a01d4a1240036040c40181242d25800c449a440c005d5852401c0d03030f26103800460300010070524059000060302d84240b8021390b020f0684004208a0325a1705a1482d0b501c0c00108601c83c7e0344015110b034001c0031001012540004405400385451000181d40e65514241e0f010784402580101030f10620b80401c10808010f00344201400c50401c41e5940810b8410075005c03800c0d201c0901450f41c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 756999532 1250 756998282 756998353
    0x70b0612060c0c01090c17070e0c0405090604180b0f01060203180f03010e031602090f0903030103080f040f03030804140d02120f07050625020304060c0809041b03020309 74
    0x90b41c070320700c006040b00030003034800460144900e8031080f000e2030350b80e0004003203400c1902000500c0d00c0104644001098080785030501303894007a0102d4024000d0380b09990080e80300c0400554a03544a030b000119091203210b00c010280b1180c04c00c0c00c480e0008803250300a180a150001c24420300000c00d403150030a2400c900c810748102e08080c400180c4030540315940540d01c600540c0a42c207000d0015200d00751800c0c1c10301c003800040e8010420700070000b801d201e005001c0d01050002ca450302000303c0341529080303e0819620140200949100d02ca0341c0d11410712904903803000702c1015030210300e943c0102e0090000d46c2920404e48041d94607104002100030140e4840c0b0514403d40018202520484101d50842170501840303456050904904848000200020700742003000044c0c580003050320308440788025410306041c900c014046058002016081100220704180680c1d56070300f0090180c1c4c4044179041a2003180d82010740a5003003a9a010b266002e02c1800903c80d0800b40d110300b0b000101a501c418 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 757000782 1250 756999532 756999541
    0x9120804120206070c0303211112040c031b0e160c0b09011d010b011407050613230a1412040b0a03060e04030c02130204031a06060d11070b061206 64
    0x4031507010301c4412a00310030280000c102060200d504800294001e8507507000c29150020041491b51110fa12912101d1520703a054905500712010f40300c074140c510700900011780b04e60515400e000300c5640010030412280900c1d500148914a44c4012a45010170480c15522580161001907406600700350000c0d05074001040030032406222190000b42e000000030328401c8030980000724405420310055941c3d10340149440f02d50344620b517220350030145944641030240319070b210303501c071940605040f41441a6000c15418031034224221640990261640a4100c101e80c04007604c4115100060350315840d02901d8081c070319004114103040110021009250504107101c0080d280c1000c0c02c50010155102c0d804101c0b0404445010b0059000792645407030a00944100140b08a400454040941c0184070801c0042c01c3e849403290301c40445070055071195143e81c081806401400c04c10802d040c20602c40d9092183c00301d0007440440d01075404220030366641c01c00d01020659240065000e5030101d800034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 757002032 1250 757000782 757000799
    0x203030d050703020f0c071e0e0703090830061c0f050f1204030c1e031202152406070308190b06030f010e10050102071703120903070309120804 63
    0x40d40180b1506006080c4102c107000c40c50b403504510424079950b80000f100b40b0003100070b841071040c010800030801200d1428206030341c982039405410002456142c0b1205e004006400302914000307020303988244826081281e4500c3d510050368100109a580c80010446a003441e400404070000c9901d4440895505903417040c03400010048195454040c0e0052820103003c148000350042c0b14061100b1348490550402250104803a407010007800040140c013700e04c41c01c00d080004998201d51741c004104800b01050b800c185405c0c00d40c2c0c5010f000b5200b00900340c60582c4801160621000107214991a0001846001e12660358044c0118074204006081006000704080b680d105983c0301040031401302001c034010f030700142c508414000c0e0407030052220604070303040f0b20b91160481c01200080d0b4034080c0083d454174801d000303000500b210b0611041c003d580410441d04880114448004903191904100b81c5903005880201e000800fa6000080d11440380c000004065400440c0c0ca0310302490201c85 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 757003282 1250 757002032 757002041
    0x703060c050316032a050d05152814060d0c030501060201110f0403060513050f011406011b1b23030c091e060f0d0606030203060105010513030b0a020f07080c060a05040203030d 77
    0x4005c10444200b02000708403c0034054a4010300c0f480250070308a50f1207108105064407003040042d1041c013040340a002080f100403480e0700b196041081400f0b00445480403452504c284c201c892001d60510480a40c0705505610841c103e0342c040e0b000300080f80e99031929403403600c1022004c0301c010105120500c003017603869004075006400182081039140c41682d031306090486989404e01e90b6550307003840c4e80241104101180d4040030920740b82c0c0f42c1c440d1403c00040c0300d480441000e0030812012009000d88440001d090b0041c02d90000421030081001c001030045241d40200103000e030140100b056120304004082c54080c2d02402014448030981001103103075450000e1406074004c142d541541840e0311000c440443d018018000803905c80d0071030040c07515014040c1d000c181080f0f0308102c03203446c1036514850041580e80c00000040c5076200d40ca0444080c1c000e03410021441e2038001241c0040181c004024a03060000c0401d40301190b841c9050b841c00c81d042114080d4154100700461b000c0c0409a910 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 757004532 1250 757003282 757003361
    0x504060f09150e280605010f03110904152301021b0102030f03010605030a0c020309060702011d060c0d09050306010b040509100b0f27210703060c05031603 68
    0x4a0000c803c1c0e441e180c001001500b541c0e08292410805064040140b40c2040020100c0003120103200d540d1402c1c0008003017024050040e01016924180d50b0318914088c1c089510109004106010480c0640180c45c02d2803903a00c10360a185516020512111058007035000c8280d2050300a803403044616180b1200710450450749504501081203076031140c040c0c0e600a18080e0515998180d164541007028a04464190503110190340c000c0c044c400480c1c0e102000c0b41c0c00d569080c1713002e2109803000110b00c1d40d401118003800d54081c5021030100c1c21054000350b900c01162055a800009555520030302d900c8000c28040d14180c0102080180f02c01d04010fa40c068201e003601240c03201b417a541c0d91402845812180039031150302ca0014070f00755612441c00000000074400c50a94681c4011300d400120446109114407a640d040040030b04005003050001100a61f00071505105075600a03000400301e81c000c841c00c00381c0790742c2c0200601d0004c0c4079100782110760444481000010021044003007040f82040b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 757005782 1250 757004532 757004561
    0xb0f03070903150f1d120313060606090303030f050105030d0c1505010603140f010501020d0518091602121602150705010c0816020303091203150a0b0c0105060d1707150e0a0c0504060f09 81
    0x901c80780040d009e84030b400c0040c00983d4a002c1c00038210b10380101139035094203101c50180d04000040c82a55800300303900440c240c040c18480c0303001c1080d20b4000c1c0491280310603880d01c64640000021503d800d40c0000301c50441c0140c0c1200d050351040c00442c8801d038280030340d82c0145d00034408180460b000b400144515040b43d83c4200f4030004010019000403021501e40301845107030030f08000020f4040201d02850400c41c0340302130030542d40161404800e03004980203403290401c4a040d81c1104000412a0440c0c0c1d0494028440280c10b0000900940000e407903034408401740ea4884694507201005480c094502000031b000040b50f0f00c11a51916000581a006c0404e241c101c0f0300c8542e031350b0750508001403580c802c4070394450140f0010542182d1004100303a028408803030084000400c40341010409810311241d0580b106110309042d2800000c0400142d400340c81d18000b604034034000507001c48030302d214040e084500c58581043c0005e480d120300c180728000b803461005100309200f60b003050344c0200d00c41 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 757007032 1250 757005782 757005811
    0x6261002181e03010e0d080402040c030b090109240e0403120b130905010e0610061d0904052113050d05030d110a030609060b0f03070903150f1d1203 65
    0x4070001001d10303610208822480da1041d00000c01030400380250005a1034402c09032444561100007c0d08030721005000030b01c82d5030345050b0384594501a51081c001980301500c0041d056860f142000014600d020203810654081c0200c2c85a6116501450b029185103440203503a6446583e008d0300d8800c000c0052128045c1c80e420303030042d03984420302c04040c6813050210114003241c46080c00c508403480c95462140301e8118400f0011008031004602c82103c00030302e06624082081d0b180e02c2103582c144210f859005415006000511500055590f945040c1c118030340d903e07800c00b050411042c810055140030740003601c102040145089110b9201036401a4213407458130f141d039503403102161444800480561800305d199503801e82e140c40b440d40684100101046440d00f8a801281d15015940300b03561001c00000c0041d0510b803041c20304000842d8030444800c402d401b03400c21034000c2c0c20804010b04429180260382000710700000015515030b1000c8000e021292850200c290b03095000500c80042c15004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 757008282 1250 757007032 757007077
    0x9120c05040e0c0405090d0f0809030f030a0b0108060904110409170c06040b070504051302090d050d020f28020f180106031a0301140c03181006261002 66
    0xc07401002c521a0410020f44001d000440030030040f0740b8080c2041680e40d0041c000055032503080200500021800d0034071042c20b039074403110070707203544958000355100c0b08000c814070501c408103402c21902c0702c009890381445035850300c084c401150022a806444205806008c40303150921b540810943c5c0e001c0e4024900340a505c5c401c0c00ca580e80f00b02c40c080700552000040000b07010081c000700d9000203c525020780b0342403814000030b0400c05443c0a20b000c45900240742c108a603903141c640300c01e00d5489010307601110210b00000e5210340c0000f80e141040e010b0303070b5540c01d24010159412408985800c030000001d404680902c50400001c810464005c0f903016441c0021402000c401802451190341c0880da00f00124660b003500c00d83e02c91054001d86c1403400d02181480307130b0b00d940c0390b00000680c00380b522565020380f000f401082581c001420380c021552000086400382c2c0121090340c0803d26440f8250840d032207401414100d0004c16030349078014004440300c0769442d4004104402d0b121003100921a00c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 757009532 1250 757008282 757008289
    0x12010303030c050c031c0b1002060c300106091523090d06020703021506010e01031a0d081b0a080a03180c09020703020c010305070c2901260d09120c05 66
    0x10704191440060a0402082c41d443d2a0050241c01f21042d1111080f8006403035010b1364583c00a0882a580100410b21000c2035142c000700d072500200c40c54007440d00305440500c3c1308a901d400e000342e03c00140d403000f021809200d41c45915a0b20001a510008010131010362081110040322a1003941d103401c10191460740d0b03c1003204d1010a000b040d0040c1d58020b54034010345454030810911170311200005c20082d5a0383c01481c03036191010b013801c0201d40d84101d00410400c4210f00c1d0704583d07000d105034003240700340711500000d824a00c4171803d10701c00b507026a44a0583e034030380219000300300f110104901403541d446038020f440b903c03081e80500000c100c11651400803081e46904a010641d9010130002c0605504000e842e100d00002e080411241c140002c00904400d1101c81c0030b0502c41c400003552150364130003030303405068001503201010f05507103030041e92034400d8032003909140c10214158000f03080071000c5081f00c03020701e15440d001041490040302d40f016032035a103000d0300c1c1c08480c100002250788 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 757010782 1250 757009532 757009537
    0xf021f0212040821011d040f0b0c0a033c092f1914150406020610080f06010504050a0e100507030e030301030c0902070c03210809010212010303030c050c03 68
    0x501c03c0c1c44044c0c0303421642c628441400d03c602044040109814010050300b1002100f0030051612121a0102a81c89052034070f0b4441c0d214100034521040d0208106601e0f24100282409100d10f540c103010501d80170b02400399a207064a590502c0e41002d00a180041c41704500c5654840541c44012900000c5502e41c00001480800c611490210314003420341c05041c070b0401c003090244100c0346121019680e0010b04803402c0c4500546541e03451450304010b4555406442080c03800c1e00701d4401da82d881c0c48a0000b5282c81d401d44588080c206400408980483d0101d441e9044210241c01000142c4c600306c00c002c041c0101a0489221960321900801c2c650018880b209680000f448040f40354100a4001012500901003040c41a04140b00500000740940014002c40d988041d0244e00c4115508140c1c444105903400148070741154043d041d26a2035440d008007840e0720b5901ca00c2400d0b40d40350812420b074420800821340d044002c40060000a010754004915a030780d600d050b80c24480c0c103040c65403843c0d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 757012032 1250 757010782 757010791
    0x17011a123a05070f03080a02090d0f030801081f053301020c030705030a02090408040509010603050a0f1812030f0204080105191b05031306020a030e0c010f021f0212 72
    0x60040d485281d48410724454604100401c0c0d18005103042034644a60b030079254004801000c01c400000030412204080d019288c1c0d4410080055120706000e00d401e6945c0e800c0c95800b2000700d001c12000065924000c69403c04030521600b40c00010000980010000c18005007001d201c89407010b081d160b8196403140308095460004510300740c0710280c030001381c9071140300f0600c14401e80c000e00e800c0c0241d850218545400581c103413074a4015499502e044030340c90085070000c036003210480000142441c2c2c1504070314001d1518180c1084140110101c881c203466190102c10480c031501107090340003440240b0400da809c1c031180360010351410502c120f1801d0380c3c402d03442144507a440c2c50900814011178043d0941c0c003801c1100810142408a21041c0003a4202610750148a0007200003080c02010821510718198007070b00440d52065040d0003c0d00801c14007142d80d2451180e4038050390b440d4054032465000035502c1d001411505080c5e100e1001003103000c0400d1745d820b0b800f07004001c01c2204825565008 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 757013282 1250 757012032 757012093
    0xb031503031b0309091501050403081b030c0703150911090a0e061305160303091a0c101d073005060702030405030f030a09091d0d0917011a12 62
    0x80f80821003c000c0310101c00b9040792a40c0206402c1b02225030307009401c5504580e4070010298883c0c2c03007103480039200e100d07107400f05000d800009240d41c41c1800c0802c0030343c2500c0c0f02d5a000c6403101c0c603c502c20011540603542c000d00c0030002840065076031810181095020989040c041034010441100c181000b02c1038442c1d40c100345003004c030345c010000c092005540b039110020102c1c1c46180303952401010031006100b103984030710306075040009000260007116200b2030766204680750303c409064450001c02071401e06d1994020400c640044088001c2850340c1210249010b103121042c401000003d9400d041d448880c800d88242021000101706121043c4200d5164020715111403500040c181803050040741e00103940c00c204007030302006400840e070300c05030b81042d100062031110003940d202010031450a103d00d2441a29510b00d10560300c9842182030f52401a034045110100d1b4041d5800e0716074482d50705d0b0b10b85840038051800c50038960740c08a00000400211517803005a40f0107800082c0c65080700703000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 757014388 1106 757013282 757013287
    0x105092118130207260a0207052b08030412082503021b011e0e0c0f0f060307110d11030714030c01020d0e060606040b031503031b03 58
    0x1000c004030411542c1d2545410404440001c8150071540710b05c8803224110303040284001d407060281c0d190000c1154a080c04200102901483c801a0f04014182088180f8503150350b101556140038038101983c80c02c0a0030064485030550144905001c0080c041c404d06101210300c058800c0e000751000d80703c0d0800020101e0281c03040c4080704e1a560304566101900d4a410352001030808115003070a811030301c044c1100c40590f180b201118044e604511040551400c1c10034110002200003022546d4826018000407032542040e5140c400091b080030503521103400401039030160800d68140762000c080e0200030239560748190f50f001003003101c034a080c3d22005036003001610324483c100c0000f55201c02c640c8001d10001c24148032100d00502c10344000c40d5644c00c141c0c04660039a005254403510f55a40d10365009040031a41c100345405210070003c04c1e20044660f4203800c1a4109440510ba = true := by decide +kernel

theorem cover : BRFrame.Cov 756834532 757014388 := by
  have h0 := BRFrame.cov_init 756834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 756834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 756834532 ≤ n) (h2 : n < 757014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
