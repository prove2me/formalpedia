-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3630
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:13:31.041732+00:00
-- url     : https://prove2.me/submissions/b3713945-bd81-4471-b693-1b3cc98125e7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 652697841 ≤ n < 652877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 652699091 1250 652697841 652697873
    0x80c124c08031611010c050d03061a0717130b03090f070902071a0a0b0a0b03040b0106050a02030304120203040b0c1c0201060b181f050a020c0109030c030b1819 70
    0x51440e0100b80f042044038102c407980c01825028043d840400d240e13000303640b168801940310042d208840d41d480000b07001016544141c26a8954540c0d82c8120100f00c00e007110540c40d44004151410304184611143c1a003001100b5855080a5500460b4250b0316101540c8101d143c070b40203007100710080b40c513607081540b071303500c1043d800d070042c04000009038142440703c403c0c02c1513007080070840d41c4400700400684007106009810092240c004100391482000a500c240c0c012070030910103903640d0104591601c1031800d045c0068109102090000300d154040e000d80f52023606c11a0304242e1122110f090340e0740070042e0910507132b04c2400a1400c4118804490a60600a0000700006490205c5416040c1304461902d0601e04e203131080038840b640d070701261980441d040e41d0050800701c4101400741041e807002250801512801c011100258070590800302a2503000300c6c03080340285940d44082c00001c0c01761910300b02c911035619281c41e008080010000d040b10041100f803c00e01c0b00d083c210301000001003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 652700341 1250 652699091 652699093
    0x915040c0b0a021c0306090e0c0d17042102190503060106050c190c08061b0a0813050114150402130b0a09091506080c124c08 55
    0x420010400e40d45420080390740100245680b4020081c0c1241001505140015219103c3c10065092a410b60000381aaa03401da401c12028040c02d03d03c507a180c68010909030701087d01c0c3c4100c13000440e4402e03504042c3d803071240501e0406840d80c02440c5800910100450f211a020150000b94686007180d02d0340034445a043c01e40f203034140800309842d00b00c14055030b02400ba0010f140e0341c1e585810018921412034080640341030f04030525191915074450b2003600011320554011a1059100000342e180012010b08928502207a650040d250034400038004c05142071241585000301e0000c0c0034042da2400348103000f0005140c10400000c428100b022010300a074418042c079105001c3c0074039813005444001d1615911054484001c4881d107000740c01907480c490928062286042d4850340350741c25910070740c0b146c080c00c1e41d84c100c4110f014000d44a08080503034416020034002980341045001610000c50001d604182401c0080300544552944000a480003204485d020b00d07011710740310150406d00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 652701591 1250 652700341 652700383
    0xd021305010c050a03030b0114070f0c15091e0e0a05060901090e0a0b18100501051e030309010c030e0d050606090603060f040b070c0b090a020a08060c0a03020903030706060e09 77
    0xd03c40ca6682c0504003401001e0558901d004030172a8003420160391480c07103000380c007aa288164a44070710444a0440202c0e4600f810b050089803c89502d5000102c1c417030b95030f840c0030b0341c185450b4090004d2680c0e07551071f1041551004001c00c140f00307401d44141c0b05440001d400300301400c1506c240040354105031b00100c0d8091816484941440000c20300b40f03140390700941d40b0740b82500da144e02e0701600106503084480394410604500c0c1010001e401c0030307040b128111603a1240c00d01c2144400b000c42e0680300c0b40e13981500100058010f560085c241d88045038000d207800a442000301000c5848410b00c041c0075100e503485a8100095883e144000700d60001054003e0105410110403000d00c0c2e17040944024903500d08100016045441075071284c5241e0741188404089050490003903454544074a410fa01503e118040810907d40008411b4020b211110f2042c2c90705034907800450003074001c4c0200e203915000130000c09001c02c100e800b600d0040c0244804012540c2011040e0b503241081000061801190b18 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 652702841 1250 652701591 652701593
    0x106060516020315040510060e0606040902030a1b091a09030c09090c0901030f02010216080c060c0118080307170c04090209010c0b071e03060b030703110f0d021305010c 74
    0x205072a596480300c000251049214800281003040c5800d60f036402a42c00ca04120034494002251310341c100440b042005000e880e101014101c0c01c0c01c8440700d40180d02000b0400c0b2041041c0d000315480380d02c00e0000900c203c00c0140b40b4840c01d044d05180400035203150004d00c541014484880218072a1a443e1860078042c41c02103a02c88040302c2500b480703090590006034003207070107100480d14840020070315082580c40f0316021610301002041030f801440b50040344401010b42d0500441a03880c802c00030141d010152007001800d5002075205034803552141084c10802c0804004510000c0c8a0740041e61207180510b070003450f4183d41a1107044034003802090000e4000100102c3e415034141180150381c4500300d000585048220450040410070f040040060042c0d000038a0f45003080d0341541031101d0b0940140c00c5094031582c3c05140c507020010404074181d10300070f500c03100c03021070924036090400070a4030400030032b078105d280150303038240d000209100924a2006850040c0000b424000350810325 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 652704091 1250 652702841 652702847
    0x405251a030402010207091415060307090302041d01140106020115031707020d0f050c2106010506032d01050f0a06020a031202040503120c060105041b141e0a11010606 73
    0x12031810403004240c00408a810f5900c2030000300c01400002c2001e02007101150840340c2600000c9a034422041d407a803051200a2030805d00f121b0003421345940e2261020f065230200b00040420004241c0d0700139074003550351003080302070281c0041e000740d91002000540c50403501a081d2107503800300700c181c118000010710000b803e0320283c0c8080c80ca440c40b12070315401d5500c041408008907101c09000100350301c0c200410002d00041620360500151102e0f9807070001e10040f21100e0124030400800c41e044000184202d08005018580c4912003a1015800c5640300c5265003001c44408901a110803014006102c2424226407880c804442a5183c8001d6032400500170f440d9407020030020100001010401c00300d4a058050700d0181400805840d0044800100302c21a41d115540c030740014081c05000050903d001c0c8030708801c4001012340718060001c44003044450000c945e000800c0300c1c0090048100000c410302d0300d8081140c4460440e1344d20a0003660103004ca81700300884072926814a2410b0002940c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 652705341 1250 652704091 652704119
    0x11130503070e0f0c070f060219050f0720040e0d080601020726010b12070303030e0303070516150c0e1e0a06230a03050117070e040809030a0209040525 66
    0x1103000b209180c9902c9041141c484d80c0719028001d4000c862651010050040716402030151800402c40040c404810203000d072a03074007400080c849420300034002c0c44085642c0c01c0030b1481d802c0c4162810703051030342d0890018003219030360100c0840d00c3e40048481e41242c1d40206c112504120240001d140035442c041c016105c440600c4d2030842d2405060500c009a44025000341c01490801410804407a0140701c5642c0e032010b442c40190002802c24404007501c1d00040210381c090300155070350b145800049031a85081d04e5507603604542e40740740c020490503280c0d500c0c45480b0070306450b076441c15040140c1d04200007180d040450001032100000302c48900d1542e400c04203030211030b400d040c8004010004201d10f0941030710035560810303610b40050514030080d4540d101c00e060b1410300c0a00005241d900c00c800f56501c00038003038075031108a40340c08600132824100c00382030420300040480302494003950210f4003802040c1c0b022540366202407007034032402ca580b101070841414682c000e502840d10742444689280 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 652706591 1250 652705341 652705351
    0x509070519030930270605070311030706020307030507052b23041b031a0c070f03080709060c080304060f06050303130e0703020702011e1211130503070e 67
    0x650301c018150820038003440f2848030701e80704100da2008907050501244e564158a0b000c80005144041d2840d8520203000c4603200040c2c1004034100c1d0380d0a00b8019241d0341c1c0007400075424440c41003e141d02e08071041008011680c842c10300541ca034100108060309858011300081d05100013801950100340180d01490100300c0025414200b0070b81492003d40180541410b401d040341100407000380800348141e030b085c0181d00ca204200b41c0140000d070b69581c06815804020185003a5120516040d50303c0490b03603030040d012609152408041d41d5030006a1003180c2801c4000c5a8100100486240c002c6c403014000c21190900e5041d1a020341d40d08401840003c100402d0035070303110403460341c0c0849603103d00702130103018049a07541c0790050208a4220700b640716040080c031000c4001400b60b4407070b0090310150b03607040c1c4440c0081c104000702c0c507000b59041c9501e0010072200014112003404c05004000300002c09155071907441402403d40009145160000e500962000c0c400708052032070303143c40b03076802 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 652707841 1250 652706591 652706597
    0x2100509090f0411180103020310051b07050316030e0f030d12020c0f070b0c0d031401060509030a080f04030204050604020403080f2d04140904080d0e1204030b010509070519 76
    0xa030340c1c51904580800004c030f5001d0b040030582c0c0d00311402d10500034540341603e0003141112145880c1264120a466080f140301c12070341b0f42520245090b80c0014003400306944184140e80c10b010301040700791303520000c500e4103800240c2420300c0c000c5c6906150014118001d801d40140148840c00100038102480070f40104600d40c8c1c0c00219880600014081c000d80049a44180d03609181c0d951100350141d00312450700681400741c18801c400c1c46000e88200380150186051400160386404c80694050b0080d0785240c1e01400b408995000040d0203a0040c40026403281c52242c45a0960050000b140c000900c014000e5104100500c0440c80880c240e40110803124807203550385480c0001d9036101c4c24041c015101a5008070003909110400c6c0018109950b01180c6450b81030004104110821005982c090308005041000c00940d0342d250308400201982101240c01503440c1c50101c0026620592041c3ca50303000f040c00501c440d2a0a240403a0448440e1608030b0030300440300c6880c0b034003c10291060080c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 652709091 1250 652707841 652707871
    0x60b0a050a03090b0c0301081009050a02012618070e040b0402120f0a030e100305062d130c0305060d0b0a051009020307090305070819060b0402040b04030f0210050909 73
    0x40240b10390882000d4943c808500c00d03030b41c1801a1151826002130284104030f00030700e00780d016440b0045c8034912295800c0001000000b80a03001511407030148581a031241d07030a00000380140160703035495401491206021215042c0052585040c8070458000c0030000c0f403190144400b02d00181e030001d4110742c040b00d81c402440c03a545501440c10038403640c00301c41801030318075690606400480301c41005106445082d40d101f60503030100c08490701200c1d4594420305010b0b280c501c00203030000c41ca10014024400180e0841884001421608440e1810f07240305e07101c212120340c182d454010b00b50050000e075904c440503100750b5180401200010070400b02c0a65902c0044d5050608039610002031030743d03000c110340d03a050540c00200703074030b410b40002c1e1014030662a002a182d0000902144034034900f01820515150740c3d600c040c0070307040807004298040e4092102180b0f0780804401840110b00c121540000e003880c82c03044c800e0641e2080d007510140f200501040d5101c0c2c80f0404003d40c08000d158242c01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 652710341 1250 652709091 652709107
    0x1506011b030225032307050a09050402150405180a0f110903010c0206070504030318030c1e0609061d0d020303040f09060603020306010f03050a15080c241614100519060b0a05 76
    0x1141000c6c55000590000413808c0001d0054816032015000343d001340d410703004200072040704030001d116510032650020215070446958104098010346c100f00815804950340d109500540d042c0c0b104020082c6410000080c91301031032500340700d8190090001d0024140034a860766000d0011300541c03201a0500c441050761040c24008803142002440c2d00135038031414152107040801065203500d0400808001c2d808010402a000e0000881184e040380e03a900c44400062196128842c0c0c1a1300098000f1890100c0a0040e6000c0c800f40001d0f20144105e82d450300d1410303c41c03409507115a1300000606104105210b103590b0b200c0020300e5204601d040114190701c40844080003003100a8404084010818000c01d1001001c100400f6490301203d444900d4001c8440b00080d20084c60860000360500b0030648848000415505e411603002c1d42210009105941d9460700f081c80344248a1603451391841040200e042c0c8210300b00b9428218101009524109248514a4890302c000001403000100b8000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 652711591 1250 652710341 652710343
    0x501030c052101021206010e0d0b0a0902030c0301140906010e01060e01031d0a0c050102070602070f030b0601170f01030308090a05061f09020c030403020913051506011b0302250323 79
    0x101070b144854000c6582d40540286501402d00039181540010b1035402518000d1a1050b140f001d007503004542c01d0790030b8031099a40c10040517100b034100d0f018020101c501d001694203100351061403009000c2c01d229803a100d0801c9003030180507004040440c0ca020018064a507020034406907010302800c4c0010714a850304d6080b481702d00c218803210001d1203825100d60070890861200003c0311020303000c941030b0f56100e51090340c842c19a07000b12190b120015408001107041d0001540e009241810132115804000340700c680c11400403075010b03200010701001041099030058885a001080801030994a54507640e074a448810281800741340c0d90301505032606944070003a610000b481490750031580d82410861940d100c3d040f500c802da12880c50300d4002401c4144210100b440c144d80540500055130545401d1440c4413809090036040100b509030b1600080001c03000802010300a400609a032444140c20350705036029a8001c604000a0f0035040000030f40c00c00c1d400f1000602c0d8240200180c6000d46d90f5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 652712841 1250 652711591 652711639
    0x9050f160804111906030609020414060d0603050327010e01020c0108250815060c070308220803130819061a03060403080106090506120103030e0103110307050c100501030c05 76
    0x90340800d000c9860b00c84d01d0001290a400c4a4103502c0901869030b80f03401c0001280a01e104001c0c1c1d030b24100076002d00381c2c42d01e100100301c41d8100303803c002120750b101e841e04c41c5140c0100c2c2036100c4802d0034101c80c000e05c24000c80c460030520030910b8451080304111000075181d000d10228541880b12860100d441a125499041025010007551010f4101c0702000182000810349085442c05680c0511001c0740c00c100c400c4070040202a00100310b11440c5659003a900d5214118200c44100115000482e5501202e40d8030010207000c401103031a81e00740345030143d000e00701303902c4185640c2c40300d0710b890030f0004802115181d160700020001800340340d800c203c0301090121446160715000e01010401055005808035058400070740c1d41020702070700c40040c081284a808002c18072003403030f50010000240300d42800880d03d20103150105a42c0000d031072a54040d0410380d1558003050000c105550241d200b00015140484691000c0c842c0e0b502d5a29203004c0e4180c14007400340928a00d0812180c004505498 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 652714091 1250 652712841 652712873
    0x3c061d040e100207020f040903050a080406020d0501060905030d170112080705010c0f020616020304140319061e05130204051e1303140310050423090709050f160804 72
    0x42c0d48a81e645454242c00035402810f003280f01b8002d0017440b10013420248a102c01c2145e258032418a42000114140c5138080010b104880843d000c01900e41c80511a02030706008001c130341c4801d8101c80c2854109428003080003100710810003c0c030f064406d503039403450645044036001d8044082ca460241007201091043d00d00103445507080c802900d52050703000d10065000c440c0307a030a589482d22230500303603c42140ba402d0540f0050380140028843c084134100b50400710900142101c00c00243c4c5400f0b000030544072103003a902595035105520840d0b0296000c3c044c03c403a8180104102c4c581250690250600c4a80281c0604e9440000a08440840c42d003514076840030010862945881400201c11080620048001900c11170700010f071200c00e8410b403401200203410005000c0c1c2042c050000034800d0303211072040303002c1d0b50a00110001042041c42d0081800001030961907082c01c0940301500c8014220484003110340b42040104c8044154081c01790400d49480d401d282c0366418201c150104044c1d0b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 652715341 1250 652714091 652714093
    0x40504060b041a031b03070e09040b090d41030901090c0902030f06010f02100f14071403070503040f12030212101406070c3c061d040e 59
    0x2404281c1c0301c1c850001e00100c43c00305a4261240000140184042c002920004c000d105041c1200c40100040c0f80510342c0401c0c0d0380740111170409810002410003400b5a001d42d41102100107002030784809112030781071001380381801e1b074500d15502d2a84080c0c0042c4001d40030120320b04903190b0096088402800b900255000c142a1a0305007910428000c02502408441003194100f00107554101402524811007000120588540d40e540042d80e020300031031449021030141c10100c0358110390380d00c40e04c103c0c0c6045003070004890039040d52250f001c0d0740203417251050101c095219135860f6003c2c002c0781da106081d450100e07104d40740e03454850703890580848000c0a45603010003c403400c03545139014002500485400161540740e4032100004a036040c0036204070f6091010340101075082000c001c01c0c0b400e00c61101100c07002e580f41038994007241003409040581c101d646005085030b440be012400420b0f00320601c01c3c0c1840c40d007040030b05602d00c040f60201c400d6103040000c80240e03980b85d22103008c80e01d0302d070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 652716591 1250 652715341 652715351
    0x10b1e0d020408150f010501120f090803150103051e040305180a12060c0c210e03010203070207050a06020f100f0e0d21060b0d0e0f0a03080403030c0512060f0402040504 74
    0x242005445100807241d0440560130b160010300c85058401d401030480e41c040e1a20465440f44100f400c0140400310a00d00d00c0d01d807610f00110018504200841c49501401c6031450003a178034000040554501400804070011a40c3e04400c4030f0f02c01303150f59034000c1c1e4182041c0d41c2d1a6a002d004030691240b0540f1700340d00600030803000400720070060700e08034042e2061404200450b0700410588840304008009000d500c06072040311003c0441d211100603800d07042c1000c02c420f9003114002426680212451b01c0142c10a0004014504199581c90003030101030002d4851121042c00c002d0703a41da865104441082e0b11810002d5803540c071644030b00b08050203142035841c0f5825201c4085c01c01141c07404e032402080c030140000d0a00503514400c41d4103030f03502030b00d0b00b616100342e00c0d4215020f024200300381c1056005040071015001c03c100030340f66034180f0a845005072450542409800c50f41d03601c603e5403d01204000e60040810f04c0c0e45c0e02cad41d10140c1200d12902010350180410b00034007450f000307640c11500d89 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 652717841 1250 652716591 652716599
    0xa0b0d29010c050a1a04120c20030102070618030801080a120f050910030b0a090204180507110303090d0f09030f0210030f0e0105090106210f02040b06040e04020117010b1e0d0204 78
    0x8581c5c001d00c945e00070208500051200d0310110796200b401403025001e100c3c00c0d892003078140400b100d0700800c00390040c009414181180c0b12101214000310801005044500006007091f8102d41c01a0050280c0806004a1105622448919402641302000308420000e60312600e5009105540d040c0c000038007104141941a00302030010081804110300c07900c401240050070324040e00840b815034900b410071301224240b481907540584000341c490400e1204480d1400340e01002080558421036a0303134001c2c40d1404c4415009040c08440069000810110b81010b001007285450903804882d81603a11440c0f031446480100c004086055172204068202030400c0401c200540101c0c0c000d5800c00003c04c03c043d65102d40303190040e200901ca4101109040126001c03c1500d01d80083c2c107030002d04049a6402e0030000501694056080300c40f115039200144025543d0000118045c50180140400030354100b0b02d00750b44070300507000c00740d80e031551441403140b154003960306654952144100564940741c071 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 652719091 1250 652717841 652717883
    0x603120c0201170601020d0e280303180f0b071403030703060e010b120105010f0309020603190e01090305090402071e241a06180a0b0d29010c050a 64
    0xc222400d0380040c030754400290100e01032103445405070005030004c11000141c503d05a84030002100000d52101d007001e286140a040185210120310000b0403061460f402c615001d04a0301c0007000480178914101800e1003c958807140510076114020340e21038507154589030042d000d443d4078801488900000c03052151031501a0442c80560708240520079003681c0719560818140141c108610180707074070100401c242d5000b040d00c0c440d001058a400f01d01e02d5426000300d040c591064414640c000c4608120148921403849400780a80e0305100134003814000b514014614000c501c42d05100350f500180960030807104825070301c2c910181d072130900c10411a601f080480d001c0e45241200c081e25503500e80000600003441040c080d03180b094886110f08960009004c015001141a0320f00342d107503440c2c0304145607202001d030310060440c0c1040540d030b10300e440c030803d05441da20b0421024008440d401c9001072084000c001050500a18005052100071304003c0e1401350094806846c084105140c8150807070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 652720341 1250 652719091 652719107
    0x90a090b010e090903040504180c0b031803071109101d0720190311030d150614040504150b0c0303072a12210b03060903031308070501060312 62
    0x1000362200c0845034003002c107101c203d1004403041d03002500300f00014042450582c1c0503c000201407000380c02d003040140d071641c0c0b904803143c01c030181c01e10005c4204410001c00000d6140101e01300b00c0514105441542d80e4282c1d0541b40751094132441a000c00600031010190015008004400242c3d600101c1400c032195648030a40b45074002030710300440402502e50b6104440850740d0140300406001402100507035402c00760010031000c010001100710500340c000c1016082505102c000002d085074010765072100704426034003190078440300620035281c02c4245000c0e201100e80548000c603440100480c64000764602c1c0e00001d15408011039003100040000029501c01d507129220701c0755200c052402070f8890000a42111140748042c86400c1c00114001240300e817244060030040340f00545400030007044403120420005c016a1107540b0007952400b00310103904106044059891810711130070390220268a2031002e024038800080e1b44041000c254000002190000b181080304204c014005117804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 652721591 1250 652720341 652720361
    0x30304350d051e010905150907020d0e190603050c070b0906070e03160311030715051c050105010e06070f0c03060501080105070201060b160201090509040f0c09020c120f090a09 77
    0x6468000000c00a480030072922181d1940f80c581698580c1c85c02c109000a048000d110984e807590342c1501c401291125461580148455006461541a0080c000303101101001906105241d4184100c1c80c00b02d1400301031081c0d5401e4074001c2065900c407440f403034080c403481c2030080404040008020f08143c0100e01c4038000c2849544901c24250f0201c00c240d03030740201800c0301101503644482000050041ba503059007a80e000381c241c4110381e554003c128410080702c400100481ca00080c2010242c5d0042884802d4500849041100d5410000000d10102d80f01c2200e50242e4400a41101441700c15805a0841903200140080480d04c0e132420101400d0b0a1081000540c01e01d80030916560060280c80c0a44103d84401c03420160031908403200d5402640d0141d0500082c0c0401052646811840e0351055001d20141d6242e0500b62030540040c1790181e01a480d1544140b0031000600300200d0300d090b11440c0c180d80c890301c2e0700121400300140d03c40c52150781e6214038055800140038142c1d0700115810 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 652722841 1250 652721591 652721617
    0x711030f010b060301090f0b0d03091401080f04080a0c0605010603091202030901020a06050a0605060304140607090602060604110d05130b01050d0b0103081b0307060b0307120503030435 81
    0x300d080400c40600380e580a0b811180d00c404140014403880600394819104c0000ca8030001c20ba0801c1d000c04145803404c800070650000d00742c0403051000101d41000300100380b00038601640b440c5031112115034408400761000f840c1b040006454502d580c85a2850403400d500702d43c04011a5030344100140091502c06400c4600010180e40006140c0c0007005940e451441078005d040305c400995078410082c54014400c1c06013076912000858103858000c00345220742c0c81a03aa000500714442103a91600c24010224001c0109003030041c80020b9000ca400f540264041d40e000c2000d0101c4c008030740890040115140607a40b4003001c1114108008114400550260310f5104a907603d0300c040c1300700c12401c480050403c0a89078010000100d08500809a512070300c504018002c40400c022802e50781714003010b4078855141c1d041d40715075140500000000b05601940e1240044023541c0e001d8403404003e20103802c100c00c1605c4001100d601f01c15088a010700c0c004c083c41d044030f404a23020202d410807040b94500c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 652724091 1250 652722841 652722853
    0x303090f060112050616050c07030510110a050d02031306051905241c050106030c03060501050a0501080604090303152603071113020d0207060c110c210c0303071103 72
    0x1507045190705992034079046400303017015944185c642c0034006c2c00c008103c010800f08008146007804280301c290043c0d031094000e0080451032051650948009000350050900c3c00c00407980400c6e04001165030300106141c02584a980300000424540460300d800707800a0708040c20041d0b03500c4002c4154100080320300c400c0115407a84101407124141e41d18414800f060941d218229070310349101450340c0000f0206800d0145150b03981c0e0182941c1d059401181c1240909000f0b008102c00390103280e0241a0545801c0740b801e107000700007491128050061802155039010f03120606109400c10580f1910780f1b00355503101542c526456503407600350061810090024000056040c0010003103074111504250424000800f1030200700c0700500000365007030001d0b03082205010012140c009030000c10300450001805108104024000e00310104906807980c004042d400c000b540c4241c824400c040c94003812800c4a40c101c00100c0c903000c40501c10079070502c0003041000400c50003c2024075450026015185 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 652725341 1250 652724091 652724099
    0x2040302090718170313090902010210090b0f04060207020a23011d010809100c0e0f030a1716020d0c050f0d0c0303030f0902060a020114151f110303090f0601 69
    0xe01c9041400035440c2515051000f0020b41010b801203640b0b1a444c401503a14108612903421180c01059201d506400d4072140c0b017200350340e0180071100726003003030342c00a01c010021a541c006050a00404010a09034540e02140c10320406074152408598041e1505107241e8650300341d00b00d902441400f6001440c200070210702c29502c01c2c142c0c515000d4107a4052455542584015982d951006000300450710803100c0740b0b03131290340308c2c051004d000d602500c607040e210300b20005110200c090202110702039440166500c0008115102601410300c00c80d80c00c03a00c880825886042c0d070079082d040690700420520800c407e001c9442c00c08070490b05c003101ca03503001d04654020700c01e0303040f030444019000f880101401c0020034003c0d00044025034195000207843c441681c0012107a030403c2c52b17000c005031744d1110900e60184000100700e03004041e00081c140242d038640001020030040c10800a10b440c0075100403080036016214030340301c5a400000f40c075140d03e000c01d189956032040360400b9071580b1801e40001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 652726591 1250 652725341 652725347
    0x80105040506030f06010506070618030f02060a110304060f15090b10030b03030d0c1b0b07020c030c0a0b07020a0914101d01090513051002090a09140f07030b04020a03020403020907 79
    0x10225152131009804030380e10305820400319401128003682c03000c0d2105803600603541c000c1c1d941501e061107529411042201100000e1600b4001040718011f503142008042c1c11201c5078041c1c962040e482040030800303100071000c40016204c4034011080011486e4000709203520b02e50007010506030199031480750190300c50811419602c08010040d05600100203640ca5188aa004500c2d0400e40781815403c1d041c90300303a85803041c0e08041c3d059a902040300144542e2580c184407241894504900810100c0400c400098000c4c1c02845080c040740e02c00a5002c085490b011429001132040302001c103c9081c402c2d80610104c0c00132905581511a40f07030020800000452001d40020702a25850303000743c0c20003a1a9009140150420040c080800300100020300f00300700740c400d5130102c44409615142c0010501501e039826400c00054241407004448007615400e1000e0b61000e0380d00d015950a4903140d005400030b0000c400f041d5006400010b000386042d030140c00900c1240e10030703201003071541da803c8011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 652727841 1250 652726591 652726603
    0x71206080c030f0c0604030b0a090b070509090f010501020616123608270d03020708012a0807050f0d09020a1d0703020901020c060c071a0c031c02040b0a08010504050603 74
    0x2170f9001105200a00204047c14151544a444040006607079882522403407001c1800b2180031000810004400c80e050425051075a000f9803000585401d035410000083c5d01e51100510b030046142503d8041141548980c102c1c448610090108001019408103c0842d0180c456440c10342c03409516541030f2074541d2402e0340680c082d04a141242018086001504000300c3c0c0341c50222050034a6030510440d5075050080380341ca5200350001e0000e2454005613034250750741c40804c5000380c20380c40b244a03034041070314440c4589944c0620308244a0703074542c00c0564280c010380070f080581c42c0c404200ca00c0e010300f199100e0000507000306e50040203590344102030b020964000c80b1014079803484001140c0940c0c02070b00500003510b014015280c003011103c01148085d00924214000c40c1c7c40f10208210a081c40000f00c00d01703800480c0c1d654502405c0c04403c0341d89218414942c0a038031156206031a01010303660594002d08403501e075071541e44400c110020580300080c01150720031447e04020039820700e2300140c6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 652729091 1250 652727841 652727863
    0x102120414010c03030b190e130302060c0306190e01030308060a320607150b0d0812060a030812090d1107030f0204020426060f0103020a0b03071206080c030f 69
    0x1120700c01002800045810034038100e401c800389925201c0300500766031030f00741c800084101d183d02c3d80314140c41c201c0a0707100f880c00507001c41c000e000d51009a9020907400300f60942d22203110f140300c0da80da8807000c02040461490007003c0e19a21801400816068072050200b81202d02070b1b9150300080d1a400e0411420303112901c00d04d001c80b060800130365401e4683c0720740c0d261b81230100714082c0440404100840e04a034000c035403c031926060309460b500a03503424854000c50001c1516401010520780e80d03008a04e200b00f008400c0080f19004c00243c0355500e200c544000345501401058544440324130b19030b01984199031a5009005502d1042c100510030000f1420081580740104034a81c0b40d91217007000482011350076078000c0c0d001c000206464442403148950792010440f641107000900040d2400e0100240c5442400c0b507458004101694031406410103544540030000e90b2502c4000302643c4403000f0001e0b0b43c6541c0c0c102000001c201c10702144e000001c420590645003c00344482e0200c5d00d60101c0c0706 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 652730341 1250 652729091 652729109
    0xf06090a0e0f06130303050a14060607050705100f02011a1f1e0806031504020919021306030b0f0619030c02030d0603060510080c150d02120c0901021204 67
    0x100046550016800802800505100703680080301d402d00d842c0d0800301c08403048020342c001902880304040d407506c1000c0d8030250340141000400c0340100d404507031900140a0621546010840a00740101800818000c003c020812040711a002901a040d400e0616014025504e40510444021100c0f410000c00b08002040780210140c0103400f072800e0702e240d04140040050141003041034140d13546e4041a81020b945402d00585481d908061900310441e076440080141c5800b030000680352403010a03041280386880220301d032203440070038000b80620982a80124854000003070b4640d010743c08200c85140964440e6203980800044c4046881142d040310200703c11034a490a50900c00d50000f030300610688140d034a09074050003040143d989640080d10300356999014000c60300703815070400005102d4007019029404160000507890110410a0172690764000346a05c10040b082e07040714002d0034950861000c6060802603c111034001e403035028058803400c2c1d4505034084401041e6011550300070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 652731591 1250 652730341 652730359
    0x70f11041b0f021e1e07060c02060d110d15091a04050408040503060106050406030b010333120302031b061b210a050411060a0c06230108030a02060f06 66
    0x4502241c524040c401070400310301945403901e0407807070300d660281220b5041d01c0081c105d10140807181a898007201d1319140c0c450380260b108003c00d42d0020720201009404a0383d080c1c440c1c8031641e516018111100d2000250400000d0070003010f4800d50251748081c5246940410468884595008542d82c180c10040071282c0e0714100c2e40c0318a00303508001e5019104014141c00c055884012900d0811300303810100209030003103801c0c402103a151080c040210024a81801010280062003114040c10240d0888601d1403040003503054241c042800d0052040048c0c501151206040080d2640c00c1505022800c5152079414166001300041080c001d540d4500d06504041032107902d004141e0100440c254954080181c5001016294808034400e900500000c2101c0c90640f03040a0001d40c0c85140b548500300600c9400b00307103a48a40540e0001b6446540000c1207a84170180351000d00c6240d0001c2002c81d03510001181d440408405442c0c5801241c0844555454108103050b0100c41243c40c0c94103d1044 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 652732841 1250 652731591 652731641
    0x3080108071d09010f020f04060315030c18060b0c010b210d110f010504030e210601051e10020a17070b070f0507050a0b100602010509060402190b070f1104 68
    0x310b4036900110043e000160500082c21000c00b40c1e04203040041401902007002c01445400d400340c3c0400f410741007942d140c840e007966142004215980030304012291282441543c0c480380f07034000340140c40c1900100741c5410000e01094044c0807440c00f464014401c0c4034202003001780c8050310b004070005200203084807069114007150328100400700e04603244a01422292030322028462140524065640c110054003107005104490710100c04640c801c3c014022484460b10020035064195042181c20000e0807580a11035134518410782203540c1c4c0440c5c4440c0081c1c5c03090300040c40d040a2032050141c40d28524078600300100b140140c0001501103a001000219403034898903c04108001a041050500f030076038031010300c0d0200303c54003200c880c06008280101505114205c2d00201300c02c1c0700a00403403620624903512074101500003405140708480d030113100c0c40e0f014518006404044038154407031505061164481d8001c0e0819100301310355001c004a0350a240c064004010007070010609a0002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 652734091 1250 652732841 652732889
    0x601230604060c020607060f0903080601052106030307050609030a090f0f0b090a180e011d190201050c06090115170d20030a03020702030f0705030d050309280308010807 74
    0x1a000132648210100b03c0301002842074880c455001846c101d000a00c11240e1a000e4103804016003038506010b400d000c12010484000700384000b03040790401e801d5458407204040f03450f50161600c001c02c03a004a204000503030301c0c0000604030f01411591070801c0150341c2c843c3d5a800050300e01400b0705041640e01c0c18005102d121008003001a0042c040000303140d038505440250b98648121000107030f440350210440c1c42024060840741c0b280c80b03101c0c82031125040090f030f6070b2240c4140407040b01500003240d15041da8025800d4070107401b40181038805c107241c1440c0380d50080c84060030602d02e203c4d0004001c41c01101c1c00c0f1114158602071002800104e074401401d45003c580502200d41004010824000000c820300260200c04455100541c03912403030b1040504004c1881d0502c4483c3d481000200019540080e100000060608065959071180104181030030451540c0d414501815000300441807400580291400d000307607561019071b41c80702c2c02e032600e40d403c900c0fa400d400c1c0e80c804c0045450040c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 652735341 1250 652734091 652734107
    0x80a0506010509132903100905030d0501063c08101a0a1707080402061b0d121407050904020d0e01050f0907080111030c1602030609060123060406 64
    0xe4141801402c001540c0b00250300440c0342610201043d449035007940d00c0f410301d145052680703290740c90051148040b500c00309503108402e080544503580c481082005118040c41140e403d0f928500c03040c001c0d076031645000b4190204001c41b42c405103500b00038001d40701d000b481c041740c03406040805406191001000440e5035444c05041a0a4929100c0c00018040060a42407078400900110b00c0d8844c40722000207400741302e0714001c480690000c070003080078860340a07040d1a0300c6907040b42e91a86039090362854016110840d02e691441c0c0c80790a40802049401a941076040c1044203010f101090749043e240d0304112082e640c881c081071040c01281c04502d003d401808000e59159030010300302400c041d059007980c101ba129442c10705070b0340c02805a0024240100c801501c2200001d209400100c80003c1e1184001070a07003c4800d0082800f003601c410042c0701c230061070740040840b8020b00f003a40005444460a00c501146600700c1d6081091a24034103a174041040402410903042528041054810340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 652736591 1250 652735341 652735351
    0x604031d0303090a140406050a030c292b020702011d220203010816300f060c030c110c0405100510020307020a050f0906101115150a06080a05 62
    0x4081030101031815220703003000000418074892140c25810240c406e00089a00c00d4100501642803508140b0112b151008004201c8000249a1016550a40000d4007030b40f41518007456a1100003592010200c00e000546140e405403010700d02d0320004107122004038800c40720000c1c0840e0307000f00c00c4114022044000320b400c1c3c8026000c1c1da0540012440500740b445801a04000168084014000d0312002c01c96190031800b245010240c5c42d0070221040304451200c440a0900d020004454581c646140900e641c042d034040e00c00034011040d440c00744050b2460300c00300c400203440d241382c4003082c0707125580c550810400e150207490802400c0301804064540200005149403000b400010030361100b070781c04288082a90f000c0d60312442284100312060400e940500d10500d4040002c02c0e26584c0d11140035049070040b569001c1201c0350300c40981d4408201c0340440014060000e9040c0103004d007a0b11903200f51403a400c10300c00b401020040120400c894010f480020351180d0003e84200d0f04d42d0710141e004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 652737841 1250 652736591 652736593
    0x5011223100608061911040b160b07020a110a06170402061e07060501140609040c0c05030a0302090906040e0307030513030206030106032c030d0b040212010308030402120604031d03 79
    0x8018024840d5041c0c540303d92010583c0c0e4400b0040082c486402906402203524030042030056158000f420703151801140604911080002404c1645141c0307030307c04204039940091944480d103007201020b274403510381c110140c651030721001010701c1c2c0c1c0c070b00b02c0c1101702540c2881d240c0302c010500c148282044941c008004981005040100c0301d250200807035072860108003500081c0e514440b915244050b10010b03809440105448a480501c80c7d172400103480c0a000c041d0740010b0307904041d102c100c40103125003d010f48107000c0040e4a1030142d0741900286080c0606036007191a5031204004e00c0f08450a40300d10007030640052080c800021301c0351000380303005841a10604503403501ca03000540c1903442a8030040129039511100445264507010062562600c100204201c05030107242e0b58a1b84580a80f2642990b61140803c445039115819500d506ca420782d9106180d41e128909801c0544c0103440580c855500d229280389105000240e86224640c13550301c1d8604104101c03240f22501d241148001c1d49 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 652739091 1250 652737841 652737853
    0x21f02040b1b0f0a0f080306030313061101060f0e0103020409141b0103051f05010f03060f031506120f1101030216050c120a08031f03020d080a020105011223 69
    0x2070348296005841640c140d40410a0403030b80200c041031504410300e00c0c54007242c1001010304007141c0c06001e202901500015159a66901d00d40024114030400c1400d01d01c21102e0240030078181c2d030103e641070454403110020028940c4403894103080b245507100703203902042d00c00010310045c241030708980c910500c600c4615003005d41c164070725420000440f50b510302c11038490180d110950307031502482d90803903c072454201030355101400c00c615650060040d241403180307a4540101540c802d92200c0000c144d50006001c1035030b141e00e00900c0452020800c80d980c0c505100c8041a1046900e07902c1a0391903100d110400701e122036540711780140b4030300b8203014149a030a03c42405401131314100303240b59074402c60250040012050400543d5000d0b040615032643c0b010a4500006840b0340407660020080000c184401c500851641c417001601c1d04020b40100400041e08100418003001c0e01a2200e0b6030004d22182c1c5c0c803488c00850543d01d840001d0f0081e4010040c00c03a800102c030302c400d58404044029121 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 652740341 1250 652739091 652739099
    0x60e070603111e0c0d030902090609070c1103210706060605030105030a060b030a06060b0c0114060f010305060a03120807021516031820010e0603070801030b090705040c05030a1b021f0204 82
    0x20500145c040c1a002098030b4030b0403e011464540d07407150780090210751840352414401c400620148500c1070050a036000c115502200366820080285145c2ea46201c0c84a0641000f0504003980c0109004840e02c2c0d09109000c030f0b40d02e02a2003564140c0344060000c05007448180c4dd480c01500d8020721840e0540110822500071901a0041d6005040040641c40c0d403624624207507400c540249a161030751094000501080d5a181d1483c03030381c00c80c2d091070b011a094032a40b00003000150940d000070400341d0b410714040c1d042c94002202610950309502076410700c42c0818084000c0d16011681058135a41520450401d01d000e030744500031040000700b200c030b14102656603c40c1400040c1d20f0301e88801102c40720107080743d0b0b8044608030344400283c078100d05504040601510200d03040c003008001804481c00629088010882c10b07006200080040c0281050039001522a03402968003598142c240a10b0885164a415002e01e003521142d0007000081c0540e01028960700400c064250015000c000020b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 652741591 1250 652740341 652740343
    0x1b080403210215040b1315060e040b01060206070203030109020d0e060901020d0606090311040c121803030608060603100b01090504060b0a0207061806050304021c060e070603111e0c 79
    0x700c0104150054100c20550000c02a18007a600603100c0200f8008104100019125504d11038200c0d400096401407040145030400480320314503d50040240380a100042d401d5415410501480c0110720303c0d80300c2e90300c940c400c9072582401c541160259108000400c06950103900510407810304e100005802c0020381041410140300740d51091441e0340119120fa190f0a031031240d80014031040c00d01c200036500e50b54070070784102c5146000500c240c2e694041100918068a103411000381201c0d0200071002826504168105102c40c0039000249407090200c1c0c105800240f0b036000e0b050046c010401a41c00340e0079400034003803444401c0c3c100103200b600000d1513244d601401018080444ca41e944406103103a00034035240c0380e42e000804024900401071819041800500c09540240c0381407a43c0e40e4460000c10403405203952a070342001051401e160a01100f50b2065003100c585000f580d0009545040490070b035405990000054202000295080601d030541030103940040800700341400c04d40e002031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 652742841 1250 652741591 652741613
    0x30c0702120c0102010f14060402131208030f060409020d0f1103031b0d030612030f051c051b0c0d0e031c050d050907120803070311030c0a0e0604061b080403 69
    0xc041c1c0e56000c00b01c034018540c0c080c0105800c42000700010003824401840c1142100c00180c03c950086500040d00a102640c54400d0f6000d4641d03005042203004007482c0190f42c50340121a1001030008000218101d8a4240140c0c2034294004010208440031512031003c01c0c800000101d91800d61403210f20b0700d80e10103101410900c841e40640c07503010301c0072010760340c284210b45800c40201131501c14140b0110a07107101404840381c252038003030404010900165000d1195008044d9240c070f11000c0070608464079088a0300c0f801c08451201c9800c00300062800250052420f070074001d401182e06503007401d03c102d200280c0241c0041c1200c05c1504002c0c649101c903881412118001500015400145080c500600d0741058404005000040c80e00184140002c4800d400504540000021032040c134483d803c0311000300005220140c2d00e04000403600c5980d4822003c2401180005d6041e40ca035103488010b440032510591900742d40004c031030078001003200f882c850446040300e0034000403010034288410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 652744091 1250 652742841 652742869
    0x30408280c060e0f030301030b2e030501151a0705010f05090a0314040303231b0d1205190504020d080d050f090a052505091006180305030a05030c0702 66
    0x10115524414200641035482000303d03090705520406101341c01050000840741140d130000b01000c056100d418110442214505051085103602401c0c2c681941c451026803044038807a00c001c0200d640800309240401d100380c4030341050181241c0c030801c0f00d08054401086114842d0000058000301085000c0464000361a1011580d009000305030806800c5000050403100700300c4d1060405145039001810b8a4200d030310102550302c912008480d100315603060342c1c954291071154241e00b41d520300c00150b6613442c1c600b940c00025405400300740d05580500c02c040c042d064010301000700101d65000318000c0c01005c0d104981200f0340d003020300c1c0410b102030050040504a0342011074182400270b03468040800181502c0341d00c1d000410100001070300040e8001c000b030700360750400382300c03002940350107202c09071a61105401078044000c000c42c030001442c0d400281c0e8801d480307500704a41c1c10150104100380d54080200641c2c001c0001510303040c000c40243d5480010001010b290910560200f1040391035008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 652745341 1250 652744091 652744097
    0x3070606031a011a160f1505101406220f0f050411030703090c09060f08010c050a020318040f09060504050c3001060b16050c03011103040828 62
    0x360920800050001590426504076420801e9505150408a581030003100428642e40001820169840c819401d41e108a8014017034070307440321703842c20700000b04c140c217031071041c8050700d004005464000d03100c403540f0641d4400508641c440da00700091081c20340c004442c840003a6641d813014414414181c05100140c2a03040b5660002890042001ea4101ca581c20040c402e50400c0d03250590b1401074401c3c0e950050041c035003c5041c1c0c009081000c80900c5503004035081a042c5200171640c001040c218108031070680000300640600d200085501e40108003c100041c2c104012914035100d0051018410306070041c00084c0c15106150307444c04541003080c0440d0741d19100c48c200720500009201d405021001901c03600d81c10611360f92414188071941c1e00441e40140082c9800426050952107c005010001300d025590341009814042c2190800c0044072a445010004041810103000c0c504c4a0000011801d0071500c495641c20280e030001e00b20041603000400f5001c04502090360905c40000940c1c0f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 652746591 1250 652745341 652745351
    0x5120703031103090904030c050d03020313060213052808030901020d11030c1006050108060f030c15090901030f15111611030a03051b07080a110a030f0515070f1d060903030706 77
    0x129255041a2ba901650070905105104125901300c01c03882c50354520f90710100042e9a440911401c48405d070050700000d0f00b18200a450980b000a00a007488000c3c0001c0b10803c3e03460703910403d0561740e10130000c402d40140c020001400100c1d009030740c1416001509410760f8200201100410300d004010088410040e4a80100b0807465070003044a40c2c00c040d007998140342d001444000311340c1d9940308200311401803030440d080c2e001a4107440242e0b01c1c0194001d0110300305580d24106200031024581c0165440ca00c000c400451100c141d02c504e080180300495818200582d44000144031100e90000351004a41512000820b6805001411810b4481e44601e500c0f150744030841075000c0100c0070b9862030741e80221010302119800041031204294071800b000c140b5250000400c40307d600c650300c01801c02c092900041c1c2042000b040d00200c41c8a901c41c0c10309a9990050200c038008007004140c40480c60040c085140a10300d04c0700803081080207070060386006441c0c1c3c00319155510070360003910303c10750724 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 652747841 1250 652746591 652746593
    0x30c0c08070804150e1e01200604020325051504030803161805010905040b060c07060e090c03010302010c3507110901030c06030e07170d030605120703031103090904030c 74
    0x21915194804c01502c1c000c90a025103d010a0018411004140d4492814421003006038418481c9a001e65070419020b00307000440c406250303a03003409883c03c038424040c600d904110300d8507901110f03042160211011420f9464030781070044440701d500b15524886805c01c8040013103000940114050803416070300b100c0d07840c6001c50007810480080364502403906002c2042180d030303030b01071964001d940c021030340019072418603030020380c86200c3d002c090b40c1107024100c00060a0360b00011200c50650041d9410f071981c1e03982da14032440134802400002c0c08642002d210703601040520344010391100d0303006440d45205007416683d040c1c0082c0780d4007100a1000010703049042240c0e48043e50300c00380007130f10078074950750441d034642c00506010f0240008040d9141205541d4800421905c0000c0c20716280840d0188403081800c2d0f1140c2a05442e0701c0802e041450008840c100551109100c9209070050f01e4014111350301103800b80c507a4940c9403501e02c002c0c0b210b11842c0e030700e03103001034007c610a48030f0240002c1c2c2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 652749091 1250 652747841 652747859
    0x1703090601060810230301140702460b28052712030c0301030b060d030914060d0c0801170606130e0f01050a0203011409010510030c0c08070804 63
    0x416003084003000500d41c2070080e159004d00580081d07805a0261200000743d0f00d03884c07025100b40c1c1c101c45a1560034105080380504000d000309004002e181d00345e81141d041c0ba854502c2c1108003444102c4418403618441304030b46904038103940d0031025001940c0e0f40769115100c24101481c203075241e01a402c2d070a50640c1c118401c4020480820300052070a0041e443d000c200c00600d0368011081707480d01204e400e55188895405d0000e41400c50920880f540c0b40e0800865031100c54200340801c4079103040d00408200705140501807001500c2c4d02d0754642200743c1c245a15410340800e01a03a49030131040c00d0280711071601c030b2405441c041c580c041d0750340f00c9250716003040c2424000409000416940141c41401103d8542c1d03a44001c101ca0312540200e00550301e11303895440c207440d40c1c0044049508c1c080500601d100c0680045049543e0f481d00c6014800484040081d004420320881c0e41c416801400e00001074040c1d04040412092810400740041c260f0b04c900c2d040d9803240030221200c0c84006401d20820003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 652750341 1250 652749091 652749103
    0x9050102090414041a19050406020a080a0e1f0212010312140a0e0f060f270406080c0906061204030c0204050a0e030306130b03030a0519030207020a0b030405010603170309 75
    0x180c3d80c0000c0d810140c880c88040c0d149404a0303028610707102d0000380480710b02c01d100d911030040060100000d00e01403e01c90000e420000d079107070020310303640e001c15004080c50007501c43e500c620001409203100c0c25060401e00c442c8050020780540e409112020404c0500a2402c1c025400340c1051a41802408401440d0b075204003105803a0840c240f1890580c2075000c82088030001c400d40f1504041051350001031402c0c0101c540c207281070400007515404841c0690f1000c0000c0340c1c88074496490140c0704013048240d8146000c1e81010350300226085031640b4000031070503000326015085c54902081019143e804c0901180d00b900414130b011203d901314100762107610303071014103208204280644000c000b6107031b200281c501c51040810102c80d441c491600c0d4041c01c5061001001c030381d600c0d030140748080c0040d0070907070021520300c45071010b00240b54084c0c001c5a0100e0f41c01418007214904004840b9001e0700b01800559081d940c640021001490325220790102410f2080d10980300e240071200c80745005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 652751591 1250 652750341 652750361
    0x70b13050f09010f06050f0d0e0c0102070830220e01080a020a0611010b09070f030f0204080715090f0e0609060307060e01050d0b180f15010c030819090501020904 71
    0x10ba20040104103d0101c101c03448181d8403149840d681c0d43c40164100811800340d030f9840d10b1000c3c5400c4441c1c495440000d04015407020030713003e0b551800d544058407501c6424581035150020505980c81104109410081201602020000e801e25800340520942210500c0c210101480400c000b031000040c200c0001c0e004280b004000e1944420b10ba02043c50046180305404c20300002100303581d0110003c0d004102c91850150107141c0b0b516107500f0083c40c1c002c103004100c002c030b40b801c0c0790682d0300301d818001c0328152007401004000031440c02c130003510f030103500e401c040080207504640456980e19000100006007c1409070030300c1802d159041003d00d83c03002d02b529101c2d40c458501000300c5074000c0c50700001d01d442401d1040e1150030f0070030b1410141c4104603603942e01291031029000c014400c42242805261401d130079030382c56034600c0e08040f0054500d03081140442e2801c2c801d040042d2252059540c407a501081d40c0f4030104040307041a00351620120119000c1c3d4010800c0440c5042520840340d40c2d07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 652752841 1250 652751591 652751599
    0xf0501080714100807030902040c080a0b18130804031509020a120c09021e04180c0906080a0c0909181101020304030b0103020f060f03070305010305010b30070b13050f 73
    0x3800011000603c407000e00c01501080c0302101c1d00140c00c10740641c0c8511031254026100780004105c0440060000c04200d50305840a0301e420803540c800c0c140b0440c04184100ca07058884d11588602c4d180e280214075000d000c41c0c2d001d00c1048040009241320404001c40f0040c8000803d4008107441004514407040d084040d0011070304420f40041500002c55404842d1940d42c0142d4509882c06121074401d140c0d681d5991507080082d000603400c2e0342c8051107844904901040204880314401154142c41d6031141100213030030384011840742c00c81c1d680048802d440c17500300840f800d07988246080590340821a04040e0b480c0b489014024400b03c40404e591100d82403001e185081e0039540c4041c242101800041d01172200c001c45c0700400e4480d4030488415a955240058036407038542c000802520007400201c540d94200400312100d800c04a480980c210540041310748101c024180e10f01e07052164051240052081010002c4d003054010b000b4104082c885a41c4264035082c141444189540d0700049802 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 652754091 1250 652752841 652752869
    0x218030a0c0e060d030f031e090305070204050603060f07080705040317190806060f071506030f14030f0706240b041706010b0406050d0209060d020304110f0603070c0c090f05010807 79
    0x7031b485103010000404504000400700e02d41b49160703c498070f44148001e01c60f8542a412001d258000002d440d1040c4220343c1400142c0c0c5100903d510342409507401155050040c005c07880321800756800c11341c04210381ca003190515549807184240e020380b00e4107080d64040e00151083c021420842d4040da103000364101002d507410864003064281c41010320204100c01d011844900b000304214409120240e8088240446070301c0b81015000782c40300d14422a0740101600502c4861400130069442884800b880c1c00d04001c0192500805440706800914501d094204100040c2c000c01c002c560217001d40c0c04041e038039142000100c52100b42e108036008410341c17003440100500818881150b044c0d40082c985a0f4403460f032001c000010f030141d108140d40c40030010440800c00b8215a014605c1203010b08507040f0f10000e4201404581e05120300b541d13030041c3c400c10000c0d14090090032400d14240c800d0b0f0b503040d0559500d02074030040381d00c01820b40031155180d0f4010040440208004805402c03603603c9014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 652755341 1250 652754091 652754093
    0x15150103091e050f0d080610020c0906010503281b0318030c080f1c05390d05040f030807080c040e0a06090f06061b05060103060218030a0c0e060d 64
    0x2160b452100c1c1c1c500c120b0040407100c1c4204581842592000c0e8842c20455541c8044c201000e00940000c0b5402400351250b842115001c0d0700c001206080104042c0c02d1401549911004488550008107624003000c00003100b06c0301013007200c120810311403a003980080d40008201c044c2c5400758215100c8400c16013062408141e101c11260004207255041c00c1142c0f2005d4645880c1400d405813000f195a00340000c00d10345103041c0454261640c86180030020081541c40b030b0034811040070300a072030946484040070b2660100488001005542c00802a81030804030507960120594404583c122492941c0405100825821510b8160800005d040141a61a1500c10040f2a005601c90b001c4140c003c000460b202c120954070007006002c030410140002031070801e014000d04000c0c810840040c510420b040c0a201042c242c010f295a8404060b02c11030b4a141c075044060b41080a07000843c4d00550301c00300150790100a4441c5651143c2e001c0b40ba070500e00701043d003030b0501c002c15090094141c0002d83d8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 652756591 1250 652755341 652755353
    0x7090b0a120908210a0c050f0c21090405010911180307050d0f1407051507021504080a1208090c0103051b070b04052e0914010f0b1c0201091203111515010309 69
    0xa50552158a0323083d11825203c1c1660f00e020179000c1d0401d1131303400c0e414082a51681c010003c001503e000e07903080c0204c0e641d85c60b01d4801c941d0b0078110602c008806201020a070f04140300c5215110f00000c003290441d6403680001050a10498005c440094224003010104044200c454003417075030343c8019142403450b20002c520300408003c9000d15080c4001105811940c0f54402002e44280f04035806842d552546451075032086038050669101210354007400825209404040c0b2480c260b0f0050701003016040011340c0505006009840d40869050f07900b8640c0414001501009000d050894505e00b03107401d08600703020b4401508031106818080a2101003822080d0b0b040810300e0040005c1c44490a080403000c001e01c0045540755075003840095440010340c0c0d0018a00510200d807240c11030284d0840716003000600b801c00901044440700c0030080a00c7d442c0c3d1051902d4000d080500da0801407010b400e0070180c642407820740703401000b000d100000b1204120000c40403000c0c00e081090072401d0b103e00d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 652757841 1250 652756591 652756597
    0x1c03180b070c1509032006070e010309060609090f26090f01020f0f0c12030408061f0f03030203071101031406041d07090c0807090b0a120908210a0c05 66
    0x1150501101c800d0700b0040000259801800400f1a03c003040740400038540104254118150601010100c2a0a40c816007020604a015640d0358803002084059940150302078240d20f0000d40b0060364030100041c00f0040c0e4003c0714a854490040421a46820729000c1c00f0008485203d000301602140c45030080e500c94812900c01c20402c44d4501080700400340100e1400c98040396580c114014620103c42ca0f01c0d000039050f000c2e09045a966a41207604000b0641d24003640c4103007101ea502c54004208030010a1600c49c486481c0000f44940e01030329102c4c80100807600d0b5204600507800064180d00b8005151105485001e09181c2030242c440b08040d44550404007502c0540300c0c603504d80402d00c04a9100c51000400c0036000103440d1540c4d514003109000700605544100803d07121400607451343e1045140c0820b84078040c59507030038240340c000c4c212a00d070400c1081e415403d41e01c55108010a240f18054043c900342c840d039420703003a035014000400001003d40f400400c6420301314030307042c2030343c100040d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 652759091 1250 652757841 652757851
    0x50a08060145060806130305071209120503040f0504110d0b010302041e05090108010203070f0f05090904060c0201270201050d060302041e0b1e0904141c03180b 70
    0xb91014100b090812614110420300c1001c80400060780c078942141100d4000c0011124018180c40090340c581c0c4c0b0396a07951070100001000940708200c1d80000400701841d0003408001c80c42d001104503120004402c0d844003130402590325500202e0100014140501e0306406090192028411801254501403540c01105031030102c45803580c20740381c00760344a90705840040034809810381404402c00001103c12072540501070080d01000d001080310f00d014001c40c0c0c01443c5a589241c1c0320640c950041328109a801519001c00c01d0401041c071040d901c84c02d049004600450000035070010f01540a42100c0002c82045259924901d14510010b03901c840c0044030fa03020f092059882c150000072400030101c54000039440361500d5032403200070100c081c40c4101d44800b40c0e400c0090741c45d02001c00c00341924081401c61031a0030706614000030704242d25244d41107031080d1001211203100700300701400c060203080c1400c56040001c004103c903907890300503190021003030030759104c070782c240c50701c0f50740c0c8550300204 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 652760341 1250 652759091 652759139
    0x1150b030910051021210905031002030108011a0a06110c060a0807090905060d081803100e0d05120a110f0a02060105040e0c03060a0b01030e010e030301050a080601 72
    0x200181c09084140800055866065010022890040c01603000100386024440081c01c0840750b0142104405d4942400315070000c070420b0b505055014445034004018454808000d00c0c9000052651420000c51003040081c2030f0150300c17913050010840c01c466030107550480c00c0382d0351504403129446c2c4640c49401d0350018030380060740c0c0072141c10080c03800042c0c20515800003800030301004c3d8103601205440c05042241d960302c407215940c5900d40d0036200c050b101180e100c0c403004441c0300001e0a5000401c0314048500262220001010029007090f07817120500c07800f60303103c04901d03041c0081480420b140040506182d82005e4a41490054031000203100380c2045603600190200700b9000425a00140112003519071f40301060f10000b5241e981c00c0c4900c600503414014030314880c8c04042014a500300000e002044150398808141015101c2441c3e000c0c14160303500d400005200d030a00490304e80305100c0c4010356495140c2410f0003949203c031790110780543c11400050084890f0380b40d280d0000c1d40050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 652761591 1250 652760341 652760347
    0x60e06010f0c030809010b1504090b1f08270601090b0301091a040302030f130f0b1206010311130e04020f10020d050c0709051801060512030a05030c0c03030f040c050301150b 76
    0x500d502d00501421040b140c0c07040c500c821100c00110608c00401c01d80c0d00604040c8884140c05c0203200c41d00d248030300760540703240840c500343c20000d00c80d243c016841124030b1850b5045035681e0011071401c081411790400d0719003141d4014400521140100210380380154003c2100d005079440b1140c0041c2040c05510b080100100400c090510800603a9071640341c44420942d2400010382e280c402c084140b0610240086219000074903160a2003070321080055181c90310b2641c0d07107181c0118001e0442c1241e58030000014030802c8139030202e0701700c07190141c9402c11030340340c46080a0041044845001e00d010b07104d612180d40d405016a404900e54444010f107040580e1904035070022141070000c41d42205880d1450441045841c070364040129950080c940003c02c0041d40342c400f4000c03165508091204603500400203079a04e140305030000e546c042030074038032203040070020000700e829507000703968203c00c80482070240001e01c48109065002800d00710000c00116680f28803403c40d040c5c1c1c600c03a03050320134404 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 652762841 1250 652761591 652761601
    0x506012718061113050d0f080903070f41150d150509090106030c050f060d0908091906080a020304050a0c1502120f0d0c050f04030303060e06010f0c0308 67
    0x41100000440c2d00040034040382059550b0b000c1640c004031019030002c00c140b8000580d03400c0c40c5160400b89508141902e04070080da444102c601e620521207207805210300c46c1c001620001e500c0d8600f02508250705604c61800c081c42102c42449160003000840e8000013000156182d10301c1c411040c44c00707043e101020780c6908070045c1c882501603001c10303215450600554200c44a151485401a0358044030300c100c141e146e05d00880e003220000d000040200e541c400c800d1009107800000540ca00400034041440c01031142280411347d05010001c89081d8004160706c22a89030440034501a16001c2e101500030364a04980200300d81e802514803070b84a81d000000c10300748034050000d00030050b082038000c04050303542ca5044401d40d508200010060041c40e441030760140000c000c80d8071070f002c0100702c0fa05202090404c0c83c010300b44042190180002000b00b1404907034880c02800013540262000218189440040c0741848030041c0400d042020f0b0160138458542c100401000141c0c00d0b1425869550351 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 652764091 1250 652762841 652762871
    0x70303140d020705160e0601091403031e0426100b0f03060708011a0c1e0f0601080c03010b0402270411041e0e0421020102041a0705060127 61
    0x741c4400c90107418000510041808000501c2c03621801d88244140c0da000d0f99000c201a20001c01d64a15002030701a407010440521500f10005d6400e0f401015a1303e0300413200381100900452080280c40c012020408001d0300020580140c009080100b0078010b4090581510792a95600741008640035a114079290103902d0b8074041ca080c0388009000c4400d01c0c186481d0260001800344101000354001003c000203104030b880130390f041076407030000600c032156440461500c410b00d800c07507401561207110420410043c0c100400c178000d200d2030000d07240d0654107009040c02d450050a246004600401204140ca00d00120700300319486003110719090301c0140000200a045200e2104440040104010030442400e0f5580c0810343c60300300034841a95034070280160104e00031036002e461a5024450f100400d8040e810207000340059100042c0f030b09031200900c143c002060f41015091a101041480030404200062405410080340c503400c1e1900407105035402d41074180c0702a00076501c80d040380c07201000d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 652765341 1250 652764091 652764097
    0x4060f1803030b0a0605090d02061e070b0106090e0f0a0507030f06080322120f0f0c060504080d03140105150c062e0308070305220303020d1d0307030314 67
    0x140c0d0580d8a02101d0400070058002400c050344a480c000000103802030080c0212190850080d000c008059055020050250408116510480c4040803c9044403500030010402a1720502c4185015410544010890440c2d41c10100300940340c0d07018801d1a002e04400b16030720a0094801143c0c982c0c8010b01100600410007103c1d24039130034460041849400800035200340c0750f480c01d00880307500c2d1102803000b01e68401d1041514446031061000041804100007650460192a5402c1c40c2c0c6419a605059280580d00400010f20042000c1c00182c00c24840c8038008003a910b400e2009189044502844280c1841002e1003003c1c40d00040c0703421a051019504504101015201146047e0300710348030b0000d034403502801110340207443c150700c40660f1925409680c0c0081c4084e0070040240d905940940c404005050002c25410f0b03d960360504069804014511940c00b0344108590310714090300d641301000a5905400d420450280180c400240d84000c070f1f80c261608040d5110001d0003550588 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 652766591 1250 652765341 652765361
    0x12051009050304060219170313080c031c0c080c0904060906080d030b01090b03070309060e0a06090201090821030c040e0c04050a15050313170a030905060f0f04060f 72
    0x1410300c0940000c0c440e011010b0400c449582c0c080d9007403003480c460402c1c4400c00700140100200380d40745088a2086101020b5a0311440402e089190445035031220726260708200404211a13000241c03044540c43c0f58500907504c1c170703030160003031042c4030050704054040d04000f080d003030a100d400700c0c20300b10310ba03500d1b00700740010140c144040200716160200140c446281c03c84420109040111021955120305102e0084038a8400718078110385422104402428180c0415a00c042d180d82004014a2041c803040304001e100b5400020001c400780300241c204901684040034681080581c0300c207911008020f0300d04540310000e1659a03640d06e11040180b030156420140481e1228001c01c060068428000d10a1307403011030340105200ea45591000003801c0700712904002078814004900e0001e024540046c0184c82401500444032070042a070605403c40c1000ac4000ba4a80440d0800c3c4201840007a41101142d19010b0305450100c01400807207502034001011301d80d40b40315526036000d090784107036041 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 652767841 1250 652766591 652766623
    0x6031606090305070609080709020d1b020d080114030a030509040212011e150905060a0e10091a0309190f08031303020607020c01121509110403051207020306011205 72
    0x2054888800400c0740040d804100c68034403a0030f6000c0b80840c054036640c02100c8101006000541c20116007402039007080b11004581ca0316003030710300955000035443c984900e100340e00818500032844d40c02041c0540607440035a1000300150f2501c001c3e100800d4046416805042580d515424000854001d100e260600a100c0d0801c0d000800d541000488901d10000840c18180f0420303203424180c00e50100d0f00070441c0202d1003c0b00108024101f207000b9000700d00080c00e05241c00c034890070108200c000c0c240014000104100e03402d00003c80d140d41c04d604050040341c801811407070408403850390341410850100c2d04c00c4501c00b81208201071b0000c0c0e58402c5a02220741d580f01e0038034001084801c7c080300c10840250080b440000c036010320000d034040030804160b42e4a040c444941140c030009004441da55000991100804035648040703000d8052070700c0d0003240b40b0340d840303185040c1541040c2ca51005210020020051500980c0c1e0002d000c5054400c110200550239849183c00d80c90841140c0ba1400a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 652769091 1250 652767841 652767883
    0xa09020f04030f050120190c0302010e070b0c1b060d150f03080306010e18010b0c0c0415030b06220506120a050106060810060c06240b0705011d10050603 67
    0xb0860190007091040001c6030600c901c20300451507002e1b46020b00f00d100341d02c0031b64681c0c1c072211003032040c402190308500900001443e04010720308a401c02440c3d400c516102c4100041850f40000100294014000f0680b14001800501c10000b441c62044d500d00d107466075111560041084004035241c0d009145c2014102d04840d0b40780307231040c55a002141c100d400322350b200140d0141820325181071402c80000c4080307010203a00b0318400400740c0d0415058103070207201c0c0042c030103520784880c441c2e013054030301c040c00c0c46c0400ca02c1c510380b0b0030703a244006000900801d080351103907070070a81d0200c48000e1280b1481e0042038550390040868488400804400701a00ca00b0140c801807100641c07020b81502d1507a5504a840e66400710340c0c0231002c000e44100e00000340304240d94000b040b001d5100f0b071a8415030399007445111100c00c4403411404959008503c4045002401c0820030800b40700c0c2804083c81e240610080095240b51301d502c40c144c100c0544049600e5400144441c1d03420710200840d05d4a00e03072203500b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 652770341 1250 652769091 652769093
    0x6020d1b020118030f02040f0605010206131b120506090c0922020d0813081f1a18090c0d020a06030e07091b08130c0320090403030b130b0a09020f04030f 67
    0x105ca07086210240e010303920704004002d44043d02c0c02920305441040e002444549c451060800b554a41d072901a900d070550095625101c10744001800000c040b508c2a04410b210103080c001c2c00c00c071025046d225141d001000d0440c00e40c9a100540303601c031100300020b0304c064641042e80c80080180340c1000b98030000012800040007031240c09812122500b280c010420390329509420340c1d88420100300082c0c00380fa0701d91018641d078507030401c0110405040c8403c580b078509030b01240041110a01d001001070f254800c0040a80080108048a10040342c5c0f6458005058010070044455409070b9800c150303c0e07031a1204249410801c010040c51009410080a14910700c1105058031810300a800168007c0106803901c0ca001006c030702894101807032001c081d24654503140030418180c1e50868280326001d001225070768098100f03125600a85022074a0498181048801c01650002d880c1262901822000c0368580c0c40c181d100380c0707000c42e40060b901d11280ca001c08640c011a4002052108500940d030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 652771591 1250 652770341 652770353
    0x1506060e310e0d08010f1a040902040308030f0a0c09032d080901090e060f09040c0e0a021806120103030311070501020f0d11030f040f15050a0902030706020d1b02011803 74
    0x31501481e1001a65039505500c1011a16040e080c41030140c13060350b03e042030051f6030303891071032540d0f0310300100010f49003e5861461809a800542c0250350040001c0b080001c10710f80704d065154030002d80131040011083c0954007504030300c50340c00007420b85002500000e08000f82a0359010104100b10340036048a5150b1134203140c2c9ea84203c21103400981e4100001400410405c030090144034010701c00c040b0340d201c00050020005004205507980780c020709002034001c44050f15503000c0d5050710700141e81d86000d15484c260407050f580341180210410001280003080460103d0705680e41880c0200b524000601082014024104064025440000d030100140c1c0c1140040034807148921090060803054545074146001c11079400b0880c3c40800005000a401e1011070007902748102c6008000d909205000d40c11604200c1d11014525610007610040d407408100903001007040e84001c2c14020303000b140007482d9444203284041028464042103045a010744061260410b042c076411104580c1c9003424 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 652772841 1250 652771591 652771601
    0x1905160306290a030b0604030c030c060516140c060a030e0d03200a031503060b0f030606010c02012d050a08010b12130c051c1506060e31 60
    0x64020070714007100054161015114400c08140e10040d240a58040311580322190307001000020030107607145807483c4c03650750303c0001c0c10103140540800035409003149406000c2900e19044802030090500121080d01c801041003111154080311606101c40d031302003c01d10b0b19041c40201d0790b0004000c15048259949503201d0705607045500101c4140c0c4244e2039040d0304403008105103a903503104148000c60072002907001050415854a800151000010b000c0310341c81c001904110399450321418620030300d150031450842c600c0821400381c1810300300340e00041e15100f840d03180203040c41005201034180e210b4881017401821040030742a49801c0f020b0500608641c41001e0b10408141e01d0348c004100c4030004400e95580d61540c02c00081c0c1034480351400c030300c8400d59000c00c640458040c400880c1503143c0e001c040c660665408411201c182c103928100ea1010340c081a11494140f030800100300440d402000b081c4822015103103105441c40644101c1101c0c640c1c4441d05150a0701800741c0803018800e41c0c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 652774091 1250 652772841 652772881
    0x5150a0c0818150408120406090318050a170c0d12080108030a1403151f17041112100e1506060a020d0f0507050f070911030415051905 59
    0x22580103550301d040b59540d003560140440a5680b20482d43c0010065443c009900a4061103e450610040201c0c5000413030f803c0700c08546407a15440c054042540259461401d10b04c4424200c0201e8208400b240250151f0302c5003000d0182c00112014880c481030094841e260b2000e03110350100310031402c05440d0f800201e010000007c80d50700000810000100c19114000101d07a5288905044061040348a8201600cac1e1350740301d101b44c1515200759480600c0c03c034400703a03800c0040c603181c0050300c009003100c44058188a01c561895040000158407060401c0d20300c03100b250380c80d415803036800000340751013030116100e00070700e10b0004000c511810001d1126032501c100040743e0041d590304800d000b918094040542c02680c0100c0714602c0b000d000d941c0722000c030100b614045013440e01548420789048500c1241a503603800103042070110720228003c8442d10400707803003580e145051a50b03c00d01d80030000711014500e569a4004075000e101142d40b20600e41c0b900103800d001501300038000004045503410 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 652775341 1250 652774091 652774097
    0x603080c0d021902040207030e12070602120703120504170d0504060501060309030c060e0316061d0f100207081306120c110a1b0305060f010801110301150c05150a0c 72
    0x940750701c881d1001034007403018100e200b00400c16010700c0e420b0001075040410304405129521010051503204c1007005540942c20388003c0c1151460701c00068104a6110746040285c93301300311020100740c101d40784102040c03200900140c0d03540c503030030481520351402014201a210009405c40c1d1844580c1180303001d02d008444c00c00140e6a90740f4150111185543c0050205581c40528000700d2120b5001107505101c100c26203103084c00c3d8000b10a4a2544020110f561750750305c46600c4100c0c410300b1f40d44030502d00b070b8100a040c0c8045a682c02d41d90707120080c1640100316000901001003210460544280b00501070301c0400c1e4a0721802c2c0a06050a1b050031443d00c189001041d0700c0651003048400c6100c02e00c00d01408000640c3c0d280d40201d0301108100c01c50b16801100d0000000f40c08210180c070440a0451504165050044050075501c040f0386548010200303000501120041c0c0452040b20080313030800e002d941c0640c0c9400da06000200c081084031200f46401c2085241c2c06070009204002030395 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 652776591 1250 652775341 652775353
    0x308060406030b060d1109100801060e0622020f0d0903020606041415040b090703060816030c0509180a080a031512020904021f0e090a0b100f050d0603080c 68
    0x12003440211580342c8030240c2500ba0342070224119041c544190202c09006500da2054105e13a0808164101010750710b401d144a00c2107010001401c0030b2040d50050645040104030034100300c00000d001c0c446a114195003001e0700480f0304a6400c0e1030f8101c4ad2429402c0002a1710b80d01c0b48141500207100d401d00c1500940139807000240d540c6082e21070340d500048009058000368441c80400e100c20b03403100d04408d40080e80d800801c00556500c610440c030170a51075902007109400c0c45c082900300340f4140d00d111103043e2442e509100007080400e540040e108251181240ea0f91000c03825464101541395100a80c00f620040381c0500440c40c000303001200311603c0c00c0c030501a110410180c0b980c43d0703114454001d1070600500c001880d01800c0c035034015000402c0c0907141491595410321035000c0c0d40c1c1034008a0514000c107806400c2520103540d0213032440604000c2d1425000208800c070348024244010480703121203039030145004100343c91081c145508200b010030384030b140204032540192540e4903e48540 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 652777841 1250 652776591 652776601
    0x2071206050a06080d09061d040f0c0917060105090c091306090e0a0302060f041718010f080702060f042a1811040303181703030a0606020127060f020a0c0308 69
    0xb680a8640348a50758016080d1a0500445080b4082c0310441c45042c0700c0140c82440b95107500130b159003220f00c10400658403000c503101a11f4002c850307015500c41c8410160209037000f02180b02d90448405a607a40300030707521011103103101c2c0304c0d841115502400544107440e94840365407141c03082d51400e1104000b643c254403d140d81d03d00a200004006074012800140080340c07034100180c21030300c00c962503041101003d6000405800c04078aa503480b810f071000100440da030003503036000d0b0390b042405e140b403450030b01120003500e800c4010542e03103200b1403c0001c1410071032058400c01540c500010f407010100e510a070b9240c0c1e1009030b4070502e8010070324007404507032510744d034499100030754a1140e0340b61800f807440c0c4c4c041e00d01c0c0341090f0034111201e00bc0d4200240b81c48840780d100520b040207401442d40c91a101c2d4001c2c2c1100c00c190005021a031502c0840b82110884c6d1090714850703580300d604c0400317401c0c40d40b030107001900042d02040d044c10300211310451482e40050290b40414031903114010159030f4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 652779091 1250 652777841 652777843
    0xe0a0e1314010b1305072d050f07020a0b030412090e040b1f0603141f0611070b13240f0302160507140102071401200102070b250e10030c02071206050a0608 68
    0x786001c03d10000147c0c80701c484094010001081030340380b03621070241002240d400055903c4c036907038081c601c00e600c0002080201700030341d00c80103a04022030030310801840c1010074602c400030000700000c0c41000d461003c01d41c5510315071045941a1300d626122a001a01d52600170042c109011056266210400c0850207803540b03001c135244170142e441560f03241d0340e14115080300d14611110405415004025011841ea00060002e0407081d46081c03e05114602d0100079501204161049407009250103001e69501e552008003546201c06520340940c0f601c2e4854140c100c4088403007001801e80c85010380001d000f6441282e58160300c03100b40c007503c02041c0d8400d200300c45403ca015140f8001203158081300c450f80c13000c400004516200340001814041b41d5a201e40d01c6040998400c004224541c202100b491140010088040030520f031095081c07840e030010801204120b00d00720705050f1100c42105406200700302100043c5034034101c00420807000e051807802044140e91301ca9078030303060181c04600103070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 652780341 1250 652779091 652779137
    0x190216090f0b030c06220e100611160b0a051303050f0616020d081b1305041a010c0b130b0a0506030601090603030e090403020316030e0a0e1314010b130507 68
    0x3805844689400d800d0a48103818203003040c030307981140807001c40229030000c00e0300f08544a41b00d82340d40300d400b090500c0c602604071411580e000900c0c0d844480c960340c000118001413011611007254050702c6988150080d5184e00038074080b488480105107002082c07140015050001041d0301c0181c4007140c031b44106580700202181c08810140e0702c0ba11000ca02c8911418003607174002c40789004101d400d400c586001c09298440c10403a80d141170304034000e2001d80b07018802d0141c8005000b000d041d031460b010001034070540310038070082c0c010030300c1c0e01c000b07151184407080401d822648280d854103103142080c1c48c14014001035480c130307010348914000031507080c40511513002580d425407298020800c80000300034940c280100308500714002400030503034440112260b0800c1501c640c40d016a00000b400500101c01540e501206681518209001c6c0f07540ba40072511041d00c0c0c000542d00844044802c8050241050301b0045030070030101e4503003403601c072074a610950068080d82c1e41c0100d090300080c60342070f0800e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 652781591 1250 652780341 652780363
    0x90308150402091008090102070204022101080303091504140304120b0c0901090902181c0302010e0c06030c0a020f030a05030405010509010903080c090a050d080304120503010b190216090f0b03 84
    0x288103094030b0201340e0286000d207a0041d0503000261a0041036070105080c0d0300a0b8103d4101d004004511796034003615090f8190241c103000000390b0039885c050006994481002d04030303000445072130340072030709000156500a003041420822070703a40d10b954000022030390b241d0304c006071400341203980030464040c804400c464001e04141d5444040343c0c144000203000358403403504100c420328020107070122610340d109945010745841341c00d80c40b48050340c00c0281c2500c0782c02032902c40302d0b000b078191356070b41e070b681c61042d46d41003110100383c203440d0290294184d05c1d0844c0703104140124400841c1c0c10324820b900c00c0007184294441d000030700c182c0e128440040c2c00d9966142000f00450a0040001d1138520101c000d0071004200609c1c01094070f90382d102082c10000c0e803200c00e90396148000108010f2040382452441414820719059145600d4990117000c18011003d00c6060404c82c0c9802c3d0300781034801c00072a50342c03000c0105400325195407020a00010b01040451100b46800c1c03080805803490007245850b455 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 652782841 1250 652781591 652781599
    0x301150f020316170715060501030e061003110102160801020310080d020606041104050a18140903070803100b0d0f05060103060501050306121c020a200607060c02010b0409030815040209 81
    0x30f01599a195030782113200c0004503035020010f000c0140450240f0044030104542960700107842418800010b085d07421036400d49486078040c000340079038060050305040460760451001d4000c0300070000100d040c117420080300300003e01c03c0c40021403031b1070301940114042c0400f01200146036640300314113515400000f0719000035800c0a00010f5003405c058100044203500728040600d000c2e141c42c0010020300b015049031000115007140d000c984c00d42480b8490341c0c1d02510a00e0303c1d042c60269040e960b640b02d003100040603204040046400c000400384500f02803c04200b070603444080c642c1b8940000c1030080c1c80146007e0a000c04105203500078070844041e658107075038180ca155100300074450340f48800091160140700f5480d60b4284114521680c80c100c0c04243c0c064403411413981413501c214200c2c0d120500c0c0340d1400103440800b43d902c000c2214a0981e1120000c40e1400304ca650680c010310811048503006070900310b19000b01540300c0d8290303120f0a101502d00002640c81e40600c800ca000d4820b240d500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 652784091 1250 652782841 652782877
    0x5040809010c020f0414040b01120b0103030e1c0807170c0706031a03010c0c0b0109050106170a090507060c0618050c090c09060f2503020d030c140301150f0203 70
    0xa103512440c650460b10340082c241500b813004010102e0304030381c0f003a603500529694102c10b0008202d110300102d0300400e0384e01c04440400301c9a0b260003102c0001071000030280070442c18003206030b0300c883c941140640814404540352040750300300221240c0c410f042c1101c03440101400302151004900a6982c2d12107554024800725040c0310094005000c951049880c1c92141d03800c41c50141c3c1d00740a440714480e0140d50792081416503180102000806800501e405800c100040c1b20702540035140c0144880c5a034500d810f9a180c3c1140c03c0020403a4140140c0755001d17106020a60641007004409003600c03988042001c400a02101d404980001d00c008000d5084800b40030130718581050020703044000c1e03038000c0d807400a0000000f0880d03480603210082002003c120048480910080c1100051366420803546641c03c9540c02901c0c0c02009000d807040c10b40c0c2d4411180321070f100d0b003004810a00c0c1d0f084400c1e601d50311092200300c0c410603451914001b82c0481d12011100f440801601c1420b03005a00c5968 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 652785341 1250 652784091 652784107
    0x80703050f06010e0103110a0e150a080c0d09020a0b0306010210090206040314121c0b0102010b0906190e0406020403050f030a0f12022505060601030614090901090b01080c13050408 79
    0x1c4c0803c04c48084034109a02e4900240210100d107004203044125611000301021080080c0321050161540c15410004184a1008581e8000200a84c0101030221043c1d03205104000640100300b0000041d42103600c08030b0103e40c00307c00d28020750040600360200e0b01c8000c00b440c4200f040e0345582e40029084070080c0000c00001e030158015405001d04d01c01907440c0000e400065030303d650000440321070011440084407903030100d140b0034185100c20a04c020700c00302030008003041c40110003405650043e4500c06046a114460300d40541c0601280c4500d5a12424070b411701202940060109503054041c0d0113551038640c100204a0310066015103514140c0c02031050190f44403410111168032507078080100b42c5510300d0b408141001002c51682c400c00c40e440c1810301d203203000c0004001505040c580781742881362154106803402c822800b211440141e6940701a101c2c05410026030050604004400214040002080850030b5a81c151581c85050042c01e1901003038030b0069a0150055402700300010f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 652786591 1250 652785341 652785347
    0x30307021c021f0f080f0f040f0204021911060a0204050114030a3b0111040515070b010b030406050604151217030108010b01021204030201140d092001080703050f0601 73
    0x101c0384030300081440d20420f240c3c600802c05003541c802643d0000d810f44280b120425004a0216007000340e281e0280c0407850485040c040a00d005400501134103c1241c030081155500d03011a82071004050701e41030030903580f000260110841e00b020030424080c280000b40040524400d580456a050355a81c070140740c0c201392190154006803c0344a03042d1640014040c41c1c1401c005030090300b090607014181d802194418020281d011340c4011407690500c124031000d00e040c00305403000d9034021601000100c00b40c60100b40e2a100e00a001040341401c4000058a5161240030710321031401000c0904c03003941c2d64001c1208032210803c1240b103661152006000c010038061444082d0361280141c0c440c06549070070380e00943c2e04240d0010825a45440300e0001a50741406013000d0811120106810030b4150390010b4440c000c00c0240004007403001c11100744503001900415900c0d6081034402c00c08109100c0444580c0e84c840c16044e0218421001154401348030703109003407169605890008642d22850011 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 652787841 1250 652786591 652786639
    0x90d050703020604121101020105060307053706020709060b040909030507140c100512011401021c122406033305010e121015091406040b03030702 64
    0x58405105945000c001a00c40c50b008202501c2942680c10750482d5070f02e4200d11b0300112038203280c116414007003445890f80300018020144e40e4103e60005000c0c00d610b403d440e1840c4071640402c444100c00c008180d07443c40d9007010400342d420130782c00c1c0c441c072540f0740c1912015500306105004100c00d0410040041000355031002501034400e1a00d81d1922030760f62103010148100664903034640e0014400e4104903e4095011b9400309428100507042004120800c1d06001d4140300e1039400307414014085a05a1080c048950200349604402d030100700c02200080c1000b407000460601207140202035141440700d124008444d845c413101c0190300c1410100102c001e400ca0300162a50120030200c0f500e1b00050480060502d408940c0714030301061300d04030005117504c4020440c103000e550000c0c1d1400c580340c804140c01d004403088980206919400103072803850031619901a0710f4803884c0804602c801854840382500803c0c08032000d01000c0c86c0b030700415849100d01c450007135101203442c0e15181812111100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 652789091 1250 652787841 652787843
    0xc1003060312080105190305100b0f0622050f0d060c02010f06090e0114040f030c031e030f050610020a061a1008010603180b0112050f030c071a030705090d 68
    0x8042605a92980d504224074508004031020407600c0006101c02e041c10b84d1040300c400302d0654000c0940d840c0d40c4603e501c80c1111650343c0c40a5481380c000d08104c1e05c5200709490200400740c103596444e4001031000b0f04c145820440c40d402c80d09681e80004d0a49080d002008194a000f030902c0321298256940500030280c0d017400c602555200c2041d00c034074006601c2a00001c0c9503420b0040390080055001c0750840720410f07000ca041886d54414040403550b041e6031a414980c2c10f08000381e01a2250070140c4a041542e01110016200401c40f49011035040e0172080b180340301f0300307418000d13a100c10b410041c0d02c822400c26580183c3c400d207910400301e0840d4001031480903402c050b0110b101c90791400704000080b5042c50070007160035400100320141d814411f294982040c40c4009403c1511952541003440d01803280f40300c402c040e03122500c00d00c401808111a00c080580840380d03104190803109071142072500c2034030240c0d900d400d44158111030507802c8900c41c08007650788900d091051400c0080e85100500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 652790341 1250 652789091 652789097
    0x50306071d090601091215021b06010e04170703050903120a02010518060a0209040e073c1208130303020606030706140a0c1a190516091802130b030402041d0c10 70
    0x7c001e9440c01c920042264900700800f101c54480324400681c0303082c07010780c03100e14070b50100d004010114144c415150b040d0202000d0780b696403203507801d04690602400303200d0743c3e0500468241d00b280400d4500100094212a0003c1c0515926825105c1c000151061207100d55009400000d6020690381d000741001140180001100c190314036a1620700051500aa1001860a21074204403103449090781110040c0006842c40780700850b1400100700c040b8822500d0340d2400c41003810030880b191041d18201300450500040259807401c0003541ea00e01650114020300840c41e002c40c1e580d2140424014500c080c20a80e0720b07048000c4402c03621a10b8444c3c01342c840c111503451a00c000348142c54101d000703886200340410740c0000d80e2030078000c80300007a20140c1e0380d80010210700c01c0703950044201e0084421042034a0740410030045908003030700c91001c001e00015082040416000c0700e0f1405503020720b0090b1030810910040410380391a40d002d0f03540c2054281d20400b15041140380c0b40c0072300070010090345 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 652791591 1250 652790341 652790363
    0xf02120723131a270d081317030a09050d03020a120207151b1101030b18011505031b160b01090b0f040227030304050306071d0906010912 60
    0x8001e01442d4100b20150455201c041408201c08112081c19040d0a0080010390f0320300208907105440050070030f445012071001e070103041605942c401e0205407450341c100c01c0c0306a81c0d400108948170940c20b139000e503912a80c00c491000807078000000540310000000e4850b8a24035040504000e0001121031048085102d8407107200c000418603005441f140507183c0081040c11308200080d03000e082054525000c004c1b06508903030094041c0a0403201013900089840b064000c803c0c0100c02030701d40102000c0d00162074503460f000300000301601904076910124000304122a101040320503100c15100401500c0b01034011400c0218004000c01d560300492499050b11056030791180c4512909034040c0c025659524a4003050741041040e80001c00b904950861078000c11034840003104400d04c08050071a401690054580e031030401c112006000300400f110701d0762030042c100030484603043ca4200c3d040c40002c00c5000e010705100d030017603001d04416142d8101301d50a00b020380c4001c12150b0000e4455002071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 652792841 1250 652791591 652791647
    0xd050309040c1716050724020f0a09051c0209150d031d0108040c170118121106010803030609090109020d0506070f051303020d0c0e0a0209040f021207 66
    0xd0b11030050410b80c142c0342d03990042c4150300c1504203060020901c00a41440a0020040590140803560102e50102800c85074000500b003c200c11098450072900e00361000803207514058904018014000d041c0e40e801c2d120903111010300c021b4401d034001086200c0f00c0d00d5402030040c60b0000751180c1c054000e0f44040481c10b18080001d051421010f000e5010805c80d581074071507041d03883e02c94440e141c1d007820218030b00d040a9542940034100c0b80311f00840c1143d82c40c251103d45101303412080f50301c1e00554800456441c24140020fa4a009100002c0890b190189040c0b60382c030041400750485490402850440e0b0320b920a00c81c00740802000700d0030556882c429400180e81c2c4004088085000e0401070440e4900440060710102480c241c0d00d0510400303000f520030341c001548407181501c0e0b06940192070000380f842d1158464507250003038000c0c118000c0811030b410009070302a04062008072014402d17520211006012407098009031100034011000069143d80186144141203860f400c00e5003200380f038 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 652794091 1250 652792841 652792849
    0xc0d0302030c210106090501030c080708060604050409060c0f020a03050a08060103240e060613181b05090a0e06060a080402120f0616030e03040303030504030504051c06050916050d050309 82
    0x200014107005003803100041c0003041d4006c04c814003824084c2000c020411a40310054203601c0f0041802e8200500c0c20000340c207a4a681040d1002483d0142c0301303001050540c60001b0261422412070f100180300c00d007131110980d1002507442c1c00940c05880340d62624054040480720303041b000348480e040c1629420310741c00c05100361084403002e8545c103000c0d61015062545d0b900024002034981840b540007404940400c00c0c0148203c0c0c1198809028901803031300b04d1a407031003e02500010750782c1443c01c4020404e00340740c02c00000d1000e481c0071210354040076180e4806010030001a90544e4024800384100450503000b03400b800d070800d000030030303a408960340450141d01d00011110800d4503900120280051024854141942c0d01c40b030f800c040c030011184c0d08802d603403405a0311000d4201600d610226007494044d404131030162030054900c1d005410308404c08042c226002d041121503903e0440010210103001c6816045044840b407803241051402042090010301c591041c2d605020030012a103407990707 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 652795341 1250 652794091 652794127
    0x3060f0803030402180910020c2401080d020601030b0604090203100213030201030f062108040e010e1e190f0b030a06150902070203060a0c0e1201150b0c0d0302030c 72
    0x20038000a6030342c0c3c545813040c043c240c1035140c100c0c10300901000510034000b8020901c2c18456009220050b1960092100c152070962240ea03009580c84503440341011882c01130103254140c0350618211807400c004801c0403a40d42c44241300103040c849154022443c140703411341006603418002011917210804000801080381d000c0c1c0c1c0740542220184004208550b014040c10200071114001040103034603003c41c14001420800c80099074156001001e002c000d1114161805083d07c034100d40b90641c2c560080d0180040240c071144425991440c00070f070b0400421003224800d81c9080d84da00003180482412202400392200c6940000d600c2e1901002036480c20081d0348401030080c403021404200c0d600e400f400540050300000f010034010811a00542c600140c1c941d0089001600002d078040c0501080792441c0152890b40c4d401040342160007202c0c201500700703461103e602c21854402c16503404580b001d511800c8000f80c460b8000d00741110019020742d016603400b07401c060b28249880000c46181d100c4070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 652796591 1250 652795341 652795349
    0x40b0402010e0105280e06040b031b120406050417090f090c0705161508040302030a080406110309010e0723040f110d06091a060919050607150515060f0a03060f 70
    0x45040800c0c0400300c3e0f1b00945409000ca41660340602e031030705082e941c0000d4840100001708120706076011288802ea101c0c1103405010114101d00402e003024035089014107000d441c103851000d14240041d500c03d04a60450b00401c8000348012624022070b018810101c40080072440c001d0760501c0880702084080c0182105000204c0391031444131300300044060f4036014402d5038820806800f08100000390000110384509a203401d0483d0b442e616441d010307025046c4107481c1828500080144007500005401140440b40f5450135201c0c11503c80d04401c40c0140000c10b6240761a02c42040303401d550610b0340c4403400040c0c1c813040c0880c4000349025048003990125400601a6030780d803d04020212152141a900c041c005000840303403001030b00020b080e40900f40c081e40c499202e01c3c0c400f43c40501d8550303c0c04c0c014031000d80b600b51103810604102c5e04403802061448842030400c1c2c00035140000a00408448c0b0400410140c00e0030a428280b52480d0072142d00182891b54852000c2401c2c220361682400074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 652797841 1250 652796591 652796647
    0xf090501090b07050301210203011b0314010512030714070e1f08060709170c040c1d0d050a0b0406150306091b15050a0c2102060708040b0402010e0105 66
    0x1d00d040d2070300060040b0300400503000c022042c0014450b240e14440c2c00030000043c00c81d1041003d20310b00000703004044401c4e0000d00810100034041400b81c05401001c440c40c140401c4581c160703a1601400000c000841c2c8141003504100f020800050004101c0d042e20060f510031211000e403615400c0c49490015076030391000c81e0040c1e0104003500307030f03018070301028262100150006040c14580904200b00d1801800090a4000301d07400204108100b01040510010410300c0303004098003010b0700b522030080c2231fa100080c002c0e00c10400d80c20a850a8002e00e031f88400109642c02e45c03502d44001440c400303081116607a03200c03c1c444e06205404900c15010f54000c1100007400c650501d400c148181c1180c9204646005451040040039810706800608607618205207a65840105003110329003801e0703200070b182c0050700c0c40c0500429000c800b1500020080d40171941c0540342c102c2d0507243c5400c1260010540c50340000040c005502c40c0103200d03a1003506040031410b002084809513007801c081f203000d1080d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 652799091 1250 652797841 652797851
    0x14160501110c0f03120f130c06050903010b0a030203070e25120b120a0201110f0304080102040e06010822060207050105130b330307031407060e1203120405010f090501 73
    0x181c0424480c480006202c1c0000b1854407900c0107829401500041035680711b0b0101c200080e0242c4082032921031034503403003000002015110381010340705400103400103000e90f02e070181d0206541000d00500e026a40c008000b41440d520300400c02c801050010443c8503500d0880f84407202550711551810841040741d200d070110b0500c0034240e07000320740301900001c0c481c1500c944502103140340820f585241540a181c090445c2c261482c91520780181d4841c1e6440603c400680081d0880065004e03009850903103400c400242ca40e540112565041030300d142c1154000580040088030080086514051041d0341c05401d03c01d0740d80ba51821660300307c5940130f414000d0100b581c10442000d132205c0e400050400301811222900c040440070704c00742c090f8111a414000344804269504200711401140e111000b5401030380c1111600b51240102c0c4118800306941800c50022031a1a092015007000898000c5040601000c2131408004026000b07940c82d540e2900c510600301c0b00303400f95400d07142c0900c002280c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 652800341 1250 652799091 652799107
    0x80c07060905150403080a080c1b0604050d0509150d110406031410060215060315010b04080c010305010b070209070c060203280905071a12010e0603100902011416050111 74
    0x51052003e4003070054030008100c18400245054103452091065217044005681c1e08002d0240720301ca16811000b1200090f10500126032001a016200d01d00c80c506490301101d00413001c2e01c15003d56400240c2c0204d0318040580e02c400c1d00d0010344038000c1442c6002c00c10f001303100d2404242c0c0d4042c0d00080002610307401500180c1203010f41490b089580319002000107031400034001e45034a140d007041e00d030a40110020801c2540c1c108031401d00000007000d00070565070341d01141c25965026210380d48050041c1a2400020742c064031499040344d540400c8140740a03400d031308119100e04020501c100f4042040c03641004281c0c03d03c05584644a0f07071050032043c601c0101e04070020016000101d14440c213103001c00c1c0001d60302081e1071040310660340004a80000703414142c2d0540c01a61038400a40044074000648a840600302a0050200760b080e102c201d044540b20200b80c98840708040d002c26a240000703e814021800101a9004160508903203203d00c0d039a2a42511170000c00a4079452010840304 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 652801591 1250 652800341 652800349
    0x131116050c010215010902090316092310030312020c0d030c090b0f09120a0b0c040306051812090102240f012102010c11060d06030302071208030c07080c07060905 71
    0x20051030740c240010600c508000f00c031041d82c8541405035502c0103030041590a480e4808001c001d00d00c00c00075811001d05a109c80e004001026000d0440502c0c0b010400c84c5044481e0700280035006082d0084074a002a00755201615002003803118448500c0d420040d4000038441070040c412502c0d0f040c2d90100b404a40c400c0001d001103642d401080c07030380004110303104030104d02000321060b00c602521420704060032540d20728246600c900000e0912000c070820030450024460040c425240301c0c1508000315160f200d0301805001240c0040396450303002e02181540300c400c0d4000340c00742c450305104540c4070040c2c240300c0d00712020b55181061003458901c01480044000d0049441c0940051580001c540700900b6101c6071032160180003078144642103240005124a48146031904800507095660341c00c6100c51500042a2600c01070340140207400000c504080c1e2840315001c1203070040303501c0c0d0441d1607464540c05150300114041b40e0350501040440743c601010700a5100800380d0381c4840f00c40500d490184 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 652802841 1250 652801591 652801603
    0x209120604140610300503030c130b0304110d021c0503070512030c12070309061103090f030c030703081005031606090b0403080f07030c020a120314120613111605 71
    0x100d01400f90394002e1144080c3d1160364498140303210100300720143c070442c803540f0388100b1700009846030000000b04421020040c0013044011441c1c4c2007101c0056481e22a290b56010a0b10000e11404000001c8030440c6802000d00d103404d40010494078080b01c96410303400101550b00012149a0008600042802014800441c661001f1241d862a41c648809040018443d01750f41c29800402c000200b400b00e80300750300c01c1f000140d22036010866880707844825440c54004880190301c82c40f8a09001e1150000801607409007210310000303504141040d54207403103c9000030400c25040040b0b902c00516650200320940c030401c480000343e940c460030701400030000c0b1800d4100c03000c2241d0410040001640c01d50495072180c2507801c480d07032910211724088480000007140a5404181003030302050002c58801000220b520a40b00c00c040f40e0200034041d8a0780c018161400c4008070392900045407401e2180c3c0306104050414400141d03030510001e23a41c110b803c00c055540a401c2805400020040c00b0465 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 652804091 1250 652802841 652802851
    0x3030f1b0c021c02060702010c060209030111071b0e0c0c03070b040303050124020304170c1009060909140a020f0f04080a1104090b0a0b040906020c060f0f1902091206041406 76
    0x11003c1c18045038000c540704e840b070b0150080c1005181220340c0240003c41c1d040d5041c5602c0140203006c02740b0110b0210381560400641550b1178512030011404e12200303c0791120807a06599402641565070461f260410b400c20105000f5a000801142001600301c00700c091040c0d1094a001030254140051140c806240751081c01071045081c001d1a021600003041d20700f180c03c0f042d0518144200d9810083c1003000c140440c0b0b0700030a040b000c0030030481d001800513040d03030750b84c0d520100c400d81c0d50741024054510284029001c179000d5000304141410640040015000b040c50382c2e441c3c6040f0008a8450381d10075405030320150403a014110801000040c1448151401c40341442240d049440b84074403110b02802c1d41c40c2c07065448110b01e51540313940c0c000c030b4481e80d04a44119201e80504a00079100e00088403d00d12500c1d03003100280901550000042c01200ac82800001082400000400a500840d12a544989001001d28412a040180a1056201d41c0c0307001e0b680c2d1007103c0341030300d000c2d0046d007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 652805341 1250 652804091 652804129
    0x120e3c0a0317071103070f03180302150708090604030602040e180616110304141215150f09070f081008120702120d0809071e0303030f1b0c02 62
    0x1500c9404a40e20040548203403403500b20910250300d0300b4000342e618901400440c1428040403400074244030654090520f1a17010b1340710086042c160903030850003000c4a01000307500501c1d40391402c039102d43c0d0002402e1171901c500700682ca0b000c1031000049540c0c00c580e00450349245c0025003400002d800107005c46e001229441702c41c7c0030006200140d038403200002c0c0071041c1010300d585402c00701c1e803050007620b07071692107942603079651911041c0f90041c2da00d14070945409001256904602a00c00260f182e26503054048844115145d00008244c8018524281035000381ea61455007807a07a600b140d0b040c01450240c4500d0100b520101011340079610003410f480f0303c855043c108000c0c400000c00c1d503201840c04020340660703a4441e40b0005280f000340b01110f001d148200c40300c08410581000b40980a46034240844541a40c1c5d018020700c0c1d40c0b00203294910310081c00b001000040c6c007a40208882d1440070b580400d5404c81040380e81124000b0300700d0000007079140300c0d41005609255401038140d2860341 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 652806591 1250 652805341 652805353
    0x507090510120203100f020a020105090303061f0903050d120f05190902060c0303090f10060f121104050f0601030b030604023118031707120e3c 63
    0x21110310035407501d210350090300205011070030855800740520354160380710040401524800c140304100035004251440d02540ca0035012a61000000054900c9860000d051440494074002c8520001e031084c200030003400050310010000400a0041d03030101e207440e45e00c18244178420454401601c9101800001203460f0000380418549103102d20502c80e409070001040d0940e10b0710110b4480e02c10302101c0005404084140804060301148010360b0b80c0d0080e088a482c10100c400d0b51048800030f108100c1400d01031541080440141d001c441c000d0341c000c644201d501820350011409980c07003115002e031142100410010290f8040c4100359501409400501c0c4501d03207640491a2031807408503602046a07074a58883d4000b240e49556000410341341014410f8001c450b5826210088c464402c9020942400528150013440c60120341702d500680c0d078400110b5007540c0480c00a2401c00c4030421507008407040304003d01e82c810080030511030681e40a06030244000841c03500d14030032510050182d0031035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 652807841 1250 652806591 652806601
    0x60206041e02010e0609031f05010602010b03030f0345010507090e010302060f0714030c011b0e0906060d06061d0303090d240609020702032b0315050d0f05070905 71
    0x1c40208201300181c0380e140d41c604140001074503060807245a00c40744910014079190040494010341e040702d000b0b400a201c0360049504054980c099184000303410001400000d42d040203400b41090050b0510004021145c14592528029042c0d4944500041d040c05000541000240704d01c541c0165249000d04695003445040540340d841840080c2c801c49020a2600001d11140104d07014590310001540700c074070704100c4003510307504010705417440c6500e03101441c034161b184001d400d10800300c5661074070b041036052410480e40c80300c090080c40e0030240c188130040190f0258441c6001900690f01d0704503908607100000f007404c010608840e4006d820a1103002c130300d92100304180090a510850074505445045020561907001c00782e003c0d28981015000221083e8960081a00ca4002c0c2c007a151b0890410440c24410490048600c1c01227142c071100780c280d980f10b54400e4443c40a40310301481440e944070005003c900000a064507484202603814081007020050038008010b0b601d400d002510780 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 652809091 1250 652807841 652807847
    0x18040b040c05220e0727140c07031b060f0b030709090809150f0708070219061b110a0e1006031104170c0306190b031b040c0216060206041e0201 63
    0x81084158030b103a48824002e20000410305c44c000c060f100200c440403500c0c1d181e008800c0503440c44184440814504140e800da10807051031118494170391025614903060f00c640d011602d0071428083e459581500d59800800100c80d03000345041c1c80304281d8007041074030681040501b0400103601c0741500500e484c80410000e2070300c034241d51000710b040320000303411640603496100a00c82d03080342201160000906c0300401812601404000c1c2c0241da9016420725480717030b00140f200c502c1c0980408156040001310403852001d498140082c414a092900d1b5019080840c20b1419650000341c0107510000811210340d001d25409002491540380a0011030300100c0d42940701e2046002d2a001e20260900c1414540400c200107080958090304071601e0346030200200c140390031011421316889061195081080c60001529072040c040100e0a411641c01c200400000f00303512034910041d80030350072860321845009a1603200400554020307101a01d824074142040140d03c00c2c1c1c50000d03401c5004841d0260341c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 652810341 1250 652809091 652809139
    0xa050c09100e040305030a0507053c03010801020d05130c060c030309050609010c0905041401141203040e0601020c100e0103050c0d0c020307060b010c0209130218040b040c05 76
    0x10595903a4000d84a048a08691041e5900050b04002e8940140020940c0c8a4000d61051000c3c03042003006071513002e0211050f03c9135080c1c0c41001c2c610140380340b08a014520524111080420f007503e04411000f143d0f015030b4100b6402458983d50110301800f100d0114085e25900541021040b03141d07a03540d90300e90300585d80c40c2c042e034402c01028002031030800d4025840105800c0e000400c44849103050199180070f0b041d00c80c2c030f41001030113403a00002d1504060149400801413009a401f03240e003040d0a4040c543d2a1501443e40044016000f4030100710600c0104040d2403018103070b1240786025800a86400f03540b010240c0074825000094125580c0207030500c910300303800d03e0003082c40d803149951403e240c0030303840d40c1185080c03a041c8a10092600040140f4019108260178481903188a0041d00d0241003d00c0c046d4210500b400064540c6071404040060644003d010798000040498165a04a42204c04507003c40e0100e06200a01c071000181c50014542214100f25855803100302190000d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 652811591 1250 652810341 652810363
    0x50402041206020a020c12010507021e07090504020303160503030417030c03010905060f041113150806060a180611010b030105071409030a14010903082406090402131e080a05 76
    0x1d030340400d91582c13080c8284106071200000400d5401c10091503d0040d00a101c142d40482c050311030559806174a07401c1001d0340c1e441e00c10850203401c0607490408800b000d8800204103d03403500040000500c0c0711094a00e040140380118029038580c6007a14041002c40d02c14040c0c0f00c8007002c140300300012502c070081120b05440394101c0100e4652610300c08240e0b03d860850384075611900340a40c1680c2444090041c0110002c41202c009440b55035001032121540503512450002d00030100041d0f80d420510000c0c480c5c200e4610380068482c1881400c110180c4c1030b41c014800240000d5140b41c10000c0901544c590890100c00811044c10110b1000e07001500c524820701801c0c2c0041006034550b6010f0042103a015080a000d04c04880025030490080c4400541100030902000c0031456011030703c0e0348810403410301e204c4580e981d0803982c1009266041005c103035920036000c10482c03c0868010031554001c11062a1100fa45803007400744a01d10105c0342c12005d0b00d0751119218101041002801d40140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 652812841 1250 652811591 652811603
    0x60409020105070605190b0d170a02120f130504140105150702060f07060c1404090f1d070602060603010c080414030405060a09060306053c0307030c050a0504020412 72
    0x1084040c40181da00e4010000041d00103403400081205003c01ca544102083d0b408030010841900c4600402010303206c101800b400c00c1c80c503a800b032071504000f803008150b40c06060040b41d01841c4c8000303003050154000d134a404030b0248041040c0c49542c0100f44102c0292104a80500034950b4100129003003d03414070070704e4461240601d00ba42c0044903001162501a005085240c0d038044007006401c09601c042c0085030442d180c040c0c64060340344280c06064a40c115541c001d407800c2c3c0307400d420801414140b107101c41c485544020b20981882601c00340d40422910001070046180386c17050190038000000e01507070007641898044608258400c548030f40c02a8010741c00c859030381040c040e2074914002c0f500032581001c0f0000c0d1801c03009810034118811241c256031705000301d985034014019482c500c00090590361160003144440032042201100745464840503064846903543d00213480d00d006079005460394080380600b8401404d0a08098020b4901510154039103450507500c20000e07000540c1c06400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 652814091 1250 652812841 652812851
    0x5030901030c03020c07140a08070510030906180302060604110a090605070501060b0304240c05070b090a0803070314180319030f061511120405011803020306040305030f0108070e0604 80
    0x70b8a000703505a031011800f600488054645400c40d0b150380c0290504901e02c940c01c0c403400056140000902032003581d13005814809aa110700c901603000d0b04008804031580780c2c468071900b030007090107054014103038000e900500072070030f190f003e0200b00c90070150072055106d0200b00030700741c0340c1c0c0143c0000116000c502d485940c50240d802c180d4010203281d00076a03103210380003040c801440303100d44c12001e05040c00000c480b4070791604e410145c2154822003000001c14003e02c442e40210360b0001d03549034400c0c030108c01d88400c1d40031661084e01d1a4011600700c0e021954580711030494011703030740c2003540c000c4214405210803c441c20b581c9540380903261086800759020480d0111107031003900515516060680c0c14024240c4030b4081004000e481d140e800300007840c4503d900581e0314009004c519480126a0b1582307080d0401004403060b501c6201d4490b0f024451120010050318108806c0344980d00072340e00c803501d078141140c24226010040c0c0c000c1c2d006a2011100780590314480e40350030380050003164000341c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 652815341 1250 652814091 652814111
    0x513120e01030906060b2106010c151b03020c2a21100b090a0221060a0b1303020102240a1e0f05011842030302010608190503090103 58
    0x10183c510f005000301000c0c18504005071a0b0b8005000d03220701aa40f09403078080b0b035081400c0340503d4508075280d0740000c41815940340810260f12130040301c00d1169030b0210301156014031901741401224243d0000a0380062010000c20041c040780f03159039580d140744404a11a40c1442801c40400800c003440b40b12010031083d100b60204540d1071443d0b580350b00362540500b45d0207105000b44003c0e5102d900912005001986401091084a5006240000003007203000000f002902010000b801c10350004111400030a2440c0e20b04045c010503100700035015486821880020300702000f90f960001e0114428680704001406d02c0e0b4039552080030003a0001e070941443c0c61288841442402520a651800716103100d212203603042036041c2ca48400c51014a01c07400343c016021900490202954101003490141e06181e4400c0500c02d91700c400c90031140c1090503034488a800c04084c1c3d0045001d80c0d074038041001124028400d0030026103807100c22540c4012302c1c1d1140e61310b0344180001c44d4101603542885403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 652816591 1250 652815341 652815347
    0xc07030303390315033008070c05070b040f030c0e04030f050c121b01140702030909040503041716140906040b0a0b1c060906080703030f0903050319030513120e01 71
    0x401090240301103288280c0e40d040c0a440800a40ca10130b40a5461280d025110003418906d0009010142c0d903200a503680c0003001c80d0b014003203540c00c40711802400e800260416400f00070f80b000c0c140926280d403d2034a5482c00b0b5034400059400910740d00441d1041002094010840511012583c01c001d5515441d003d070440c10072211500d0641d5040000c195124000d20700b0340c610300d07131403c0701000b04a240750501d501c0c000c0c2142111850010380c020860000c19040c0803600c540c1041c851000c0702c1c03c05442d01e100898450a01007440c20039840b00c101c50f1510032401183c0001000320134280b840200110340442d090140003002ca0380155154041d1410640b02c101d0741800900c45c04a0079511481c280e00c20300380c040031f2400d8001120b41411400726100c00d49125041c01c0350f04100c000e100319880c0d41d6007a680c1805e00c2501d1001c2c010300000000200d44148020404003c00905101c58581b421501404582018201e11713144100103030b141c80054a0841c2541291407903060000006410400403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 652817841 1250 652816591 652816601
    0x230901061d090117060916090c020115060c020a060905010504050409020d02090414011104050a0306110d1a090a090506270f01090210110304050d0212030c070303033903 74
    0x502d4000408000009040c0c691001c0c07a000c84240c001698410b403a01020b581d903d1600075100c0c0040c000000c0300f000313507007655800700b40002954000818400b88104040c1d000407003d601c00e0001c80d000310740000840c540441214080d060034100b0303040345420440002c005004a015150189603104038440540d51401c451441c15540200808281c2c60035141007183d00404c8000038100d58203000d001e07801c40300c24130b0035101962000751052189600d581c882e60040c201c00e10301080950000c0041d0130002895002c2c1d441215400b07180c001c98402000140000703030000405d407002d010301d80724403440000c0d07010030f80c250088194a0b40496030300c03000000c80090004403c1030006c0d88210319048000b0301064200680107802107641805a4205080c01d0710031a5040061006640041105020a203031030b03000c2d40d01c2c4600280100b100d240c03810450030700d0750f400024400180da206040420425906004080950160040030641c400342024000404a10156980000700a00c6400c6c12254426404 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 652819091 1250 652817841 652817897
    0x1b080a0f060305101b020c031005040303060f0f0e0f160f02071214060603060708160e0d06021b010c14160c26010546020423090106 58
    0x4e440c0403085200b441801030034a9040e0a00b100c0380e031178103000d10500108000c500190041d01038079518414848940007801c004004409140d0394510202c1d112030112401009401c6500e41a001503092040d09004500010050640004401f04000440b042d81e03a0b00c600310071540c18083c501400c1c0b58016814070f00302c0c0c1c208003103542e504080c00303085c8070954801070900d038a60030075228036884030814542c80745001c80381c14020407031850100e40c2e40108614a0300d2440300c030389041e124040c1c0031000200d42c50740b079143c00c0e0741140e00402d5114100c01043e61842d0f411503018000c105950751900050305000c02540324000c551008500d80ea41500a00e00d000384090b0700c00300c412806900c6a010054a080346500c90900e40102903001d405150148902406842c0c6407410101e02c280340c0700220401c1284030401c01c241181e0422640e80c80c480e0900501e00f0300c11800c1d0241c2c48900f8860b020100c0c201c00c0840206c1e01003103561031480f0380ca030080040d06442a078a0315050008845040484181c0c01d100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 652820341 1250 652819091 652819093
    0xf050c071b05060f311a040801020a08060108100e070e030703150504031805030709020a051207020f0d03020f0d0504030c0b07080103061112180a0b04080d1b080a0f060305 75
    0x142c070b21000325a0304010003000c1205902000c26001700c0c03683d03407615800c4080d81c00c0c00b403110090a10038400d081c07079075100c40004440600e1a26031213283c0c20342a81c10004800000c10301c4c48090100303d603001008a03174803a40380481d9200c4240b81c032a00044400010b080340c030a01c03504034540101c81e2418000640519081105d01500c0c180c003402d5180244001c030703070940000f094000304110040d9002103180072281d00030000c20346a8280306109000751320845100060001c2004420422032082d04201c0c86804d5640180080450060781c07036007441031070b603a07100404d441008400803035143d08080d980100408100003803956250324080d15046200040a0815052036040258503940300d1441c40c182d03807040310180207003e240c0d256421140104152110200001d000140320924205a0100040c20000071603a420781c2c140c40d00580d0341010b98054072941c40c0020a01300106807405400e161540000014403074410700c10000f800040050508403880e52100807070700380d144103a00310001039600300c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 652821591 1250 652820341 652820347
    0x60303070b0f06010e03300f180604170703060c0e09010314030f070b060f0a0b0304031d060c06010801050c27010c1211070f05360c030702010f050c071b0506 69
    0x74210f400c6d00d180b0051400386072001f02e035a071307620075680000b52000b0b03080c60000541000f4403842c1c804441501d18505c2a003254090000041039030303606c001c8404070500400909420390640c02c000341a00c054040c2002400175000313050405803610010030741180e0304510a02d91544a40c0941410352140f01da1141640c500403420700705002c6c0340d1038003d0103960201c869100300c0707900301c0c00d100207850b4078443d0040040c0103000150110380240c8a00e469116503083c502c48102c00b6800194194000b01c0306101140e01ca603006112148091040940240e174135103141b82041800c0e085030350710500070001001e000c2000b4440042c1e0f40d018250b005034166026244a8085d1698840204403a10702c40040710f5a00c0b4010b40082c0c0c1c4050f8044010660340003130413061182c080072417401b1104200c2c2d19100c41da011480b84082c2e55201e10240b0034000e10740c00c10300035a45d0424200007401d5035951840134500620304000c2c04501c3e82801c1c00c40e81040c0e4445100240d80f162201d880070b8031388c9103601c0660444000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 652822841 1250 652821591 652821613
    0xa1a0f09040c05040914060105121b0c0109020a05120309120f030d05151002030f180603010303050901180e0601031d0a080a030e0c06090f0d1514060303070b0f06010e03 74
    0x800f000c1d02c02c2d00c08416040185280f100c8959003254000d46901d80070402c2041143e8072101a810617541c80420040c0c1548207200765240750354160700c05640c141c00d60355030328405021880c0418259004001c2101c0091042d030b000e043e01c039201d01c01c800c0074521030b0340700b03000040000e9402e114549800c40d490040d00e4442c00c03086414000342004491170647c2c0380c40c00b46440581c2ca443ca9070300d80b844440764000c505017040a0480c0d0800d80c419100d0f100d5403002c0c030101e4031b229560303000214082d610986e112a1502420800500140151404010b40d03961021051250b81e944561141c2e010303409207008200c1894101103410104d6011010141501480781c0c40c50500040000408003002c2c00d46d0100400600f8200d510303220207002042c02e40c009002c11500c40030340380c07440c04041d48034001414840080829034920702c500a0003c07820b01031940b10b00b5540280800c4030b4042d40c2c0010240d000d1407070580d0780d035122814000018140030803402c1d4a07002c510340b41d200f101c0d400460341d000f50840d1801104 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 652824091 1250 652822841 652822847
    0x902030109140606120f1504051008010c02121603121802100201020c061303090e09010501030c060801030f0f05030f0a11010b0f011b1509060c0e0a1a0f09040c 70
    0xc2c0c8800840a2108001049050078258111802010400400001c07519180746501c405c0f00c02400b480c02110031040850555521407140d68058464140700294561030b201c0c030207003500e640b10307038440030340d0400c0c0ca11220b040b40d00c9003258030321080001aa04d2842c0700349410740d90100703071221034030703440f40751842070080602010031500e02c6900840c0c1e80c8841c2c5441c000201d00340d20070304c41c940b0700d1500705001040c100005e030440240124800d0609410380358840d110000201c0c021910044c03281e4581c801082803000600750480545185c0c6010111503045d51079102d002034040700300400081c2c072a0b091405000041c4161341854001020b076035038610300910024030b11401096010002d504e0b011b0032081d075182054110314103032010f8598200d40c17034010b41c60454640d180303401614600c0a00010500c2c0e81d00e83d2250b110341c24802c80c000907a03440344e0071703006150400c0301d076910b80920040c0000744122800e52124581c0c280d140c040559036600750380300640340f9000d0600611b42040c01c101c4000c000d01c2d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 652825341 1250 652824091 652824101
    0x7060c0512060a0803040e09030d05160e0307061418060f070b0108010b0d080d020403060606091805010812070203070306020d0902030d05122d01170f07050f06130902030109 76
    0x868007042070341c5454200c100b101c44042031040440d2503200300820011074002003c42a4400303021001e881c18076410745000415101b045801010301d80e84100050942500103d03810951310b810b90041240c2c0d030801c10054540440141c0c080404400401c420300391555880c0b00200c0018064407007900c1e9862811080800d401600b41203910f0380d15070001280745241440703030b80d6000100408031112501d55031100503990303100c075554100041c0c00300404804a210b40c06610020040d1b52785003180d891a01858080301c103030041d02c0c1c2018a0074480100070b0b0030741c0014070034940f10022414560343c801038130000e840e00850b070b031009060600100d0001c101c00030070f40c0701d505128029003d0381c905080e030b010308403400e03c01c10458241081d02c1c840070070306450780e90440e20000030b0100580d14445550462100f05c0040c00d91040c60046030b003010006150b00300f40720740720f40305200d80300400c00141083d0010706640109017015004034400f0490b84621319402991200815903050119903a584175006180501 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 652826591 1250 652825341 652825357
    0x10906080919080d1a0901270603030e12010203060a060f0c05070806010602070b16081e030f160e01050f071109010803071205030721110c060402031204060903061107060c05 76
    0x91074840510401a00e80e05101c50415009202c0f1507035030708201a008003000c8510382640d23008400c40d115030008210b8441d0b500518000c5e11f40045601c00c51003044043c0103142202c13012a4010300910045880310300c0721000b03403515410003003540704001e0401c540d44940c10f080500b061017207800c00240e00c3c03404a0301d80d050308d00580c00d60b05070580381e642c240d10038401c417549562022480c0383c03aa80401c00810140c4107072450f95040b10381820750241010b807079030000c1d6440941c44285005000a0000312a00380540440c107041550b170600e9800000307001801044000080e10000060700e1081150205040c412444010144140c1d56107803142c150742c0b6084041c00f19102d0740320341280c1c1e19450080c0e0903244544015a10702c80b141d1202d1200f0120ba21582110162043d11812802d184008110282109031141e00043c45507240900405281140805101110b540d04004c1485080c2d440004130040d60f400143c003050440108444107482d00c01c1d00809841549898031911300349a00000030f20040c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 652827841 1250 652826591 652826617
    0xb0f03030a090e0106080907060e01090f030b061806030a080304060f1404050d0810170a05032d070807080a0c0f064a070308120711010b01090608091908 67
    0xc4c0ea00e442041d54a06015250420964803c2a0401820703100780080000c0444c10314184905035960f50b000c030b074400c0f02c9400c12100302c004001003110700d040441d0418041040e00520300710504042012940343c0448080140c02c92100000080c2440303d240c200d40e01032250a1010420341c10701420f44000b035001598100c8290241c0c078119a0315510030900c0e54040d600440e0350113165883e040d003030f81250039140420340050164240c2000840c00c284050b00f0800c1c44020014104004071500b0160010b00c01e1304501c8201060000d40003050503072040e58402c9034040d040c1551600e1440342911058070002d0018491061514482c04100381038110700856400307940540d8050312600505000d401080b414200b103011a580c0d030054825000d03007265100754019040d20f01761901c2c0d4a400d400782e44034820302040c08a03907006001209901000f1050703070007100f000030451215624002402540d00e4840c4600304100140480c0440c41c051181e24407401440003240141c0b031080c501125560000341400d205 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 652829091 1250 652827841 652827869
    0xd0e0f180f0118022109010e070b090f01031505010302091f05090907020a15050a021b010603140a0c0302150f0a08160e060f0f210901050c07050307060b0f03030a09 72
    0x3d641080d000707645080742865625400184200c00313540350382c130006088403015034a58009490451b424008000940380404415030b4880c2c042c17050180400441d488181014981003c1c11041d2000050642c2610030919000d0390304c1210400007480800c0004c01489039800c0c0480c02002036070804020101901e040d90243c40960316040180d03141d0201000240c5000c0c0051054500181d2a5000b10352000601c0001402d180c0c44071080ea040300c82240c40003482e0b80d5903e2090040c03000200602c40320720040d400400511505907212001041c40d8030000b8012000e0b0300314001d40803220002e4a40c0c400906002686817001034800406085003911114420008207440001c994400e00f840703185084040d040c03a181c10400c80f0f200c80d0b070703600c0010000c1c2210360600120746c2141d120201d0802c0040108507003442800c284140c1d0382150400341c01912415010420b0000265001c02a1105a600040c001502c41c0e8004041100c10900048465250100041800300d19400c680d81c44103542e4110000c0302 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 652830341 1250 652829091 652829129
    0x50f010504020a08072d05120109021303080708042d05030d021213172b0903020d020301060329150307030b040c0e0a0c030c020d0e0f180f01 62
    0x7203100d0644042c00213407035000054141c901803958400440414071610107030341d032044031500340c52042c06000710000341d00090540440d681e614046024005442045151050380400e16110b04424840186110000700f0100f051003440d405071001003001d0449080384a691410a0126454403040c0380c509003000040441c203030800084146400c84140c00820701147c5c00c0c0640003580c3c11080410140e0ba4840c2d00c00b0a402d0f003c19200d907400c24048000301828241d055620500c45401c01c040f80203a0030ba2048008403942c000d8015084a4043e601c908800350180046400741032503400c090003101d0780741c83c030f1184842c4071500c02c1034040b00c015048407030391901da10721000d05c003062505680c50350003a1400d02c041000b140b00341c0d03045072042c22046d00c3e07959a502480d002c00d400b00c58141c02c0c3c039035480001e02e0494044c01840883c0a4910240c980960341c00c0c0040c0801160041f46030203403c0641e261011307616071100b9080d1454504094100d41c2c40d010030310000c42c0100740544080311141c650340e10703 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 652831591 1250 652830341 652830349
    0x80a1b082a0f1b0319020709050c03070f0215010b0a020d05091305070507060c050a0e1f0f030204090219020712080711010c0b04050a11060a08060402090a05060a03050f0105 76
    0x3044004841d061502191071030700c42c41504150a1410507845005071607910140400c01424000c0900141034100d420021019090111980c0718000141c10282007080b680c040c1c104480c0d1095080c144450f051a1100c4124500010904403c1d51001c01400204c0d14548040140c41c580d1101c0d4221106a008681d04031414001c5100c0b45800901894044840002c1e0fa000282e00001d2894280e04088143e1108801e50742951200e0011880002b00001e080343d20890035140c01d10300b80c41d090040c50030351500030502c01c0707400c040300c0421021401551041d440794040310300421300500150344402054240100400407410807802502c01e14100241142d01c013001e00d00f0040c0c02000680c20030300f06407101d4140201c81c04115041141408011001490840000b4080c500450040003540c51a02e08090082c0b044400c45104e1203007031010400c0c05500980b055808542507801580720403101011581000c01500529805503003c1092141d80c0e5165010521481c07003041c00c0001e03a680c8000340 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 652832841 1250 652831591 652831651
    0x10f1b0f0212031312060e150f150603160306150504080d0c0507030b0405070317072d1416060f0e0604030308010303081b0a050c0f06090a03080a1b08 66
    0x4140d40b130701c1154040004da0304030800009128043c2d00b0200c0d0103c124a10070307080c0315501003414808980300c001d0103006809085019409235000c12080080120750002031124000202404052a4142d1045030058400d8000d000281145000d0260502c641000904550418014070103148102101c0c0100b141c8103c160915154114019055131f50860701c1b03080b0015401401600c9612808a00100095403a10070305280f00300307406155214030080c0342030700301e018804102c60302c81000c5403a5854104994144050300b00e6101c2d402015010006201c641013462440a8107003500c01e001c4005001034003c52440729514003a0384610b0b009260b0402c000050040d0700015002441e003d0041c0002401902c00c00c0d0016904031740b031810002125001c003070a50111000702c0c0001e10108041503149420040300070b820820201820b26072900380562644c0c2c00030b15078003030104407480d00890312011640e80021a41781408401080c3c418540d030029061075401c0d64039030a900074802106002035001c0c529 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 652834091 1250 652832841 652832857
    0x90803011401080a110316021f020a030507030b09060d05010b090c190801031208190905030406020c01030203010506070b1e0702070e01090515040f0225060617070302010f1b0f021203 80
    0x440c1b8256242e450b02c1900508110801c03c00307510564684040c4000203e9078443d9051000501603500d018200e001020385401402c1d10003894205014031346d4139564000c1c01d80e808a020b41d110303144e4480c40c3c103005026141c00d684680e0805640824040aa40800e008140e09a450210501d552422072000ca0369040c00b480054440c2149040c01c01c10140305220303480e0000d00c402c004001918102007180111000c208046626034400a0100f0080d9010b210f03001e00c900007404c0450540d8985004a8102c1c403c02400601203040e03140001c0c41d0300c800140c4407010100c62030783e548192070002d90203560b40280b40103000703030aa40c2000014040344ca600075039114101409100c000c1300342c9030301484094800480e103042015024448080112020043c45d10a0040080030784840062800c0442c00c544294005d410361521035444a42c250704d00092030000c0300d0342031a0503048040d20704002c40c0d001d60180780c11721107060ba00c000c4c90284604107118110040c000c0301c42d12032603003400305042e64074822058 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 652835341 1250 652834091 652834121
    0x1a10080c0d020a0b0c150a1a040f020708070c06080a0b0d0b0601020c03030f0d06090903140f040e040807031706150c0123010320061804090803011401080a 68
    0x1008500034107100701801401880a00040c8401d40c44100740340d03054200361100070341d640c0190410b220700d410340ca031125002010100c1c10040300c005005072419201040192500454480d0410b103a100601d5044980c584d400089651321500d0340e02c1c1a450b60401481400002002c00380422031454070381c40b56681c80c450040005c0c45d903040b0b076030301c8800d0464010100742c1503001c2d940d000e4949890500007040d81034601180316a42c0c1d0f03102881030040b6a22500300d0850289085001400286c200ca1040103114603104216280c414041c00007240d0b1166401c10360814400105200070050800041c5c45280e2103030320368a001d00404580070320100c4044608a502c48040002c0501081030b43c0c9c02008002c403100004030f0110700010150459415160024070700944d088010002c2c01007410220007440760425003070b400506500300040c080e0150703a82c5225028400c03068a000d5640d690f20518001c0c0d401421641c0313960b520400886826400580c3e075000c5104040080d12040301031151203080c80041e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 652836591 1250 652835341 652835353
    0x3150507050d0b0a090e070509100303020727291504150507060903170f01140108060d1202030a0e030313060804050313030f03120c09060e01090308071a1008 69
    0x80340b0200606800c5610079000021680040f44404482c041d007a0111400d5000f0002a031508040c086440401820300150030b408440074070000e903010910000300ca1568060803080f02e0880d251001d440c802c00f1403128210702e49800d071074074038860000c122100e04401c00036190081c4608140401803000c6140c01911030000c102c00c0c820a5580c145100560040b0f1a10b00c0c01c0c03046564460048501c42c1d9810350100d454540b003031340b41e40d1002d04602d6100074040306a050329454014000000317422824a9814030403603100003030703c0ea1200720031348903800d400054804410030401d42c040d46030b0703104c148060b0005404200400032410000221500f0044086d8000c0c14a4900300d001c4581c00303402f034401c5540e40010444402d01c0011411280c0c003550150014135070b40c60481c64080c0000c00603410413502d040c1000d142c1041d15420480c40c0b4103c80c0309042201002d03503020b0048400c06426003005025440101c0d0300c4007441415043c8414491105040140301e480300c140800010300144501038080d4006 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 652837841 1250 652836591 652836607
    0x90c140d0b09010e0a18030804060c110105100e090c0102030301091802030d0504060219021f03020d0e011a0402040e0403050d0b0909010c080601141e090301150315050705 75
    0x100004051010309a00001001c044280c009298900281d11825400c45120244070384524a031050340b065989201440e8022100d56501411480000300040c140c2a03a804446200d507000361031003002c121405008110714900003550700b2001340d450081b102030400380c13030001d400984002140d04010005030000e6040d80c0c030f40403c0001901c0c10b80d19a00a4484100034000141ca0801910540396802d403074054444d0300b0400000c6c03404010900d024820300e481c400c03107005038a501c008083c050b2140fa0062040400000094001e031181050080c05940341085290040da4190301040c0c10741800c20300c10b090300e80d100041009030b0003540509044140070001240009005400030030306c0014010020540030342a400203810200221080c015a035110600040015800240035910140074200440f42c0b0080040c814028040d884100d04007840450301011202800410340d44054070081c02030200310506203070120101f40301c0c4800c81d0210741034082010311032001c0c0109440341e0309aa483d00e00b09811303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 652839091 1250 652837841 652837877
    0x507020c13330e130c03110d1e1703091c090e01030b06122e060f0b212809150b10090e060108090f0f16090c 48
    0x4615400e40768841c20314404082022a03544100b1100502400541003454401d00080e003100c000e20803403e4001c014001c0c0d0010b40c007a242c0e902502c0d00100c5554407130040b000404c3d62010f070b8800150000c0e005004020022000844031503800d031140100801005404040442e1400b00f6154405079801403034940302d00504000303a00b00d01d0748035480d0464170103039140d425600c1240281c00c01d0701c8100e1003034108a07050400006121844039640010312012200c140e00d855410481a00d40c8000403102681e10013480b129004100640707240900c0096480d61240d5070040c076841107000800c0b54250b83c002c00000101b06d40d00313901c5001c0c0c40790403080c90b200203007041d850b41c0421080145210b07560809200071070300c400560701081028240000c1c6002004007080b6446055007545010846103103002c1c0b0501201224803a0060301c21308020155071100302106040c1588090110054815050312580051001500c420103400c0b048000d41c5190311348240c4401c0d03400e101c2c10303d40030880c809a00c003940b8032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 652840341 1250 652839091 652839101
    0x10f050412081306050406060e01050f0307060f0908190b090d0804030503180d0c06110a0e040203090703080c0a030f1d010f09080a0602041805071209060216150507020c13 75
    0x4a40040c0e14100f07103403641e0f26003c0302c1098030300396400c41d507614043c054580c81c60003903805400102d51103d290300c0001c0001c0d542e0302050140008100d00b00d111480d04602a00e078031405030400c80b09a402000500f555203400030003800054650145d0a401300d5100c3c5808540e1100d4031109544400e0740d0341e100d8a094445500161504000070b00d58002100100c1040c050740f80400a20b54071461440060f0425900f42c50580074000b8000c50104103110b401500003080708000070040e140940c49648880d0700d94100b200c180c0c030160048600150302d10200700e01107000a1024440e0720b4242d100b01008008654210000294221101655189801640c0152180f01e626140ca01e440110192039199183c20300c20714480c2210400d4020909001c454100f162007807003007071a103400f00311514100900900d1001c413002c01406569840140c0720601c400c5404035850044c2890100c41028603070f2808080d1050750400d41487d861524010603285403000c0384408c0200310003004900800c1110700b800b0000c02c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 652841591 1250 652840341 652840351
    0x70c050612130302031227030c0c0d020d0c1d0a021911010905070b120901020306010219060b0612160903050303060f1809150f0613052214010f05041208 67
    0x11005100c41c40c0c071040411034052003250305600c43c0c45640201c00e64101c8111001f041100250800d120908105000058034032102401f00c1d51000318071002d00214207004540007002e0b1981d00c1c04140414411030a26010f03c448290a4843c503003a91550420422401100700048013181d407020304040c594070840c00045540c1c1d041000060100d507a43e41c0c50f107040b40c1a40f0449445801048410520510300d1200b5444100d040c0203524620300b01000039118010010114024441200d288080c4071040d8071420b5010000341a150b03440b0b104600340804064103c0d4500c80c407020168195410340e100e04500022030707502100840c01c0d92075203400c00c500c816009040c3ca800084486503514a006000580d501980700f034005802c078054480981c504110000306034210340f00500c0244915610b070207440e440001d5540200090580f5494500d4110002c110b0103020000310b017031031000c184091000500c0c50462805e000704192060b2242040c1901c0040b1070241806200f441342034882030103421459440 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 652842841 1250 652841591 652841593
    0x1103240a05190f050105011d09041707140a1e0b1b0f0d020702030601060c0807062d060e0a0c0509090907120f110604051e130c0203070c050612130302 66
    0x20744030002d0305811603d80c0654201c3c103586400040141d5600800e012048218000c4040e0400982001103011004040c0c0010f02030141103040001828a8106981010b82d0026400040b0b01c41da1400303550700c11003110251110400c8e120b40c0c500036903030b40c1d03800b200f0f90341e000c046402d07aa554004901e4051980c4246100c2414080260910700c0101d00001d140c0900c29044c0161544214010b1510b0a001600184d0a1002c240d111402140903001a208003550240703020800744520714207111602580090580c400d6070034840f04d2107655440c1c01c500300352500202030b40341d00c0e83d0305880c1c0f00a0352100103080001c03400070041043d4500f00140f4455110b0910030445e482c05507140d844100480038940e06903081002e440c058010422940f200003101401260081d0903e070403c0d00040c00d2458000c2c54803042d100c4072000c0070554407824012100048460780401c8141c04982001c2d44070f6000c64000c40b0006030f14000410640b80200c2a5401d01c0791280c5a1403142d500e1100b00f51008171800340c19015 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 652844091 1250 652842841 652842871
    0x1e06010908070e01030b0604020f0316050702100c030206090712030507050118140f031e07050a02090907060912030e100504033206190b010909091103240a05 69
    0x1603880030001d150051040ea02e00f90038075855400e01d19840c0d640982054130960040050102d203100354000e80341c1010584034000ca40204003d01a960780c0f0480c00000d4002001314025148150042517840049010745c00382c038401d54a0702500c5866030b100740966103900c510210a080400e00c00d4001d40304051280303000113202000d80e48049202d50310808111424030000039620b1028005010501020560300019414104515038191040d01440c0c400b81000c9004503e600c207024081003849841740e0003420080080c20076096050721840365018200108840c454001020328803182c0410301d0704d0b019503a20a003600d1080070011485c21204d02d52040050602011010030511078051340d0040441440076000181c2d80300011400a5400200d15640c0144081080225104003001004084040001307001c2190f5801170b00d170820140c0120003240d1400000e0750070080d491f0851034104904408441007041c2036142c80d03c141c03a002c0c011203000404000859107403a882c0e00869048550200c1d0343c00d07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 652845341 1250 652844091 652844099
    0x1906020409150302010f050f1c1d03091801031101141c0207020a06020a020d12090806130b1015030c0504090c020105040b1014060a030e1b181e060109 66
    0x695103840305500d5140b040764400c00031903030004031100d0081b0081c00c005050050030308441116015008a0702d0001c041c0b0892102d0f04102d561100031043c504032b00c17451415100303000c043e41c1d03030304101c0019010780104054400300c100b601d05010304803a400401c003008829880011500c0902611028001c004244a0090440781034041c000d10b01141d80b0700143c892001c1d0041084a0515500c090300b550030900880d00940c031001c41c3d40c4505134010754034104002550108850001056015800034014101031215010064502c131001c64020a540255902c806c8955601480144038214025400c03905a803c941c0c02034010341d807110006d061450410f5900d07091501521100011400180d55580401c03040202c00c00d03e05402c48460128030038100d040c0000210490000e0b0030b254403032034ac0843c501c81c0d11403190300060800c0c0c01585c1030703405d0380401c8164202000007941c100f9209920320943d40030350b0582c04014903c102e0142030320081e081c51241d07a401000c50007030a03450401001c0700000c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 652846591 1250 652845341 652845359
    0x313081b1015050112150510030203090d020d08150d08040312080a0e0a030e04060f030803010e0604020913090f05060c0a1215060f0c05191a060319060204 68
    0x40103800d580406005811000d24540c0110355020350003102c0007050081c184600d980c0100860800215201d0008420f1110b10714103500311030f1a80051703800310304210407620665058000d03500420701a0120b0740e40c0884000107a844401624504000449400028800703031a80b40720042c3c2801c0c081e060700c48145458854003155802034100384d860180350304c0c4955066a010070129848407180c2420008030040c0c44045440b03122480d07015042110103481d03841c40b560f8a510801c01082400d2040304013680da4070703000c0000c0e042403141c80702c65850b0f5400505a07041c00d00840340200310003842d001500320015034880080036505070680e90051040d91202c0011420881036000385203400342d4a444901005004241d0595043e41826131414514141c070043c00740d02c61a02a070b4018103001d400c80c0d2980c0c0f2700b141c3c0c10317000e810041c000307104018165000e1081e0704c80302c1205500580c0c2000400f01000e40040000800f603a0940e055032041e8055041c400388242070581a40c452840940703015501c003501 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 652847841 1250 652846591 652846627
    0x70f0606030303021207020d0f11031c1d030f070204090303090b04030315140d38070e010513180902040204032d1709151c0e030f031308 60
    0x1c4003c240c0c001824001c001048620982c041001e20003055816002503009110004180c0030a05001d011102890b1b107640900656841003583e00b140080c410a4200394005040b0201d0005044882e02d080b542c0e50f540084111401002021a141d282c02e280f9402d000c02080b01080980416a88941c2d2200049007902614010f6000356000700b140d07020886c108035551001d60015540b03e0001c1c059000c00d45855010f05002508000144071a40403040d1180750080f40f010000341c5102c2c40159014a03100c400507030f500800f1f5a90f10201c03800003550066030f40303103d0f181d080070781c8240410041122940d000b410003204041c07548082030444070baa011806070307000b942089402200c0b6000c4082010b441c900300c400702c144070281005100c446a2541584584411100b51a10b8030004a0040c240c84600b8091070240d2000c142a41e03c0e807d42010340c8414006000341ca41d854140442d89440c1c91000007035034000e00c2840405031450315079883e0014002c106907802c80314564180b141c0e0704421900c3c012 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 652849091 1250 652847841 652847843
    0x6020a032d1e031e0c09080a06150b0c100509161701050a05162f030d050c0c190f0c0815090a030914030f01051314030405060f070f060603 61
    0xa146a1241c4a141080c240c1545502a0041615002086880b1908078107103401840424038001000e105a0104884902c11b5802080843c40343c070044004011a540c004000349643da0f4002c005240c0f140c2a0038968400c04039a2849a071104590032038980c829401150406009000c40d035000004058101d48030321194090038a800c06402003004103d000e014455002d01040010011442e008801c00c4403144000810420841c0c0c1269800d000b80904200002d2110031715032446030031000f5540681e5a034000761620141d981080f01144045c0c140c0750036a00549560300103450700c0d20204078a41140ea00c0b100c01690b020a50502c48808501c450400c0d1000e4076109000c3c00c602000c05890b0310000d580600100304507400200454003180d88082c600060b00c3c03034406090551008200024a040d03600c600030003181d4a844244a4207106802d040c041d024410403800c0c00e5110314116141e201e0185101e2160041420481d0941d003056240060807240d2140c081c200e50003404d034450720115517044c5c02c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 652850341 1250 652849091 652849097
    0x2007080c0102073305040911040510020a080d1503021206040506011d07030209040207060c030b0a12081801091203090315050403090501050d020909040c0603050c030106020a032d 78
    0x5a08041542e042c80910040c00d2284c00305401d013200110480e00034414407140b00c8180913031a4a4102543c495022100200120b10091151000c03410401d0f0a580c000c0c400d441c0b00d0b070781400403484524004508280e103075400207185410211030407140c00c050960001c541070b1040718484044016503403480c24500200b030f00c131700801041c646841c00e207141c01010f03001242e8040540e118900c001c0700b840c144691101e11403901688445054000c14064014100020100c070304011405010550540c010b10145004a51310080e680e0b8407400090710401e002c1e00501800c0f01005038160390128245030081508041c5003003010340f40c5d10082151804114030048001400001b010000e01c403000307002c4400184107841c100310609056402402c1e2510713a204a5040c060045002d02000c5401d5060b50420400644041401d281510300303030020840714010038001c42c1c0780402141e4440d402c141520305988840e0024444070441d62415500c0d6942d42d140d144c4424000b541b51b000d002264104609441d080791 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 652851591 1250 652850341 652850353
    0x51506030c0a0e010203160f111e040615020601031b03080714062415090406090f05070206220206040f0e160219030302030903090301060b0a09090c0f200708 69
    0x20000400140f0300080403411036100b03014900c100720f00b00a0302c070280c941c80403154140c11750614245401611a18a40340e10002d6095420001d100180103120b00c01c504860802201c4d488103c90581c0039005100d0100590021006000080715643c0000000700c003510304d4070300140d981d90b450006a212080441f103100d154140e248240c9000c00156800c003806007000c600d03003046100da207800c1c440040c585610606851a03400d510b4252502142d01c24100a0414440a0f80311410701c0040c0081509003800d0b90324200024a000d4400301d0f0b024081d4030506100344100c40303403040300b402c4151610000c2c0e90160003008001981c030b406807241e00090040003441011807816065540001c60324055040654019890180c4050031201e2095521035040c00e0042c1c0702c0e100e040301d091641c043d01d94215019842c260b00803500e4001540981047c80307450343c0c0d00018684070620314040d10100842500030903008440c00040a001d0380d440907014020903107201e404038840c02d850385030580e50352081000ba0411 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 652852841 1250 652851591 652851607
    0x8180d05070603060b161506090c030e0601090b150d021c0c020d080405061801020f0c07030c090219050306010e0a2c011202120304030b010902040e150d0204051506030c 74
    0x580601d100030900c01c403174641081b006c450105100c101800700105510f102c980401d0311100c4a91201d0043c0942c064104590a07040e40301800809040854500610525000184810f8513004403402524054400303050440c04a2262a81d90881717031081040503001e01c11a800c90100384000018016481d10105403e02002c0c0c0180c1003001010092080091140402010900000d4942e070010110002d91450041020101c0d00901500044084400c1c0004209460010016440d000e480c0280d5011400e5680e07401030004030b1062044200d0340300c41c03c1050b06c0c02540140051035010f401818480c003038603140b02c002103860075107410401841200210b181207501d21000c400e400e8445859240043c0e50400c410303401000c080340303402031242e2201c4421101182d03050044d100250f42c0401c5c00c01d681d503120701910b070181d00b00c0e0085c3e020000fa1880081d00705040c0c01034068026902501803e00b100740d6400740f0000e860020b2001c0c2d14103544030007a0041d81c49800040d0700c01c0c8030368031006842d4002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 652854091 1250 652852841 652852847
    0x2120c0c041806090f20010c020f0109120605060a150e0402090105070f03030903020d0207060905150714031e2b0e030a200609150403140309010b1003061208180d050706 74
    0x45200d41103524109082c21b40101d0760403602c03402ca01501101c3c1c051400040d100100d9100c1100d4104800140d4100c3c039440821480342c010a00038081220381b201e03115102d800c0160900404042e1700d001600241c0d02c030410341041d0b40244130410062404518161b1143c13182010b100c00e01c0c0044000980d1008a031040c03550600c00001c030040a44047e03d00c1e00c2c42d016000303200c0582d0b4000c2c0ca11901849610500600100c0200d80140c2d0f48645480e0881c202c0300ea00646903001104003100c490702140c403c0012813005811074440031810728010303860a03822303006010686100300e210410140c2e07400c880106400300f08017074180c0d01d003a80d03220703901d01042c000c41070303a42ca842d210300009950000090066000021503400c0c04d90050030005243c681e15070404580c25203102c03008052240000040c0b082607041074110440c8036100756110104010089000c408680140c850301540c0350240d0780250020355100000c1c03510000e0004a8030110100100050044544100803101988030304800c0101c0c2d50 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 652855341 1250 652854091 652854113
    0x12050d05011a0a1b060c021b0d0b1602012405040e1c0c082502031e03160f020a060503041401050402030d031d0706080702120c0c041806090f 62
    0x101c01880d5030001800c40d045140342d01803480f5070f20a00002c801007155210034a443c000c0026001a01071005060b1003c02a4031416440c5000b04280044600c10b1000d042c06d4480703010099111340450136541e11184d9035524000124222400c654844e42c21041400c11146070780403000014680c0c1d840700d8909800c0000f10703072070f1242c0381d400b5401100e124118071844940c1641c441c030907401c0029401e081c510300245903210f02035004401107066030b200381100d5501545c1000040c400d0b07081300c0c501caa00001c40784001e12008007000c0961310400070070040203d03941440da203591003090f201e01d120945500284503010503421102c0000d0000c820071041c071156607444006042c401008000c14142a008681c481c0f40010303448082c10344030036141000040d5030240803420080002600c40d41a00e40b44c00400b416800d44001d40140f081c1c1c0184246034103102c00300c82420305132400400000c2d0303034482840041d013080051800180c0440d00c0243c00b080e518080c4440c124801c0c2500c1c6030515007890848800700d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 652856591 1250 652855341 652855349
    0x5071506050a0f12062c010605040c0c170d1409160605070807020f0f1c1101020d170405120714060c03070804020909030d0905010912110d1b12050d0501 67
    0x1003a54800b00b0044004c02001c2c106160040000304041c0f2209030195001d01c40701c51000d00c3c07801d006417041070015041d40440f040c0c90044a0902c02d903845024212070300320b40140042c0c001c10311004405c00740401440104980b901c0c03c4404210060600b003d902c2000089540e550117070480c400003418180c4003006440509007606015040500c5074031201103502920030700901400c40c25078600810333500d200d02c10400450081600508400101842c2a0245090f604450900c2403034121041503002041e2002444031035a52040a01c80d0302d0391800725030710003800640c1c003405044480d5012421801c000c200003801027080c0c1010589969034146092001441c2030b450030000c0c010f000345907501212603500550100c800a07416101c0c03417035a5003148242501034101e246081c1d660741c02c000040d080b0200c545e00400b0058048850300409458011100c1002d0310f15030004900030440d03038000d8000440203981340d64489201d032074a503903503607001400d1001d00c0301013000403e5075140750156000302ca000d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 652857841 1250 652856591 652856609
    0x10020c0601032102060f070c020904030f1206060c081b010c08161b03030b0a0e070c1109040b1801090f0f060c020c030309131514030f06040f0b04020105071506050a 72
    0x2050f0300079100d460207094210100b00355004624268441c8020a1950f0340041c80070301241007501d400380030442c00050100c08660f0302036990300c003400c0910455040b0380b01d945508c0360a004036602e012807648107410107030180340d8010f10030401c04030921030803510f001103445256141c184907a840040c071050400c000100f0500b00d1545000454404117410f096525083c04110303102034034001519001550817207020f0b03030351100170040101e9001414088041c01103c1c0c0c542442c0e4408103111070084e0480c0c02410b640009404503201d083e10b401c00303c40702c010700c1000040c0118145e0325800020742910307096034602c200d031021109000301c0c5c2c49040c0c0034a03194002805461052004651240980034040380701e108640d40c020300141d41c40c3c0050014418101c00e000c004c03034480c03040880c0340004891182c000d114405a40c48101c0001500c140565001a989000400c540d6a13903200700c0c0e00188100d040007000d0050400042c500c21a44075070710f40072280483c0c034500301001d100302030569030b20034892 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 652859091 1250 652857841 652857893
    0x8030f03190e070512031c0c03230f130f06090b0106020c0310020c10060308070605060312030123030607030f0e0c0d0b0a02090a120c0609030809040c0210020c060103 73
    0x20b2081c0008005003122401e4401820840a00480d641140241c0c0340c003400074890714002884506c601d9100b01c58603d1240c80c1003080c41d0301d2230800341200c0c003114207128406c251840454400c17421111840d5000c4413040d2115412200f07a60b84c651004140f2904440d0b036500c541880381080845075255014110610003041c2100c003440000317a40d078468070144c1001c90340c0003034003485a10050040c0c94480d82483c00a012456680c5891140d0703078442d030426604c062814001ca44e0510340840d03841004040984031504503401d2404a0b0054443c401e068040580a1050811691824040c180c407034032090310000b6070303405014030460a03a81340030b5909a039900040468041640c0300801500300c0741c1c007c10b444809039114130143d0001d01c9000c1c40305074422100c2d5030010f04807090010000d52984540c0106c0b04030399643c8019550703080c103400000c0095030240115210341c00c1c140d1010011903090710482d0b20503101e0252410803a070003000c019480d500700100600512800f0002500003661001d400c4107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 652860341 1250 652859091 652859111
    0x1805040b0402010e0a0503010603050a02040f0b0a031407050d0b0f2a090307030506010b030a0e070b04091817090f190608072d0315030210030c050408030f0319 70
    0x8404a0020070003410f01c00d0340c00030040d664440d110410040d00010b0000c1001c581c683c1000b81c2d8440c0c0c087c0041f031080781800364954500c1e101d07000d808a2007201a10b2281110300316952a401c50748403000c107643c039103e02c610000325640d55500b1104c1d181c0c01078036500b40504103c0c80015403000001c02d0140310800d1001c54000b40515900900c40010024140c03c5d2a000024002403c0c03000c40d81c005131251041c60008501041d00304000d501610301080c04000d041d8504140a4403044544220705c2401e4007440104040c0c8082c0c0c2201007000950640217050b070420707580310f100b001e000001500084134040303060340c4a81849407044204082c11900d0700405100d180a00b81070004c80d000380000c02c526800411082030182c1c03045000c0b54440680c4600c2c0d0b010806a54001d00d1110226000007400d0103c0380004041141c01d80382502e0300545084203440d8006402d0700900310b406494001c1010421000070407030701c01d201030003e05d003a8503078281d80d904000b81501440390224544101103490004221 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 652861591 1250 652860341 652860353
    0xc0d0c02011b03140918010605090a120b0c030a0f1b030e01020310050d050a0f050309040b0603040f140f100605030c120604020f060910090509010f030b0f1b0a0504180504 75
    0x4c1198000043c402c3da89034500300200304000402500c40d42d40404d4203001240491700f0801030444800251242d2000ada99140501c100e000c00c108050f00c64041c600c0405c5065517081700466000b0364001003c9908402141c5510031030302c2ca250054942416140f050300d8407581805400440c00d1004025421402c1c43c61030110450311038440c40d4400d0040d82010300401c10140030010745e8680003010742e16440424141691a944002e40b0540306924010950002d03140030001d990003582c00940c0600c07181030385c3d51050407881e401181c2080c02e2180103110600c00c0010000e880780301401c50700201e07269207050141482c0c8118140328621a044245820106080001e0103d600c642c044800f20300d55803594011400502c550500c16400c20203040107101540d8000040c00d0495200b5641180307242e0340c1e17100c2c10300100454000100001e1041c00424540e9940c40d4400c1d401c01c0b04118690038100405461450550000d420f10740840c1380850204070b08030602100654141010708240305a1600383d8901c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 652862841 1250 652861591 652861607
    0x60e01020c041a03190605011203080403030903180b0c0613120e300607030524060c0d1e02011b20030417060a02130501080403050c0d0c02011b03 64
    0x90b801503940d490240300003514014012100034000e4107170b0301780b01c2c50012021001c42c3c41c40b505803202801d000000519410621150480b80d406903070b0035030f040d2216a01203019007842ca0094080101c48000d0b24900c0368015604001082001501e1350780d035504601079414020b0080c40d0044070407699520b5000715035400f440c17071a980c01505d055001c2651000c00640c00c0009120b20058407407250342450400e1154240c0c00c9184c1403501c040b1096551005411001d5801c01c0704c12003440d01c0720241d6401080c0246104202c115001001300b070270902a030071700034604140300400600240d03030768200043d0ba111394110903941c0b403420710003031001c1d07901414412002003000b58940d0030000c6228850801010150030040002d020405490703585940da00750a401a100314a018054010040858412103540c4211403a00c0c201e960040e01c0246040300544400700c0c01030080e420301c034003040002d44500f014000710344140d0180d00c4030303080940c030340c000149001402d403c92884a48002e281d03d003ca6081882 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 652864091 1250 652862841 652862863
    0xd030906080c040b270f0f0f0a0305063303060c090102030c0d02010501081204080a020108091e01140a0221070315030b060111030f031f051905040501060e0102 70
    0x4140350545442e80240c603a03210300c1e40201e0041c8030100f607104100c20116040141640072082824200c0326220400101c801e4401d490355020880c404c081c03c00f401c190500341542c5100600d2103042c2039681c1c5802c1e04104c001c0b0788408400b02c0d1280c6002c0e001c4903003450407074262900f0700416221400a00801c0e502e54001e003000c507000c030000c034030548075a20800464400c45a030506aa9214140d481d000e8041c1000707000e850158000d1003143e403180c240c00c5060714201d8401d04020401e1940f20f8005445040014001801900401c12000b0b03d4a0f034900120b00354014640000600c1e0ac2c50079210110620b000d0500c00704103004102454a1401344074008102043d181404d481a8403101425001000c0c0d92000350440b8551240002c10311821140c400d104120a072550401c5400c0710810544900c141c0d41d0500c0032000c21b0010440c1c2030610426201158002481150702c0c54850f0b000829501ea80142010911800601840241814001c4500620641c20901151108800080d40362494441 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 652865341 1250 652864091 652864097
    0x10302120f100f090f14061b0409050402240702090708070c03140903121308120d02030601030204050a0b030402042711031612031806090e1e09030909060d030906 71
    0x4006680c4602e81d40719000d03082d48081c0f01109505607207000c510758018911003503134a010341f03c0050100b480c03061b000564281c0c19102d2920346820204104001c1030301410507030300002d1448910011030008480d18103100f044118040e10b4400368070401ca618a0010f21030f1041100900074410010f8210050000c2645d2500784280c000480503a40151405016030302036140c41034100715601c9610400081c0341880c07071078149607a115101d00a2030b07640c0d00941ca5080c0304070010002e9403d14000c0754050740e000303001498094507040e40e4400040c0300f801c503600880017824000040c081146082c0c40303046800688007068407450608048040845120281d015005940f166980b044581d010300c0b548520018408100b941039071241d120070304a00c1d04070b404501042c0c80c401c0d14804101000c9201046030307565a503211503607041411000d07000e24043c0c1180b40c0c0e01243e94a41111801c3c40030464803c6052000030364483d0b801c1d00800c0360202c0c025096070b000c1c0b116071240e040803944c010031950994410b42 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 652866591 1250 652865341 652865351
    0xe12030f07020f030a0e04140106020607050c10020f0910030e030901050d240f09020414120c03061f09150909030c060c0c0309080c010c1523010302120f10 68
    0x1074000d90a04206468200c0140400609031085641106000c5a400d40c1070b40c080040b24084200c104032000300380100c00140c1d108000084a0f54440e00041c0056011038050b40c072000c0c401c4502209903004104034003502130b0701154030056404c0074125a614032030685003d009291075180c040d9160711400c0341c01410400006000c01c0c3d00d66440d040101c442900001005140405101c085401c00d10b5001e1348002e02e040724400a10702ea5980207540607281000240003031641c4a004000c04150070f00101081409881003151140d50203003d00c1d4821020548140401c0c00404280120f1200540104103d14039240c800f858086422494000782d0303014020021316608641800d031501c0c1c11144c0028503d038108000303042d00302c0d80f09202014451198590301102911001400d8640ca101d10010307002031082d00390200030551144010f040c59414072800070b80403041c2059142c40b12401200080705a01480c0100210b013480b51b504000f50180401608080d05e02500302500e030701e015400a8961a1a5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 652867841 1250 652866591 652866601
    0x501030203100e01030c03110d0305040e060a09020a0810080d0c0f030e030a03030b0f0103060303080412050415020309150909010e06031912030e061e0a0b0415090e12030f 75
    0x2112015014010340c40f90a030080d82c0d2494600040c1003d8001140c0003c8201d1442c404c505003c00304080340c60385a180c407414a0304111504000100c0182102e601006e2003100085901c030741d1004040200313540e90b8403251450510850044c4030a258003c100390b5100d00c403003040c210782c0103242d4a07400b944800c0f00e10003984181011140c0000c00ca110315818000c82403180b00701601039015940b504019190181040b44032070044d811100720344005000701d85084000743c0040d2000c20004050320150070030743e082c5903c95001c002c1c411642e07016400944e000158625562a14200c02001d041c00da1030b41504c3c2903078400205190902c103209a482c0c10305c40710041046a034040c013055109003141012503034010a5030801c00200d004100409011904e01044010b0521010400510880b40c01e0300744420070b5881c0a0540159000910b521169a80c5002c5008a0f90381d50040c05c100b420310003501b00e181410045001d0440e04d59001440c03d5502100d08072500c0221101130300d80c41054110302c65425519 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 652869091 1250 652867841 652867861
    0x13020d1d0d0e03011b0f12140105040216051905123a0203100303030510081207030203090d030509120d0c150915060f0b0f072d05100c0807090501030203 67
    0x1900d40b140003d05c010781c080d092515404040e20244201c50f40c0c42c4c018071044010007008075280d42e1004d021103c0c90700014801818103070000d080141045c80c40c03103200c0c0702d0364032900d050080c0c0600507585510b40d030b6004014808100402420704081e0307580319140070f0754003414442120300b03641c41d55011510305544c04114908400306940c8480d40740c0c402c0d0360300e2500c2c0081c41d4111206000c00c401091404003c1076030b05528111817403e039042d180042c203d0100f03030038030040160440d1808030110300c420001c640c090703181c11450000c20703840703926081c0d12170703016204020407080c00b0300030342d00554042107500e4400b5030701070308074402d080e00000402c40c44200480ca44016003065030b0003808074002205110301c4103426a010408841d105518140c1464540b040110389215482d84502c86050a01c44d11012644111800390210f00352450503610102d031040840d8400180501950f25401010000d01407400500584203e541c0a01e0b00d0100c7c3c0c03601880240012656008642c101036000c400109050b40d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 652870341 1250 652869091 652869101
    0x16050423040516030e1b0f21161413110408070b0a0807022b0311030906220203030306040b0d02130c02070e0609040b0a0e0f030913060b0f09030a0213020d1d0d0e0301 73
    0x200d04040e460b00407105a0f0085e0f5102102204818040d20680f0004ac05a4040c012411032000c000c1206403c000580c040902500b04600d0901800c4000c02001542010401c669030040600700340064aa100390359001d02021001424038041d5005684206071000c2800e890a1155001244041039882c1c10f0004400929a020f490403c0180010501501d14400501c0c28440c0007070745190440001324510a080c00c114901000390160f10510206e41d4610305500140d858400151003070f00e841d103994001803140120180c244802c259101d110355091a07060281c400946065004020181002c001240b241d0b5001000504503038600c202003503035001590007060441076403d01700d413005200c140e0165101e611410915101390b10101412544100c0f078050107007100c0e42801c0720350134041d04000320300f46036003d003e41c41c0d03050203140302100050345c070810504194100c040c00180c880592178005000c44071030681140c954142c0009103810440d000603149016540ba14140c2c0d05d482000010034007400b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 652871591 1250 652870341 652870369
    0x30c03040b1906030b060f030d0909050a0902220b04110306010e030106030b160801081617030408070b040806070309150b03120703051216050423040516030e1b0f 71
    0x5080c030a000090003107400d02280a40007c8035820761a80b1003e081643c0d03520134404100104051210401c02e07445581e221a9000011810115212040e0707400151604114800c3c03180c040a510020350410149101d1344484020a440400c2450319412240e20b85010090110b81000220310f00070703510b5142904194011a844240c16041d4108000990211615541480c00141e0141d00006400300005810b040c8184500c800f100e0060600f400c190710546144540c18151108110024405904001e4030000b0010a07a0054485080045031814400c1c00390440e0201810180b000002c0740100020300780a050400f800200901c03030402007410408201c0030442c910f080403c100084c15006030042c4410103050207980115600d280301101044928008400010070a200500c56440081020110311041c41d80544041e604100002d05a81c022601e209024454080d00701049401d0301800440f501e030380c805403485009120480d07150b0041c0718600c17845542107841c1c201343c640311480011809 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 652872841 1250 652871591 652871641
    0x17090904050706030b0108010f06050c151003030e10020c0f030106030803180f0a050d080a0608010c0c020a0605090d02100c0b131a04240204080114040512030c03040b 73
    0x1032420741801a200c1041d8030809012900741a02810a5881440024182c1c0e00740c4a8000307282d4201b507021241078024190081151042c1502051102ca95200c1e0714410170300710b0303014504903066107001851071040500c003034022840c5400da802c05c55001301d80c0409400003038441e51440b1a00303600090241405600c06814008000b00b4801d140d1802d100c01810504107204440d6820010395100340d54205590001e4006c7e004035014081706c3e84601c00140d04105801808514035444800c5c031801c4400418440010030809443c03d411803d020103030000401143c20203a040900700d00102c0c60201050100910504084ca03981400300e019488400400c1d401c004003501d5450f200201c11240c2a10f06070035140d13980c00d58031070540e00501d040c1c294829070740715030300c0340428498144040456180702012001d56800f408003040003102403050404040b1040c03100038060a281c103041d030800b810f455108481d07820070030030030034040866003c40c0e4206501c84100314056407071010b00c10742310000300c01c3d01401c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 652874091 1250 652872841 652872859
    0x122b0e131d030d0e0303010303020a120507060515120d020c130e070b0705070803030415050907051207061d150f0931090203060106031d0f06070f0512041709 69
    0x4a101d00002400300b0f019041401c0240d51044107440360341e4002440010300592084c1641d0000070202d5441ea02845d056041860800585a40301070551b0b0b004c860262520340b100f220007403d442e0000340a96180300c03a03406001001051078000f91144410301c0500c0c001e0100410507800511190b121503000c0300fa50341641c01040c1c5a10106000d640080c10a03229803081074004240000b01004490080d0781c88031000d1040c6d0610400040901801807031000107008a4400007607a0b02c4080e282c0040c1351b800c5001c0d140c120700b0024054501c041d0b43c0b070383c22840540d901300b510881d00e030041c45501e07079288007031000c0e21003075011100c82c083d00c55202c0e101d4000452003e032544075503801e520031518005c88400c03110480408210b82048030381e500300182d0302d81d015500400101380250700c221940d41c02c1c950382c1ca07074804500034420314000658102d4221640a41304021001c0d0344103901c0d29503140d4602c4c16510b41203016410104c000d90180000d4000300c00c600c10102070704c94039421203a8144010302017943d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 652875341 1250 652874091 652874141
    0x121020c0102090a0e0705071403190503062701031b1e2d05040e01061d070206010f1a031008011a19030b04110f122b0e13 54
    0x4040c0d04070054050044a1503413000c50640b42d2a1410361055000f50740703442c2001c4a584400703c85018295130380403580010017618481c180e60066038117400002392542da94a052540c140903598001c40460010481c40b041c00c0441c40303000c0811340c3d0450340c00c0079180341c44011291074032408000c2c584c01584542040e11101c020f40601415030021680703000341090007141e640c05540c10030078499080c8100e105800300709105510307107580300392081c028400000580a455035a01d0225900c44628007980c40c0400f0100301c0d2107581001064050005c2c8028218281d1410075400340400828424500540000c80010311010840c24100002d1501e00024010f071180d8041c44190000d10070700341e6000c1c1a80391040410104070141c5101240e9000d1100c80003030f81e0b90748508410b1840f0354400c45c1d010411018038241c03503940345c008078601d0021801070441690071018012900c84403621031318081c1d00d0352881e0740d0410b41028000c0146602a25130fa14068010240d4100424600c401403a0424600881031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 652876591 1250 652875341 652875343
    0x9030207080d080a0c08090606010f120c050403020f10050a0f0e0a030b090c090907050906031207120305070804230f010e0706020c120703150219110c0901140121020c 73
    0x500513180d0f800c040040524100003101e02035000c41d01f000c0c06034401004159154424442c074041042140381c03110305011061070213800d4501625213180080c401083c14015442e00e031050702041c581c1107602e580020040f100151040c060710b010321040c41181d119049691f80070f00c80f40400d01c90f009080007100c1c1d480303182c03c02c00d442c415102803d45211700484c0300c1d02c900300054550700400115004110680c940700070000c030b6600007080c443c1c040c0501d00900901007480c03409060074507c0390a070b0181040c00078000804a481c01404441081005018400820605a0720304103031405aa035000d020896404510b00d81628410042c03902d42ca00340c8038010019012074010252480b580c01c6c3c41d109001001000083e5201c94542c00d081d4100b00700400014000340041c85410512000160820200c3d0456a80041030801420013041ca21442030b0144035052000303c3e08001f040701d10304100d5040c400d903100d038110304c0500c050602c2400c0f8040c4e2009915010032042142c8001030555880f154200d0781 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 652877697 1106 652876591 652876607
    0x302070806091c0309020a090203130b09061e010503032a0a080a092718020319020a05030a11240c0a0c0b120a09030207080d 55
    0x905280140718042c03003440090702402141014036045080c41c40400c4841c81010300e888001001a92030613603130300c140d84542d280141c0360760300e001e119840c07030000c54400313040a400c2030f0410686100000302c003486545c8080411813a9100990700480b041c03421700440b80e140c0c200340700070102c0d1010400da08009901081d1100c1ea0800e2640165007408095442a503900c0c00001d030111201350404011401869030b0b404003105050aa188841c2401040040380e10658581400d080201000420300000301e070001c060f031300c59600048800b1240d00001a04034040c4901d0080003504e45004500041e0058001c410030400b003100d182000390402c8503005585117000002c030300c00701104a0b00090010881c0c4407004107440b044c1c0f400e0040460003190304c5080002d4003004008094034011901941000001d040801c10411518003139051007280e400c0081207209090a00c1340140d40007070300c = true := by decide +kernel

theorem cover : BRFrame.Cov 652697841 652877697 := by
  have h0 := BRFrame.cov_init 652697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 652697841 ≤ n) (h2 : n < 652877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
