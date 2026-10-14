-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2833
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:52:48.225027+00:00
-- url     : https://prove2.me/submissions/ff2b199e-e507-4b78-a20a-8788286ba051

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 509352517 ≤ n < 509532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 509353767 1250 509352517 509352527
    0xb092e0905040c0605070c0b0f13030f050c031b130f06170c040612021212030a061a03010605030c18030a030507060c0914040906022104020a0b040f060311120106 71
    0x1c2e826100c0e800700c07040018100d8815001c030782220350021070300c01c2042c5c20401320000301d52100b044540244414820144103038a68040400110701c11b0140f1301541e201441c0c10781c1003450f0550014440e4000504c1d01a40c481401083c00c01c1031421074141c209444160039440041c00f48a492004240c40c103140420701451001001451807121411108000e4001b020401590054081c1e080c4180101d102e60b401170800000c401c01c410420003c0c0d854509210700c41070f206820454000c1182034489104100d4007884c45011185c0721074030410b03c1d1443d8140003003d801c03440050b01c60890a10b00044803002e1604840320302d502c400000b01640d42c07402090400502c560405003054452a2601440020450041002d90211a44500f4144202c04401300b00002400080e00c1650394540030400d0010519100c00b458489110b05802050329003024010321034007070440e401c07400340c0c0501040305010302d41d80030244d242107807014500455000510240300c07c95008040b40a03c668615500103d8816001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 509355017 1250 509353767 509353771
    0x9090227040b1602031801050c15060f0a1409040203120d060603051612050910050109050f061c06150302030d0806090a09031b02120604110f040b092e0905 68
    0x190705a032a2a40f5185240310401c0f0081c0c0148016038400c10412005040b4050b40840c044014180181020400041103040852881d007051007a41081308104851414904078510035506031582c0e03a815040500942c41d40c040b0111540c82000c2c00400074003196005c001000103049085007081c0c80303070310912840000c0c21541c02800c0200303042c800014620784803c140f0b01a445043d81c1d500b4400f075900e038044801481c0c00f5206247d64040c412001007003000341e01805000b021620b20001c0c2c10300c0c051032155035140c00034107128800c1a464900d4141c072100031104143c0c0716041000014000c007a5861b000010a91f980000e40500030901d0642080703030820001c620640c0141e403444200d5940d040c264088800b4400d0040108100c20082002c8409250081312000e10244c02a100c0e80302c0001c100d40303003002c221801c882c6412a1280d83c9043d060041d8803a086900c191420310035012020009408108010607100406422027500081645981d2045205040c51548208041c2e161089200540b0003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 509356267 1250 509355017 509355023
    0x803090d08271e01052d07140f0118140c0d0501020706060b04080307140709060f1a0708070308040f140a0b06061201060507030c020a090207110306010506040909022704 74
    0x62600c00b102c2401040740400c04043c0c0c141c0d10140341c4083c40e500d02ca0b13081101c290740042d40c0d00600e11840c04411081c0240311140c051a510b4030480075112410b4605840d034520511079904005d2440e10305020fa070959000c2c40d0348200c40300c202e0b01c1600f83da0352500d1484800306900000010071402480010b40c0140983c50064409000071f03501d8003862385103485135101d0409030b90700030004080032801c0d0112440b040c041d400d0684981c1550340314908142d5065400181c683c481d074110400440c80c04000d0b850525403100011414a055034849680d18043c3c5030000d428400d040c00001d00f0480b10061140c001a801101c3d01080400351307207080d594100040c0d00300d0700c024004001ca1144d02d0640709555114483d1400700202d603003481e40854040e0401e4900b1030600218840f0311006070399900c24100600342d810380041e00d0340310754141203265181803508507009420040060145440303d008a805503450b00324003045100c1e0034800308480b20000406150704605070144a80604865800d0900543c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 509357517 1250 509356267 509356279
    0x5060f0105030c1e0607060603021008090d090b070209090109061b090e0f07210903020c151206040c050d020c03030f09030a08070c03140a031d070803090d0827 70
    0x41d0800c14441c06800384d40f81003060000e02141901da07443c203000205007031071203420041005a500c0d80825940391b10382104802080703988040048100080040440302806031802c046550f02e4460807901038410b207039029000c1d181d5480022040c60094010300e42203a80023504001c100c1815444e0040f404c07008042c0000212540740009056400f078030841e02507101100f00148036181c8000540f60092400c1100b001c20076901c050300c01c5032040d40b00c1c00f00158003076000343c00c0f0900800e08008250f1202003d8952000c0140460020305491955140c0e101c1c1c0e082e07074006018811a4426070f914010030030301c050198000503110391424004400b0f1800356096180c1c81005440360503500ea2a40100d480d230500048051001030103480c428030025103203500a052078040500030048441495014a090303c0100e5100c518000d801040309004040019455001d03040a508050b0110384034401e103400c00f40b190f16420320500900403034500301e601a03520480c8045000c0c580210030300d503207010fa00300e86100d92 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 509358767 1250 509357517 509357533
    0x19020703060b15030f0402010e03030a031505100c03030e0f070906030b070509060d0209010e040603030807140307020706030e010b180411040504031704061b02070f0b040e010303050703050705060f010503 89
    0x801c0007220004100343e070a0b103060659a60080041841030020010707030411241001d220300b80d4405000400001c8010394000c10f04000003001080741002c20750210340900c42c64100348108030340c048070310301c8095890300d0046080001c08405070300d801d00314030f0b2181050113041000100380342c07603034403e0b42100e01c00d144448140d5205003064540e40691050b1036000101080107070981700e6035138020000a8014180319820a1545001c182261840d41080700414054000e01000a410210400d134001c14244150700e1841d01c01c0d0000d4449542d8458a418940c840c1000c0d100c840c1c0a40081200c5803028054000004240c0c0842444213005d40e4113442e2802082c10703000841c2401c0c0140c501c1103405454504080b4400c0803180006900180161080c2d940c80184240300c1014500002c21980158000e0110a0a04000880c000d503180d02044505d00100003c00010384251605811240c0509041e91915140d0405030f40910841000900c24002c01c420482400313000e2207ca4107842c0c0a0b401c5030562 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 509360017 1250 509358767 509358769
    0x409020a020f0d020c06161b05120d052209090b0f07020106080d050a0c0c080322080703080703020a05030c01090c0603021204060b042306040b0a18050c19020703060b 73
    0xd0300070800743c500680050084400030704000000b00b0480984058040020040c0c0c4c88080015040c03254000c1d821a80d94400c00c003615000c0201009020080003070942c030f03251030101425610805074090019a003001664500b9280b0300362210040ca40800140600400d511b80301300f80311400c603000c3d600c90082802059030a40b05218920a5442c04001058107180030740703003078419420070f16a54007000491040d03500002c01c400a04801000c6900c01541c07a0314858091400c0449103040100e40d03e0140708003002960b02c0007592a080741e40194010380e8884850030101c1c02d10306051800f511500c0002181c8404103415404010b19601601e91502c8480e06c8107804c0b0300360721511501d0701e940709580b00842c0200f1001c1c3c1c811848410b0040c0b0000b80c40c0703803581c0182c5044118100c1c41c02418400b00c104201420607009482540c00211098411942800b00c0c071a9000342c00d0102e1001145d0b00d200003040b60350802c088400c00c100c00481d450b00d102c5d42d200e009569100d0b07804203c40c2941032840700d001c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 509361267 1250 509360017 509360023
    0x30f0c0406060804080d0515130b01120b060706020f120103032d050d0c02100c0201020304021804051e0304030f081909150309020411310302011d0a03080409020a020f 73
    0x6542d100c18818508107001c2c40500180601a06500d804488c00c1c075400c41c0790ba1200300403145002214404614108400005099244009440000745040402c14840b85d030700c14088038000340d40040c2c01600c0b1680c80601d424140140e0840d0001ea02201c0c00200a040d00100303608081c038140c80c04012080c03840030340300c0011610103500d00c000c50002c0c00b900320a00340e15048111071100f10700c1280c00a00b404070f07160081d40e0801a924000d070358004248015410406410014842002d1030740340c450410b643c0302c0d0b03910745021460786554100310026031468072080c4115401580c000c6003080000880f401c003040680d00c46041c900c900018600d0184186000300d03201000c40e8224142c50f840e0100c40c1c04190081c14880f4001c03a401a42d80c1c40800c44511180003400030741c10000c503c264040d0281d44414003011060702c0e48071104001000410050703901801c55611340c65500d0a802d078006c821000704002010740e810040c030812000c82c01050094a6030b001d48080c69240e130840300400155000c01e62 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 509362517 1250 509361267 509361271
    0xf1e080c0c0324042a060212090a030807030c0b010311010201050604090309060c0501060906150f0212091509040507020f0d1b02120f010207061409030a0806040f020405030f0c04060608 81
    0x648280f00401040189480b00202c50f41301d0f000b80d025003420070003140c0781906100041818108074051417024007550390704014181e040e02c1c1c0342e0346181c5014400701c00584455058840100103000000d0032008040c41483e075811200d03031010412900d56100d02d42120300c1821004d0b103500640c0f9080014101e841c1c0b41c081c610030542c1548a4281280c00d0140c12207155020b10000d451940d2503400004140c4c03014858000241501080c03100703050109034000382241c80e003800213400c56001d100c041c8040e00161007140c100c40c100310f4442000900c90740c40c03080030780584251103510601e440100050540c02080c0f074001d100902060b40c0e60078040c494142c44c103030040c0029010894007601cbc0e050041c105141401308403500d402c11201080b510f0080103081e82d210000403111551502c104c2540040d80100568124803410043c47c240300303c101008042a0008009030701c41e9071102c54068050b802c650440b030113008050142c61009801003c995034940030984560b0085240c82c400141d010700c174007103581c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 509363767 1250 509362517 509362543
    0x509091c09030503182d010f020f07090506210c0910050301020d0c0306080d080a0903020a0f0804080d0305091902010e13061404020c060a0b1f0f091a070f1e080c0c03 73
    0x1c1c00341c6c5030300011501600c42000c0351055128241058200b4a0304018000040a4203400070605107000000c0c401040ba0071200900e0105810840010600780880e813080384850036504100305a450000c42200d040440d44204c0d00740d4030000d600c0e0346580990300801c5045400791001c1c0030780c07070f6200c080c1e5aa8508200c1001e00080c445004a0030b60715041d00100c00e46030007441110f480004d02c3e16050600c0495070000c8a28200000b0100718903071f0180505a04501d1500342007240345002202140c941c3e1542c940030020803520f012510440e030084400004108010b000d00740509900504038006016a005c0c0300703c80c05856403840390300e01d03040c02107544202c03c0d0005041c558852244210182c1000340900740e10000001e4100819005c002c07080360540f0749070380c944103000c040c1d04024116115940100c0400884c000d0500c00c0c242e1950115224980d011038204401c84881c200242201101d05501015084c0d1508903414000500b024281041025056890034440c40040503510030132031150f1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 509365017 1250 509363767 509363839
    0x21f0c0237051309021216140603271606021e06100e0a060e0c091c050d051e0409090201120917030603031e0309070509091c0903050318 60
    0x4841c800300582103001c49610141980505403102a403007810a2007c00355461300b030b1a400d4042040d010640c11184200c01c09a40c1c131407071420034415410380108100d0804004000d0110340c4550000308010101d4100e40d4199035000c215200c030340094881c4c24021030000015000e0b02da0a00303204002c1201030007080003042c40c1c50070519001c610028000f00401076800310b17036980030024100645401061088034503660855036820980c04000e4000100d04c04c12000182c800c0d55100000c40c00121802d12001030304040d501e84004245500032101d1901c0f5503111800d011600003100703d5140c001c1440140300341c85101400003203888140898460010281020312840720105400d2201002181c0040300a000d880c0b070301ca160842d80c125400d401d41108203000002081050303442c41802928041d0071b04070783e0140c05042050500e580c40f0616a004c01d9128490b440b407078105405005508e000b10383c0b0205881d01d6201d12040000e90f04017a0740528003c01070450b5880f84030044521700041d8007140050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 509366267 1250 509365017 509365039
    0x15090203100e0912070f14150105040b030115030524070807030b010522080d050a080c1602090412030f02040503031204060b0d061a010c021f0c023705 66
    0x3000010280140060340c03a4003c0701e61001981341864001d1812a00a0303103400c060341d20519000342c1091500358460031b150400c0034a0207840b044450307007a0441d02c04a0b000b0402c0010140000e0040510598003110f03000752360000410044081010100040540c240038071480201500d091000011035810001074034500001e84403074003030340c05010040030600d00181806d0000d0110340544491070341c0c4000900484108115041080003056101403240c1307401410301901c81c0002e072829201030035080801501080d2040000e080707403a01c09196030000d14083c01410141403815003170545038007420001c0c0c10999503200104c0701d4001c03a411120f000d4020751400e5040b1101800b100d0014000b210681d850350303458545d80d0f42c0d00144001c0300c1c1c05000c00044685074501c110b0030010364002c541d814010310b41e18042c00b5175500074035055810b94034040d5126070351800744102e0314020f844500941c4124035841d48010005048084100c104d460800120114521041c90004031401c1c401c503603001d000800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 509367517 1250 509366267 509366279
    0xf010c030603031e03021e031b04050f0108180d05030a06061d0d14030a090f15090e0a18030903020f01020604241104083f0a02030702030d031509020310 67
    0x104e5240d449035629006040c9000ea5158080c4460150b15100003c1004000e02c190383c07515070080d8940000f0720790740e545002d2401003c0381c1c501178400200c6052104110010b4030882000700808901c441d58819280440040e100160a0350002e448002c43c0a00c0d202020400f140550b1200620b09003480800c11203000f18000c104c5590341c100070444852601c40070a000c0c04c00c042016081852240d19044030135818107045a072540304a03400340d100070f050390b840d240c3c1075038202044c3e03010b403040041c03198a00d980d03214009000e003600c001c102000c50110300f807031814180d100d0304c0034055a00c01c44820303203400b190700c004907036604099402520f031035015090030301020310f00f4848100030105000e001c1424100070003070320595045a8840da0840c0c0200e8000b0242402503000c03069041e1201219a5004c9071183d07081003259100d000c2c0300c44021000412001d12402081910041c941c001c00b11120350255420040180119412407140611107100c0480d02186600031303640b0400c5a280d0303966610749441 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 509368767 1250 509367517 509367557
    0x2010c12050c120a170609010510140f091c050d05090102160f060318050307081c050426071a100803030906010819020619090b0c0f010c03060303 64
    0x10810505001040045400b0307824180701c003480402204000c19212004190003421202480300030031080d0360340400b0405a6070740c0d1140103064601c1543c6410b110f04484d0340c1a074888401d900c01c215110804964240310441d003000405148030203542c1610090015202018882070004008005030400310720760070403074860000780c041550140b046840c032203510240302c288044d10b80c02c640e000340c01211050007240e406016084031051002e86201d4114115260141c40b070246c140c005000406c00940c110ba050200d000000c041c1144203010007103410240f8084020745013190401d08100602813480495480101c2907814541d00044080b4102800c064201d140500003080220701010010000c0740120007003004d1480f620580740145040d50600c50f040d864403400000d100b0301c07a18940030000068503458103403480d00c0c80072502400420448081503c0b410666041101140d90200d0414002c040c005045000c00080c84000c1080001c80b02c811001d80742d0a000180124802c6030102403100240 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 509370017 1250 509368767 509368793
    0xe090a0219090e06180c010804060c140a0c14031806160605270c0a090b0f12100f0b0619030b03060a051602071823090a0b011202010c 59
    0x2480351a070a8949603111203080f5400521456550b0b4050410010b484140c0103a10030a410280001d0600c2c0b500c4400003040c02000901c000c0c071168a80d400c0c440401d02401600d030b001205d1202d46900c609072640010321844020905071420920800b1280c211b180c003101301d0b0900c50f030082c3c405400d101395209000c11a80b110030716040300101c2c10160700120300d0314813580f80100d50318030003100440c62010702044201038900500220390800d048c1319000350740d510107000c215030140300013044005003500007800111400250307980000383c48229899041c8003180c07001e000402c1e51810440081303000b00142c2194100c1d4140e580068042010050000794660b40039400415071401240004805c40803a0601d501910319041980d101c00c18002840251407091031604060710043c104507150a90080e10300d10080441d0910554503071b05000300460701541b1010010002a1820381418944072060b40d64202c3e80c41a01e240e100040082000c560a032031400310503405030f443c2c2e49410b03600d88404107680d0701 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 509371267 1250 509370017 509370049
    0x60601030e121b0d05030105010c0b07020f060a0221100621060e061003050601090306050c0903030c030d060807030302060105130e060f090c0103060503060f100f0f030201090e090a02 80
    0x3926010005207280000801c9100c00f2504401e40007203072a4511440d012101544609000080c40103004a0b644007001240c042e4103c000c041c00c2d40c86045040c0d09004000d07800300e00c00d014800c1040300d81910303a001040d4121086078490401840c8811481850134240c3c2c06c158410b00403c0b08002e468464074000641b450700e01c03030101806000790603072400c855661f0b0042c081d44400404020b428946050801031140c1503090600440ca002d07070000b0649141800000c0c4915950780c0071800c0345a0110584400a0016044a580d4800d860140b44d40b83c020721501100d20b814510701158020011500c401125030580090803240d08250070024031082d240014001c80e607407021800c1d5140020404c042c080c8218110116407420412106400c00028112403414981800c408004e03d4600042031a4040380f4000c404416887c0c2918400800015920501c101180c2110110f4940c50500400e030850340300740c031440001c0e82e0700d1401000061044a03102e8160f046803880340091f00b007103001207442d889 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 509372517 1250 509371267 509371273
    0x3150b0c0f03031603290904060f020a020109060501080d050f0a030b0d06021c151a090306091c0216050618061602010305100e041401060e011203170108060601030e 72
    0x401c40301d05a180d038104507944404a181200007401541e014031406e0b0650010014003e14007a20342c11894020300c25943e4a80030b000403000003414005a83e01c41464041000c20075542e507034100380000e0103014680300541e0214075040c00041c0e4614005600c0710000b00c5511800c0c1021407420100110b500944036680a0648600d904090390351a45064003840d8031500e40140c449550780c83d00118071042d4080708100901d0015551000d1110024080c00c4a0702800b030180d0346040e120403104140070300e624007501031040006200c040c110205240e101302030100505040b803911420126543c0c1c281512030942c1403115034003845681006802000d4840b030948503060240002c00102d03c1e5a44031b245d81d00a42140c000103141150b030f05000703803900314032048082c003562402c00c0c0901c07000e40000b810003080100b9503440d10315880d400390030420041881c010034205560f5100003e5110191502c0101d0015260700c40c030040400615140a0698042800500c400d50310303140150003e081d41465581284 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 509373767 1250 509372517 509372533
    0x40b070c05031911010903021b0103060302040509071809020108060f0d0f060f06050109030c0b0a0903050109030201090210030203091209030708030c010f0b0619140906070614010603150b0c 83
    0x81c00c10402002036048a0030411040740c0d00403030040924502215091859040c1220305010950000d0f805001c3d0200c040828044040c450068004102550000750054184010440c0000005c5901411500c2196032081c020a03280491000c40308443c80080c086425a004a055030500400b011a00300010b818801c1c43c58864540040d0041c02c0c003000c488550f01c4000080080c2001e00a00004080a00f00103940a04543d51000c40328031a02030700d100707030030081529900d203841502140011078005008005003003590500a01910301c844040e4018030b0b0481c2c080145512034402c807407184a1a202401006444200100712544000190350389807045900224803940d044c8001c000340c02c1e1380000002e080705011510ba0660782e16040151103200240102e1004d0b51070100d4040030100549052001c5c1c144d10001e4001e907009200d45183c0003c00030850341e08102c002d5203c090300c80c0304c18204100c079a0381c2e084118160b42d000c050f4490b0f400c40c008000c01040b624500580149400707002070302d13401 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 509375017 1250 509373767 509373773
    0x1090e010b21040f02031902061803011b020c030c01050708030f04021f0801170d020d08040303060f03030807090509091b060d0c080712110f0c1507110105090a0b040b070c 75
    0x26400c03c0d142130f02c81c1d0007020490b80841c80c040211a55000c460202c4100c02502c0e40c0001d401070140b00b0411807540e01c041c5840360140d0707081d072007108800c40c0d40c0c0c4008080d58010307400030340c0c1b030300080302c281d02901ca601d50440c4950f0065050300c5040394007180340d03803860380c074003074110701c6038030f01520403070308a04c031100750010300b1000c4a2803109070001c5a844000c0e96141440e40034020710b52044000054010310808100300d41d0106032200c3c490010305058159889a1030218001c2c0040c0d40107240303481c05800040b04055000039550b0248800380d44188060f40c5402c01c000200304169800201540300808141c0c40c288883c2c002201110001c1000d030801c01c01ca41a4015112812404000200c0d01c0c1c00704039000e03402c40f02c07031038400440b8501007044558080020074544145c0101110b1070002158148190300c04220456894122007400c04c41e070b040440b80036043c1458403c1440055003020700085144100140b102c14031a0090302800442d190340d158074204101c041c014901f0480030388182c02c08 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 509376267 1250 509375017 509375077
    0x708040308181513050438040203010e01080d17071b06090803041502070c060806121606020d020114060d300e0d0507030201050f04210303060501090e010b 68
    0x248203120100740340c1e6000d01400e00d000d2169240c003c070340300e80c0c03501c0c20640861070060342152141d100310210741c8074000f0b40120716500d21107440560360700274000800403030912021084a4100c0340384808a401d03d81c801c11080d501d00344c1210140c0d0030003202e0300c005803e4900c5821200c62454011807203e2a0094035101c010542d01602e0301584c94850020500040141e076802e43d41404040d0181181494010394401d00305180da441000c040144030b42c00728080d0b5480714004100782c4207400807256869030303542101c1ca8041140c45418050b001e424240500345006005443c1e292412510a0b000b554400301045600900c18000303550310204580b1000030803049401503620505044041c11148442c0302c0020612204001c4980c0a440c20440c48400548002041000c3c1c075824248180c44040d40d100700c501c140641d502c82a50b005260a44015540c0e0859002c280e035802994244901d540b0f0310b0054420103041d01c1350240d40e4a070200100300c80e40e800d0015040c0e5011100301c1e18070b608440384007411 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 509377517 1250 509376267 509376289
    0x703060f0f0608012414090d061b03060e0c0a05070203060c040f0f0303020c0103050901023a05010e041101030b06071a010609051c11030304030507030b0a02070804030818 75
    0x41000d201d41400d128094200c00c1580c0140384480c21010011085d00b05804444c2e061280c900074484526940316681241209591288401800c00400c95141e030400c10b028092500184c17540c6980d9190300c05203540b00c0e02414041e5200141580f426840b071b00e21180066020b0524582009014001000166014407009002c0e10a03451182d40721801c04202019141f00c5501c80b0440340400c0500b000001c0c0c000c5002d0701030b04001d080006041d03460900075070180c8142c040381164a504c0d001c9070807003c0142d41040c00302c2040d540d001a15240304244e41c000b2142c0a001d4401c8200300040003400080c0e06059070f00b000742c810f24021400780740700390100ba142c0d000326000f12000318980c0c2c141e5100c81d451880b00340c01440c080c1303007292115103881d021440104288410110100083c4410020320150840380308840070098100c0b0303a00c0e9600c0c01d1041c1c031000e90340070403a40802114081a210380460081d20a41500902c02d40e10307051031580ca0f070322180c3c80400031500c500018803090800c3c0d5030300381c0510f07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 509378767 1250 509377517 509377529
    0xc0c0e040b070f021f0507140d0c080a060303090b0d0f0c120b090402100c050703080a0e120a0b0106120f0f0f0e2a010903170a09060503070f080703060f 67
    0x11034201560050306096203948043c0c11903200f80d411044a6110340d000492404c88680c00003182e803141c0c0703011103804200604415201c81d0000b89212050880c0e84200c960042544d2071070a503031200300e040c005980c29484042c0010320511420700c1042001d8006040c160442000013408001110654058508020030340b4003040498803114002802c034010f021080c40100c80d090620b02c7c090b4005000c2c007646228a20070854070210680c200501040017001668002800030b48a84031486e00400300b0360039480e0741d801910007020384061000d000035484807643d4010300c8060180c1c01c1840031a5a03801e80610304400ca40c82e102501c0ca8580203100b03104440007400d0010910300e12020404d415284d250b0900040c650000d6040c290b8400720040c501c581043e004226101d402281004030340340310305d9810250001b691049500e00c404511001020300462580703030502c40a03543c85050711140812a0b014000c924038200a001051007105500d600c6203045c240020407070340350380401c2d52841c1260849 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 509380017 1250 509378767 509378783
    0x23180312011d070315060f050f040e0604111303060b060904180201031a01020a06020f070803190b06091c061508010617070807060302131a03340c0c0e04 67
    0x1415642c0500d8907035a10240340e00702402001141861448040454131500041142c0c080d0700b190003520500c07c032054255020101c82c2c94079180d4010324001d9200703445a512403032800c450b105281e00d07000b00750ba02d55058001e603080340a155481d148060902d054015a12420400c0103014035030f41c130b09c5100389149141c008260702c0d40b85440090212400998034040c0c034000b200b016002030307a0014980307070f125a0007480583c0f21108030300d0f02100f038024030000070302a001c00300800404026460050039a2107d564050203030516180c107000c954801c04100356006a40008221a04101c041d02c030720700d0512079000040c80a0848a107002610010707082058a40d45820342003106a681590505c40c841e000c401a041d01d91a102c025661040584121014190041101090720b90410184c40c0200300f0700d0300e5180d00300440c80e803850995104a608a01040d0641d90400d92a96442c0c03034044029072819143c07461100c0c443d0256001c5101c0902110044020701e004603038104050400340c00395200f6161 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 509381267 1250 509380017 509380049
    0x3020a060804030314100b0d020d06080a1502070201080c0714010501080c0406090501050901060f11030a03020406030c020106050121180308070f02060c0a0806011808102318031201 79
    0x1008095a00140c803e590a0328005e0034024400c4242500004461f8428601039071601055050b0000e801800c4501c0404d80c0760410000d1441c40124100355540d2140d80780c03030742c00f54400c0524412401185006800a444400021f8480b441c40c3c004040080c05034400e82d004118a06800d07013034500980109105030007028859486040500400300a020f07564018821782d030400011908003201480350004014071448295071680c00b0340609681c1315440b030103070707640d950729004080d002e94014400d0740002880c0003c00211940f06219200580c0e02c140e5034599201102540040890307500c000403044c40e0395501180002c41d0488011241303081c42500d6071200e601c1c4c28500908221910741c0540c3c00c0d0b4010070100f15650744000210b81d6298940d0420070881e8641c9001241c00352441c200341001003030035400107d00040c00182840c080d44004800313209440394514800304041c01490305500f6611401e011900c510818040105030385101022a810001d42d07028840c0c10380420f91109840c041e40b150 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 509382517 1250 509381267 509381273
    0x7050f03181b150705060601030207020a030f030f0801090e060c0a1103040306050103020a050a030506040204022b0e0607050a021902010509130b10050c062413021305010c05070b07060603020a060804 87
    0x503906014001d0f0007a80b0308010030764444940300e950050510741016130010300381e4215900e09a001024507040780300800303d48503510b0058401d00c032100d06040070410301d100000d420400f80c083c0c0c2a85a0042001c0c020030388648000c0695030300029080381c2444030009451750280c00800290005602a40011072107524500602000703140c20380045006403e80d001c2031001c00c2c000100190020340c10b03607006a46600c080384401481c030301040000000054002070000703c00751900515000c00035501542d52030340710220160351500c250300303041000d40c000e88c401c91101440d402200140c140103042c82460301080100141c031100d00d00103549178443d6030303000c1c81401c4c0c00c040a80301d0391a241414100e107044000303240e0a594000040521080c1e06210b20f000c5410b403268030f080c007140000585039192140800f08410040d4010482180c01c0030f1a4440c0052590b2140d0794242c0565003150140001d18140703421441154003514040d900704d0b44032000000142c540324000e2005100e10307980e1368560304140c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 509383767 1250 509382517 509382529
    0x60915051f0512061503010e07030e011e0e10110c010b0105040506070204050702010e01290a050901210510020c300c01290306010603020307050f03181b 67
    0x146040a810300000038010381c9a8011040380c141c900d9a010a0829a40e800c00245d9400c0c240c0c0111403016074003100000b0141040c1e0f00460146046880902205d0005170701d040c204c401c209240c841e954102c202000300c1c14066400a001150718000781d9195124050a09099420460303004103004d0000a01616800c0284140c0740d0361503003480c1c072616051034880010164050389002a11607640c8101140e900c5000b544000c01450703a4000912401070340c61350121060641441c0c100d00d2420b00700383e0b40c0981c9421580c60701501d40040c030607a116400c00c452a44020110140c086104c4445104000410f50400c610f6680d41c084410260b682d000100301107040c64021080300c0c80f00002d0b007041022001c1c0800345032040b0300b0401001a00c0c2c5280c0604c060242c5450941a03507032001031020b01c1c6134002010a0000c10000c1503045501070790ba5014101d01302d100442c0c4103400941c0610a43c0c150b030440f4802580c002d6000030100c48101101203459003030040601e178a511184041101001c40d040107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 509385017 1250 509383767 509383789
    0x306050103050a150e03180402090d08190305010b2505070e04060c0809120c03041e050901060503091b010c050303160801092901051909260a031206091505 68
    0x204034103101174001c0014940da2401a00300180344040080005440f5454039410b80340201001020403184a5607401e04001503413001a44038000300024030b0703a260761802030080340d040302c2c0f508803e90b04c1c0000036108200ca14903007404003c2442c90301081400421000c00419019100342703080c0782c1090401c0d20300541103500f884001404e21185900f042107440300402c562984c400c01d20303085661000c4840c1040e055100c0c42d0400000b0f03601001500f800c4440e50f0103142e058503810f0701c1003403032643c0382c1400b40d525010440c0c0b910b51560000c0c480f01c030044000740452012000605003403c026503142d40d80d50841e0411501c0c1e0201c400c90f50b40c41d0010541c402100d6004121140c010403401c80c4401210032050700141c0d580301004610041e0040350f9209004841c11640307602c044510a0401c1c000c0100644114820322061050324810204d03040a4085a001c40304890b00c0240004440c0c0d90b02030750901d010b10114511590740b020300080910150150500d41c94480100c90b210701e0510040210b49485 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 509386267 1250 509385017 509385053
    0x11030724030b0d0807140f2406040b130b040b0405090d021b06120c0c0a0c06090e1302010f0c0221100204030b060909011803030b041a06220306050103050a 68
    0xc4100040104441e1000c0b42c0300546c000d40401201003e03010940e207407110340d0110600d148a40411200c1d010100618024050180d01709000c0a1f1a0700007088241c0f08003003d40b61b4400180202c031100805150b004d8410342c14044c00200d50300c4000350014040f030f45d084407040c030503400c8402103200d801d074140100d41002d4802c07aa0784e50301c082c8900c0030413082d0123550300150301c01a101b0042081308210320269440c10720204200c0302501ca0515105c115900c291040c6404111102008520401740452041c800c10405910040b41070302038004480f092a040c44080a10000480c400050f8856402c1e0004602440866200c0442ca250103070740b6042030700107044030047c0f040c0000c0c000039140401c0243c1001040302c2c0c07660b054039020221070042c0700c2b0b1f0141c02c1411940ca10260304250f00341e0400c481d038245c101c504000c4000d100780c5062a00c40042c199541c050410400400039010b20398840c0c908140181220043e952269195011240c0a0300305030350503844442c40504002090000300c0102039 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 509387517 1250 509386267 509386279
    0x3010b0405040b0619031407080d140703030903030209090108010c0909150329040c0905150a05040c03110c0609011d071a0f0d151203080411030724030b 67
    0xa001c2d02d480400c03c1010700420700c5150609601d55030304002c4044100556000600400e000002c2d18070300ba078440c5144554a424082d400c4110149809103c0440461041e40035451402030699403c03001040040800c030f043c15400e01038011142c6400028a01034010f18000044140080b1406071542c50950301c000c20702c5090803800e00040f410411420b0459070701c101e007101c035810444440e59111300c801a01c1c8242c64400700c00c04c014400e0301204e6030100c5140c20401c02180e103074800c2143c1c11101100780c1c1031304031908120810050502c0e911440b0180520b05e0000f41005018103e651941c0c450121600c6d994003200c10710001400070710070050603680b110b441121810342c1d030032961b0321043e0304d104800824580301008240c4613140012a4403240c3e000a200d665200c140c00020003e0010400d00c00d00c40040398804524810740c0c4510355482a09a1104540b81e5195500e03034410901e0f05640e582c040c02440300001d081c590388108092140c51592001841c1220071000408070f50b004008544501 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 509388767 1250 509387517 509387521
    0x3110d0914061f030b060411030705070605061203070b0c0c120903010c030e0d080a091a090706020706021002030411040e0304090f1406010c0501150b04180209030304172a03010b0405 80
    0x16410000780840c0e174081a540078581d140b00000e001403480c1403003034038490400410800300d6070340312004204592080d0402c02c01521101c040c020b11480d03594100c001c541c01000a6408980c50117030080d84030088816451030400003100c00c0d070414150500180c10604042003000d074500d028010481b07082c00302c2c03808220301c4404041842d5100c074280107c2c0c0921185d080801e10a0714940c000300c1025400c44510a0580c02d41c8245011400f4116441d020714000c444020444a101152010488405500408802c80b0103035204000b540054021aa074005418200c00942c4a50049400c4a0555005180c69514103803e0909035101009000407051521103112120300315144025040788080c44c15500c030760b4a51811a00400c4903203007804c806c4081190015035100e10600400c01d603028000c100d421241a440030030264050b0348600340e895003080c4018840100c60100321040c0400e090300300e4002d920105004081c2500143c0880c00f4498030340001045030609014603502032000741d400b08424 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 509390017 1250 509388767 509388811
    0x309080604020d020d0602090402040b070201020d1106061c0203010c05030f1602031c090c0b04230f0108100306050c0a0f0c030806040f090204020c0102090a051005040603110d091406 80
    0x1d40d81d0102c0c0248a85c0741c14070303031206100c040c0d8152580c0e2180a001150703101d0302c0319821300c1140c000311412801407040c80740000340b42d0703c119880c0c4500021140180029251001007104c13140040d0300f0001d40b000440c5013040940d500b40111900ba450948a007552400c100c0b0416016100040c0443c4100090114008140750b0010403907680e50b0360494217a09003e1100d602501130144010040d103103840c8000c01062440308907006200702c030f45100ba06004001b10340150300042a10070f030a25442038143d0b00c060302c01c0d40a41030456000038184d040030440354899990b242154000d45814440d110080f5411800315082003c2d600915840e08140f0300148103a6070040034080018881c6010700e4581c3c150300401e8855801821000c2c0e8000e0056441b0390280a05034002d402084c41c040c030804c800d0800150310b003404441c24a451210f590380b185000d09065043d4040c000c2207958410a8004110405d0091181c0c0f103a07504003132080c1e0721816004034103502c0c6864080d015241d40112803180c4030800030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 509391267 1250 509390017 509390029
    0x80903030a051008031810140d0207020f0904030c0c0f08060a0f060f08301204050307060c050d0606030203010609091116080417030a0f0e0f10020a030908060402 71
    0x1c0a00c0d21000032a4569400100d440c000409500c41d454611020620b45a007014418440112001c04e448118146262010440341a610107c22040e583c00804c4404686001600188541d0307001030100d1403402444404116910022a41500051800b01c6003200704801740480d030009220810b070f2a11206d0600c088140c954001a040042650380c0b5811428001c910b600142e00521a00c90f00200f601d6070b80c40d0b03841c0c4442042c00d00c0700710700090100b02c2d018113120904640d501c0618400760703410100c20007240c01100d0400340003590140700c28000d00e4002030280c041d5400720103142d40d038140c03100240000101926042d800003003d050041c0018001c40341e01ca40f00e0740172035842003004103c23002c0748281c00160384200568071781030481100b441000d02954100510883e04d412481c0d50905e952400481c0e01da01841e8503102c0081c3c094900100d510f4440c1388a1080742c0d800400c220b402116000000f40350040050b45107015030000382c001d205040e00071140344000c103122000b44c05240742c60750004517 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 509392517 1250 509391267 509391271
    0x130b1909110a0503010509100b0f0c010e0724030605090109090b09420108010203040201110304030b07050304050c090127060302130c050c031c0b040c0801140d1b140108090303 77
    0x100961f29000010b02120812013144000d101380030443c1d40d95192b2006013481c2c0c0e4401c00c3c10710425030910240c0301e9801000142c01e41210464a007803032410404101030080200702070010f0041646410303012a203030b6529070f0118001c0641d404001103001c8145815440c00c24010841030442e042031030702900c021900c04021074002c054840159107051001081244407a20f640010542d19400002044002e015401580664001d81703e103014031103180e0071240e0320b220324040246020417410201342128000e0015541080c81541590300b680140c84c04604806801d900c0110800881d03050b546c0c0b661005101d12000401c07aa209001c000e0031034010802100c0c0007104000c00070395510000c4040c0b071203641a0f800c03103914031003030700ea4170401c108420502801019107a000340b49041038440e02850071384210b61035000360392038100b0140c4c03801910729110101140c070603800c08138801703141c030004010301403205600d40d40303440c00d51034107080c055601c00e042c40380340e456818000b031001807101105001042c1ea07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 509393767 1250 509392517 509392519
    0xf06180906120709140108031305060702040905160513110f13050a0311011e0c1103010b0a06081602010b0102030304080d1e091a15130b1909110a05030105 68
    0x1540685072000840d00c01051580506000d01034200302068040640c1c1000811924071540003c50780d881e412065241d11403032a9180d2101010b0f40100500e00305034014040d06030004000082d00e050a4541d81d0500340d00103600c00810410701c5050250345819a20300940c4041980300f000510008080e0503128450182880e0070a0300115003841c80c90031141942014200c0035044c602c80668900d4000341c00c004503200390303011552100800c0030010b01030940e940c40102c2540d544403591030340d4070303600b010210081d0119095507c0341c1110300381e40c56441c19500107200c070f076030781844500c3c00d0038095007400c004d00f40340c004590400381392004607a0300005494001d508058501d6688802c1d5031104004c00801c1c5400010b40803541d09030404800c0307940b00a05a80c0100c5120402024601d10400c29200495542400d42007141c0b15003418181480600142440100002013480b00c0000045105841c1903500807000d00506061000d40041e010b0b130240c00064581d81400d04402c0000034045000500800d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 509395017 1250 509393767 509393779
    0x42402190212160f1b080105070507020a15030f020a0207060207090b03060118090c1401080901050f01090f1116031e0c0f031e0503180f070b0906041a07020f0618 71
    0x300706012224038034103540e640c414205d0042da014407030080b0307013410302d44602c0c40d15500e0300b00004c0d000e501820446919540c005e001c40b00080c1030080307030078032640c50071801070404d940c4601085440700580b000745801c4480d900105011413500e240246003100c95002003480904050328080c007514001038403410344028100c02000e078000c5804d404000c102e2a40050501500d00a00040300882080404550842aa01d200e21642c80e80040d80c00d81d0000e0b07903007000184411004009a00309903000564010410b003011400303028079036041d01c80c1d4020007004103000501c07240103030070140c005404884800489400074018074010074040c0c0040680c41026043d1400c0304c94144c101840f07285030f00c010084498280340b25050824008046400c00c1b201d03010b89586052440a20600001d01240141c3d0100000c281403414085800c0140d004000740d076402080511001c5a201c031500c0200901c07501c00e5040ac0d440c1c000350b0040004044543ca1075070702a1000304058003034008001148c0a00500590322 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 509396267 1250 509395017 509395057
    0x20c0615130e1c111f06090e1005090102070c08030405010206010e0f130c0b030f0907080c0312090109050a06032a020c0409030207120b04050c01020d0215042402190212 74
    0x20542d00700c4c2c10039010000e5401303010f0395a41c0f040074000c15084286250b032010000740e61900c0c0c0b090b04460030000c11540c198801e10781c400382202c0d940c000990041d595000903042412a42c0c80a40c038803a00c0d000b0345400d400120303080c4995641003144500410390b40c2d541800c1800c0040c4046101c40000c0c203002c0c5903141841d8010240b162000d1604028060150002d981c0c0c50030b82c1c80e40c5401601540d6890301ca015900d400a86400300043c00e256419005029050301001041840c1d2140d101035003060500c235121200284650b46c0204010081846850200e4081030314071240000d6402c0007402e0000300640752000800740da00103410361052005803400111100b26003030583c500700880d40a418100c005110301e80410001507842e6000d1072040c4111403403101d11000598440d042e181500c2c0040c0c1c01488409503940300d0440d1a40c10601400381d50340007a40c946e90079001d02d204020041011900020f400d10003400c03043d00b51584007560f20240030f01000154030600b039449001903050301078182002e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 509397517 1250 509396267 509396323
    0x51f090e0408041a180f0109050103020c150103080c06060d080703030905120c0f0708010c2c09070302192c030c0d0302072909010f03020c0615130e 65
    0xb003120040c1c0078040b00b00703410285824402140342d209081c009a035820a0141e040d41303050408481d03142c0c5034161112806182840c0045000350005480306a070b42c80340140d42d502c0383e550a140c0368040d41c001d0180c070307a844480e0107a061030700d01c0c0a0a8079024400852501002c0340d00441500d03029541440e021441100ea400c3c031601d4880307425980d03000c0380380015803004410700000d589904242414180d451250b5070303000540c2203518100f401400b144494042000070310307010f40000d06011001e60400c01940c410300100e000e10303400702c4030b400204c3c2c0d00081c8248803587e01c40b5608450710b41483d2440758040980c010520442074500107806405010103180d081d59418000380c02c440c5005490000d00d0491400c00130340d520000e00c54050500c6041903c1c44015210721450340c10051010407a9140c14100801101e000c1c050400c41400c159080c065091071001c140b01e0300740140c0320002008001c0c00c1c4001001801a030042b07546100d2482c0c007904103403007040400e1104008a0403092244002404c01d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 509398767 1250 509397517 509397533
    0x7021002010f0e0c0103060b2701090308121b03130b1812132405340303110909010909050f0f0607020c01030e061302130204030606051f090e04 63
    0x10710041010709248003c003202c9000184c00300001d80c241e0342845213039501e904022482c40b0302005191103680c9000d5030101204004880d1060003410316200100503525292803000f504020000c1807080c203814248810560034205804903480891251451801c020704150400301d2500001088441c2c44000100302c610740c440c081c1c684540586c1542c40700440c001b00078290340c0c455615042a0021b02801052072243d40f07416000311210100700c801c01200b00b00050750b10b500110b4003200c010042085c5202c200003440c588003c440d0400c10f5442901d2607903d00901035480704202c0c540a030509024598040d91140c003d1411900c5a010014007848942401414810804400c48040c803c1e51741c002e1070b4100005009106480c00c1c0d00b52800380f005100110144c03050fa424142c007960158001c01c41c0c0c4504022140b022134030003800302c06c0c40c84480280710181e80140e4001d450f200d80da071000b04414142181c0341d14005101c041d0200c440c408960001c4c21400641c010404180101400242001451 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 509400017 1250 509398767 509398781
    0xa050705210d2c0102031f060c080315060c0c030106290309030d0c02061b030c0f0a0c05011b020c0d020a1a090d1212050108100e010b09070203030105150903030702100201 75
    0x1002810343d0b40189401034040d41c000c1e0791a00c420b1420404011001c03c0c1050440b00f9103a465880420824917030f103c0d0140783d00050702e10018500095100d414990b1248001c040c4074a10760301420400403903208141c00c58a076903121403606902ea1400d4075440d86408094070030b2400c000d45031a0ad80c0c54004103d443c601490700f6040000e86071058045c119600010580c9c400e0850141258180a2002101c00d40c3d010a495400348844107020503048103058001800f00d6034980e240180010b440303522601d0950701d5855410710890344264280c2d01d61035040c0240c40c460321027550501d0641d405503000c104500c031148245e6a40107030311440b10f4494200d54003195884070000785141c0000320b40d428116000e00640800c030f40860105c610200007000391340180f07412260703400d02600e088203140c0c1041d0b028040650242c0ca4555072060924026960009010b024810b070b0b5004580701d6040030300b4410311130b800120f20740084200340310b0035115a070000112002c0c907038140c4944c03420350a50070f0164003420135 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 509401267 1250 509400017 509400071
    0x70203070303031b02070b070809030f0a06021b0a0507030b0622061701090201080703200c0304050f1509060a0e100806030d050405030c0f0a0b0a050705210d 69
    0x14034000100349541504040f002107038600010581d04c0030300c4420781c3e0741d60301c0e44540c20f1240c00a00c00400820441c01c0a89007490001d006c0d1041981003900182c1401c002c5201110342c03aa012071343c0850080404800054101c242c1e00510707038400c10340c035003a603200a10300c4014030100c06c4000280303507a00e5407082c00c1403002402c50001694142c0c80c1554018240ca801060091510226440fa0b1140305006480625030182c42c0e07100141c6984600701c000d004813100d0f242d0aa01540c81c01030724007852100506083c94208c000d19111130a0000b0004600000c12000344030303500d030780446094072201c00101c60204000b01d03203079541e40040038000d40340c1d203840c0d40035642c1c00030000205052840c2c1004040e845000118152004141e9001059800d400750303000d101e40541c0100780d24003582c2481500c41a03050780081014494035034400402065034840d5043c0760010700d000c508102006410401c0002e090310913450f000c43d000310107002c00745074003502c070182440548500d081c5103444042e4403600d054500c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 509402517 1250 509401267 509401273
    0x503180f0a050d020114060d0f020a120b010e0c04080d11120406080f010509090c011d040507110606090c030604050703110408010b0108010b03090303073b04051e070f05070203 77
    0x1810003c0e00d400c281c48109000d5401d041040c0a0702080c1d0040501c6030078001e084c03000f2031000da1108150b5501c1000203e030051000d00010448203070000e6201c082c94031a4040320a07640c10103510709048000a006810f106000740b0092083d002c0219a070303101d418144c50104800d450700d5904900d04401e00c0e480580710180003401240c40ea0707100021910036004007051965690342c0754140100500b0480f01c801c01c941042c065540c20303605c107020895005052148040e000d03540d81d000102110010745035030000c2030300711444051116090001ca54000000c5412580ba0320340815454210300c00207002520941d52007000075001e40c06540a881c144141c4d5071a240c54640316404180280141c400d000e000c11ba401c000014a0102c80044912804e01000a5811601c413810180e030ba0301507150b145411443c02c0464000040c000d07079051341d036425201c00e051251442c007006000845001402c141e900042c4004141d00e030f134452403400340e08201030380f418800d5100300a80469542c007540b42c0c0258940 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 509403767 1250 509402517 509402533
    0x7050d0b04140703030e2403090705030f010b0901030b0c120f011e050d080f04031b170d02060402010818060903071703070c0f0602042105010b010f0503180f 69
    0x1500c085091089108078007910742840c0025850b543d62031944030040002c0c100400e8901d06045c0000c0e002080707003500b100101c0f560320082d01003201350400c644011041d4000c84042040d8070b01041500341e0381100300001c111003c03418001c21000c513814040502041050b2011030290800002200e0450404a03140c1003d41807201303003690001d80030b200d45500040d24a220181011003206c0c0c07003040340c2d0021b107841a1701500b030345c400001e60403c100390440040c040c440080803441100181c0c144100751a101c00085051035240c14400c0e52100565026512828603119110740000720182c00c00d0f024200355005903161403c10001030305040300802c00d0b0007041c050003040000000900012842b9603109030921509112003407190108a0710400090408155000403602e1035400ca05128042d080151800307403601c69108443c856601c002801c03144400b80306e81404403c0c41000301401d0700f4604640d4082c0131a5004056000103031031031032050500c1080708181c00c0b08011081c01c03a9406003e54cc60a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 509405017 1250 509403767 509403773
    0x406090f0b0a0603020a0519170307050d09153209040603060501150215070c050a0b07080712050c09060c03090a1d010f06120e0a020a0906080c0d1205070507050d 71
    0x90000c904c0100d010348514400031a0514269101c1911420b0540c2340100e283d14260000000c1e9813100d5207080342e8003080014801049003804040c0c490314035a110504124601441c45009900050f841020010103400704804407041107042d00f054918003840188a02c5c880043e03003040d22803290700300d52107450010700004104d0150041c90403503080700110800c11341884800c2c0d0311448200184a00a001a000962618061405141c3c3e540c000c1003107400d45030300f950350b01c80d42000c140e450380c0c0416911b20800a4050740412040782c40e10754204140120304201c2c2240d2031340e024034030806100c3c032004501c248040e60104182c5008000090095139210f5913039414811a02100e400160320403400b200100300e48010980050481c1e0040c5e4490440300d0907207400e0b0b0f00802400e280003005c0c1c050b640343c950150365550340c0040502003070b460000e00103252124680c90611090b90710703030103115102002e40105440d45000090300210b801e065642c1c9420385000f0381401c01c030360002503000915a06520038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 509406267 1250 509405017 509405021
    0x70e0405180708030a1710030b010b030a05060301060612110c0a060605011205060f0f011e091805010b040303031e0207080a09120507090e010b040f0b04060506120406090f0b0a 77
    0x8040a401c156070b0210344459180d034403071285500001c0440c45140318485046150042654080300d00083c40e035486459550b401000c13802039000d40502a40401070000e655000d1141580090046000b00511440c1c198050000d4444c9800d5210860362980005034501c41e0b501202c414140003030649a803041c8614104e4000c2c00c3c81e005081c00500341c0e852142049030b0610659025110080101d441e2041131300800c0b00d10307500b04446504104103888441e00c03140b003a814401030200c180c3c55298955007040301000e0620780a5035581d184034100b400420003a003078407049030b096070b400d40b50100e440002c00101503910000b111109040c20701c0000c0101c00d2010fa4000744c0fa90703480340d035030702e4802d2a40c81071225154803c061010784240c0200904021144407540100510381050002155041c0c290001900306d401d58001e59005540b41c0300c40c02c01c03030b00e8a0310071a00540012150b02d070409001c4029200f0104000f84020071050341d611a40040c04001041c2d000811707405215000c46150071807600b00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 509407517 1250 509406267 509406301
    0x90c080606090f190212090706023d02160c0f0f151805040c05040504050a061211030703170910030c0c021c05031b06090705130203070e0405 62
    0x81140545000719406141410348503028803202e000c940b0302d544425111101c8004032515032100280d080149559446800110512800f14a00a001c4070ba15011010303061110304075112404110125244603420450004402c10441c407040d0359041c14049001080244607003210106c41110240204e420000c001080c0000c0d40d41104020301e007150350b90300740d001801490003850a00a44d06100840c030030300c560310400c203650707912641c2040195a200031900305c42d00c00411000090000400780100e060038000c05403c020211010000246000c02d26002904c41d214024482d80440414013061390381007044001440d00007640b42d582200701234007400c85601ca070030414050b00c40150301c4001a4007a21449100c4c000503200e000c02ca5080e03030708100550b40c0404569580e0102980d41c0c4021600c00c102030800f8205112035100d50160b801c98180c902840141a0340d844e90140c0c4052007180c0b105001d10f00c80c2020301d00d0249e1252500700007030b150384084051003134220745414200118040c2403046c0314 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 509408767 1250 509407517 509407529
    0xb091605011e03051f06030c110c01140a030e1501090b01090807090b180f04030813030c14011b050a030b0d0c030b13052a010206041203150504090c 65
    0x19604903a25001920940c11400d026140a407001c616003226a02039000150710442100f104542042c03400608064491160002e80c006692600c9111005400c440a81d06012030700005103c07a54008000804050080000542910300407940f5844503009400848008011170290f0f02d4049070000c043e00e03d241c0903c9504142400e00a640040d94003402007403054980000103400303031a01f0031b1122006003140756410380e0000800d0070015900700c0d40040c8280030301c080b014112440d0078942001820900041c025400e910a00d1504800280c3c1006961181075400384042c90b6000408140600614640c2c142807402e4a010b401c680320540d101008003c900f01701c0d1002c01000da8900140314290b07a0a200052441da603041090004c1780e0301c0c1440941c806900d00c50040e0001a82d0364480c2054024014091031036446000d90420310030750708941e00b907840d080c8010582d901e040d459000c1c0070a591a00c50050503550a82d0030300f25440300e02d41d08080e1001900512201b90399280a21448a20384503403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 509410017 1250 509408767 509408803
    0x30e031c03140604090b0a0c090f09020711060310050d0c1d01030b0703140c070606120602030103061a21010b030706020f010509010506010c110f090901140c0c0a0f0206070b09 77
    0x5140c0389131600c240300d000c0350400c08002d00350791750301200300080580e01403500c28402c815000240180c408854400176084e946400368568800c0e182a2103045100c980280c0301e408140f04000309200d889080d40220b032412594200f50800600304906450300f20b40294801c198034070401c0ea1007401090041d4100c81c4079034440d0500d03075251003085040b00c440d8040f02c0c0f2150004800300f07410031000b5011f004240d0103a080003c030320f595451610349140b840301c000c40d4a070303401100420501a1500c6204c00082a0280c0d85805840301c1e4009441210001032450380390502c0c81010f5001e4809500550007050080e0440d6085500e665000c0d6803010311110b1179503207600b0840010648031060084a002c1c000686960302e0b0840325a3f113a24030b070350041132900d400850780c0d031508030142d8800c0707a16400398403c000000703004c04c0484207240940000916094071800104548620030400090300354275550401c1112035510704510010341144902240030b0410100c00c420301a2005020800601c011048285 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 509411267 1250 509410017 509410021
    0xc090d350a0c02010e0a090e0a030e09060906060d1d0109050601090603231005040f0219140616050a05011b09030b040b09010219110d1b030e031c0314 66
    0x82031441d12a01c101000003445820010005500495120a00c03101c001d054a07925921140164216819403143c07059036800102c0840034150044404c80010300269130031f407100c1c5440800700e110700b00080d00050140400147c0044c5691aa51268004094142c03800c20003100e04c1100364081e00400c0020b0300c56010380400000c000c03809218502c120396100101034000000d540e0140480354600d21030040c0386c040c540509426004070302c00c00f03110780e10514041c50303040502d0044c041400340c042803c5da4403d2882c0c0d8144505400c0340d1820040f4034044803015a00c03072241018030206000d520005010f803060450440800c801034003c1d4080911b080c4075422000b04602e0201c0303041016200103040a4880c402050100700c00c401140c0e404044600090701e004010107076032403003181c500c0c0000005915101c211408807400d20044074030242a10700140140d01540e040315661919940003024801c0b072543c0e00c1d1041c1c800b44400207504060b20340949007000c400002501070090b13808504101c103040c0740 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 509412517 1250 509411267 509411363
    0x60519060b1306080c1207230c120903010b06120603010c140304020f0d0206072a03030203160c0e0f06040b010f0c030e120f10050a02070b0c090d 64
    0x1090301d4002c44040d8000003101d141020a6a5105014265841c007010800c049051245180d031400d0280d00307143c0d41d40f484403a40301400803a5500315440c51070400420003d02d0002880003502a0784091020707070f401c0d550380080d00040d00521a003640c15401c03c0020802c421f1a0300036a131100d1082d1340941c02400304880821003110516141c01d03043c04803403814030226000d8286020700704041038001e4114488101c840c1c0010390590443e843c12180c4c807141e210003180440c842c030780044400d401003041e12002403c41ea000ba4690181d0401c40c0c20043c00c41d61801d043c4200062030320001d0146038507001160030b0002c4a0304c1c944a0481e01d60780234a080110744030465211b0021440b503540d0540d0755405000643c0d82c02c4426281480c0d919511150465086203040380600c10028003881881c01400c00000104240c025500001e06a2028601c180f00c244081002e01020079404040da02d020b5070b890701c2c28400101e442000010180404c0c608181d80c800f01c1c1d032031049071134101d14001214080ba1078218 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 509413767 1250 509412517 509412539
    0xf020f07080313090c080705070204060f080f010c020c0609041e0504050a120504061e020a05120702030721080d20042102030c0103020d0207120932120a06051906 71
    0x1105c0d050000b40d0140000d840148541e000d06940c4e0700c02000841d816a80d9100001c1803000ea070003080d29a04850303801900324809105000110031140098403500851000080310ba01a2403c842c0c01561103000c3ca840346100c10801c03059a2102540030801d604090504941d280c4600000300d60b541105059242c06074000c5081d0750440d01565a078414030703018000007110060031003a4840c00e52240803103c2c00020b90038030030805078610103060b03a5102c41090040525000c960350080c03050200d00010180840040e142580a16401401d11544d500000d1001c200403d0703071401c6851800e070191b020441c60803145000b04102c48506142e241002016a10003c841c00f0a050095040d803081c400412154080e4000e8600c1240c0804010300f000003039180d050b240e1040034400b0000403548682400000c91500c2007401c2ea1030b1611a050348000d0015800702d103400c10301c03845846807140000c80c04e8079682c10002e60142507400070050002d0b043c032400702c04442c41c80310203c0620030b00704480400c0b82042c0b8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 509415017 1250 509413767 509413781
    0x807050607061d10020d060b04150e120a0308011d24030106242007210f0b0601090515180a030f080705150601020606010f020f0708031309 61
    0x800d120726181e15580c0303200c01800000c0c9041442e0710340441030710200d102840003915030f220b040c0707001d40c5e21000a00d606007114121342044894010610050114410884842221204500f0095840120303d40040e81340084068498420300c56032141d1001c066101900d64100d0304801c800b0344081e040c1d400b116041c03c41c11521000005802085c15810f980e41c4600c0032501c4401400000321903843d61800c220b054000036229442543c00c903401c000066021002c40006074030607006603000200c803030085840d11030ba0301c10301200c46d04084400ea190280010782104940e0710405900303069002e840d01440c401001c0317941d103004c00c00c3d641e000107407410811800440c0c00c00e55444985000003c4d064109000c0c0b004451641200c568103011001900c002c503100c03840b0340910f40d500d454080d28a44a4503048008111500046105043c841282d07000107405401103005d007000201310b0900e040c00ca1422070004140f181c144200301c00003455480c0440205418401c6501007403981e61502c1145040c0e40079 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 509416267 1250 509415017 509415019
    0x120a060e07030c09090c0306030c0e0f040f0309151806081b03090f03040806010e010603110f031506030a060602060a0e03090603190c05031e0402010e0f030c030604030207050a080705 80
    0x25060024070998440e40c84075481603001e04010036040c4e103401c0700c030040303805440d103610200341d6940b82402440f100304c18200003402c0381d134081e00d45850224006030000c00040e000030681810b9a40360410540141840c1c0042c0c0000c811010301c02c0000d080041250b45950b00560380d11004000c0854100d00c142090b17172107002c01d480b14001c034020082c2503a909500081c0b180c00725001c7c11070b020702d4002e02440204020012400140300b59410494414002310040c4d01041c1890310b05500c00c400810540c0a40c3c20288a004c2099280c0e540c40c02d41d615a282c0b00a0410b0780402e001080003039032a0144c0c01102503c4e0554225a080d035207c1a1140403a2a040c0b14440e5aa005111030400e6141040045038011b20720301c0705110001d4422505800c0d00c4040744000041100401003100c0408403030f0418403d5280c0c0300c003100c0c0e58101500060107289007000640e00604040b100e0b1145600e04001c0340c80503010140c2182c0b030301c0c90301c0e040080d1903500a00a07584540c4200000141c04000001c1301c07015944 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 509417517 1250 509416267 509416289
    0x6021215100c020a12060212152d0d12090b160b0c0c0d020c120309010906081308160302060603070e060d14010524040204030510110f0307020102120a06 67
    0x40014001d480c0d00e1440c0304200d038044e01c0e0720b0000c591083c1401039140c2d01441401d01680f0340980c00c1c13a280c2c00390002031000c009060074858001c05d5644600302c2c0f41c03222200403511451102d61500703160141d0701540703410b80c200c3c190000c2d02d001c11494074000d04a60000b82c2c0e8030714160361030301f0080420340b05440301301c80c400024100901c042550544041e41111010500500e03000001c0d040c40e082c401040000c3c401b5070403c880310100350419000210440c000c01014503d0441c19800180c1124107500070b0204124000300002c1c448520046190056900f12901d103481c1c000311a124102c5000100048005024200201d0340c18180000d20205850120068108580d651003c2c00130440741007109880d90705014203042e428540a2084c40d0094203a400009121144001e0b104504c44141348014081e9104000400118a000c1000d941031006c1ea2404100c20107660b0040321036000e4154400b0300e87e03030004248502582c05600030080c0035110054070000340c0e5003c240c04203c80a507c02d01000b80 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 509418767 1250 509417517 509417539
    0x190302060c010e0d120506060702180606090d1401061d010b070515010909020916050f0c0a08041214010c0918060807060e0108160c031805040906021215 67
    0x11030150301504000d40404000540b80040d002002c0c58081c4101050300484d82c400710704442c1c48814010140d20901c2601e00078600003e0f9404075240d13840c5205229404130258010070030503540c004c00c482c42c40ca0001e10100d0b142d41c807424100b07070381382c1000d4010341c81d5882d025000038403044600009c140079a031150900d4891780b034000d44510b00e034082a022215070249250004c850811002850701911119600003070001d118410f004400c007018203d1444019021445050150300c4404c440440390756007019a140c940d103186c00c0d49041ca0060000f03180c84004a8045229030460b01d031101d08602034900d41150f8100807030b5182c22600c000039030342c002807400c0310306205c000d910b00c40c1c05c5c1520744030050010b007951f92101e2080c20141c890300080c2c002402d02d50f00016569100b140309410003241010110201d503044405090024140d0707004040c048a418954140d408000c25400100000392062000204a142c900001d40c4a4180c19070400c40c1c04001c103890400844510003080f01c007908c042815 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 509420017 1250 509418767 509418769
    0x100f08010b150d150b0304050c01020f0c10050d051f091a0f0f030a050d120b100e0a08030c0a1202060915060307050a03060902011e021207060b03011a0a05190302 71
    0x3a40c4443c010589042e140d252508941c4001c3c081c02c402820141c164640380d0900b40340090408001d40c1600f811580181c2c0700c1c50201c80c0100d14040c015030119450418061015010360f0386001e410911081240383c5010440e01b2400d08003800103954100c90850800750300c61034078400300d0b40391014500c10881640c80030145800d10880140c0311110042c452104002c068001034a0052100300c1206e4940003148003610b44e81d0031a6a250341c0025406040c00071241c1c440100d51000c031940340c00e40412004500245890b101d2450950140107414107899940c01c802d4035255035899820005c486024080b0340b001001d520205115006040c403030007610078100c06250285c0c00487c00781404e945409100c0d800983d035524041c0c410001c502c0740350301003030b10241c5000252403851385a4032510440c5503040314101c019070108000800511183c400c3d6285c8456082031130003000800021909503290a58644000110f0300a5000b0400c04072910100b02c1d807103405020b0f08400402c0041d81d02d444801081c401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 509421267 1250 509420017 509420059
    0x7050c1f0503280902040b04060b0d09060b0310061d0115180b070609060e0307240f1119180605070609050303010e010e0a06030b06010513080303100f08010b 69
    0x81203008001021544448040c0041d5044801a00f01c3c0300b80c0c1d030590f410171410a4015010201001c6504100061500c80b041da014400c40d074003440c2055892511004008555009180002d8080d044864110510301400c0080140d030180c41440c584040c500b107001800d03005a18142d8212030b00300c0155034501c003415602011038508032075004c0680003022135445406400351900070300a20010416807041e041075003c50f0440300748409981c00801440000c200100c0000c103902d442441c04070710100c5c40d481c0344001048a48141c032441030a1840e4140001c6410020b4840b04414100c213512020a0010565023074803403d0901b10742402c080c1c4d08001c1c0d540128080c00310180900004203030401e01707568460469009030070502d1803107030b4400140007070a4491103065000d09448001c0281c00e04641701c001038100014242410407400080005022540340306100042c107148003100e40703904107240c0031000b40b040c0380680c00b4460200000040c4c007a4050240c18007040c40906481d19000103002c00d00e02c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 509422517 1250 509421267 509421271
    0x412080706090c03050606270403120c0e0a15020c13090204051003031805100f05043512070807021f030b031506060406032301090605040c0309030e04020d060308070807050c1f0503 79
    0x1800720b08590346c50414014080c88450300d92540d378405c00d00c4a00c00170816078a00382d4201c50a0aa0440d11003410281c00150a00600ba411117024a0760b90080030100081e00101d50001d411905020500050318410b28004054a200382c840003d800071000101c04a05000d20400341d1100d40780100082081c0500d841034181401440c12910707094503074601d8001114040030015810200350595495011a80a004509030704140581200107464082440c1406091000b804030b0200052810441d0707500016002c1000c81c0e03034040b40c542c00d010140076000b0034403900954080e0050045482640d64691201d500c00c140007401c0508007800d01e04110001c0c0400105090b84a9814055860245800c42014000d0000301c40100b04a81401c0500050341c242c0c031002028982480c445400003600410016400f810135100181c54903010315402c4042c010a60000c1e100c10700015065090055010051803043c1c0117104468002c03403040c090000d4008012529402c5001d00020070071603e2040d40203517 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 509423767 1250 509422517 509422523
    0x509042105070b1e011a04060f03021902010f05060a030305070b060402091f021605030307020d2a140102061b0702012010061a0412080706090c030506062704 69
    0x504080b096601c40074509401d45070049426400c0e0a07402a2550904449024100450344c45480540c5c1030f04010840c0201d010302001d02c07203a2071001c50307007610035410759141d0300000400c0101d081e240d6001034002c155915410544906202c00030340b480c1014169042101d074150744551500c0b03416212801c0340e44024201691064003041014800da80e10403030a000880d4040701c0844000304410060325000e18688a5000d0030740d486010400c658010090b5040f032501a205040586030f1032030a5a0742c01601d000801c0b8055490141c0f200311070488080c94141c5d100109040020300102c070041e6600e507800c4070000060001050740c2c02d0031628403005004e045206041002e010100c100c8090584850400b501125502023400200500f010b4000c00380100386040707640f00750b01411061503840b0f03c5240940c00b5070809919a035020003054104407003601c0e41200341000b40140310315008803a00610711050701c00b84141d401141f0035143c80c0542142e50003400c40380002060420004100c1090014170503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 509425017 1250 509423767 509423777
    0x50d0f020c03040602060718030f0308040f06050c09180405030403031101110304060b040c030608060105060703020c030f0a2a05100309020907121401050907110a12051305090421 78
    0x49289041c204050000b611142d005003801e1318021800030804503900003c101c0300001c50104002040b016910000101e0701840c05007911b0380c0b907041021128100301c400519180c030f0300c000c100740c1c00c481b8030103000210401c5400381c04080ca400c8071082c0c250005d0314050705079007007007004000080c01400001b909607407050000c10390524541a29004c0d400864040c1d8519454410b0030cc03003031a042c401c0032614038460a00300801801c00c044c036a55890305002c3c143c040d501c0011080280740c001c004403820014024121444c0101070020a502d40d180307100100d811305000c1c1d6000d40f801c0c8014800c511070380b60500d6030861a41c03604c0c0c10840880b01d81c0007a03209269841c017440d009612a0f188662007001c580d150b95154007141c8241c04120303800207140f5142c1001001c0107001d15503855161326081045031400c02000c1447c0701c0303c2da082c00c07142e0398010700210052111591494012016041da10901204a41c00564840034045425030845005000c445400203500e144a0405050381c0e00701041c1c500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 509426267 1250 509425017 509425027
    0x81212070f020f120711030307210e04060b0903060108211e0a08060a09020909040204092306160c08070215041805040b0705070201020d0c15091212020a050d0f02 71
    0x1010342000080015130300c50610000f1214140030b440518181c0f901e2043e80110f03e0002d0940301c00ea1b07180020201e0b40449000030748200400c51003540303034075819000144108082950f450340181180d0100d01118081d0003800000580741c0c0001c80c004408001801d40890380c5d0300c4070300c0ca00c0d42c1a4840c24001c0c850b0a80111000e200c009110701030509075910f80c940044c1814090100403055281d60702442c40c2c180108180081c90302c40200c1c0642140d0b043e42c1c08607071980f1614044107042c54802180f25803411145526109079000181300307018600c045050200300804080440781c1c0c41d81c5000140c000c94007005007000504103100007211042d5040300b560b0409442e40980c1c0815401c45e05800005a180c0c0103000a2091342ca030800c0d04840581841c0d803500086038000b1752182d0054040300103021750807a40d4001c0c40315411440c180b020540104002003001880c00790070000024181000162401c90101c0341c3c203070a442129142001515902d040035107002031440034050701d00d200b40d9525001d01c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 509427517 1250 509426267 509426293
    0x201091a1e0c131211090903070219050603040807110a140d060605060d02071a1509040c030f0b0f1302130c030e07030305091009050a15051303030801081212070f02 72
    0x103c0070f40988614030035000010054106a059910183c640501c01d80c540d0381407211400c000012502d5684d0305844c0151a010460914040c410490703000a8004a00104110411400500410043d4456103614403041300074410301c8002c405a02913003144e41002a07001c074092825036075a180740d03482000003150300350301c50010981c260081c1d400a02c5480c0c012031070030b080081c1d0324464000d24044800d019001d14080c07051180c0314540320040781c0255242404202400a2038000401940d0016095841181c8900d01160309400488065141d4000100450040b65010704c0c2c2018698000b000301c0c40d28000c82010302e00170003a48808009040d91420130b080e10301000e1107000d0055000e6102c19441c3e0f480c2c08144010000c0c1c242948003007121030b8a0912460342c800724180291807400000440c0070321200002c0d030b00d0744111615602d052244410000c201684110401d0603a1140402d50703052159800e071007a90b0303019602c1500894844000041c45091103488640e442c1e0f00280704032030342425440 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 509428767 1250 509427517 509427547
    0x1e09080702100e01030e031204140f24060f101b1407030c061b1e150507110c06160201021e030c0106060f02031c020d06060201091a1e0c 60
    0x140094003c191480004010356030140700300c00d40c0c100d02801662500801d0030a100c01c1002c018001091300c80540c0e103200300102d0410810000c01617110890318011075100324140e1403036025101c040306c411a400050b40d00e0600d800c81017068039002d000d90400c0180c1c3c2c074041d0b9a44080c80301c0318142e0030011003241c0104900040d111004510380018100050943c141516265040c1e04440309004000441c040307200d11190b519061a60400b00801c0f1180c02003452070300d229030b41080645002a400024981505258801c40c0110840e441b805800080017030001e454000c040d005541c000780c1070200301c0c8003094544401030640d00c1407065038500595a015a10301c0c90380380039041410b03407000c102111006024800c19024041a0074400d881e081f6110000f5900d1045850300b01c0c0185000b034050302242025010f940101c594200140645922031070f000780200510030098807800d051038031480303415403c2890540620099040c4484502401200030f1070700b100074202c01ba11031010020019959401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 509430017 1250 509428767 509428789
    0x60c0303050619180b03060402030604080703030f021c051605040e1503010519111207110c03010216060f090b0f04050f010f0e150c031501180803040314011e09080702 73
    0x101394080780d03078408199402150342c2010b2180c02907100000703010145c2c1d40042e003149c1c4642d21143c0c85a81c2e81c00c41c68200c0c00b030400c41c004c030301032240041260840d43c150101c001520b51001c5500f00205d9440f0842c0740506040d1400c1c51000c11030411003130141c0f80c141ca4000f54040c910300b8054a46603150008242112011a5001d0010f0074041a040a880d01801128030940c0c07166042428100340c090344040e42a0060890410302662004c0704003941000d01804080b460014002c45d20380e800e50002900d101c0781100122005032078050780514045641c45900358032a00302c5129400d580c0e0b481910000130030040d105031031500c520410084180024010005081040800130901e0079459958a240182e200e07071542604c86030404018010700f40c0c40940341c0c08110b0499011040a00310300685403c22038401a5520320b000d5200440c00000c000018002c481c4901c41c00000b648207506007900320744a058002000c0d4100c1d282d0404d00038443c1d0000c1c035041e03004490991401005500040d84522a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 509431267 1250 509430017 509430029
    0x1503050907050a0510030b060301090e0f15060402030a0905070620010608100207021503090c01080c070f23011d06070504180b0a05100908300304080f0d0603050c0109060c0303050619 80
    0x19030414688540340de008802d14244108001c10081201d4412603403a44c00041c040c0b4042d950110008040b000700f03811500700150010191806030b85c44010040101c4580c03860300001080000849034000414030032030302111369076005000d030100c503081117101a601001e02aa0b0020725a80000c001c1c400300340003540640300f00402403061a1940c000540f5114004010080c400001e0050301d0215420720f20010105038840150441c8644800603036051480404c3e201d4641d40c030b800b400405602464200c0c030319503038294049428554540a00700c450b48035078042e45008541e117400d410500940c0d5001421034120040113000c040f41c686c004140c000300200d0320900010b551040030095407200344070310043c00786884800484060402000d4a16030583d25071000394800020010b0203124008054900525000c203006588400b070f203500d44081d00b0a0301090350540903422000d01150300802859048401c84d4456240604894500360000c05000389019000103054110100e00c2e111080c441c406402 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 509432517 1250 509431267 509431271
    0x605100c02040504111f17070e0909011b020609011d070b0313141507080c0708070609080a021b0904120804020109031401021b0102090a030813030b011503050907050a0510030b06030109 81
    0x41c04c01b000780450010300741107404070146424040e81c2c56111108450901003950a8078040d150424524010310717481d0800149510280210040d09034041031042c05202402d0007840441565810495803c40e10040c10f91150f12840c41004400412800703160720104180d00d00d48401891344030440c80c2d1405030a003614a0b0000c075100800c03958950006034222040f8681f0029601d00943c0c02d05c4580325240018060030008141141081825004a020070707902c51105c540741c01286e0740c065510b601ca45441030f00c00d94074004244007412b210410a00c6140c2000c1c031012000f608040590302c9035800f50099040044918010004c80c00e2940c2d00000101c003200016510641030120511020101c010941e20340d004001c021504d0b55443d0405050b650011405991030031584085080c4492036400180101c4808000040120300c039404a10582d44070386007441a50740342048036440700e0302c40c09429400846444180301d281000710505000f840c0174180000e100c1c41d9100024071f950000d9000760851a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 509433767 1250 509432517 509432569
    0x8040303030c0f0921080c0c0109150e010f17101e0503030d111e090f012607171005031212011a07240605100c0204050411 54
    0xd41d00d44100ba1218405240c0503285403080c1da401803011825104202024810f503030306032105c2104868801049074050300b002d5440500103252030f203e00e0b040f01440e0114030040400a69100341c20901c6059a290390741384620030412100564400c0d0029000100b0004203c03090300c041e1300604581130046080c40d5101b4100740c5048108940c1c2011615030800d0386440e503034100702c5a01c000043d5002e040302d240e00401c210012400203181401582010b042081627980100015103121001305130b0043c0070342d0342c850103038200c200654108000101c221240c048609001d10650845901103420648501d0015000440d800b800003600c0b0003a110038403401c10720384040049241c2000749501071110124490700b0445501c4450400040512070303021180c01c0c1440360f034900c0750380d001160780f0650302c001c1c02e01c0c481811544155529201185100c2081e2030401c020405280c8490603c4103043d0707690b0707448007002c00c0d81c1c06d0202a14001e00202d0340c50782001d038017800c160b807200b07180351544c0342c070140c2040c0b44 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 509435017 1250 509433767 509433773
    0x9030305060f060f1c09080706020301051005040308030a0c030e0703050c0f01030c021009170f030f0a0b0307030818090705070302010c030c0518121f05010b040509061905060403080403 81
    0x5510405809403084030100541c0604d0f40c2c450040d03070710543c02030300b540c1c4011507440b14500107001c1e8440001d042001c00207040c401c1103129400740d81654001e4070201c00b003013003104080e54288501d02011300004020f000007001c22075141c001c628070340e1207460082446c0290341c114515090301078004542c903400001c08004070741002d031041c0311580002d01e41808120040503000c0c0d00d440510f030130003401544606844d8140720380314260700e0301d400c00c4581c0941e4800381d03036485011641003a2074140440d42d192000c0380c0c80ea5454010080c00c038000038085e02c80140741d1380e900880c1da4031040415080307641032a00c116440e500c80107101e21030300381034461550780c440d01c0c9802421030708990082c0c3e081c54a0a8041c00409502c0f800355124a00c2c0ad11507403014448020020b084155110b051564910a864160500342c1c0c218602a201c5104000c0a00190f603c0c0d0080b05001d000780c0c0079882c2c00088000c00580e261501310355181f050762024001e04541d640b1000450301a9020750402d44d06840300017410410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 509436267 1250 509435017 509435029
    0xb070b09120307080705130b0a0206070c051002090a0513090b0a20030705130f1701060515090a0902180f040504050c090c09030609101103071b0609060903030506 71
    0x8080d84140151401070040c9651100341d0202601200c100700000d400159428021306c2114070021407030300202241139507440040747c0d950000d0400f0380107010715804102054020344490080c1c0e60300202034404002e515440303000039000702841550040410710300185640707400e045e110146c0306e24030b0081000c08117801c00656204024105014a0f490540200c400710041c000c03901d0f0703101c4131003021a170740d8480d4001255035001c3c101d10203418504104000035000c10841c62007088510140b1142c07490400c8010844c00c07200c5603c174282d0001000850f4004a1241a0042c2004100104501c07440ea46506918003283c001d044c2c144105891200c07858410700d44540c1e620000f00c0100c40601c040d00c2c0c295202c0f130302c0e404250307110f03130140c010f01010036078004403002501d6074103402800b254901e00d4a00115540d80b0a81d00d08100705a24114102d0700f81110300e07045902c0340250380c942d00d039081c0d40d051021000c850781440a4480da65985941000100d041c091410100d01aa03008100360801c4000c1080d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 509437517 1250 509436267 509436271
    0x8010609031101030c0e0301020d1406030f060a180f150f022106030f0d05040f060503010b07030e040b040609020d051815061f09090501050a3c0b070b 66
    0x4103100380c1840c204005045a900402940c0003031a000c62820f10404041d1442400d65040650550012905003910a941d902c0759010b405240300301c4519072100301c00e040d03c59102c0800020182c00c510000791041001ba04410100c41441615030781c800ca0766154a11242304904045650255250b07500c4400030041c02400c10b41003518104601d070844240c4c3c4c490702ca81034440a4001c039815480024844d64091015030b204240c8442076884009110000411607403150060742c40005d0705050104840d4490380580c0d0580381c3c0c40d03204074541410740e1001e503104101d80480c00c0d48243c403911a10461745841c01362000600c048a005038540c46140c4400041e81c000400032100c0030300007280150b210800160801e54203190340100c80042e2210004030310329012086001c5040005210200174071039100d06441d0884810040402c11643c0361410041c804680d03104000c03040d501c043d180d00400441616621419140c607c82801c40241309154941c20480d5038018a201c040201d140401d01c42c100c0705d455 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 509438767 1250 509437517 509437529
    0x204050c0d23040b27031e041a2206030509010b01110d050c0f010627050108120c150a06170a0b0a090503041809030e0303030601090303140f1602010801 67
    0x481d5008400d40000c880d101c003c3c00507081e413000b500422019081c20070041d100c1e5560700302901c2444041c14845a6a6005004010b40c007400d003843c042001c0b010f10241c80648020707014401d6042032540001501e038210205880d403500e440c501c4503c0314030440c8180002402071340c6011429240c01040c560071205c0380207a0030305104c000582000d24400104410071041c0842c184691100038440300e89250210315103001450350f1808401040c180c440c0d0382901c140100406044548000c1b211000b8143c440070b119400b01c0e64046112107819000040252200e00c0c004011555402c50740031203005458816120314000350390342c12062100321641d44404890303a4148004060b15041a9150104100010440e01d4490b641c0e58046c0108a014012200105007402c4042c01d042400103c40c1c0050604440840c00309564460b580042d080200c1500e01c41d2605854107a070300d80c9152001c1d034400324241c02c40f41c140c3d40200b01411104054402924030a0030f0490710901c483c4881c4005851f0340c1040c5c1000d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 509440017 1250 509438767 509438801
    0x60e0306072010060e180a03050403080f070b071e02010b0607081315120f0903020a02040e12040e100618060e0d060203130221030d0e07030204050c0d 66
    0x101040d80c000901d81084034089241c0340302c00300100c5140e420958a8008100560308041e800a600c2045102c201d01a0f0564032580d000c1020400901c0d030340311060000100400c009000c20408200c4d88005040301c030703c100d1961490b00089036a0301060b00c0c41100d940c0080b0f51085951a1149804d25074021a0342c4d1600080050349040030000d05940180c00e0000c040040002c2d040c200b4196040c024802016507121580c040303444241c0c09000351810118590a05140110b005103200307a9000380390700709030590003514901030a034003400050a00c900c040c0d003182c426081700001ca00704c00d40041001f80102c1c0f103403078460f003000301040c001044da41e0702040401803800e40c0660705200d80b00b405800c03101c1d241021400100e43c04d020880422002c94054071480c4044100040314074000002e050041c42243c05100002c0b80a90302d107000c0b040000da101036a442072021420445483c0d0007904d800d58210308996010f5941e034001002c0e40c808403000e9800300004602104c031503500307006240040007200c585d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 509441267 1250 509440017 509440021
    0x901091e0204050a051903060c050d0c1704030309260703090e0702030f13050603180f0a0804120204180303290303070b180703081305060304050c0402090316080106060e0306 76
    0x2540381d89145c0a840e00c1131120741030f034140030103609608a00030350b070026060008456001015001c1d8100c640e0031100c2c60305091340308010341d12078042c11190880d41030303035041c642d140c0d5101140280b0085104a03405450b503901c0001c0f22000038140d00035901d10800c25a910f02c0c81e8038004241142c0c9030700405820761904180401d550f00441038900404070350132040c1d15100851030400d07081b01658005500081c000091050f04101e2011501411209004841010a50f0b04945641d00b04000001d0803650f0140705c24030600840702c181410b80d80c0010b1010070744590003000c820384400f00d080308a000c280ea8440c200811000b580c0684a4201010340e0034031002070020110781c503440745035001001e59800b44000340c24000c0880e9011070340c0545900700d68070076880f4a840940b0750301400e00c05108802c0a80c00189900e0b1010840341f00d260300101130400e0725010802c0c40060741008803002d5050140550f613a400d4038070f05982c207004000c21b00000c500701e032601e04058441c0080700030f01802074200800b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 509442517 1250 509441267 509441269
    0x90f02040803030103061821140a0905010f09050a090b03012304080304031106090d021905100905121c0605011b03200307050601050a0b04081c0e0901091e020405 71
    0xf5281100c0e000200030510629045500d05480fa0f2190018016050742d61400c84c00d00c4850b1800805071310686665101c110044085000748c0030310708a050010b58010014030455105115003c0d00c2003550074101d40f1562210700180150f003007078001220701035070303a4000300c41c42c5003d005001960003640c60445050761038401e042c84040b002403010b0510803000000c030b0100352007142052491104401526860704200250544580d4078900c001c00511403080e0100a0b0131b119a0b40901c0994084000c020324445100007030042d0920103415502070041e9034088220103000c00090400c12340d82c0703288880c8100410101000c8444641000f070420452a081d00d00070a40c4424482e1501d4050810014003d03d080c00102e1490080750000020301000c260324041120004286068913402c8602d0061641c80700c03502e6590b8000d0b80b041d241254400c4c1c2c01c1808011132500802c942c05071038075004007045444004241414000c1c0d10005034180d44036000001e50103940002d051050010100703500d00f600d004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 509443767 1250 509442517 509442523
    0x190c17070b0f0402180f0a0f05100612020c030403030908150f13020307050310090302150609010b16060c0804030e150913180308100609060503010b07150e07090f020408 74
    0x518aa040030300b500080750941d030300d01c20520410b048950907203590b40f400d0303c005120f518094402200003428140503030302450311805200e00c01c03040040032200b00303454584215405c4114643c1c2001c0a81c0c20002d0015691040c00240055802522100161407528840782c0c40c02d050302c4420250b0768029010322030b440d00d000c84c6468200d08040802483d1858034000203083c00c4076070740240d51600c00c1040e1030803505c003a0b811840d0b00d54003079026621400d070010141c1080b10022146d0340e901c410900018001020161b001c0c01e9035106220000070104016036a40c01103c5c40c242110020034802d41c100b01c1010b51090214800140c2a00e80c03c04a0010602001030fa00418405611442d000740b042c1403450742c1030f48080e42d03c0b00c0c0982c0900d010301580c2005003c1c0351b4181e810344550a401d80c00402d5141c0a0b950050850743d4980d12585981e1820483c880c2c1c540041400b102c08400c0302c0c00030560800c10740550a15445103034042c00c091480c14030300e04211100d51200b0311040b030052104024a24000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 509445017 1250 509443767 509443771
    0x201140c0703030b37080d0309050a05030a090e0a0b0d0b132906061207180503030c0c0901050f0d06090606150c020102010506011b1106190c17070b 65
    0x25031441d450394480d140c00d50281200901040d041811805407071401100740301c45160321036034802c401c03119070360511008028944500500c10690700150101445034030a45c071125000c0c3c060b0007960000038190340d03100d0546d0301001140001500146050144098040c0d8642d04100b8142003041145408000708801400e01c00e400362070159a4130000e19106140700c11714500c03a5001c9101000c84410b10f08418050b0241e607451000d01c4028000200302d1f007040001c58010003c03800380070040d503582d400121200422128005840324403010002900d88081019091140d203c070702501c0748411400034040307145016800644203461341190900c0c40d8a0b90b040c41100650021004941b1160500b020006010f0580c0b00c144480103c1160100d515480701840160b14403d85c0280842c3d189c00004403883c041081030801d040d010034954030300040048035050b400701c6010b004a42880f51020003194a58022a8280080382e0304201c003004120100030722274401120b03803811508140d15034560504500340 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 509446267 1250 509445017 509445031
    0xc060e18040b0f0403050c0109060213060503011d04080d02120a1506052a0a031220040e06180703060501111209060d0b060f040e0907030803060f010302040905130b07020114 76
    0x1c0f200100e41414810011104103405610003884415030b14500301000b03511515849a1080c60400045040352050382124101c41105903c228418510605140c141002800840c0c05c41d0381040600b031749290701d00160191285009010752140f52801008c000c1c0d8106200c0391420107400541071007520f40050580d41c2c01111000040402c02a4600100035840c941c0039442c494800d140c1e1500c201076004ca07034114011580c07041848a040c007034032410340910382c158212112503000d01c41409407082060130a5030091008200e102807401c04508881002d1080ea00300002039190031080c810755811070070740a0031070508402010460700c00d07a40035215018929500d03102c2c0000040b00c1507800090b0b040724042c54030080c1503660b682000c149120071544207103e040603c2d0340c00f0001030350400c4003052a0044940080f10f4600d55a11001001a5200c00304102ca051660a11010552103401e100d451301c280e02c501024240c0303500c0c606140300c800000400c0c031000c40e8140440c3c0004084110241500400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 509447517 1250 509446267 509446291
    0x3150a0e0607050f180616120518010e0f13060807051509240409150b12040305030618040b09012702011206030b1f09110f160c060e18040b 61
    0x9102140840229001006a64000b4001c00d0f07c00008071016800c140c414400c03c08010800001141510a8020924140804913203401c2c5508a54040c41142c3c2580034024103203507410818030300003016081e241400c1d80b060f0350307181d00600540b00c00304035107005018100c80142d4242c1c08d080d00c010285c07040500481c0a071032200ca0114882c06030b100c01c59040564072251503104c949881080009001d40720800300c00300800600014050011030880f5844004401d04420a0b5181d407000c0e1a5a03002420f03098009013190a071000e50f0f0307491482e86008910550b001001418495000c0d829074510141c19140750300581c00400586140c00605c1c00400d90a0070414103845044140ca07004019aa10141c140803a442c20415000d0103003104040003000041054403203602c8110306801c643e1504182c10071240704028540a10440d03102401c031000d540c44030f60b000d801c01999261481136095104034049450b100e0190950720301414000d1035403209040c2200307e0b1610380c6078980558005003940041d1a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 509448767 1250 509447517 509447527
    0x70b0a111b01091a0702100e0c040f0204031704121e021002010b090a1e02070f0c080714030d080a0b0a0e011d090d05250203150a0e0607050f 62
    0x455031015205005410080701d031807401e90314803480c0608182c0c8000c94070000d1030052014580b25601e480c0303002e141c0d03503030081040c4036412004200034040604490083c1c8215584000c0c155554000d00709055030f090b10168882d861460300f252426071290400303001c06000d003c02c1c00088418040415030315003141041da41240b034400b441c0510182080081d4021820f0341d6802c0010781c05405c49104110143c44900840c1d550b00c2d069400c0b60600c540c8458007009105e60035403050b060b41c01600d892801000d1603d0546003581c1d4102c4090407680c00710000d1b4203c007104020040c203400f003100d4654010350240c1609542807100030441003004106991131075482d5100c4045840b044009406029022a0b6004950319200010b45100c0c203026000e0660805c41c000442494000c01c102c6103000b4151541c0e424000c40507410f58200c995041e03a00c0082c0c0b064080400940c0d010010081120429440c000045c1400c000910075142140e080c1d003807580c0300c3c2060000c002d030710200f21410110801c203201c0d214 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 509450017 1250 509448767 509448791
    0x603030e060702030d180b0f1c09080301051e030318210a080f09150309010c0903170a0212040e16020109020f06160c080c1903031704060f09110307050303070b0a 71
    0x14081640007103200240105010b41c004403523800410b04180b074556002c500381d6109013440e09070381242030020881c49040c4010042824403280c640e071034800944804102119020110345180c101c14800c8800555004c081411400c0c000b0302e1001c00076040d85031404180400c48401d550f0202410014213080002490a011701d2110040d6104144020b2007104400e404041d400c40641058070040219464445116003d50084202e0011664004101150480c040c021400d054010804440039070251500c0c043e81006508000d1010b481c40c42e040316810f0a007403074030380904009103002d04156890300405c0c8016950742074040035481c0c07048810550700d221006a0f0b50442602d0300303004011070700c03042e40440d2003030740400c0302c440700002500e030302540c96800302c0100452301c0140300240c081404800d1900d490340b04009030030f600600070321010074101c1c1020360100403160802d01c20f940b00302c81100b690f030ba0707031a050000c03000901c812130065045c04002e4450b9100140c020300b0004001d035865103035082c9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 509451267 1250 509450017 509450057
    0x121006061b3f0c05060606090a050f031504061a0105030f24061204110406060f050c0a0f050319022a0f0414090f011a090402030c130603030e060702030d 67
    0x2c8400d004181c0c940d01d241850182c2002100c0c60304841500030a00021030314145081a100e1000005241010f4a40303084240b001c4104071000741c7c2d415008503040000f01d00c13110310710f486c0510b02ca6080002c1454401c241041901c16204086040000400034055000005100540c0040e0900080c5d100410212400c070790a840711010740d508074001140c4c0000c0c0d80f40ca50102c40c4158050f802d00100704c44100c00f0041140d0b03641c040d00020580300603c0482c5544030380d01815554401d02c0803542041119154003074a065500307811031300342e803002074002a81d8049a45d54106d40c84a40000d00781e0f50011082c0c03584080e48120070f20360250406803005420707501c1d0a0103a543d500040c000700b00c01c0100104203549988200c031203101034400c01d601c52480303d82c144241c10b020b98042010100000d8400c3c10800119009441030368941b1502c0c00303c0140740c2d20340c400c4440424011030000381a505e0740c41c015000c81003018000f8030030300003403202101503140030039401c0c07132840300d0700d0683c41c003100600c42072003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 509452517 1250 509451267 509451353
    0x3040b0601032a0f18050306040b0406141302010f020c0a0b0705150a09050d090303022107150b0102010c1416080408030a0903020a050301051014121006061b 69
    0x10100502003d20110580c111101c0016401159030311007050050300d1000403086504e208260305a031040c40050041002c45030090340207882000d020403000c00102c00301e220b50000f030f41c00d9076245008000b070004541e00400804443c20250000c5e00407083c42c900004c03244200d43c4502d048400d00007c0c1001044000d021324011106c003064460441d0500b140749a00030203040004a9135440350151481105020380142021a54140e00400008400301da0a480320b8200d0608144070090602041c5c0c0081d061607030a101c42403c4160000307419009800081c2920341d420100814407003403001c4200202c41d504215600035520b60b100d441010b56030b2130020140d10560b070194050380804a00444050b03400348200044900031540f40140c41e448004040c2211400d0b00d0401e100540c4007010801c61100e8184004020402014010f40c1004098200d0501d0203001d503d40c05540d6820050001030741060303902020480344003c1c10840c25540c3d40e031400446c05a0703a00c15024032282c200d907040c9081542e00708 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 509453767 1250 509452517 509452571
    0x60d110105182d0607050d030f060306020d05060913020108150a1a07120e0918210c060c0316080406270506010504020901020304090513080f041a03040b060103 70
    0x10704080e91541660546014503920502c0a01d0f8000c000e1541e490208143d650880d0850050000304802c000107800420340c1c001d6520f41c9541701c0c980000492400c2c40986604400c41c030f07012403540307040010040c95040040a0000050b1110600d0000d80d0340314100c190300c1280801d410a0195030700700040c1003103104c0e038800d10810401300c44405040b0140740192903034034824510b80300d40403840c2e201541d43c880144001d41d0000c0c1c00301300003901d002c10701c1000914200c0e500300340d4000c40c06000c4800d00c58280d2400400324094005250b0f200703141c1c10442207500078032450740181181414025550381003c1585100e040180b00004035003070045590000c469402003c00d89469102c07080000d00c0c0764900c00c0310582e098010400005458107090080301c0b1710040590181d40340c01c0c1440c10400c02400003800c031000c031080c04003203800022540780003018150301c00c96806484610b021015126444c0102c0200c211080030310a010008904a8144d0740200003401d003c40e600329901d031044d070039205d00e41504c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 509455017 1250 509453767 509453779
    0x17041a090f0d0302030f040b070306231809070302091801090f0203060907180c02010f110405030f010605010903020402030613110c1212070e121005010e060d11010518 73
    0x40516090005244000c9107450390544040400c0078000350200d010455008401d00c440c0c0c00003400040c2e041420079440000740c10001286510b40d140040380201040c10496010300d0092400c043e85016240521441c2c070954015500e458101080d40e107038440d601c0300034011f101001c04902c02411892360300c0f10849031000200706098141c1000c04140341e101d0703010380c040c3c0500000b00d0000c0b200030031240c0071b580a07122070140141c94405150000c0c00e00c4680d500865583c0d25441e6000d0a280c052040c00001126501e6215400c0c542094141140c803a010001a850010100966608203217410b0403a40c04031401a00e80c0d54507004198030080002341c002040d490402c01d480203180c544040c000c51040b20089820b14030300c1c10500380c238511445c00f4503aa0010008005568540320324142d9081d0345c0003401d004014840c1c0c1c20224941075003500082d80f007544840040c01141921011581d100c1000c84014014100c0c0c0d0700e5000f9010301021340c084c1007000001d03d244a0a60b213410030700143c100a091 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 509456267 1250 509455017 509455021
    0x3220b040215030906180304170303061207060e01050f0904240902120412090b03010e1902040b0d0b0103020f0d0912080c120405070306020403051005010501090617041a 74
    0x21919090045030100d102d5102c80c41d0842c0b05019800650340705054001c01402c1a0720381e0018050070a0b40c440d800c44080c0f0082201040f4481c1100749444c05140301001546c490800d01c007004801b00c40b01880b91100d41c0001c504024050303009071041d003041c40a0814580d2806070307043c00f0006200e680c440d1071300142007140300d288100300d032568404410300465a02d2900e0340c58807e450240c0c03050400340d0b00d0030381c0b0102c040b902040c0c4034011288104150308010750010707910580c000250300260b204004d01a0218100a40078049440d05914199038400441c980b41c1004030044507809040307100007006503a0f850942050f4040c0d411201c810b280740e002c04e900c071a02c000b0800f001d408070000880340c0341d0008510114403400307001550302500607204c1da44d081070140301d801c0443e914002c04c00c0d5a0381c4184040003002c12428070007440518042c5020301980075482c1181800e596040c0d20542c10000760b01000c0180550121140c01c036100c0003c5c1950b89034a60782000e40600303007603081014080d080881 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 509457517 1250 509456267 509456273
    0x304170a02211b0c12030306103504050d030c08010612060f1205071d0c07110d0308040203061608010b090a050406060921021809150420040608030f0322 67
    0x140124500400701c9500da40d40c6501d440c05c64a9000c141c0d9000c0c2c00001c2c117141c04052a01a03002c6007100e070300030000e9000b08601c134041c43c5400211210b002e098401640b0606c000c0c00014031660941414500b4140520160000000c000c00c00501c0758108004d0000c2c82c03009807980304d41015000301848c01078400015141c006101c0300703041d21041102c1ea84940c0100140030900b51810342c00b641d2003a081d101c000c1d81c0781886250796074042103046404135440f0780300c603d46644059100c4445402030f83c681710503203031610500d450a48007401d091041c455071090015031940c03090f0f1301d41c1901c01898101e0b4031012840c01044901e542904071035407180c00c1220220b5a10ba20098001c21181c42648403800860f02c03000f0019010b07103e0304040e400002801580b1155401040a01c2c1c0001c641411100151030241f400c24008030152000c40da445c010710844d0072821580c0710f1002544600301d03800c0044c86e20300801aa940d2142c4141709604960100024140420342013020417103402000d642c0700210b10782d00d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 509458767 1250 509457517 509457523
    0xe13050604240b1507020102030c0d080105130504020325032108070906020a0b100b13090b030f19030216031101021006060e010c020a08030a02030304170a02211b 71
    0xb80400c900010b201c0ba0010b004446025900030694040c090070181c107010140c40840e036000200c26410341c80304114142d089007040201d090340e034000c2c1c1d45e06d94017541084100a000301c042100c0d180d966051505003c0580c1d008074551441c0c81b5004480402180402d00002c00b45051354801f034066102d50350f9000c14091280040d60100310240e590080a5450303410503a607141190195000503480b01e100040001c407903403484e0750402d0b0140d0340f0240c0c01e55602000310b010392040110351046141c0400c2040000d01c240940044018101c000c1c040a01c031111010f82d9400240d0b84d148510602e401001c810701d07000740108000b009040701400719581d12402c1500c031040c1030f401444d00520401d1126010b0050070b20819007520304590780d110021405900440c0c0d42003c846c0c040c0d074020641c420009280314100000c211008141c1c000c0c40d240c0c9041e003400110214a07206055400004100c001005d82e4041042e811085030300010500e032022180d4440018001c0000c485808400910302401da01000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 509460017 1250 509458767 509458793
    0xe010c0201050a061208190e0d050319050307050f070c030602070c0807060f0f0f020c0a090b15120c0d0e070909110d05030a0e0d02060703051b070e010e13050604 71
    0x40a0150315a00c6010a601e9a1411700140c02400b052003503030f24a18040500310000d40e00c910304081c0c50740b06140090f0003280084000c8910b907000080d0188140641580084a212682083d9045181030400070346544201d941c030100c82c0500040f03000402810040c004083c41d0001821501ca0b00e10b8941000a9a240d000b51091445040000100c291260083c510f03010b009503290000000c5407001500d0020080303506c2c81c203601030051887c00f40e031108440ca1001b001150070208041050505102c0c500c02e0303402c0300480f090410007011501400c100100b07500b1454100d03170141daa10001100000404050300c143c106401012800604001c0c540c0014140b14010308003001403040384030401c1030000782140c009046400c10300000ca000e43c02a000340300c05010140010807040a541c0c000f80c81640240404c9001c0b1b0008110750b040c2111408001794072924010050590360b09111710600030050520641041b0340c1c820000a5408043c00c540d1188035070f00c00c04486060900e0300e0010102964 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 509461267 1250 509460017 509460031
    0xf061503091511130b0a0e040902010e10022401030c0515070c1409070c030e0f210d080709080c040b0414070305040b070f08010e070306080601090204180227040e010c020105 76
    0x3113900007083c1e00c01c006084442440c200c0d141c3e0b401c88044007081c800545078003031090f814480c482e09044000c0e140d02a0036610241103a0203420300443c48200e11200341c110815171803052501000500020f81e40310300c100181c4400f02c030406001e00440e40141c11512408100510400d42090001410103c26903a000540001c1b580300086540340c4034200d408444500b0068002070343d015488003541440044a0540c8802514081c03140340e92260381c1341c240d0000c0d4400311195001c480d100004030380c0030010301d8111135a8030700018071502d88110140d6840f80809298800c580d030384c0b803100140d40d40303a029103401c9965080d410618a00008040d004150444050b02c5002c0120000f960451107403408901040203a180d041290742001100082c00c08018004400d1655400022402c2d03242080164028840003e01581c0c030b03804c0a40300558111340101c01c030100307030051110400b480740d0641071981c54030314031170340b0700c3d0a00e610310004016080d4500d00e1701180d46802030b404503066064014a110b208 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 509462517 1250 509461267 509461297
    0x7080d0e1008190e0709020705030d061502061501030213060c0506012403050408070b040c030c09020708180f0604140f1e01050a1211040602010f061503091511 70
    0x402007058400010440e00c403800200f640800c3e02980446034040100886000201c1300220303103444020049901425054529500c0440c00705c607031a2560142e90050003210300050000340503500003070b6130f800b070203031212100480e20003952200364883e9040c1c4101d0400032000100b41682e40801904c2d6400c9110182e509004541c0046090082e031801070b25041c00e4031410020380c15501500b10001d09010f0400c80314650200080400700c2c20080c030150089000c2c801c5035032100d01e54034140303808091951207801010b005100100c003140c0900309844c3c00700481100c100b480b60100340059041d91a026000d60300440205002c5280b80880302402281e0906171281c102d1569204e04112100c544c8440e01c1c6048601c04032900003a52150020700030316507060520400c0da60390b80760b6210544a0140140c41448000304041250507824069440042e480ea00104002400c0c0001a000510301021074828583c0b1080c094041002000510b042d0301d800075401c2060081007030368040d00d50300201c0c1081d80342c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 509463767 1250 509462517 509462539
    0x18150409050f01031101120b180603060f190513060e060108010e010b090703090305040305190b061002060c090d050624060c0c01120902031c020106060e01120e07080d0e 74
    0x140b6001c1c00d14181c0c3d40000d40d41041840301001103c0c000e00c0c00c108441811348078000c480380b81d1281c6024051040314441c40c08900e161142c14503261200050802e210b82c8900818403030700f1a138a11240c00b00c0c2190304004615a0348000456801c8000c0c1b01c0018181450061111520f00d004503c19040c0e13143c010090200304100c0d4149800c1e140d0410056521403c03000100301c16500991081ca085442410a10b0406943e9107540381003a4107030f80942140f0690002c00020040119415640300401b2103c43c031010805038402035503000d009004d140025000901e0030010340e40d8100700e42c40940d01608440b0303185400708514007280d04500c9004588403010015481e980b4217a01540c41c440c0da800014007003078110000448030068a040e401000a03a601c03140710245e2820b000c00c0003900403440700c842c001c040150009003150450742c404000c00a2444080700540e0707000801c8800100700d100080f4001184a450354246582c962000310b19110710203482c151a034201540500050049590241c45 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 509465017 1250 509463767 509463781
    0x70510050f0c070305040b0a09050a0f0501090f03050a0f11031605150a0206191803020607080907050102030a05030c0415020616080112080703021f021c0c0f051815040905 75
    0x103000f0100b0040226001b07110034000003d840000c1d1903104202e01c1c1c10744406a0781c4021900d165041d811003084141c03000340611103940c00a4401000b000400310380300720280385071101074440b40311400081908550111207028000324103c0322054a10081c2580c10840090301d15003180f517003d2242900541288011255800141098a072101a2130b0050480c954401500e06c070211140325100807800c0e903034502c40404600c00722030580b0f4284260020b01480c14000805000540018025212940400001d00450342e0200646404403494100580c490700d541824190070300494200c24541c2204104001c08a540007851500901000c80180c034004d112210440d1403807401d025030000054213000c2d004c000b80d081d40c010129140684113641301c10204a0241d40707800001071985540d680c0114001d04c4505200f40d02d40c00200c9685000c118500e645035000d0107443c400301c146401c0c41000308044000d030381804900c510000780280b8001d4003039500c2d00001b8a0760014050084801d140c14001101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 509466267 1250 509465017 509465041
    0xe040506010206070804080d0507050c010b03011b0315080a11150c0715030e070e010f0501020303060901121b06170f0421050912070602010b0a03150f02070510050f 72
    0x2a0300c042c0c0c082d21465880440030741c0e00010190046071410010045a090030300385100340380c0204d059541c1c1a990354060f08030366080d98600030743da078442c4e450403001d010701c400c80460007001c9034500c2c100818000c6070121100c00d51690f5600008203805210301c104208840040c3c800100541154124040659141c2c03513621401010b4405410b03521a03101440315080034900170f4582e00c40e40c58040350108c10341da400d0382003401c60380c008100caa01e1480140032050102c003850f0080d110070f10055040d46401000201c03038841c184200c0f18000c00c4c90f0149424010700840340751101321090700001106956040c000c04401070403c0c5207480c080884040747e610540030100900032500a07103412040340255180d08004c0150000c0d09003030020802451216886607482c2100340c50242018002517845c000020782590000c0309040e00c60506590103200007588070113000c01203001d520300000c1c410030018a440c001e110707000c8050920300c550102c6140b0b010654201a1141541e0100e0084c207403101c50404907 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 509467517 1250 509466267 509466271
    0x80301030c2309060d1a010e07020a08040b030703061a0d0518030315060c0f0733051c0216020406060305010b09010302030603070f0b130e01140f040b040f020a0e0405 73
    0x102e00e21500c0000503407480c1020783d032504a01c008001c9148543c1550741d0752921741038000040c1400f4660303801007140796695600300364040c0f05800507114401c4107944400700b920a60082501041d00400401c448503c81d0b8032110251040d6414000c88025101102e9429003010052800301e42c04c0500007a001300c540c10301160511405001075066480b01e50040303660701d2061442a030440420b00100606030800c100c80c2091002c04006480b0340c504042c451040c8003070b140058034860b14030115074800702c01d000c03051a104162600c1d0403a06c81015010903401c40d900160b55030300300c500220b80d0341c0b0340040c1107054030a0360384211b030708001e80c2c0da94000c11f0b029183e0034419400310000030300140a540d402a00156407200005041e0742000e501c40f44241f0718410140c0103014a1840071070219006880102c4100c080c040440032900158545060b42080e101c08410b200d0040a81507000d21140c0c40720f421039442400018400d0065103880d80800009420200000b0f0002e581c0c2d0082801d20b092900c6254 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 509468767 1250 509467517 509467559
    0x50903120928151d030301060504031406070f200106090c0e09070e010309050a020907030902090f01050f01210f0219030b15090a15030504021f0206041211010207080301030c 76
    0x16920000f400350b540040038141010a80005504201c1c60690414401940602220745405171240d0460070280701204a22a5904440c5d21520a00c01c5076034002c41c81d20f400301140d06d042c000644c81b014151b1402c0e40940c0e920000e6609000d808130700003a86410940300d10200c1d58900824028201c1000040350301914000081031102c4d01fa013089500c070b500f207555010301135005c0360b074001420b40c08142d030104c0c115000320000c2e599140c1031303045140c20b6075880c7d009a40c3c0c3e07a403410380394108000505280b090f412201d040c0a20b00c00380c00205079008400305064094a5002c00c15a1a45a518806503006452041511b1400c825000c001c0d40284602c000800c006848410a0020341e00c00d040071358010241c095201511510004441244158000004110369400710b101d041620500904c44c40d080455050380d124030241a11695000564a40c42600f017415140c0c0032400e1081614103111050030704e0f146500000e6040140120407004604a0713118422580a0f2070b612540c185400709151581 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 509470017 1250 509468767 509468783
    0x20d082125050f070c080a030306050d050d0c0212150103020102010c020102120105040902010309120c12211508070e01141f1404050a1707150903020103050903120928 73
    0x1e04140da2042c405440300602000d142450810b030f94441d44200071065000008035030101e10000105a450300880c0002d00717081e100d030300d03512013035a940c1c60715400e116503000308020301d154651041d0741e56850341030001c107080c3c02a648400e41034170054100340400d00003a400341d820090042d2005105108451820300000744e40841a428102000058806808141e0400d41c4441c0210040365081d0003138240c0716410b4030303946c90317030809850524a03070342c01069140d00388407007d18000101140e07890b1180030341c0c12580000600aa0128000c05a080301d50812007441c4140e00340404c0000000c1f42c1181a903080124040030000c41ea010403800d450b540096024986444403040e140d40d002c0c80f43c52000340301c001704041c1402d407500d01054440300d080e80243d206144440c050011020180880340207444900340d980d410408a25015049440c1c51100a041554800c000b0380c041800f0304c1964449049a0100c88142c281000b22903640c0d80852030020703d20114040b0300400241c414840c000c401d51080305 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 509471267 1250 509470017 509470081
    0x3030b10081e090313081b0604140402090409050106180608061003120e1c0b070c020f100908060c040518190e0f070305030a02011a1804020d0821 64
    0x7905042c070001e0010040c520081c820101c0b0403030301d020b0000160900d5801441c01429210140e290725182a280d80d0107181c040109100100002101400d107040a650260b5240110008100102140070300030300f00b946403d03000704608461042040300308071102010300495444900e6240c860506865800135000210401c0001802d41111852054500d041c89040000e80b0004500f031450300e1901c40380c4a010004900e03007040700c04044207400031000d180c80c10258030680c0c0407a002d0300c518401c0c6c07841a284401c0da0300b20700e80700e8181503018140340c20607501e130f41c01e01e503014a43c3c942003801150301c25024803002220345103804100d14800c0004001842c0140c004203400c07001002c8844982815002c0c401e20f945501104110410007580315900565544860810090031a801c040c005040c0d455808041c1c00ba6945400c240035045c035070611000503d0721030388005000400e80d81001022040003040c024000e801d4282c00660070300700342c201c88003180d0b2490b80b8000b082142c010841403038035020f28 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 509472517 1250 509471267 509471311
    0x2615010e04110922090c0501110606010c03051b0312090606240d0902030d0809100c0e150412060f05060d030c0b09100603060b0f04110a0f030908030403030b1008 71
    0x2104c0c010007850321001101202010310100190707105500203682500c10800100721650f40082c41141c0c0c4404000980000e087c2580024009100e0aa01500702711001c962492400140b00c03621282403030050459598100384102c0c10141c101c02c4075010003d01680c0c0004200f8240000c0242c07240b43c0c01e403803454030021030000c0c48100760811000481c81c1d568404901380103880400c1960703540360903070302c0b45000c81c54207091503032520801c10178140c401818056500742c402d810808101d02120102c904c450798007908108940240500d80c1308140007165401d030300d01131102c0c0c0e40c840340841600c09020700c07081c2e0720b01c006e000c080c0c0c0580d840240020b0000c85400e001c9511401da241c3c01c1803644061740c4c000021140c80d00b0030355950f60419252141d40e202071042502d031154a0201c15641620180245250402c600000c5d006180600c0b041c00031400c04000314030b11039804440740b16801024a0303101d00f85802c00034000c150102d0803030300a01203407050f0006c85000d01c07042e1707125891403444e807415000198 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 509473767 1250 509472517 509472529
    0x8030415150b030a36170f0c0601080c0a150e15090a0503070f0b030a0902130f0b04060b03010b09150d0b031002030f01062615010e041109 61
    0xc0101115555901c4807000c162040030081c0024511145102d8490814059900c04c8038080504142c4c0603001e001980d1052034281c65000082d05000104100d180359828540c007a001c41c40d90107100b0500008100c081d400c00782001c1e046d54000031085807150fa0321042110342d2484021012540046a24000c00038048400d0054145600d41d140584141c055040802c00c0300811803080c1103000c0c008078a0340f100d401e1002c103580003084210000e2200510b4490f080f00c0780d000f03074003400500f00e00000001c0d010304569040080c039564084c010f20f81c000704c0780da101307001000504400c0901504080c0d4000643c506030064806603001e10019510316440d005080107540c1c42071521030b070409450500740e204a881e040141c5940d05010401003070000f0650200760524507000c66400d2000d00c18014070102c82c034040040b1741910b02c1e82c2028060504040040c0740c54618031400501c00e84d0010040224040c0300412007515100280c0720001c141c01e41034200415540191801c03c64000c1c00d2000102e149420 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 509475017 1250 509473767 509473793
    0x130311030a0501060306020c15130303020306030f0607080a05010608091b04090c03080307020706021203061909020d0b01090f0e060607140303040c0602150f280c0207030c12080304 79
    0x1412114522000c2e90391900b90780d055401603074016408514050403410034411038409a4140c00c5e0701d038541c03230114031070b02e0b08211602c1c018007015408000a0100d0b02d00704081d29158a202080704e0003032615000c02000605c0444070801e5250a1074000205036000d003c1003801200b045018210202d520b0b25080300c0003264400b0254081d85528080e8042160b0b018a50701130344c09000003641d00d01d03100300c01a281c1021540903074110b5000440304402c19007041e007a00c0c0c0000c4121500386005032004505000c6020503000300a52610000d1a9503804110fa4015424480c0c00e8840f165040da4800700030341f0a030020311419001700d1981002407911b10744140104803040c031070604094221410000f003883d50f00212400c551000c4000028031030144c04110744041d034115207801c40100c1c60070041c8901064070103800840015810ba1000c6201c2e00b06440480110710755140c1044020014017000b03644020500c070580c3e00014418001c10074034a649021031380300d50415145813540c0c85540d61406500c00d8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 509476267 1250 509475017 509475019
    0x601030b0f2d22050f061e0102031b0604060e0601120b0c0d1b02071e0b0901030b0415051302031501050c0a0605070309061401050102060c0d02130b03010e0705130311 73
    0x1c4800030a4aa41d40450801c0341c00c615070702c1c4048080100c001d4001c0b04d00281c110b60b036204150081115950321034845c0040315040511907152022101c0c011f1b80b4500070701030741049030803481d65140e20340f030f0300054440e200718000d1230b00380a01410b0303280207038035030000b801403841c4005180000c20100da414900301e40c00c025500c1036036113001403010b5080211951540092803000e500c10041c002d059040140c080900060b5404404140f00e0380c2403940f45000728429583c81050105036511a42e010f944050f41c4602c0240044c0075001804034070003903080142c00f40074460407407800b1180c90b251345442030b00d2050000d24a00e41149003d0001900e4607000a0442507140c4501c40e080300000d1080d00030107004d4001d6840120b800038041c0342240079105032082080306060018010481683c1c0014041e80000030191103e58960310150890042d22034510418a48503480d00c0001d8800c400c80c00960403902e44951990554460106c01c4032144111000f0482c488011441880424500c15034950b00c84c1c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 509477517 1250 509476267 509476339
    0xb040b061603170f041205090112180611030601030e031c0b030718020d0b190905101a04030302280209062b03271404140f0601030b0f 59
    0x2e840b21221203000404c441000c0030f0303c01e0b00240820401d52080f20b2150002d01c0c108941040c05210000b0240b4032a82c205054582d200d0040e0384120010540d02d5003059003056050107480040e04e02e100c6a07920079502c80e4000307403804024071882100803003643c84981c00182c076070618a8154649101411490a4050340360188140c00600220854440480346421203405619228115000000c46801001090061032140d4243c0001611001c3d1601030340c5054030001a161241010070032125032680080c044500100542403d016452018200700c9119071308035146520300c0403919240454450344801120b5801c20b2283c01072402c001401c1c1e001c940500016800c02500014070030054004266104c0c0d08507849003c414140c1c4014480c1e10640d00e032142c01040d40000d00703da40100114070030015100e00070600640695590740000007551311300181d0040c941065140514111829540e1030701003032800e030310543c035130800b42030301142103a0042c05900400103020000d13540c0017034042e08206002d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 509478767 1250 509477517 509477537
    0x1091b050105160501180b09070b0a1215080f03040e060d080304060905010b0a030b1017100203090a0501020307120614060301030b06010207030b150310060506190e1302030a0b040b061603 82
    0x10700d1b985140c0c2018020f8040c0c840a0030b19038030b50f42c20301c1196004446210010030400c441503401c11750303c405442695a0008451952109440920340c064001c1c840c10b00850340800341d10100080500b0940781e440415600c01e0b1111010040c00180040e0010001d410620010b4045101ca9008403456805000041a00d1100034002464a0307032581003140d030403202c06c09102c810702c41c07000024060030031131b000000383d0503015050f1547c4121024040310203e40000000340540800d1081484c074a034040020740d22400d1142d0060003e021848403c10810310748034000541c0451600041c0340740c5009445145140d0841e00d8010a404000b01194154820b00c10004000703104040c1c02482450202c600c2285080c1c0c40c02018101030781c0103520f051403070810405101d01c0c0d03150803c0721803645614108500800304d220054a1a20300d481c0c58a40c811004501c03c40c040001c1c0d00110f114003803040d401c0021b0a40081080111403100c1d0886400c00d1040c0552030070003401c0000850a0b6000f070900107665 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 509480017 1250 509478767 509478791
    0x3100b21180606030c0306130809060a0807022104030308041b03200d1109190e0106050411070f03110307050f1b1005370201091b050105160501 63
    0x3003442618401024041109526034030764040c002c0e5038100e0001c0380902400d00c1c5440000e42c0c0d980000c0d102e160300000307221001c420000442c0480b0164040a00030039203841200a01402c43d800445100c405806031807400c2c180f5150071007000b0400755081c0368803400c09003951002c40d04004000c00884400000800d1594000e4101c0c480030700441c415002c1701d410049824000c0c5a845808481074001c3c0c03603401003140080c49900301d04103640c005484d00c2c030850b0b4451200c008108400c0e6102075501d031800c01e08454104c0c0640000040c1d0300141c80500141110000d10002c43c416082c0240040d0404030115000a1041608062260a000499041c90741503100d107410845407210b00b9103160300c45982518501c8800d00d64000c2451304450000e04074021100140c844d118101e950813982810801024105c1407400e068900302d51802c803149600b094000002c0c0c001c190007141502c0d242c4819200c0003007483c040b84010151081a911282401040f807485049074401c0f01088407655254484240c0c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 509481267 1250 509480017 509480077
    0x905030109050601061b051002180904050f161503150503101a03070b0d0e1e0d1202030106020a200402031e0c041a0a02070f0b040801060b03100b 64
    0x6150151000e00840e51614170040c10100c0490070902403100c010031500d000ca580820103a4514403200c00260b500c0344c00e04054201181d6146210340c0c01703503440307081c0404e0000006034100c04001d000e0480750380f00d0f07617034840841c1c011603442450400743c1102c11500c0c28038441e410100294002c0b6a18400c441d0f107070b0700028281401c086410040c6650380302103035107a083d0842182d818202c00e6002d0600c0c1400c3c80040b440912500807105000f41e210388031b206401804000f51350012580c050781e14192040140e41d25200d980401454001400d9000c0d4501d5902c014422070781290300e150000c000c180403941d105c1d040500050300c015403140e012100107006403220b0009522076071006409000c16050b0083c40310300400080c10031141c0e6a0f050009100705183e01405032014a450800562503020040c42245000400e82090301c40340015000050b0030409032003d0004e59510100038010b050301c542c02030400d030004442200c1160505c0074100440f01d690001848040480000689000c10b40c41e00505 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 509482517 1250 509481267 509481281
    0x2010207080607020d02100905150c07060f050f06180114030313120201110c060a140702030d02241005010c0305120c09040c170408090a0503060f07030c05070308010b0a09050301 78
    0x40540c05c440a04240584e061052010300d800164040159140c140c5074641c0c0d8042011803a00c42100a20100719464130000590301d20b168059014401d51010901041c0580010b5400301407409081c1c010502902c0c112800001007004c0c3c0781280000c0e0310b80000b10f80e8000082d001250940000c211601d180007015110030058144c4003043c1010700480d200040c034400c5840d800441641140c1d03004600c13980c61100b103c1f0319090a00d00140564180d012a007040d11800d18000d5061245400c3c0c81449900071400c0c404a601d8403c0b4003510403590130818040340c030204d418041c44004440305201c203600900b05104500e010b0b244c0f05062501505041140d0202512520800e02d00420b42d02e4440c540340c02505081d200360310b041c1c042c8022005005555001c0944010318640c4003040d802000c1d1190343d5228000c0100401b1121281000c502416541e0030a031040c07070020307080c581c80070091801401155a060392517a07800300c03107030301c5c10031a01c0c0140c1108008400700803042000007099a02401405 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 509483767 1250 509482517 509482531
    0x1106070f060b181e04030504080318040501120f061d0a0b0901110a0e1002190f06050c0306010c12020c060f0a09050f01050412020301090f120f1416020102070806 71
    0x80e03003600c00b604020806082c10340310302c4035441e01c1040110342c1c84100f5510700000e640114000141d2a140740c1a13440d40190b81108015100c040340980300070030360350581c9882c032805540400c030302d0f41c0342c1403000d10311040c141000e40460160300724900027926a6004402c0e02d03000c4c140f5880b4068101d034500b800c3c10080b160644090350b401003405003c24081c850101c032504002c0b092031410300500c202920b41e8155800c1c003482404c1c41403059245038028460300124031200e00841c5060076035031400c4000c03c800700f6825240c2c1d41c43c0c140042c05000001d000c50303008401c16140e00c0c15080039a035444840350b010410090460041525100f040e482c1d02c0054004400e051001c00d88540315080c00500300e403981e41c40035200d42d03202c007000042641c1003002c0301c084e0740c100344000308403440d50b0009c0b030301501c0d903004001c2800d10041209001e024903c0d03180500307240b15649465902c11032400444050f40040b6600c00c0000d020004241991943c200d2150410300c180156100182d0f6880399500b4140c04581138 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 509485017 1250 509483767 509483771
    0xe010c020a0b0601030504032106031401061805041a3303060a06060f110c030f010209190302012a02030d201c1b080c100f0b0d1106070f06 61
    0x3410800209840a07079103c0400c2ca4100300034902a00d00030000c0c41038980b4060b81205400102c2e504c103040d50000310281d508181a035400c2c10103100494000c0c02030f481003000319285002c2c84400d40c0303800d002d0761380601d401c288000031041750784100f00380015002d4601d50204d0001000d103085182c0a41c844128114000242d5814a080d00d00741414410020408440340b490420b0600180b40c00080100c4039407010310305501c61210b94402e161401c0404488582c2c10311920300b0b40c8003400415002800074801c191000c60b250340502c0d41c281d8001445010090116403d6060303140c0c4d11560041e4490805031440294034030200c17a07008217051117254105500000c070314914911848001552445269213050000c00000c040d05070b6030004c0741100c0712058104111180708113a649502800703524002e0700850720903034840c14102110703230b640c0c180803903c0c070101c2c00e200c000c1c090a07190348503240d02c544e000303010500400b01355500c4000380f41c0402103003644901c00340301000c0424400f04011004030700c21500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 509486267 1250 509485017 509485033
    0xb030109110d090510060b0a0c080310080114011a03070518060405061204020a120302120a020f060709081b10030c140726030903040e04080d0e010f0c300e010c02 71
    0x81d079051302c02d0b1f50002242c0c3c07007080000c0c15640398840d50000615402041960302d9032a41c50303c2000d40d40440d40200c140e50300708a03408907180c4032420014120785003020134403903612140c04608141e02040300c0300c4011490a000395124040f1030640e520000c6c00040549280c00d48542c00200241c01c40004a00201664000c01045040a01104000c2c00801003c0d0582072210f507002540c4d00030390884140b40000204030f07040f946000304014100c40c0702003c00d5070340502d0701c40002000d81d6507903c1640d0b444d00c5a20b074039480e5501e2504900350045009031513500300310001d1205402420380031501c60304115046e102069a541c010026114061103030902084050340c40803407080000300c01c01e440b55000c10420500c403013010004110307806c49040035184e510994690924000034040e03a40e82d6600c460418012110201066100307400552100800300507107888410103c41c1104610007071402030f006000c1000c0c1030320441000a600010311540802d062560300e199030700391045850100c01680c00f02070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 509487517 1250 509486267 509486293
    0x1e0f030615050c070503010528022505160609030308101e08010608060f010312050910050307020d090515090a080d0f09060e1c21020c0f09010b030109110d0905 70
    0x9010005e040c104c0090100e03050203086008a1500e910103004025050001c81800340f9254059410b520f0303d901c0c0d150210075442c4581281d24144c604102c9150107800708145280e0140320341e02066410300e69800010608682d429910600c010f0459100350140240c0040c40031a24800030550b140b100900614080c604101d00d030039182c041e0001300c2c180e004481005010300d05000c450b07044942010541001c07819403881902c00348a06040b8581010b810800c800e55241c00c00e0056018558503130032100c0c403041c10403040310000d030b01d03015003544180071030303c0d5882088400340500803642c1d0040ca0001130550ba8040c881ca0461880000c501042e5642c00c4080f6032608088141c00401003424041506560340300020800344201418001050303100c444c20041c8a016441c1c1d42d01e803440101068072396407004070003960b54050913080900c10000b03801410301e2030800d001c1e024100c502c103d51850441c1d007414400070242c540212000000c4c1014000c025416081d40900240c5502460240c500c5c0100c00b1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 509488767 1250 509487517 509487523
    0x3190519020303060306060f0d0b1312020309010c150b2206060f02070b070309170c090a090503030a110c0601090b0a05040b28090c020303161e0f030615050c 69
    0x1803610095400034020041c00f07450120304541e100c00215150b00c400840300c1c0002d07085a4001e50058031280085040000140710408d0748a211409081a400f2891464800b241c0c2c030f209000c043d07400252559162400119030b40804511000014000b0840211110204188060440241c28503045100c0040c02d0b05a0600c1000003414892500300242180000040d58902080c400e0010300340c40016103205140c802c0070b40c0e202920500c0421210f42641c200c1c40e0ba0b85482001506115241c0d0f00c021076519407040c41401c000c1a4403502850651b90782020344002041983e01503608034008010300f210700c010911065010304000f180004207031144205000b0019410740040b07000d20701e410705040795a40d41350320120008402d040142841c20248078180c030a80c0080c1c0c002c0892506108241070590f8001c8065407080c0d00c0700c0c0c2b90132001301002c00100c0780c611040c000d000001103000320b40ba40c0d15102d800503d0740030049040101c0d20300c0d138507410610741c071009a031407000082003c111b00800102c28 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 509490017 1250 509488767 509488807
    0x40501050a050108010e1504060801020c0f011505060c19080408010b10090e0a0906020c0d0810050a17030f0711010e040e19110405010303080f0c1206040c02031905 72
    0xc0c1ca40d00784190400002074074a4606026000341c2000712000036105809401040341e5907413024005000d41642c030701880e07010750481c3d04440524004d840003840d030b4890503c111342c10b20003100026201c0c2840c1c00240000c950006042d0b80f1203005514220040f0000d0500381100310b842207115036a224a4181341900312446440020310800d40611410b000c140d2040c901e00954900d10300120541e101c640f8034100070441800700502c01400841d12540d480800b040d0f00111100649491401d540c0c1c0002c056201e807018007455511041c2c0788030a0184603001114020414200d50844e854002058803010781c80c0c00500046a00f090400180031695901015000c01100b061314248001c01045062030344900d01a088070004000d103800c2d12051204e0305070000344031800948200215610b03407c00400000c8211070342052a91158049008a81508116681e00444804000c46525044100006403807400c0010307045103c2403001c8402c0d0005001c0ba41d911503803a03214a59540c41c5c40c61301c0b107c1244a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 509491267 1250 509490017 509490019
    0xf070306060c030e03010b0312040609050a030f0305030603030d1104050414070206041226010e06060f0a03020d061e140a030203070b0c01020417010f2d050c0c030706050604050105 79
    0x20003808101c11a0028841000154541080c1c401d2841510100b401002e03400c04080c1c0c0b501c560341340340410250000051058038032507520030071810348803814000004a6440000d107400621658180444d100f86d001c0c0d81c0015008003642e00e4441460415003e41c2c2c00c0310203528040b01d001508003ca8038091041d00c134443c1004001da00c2c00d00d05401c3c00394807480000d0000d000e0034010203c0307884d481d02ca0324940396401c032103044072241c00701140308030f0030100d009000b80302c1d039007041a0208086240c1340042e5001c10305000805407408101c080210040d401c0443c01094040c0c588201048201a8115410320325400700e035003601e214644000380c1c03e04060750700c105000d412001424005a10042496410b59900d204003559071008084030b180244600c0e40413220001503031041d001101410340083c42c074032480f100305120b0b40024404078504040c09000402e4064011254410381c6c44203904102d0340501000300d640d007440030540e040ba09550040c1c03401c80303401d96144200886031400d84107482c05000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 509492517 1250 509491267 509491271
    0x5120118140c2707050c0109050c1008040203033a020703080a05060303070803040f02100804030e0a0605250605070e040e03030103080901270b030a0507020105090d0e180f0f0703 78
    0x8050800303083c0c0d00c03810f400c0c0420300c81000009001d550041d421604101c0004000704623000e840d0034a5031b120340380351424920416400003e40711541c41118441c0c0121340050195250074030684200e9003000c84900007141d11240c0d07104000e0003c4861660401d5158141c1e0090b0741c541c0d19203002002100010280c00d20750745002d080c05043c0d2400002d44200d02d6200c3c0c589562a1520f041a62070301c3e0314100d009601c11030040d1302c1054079a00100c00c5000324466240c5c40031095902081111041d414061035001400a128100265004c0511041c03049018410b00c041c8000e01c1c0c0712003050740d200b207520300c020030b840c032240017003a0920740710b00411010000051815941140e0f1030308180c3c400c5106040c1003240c04030203101d418601f007e40400c02221040c280251660b1445544c000d0b81084481084541c03070b02c000a0388190041c0183ca2007404042d000d020301804503807041d50b0301c0c4c140c1c030b00403500030b50060441c4401c06d0b04c04030068010400c0e60305043c828507003184000600b500051200003094 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 509493767 1250 509492517 509492539
    0x3060f25020c12010f060801020c06010e04032a0c0303050405010f030e030f0a110f0625080c0f04031707020307050d080304081e03070e0109051905120118140c 70
    0x10703501041c1c8107980181200e05410205907042d015014062407620b00302c0451500600280e000c034150300038484503190809407022aa80e0300210f1081c954101c9001d000304030180d43d08000e0301c2c00c182c01741c04081e48044c1c4c0ea040460240e1140c0d4808806608114003140d0001802e01046da0002e00301c820003941e40c60280034804004041c1501d90080c407506084103100480c100c0b02e05130140310003050114910b42201c01d40c1c000801020f80c0c400381038508006802e0b1008104206c1d100e001500a000300c4603403104c0300d00741c960400807049170740100b0300c00da80408184804000607062015034a032000c1d00c15032070358076005140105801c1c10302d2544841d11901c85080d2450005400c8010341e60700c150403040054580000740d040108501d00c840c520001190008201f2240300d41041c8500d96030f030000e0f62a06185c40e03c480600c070799003070030295030000504940401c1109180113520421030344200d40011850301c0e01c4510500c00c030030504200b02c0f5000481c1d05a01081c0c7c3c030820462540c0d50040790245004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 509495017 1250 509493767 509493841
    0x1b03060e0d09091503080a03050a0605040b0603190f0c02010b100c05070e1b041511061009021303020a03051c032c0f06010f091a060a08090c03060f 65
    0x15002d40e21943e0b1a00f42c4036080080c51000b0b2035071200065405c4100b040e500c07000240300a004100c00c60b04602e9083ca0000045020309141c4104128200050aa245952208201403101a04070203919050360b44841081e4041e1061380102000e4159540000c1100c80900c070811070818000580401008040696540401d2001a010301110483c050000d103d0300c506290461105240c50944c02c41040000c001403205003c0701c1e5082c41070141da030340241070b4441c01c2d0010b8444806442000c1c00c148185c00500c0352a035240d009182c440401c0e1002440140d603076001c0360210a881d031003907419030844802411116a09404c600310942e45240030003c04402401407038100214940c541c0e4104030075200300360485400c0005401598100741210440c0da5108180c10811840c0e01030f500c4e0b60b83c105003c049401d00741908612606030014003480c1030003400c40c41207031950401091103031641b04807846016140c805011135401504204241d070f030700b03151020400c00d82004005c0c08a1040354480070040e90 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 509496267 1250 509495017 509495027
    0x11060606030403080709050d0c0810090c1406040f090e192315010b0a020708010603080301120c17030d240513020c160302010206100303080615071b03060e0d 69
    0x1c01a4503040103101519001c90451b603007003460304010b4000d520103e15009100c020040001117801000860345848a981c0903030042d10180000100b00e01200c400a20800580c80c41d07201e4000d43c094045e6051990b036a48401c8862920340c0000c0b000b40e40e4900880814800344014091180c1e243c172810080491543c484040410940d543c8200500c3c4515a4030031500910031200c3e2000140c02650465031a8100811580c0c8402e01d01030241c0b040317502c00505404180521001c0320b4202065130b080d0381c0f0b004040303240b980d200007040718103108042c0041a60b200a498003c8400c80c03d00080d82c4a045005c00c040485a020f230008070b4824280300b9420070604c1c064a804195101510710801e16007001c0c40f520040d00030031880140c0b90103082c100c65590740501ca500400c41c1d000340e00722031058503070090401c4840c4640c00058002042c001c00075049044c480401410503165008491a24400e80c460412110100c1a02582041005410002d00815015400e10b0b898072a000e001c0543c0a20300c003821b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 509497517 1250 509496267 509496271
    0x6090903091003020c100b0a1e0b2208070e0a1a013b03010c030606050d091e1103060c0c15041b061106010f14010809120c0a031106060603 61
    0x102c90b940d002d0003060b080c0e00c01d4064900240f884000c0f110500d003004142d50107460b04180c264001c11110000140b41848100b0203070140741030041014100742464400700413a03010090300321030200d100d00d0303082030008040d00c9240140a954042c1c1a01410700308020140100a407040c0c02c00c5080000300595080044480c40b000402400c0040310072181d83c0348141402001e020710303440c5004440d43c2c04610251055040032081c0120020810809548010b80c102c40321384c043c641c000381040c4442072007440d40768003240115000d80046001c4030782d0000280b03c0e01c60036010842d1900e64101490595081c10040340d60400c0c66190600e0410200030112542c0d86200001c20340310010002c0422305006900d624000d8030400100c4d00d185054460740068504081200459041d208040001900c40c103802034250554200c07101050401400100451f400003015146c0c2c9090700441040c4000062140004d0443c00c0c103441c090141407081c1c0c14058800c0c02115040852900301800304521507a81c0300c220790b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 509498767 1250 509497517 509497519
    0xe070807030b040e010603170a0c080c010608070b04241b0c080a1406090a0507030201050a050d06061110060e040b04140303040c030b0603030702150a180311090609090309 75
    0xa00954610a00724080e1040307040c50b035041450b14010240d034480c10b4100c07400781c038020324066041d04180500880c03184180842040000c4c0c0000e2014002500a030007011244240800030070307138030303100c010090a100440e03000e110079400c0014208055850070205800d0314103003c01101c0111700010380600300c00d14042d884515400c6001000301041000ca0681c00545070580464085801c2854200011f00618240d40c2c40ca1040400280d0350b038000080e000e0303c19070711901a00c080c61444d40156a80e4206920b41010300c4418013015040310950b10406005080750b50f1214040340a140c090b50500340034504031328039a4100042481800e007228001034205501c0420501940d8071801e01c2d640703100c080c2c0c005140350300002061100348111020480180e0f03004030078680d8151986801c150b075070701c03910000a412456482441611090b00380c054409800503041c107850316000101c0f940f4101c1c199800c111020000c19140d090a070030701c5c0304000e512030000d48000c0c5070707401d00c81d078000d42da40900400c003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 509500017 1250 509498767 509498777
    0x50706030b01030914011d0a0809010507030306150e1306120f0f0b0403050909070807020a122109120903170f070b040b042006091207150207090c0203040e07 69
    0x20740c5036a40710341c0c841c01c001c50300184a480006034103a0003c1c00790802090b400080c5102c001080310b80c503c081058403059070300000d898a000c0d810b10055031281c01ca11002d90034940e46074400203038850403003524038604686580d5003000c803405501b00f00c55460702c1010890402e1800005000310039000b4110128140c2086502c1c41d842502c1c44c200c0c0c820719160700010070b2000403000340300c1015040b40180c203003810101c4582020342d40e9620100c0e030351841160b01c03400691200c1d02c1500410000c8018001491643c98035107a80c15241c61b030000c0443c044410741ea0010341e105030440074042980c0b05154801e15914000800d0391840d102d01614a05501c1e0802c1c20000004103282d4140e04031040b60002a80014408624540350a12200680701200d058403085081d51241800e0000c0102c14410803800030051030400f0302e18414800c44903007000d80408503200304440485c8049045948031701c12507141c4d0007401c9060a201d40e03002580c142c0701b0801c055500501082c05000880d01146611482d18030348 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 509501267 1250 509500017 509500031
    0x30c03071b0f09050601030e0f070b091315060906020d12020c07090507020c010305010e06010c03110316030908061006140d0e0f010c1803051011191e080f0103032303070914040905070603 82
    0x20302140c013030460342c2c0209853b0890001071781d41d42e8419039003220003944034100e00c40d960311001d0303840310781c8000200700040c82c402402a41c8892940a40140444a4100c92110f5150749500084440c1079902c48090f0b03201d08860059581d150181501501c000040021130b400c000c000a0442c010302c000040c141b283c00b00b20402c1410301003040e00d015400c03c00000e0310500203410040c0001881d8040c603405800740a000940f4002c1e09440300080b10303a1695024424181c2c03c80060642c0c0080746604403458075040c80b0f0070060310030810071580440050000403a004181e0019284103100102a40e404510402c1000890070114101145c58059500822901c594203030a051038812043c40130303a0702a00c6000c04800e00c0d40004d1013154207040b0141d0138401111190150b0f111740b011102036505680700c10041c40083c2c8a81201c0c00c4019882004101d242c82c040c0030108583c004443c148005070103000100310b0801c01008050710a10182c504204c8204291503864645001e03010383d8041c1030329210 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 509502517 1250 509501267 509501269
    0x9170703051207050d0f020a021216152a08161403130c0501030e0307060c0e090c0702090112051c020304080f031b030c03071b0f09050601030e0f070b09 67
    0x108950b18641c01c07a207021140d2800d0300f0080d059401849840464500c2c0c40c9060440a40c1c5100720b03103606402e0f800414515010300403d480369401800c1d070090ac0c0c9c600103104c10001d08140040c040000e03006601241c26200076655203809010301840841204503682c0c941d40c160f0300194400d811580424144e001800045001d40d100800801130260901c1c00004104104003628151301c1c8480c86201088150382d524001101a214003081c58116500200100400100f442e40b2141220b00141024174015070908002070840303d08560100c40c281002850000711f141c81c9018034050107600800c010004420303200c007a034880043c80c0e4040c1414910f004e91044500030002d880044c05c802045072084001d8940268507900210b0071b034170b440051804a00e80f103082c0401178559102000000b5030814181c0e40341c652884e001c1e0f40100028010040d40030483d140b101c00544080d00f00301c2070109490926100050440d071303800d40c0040c160340028210032111030700030846034103e44155a21517169403c0394 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 509503767 1250 509502517 509502527
    0x30210140324090a0b10090f1e090e0703050607080c07060f0b040e0705211c11100c020d090e060d150603120210020c0709051302030d05180409170703 66
    0x41803694003095001c104a500350558100c0345c4020b50944100035071406581c6c0668448289024491901802d400c050103c21005010411518804280030f4600c0b96102460000c94041c0c241b81e840c00d070001c000600034400100485500b2a00b1480e02100300d00d080b03801f50340703c1d0040e120014002a1100010740d10000e40d07070841c1c9030450008000300070149440c0d1105a59001314420980503000100340d01290320200a076042c0c003d05040060940d50707140c00039064124140201c004207100c0d14109010345030f0010480702144c030808070400600324100a1000e4a0302d003945032481c0400061500901501c0000c0744803a400c24000c1c6c0700320305550036070324003001d480e948444000c2d0700c94500760002082c00400540c070a45145030b030302600c003905039054800c8160f204510030311007d40d1111500300010700469010641c400400304010400c4002c030781c002814960880741000000740045440e90b900305682503036185c01c01c02101c0801030705016544003000501e41a5050503801004500d14040c54058 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 509505017 1250 509503767 509503831
    0xd0c02010b10080612010b0d020108090f0d18090c090915050d050c0a08061003031d09040308010509010b040f0506030403030216050a1209350111040302101403 70
    0x108411900b0308807150041000004071403ea2080b240148051240801803040d11000040600005640121500191480200502800360502c0350402041d062007090142210b80022592030a0030500801500e1004500e1a004406490302c0e00303440b6411503170000d42d00c20440c2e050329000f0a54000361f80000410300066409140c0080d51400c103030742040008541116602c4c0c1c211618507060391a00c16407542d0b0b0300308480e814032030002c5a40500104e806050021610302085494007000b80400300403e036901d030240c90071030210700d900006101d589450304c0654054015060801d06062804081e080b049009d0b20455000d544000041000c0c188603170100e4540c0d404800044141030400c1c6803040d5101600c90058510f4404c4144408102e13200d10f50040c2120ba50408a0303441301400d0203644c0f00c4c55140014807108034000d4500c074aa0500c01c0c0244030b403500400002a48a91a50041c4181e550001000900b044805119000c034680c100007500d412405140140003d1400c120405420343d200c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 509506267 1250 509505017 509505019
    0x30306130f060605040f09050601080c1315120b030303060d032001090c090f0204030c090e28291b1e04170f120d1d0a02030d050c030d0c02010b 63
    0x344a00890f0f620341201c010000c81c0c11600c20103c119030350f01c240c81c044400a0702d10500092a000114003034600c05006002d8281c0c510050f007908036034448003e005441e0000c8180d0205820010f0034010490700d214405c5250300c103070081c0d40345103000d00c005440c0d1001c940c40241486080e00304060b60000809102c20302400000c020012002e142c1050035542220344984070b0f101382440919000d000c241e00031366003283c2d448140d0b11100c50030812000c02500c41341500f14a244600020b450070410451012628218007105541101d4080c0c00d202c0001c4040c0e1180b6030451109801039080604890082913002042d0808610003c0000074040340900c5680c002012203e90051101c80c0080014010000c4034094a08031130091036000c0d815032075603949100d009044d00a940901d50707613113010005061500100e040002d0707015011980d2000e11400d0600c80c03036507500ca038460404504080040b650030030100c1c00c00c00d081001f6020a983e0f24407848122007803403904d501049d00118002d4005012000c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 509507517 1250 509506267 509506271
    0x90b0604061a30041e030e1c150b0f010e13050c0f0301060816020f0c0906130501030c05031612030c020d0b0703050702070f0f17160303021507080108030306130f 71
    0x401c24074801e4007618152015240c460b5036001c14101c0140c101120350020340c0c95100c3d40b42031f02c3d0305010010720b9032044101462803000c3c549150001a00d01003506281b81807544000743d00c02422040c016030031405060300e414440e60b040e40c0c40c0f10740e40303511007061130012000001c074042d502c44002c2c51050040200321000407030080004688280c00940c598861b070b00040200c41c2c6e1400b5100200d0b600d003220b0403609480d4010450020b50760500c0c1c0340096010002800101f800000c0e03440741001c0301c8c0c09a00c01d40f200e194402c0b05000c2ca150a10054104130781c14840090111308011003026445610740c0010148042200301000b1500d80078000c5a02a410040b00c030801d1500c0c40d000303405803108845041c018001d940d0302040c1e0000d40a001406c0d038880d80c10400c100d604012415400c96000e09e0748549610401e403440309a5011a80850099407007036010f0030502240b10b80180d40d44c2c4014204106009184e4014440360100000740ca07070000302120302541070441036002900400c01409185c2c1d01c14 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 509508767 1250 509507517 509507587
    0x9010b0a0311070309050306100b1e0c0a0f0519120804020d06061d0601091d04050102120c070b01050603040f0f1506141f0c0f050c1003090b0604061a 66
    0x16002600c210481b0415001d4520542c4d0341c041034858000203001c3c86031852014082e170a9580c40440d0300c094441100c101c90307441e00130704e0f04031140b070b104500c80c2c200c5600780c40c0c1003403c0030800f05000e4000c40480c040290200f890141c0e4075880d1650280040034108191400014203540e00c4138201c2d051260002c0c000c0001a03141d95248006452009003c2010454500480c40342d500c682e51450480700c4041e000c1d441804645090403a2400180c4207407040c0d90207005480103120303d0405036004400107042c40f940c1e0215441c0c0400044016480740d44908800d004001c08a4580581501c03000d0344841031989000c0c261800800444c10b07004000f25103071400d80041611000c0405900503c5000c035803071400401403510a2115800000254001550403d1003500056240c018942501e108030241c504124101e408a0164200b803241007000949070310502d4103000d0104412038100c00c003030b81c007445207034100b04200c0392580081d1000b8241d2400010014040003203080c1c1c84a00038021324520b2046 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 509510017 1250 509508767 509508773
    0xc050a06140a0b1009150c050d032a0e04020d0e070b031e060f0d030c150207020a080303040302061902040503060a091b06080f071b150608070509010b0a031107 70
    0x140c0c034200ca01e1030320030f4a810f01c55581444e00b450b801c072400500f0350700c0010103801d100f130f12803020742c03810645810710841750800000940c080c0006079400032990b50001d10034155415001144911602100641441040b000c0340d050b44215000d0b01989c0a840244c1d039550211884002400741c86c541c69218040c101005c42c1d0300c2c08190066026480007000340017440f4502c4000c040e428015a280d80d03200b104096a02c502c0d0402103400800b5034000e05101c2c1e13a00400c1c0d101e490104889404c10420300f680060540c0441c901200c0340c2e40a0b100c0c0c64011401c5151607070b006580c4807405055284d188002c1c401000303042d1900c0d0112009030074054103844180c20400d9100001d000c07541011240c4030380c51001c0da070b05d101200070b920003100c006555000444e211040c2e40881c40e47c014000104000364181c2200510803622100c04103184a071a240c281c9840c09444801101c076160071120003600494810055650b80d19501c5042d1842e09108550307e0180e0b80c400d4006144e8035410301ca541740045407000038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 509511267 1250 509510017 509510051
    0x10e040c061404031e0203010b060c0615180108280302060601030504080d022b2903100911091f06030b04021306181d180109080408011d0705100c050a06 67
    0xc80d06c258001d0089508140c01c1020f1809603120030882076100e440001c550300d10000c14100c81a602501c0c03880c0c0521075440c2100c1c0322100b60400342440d40140221011504100e511030b0400031203982d080c001c4181c0d9580251500005060303541055140e00208050000b40c60480380c0c41d10010004550b103200c6211120b603610694114500070002c9800b4114211010340100d1002c282009120045050082c040703140d20442d400c0402d401d44604003c00c04a602c49124541495009481c5859841103142c100104944002e1210101c03a0003001c10380811098509d1020540c0c280e8280460076a2201011070001c3c050f001c90444d42060780c940c0090f106400c0840e940e591180704420741c0b035150715030440b06d4121550721500c00d104444100040c02c41081c0310b0024a01c140a0000415441211b885800b03890300305400980300d40e50f6030345185c5190035160380441040b05203800503118440c0740074001501000000014800e1054100c40c6408009061120340150b55212504012000e040811311b05 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 509512517 1250 509511267 509511323
    0x2010504060e220f0e1612060b03030711040c032d11040e010303200a0f02040207230d0e1f021203040807120c0f1205090603040b040b010e040c06140403 67
    0x4d2860050148040403000c91350884144944100040741e40c80c000841c50a03032a40c920541e40142d989c00d040203a542d00784000d241003400ba080a070100f045c5142048111a083c07040481030601d0a07400104403443c0d401244040302c0c40441c8035205280d142240720160000c81c40c0d0300d405000c001000300d0400c40311882681030342c3c065039860310301500c5020343c1c03444841c481c81044c10382c0e8088400c040014402c07268403101244081e00241c2420140c1d514003010080070410005450101001600440010040500000c5451401c90700300201c610104403418294040e4102800790f01c19403400310b038000c000340c4501c01c001880a69882c0360501389026903800501c0101e525a00c070040440c54188070f00c2d1600e03991034200c0c000880141569a03220b48080c074034800c01c001d004007401146410341d00c804c0607610030b5014410a4125252610300080c00000507080002d02c3d840da00240000318840d060b2030360689030315045c0962501f03a14800032045000c1e540c00100100c959100400135000307101c140784 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 509513767 1250 509512517 509512541
    0x71107080f070f140f01030605040219030e0c010e0603041a130303200316032705010501240e030a141b0604062c060408030301030b011202010504060e22 67
    0x44103142c9401a034424030f10b061081c400020070011216150f86441031000041c450141000600c150382c0c4c60100e0166007100800c0c41007000c4420021083d5030301401046e0103007121b00040e002c0711071194000b0f01481d001004c62070080502100082c204035145480f010701e800b0180c0c03840c009241c20551501c03820700040d0120700280c1050280e41c0121044440c0b101c280f11000e500a0842d0b444001e04540384804021440400d03480c0c0780003807550307078982529800020006039004455032080c1086803d407081a4450450902990203a01070f13907068083d0b0400703104041c0303490001c004800001925003800c10b00017074008484a05065900e140000c1c4261180d25a000d203081101071003010442140164840c0c0408075180880c0b9295404a032500d1105080b50210307040c15007150000070030501e030041e41000d070b0168800401031007402944854240140b0303841c00c05000d910f1450740001d150303014a00c50b510612000701c50078102c41d920580e01d004c06005020200c048020700d0030200c0b01400400e2910 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 509515017 1250 509513767 509513773
    0xc070f080a030b0f0d03120609021b0c03030c0307020621131506030203030a1202130815090304050109050f060d0e0607092103110304091410050126071107080f 70
    0x3d100c07030401c5800d051000340c00410800c038807802070f24140c1d003201440c0c2d1880440c3e541d0f807001145049041c0b0242501950f2814200c40848401416510380714a0821940c0b0a510900011401c100000103d88842ea0b050720795640319422010380c1c100f2074041c09464940d4000c0001000310120008100c068140d00a1501c7d80014441003c1c83c2c040324098040650150000c008060300705000e0511460718542d081001450000c04420703100c0b0015460300100c00130340000b5600308982025401058008451101441c45c3c90f2801c00080e01c500070304d12030741d40150a030080c121440d546030801c0d07030748286106109000c00301003a03503000d45a07181100d19001148820030042103000803506800c041d800b52640c01c201017003594030140c64401008500c41810702c070800000c2040c1e40c5c240a040c0030441c0b1200c0c07510322424091114514100c1a40015041087c84a1081e6a2442c0300760310070110501810b40c0320150b25400d600b00c03405800c03c15400b40b45d1240ca00d0018601200003042c222002c40c00c026 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 509516267 1250 509515017 509515031
    0xc020a03140304020a061d0d081921110c01150302030d030c1b06110a091404020c0a030e06091e030106120c03030e031603050d0206070e030706080c070f080a03 70
    0x1c000c20a02040c2c801a4001c602940140003c6000da0343c50464829003003d0018010128400103181424500040310b2440000c02d5061003484440030325101705081e410450640e000742e8488424844072400c143d41d4958803555144c03825500c40d401ca45d44030b15804000e2200c1014010b5072034040d4a9131004a0003841104441d003e00c43c42482404200e400d0b55448104503801034501c0203a512907090140d40741a0741c1c90003800441c12200040020041507151041d01900d000c0210096020b4580c8079030140e40100190888070300049010480d20b03a1600702425000b0307280700414528002e41c404540c1102007441030010702c070800d07000c110740c42c03400b00c1c0207000c41034850103508540340510100a0031001062070900001e800b40d030402c1d0280f000903085501c800d4004d0030650403ca2036502c141c4030381e045010078682c03880c0d0600200c1d41c05072460411038001c0c0428800309030796020301c1c4100b008010304140465406501402111030843c1c0000019540b030406003000c240c136074000c060b48004245400a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 509517517 1250 509516267 509516297
    0x80d200711090601090501121103041212051302060304063c0606090509070507150b01020d0c170f0906070b1006080f07030b0f09091608122a010c020a03 67
    0xb6a00c61001030790b40802c540e16140055a4090104840d115440e07181c041c41d003241c0103a40c0c00366210f00c0c000c4c81c203a0000009400c3c06000b030ba40d401c1e50085500d080200f0441c0500c56503030540c7c6003a038195090341c3e5036503070ba0400740006d14144444c1d0a0f064480031415110440d404d1811200c0d1940c00b10f40010081001044012075005208403070106d62036840c10086441c059903220751001035410000e14001d500da641d00d022080800e54612a00d60b60000460b040d40e0400130351901c0b49990611031032100003174540ea0721858004040c004081c1c03000804840d4190103000751412410302070680360300c0d00418038040341c01d90011110003007008150000000d81c41d1054916a0141d0071a000b48011500c1d0000e04402a115803540150000c059024496158441419252290b6a0726028060340103120b82041000c05550b40702d84c003690b00c21201c00070a8240f1804503202030051706408441c40c41c090303005100d0340c540c1c040c07400c1c4194a060000b180706078010a102419a200e0f641c2c0c0000100022 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 509518767 1250 509517517 509517529
    0x30f060a060f15110a050a0f0c1203080f06031e030a030510061202090604032909010902031b0316060e010207050627011101091a0f0105030604080d200711 68
    0x44110035620803500c3d44074429034007800000c1100e6040500f07484e00b0059a4480a00e81101c4400440e20f446c0d90303103082024841d4910944000d05210000c61a2410031920b008190318400b0782050004001e8001040169908010403805551040180240342401d0f44402c3c0c1c40b500326080715000310b400e25000448858843e4840c0f4155071403038135a849075002440c08980290071500c0210340000c3c08000c08404909542e40410b903c0d0a811401e102e00724031003440e64070f015000307081900d081e03042ca0801401a940481d203851048552250b00502140f0040000d1500c0000810813002080164006c16907503400351b400100d8a07000c0c0c0848000c40c2d507a0051202c903104112100900540c8400c2107001c030340c001c0c400e0002007503051410541d030410b00c0c070300b01d403c4442c40300f0100d42190003001070840460601d01c03481d502075022000340f0b80961410000c01d4171404002c00c000d00805000a50500306902070344082d007119031030002c6410b040800401401c860340207880654a045600101210b240b5100d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 509520017 1250 509518767 509518769
    0x19080a081b010e060406020a050f04090f061a2d0c1b030a0c0b0901020c130204050a1a0f1e030a09030e0301051b13031e0b090a02010507021e030f060a060f 68
    0xc80c000d004c03c0d81d40e0388584000b17401030a0460700704002000350310944403202c8c2c00f0700003800700c48500040c0301a007480c50004841c0350780e10031810301030714410080c030103040710068503800644919156041c880155034200c88400c1d00441480501010800c45c1e401c201c0042c83e00550114100d4940b4414801001c00d41e649500c09402400c164121a042c4858403d041c080d0004aa0600449881c040310500084113404280c400c031403050350125041019240500e049001000f052522a000d882c400c9a903003850f01c11500e0600303a06100080044441051524080f8005c5451459540f00d0500340f80c41c80181c1600d02098001442c0210380b00070525040c4100c1c0c1c0141d000360458004e100c41e4100b103030601e40284002801020f522031000011400a00301540709076450f10035510f2001e02451f0102e001d8001500d07105a640c0403044030340060740c22000300c580090f0115001d180020245459080840b43c01003082d405006490b0070341c40c048000102c0500440d05001d0500400d511004006c00720055 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 509521267 1250 509520017 509520041
    0x91b080d050a1b05011e0902060f0304020a091a010f0503150f01020a02091f1e0b030a06090e0c040b1912081201080307060b120a0219080a081b01 64
    0xc0030912004441c0144001d2120020701d05200d40d42c0c1c0d94100d280f10416a50704000da840d65114500d003c112a00b80d0200c0722211011041080f9508054000c80c1890188807080d11060b58000041015547c0300c141450080210765000c1c0500c09a040043e500c801503001024003265491100310324003030003581541e10441d0440506440c40410b4010003c00b41000e90007281035008151071038000d83c0360754065900c0b45000c00c60010750b01036003010340241004030340c0c40154400303040b001c02e010018926103d2000c030340c4140040354481e111040c0900c007e2042e035102d80c01ea640b800814403a100e2001c038401141107c11a0200000086034003440710301440380029014611a25205000f0700401c08464503145000360b2101e814403203504019001d1003c00e0b04000003079800824460100406402048030b140c001b55070344480907040c0300ba106d070b0700d009843c030091080c9288281100d080c10303040072200c0140f10240440b594000582885410ba40c00383c81d00e423200d02d8002c0c4040c0c1420300c05005210000750 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 509522517 1250 509521267 509521273
    0x10b07080d0510120f020319030215060f21060609060a06050d0902040603031707020721030e0a060c03170903040b0708090405041202010e160501050918010603091b08 73
    0x1140d401d4071002018020306a40a100c41010301180c800c952102c240c500c0b83c810120080c07402418010075140401400e420b0340c02a0705004800b00087d4041014060032711b0b03548012071203840b202d000842052003000181c1d000a60a18408892280d442c006400c1c41758200a8800c40e13106c3c001880040e01d401c03216150130007105801000003a21500050607901000f40001a40c0c040039030002d4250340341c9500907030008600818070040d408802c0d0780641c0011140c00188038081c5001d08058450f15141250440403003044d600500b03140c000c2d2050055030000070100a5010749922001d4002c00c5016020360006602c004200482d483c408031081c06050344100031400d052070300d070440c1400e40c012182215015000d1107081140d413113038010140268420140f04403a4118003800030700f12041c50040b440e00d80d011309101b0a8002c2c041c2108401e42d40c0c00c0ca88181e44448442c0030645284446503160b12900380c90000180456040e8410540b0511409240034000c3e419542038a985a00e8080e000d0250 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 509523767 1250 509522517 509522527
    0xf10150f020109020607050703030f02031617130801020301180e0a06050606040e090601090c051201030b070201020c030c0703051203070f051b0f010516031103060603090f030f0c06010b0708 83
    0x16010380030980c04185244000315009402d9030101d003480c0c1015004480f00d0b03004140a104050b00700d5508640441284021414400b96021201c080499403101901c819481d50040e00034150420490382028032206090154641c1c0d001114001d41c000d11403d81d156900c002c4840e0384016900a001c200c0503008020940d0301043c0d01c0d0b0390300420340036000070b41c09042088002441442d51419900c18031aa2019155941c034103405481900d01c0b4030542c0003000000c22144144a00041d4098152070300000110b0566440840681c02840f440ba032015041c80041f5401030142c01c00981c010550744960256a00b0941c8000341d00c525000640321000820040011058003d100706c000c2d0000355000b0303021118004500d0102030522403600c000401c2030f5100c6080114084001d5409280302d03d061600704180c4046103540c44240c04040d054511860002000c10403c0780100305460303494201e20f090700d0b07480801c08020203150303020038241c0740c1c580205800058036641d010241c40c50107400c5a1058030308 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 509525017 1250 509523767 509523809
    0x209041506080c070819032003150d0f12031d1606030203100e04080913154407330503040f1a0c091914011b05150f10 52
    0x8a11094440c01c01c07d66901c8a0320b0668034142d0f490301540c18611519652400c145c50b9211152214608042c024107500c0140c1c400075034947c014840079900030159904809450000b10050248200112030b503545009d12940c001c2008144202034681e844503030403680356244010340503400100d070707013003025120380608018400c0c250700c07440c0d40541301c0c1d40302910300080d603000661560301540d0a820000e645108001d20b103a640c1c4103c80180038401d140101604601c5031880350040b0250300001c04034203130b80c0b0008a41c80f106103030700c0e82079802c0c00556142c0e40e1981c00b0181d00e4034041c411148135070b0070300e10a040190101454020100c406580d40352a5a4590300c40c9507800c841e040c022580001619064009544003651042c010511040840c1c3d0702c0e505e4100b044082540f03084c0c441c3c03401d01608010801d440c0522000b6240c0b06082c2130000d6510a08981c4604940000c41c0140c40ca001b1880706152a0380e032202c0f0a841b500003103c1220142d154a01142d440311000d001c0c2e00c2d00d101c0708410b08000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 509526267 1250 509525017 509525047
    0xa2a0801080c1c030203210105090a0e0c04020708090a0603020901180806040305090d12270e04030c300801080d090915090906140c12040f02040209041506080c0708 72
    0x2030f0358002d00440b4900004d8070350040c40d040072144018908680900103120901c0e14542450304580610303004e000d0b031910110126100d0b0740002086214a80c00140b004c01c00a03000c042d1000d042000f41110001d07035075801c2c058060350110840c2d5001440c1c403000144983c2c100802c50301526050802010156903646e01030311503600008180350b02244400708080060001c05442c5031800c0247c3e101180c0c80c0d8442c0540c41096403d0b13940790b0501c405140244030741c149140280798400c2c0c141c5090b514036041c5041046c0c2e842c180482100b0344400742080c091480380c100e04c1e8405d00c185036a440440c581c0c0d0396203156403602c0031904180001015864100318802003501701082c541e02000130008020399031030303110341151440403040740c08c680c4a000f0384035408031324081c20340d000070145241850b049404a151500e800000c00042408010192074800e549860741541c01d400c1f0041c2c4204015282e56881100010184c440c010000b1690b1000503241212007040d50b03503580d0b00109060502c128030350000301c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 509527517 1250 509526267 509526319
    0x6140d05030306011b1e0c0504020f0d0c0e03030c010b090604050c070f111206090d0905010909110d0504080306030f0705031e0a0203061008010605091308030a2a0801080c 75
    0x1a000c0303c4170383d1070041090389080e030441d0882c0700c01c030312042e075000d107008942c000c01c50384100c1c0300b0351051000b160040d06c074000301c0f406e444c0f40500009000c52502d03010f9a00610b981c082680510005ca90400f8154055010000c440d80482d8003060700c5d51000100030945008464500c18200103000900002d8155207e002c000761080c40301c003405034000c002148050140c00c01091050b0b104405100700148140100d001e03092062400d0200c0600341800600030b000c00384610f1101c3c81d0f50b00600c504403181c400a503980e19880035010301160809040440c0c0b650000c0d030f0524402c0c000c0344403110780c2541c0010f046049803400303409841c962030a40c900b0546000040c401000902643c03600d000140e80a204281c8203a4807040d0340c0103594100101c0d41e084840c680c100a01400c401c0c0b05200008d2051203c90400360f07400010640c2d65611302520304054038104107031098000d031150780c444c2c221b24240d202e201190740c0b03655658002d0b070303035180c840c1c0c0e544c01000d800c0350b0001407162200083c101c1c02c5580d02c0e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 509528767 1250 509527517 509527547
    0xf051005090c0a05062a0a110607030206010e1008011b021c09050f040e01020d02030f07090810090501180c08010e06010320030f03030705180f1f030b04090606140d0503030601 77
    0x20a0301d0801d001220f110300c050720b4a1b0041c2d0004086c640402c9190403100788658000d840c0349041034559a07019549400602070080e05600384000100348801000000010300800002480424000680d891030310414030000005400b40760080c8072109071001c2480e621810f5a554142c0b054948814480400342000005810540321504110301c41c10034001000d030304048000044c1e6a103058500e14803501c07405000c0104000c640c01080103409800600034801d90b503412400546c001542c9000e0b03006203819181000f40348604203580003072000c1102c20381e04599504000b4460b010b800e025a94542100740802070854640b1500714940f01850021050700d0640641103402280704250000c1c5150821604e01d0b000500004060442200082c2050715401c8152220102542000c0c0014211034044500380948283e0100081c152407181d004502e600b10058403c00804800e424540f001d001203010720b00c0380400c240845a9581805001c0421032504000030b50704585a110045944801c1d0141d05 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 509530017 1250 509528767 509528797
    0x90a020c0d050310081b010318080d0b0d02031507110d1d0a0b0301180b0108040210030911060c0f010e03090a14060403060f1a0102031c05090a0f051005090c0a0506 72
    0x4596040108106c0384121211a40715115001c3c0e1800107055940301c2c110005a44401480080082c800505440303220500b680c0109034801c0c42d00215541640c0c0e0320380079601d44110811102c0101c5010100e5000d00407990328003c0b40c0b800c41c04003958802210005800080a240103141e0040903e611071000c12401001d040381c0701d54440e00d00246030820b80040c001c2000600481a9601442c8564000300200b802c00890516003074000038030006000c18104103041d00c50b44001c0400c66801c00d41032000e1001400182c0f103820600040380d9512454602080e00d62900a03000401200082500d030182402049241046e0034112160440d011001c2c0c400e822110510010001030414099410006020b0b500020082d41d00c03d05420003031840c200480c1503420400ca541c008500e182d12803108281800404501500c034480003500c1c06140810103001f1000d40301c081703410000080b42e0648000d4807503000784502c0e1103400c40903481d8500c81c0083c55200e400003e00700281d092100103000707100c6c3c8406034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 509531267 1250 509530017 509530019
    0x5090f0a06170619180b0301050403051204050109020306180c0a14010c03030e0712060f050705042303010212160906080f06270105031e032b060f05090a020c0d050310 73
    0x290309044d40c650088940b02c0208454a5000030391881240304c0c0302e100b00c0003070100d800c2545001d8040d00c1891088011690400001410f03c442504041d0089501908075581131a00409007641d04001c04003901c0540a108515401481c0051780c44064803c043c0000c40413120b02401503c0079042030104a0515468450fa0f42c0c034400c0c144281c2e40200307a94205204c0c650824580101182d0402c080c04002602d40350901440591141c00d03034080c0c5080c01c0038108100508464070072a004004401e0f6410360000a1070303d0392140f04100940940032380459400c4515245034295451100e034020040001c40000c0040c0e4110039280320f01e90094005007040194445004940b4080c00d030904101e51440c8140c00100903609040001600001c08940c01040c1100001c2c001a26807042980150300140a03501a600d22030f0b00409a4144000d1003800b0031485540f00060781c5519010710495204120220018a0010183c022030b004048a9000303448441d508201c01d5890380c2003d42a0102d500300d00c2c4e0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 509532374 1107 509531267 509531299
    0x311010212011809080f07140a051f09120309140109020f04020a02031c0b040b0d1505150409060b04060b040f0b030403031b05090f0a061706 62
    0x407850f445010014042c805403003510805071079244005400d0480644910081c4000303441684900740301c400441d0010749076869000c2c094104c0d00289050010504c01410021005d0032007540020041c103142c803224002e0041d00c0000c404269201c00c000c06000a002098860541100080c402e200481c0d01149480901080d880d000e9a004a181c0c0001030081c81a54152020103410582c212003010200c800340c1902103989010349d150400d000d4041c00e20724001c007052500b04d4410101840141d00030703401030100600c4162441d064201d02140e0380c0d5513001d041426030103144003044c41e580701c030300b0070007154080d80c403075074100c07000304400c001915407202c040c01218200d240c401d450b5a1641400d901820304299418000309800d0f55401003180c0200103020200415142e82072183c95010501c01502c900380601004506030205540d02d20040016407030740618042c1c241001610f40314 = true := by decide +kernel

theorem cover : BRFrame.Cov 509352517 509532374 := by
  have h0 := BRFrame.cov_init 509352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 509352517 ≤ n) (h2 : n < 509532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
