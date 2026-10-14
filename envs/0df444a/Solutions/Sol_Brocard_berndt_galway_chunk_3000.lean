-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3000
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:22:02.099472+00:00
-- url     : https://prove2.me/submissions/46d5d5f3-edbb-42e6-bc4f-7f96a8f82e59

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 539388489 ≤ n < 539568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 539389739 1250 539388489 539388539
    0xf0e030309010c020604030b16090801140a1109131b0c050c01140403171e03060d080906040518041101020a05210904050a0b091605031602031b0105011509 68
    0x30a00942d0345d0031007540c6c01150312400324070091500f4428005011ba402400034041550700700086404c3c0418002c510722074440011844199680340302d01c4002c2c20350a618880c0d10041088841000d07140d10481c0c017050740721410045030014498180f92080d40004803458100618003103050000780e00480c1d0a29052000d05c0c1c0b1081034140e04000c0e441902c603580c4010000015109603500409040707000d41400504c075600441311124105c80410b8038031040b54016406544079041d68001481031018040200c0c0213002c0d241855201c070b000c40c14403c020085151248040e0b010002080031080980c60458028809080a0401e80e51007654440030000b500b00500d203500888014107a2200980d180b401005109008034181500484000d0488000160049000380d0000e05844d014141800c0410319650340c5500d1039641284000b013099440b1030300001c6000801201e9000700800299044882014000196651528403000902001070510340c0602c16191010081107030311100c031107020541e13100c3c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 539390989 1250 539389739 539389757
    0x803040318031a01090c05030a0f0f0603150e01020c03030c0d1803051e031512150c0d0506100f03090203070e011508010503010204151101020706090b06010f0e03030901 74
    0x1905903071511184409030628522003800009001c42d000102c0802c2c200100c001c061640c030f0301280e4040d1900500f01c0400702e0301c00c01c04200c04004030381c4001d010b9604a100000c0f0340710300303014110039103000da4000e07078641c40103894541e0b0034035961068200d0712014070001c61410703c0c4d00e60025142e0000400f0040d031680045411040226075801031500b41c403488001e003441c0c40c468940503103190401c02c902c0d80c190381107284405e010803d00c02102d005100b000c6282e000031149404000f41c0d030744e106803110300500640d859841c9501007200751074050300141896070344480c0440b800c030040b0b90f001460280719800d0a804041242d800c9825418900aa8540402e41c4182400824030b08400781d440403131000c09030800021601007c54000c503500009544e0540b050360b0317035800c150903070090b401009598802c0d10802c9041d14080d401c2c0071031100350000050305107007081d2282d00843c0c614540690350140070001b0401250f80c4008200d0322011241081041c40c9120000b0036a280030b901d80d078505203c5102 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 539392239 1250 539390989 539390993
    0xe0f010b01660309151101060f0302132c0a120216090e0705010819050411100f0c06050a0929330406050301150509011202060304080304 60
    0x110000190300c1d40c2148490201420044140580c5a01085000b81d80384100e0a40152403048020a0300e40c0640c0c50070070140c1030076901c0d26200140c07801d0a0902c00303207415000e01c1107000e0044c04010001c800008883c04d1550040c081a115121b820340780040c40d0a0340c158402952400c28807442d002e443d0b21030880c8405102140c43d00054410240c1507070041c101c0c10383c0d01980003035034904612030b0741c90380c40c5166a5840c086003035034014846020150042c40c014081940b00e82002a4400e03482c5c030907064410303507181107a0100c0340180c2c1c003034900710038440030003000d41032000301406000d0480c0f401803980540c0c40f2005008504240c002001c554498000c2054100c164001c484801d8010013070072404101400c0003903803030806004d00180b2038800b00000c0c21a49000326151040c8034a44d003100c1080c07010381244203482c2000107a4030b41c0300359545408642030700d09100b010702000b280841030580504000400c04440c0059014003007404894000d080180c1398001038030f4009a004407000d850f80c07118 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 539393489 1250 539392239 539392307
    0xf090f15050c01140a2003011a19090e10150c050f030a030b0405060108071706010207030c0e0411030304080307020f0604271404020109030b1503030a030e0f010b01 72
    0x1880b0b500c5502c1d8204941014100070500b1054020351785003d013080041c03500d80080710b080c00021001c4e12110300a000422041100f420b0007850310703002288007407900340c80717a41308032402034104050030000307004a070300380b1001c007000780020707048200c0701c803958500d501d01007192901d00c0c981c0c2452010041d203070262008020041054040c4094201d0580ea2076644040c00200104640380d9164415802c0c80081521540a1f8600340d02813021030ba40c520121200340040461a50041c14050451151960000c082103078903403450003800c0088069085130400b801d0a5178254020b902880c030940080004010b54540041144d2304290306907015150b280110000610078020303071340a00c0b41480c4194440c1b0189210002000d41d1001a900400210400034082042c900c01224000d000c01c04109090000c81c460700c90461b8403403000c462402d0460028408281950881c4421102082e100c0084040701c030f0051191009102111008105070310f14038000a0441e258000071010101da840311180b044405 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 539394739 1250 539393489 539393497
    0xa1a19090501060e0a15090509040f0204060306020a021027031b050a03021b1c0501022106011b08030705092106100e041106090409060501080703030f090f1505 70
    0xc50001040301d9a520140600340040464810303200f0300c00c0040105001c410b0010512402509a032074095480c102014440000c001030000d4441e201c10b8440000160740d68051b00c006148113100142c0c0700d22007402d01034902101c40200c00940341c20103401c1c80e0040501b0448101e85c206c0030507003421003445800d0550700102d85000810222000410303260521100042082141d44241e007110f052030112494a06920a12890654403080150f07817501c6003400c201201d86414090000145081542c2c0c110314090905100c030040b0300001481080155a0000b0740c5030030f13103008682204403c510b580d6030442e103440024008400c0c42404921840141c88112024480040303100d48a001449686071895643c6001c54114204192030440440c0701c3d100d05c0a01c50103a030b4481e07803803000c02202004208150708090b0340700b90801c0c3d17111041e4000c07407a907020307003802448404054403c007411400c1c014140ba0be500101000c0c401c2000c07040100071001d491120450310b4031440394641c0488a0011142481 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 539395989 1250 539394739 539394749
    0x102060712092102070b04230a0503010207060608070b281b0804180b010e040506030129040b06070c030605060102030715020a0905040b030a0318030206040f0e0a1a19 73
    0x80000d0002c0f0000205003000451142da021540c03a9039446c40705030500d125a010b10544410703e5400700ca0b400c99a0100d54006860040030320f080652114017090880c0c20059056684545402080140617402d00003030002c2c140ba070071030614040b51140121100e4030894800c501c50b0b011490752103131140c402d003c45202d514103001325001d0348080c3e04150b40d041d00300703000701c020703030401d040c50b403010048a0711600b0850181a1607490320001040b0400c801400028400c0f900741d525010003800142420310b41500c801d002c81500304032074140009000403038040b030321031a0144604204c5140070900103604002100e90200f00460b0a54903040100c0c158003403100f00402170018140b140d040f003c01038000d80301c52030103541c440e010560f45400300429106205002901500072001c3c100110b80300e601c01ca8480b40c0704070b4000c95015a039a01041043d4080d80c05000188000c080a1100d500c4160303a46800c22120038003400401183c0340b11103441850981124424040c1c1d50100000503082126800202 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 539397239 1250 539395989 539396003
    0x50f070203240a0b0a0e0711030f180d0f0b1b13060e01080c1804020c0304031a0a05060f0f12060f090c040e1005041b03050d03050105060702010206071209 68
    0x1001c9641101c10003040b030b050103811090300100060380c84140f4410344041850042c048080b4901d00070185142d1480038014908010304e12000e82c0712604200f00030034400e40d2000d1000d581d4900100c20301110300003e01000d2084a000c03601802062a101c004030038144c2014001c8181e40728a15010744031020b102c0200c041142c0494885040c03182402e121040b03407000e49a2100c2032011b00f0044070a4841140e024200038002d02c10049001161050f144940c400500018605488420140e2035604190320894181c1113102c060726034107180e04100d42d00f045045000b880b480c205000003c4105c0490820940140c6207098106600d03a240604000c0d149413940682c0d4090900c1c4482141070300d021558034800c0d225280c404400c0d401e1600c075424605032002d010701540c006001041c009008050802d44111038100d05000b081401d5441510043d0301c07910007041c86215044018058802c164017035442100300384200c10241c1d07008600e00303902c100c040c6000c80d02d00072a10310304001452402406080a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 539398489 1250 539397239 539397253
    0x1b06240a080d12061202010c0b060d05100203100605040303050a0f0c240e15010312090f0602032203082a0a05071d0105030a030e030109080313030306090209060703050f070203 77
    0x2c03504280200f0350480401c3c0c0c24440540c80785002c2d01802d2031000002c1c00240e00f80e00c4130010810100f01030740c202d04000c024a00443e02601c0c1d41c2e00d400c01c0e0030000c060a503400018401b0800181a5420003043d050400d179040c1841e5460180044c002c0c1c8425400f0711240700c4c402e114141c1302e8410881203552040141602920300a0380ca209607041c0070032204201e00d4581c3c02d010007040020440310b0348104401c2a03569070b09660311111200f400c0846082408503400380410092001058070f005000d20798015500e0301c88882908848032082c1062034162084000d0074008101c1038011142403100140c0700940962800701100416210208401134a0242c0100041042008030710101191102060481c4806440300c502c16261402c2c8541649903102c0c41c0b506c0300290040391000500c52004000040d071301a55215808243d0081b1000b1a40150b00c2c500ca408040d0941310385000b800020a0840c00c1060000228002d0311841c01d014051200101d5900700c4408800d08a801d21503028003a11a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 539399739 1250 539398489 539398513
    0x3050a021e010912050301140402090411070b09060c03131103121c0b04020c0706080403171608070309050d110c1503061e09010302040b1309081b06240a08 68
    0x3d104006084450540c218100701c1c060b846038060300c0c103030768462134855112014441000001d5002c00c1d90103400c030341c847c40701524844000303001e0039a05000b21040540e03890100046410980d0003072601c00d21650900c180041424002215034180d648000303d00d4054600d0b0340024038000b10b0007040c001080c0005090504045d51030b110100c28140310100f840b0742d9400300c0c02c000c180c5c0600e03400c00c0700e907600032001007114a02c983c3c2c10b250858042d0504500c44030581100e400d40c0b0004460080004160781c3d921a00c89a019590a920146030300c2c0812044008d951038644820019071181c042051682c002680040140700c05041e84134014241c400c1c44048003100c0300280c000300c074020711440701c104048141a2840000e06541480103002011907800c5908100082003407400c0031350880d44d80441d44109001920542030414002c0d8034186d2586100449083d408001c8102e020658100a007440b52040b076081020f482a040038070925001001d000114101b0541c69100f030006202d8407181e005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 539400989 1250 539399739 539399741
    0x3040b15130c030606020606030a020409080d0e0105070906020607081b090d050c030f1207200d0f0b0c0c070e04060e0303070f030b010c050a11040b03100b030c040c020a03050a021e01 80
    0x310b0305a80d81c03401d00007913136603800076a103071071040b550301c0d4044c0c0040c26040300500d4141c0c49005282c0c40b425609043c4810502e0341c030111500b0302e251902d580c1d51a001c0c00610340c0c103c40301400400d0588020302251a082600404029010b000c00107900c031203031034180c00300e40300506483d031030100034007200e061001c3c2c0d0034102ea0358610022014005d01500c1ca06000313a03400440c10780c1554840c00c80c158a071803410b035500428212141424021a82000f00203081a51040f20030081a03000d0380f0001000403460078485090032014140e0302200c0010480030704600750228240040710265111100d03591344500304030700600900000d548190200008012859800a41d010042c0682d560100b00600c80540155011804400302904039030108000700e0005040c3d425001800381e0191001c51483c1a01000ca0714250f0700c0c0d82201d0001c2d441d2140124607050400141c1c40300710b000c41c4c0034010200f601101a440e100220b6028041050000300c804600e80200010104400a528940d01480714112058 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 539402239 1250 539400989 539401001
    0x90603230f120310141e03010b0a06030b030601090204050a0b0306060f040e090d0215180f070602010902090606030708010e0c0910080103060c0306060516170406110d0201050c03040b1513 82
    0xc4d42c81488102180015034101100710b00400a0703c40d4090000501402d0110092aa6040d516640b0b0b800c2410043d11007000c0e000040c06503840100d8401c0400e0708160801c24140c208844040c1b050004002c00d960340e5807404215145542481c0d80c9480b004003207841c9120b008030b1101600000140002d90000000c88140700700c07513010a485266080e030748108e0310742241046c1c0309400341c0c1c4003011400e058411283d682c82c4804550464100951040d0101c0c07e008140c2c1c00800581d541d40c501105604209160641c404022903800e4503500e06940003402e2040c1c1030044062806010000809107005c03d0100e42d000a00241902c03034003120408014403009090004540c01401c21101700b600e075000e4000c140a031141c0361030b02e42c1042e2800c08444000d089450040c0d92a0b4500c0d0042008040594014800307000070756166030202c0c0405001d6480c243c030703c1c00003204580c5841c0070803101c82c140c0342c01d0b43d401071f91090300000d81d91551402648102007400e0520b9004002c002010b8426941e94019 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 539403489 1250 539402239 539402251
    0x1121406030f010c0c3801050103150f030303020927010303030e0d08040803090304090e010207020103111207030902060d140411030f0c04051b0406030603030801090603230f1203 78
    0x182d00700601c03044414240c440002000340402d001910070000541c80d010f02219031034000c2e80d036085440c0960203060004046280a0340b002d800e59005100c2564075000304240401c400c505400c02e18580f4080031401186880f0241c01c05601150b520800d82d1001543c441c200c1d0b03043d6862415105a0802c46c4a455003880103c011928058070a070100310301082c0c0f0001e10a00f501c2d8000b5a0755640c40703211059000411020443c0010000864451414420140ea041c541030006841705403a01c0003408136402002c00d030f07264000c1401180c1d507420b421050180d01141c03a141c0801d070181d062008c07071424000d08142040d01410502c0c07903080c0c86070010350f4501c2580101c174003004110103c01410749806400d41e400003141c10640c0da040341400c19401140d040011075549800070030003404040c005411582140f0002030f207540d03040050540c005021405441070440c100040c13450360703980150072403e203a5250fa00c80002d00c1c136402d8800050140f007551a05800035510100c1c10b040031038a8a0740101e600e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 539404739 1250 539403489 539403493
    0xb070302030c15090a0f1b2d030c0b16140604213507020a0c1a07200402030a090c0902040506031f0b070c091b1209020112140603 57
    0x201100d1415030508890042d444c0342c000d05180c82141d203580001641800040d54007942680d0501c00c03a44229040f40020300c0c41c4403240301c40b070959141000c500160b60840a02070702000310203001013640047c85c0b40c111403288045a03a40c104550101c0305a10058001804005c0c40c800030a0788c070240418940c0c481da109200ea00d000d04641a5114045880d005802c1c0005030400408540380c4500d81c0c100c00c1080e1401c20799810040c00d10700318504c0c40021100b080040c0c2001911404110513224000080d00198500301203ca02c1115a40c24900035914094060345031203085034250b040e075021040074040c6c060415540c91405800c4000940801401100c103450134001c00540c1038050b109507403d41d80020311642c60368403801140c42d0307401003552a81140d151011070000d0542d402e036004100e040c0c03180d905610210320345464142143c2d024202c12101c6c0800e8210540400c0d84051040102551701c03000065680050004880315126245180101407a08a089000b501c080c0e0110b84104000c0741 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 539405989 1250 539404739 539404753
    0x9030606150306130608010f0204031e050a0f020d050f01330303031e020426060f0105280b0705190c0308070f0b160f0905180a060b070302030c 63
    0x5201080e03400d0040c190070300d903042c40450030510b407083c2e984000c0400360ba008280d490302d84904a0848060301c4c0140c040d2540018200104800b035040c2030340c107540005882c290000c4035151542c8583d41084020014111203410a04564a080c107048200341c001c0115024030800400450081c03048040b110345103170741d144007128601040460107002c4295900c40482c60361940d0b03000c1e4003070005400280008800c40c07510f0401d050b003d2000d0b02c01070200402c204000e07842c015540b81c04100a80d0303095046d800200404c0510020741d01070a045400c140d4501980c024800c107480d8201c00c800110306044684000c00003000d107181c00181c51058010000d07160f110120244c1100c0d0300c200343e40000c1502041e000e0070000314800301c001c1e0002e140228422800440303213545440c0e01c400102d0359101c0710f1070b0701840d000d505540b14420b0b1604642c00d0a11603401c0d8206000035428105c0e80c00840443d4bc4100300050791520345811503801407110100c4561070305600c1c90083d403260003084007203e552007454 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 539407239 1250 539405989 539406001
    0x81503030a0215060d08070609060501090204080d0804050304050a03030908060c0c1c1812140120070f080c0a050f070612020a09050a09020a0210020703020601061b060908090306 78
    0xc421551444500d800901c0b9290b01c18610b0600018014085980703d0140503805000c2078620f0b008002e4030784a0000090701104601e0004d0403150181c0200500c9441408207029040001840034009029401c1c40a040d40d19440c100b403452041d13801c00d035002180c2c030308001f0406400c9042c040544041c0003e0301d0190382c580340d202d5035500403006941c14651000e10141e800002d40d070304c0c5501400403031600c2d000000000000b482210b549922030302e00070018004441c107014154118948a54406000340540d180d104548480c01c2c840c10b6441e010840d00083d41c00410800030300d84c075222544803400310703240c00c1d05030364154848a501200ba0380c203000e0031540f14481d4030702007451700940c1c1d10382d00c902501d140c2602b1584000d41201c101002805141540441c82e951840120b800400581c3e10140e607401c0f140c2030003414009000001e90626005008050000782c0100d800c5055071294903105018007546500303410701614a03803002d48141d1070585c010046c000a18000c00f1320010540c22903e0b1070f2900c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 539408489 1250 539407239 539407243
    0x210518040b0102120c072102041817090301090204140403170402031c02160b04090b18041103100203090109020103050601231b070b0406020c150304080306120a03081503 74
    0x1041c0100d00607000040d41e90800395000018180740f0b000c00c0110340c100c6894200c404034481010000103051403400c20880704626003401444601411944e610500c15074558840e00381400c3d01151046101c0041a000c285071400d52004400d650002d00a100707070044000070b99481181680c0560000d02c81c40c48480700c0110802d0041c0c000c5034044c0c02060760001070840088800d00c0420840110b0144001d0f0750801e0800d42c4844010b1b01080c0645a6240d29284d00081210751490701c242c0103600c85141d082e1a00c284100040e4081c2c0c10051841d080504540000e080081900c03180d030440c4e1010091004a94055100c03002c154800e81f01045207440f0100103568071542c12801181030401842200c8026002002904154941211310300c0240b56485d5650304110b00c1d50000e41005001040802c941d036810001141400e40c20740d1040007800740c50288840f14070005001401c00003000000c10082c0d10b1b03003010000742c502e40d40296041d000017498024048801920021103004032030722248214640 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 539409739 1250 539408489 539408501
    0x4030503030a0510260d0e130b060c03070c05090a0b0303090d03092c0c0705070b0a0c150507020105070311070f1109270d0e060721051804 61
    0x101000350704507039401c407510020f803400600d100100c0846075000036000c2514519861070004801841c0781443c90010300320300e00212180d06400700720b4580320504003500d9480192800c0181c03040082060600940828054803c3d07440203201c030300c0700044080070700840950035010744d10700311003c40c19601c0340107840c02605c0c20200350590542007009a801d00e49404603540f140309100c1e060070010a40d54160848a0702810f41c074402d1082d000038004c400c4100180c9100340d000079641c01481c2090402e44401d03075100d8280c001c980d035041001410b41e00300e80c0540d68600c00769900c0f40180300341071030a100f100003410050314040003542c01c01000c03a0006005c0d00980c10681c0781c6080e0320742040440c1c0c0350444003508100c0c1c2501d5440d020424018a40c445015071b0340724015880644550002170016142c1079035890b01c080000b41c1066040c060141d912100c3c4068080045910a4490040c1d04100c11124580d0154482c1440031502c4481e110381c001e00a001649448508a55140c038030409000035590 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 539410989 1250 539409739 539409743
    0x1305100501050a06030b0d140a020a080d050712030e0a030e09070201051b0f0c060a06050109081609050a150821070206042d091a030109230f01060f030201080c0403 72
    0x443c520003030004500c680d2150080680c001c0c040000f00c480c644402804902614208805403c20710790481581498050000108290b10003030510340344a81000f80180581c080081014000c2c0500f400c0e680d00c41d030881d5212480b05016984450306514024280300007080310781c0d004102e6540024800360040c4201e91282c0381c00c072040210090034184801c0d460f80040d003440c5002c081400344110705502004030302e01c50450040e00150082c00d1000140c0b0f004002c1c0d120040f16401400c807035100403031180c3d501c2d00b264501900403496840315a500c4d000f800c60091284540b1801d0200069a41030016480c0c0c070a0038080503100c8182c450140100d00e40c4508800650015420842005090308140b250004a601d0390451002c58615a05042104410f40e010410840e1144018903070b14051903103402030303280120000c00c5040c0c0c490b0750300c0000001c0d860000045002c00ca58408502e1020b01101d06001d44482c001c2203030f00d407980d1201c1000c240602041c0e0014030300e4000030700750382580380460f0705403a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 539412239 1250 539410989 539410999
    0x9101d0f0708151302070c0f090e030307141303050a05061506041208130e0a090b0105120c0415080d050c0709020a1b020402090618090601030623030f06130510050105 73
    0x1401c00061007a8840038084d5020100d42c02c120030000318000102c0030340079144c00c4502c40725041c580300054080e0350448503e099590020003d000c4029000a031825101c03000f03011030380c2c545800320450030903141d981d030024085014443c1014108200464042d2103040010b60322910405100f09010450255000c4e822a9810030b122403404a40c1e0a006400324081c40300304d01130702e41e031944400700700448180c42c3c160702640c984070058100050f175800540942420b81d1070480ba80462650960755003107042d00a03008641e104413140046580c007000340c000e02881030480e42244081040107141c1c2d4016031101a2901400c04082404030041c02280c0c000566175440c030580d0700301c00c03403005042a0400c0040340c2c13080e0f003000000e0b61915400c000d04400400b600180e071b0314100d06401d0207a07040b4001c110a040614050060001440008a00000688400c000d14201c1c103240040791600c00011079844561203000c0402c0081110900703401c4540b8840d0080d504000c040204010545800b800360a50007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 539413489 1250 539412239 539412271
    0x10906080a0b09031303030507030e01021519110a1101051305030316020703051b01020c04050402030616050d1a030709060b300c041e0302060909101d0f0708 69
    0x402c0706114140e411038204030a4a261083c0d0b02c0100c03900c50000d910803000f2036030102d0b424090540041c40e00c503c1200a0024006504413551703e0036a059008250704038040d85080d880c030a1605641c8403205e1507944181c00383d40c0f000a144040c01802501441032815070074131000981a8903050102101c065110009608549804600f6000e202c0303000b82801c01c5100d81d42000000c500304020001602d01c90150f0b030b0100f4406074000a00b00603000d46c0b880d002d10709110034000184c4002458950101605420043c1c0003c0714804503464400c0740c482c152441c0c1030480c6280301c000d41c203190380c40724034044003183d601e20340e21304446041c3c070480d11402c011104107000b89446005030b00a0290205289012100e071100a40d84201d0102c500340d458016a02c0c000c01c00380030082c0101880f1100b4440410401ca855156600081b00e6114000d010b1b4001c4c01c0601c003142c600c0c130818090780301400410040460320410501401107407c0100d4050200704035203070100d01c0260150440d40c1c010f4107440003442d80 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 539414739 1250 539413489 539413493
    0xa0b12010b1e1203190806010305091c030902090115110a030c060b0a0e040b0f060121090c08070b0703030b0d03230c190c0902030610030b0301110403031106010906080a 74
    0x6600c0d0b1a111440d0450401020384240003014401041081040c0e04000b031840d94400004010700d81c01403145041c035180c84c06001009a001412009140507030312400d44502c090082200a0101c001c802500042c00380000b1402e800080c0c070780c004580c5d03165075601111a0040d00d9590781e55030210090003140d0350220000108190360071039a00e030711020f041010b07041d0390f80001e618503000032981599208280400d00c8050b540954210350050024a0a051140066410340b126120882c50a07033115544e0080c0508200000d4030040c028000e020640b4005a500c0e1012882035200403012000245024440312191034450312034111683c06545000c00ca150030141c05e550070328017402890b500c0200303000f075041c00d41041084001e0b00c0c01054105034070084600e0100b52412140d001801d91070700500401060340c4030303450b04036003080380e900e0003141300602140030900501201d0030984419800040200a064000059840c401c0e180011122242e81c2d0350348a5084030014000c3c0e030b1361038014500d03601c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 539415989 1250 539414739 539414779
    0x60909250911072301090b040501150f081525020d090f0e070302030a0905071706010902120f150d060621020916111501030c09020306060406031e050a0b12010b 70
    0x6503240144d00000f5081c240381c0c8a8400411044030300312800ea4441d041041d503600e0750b20b00d420003802441260031440e81495085a25552000341d82c1c0c80c14020840040d0388040c10205000c40a020513003d050f404100307400c02506e905030503481001244901000040242d4010b0b01d03002140d00d212542001034032002400c502039840581860061501c5241c0c100109405025180040801000482d801089031340010b0520304143d00205580b03105001840b656040440f000b540450b81041803200342d92041a0f03402440410103990b50080c8046203400c080100e80c0e84118169042d81c0a10541110300b0058400e40850031407000750000700310004201c1354204488810050b411504000c220107103860100b915041e80d071010481c00c59050070042040c4920f409450707000d4600c0c4201540b0718a84840440c00510030f501c20a0200340d03032034500118000710300000900620140c00140150308080007504098038840701040c0c450030300c1001d10362000e07130144030390181a54040c180390561010900210 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 539417239 1250 539415989 539416043
    0x4060204031a01060c02090703090c2912060f0d051606031b12021602180601031b02060f06040207050102180f0103060807050910030203030705100f1406090925091107 73
    0xf006141c3c6892b2510b000403118441e28002d004103183c42e100c00500a401c5161803121001c00142e060300401091481c003c4a182590303000b40b041e030f2051041c0b0403c00c04100d29888034070000e8400d00405448480c2c111010131240d080b01d50b903030349c184944140c5000e641c860f0818004030318085035010702100051096500900000003141e6842d504140840e00858180300c81d4410b11030701d003105002088a1580c0601c00d031000e0b540340100201403a1441e0310041c2d502e10010300310fa43c200c9106070009400c1d07940c070b80440c0d41c1294004000d548540d09031425011422203d801144074800301080f4180c1540300b41b01d01002c86456400800c42545040180091110b01511700c81e0071101e030741b50100140e1410801450341e280f0a0b40200458040ca805100c11107846032440032503035080082c0c0d1411303854661070700ba8204208413006603c68660b0004680b8200500740d040003444401e00350a18411071401c0c01508907007000909004040c460680601c4602c6020402840000030600c103e07a4020038594103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 539418489 1250 539417239 539417251
    0x40b03090307062d0c20070306050703050408070311030d09050a14010e03042309041a0108030f03040308060102010b0405010b04050307090e120f1210081c0e010f0309080304060204031a01060c0209 86
    0x11400000c000c2546c450b0104030710f00d19159020f81c40820030040c040c840d203030f030000c40c6140c100142d040954444100e8419100c0240400c0000080c0540007a0f0920440b004030a1810f801c0280c27060350310f482038030751501c2c4206544800c441c2c000c001c03d0f42018050680c03420b03101d0001e503160a0408000362072000014002180345d00c482d01405e0103d0329512503281c0240d0213a14000c030b00c15140032015000000503004650650402e214005d03402c1542001e0725001079050030001c005035642300c0102d00500321840110340c081c3c107080001807500d1084c8020015254103400b44d41d00e0584070101001961000240b1103465800342409a50102d109000b070100030034007100302881d00c444581c000c91318210984510080e90650301d01006034005c10403007405000c2090400001ea414402c1d00030b055aa091100241072140400380600058070039484440f4013680440c0b0291281084c4c104400203401c0341c0030031a6400040607594400a062a601d94100d4025a882c0701540c00340d0b44c20f1021103c400b401e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 539419739 1250 539418489 539418497
    0x806010c1110080105090a020901050702222a0516111207080106050a06080405280803040b040203070e012103050f0304050a0b130b01051005040b03090307062d0c 71
    0x54076003680c1d40901002c0b0352111030381c4281240d4141000c0020a50002d021001c031a44104102ca5503660030000365588607804070f0380b061015044507404202010398050030f0204034a00341c070400c1a1800c40079032452104100b00b41280220212405403110b10450500c1c2084064600f501d00010302a40000b02c4000b0380600401c0c1da184510800758913040c0315030130a0049035199002030026040482c1c008004100502c0c2201071400d1646640c0d44507050710880c01074175501d8003000c0c2d52849030b00d40b201160700c0d40155456540d03c1d25081074450341005540c100e00c20302400304001800c030030120707000b0305235040500044401c6003540064012120601012018450240040001c4c460520f000d144282c0c042c8000c0d140c032004500d0400c1800345d00406c50700e400c8035040c9100c8045192401501d064038010f5900300360300740d416031044d601e0340103d0f841301d0b8040400004202c0a41c002102400b0003d01c60358091100d18400142900704003941d500c44894010306162031690340d803031074008d1a640b101c0e500b4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 539420989 1250 539419739 539419763
    0x30f2a050c030d1d090408090d110d0b010e3102011b050307060e070b180301060b031e0c0906090108060d170a0e0306040201050405010c030512040f150c0806010c 71
    0x40ba00b4090b2462152001c2100d01c1e01d104003018000110303403007090088403844044d1406a541402500451180c24081d2252171000c0c010800c0354a422000d1044c024603004401800c3e14111a06160134040c403003003460b00c1404642081000d145182d0300d0100c60202c0d030000c03111210810801c64034401c0681c104000b22035480100310080000700039107400380300a1999612030f0b05040081d07510307010024503643d01a9500300481090700c1e0681d160401841d500b251035800b80750000380540159040402c48003400020f0000e410080c040b49001c4d841303510b00d01030090342c502001031904e0040c040c0c500d80140b81084062010340c8101030f00c65000000070710150881402d52501d01c10f90403a154058485600010400c3d00c0c01d4100c1080421030600710010f25040c1740580c0020720074000c91213418140309000e89080d0130103020704140c808c0700d6100505d0071594501800e05804c10303540740005032424955000c251041c0c01c0d0714000c08441c07030541d0302c1d111051303241c40b8011504000c02c00e1050315017401000c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 539422239 1250 539420989 539421013
    0x30301080c21071a04051c030807090f06120f0c08180115090b0402070f0305130522020310151d0105070209010302151e0d0b0105040f09111c09030f2a05 67
    0x45e010503c7c1e100c06031464501e40d030710b898042c01d42280581000300f03112003142c0c10040040021179110a480c071924080c801380040b4600040070700006003045c3c0c1342e241410f2004880d00d0f88140d0844c4120313054280441c641303060f95010b500704d40f035014040c00510724100080c00b002107941c2204240c2000500300511341602525151140418000c0c1240010800102030302c91801d010175000c080c0c9400c454040340ca581c0c000300c109401e403111860003907183e00130000412424a40452000901a07403c9000c0e1001c0402c070014110048452011042550550350718110b51169090790100c941c0078044210990070b40c3c0800914522040d040c40b0a00d104200c004409910000d41584034080e42040503203030700c2c0c0e10500c00240c500030001c007410000b040c48100052880200118201e80060300000350074000f00f07604851500c5901c07a117040d13240c100840300d11041129446480304034044c0d510f8030148090000e003200c11007045001c443d000a0624035441c001001251a079051511410031142846281d07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 539423489 1250 539422239 539422249
    0x9040213020a09090b040e03040905070201020405030d02240708041112070b030a0e01020a050f180d230606032112040f0c14011205060d05030301080c21071a0405 71
    0x4110300500160b04000c1c10000c40c030701c1780503459803000c00312070601c02d006071440d400c1d542e802907203d0041450b80320008034400030700031350450b000b60001806444d1100d060800195450075600340103c030007412000440c0d05501050403880c010740f21507807a0200c1e902c0300e841d046540a0040c0075950711240d00000203601d42800c004000007042445041d0b922460b2140340041140c2803401c4407040713a40108204801ca95000c1c0442305503868030070071a84c0f900303a8504c00a02c1172000d85044c50f00701c040000c071036082c06400c101c2c081007684040340000042003403801d120b80f00d220545400341c1680c4689446400700140d40310000d1480b0703400340600d081640c0c005c2003110034142502c00313a40c8194425101024840d107c001000a8a00d0b0140e02c2c800521410000701507510100860f81d074283c0c0e440c0070501b00d0b9907020080300d103203070840116034403940c5640742c036611400c54018040c400c0140051903404840101c2c14465101403040103400035a160400c059140150b45601104110080201041590720 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 539424739 1250 539423489 539423497
    0xb0a050126100608010e071205060403080a18030c1b050f040e0309102607090e090c040906021b060603150903040b070c031203020c0c2110150e010e01050904021302 72
    0x130480010840c1c00c0d52514031410424a50001211041e100d4018008075000049413034010394540b40c06d95060340c90902e904018078442d001300402a5512881c10281503209928000c82401228480710441e0b07920a0b14011403a5480342580004500d4010701e84da29281c0c0c450403044903104152840c048510001611a008500c50f090110f484440007a0600c00c02504586540a115220f00050305000b20302403c00e51300391160041200d610300014a0707c11082c060023010100c09232042c4240107051502d04060741101c0840a481150548040b401e80c40029050b4040d60020300078060440e501140211803100c018040700701c61104110001c0c0030010fa20051000034040c4890310182c80c114507258143c1254641032508041c010b11031b0000301003010601c0028a201200c007148144261200e84000c864118a1810540180e15110347c0b400e4554001c0a544030842d024002c110340c480c0081c4103140800c1c010400c5085101c0c006002500345203100c250400d000405a500006000e0401c9081e03901c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 539425989 1250 539424739 539424749
    0x4021809191413021e03011805060c070f0605060a08100f110408151902070809150a021e1207140d021b01030b0a091401030b0a0501261006 61
    0x214554030610071070818482c0308464046021003640500302808558040e50707900c50060b20600130000c15600c00500340c800f00da61400064000d010b480700c030764610302001107091800d4959004200010307501c02223090403205000d030300030b4400011907196190701c8001d020081c88203401a001c070401090f115020807070b148070140d421002051914010200703030143d231600d50f00c08020b010b00740002d01084030042081d03416124005100d4420f076507200d8a81c0340c00c10481c503010150a10000710003080c42080b0300105030440d01910b03003440b607046260300b4000610501075404016040794901c000131110030302403401d03030143ca5400c450308405040c01c186815071200038100c81200005801481031402844002e01504450000e449410744c1114583c0310f151101007030704e040503a40c0d00442c6541e611005441c0242940318005c200c10b0040030005440b14000380010380d40d044140740001da0035069030040c181030f140c0c0a10600c581c114940140c0300a034980d81201040d0380600322905d00030205034410400186 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 539427239 1250 539425989 539426011
    0x6021c1b020c0406140909120a03090215070f080c0c09181c020d050d0608070902031905040215030a0207021305100905040803010b03071413030606080a0201080604021809 75
    0x11845240c081d20301400301e04094000c60800504000c0c102810104100441c42a40d0303020541c3c1e1034403611400c21071544003846c84074801041c040c900303a0f4180d218240340351080c3c4803048040c0c0348428003d01802503042c0204400c00c00950365000602c000084d0145401c0001141c1c1414003000009000020403224802d6107114070400801030078042001c00400347d512880d40c6081d842c0480c0c020b480d851080c01003002e00400050b50701d5200100e5104100074078200b826100f50707944802461000c0d500c1940c6040d104000c07001d11001c5d0308041e114940c09903078010581451030440502807440b90308000c11000d4103590a101ca500035880d00d0403402010f000c1c007180001e1302c2c43c10040044001c0b50a4200c14100c0f4500310401c400030fa60541100d0544200c54001501c980d40c035034003203034410b03078001000c40e84150116a18611910f5105407a0540748564818040580c4840c09207030345010001000c0d00007210500030983c039041c19801450f0a0f80d034402c259280315100070208001e4502940c05502d40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 539428489 1250 539427239 539427281
    0xf0c070203191a010e090a03110c0d06060303030e0316060c050909090607030509030906041a04080709050a0c3f140a11090a1a25060b0103150306021c 66
    0x200d03841940f89001d003504040b2584542004070369150b50314003a40c002401d05c00324140300c8142a41c100906203002200401a041e10401450840060309d69480304402103410542110001c0c00080b00765124007c3d00800c0c60094205502c41c04050700c1010307500000d01c8420030444225031210500c1c00d00c10940140100b9a9090000d0000c0841e00018060101904280b041d00f0f0943c2d9544100d804817603014401c480c03e44c03001e201d2000181700c3c0c2c3d03105603001c1c0300b504030002d051411a00b1461155902810401c900e0103859001e60f0030312080f000118621b2650448005006801601c003050360080c07031000c0a00603143e02c1420b00b155007191403000e240c1c101d90b0400080c4805030290f02624500c0c0b0f0451414080f1a201003109006d00d80161800d104808402880d1501c95400380c0b410901c0c1101d42a00003910074101703000e54100000241c41460505074000c1c0785500038001c4006501e400c0d46c4000c605481c8d92580002500b119240c82d0000000601340d5101c80e0307103802510b1104c00c182c10309540e2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 539429739 1250 539428489 539428523
    0x51e010815060f0d0b36010b03281e0f020c03091011030a0306080f070806070c03030608160f140315042f040c0203030f0c07020319 58
    0x10440c801040c0003480c0190024006040c0c403000c081d2240c045544084503200c030385162a1601a101c1d100e9420b42100c4c0f040ca2012545c0030003511902c10140c03a04100c54a1107068400300d580034024000c170b9640d10030400209101100034000510030180004014000360211503020082e80c01c1441c414a00d0703042c40c403842348800c0701c078464181a0b450b0103204504c1d08121100040d240d00603072924600c103800c110141d26410703000b241040d60481c1c5c0305056030350300c120b1801c001d0b00030081809080001e1190407000c03e003186001420707209441041d0000e103940e5903220021104044808403c4080546030b620001c0c0503082003100d039559050300c80141c1050740c00e00f030190754005401e61062251001c1c0816140c00f94401140c0480c8108150044800c10340e81c1e8100720a041d10b4152016a40d40102807441164101481542c500701031b0480d01400020300c0800100d80d03a01050314411603903001840490218401c4100a01d20356201605072001c85602c040441d21071940060150f4402403c10360f1054 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 539430989 1250 539429739 539429747
    0x100801061815081906080102132720040306020c0d050a050f2a0106050102010c05040302090f070311030f07140403051906020405030106080f0c040603080a0c03030204051e01 76
    0x140c04010a029441c410345064546807000310001d1191090003800fa0100d060f8103184103500550001d80390045c00300b00e50716a0214001d6000b8112980c001001460204150703480000140c00210002e8012090007091031901c0014540320030f49070706035041c505107050075003507000203000158010040182c880c00815102800c000c0c00d0b881000c10808204040a20503400c141a160340004151030107072540a0301c1001e890310400340035900000c0345101070951481c081504040c05441c4203030300030700c06203400880c03d44650080e800000c0d4849000c0700010140c40008a803d94044c16a01e008145c1d1184104001c0981e8410388840080c61600d20070002c2058010760500704050401500c3c074582032a503200c2c1130f1114810b000c5000424240c403652010710155806076005404024000c008140e500d0180c00e40e155142c4000c114140110510160207207024818034044903000301e245803505000c50b20440e000703540c114040f4203042d401d01022480383c54a0704100c8080c80301016a908114040700050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 539432239 1250 539430989 539431007
    0x61806270f0319031101090c09050a0b01090503070e061504150f170a0c1403070302041a03060d08030a09050a0308010501030e010507021e0703050a06050f070305040302062410080106 80
    0x74025400240c3c2c030760701d4800303088200c0700c0942c05142405800d10300c0c545441c090b040010000d402618449008188400c09500c160302585c3c0c1480c04015200d00400190340c84aa28421039515410203001000001101c14106622007001041c1c1c403400c0c0103c20b44918990803d40105501c02501c0e070b420411903400245940c802606820702c0031a600035140105800300f00202007489051315900346e00942802854402c5000819060391a180c0c80c0404008000790410f21801d10449003042c030aa1a11062900b00c0e0b00815018020380d58407400e83c0c07960035455101801400c41580c1e101101d801041e02840364610840c0f0940e42c50081e03502d820001000c0d15520441c810603a49000c0501003003540010b920340c0a805600e401c82c1060940e03001c180d00b04030082d8005081400f40c0c541c90f9080207903903404981300c0c80c4080750a60384c80d15061401c030100c801c2100c0040141e803240300840c400141140000b2800e5901ca0100a00c0118040119244140441212011458100c0144071013034018000c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 539433489 1250 539432239 539432269
    0x1104030803150a060503040b060d150c020c0a140607020108100f080106051305060a15022418060702100504020a18050a2f07111e100302040506180627 66
    0x141142040c0d12040d065450107401d09212b8488801c110301080b04440b40b8480c0740c4500030007004441000c0c0c4011b9206d660a22503144510244007000c221301e03000b510300101c0007034080c00d0a400c080441d40151000c480c0900f8040d000c5110040c0052090840f10b03051018180f400700115400e842e00042c0009000c0d4450240103003418001048955110300740e6038000c07610308100c11030410720550380503810440c4000c04816507290391b40c0681e0001c0550940785000d600550141e00d88a5040c02000b0f440f03042c04e488007001604442e6034140f81100c90741007150818002455289443d42d47d1062180d0042c409000b40e400750317186d10401c651030b4a144254a406e460348211124264505044160003001200c0b10115180020425005001c0500058000e041010b070038064110700c8000300d4400e41d048030404500c9500c00d031440d100c245120703000390f8003160000780125061400790b0954641a422013150182c001c0401c0c0040c0040e80c220020112070040c2c0910810000b002082c00d10860049601c80d07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 539434739 1250 539433489 539433497
    0x1b030702330c0a060b2205010f0b070308150402040f030f031211090405090f0618070603140c07030c02040f021b030711060703020f03041d07020f07091104030803150a06 74
    0x420b1100c0c07000070500c054142d6001000007885a141c50002c1c8208040e4001160001102d00046c0c44194031907000906a404512040c9501b60759010480d0040c03082d01c01c020002580319000c43d1a42012140035014003030001d1000d0708140e12881000f041c0d03d80d5600a0b0f41038078903442410141500600090307000d26240c8014880c40e050710f1500c20741d074443c40351014041d655583c0020f405c101e0038080c8010002041058030040c1c140500c4440300e28040f41100380e1180541032000a039036000e031046010300c6500c0c00340c0c2801603440309080301d11900716010540500c4500043c0c0b500580d5284201141d4ac100e038807006854034015680340303111200426000120f9071003082044c0c0401d610582c0c00c2408035048825036601c2e5424a0100e0420341a01e00c0081c1d144000704010402d03001a4680344945541a0107040c2141e403950001c07a91540c2200c000021034100c0881031000050b00d401c083c3c6c6000d00c0320f24041c03030503a981c0e031071b9940750b030080315a40b411030100c0c9108a0586001c80383d1400030402d92038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 539435989 1250 539434739 539434747
    0x3030f0b0307081207081b0d020d0203030907171c03150e1e1e01121110231308030c1504170a030605040f06291b03070233 54
    0x800c640d40c1c4c1801c1c3c50340e40b1030080c041002d2003080b1032102202d600304102d0102003c101c50040e0b1480d0f0340c20146030450702600856181000d8944000241c91044034100020301c41e5501d01020150211004200204180100c06001c080303108041c0b442010724590707070340000304e000f480a807000e403981a90b0030146000030a8014060780b5030016004101c900c1d40c9c4007014489031100c01d00c2c10703042203c06260361100040c4000008115049506440710300d80582909a41040100e0400801005100d681008651001b4108020308104400b42c04540b00051000d49490303440003c07501840c000e5401003026600000d0206041c10080c801c0c820752946400d01d600090a042c1c6d294080a00440083d40000c400440d0240742e0310b20a401c030b00b0003041c010f8400c01c0100703400110340d00038111034059188654060b032003003550301007c01505100780411100307541c00d10380440072501108100032400c002601c024428000940c2d26003003524083d490710a6031880502189800c0701200c800100886521b02042c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 539437239 1250 539435989 539435999
    0x13061a090a0c120c0c02090c041a0415271701140f1303050913021803030a020c06130803130801050105060f070201080a0906020d0902041d0c01140d02030403030f0b0307 74
    0x20b12180c003043c004000318000004100c1129654078115001c0d41c17280044041c01200e14011000304159040ca00386841c14202c40000c0320b8072481103205540c80c145a0030307102030090780f046071861101050001144e24140c00580b0380c00c5c0c005000d411590b42225686048801e8034800d20458040400e81030303d520007032614509810f0140b0004141e681103902400f2680d0400d44a070301140c885203001003c04142c908083c40d00c40003900b09800da101d0341d09908000088500c0d0010580b640305c1210350007048003599a034180440b0390400c500704105818440400318003010148007800002200800010000e4581985a400c0d40c1d07042e03001c3c501480c1c042061104210440c000c5921050702800c003540d0f6902e9050054000744a000d00242030144081003030b4010520b00d41002628134001c507024091000d00f5440c0c0200e000e40d1640000140c0d00c0f00c80704030400d500070440c2c071140104030b440d801d060007000401031041c0d91049808900203681c0e0304056507007200c1d078410180c01c010300790014482d0900382 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 539438489 1250 539437239 539437247
    0x90c05040e060904121b1704090f09020604050103020c0c04020c010c080a0e07170f060412020714131e0c0323040f1e060603142b0813061a090a0c 64
    0x32003013090420803807881d424000b5800d13103a1b10000c0c0398818010001d204a40d012031003a608180290b00c00c49081c4007001c5001c00d6603010782c001c4a90000c10407450a0702c2c00b0b006400035880038030081c003640030744100301e25155181d00c06031210a4000307001007080485100014400328008003d221101e2070407420190303402c400101c0c1001d4610031020703001c00e0400f64007810700e0312200f440c180516100b0b038000c0104112b0400801c034540c2e01640c0031111200d4482c1e10f00e15480b02c920880740d030880c071100d80c10a03402d8100c0e00300408003d82d410200c0070008403191b1901c141c0c1c075a040d11101083d00c0c2e4001d42007a01710012030960506822030b90b260b042c1081d03510440c1200700e2940141156005201964038a40688025103906a1020b001c000e410b65030318002016450020800109005440340d803899908101010440c45429011042035000340040c1501c4201015001031a8403104920300c10000300c140c412510302c04001c1240c10340a82100c000c02400c904020000c4601d1810040c0f100780c52030700 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 539439739 1250 539438489 539438513
    0x30314040b0706151e1e0602060a1104030f0318060305071b020a0510030e010507080402030a03030e0304120b06040e1911030c030a080a0342090c05040e060904 70
    0x44840081030b10814004c1050f40140c694200789016070004e4000210401c400c0c80c004211003210f0101c0e607012900c1541c03007450101c14456900503810403400038045013820b50280c800c101a0108003424540c482e103460407054000c0c8030131004545650740003422600c2d0010b940004085914040c06180b4141c0c0700103200000c1d00c4006884a45c80021000031590341400d40405007001410f04980d1082e00e01000740540341d4a0800060341d443c1c000407802c118890700520b031003280c0180080202600560f0100d00620501c0d044203460301080c08042004005000b040c403040c1e0040e10215098200071040001301c40014140d815141d12080c440603110560204214000e80c1148105151038403502c007180c1003810181c80d680e81030082e08409001c010500d0060300c036000c41594108414142c0c2c0e8440c041d4a03070480740191400081c24100350030300c840c019075041142a00c0343c040305217660711203242083e50076030450000496000710381803100c0d064040c04503038841d80846c2c0094084c100782d2141845000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 539440989 1250 539439739 539439743
    0x31a0d02091b0c0a030905030703021503100504050a061404060f18060923010807050607080a051c0f0b010c0213020717030108060421021b01170907030314040b07 71
    0x4088000540200e82c072100d10010300c20020304150790300c0c2d0980d400e0740c884031000c0c022400310f40d01a40c0401c1306c3c200000d080003540da019103108644c440070340b244a00703500000c091032440740c000c920118998440703025541c0640300040002c2401b90402c6450f8550b603800701d8805005518001040104410400000085803130070815100700c0a288101c850140c40345d50080a205401d0240c0107196100e20381821410503800303000c001140c1d8a508982d500c86405200755580000207010300b101191140b0000c102c40800703810401c0c45c201d44092110960aa11202200740c0ca43c0ca1002c121805514004c00507908000d10700188410300d95400900f071550162100002550701182540401100300200401d00c05030780080d80c1c496944180b040d5403160b00301e50407558503c4080b82c100b0000e144001810030140c6913000707400c1d51002c030300040c0e054500401c2c1d4141045803800c240440c100e000a800c0d40a0f004200180200509506000c1c002d404841101c05d60400b00300010403e440780c003000d64202c5a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 539442239 1250 539440989 539440999
    0x10b0310031202010213030b06040e1506060a0c12020a030815130905011103090c010f0c081b1e0106080c0a0506030406112b050f09070e0a060f080706031a0d02 70
    0x400c1c42e070100d0080c0111802c3e00300d81341e00b00780040240240a00340ca803181c58222401d01c04000d000400a8503100c201c0045480e203540b00010600b180b800c8000341842e04014507019810031060344507400301c81c9034a200f1a0241e04104a500280741d03101b43e0700c0d60310440c0c85071080c03864180707080403c1318a4182000b0040440e52611003000b048001e42100d004c8d26140d00e1500e440b403c2c5888d40c692603001000403140458000203110405502901020004540000401d804c00c00e031080740030400d8880c1c0a0350030080c02080320901807508400444888203007544000180030781424055464402c0005440e481039214000400c1141d5407103003125402075110101213034910181400540c903001e021500074219003581616400250740c94a0005480003441c000c0c00203407602c425401d6452000d69001c450364228580601c031008030900000d4112060a00000ea115070300c141c00d000303002e12600001225000581e0402c40c0507418050706004803d0a26a00c1807000080f00040c08400000310082c029 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 539443489 1250 539442239 539442263
    0x30417011b1701051027121b0906030b0105090402010c02040c030c0e060316050a0302040302180406140c0a03110c010204060f1e1d030f070b0307110a0f0816050f030a0305010b031003 80
    0xc0441d80c41b001c00a0400952100d44082580350201410f00700e00f8412139920306400d0006040070450007a0380889800c55004a040d0b42003205200700c507040184140d05001c0b0040304400162240d11900100b510345030740007d04030040c440020424920350a1083c4030f11000d06c24000301c1000201c4e0f1340c5000ba22810a03960720f1400e200268040d02a6600180d4850140c01c482007800035035010b110701c0382d4070641e01000200e01d1800c181e012018160744000e81071100f03001c41061103001c1d40c840c900101d1014105802d0503059008903003668007070f8101c040014407003030380140d54903003001800f01c01d5242d28007a0a900d1140710340c0242106003821003249036224403900000701d07403420302500100069240944004946607010007102e603000359107075400910b0102205c1c000309808100140902e03400001486440403584a00c031140c0c0020304400745124074401ea1000164040051003a1180c094018603110410058042e04440741680544080b000800c2001b884d03003407150000003907a510103000307160 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 539444739 1250 539443489 539443547
    0x60904021e030106050d1d070b03060d06050109020705070b03091c05070803040b150607020f1302360904020108070f3c030b03030417011b17010510 65
    0xe1841c00398100000c40c0c030002c0040354451340503000b02400b021408003802035002c16210300c180700d01c1e4180e00302c5494202035810710544030203000071500320b40c0041c0707202d10490160b10381c84212402a4008041c0d41d5000401c1c800700036007800840020692000400c0c254500700801c00c0c1c9448440080da41e801c10117031145d5071407d0080c410303151040e4004c0781d41501c901d443e252004284d0400c1d100441c0a04000300c0c01d04d5a450800201e0f1005a0702400200d60f000c616402e029449504160081650390203205001c80041458034110518541a0070b07540e000c03c4800303114802e0340894402c1401501c03010100030250760050401c7c0d0b0000454504942840c5540724215690b105007404800c0f1141d80c081103009041c2000350340840107200758020846c1e141d05a40580413a4800100da9805030814801044010341011109444203003200000c20210640492904038040303403207040c008100d011680e40c3d03141007036280d400c0c050041030300c8042e00800d0545018240340d002501d403a07068910f0340c0d00840 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 539445989 1250 539444739 539444767
    0xb0303091c021804030c020306010503071d18030a0503150d080927070e1206150108091c05030f18070b0f0c070e0609101203050c150a0f0c08040206090402 68
    0x701e042e4128031104541020300e4020301411b25403805901c00d124150020880d440d01154030300840307144440032880b620a428904516420041504454010101b042d41041c4014401004886050780d1200da4a142006151403103441480c040f500806411b080b40002403501c0d0200c0c1c41e18082250701c0395940720030380c1000400541d504400e4140940942c180500160460741c88403485001b01c914a10041c03a42100b6940c45000f2910b80c02c18454211030104a9400b0300021504551940f05503402079081b4241040c2c40042020600001031000042114090380500060313000b5081100400442c626070440c950b40e03200d60301469605910015170401c0c1414010100d0300022015001d0742d00642d81c400c090134101500b21106805030381842c000403840f403c0f44860000781c0e0303545d000003001c50780c3d1600c088509400103490510940709991411402c0c000028076288104194038010850003000407501d019a410001c00030140300c05082804011b0303441600340d520780351081c2d41c010b0b260b42100746142 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 539447239 1250 539445989 539446009
    0xf09040207020a0807090e01090b01030b04030212070b0105010f0201182904050705030f0f0a12051c0b040608010b031504080403020d1103060f070e01120b12100b0303091c02 76
    0xf54401d4400d040007860100204182003280c140000c20409000b02d00000f501384e5443c0000145a40d0f010001400000e040320302a5401900904c11035140c91002d1030392000d039611840301030312200100c000410507584d0052406200200b988000d202d60702a1554840e14958002c0d0002e10058040e0080340828038174512a40c1d503032031003404500c02c5041c1400c1040e00d65441d405200d000303003d28000c52001d90b0300000e808081d6140c00c0c004110000e06034580307c50721503030304194400300881000286617210b40201504140f034140d0000103401c2c0c060340200811103400d68480107880e41001e1040c2e07955a00840e000c031114030030102c003c100c2e1340c071443d0444141c403c0c0d0304020346c0076040d51400780c18415808491802064150201d8085031100f103000c3c0d29003c3d04480e0722001a5188007903c4e61940700b41c03841541701c0881240416003400f0403000a1004980c002191131540c0104404850b90104d40181280ca200903006185045044d9012502061000c1d0f0704154502411480008646805100d8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 539448489 1250 539447239 539447243
    0x30206180c0604090f05070c021003200d140a0507020c0d1106030c03040b091906020702010c0506070e0301150b04170a0506040b09010b0f030303130201140f07031103070203030f09040207 82
    0x2290f845446155020042545080448000380751000298030785005084070325a150b001403000c2c11340381d02140100c0c00382510601211065040310480b040c2c07614400301a1104900d0454007041451b65506418816000101007400e0203080c0700501008079000306001d21804030941c0d0300561041039044c18a07100c054112025006100002046803055030400914043c80c0f1600c0d45980303a4131820001c0c1d640b00e00e0001a02002c004082207003000854680c02001301d00c1c4103060400d00e9410302d03210281018422221a4041017a5540d211320610342072040020103203001811800a0f400c0c05070300000e60046020b107258885a2580303c09002004001000080b940030b4100d48948c82c0510300060241c006031404803080d82001503a01041c5000b080f50b2260f040064019400d43d66210704102889401e1802641441070b003207005208500f002c2c0c0141002100c1501441c0e66590b81d00e801000d5070b00c50f00d4a007069800c280241d50045e039011003100d11010020f00c4860b2555614000075000348658040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 539449739 1250 539448489 539448499
    0x9022103040f060207050109140108060103050a180c0503010b060313030c020d05030c0a02010f031803180503060c09010f080108060a02182d01030605010e131107030806100c030206180c 81
    0x840f10307800a0070303400b036410a80e0f0b41e00500d55130300c9044810020f000341543c085941d11000441c035511a60189501010040002c5036000102e07000d28092a0448429038440c2c10003070044c09a41424010380100b2981612000d1851424411581c040642c0c40b1000b802c005001881034155940e807424034160380d4101050341ea8840321403096a81d6044510400c07030100c3e4000b00d40d59011400b91148140c0d095003604115002c031000c0d90101e6404021901100034070aa81c1d80100e0305032402c0140303034490803201d1042c5542c1c11200d400901560010b080600420842d88010710080202044035500007940000145e21042103030503491800b001c2002c1c140d0404242501e03020310301005104481da040c103040c444052211440011010390f1442e00510303001ca03c5505041000d42400c440c0b04c014000c0300400017070090f02508415200b980a003809800243c211418440c807444c01280307414620640d42441000054aa44c000c2d448110007802a0f0002c3c1c03003900080c40e100c6050054402c0004006c1c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 539450989 1250 539449739 539449769
    0x9040503121e01050907021b0328170c0304061218080d061a040612060e070c0506072307020d080408070e060d03021e070504110c0607030902210304 65
    0x1229040b96807a80d4140b22000003000004003800c150184a00852450b409842c0d00c240603090300310f01c01405400a60540304804140940f05406192040d1031800c0304c0c80d09104040350705260680f1142080310b03003034806003000161a2848000210303421100740e820090128000d880403a0000d01c01d5800c1200c015402c00350080030032a600c4010018903d10f801c0821100e80c407003a1050070f2008a0713181d001d5200c81080700b030141c140510084a510345100c60041003040e118003d581000c1c00940721003000c980d0085002d02000310910116910114601c2c02403c0011a0340c0410602003515540c50b5461200003a40c0055444548200d14000d4002c80b40654a40d62052070a0f030340d1506101b040b106c540360802003213481c5014000c03000307415050790050408207480c010121481180c4a18811507100303000d0000350a4580d030040c40f41c1502c500702c1143d00d401800c0c0c045400d00340020080410980380998800040e41d501000e030740304d000790003000c800310b13071f01144007615602c540c0c0c010041417000c000e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 539452239 1250 539450989 539451001
    0xf0c05010f0c0831050304080d020105090d180e04111810061106041b21020a0605161b081c020c01020a03120c050702040c0f021b09060904050312 64
    0x10700050606150382c0c3d5810080d565043d01070f82d08680b001c1c3e0030644003489440e541c002032007102070005200d001c0e03416245419074583e04075281c042001507100140c0d454004014000b02c05000700c3c031b02d018a80c10303c2c81c031030103c240488602c4046400303580d500071030740008a01800310b41054566032003005441070710341072000c1208030010441101c0501480300c0c00f19021a040d07202d41211070224080e40c001301401d45851355801c04a0b01e60740800c0e490314420140000300c148200307554a01101883ca0758102d188140c0c01406507810154100c10140b00c0104400c030303d42101160035903c11178104040b44c04807003a01c90500c502c046264002c0c1614070481841140302c000000804941e0f12450302180c0c020181d0100680c0c440c070441348041d001c510040a9106090900d0300a6031410901d0329000c0e142c42000c0c1c0c002003c544007078141000090717006a4a80005404100d064000e032691141c4d0403003401c1c84030006525480040060b40500e0000380410200201001507840b140c98402d105120340c9880 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 539453489 1250 539452239 539452241
    0x609060605040605030c0a0e15150d0c1b02040c1b08030a0b040513030f181d250c05030d05010b0304061113050d1b0815010f0b040302010f0c05010f 65
    0x3400340714400c03442d062001901c1e00e0005010495010050304d13580903145419032002c02c2d5240200117020b1050002c11402d07041c3d461303840240510141c6442c454682c440c0c00f0280c400c84030080103080610514820300050a0444a016980da40d4116004281e001e094207049841d54448096400c89130406104c00042200c96405544942485042008441101c90400041d9101078412103000482608a00c0101e80314079a05070f880060750501d9440f4000304d1003408590b40c500e034008000082d00c081c0d02c00c0f802d110580e00236003150034a8440381040903c8001c0301400032082e117240061041030301000041200030f00549942d60701c454002c0000d0360f9110312032405580100d4080362810b00c3c00458840761440c03142500c1035040c001800716030300c50821041c004461b20151099800340c0b01109031030702c4818600c8494028000c1100540342d142040f416001d106e00043e00b0003445807400f64002c0c4201001c0d03e0030764040380e0702441c15800070070342c0220a840e15910818017030301c59400c0031a008004006 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 539454739 1250 539453489 539453501
    0x1101060b1c060302090726040602030426040501051308030f04030b130b2205010f3e0306012d08061c140309030709061d0702060f13060906 61
    0xa6008030081c4904520520480301c02d4000250300c40d0300e0b2804944054071600031480848010b4900d815010300c4031032074072410501200c085500700d400208020401c400341081c5c031f0325079400610141454101224659550080307002c0ca80c100640404d1041001e0500e400240c02000f008081e01d0392000204486802a84140001e84203d50001e0121f0b9107143c100702e0108403d0340006900e44140c40d82200c03005401007000040920205d2034210340007090f420304c1010817100c00303118000b13018211518401c00341501c8050886500c00302c54941300515513445001800200c145101c1549c03961a10010b0310750f030b640e0030f1003580c0701540000070580d100440b50340d41da04c044c81030300c80c1021507440e18100710104011850000e0b02c02c082d0461000000c1141c180103003085c0a1100352800e01c41d4100c0400c3c6006440da220342c14060312107908000500090702e56038070742000080c940c00135103015800a0764824019200704040425040042e045030702851700010001e500a40034024400d0782d042181c0035240c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 539455989 1250 539454739 539454757
    0x50d0201060b13051003060305030a031a030c01020303060904020109030803072615040c02190803010e0708060a031e0c03080a08070e0315040c08060705031801090308010b0a1101060b 80
    0x80703861808500d090707410003500d00c000803800300d229045050200340400e03000f100801034103045d107039a400300001d0300501c05050100450342e00014194040f8896a040000202203107009030403524184069907408001c07254801000d4a01c0d01f203a4071075200407100100c06510240c10000c000c020b006000360300180c1c0e81c3c402d00340004003d9200c00c04000c800c0110005603240140205040c1c18203510782080d812a41c0d43c6c600d40e00540d109149401010b142c018500281190801d40000c0140580d004050340f4942005503860808990b2501c2c502080700e0b443e280c08050520010340d12400ca80340046541d80340388990000000c251701d9035900e818551501300e900104003080002001031910361054180701d2160300000d00610605003041007507041180080d0003a80c000b0383c0080c02080c00d80040107003e010310304940e11181d50f40b030419200c0c0b001d0201c89590464690610391800c0209178007029940c1550742006505554840d02c4505941c01c04424040804c0e030b5092060000b02400c240000c2c0600751 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 539457239 1250 539455989 539455991
    0x1e050303130606141c14031914090d02090c040503011b030c0f1d01020a0602071209120c15050705010c0305010f0b070c09110d090c140607020f0415030609050d0201 72
    0x30b40321910313200905881407019030801c0303242003c03029004540d103a030007889008118850300181040c03245825503011414034200ca400aa50900c440ca5000013052440100703100440d040007540d80000b0107002103d00702a101e1f005070b00100c2c1108800c102140c00401d03004000b08002000e2001070f030f5440034200c41c12004280390031350000083e07000e03558044000c120303542d070b07130900032480124040c2403140091207038114404d110701100050898401044503502a8141c2003103508403140060440c420307600320501c60071034106540f002400e0041c40006176080c4005200030385444002c100c6850040100141c50740d82090400d021454065000d035050f19070801c07a082145490b046403001610a80c48001d0162049150402c410842d650040c0f1000480004003031901c00c0c4000f011055562040c400d603a0844114401c0084244c942103100010300181d80b01c80c1010301030f40001d10310106901030f6a000c0c5440e010014045800d2841080242d40d0080c01048500b666040c0310303a6503010441454055 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 539458489 1250 539457239 539457251
    0x51005150307020c010807030e0307050f1204080c04091106030a0c09060c0309120c05130203070206070914090a0e010c0903050d030b0a14040213060e130b0105071e0503031306 77
    0x18019a42201c0c450110b580040000c1130b80900112000c41004001e202007568484c1d00841d804424001045d030640190700a140c015816a83c15040c040c012002000d4a031040000f004284004600c0c2d132550101201d0005080740e031801d08030790818000155a6101e4000002c12148800d160700080d44004e41c1d030350b101081303900c0740e00907125611075100150201d00280c00030803107001c03102c40406010b84070b141d0700e5102e940c2d00e002040800c0c60041042e800d0640110030084401da04002c000c2c2d024140c1c1c03a00d00700403450025085040c08044041d0b40c01141c000c400140400e4064020191070000d02c0020131010a4140004003c5211804111058082c411010354445d1090040c4c455200d03004003048005450f0031420164030200034400ca801c95001c2c00b100448403681d102c038800900380c0e91608040c0030b103001e0405c091a201c0c95030308006d1625282c0504140e9074002d05440640d64806a008100c0c843c4030369844a982560700002c0903880000100440c051180c07092641d11846408103100b4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 539459739 1250 539458489 539458519
    0x50a09021b071404020304021813210f030b0d0804080c090105090912030702010f0903093201050702010e040c03150b0309030f090d0f0302030a140903030708130801051005 75
    0xd510b02ca114080e60442980901e2046241542c021608244018200411501804084220400304032000200c9a030b500070700302c05200314402c40c00100140410103c030b841800c0c2001401c0b503003200b0099030030143d85025070705054482801344401c1ca0b03006980b541c0c403580d60300c19140d500c880107141e01e4010b5140b140000b0301405c0c02d110031800303170242001030089041d031b4070f105207455000107002d54215900c68034001200c400c0780c401c1c810028081d640d80311381c0c1400e061050195040301c954448007500700c642c180c250310401e2255101501e0091030030554440e403a00040350041041120b407640940780450007860b035609a0303c110403614481c403c80c456542da400c001a1680803ca40c10016500100000365550310030000034901c4c01001010503204402130380b00c5584005070801c0450240c2e00000b084254a40c01c400b15500d0a803805045070310788503130341002c05d840313005244004000d40c0c00481d240b4400e100c010360718005001c43c03000800070391030050042062000240700b05401111388440c1214 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 539460989 1250 539459739 539459743
    0x601080106081b06071103160f03020a0e07022820040b01090303091203050c010504060e060903070f0209070302210403140316080c090a061d0a060c0605040c050a09021b 74
    0x103c805004100c81c5c10312220780c64071480040c28549459042c05101d9140038441840e80c40c45014041328012a80300c2800d600c14845816550b401002c4c034020b901f0200200546c1c0003500c01290000aa201f08001000c0c2800801500440c0f4005003120742154480c450f20380c0600c411184882c04680a00c002500840151001c00746400090001500c00e1b4048c4800302c0c00f003403556036292113440c0072072030180118040c508403481075404464154070340801c026095001c11030a034012060340b0141d407420010395140e1910101c82e2074020b0181d001031000440c03550213a03043d58000340d000d4942140d51081d40d1048946130a0481f000c4010038246020122204c803030b0001c0c2c1f4070410080c400902c984280107015100400b0080c1074814498040021011688030070104a0042c541a1910075181a403201098891050b2a0002c0e0249141d1941040780580c0030b03141c0090141c0003680011123403520705062120640c103402c81c58004210f80400102c00e09158010310105864001c4c9000c011030032000d041d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 539462239 1250 539460989 539461033
    0x11b03050c01050f190b010903020402190e01140405040e0a0f0f030206070206011d0619080703020a15210608010c0903050d02121b010209030a08041703070503030f0711060108010608 80
    0x580c02181034817008084114592001040d00d01c14101124265500e500007810382e030040340c9231703c00042102c0703810764a660002800c1e400d410003401e150754640e00418400c4031034000e40c81860700c100d031114401034103100c00b4455001c140384c00500c61041c0140b28217159112004601e0220014490340c000200c01500c00302c1c12a06a500740680300801d43d141c1c5048443d40040507100d168003081031100308148070004c04103c002840c000d00070740042d51840c010481c0700815940301e2078203444008500984560b0100ca0a0012038640704420000c0481628480003450540c00000903507207021544901260000e10312002c6a00c10004c95004460f1035100303d86583e6030505148d0078540c00e2206d282303000000c0c0c4d403d55040411100050030803050000113450024018016264184c00103024000c4200c0e2051512000b231046c8001c51030b10390305a031565900d101c003c106005504140001c04c200a10542040c0e00c2c1412110868840c2d50312504030f18001c0400d8807400c4000d2081030141c070b460858490b40c40c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 539463489 1250 539462239 539462251
    0xf0f0907030b06030f0106061d030705030a02150f0409020301090f0e0706051b0102030a020306010f02070303141c0c031a120309060a0203042d120f020f011b03050c01050f 75
    0x585001403030759541114120014042507458002c1d01c0e1041c1d501e1000344030760300003070500b50b655003820001c0c05080c292020811509901a4020000c1441035881c00207490007095410348119403480c0f4000800b0300680500a107010010200140000d001380c2c65401071410303500001c0003007005544902c005400c507400b01c282a50203030022402044030a0007400541201001da903600700b1000408514103089910440702c0e12142580402888181d50388004201d030380321030343d0006260680c2591005001110303444001c4c0c02002c030000d2503400d10070038010b5030101030183d407106000c0c9a050a00260240001d0009446520f854101c0440780c0d24040786c003c40b41c6c20b8100007441c40c040c1c052301030024590121b00d0490662004200014008107a00c10398244e400c4c1d080c000041c0d120f200103802ea0429a151320140b00580218000c1c804244041d0078a07420360b90407604580a0486000140c464100106101201c4144080101b052582140003480c1003801800200801d58401501c00070317030b18042da45 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 539464739 1250 539463489 539463493
    0x10e180a0201031a0613030c0902030c031906050a06020c120309060d0e0304050a031208160504050f01020c130e061006080c0a11120c010f0506010e040f0b180f0f09 72
    0x6244050750103a070088400b08104202a810f401c20380713000c224154070208100c04407944c0c82e031041082c060a00c9103c000707020300360401c1d4990300b05540da54819000c00362421035016081c01c9114803d803e40e80c0118002c24025001d010010b503245030103500c4003039103081c25000349030800c1c090b61510307400300072036080700303c0180b1550a2404050380d040017800001c8005009200c10800890140c2d24400c03040300951041c11101804e2480400040044802a05004200c14100c04000c2c0254029003a40d060b035005a0b91303174600780e2003c1d0040f4645a0100403c94000030f13030303240b030001c500d6942e0025001c001d00103003198407070349682d084c96800780700610030000001e200f9008220204030000c01026403042902e0709a0f02400b448803030701c0c1804408150400c0260303001a40a000040c00c0c0203540c09000c03a98810840303490442d0000c1c00100070103c2540c0b24035903c0600a0042941d41e104190407100540450104030070000c070038034900c20545166404805100000741000c4214071168450041640 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 539465989 1250 539464739 539464753
    0xe07050303032206060321050414150d1506020f0a0510150e092b0c03200f0d140313020409030903081603030506060f180301020918010e18 61
    0x2441d600821500300520f050000083c1c0460100d9443e000380005940611a145c500607555110640804a440c1002c1305010041c002003140714000c1500c002240360a5514080310006c00340008194402c80356007480883c946203002e403c1035251481300050700c0c410f40071113411400505443d695050010700c0148607600c496031281b4040c070b03290452b010350300c0030400030026143c40c2c0c0000894828115440c280c190702c03241d400442c0544031006840c000d11800302c4600e03d18600c00c401804440c403900e002e42031129186444002c550343d20324402c08081e18105440d0024004d021051f100d1040381391400c0001c84540c07101880039024000c80340145412503000b11040001c0d401d11015000094003034080c40b08210000003c1170303201c40100301206041002040003446841c02400f10b84000e00300500844080c461105203009200464000809108241040302c2c0301d480024064860b101105030045002e4200010141c20848040e040c1d80b41c50040ca00156281003451200821810854083d80d0110b8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 539467239 1250 539465989 539466001
    0x12070c050d020a050a09020a1202190c0c080a24020309060a230a0504170910270329130b0717090708011b050316020309090c09040e0705030303 63
    0x105041038a0344050841e40f80c035640c40d00020882803160348002c2400350009000c0c04038581c440303141741d10b20003108811401d000c020400130294450a0503c102400030201c0c4003002c0c880f107126584010240301c01111703089020380c6441840c40791207030700c400740b0b034003240a4400340c4150368003d507403007008090020034882d070358000f458024002801d414259038005503c0d00034115a0402030f41d1007082d005d2808280c1d42402e141400c40d081e0b0030344086640f01c00a100c1e40c00b8550328652041c01a003000c0c5444403815034101c0e038001141448695400b45007004010000800c207804120f452480c0c1100400380c00220000300450700030303d00301c5001d2170200382d40d04840c002030f80c1e05e00119042119032908110340110b81030400301091040e2040c0e842350b80441c40400c1459400d000d04451800a007100700140c850800c4041c1103130002600d171420b41e02403903616075041c2d407080041e1550644005c0c042c000d141040b1010400b00e40c00030580074001c50a1030344451034903400281c080f003101c1c00603000b9482c41d0748003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 539468489 1250 539467239 539467249
    0xa0f08060909061f030b130515011a090301110406020f0f0d02060117160906090b010e090a0c020a0b040c050411030621010b04020f040e01050a03110d0303020d0212010812070c05 78
    0x1580c2d03110130300e002000720101342d061742200d01c42c502c81018000c0450301d5060040c5420300c0a00310980c0c1d20034800043c0a400100d00740c1c00802000c8086403901c403d044000070340034200c004654081403c01140c0011a60390005001715403041c0d660942c1d100c108070441441d101c003020580310703015900401c01000300340782220084a5400e0700e1010b4800c0c5101030424140715440c3e590141d400c40b510b50b8828003102065124680c0c0152003420038901c141e00d441d0200d04104001481c488a441d43c88030100c12081c002d00028004651244c490001442c152034203100c12004c60160601a9280074000b09a441980701180d0044000400e25130034103e003401d4030b0002e20300490120020355250b030800c0590745c40703130700103400310310441c2c051030b40c03190b0514407029601c4005070300c2140301d40542081000031400d000f28612b050201925000900d11590070103074040c1c82502d41ca081141d100190750600904800c00d41810b0f62003420907214664040d51080c0b4407030151050150406d803600380308001c50300c0d01c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 539469739 1250 539468489 539468521
    0x302070e060a232e05032212020d030c0905130902030a210c02060d200a020601090f050402060a08130b0412030608011e05040228060f03090809040c0c080a0f0806090906 74
    0x4016144201400e0404008000d0301941c0c04403600c2c000719070401c0c1125014403c2b0018407049140c1080501d901d100002c00c003051602c0340783d01460f04604861081000c80e00f01c4842a030b0064125610303041c01d03250505a00303022524002401c0200c05080c04081c1c40b4081101d074142d0010045414200c504091200400d0405c078100c0c410a001010ba4020f07030b041d800540100250b90300a480b10b90315106d40031094401c5080c41800ba40c6c41d24081200603031700c040c2a150052414500305100ba03481c2c8004844a858500300540202c500c48100820030882a50f201241c150b01d0f5000e000659607038211702c3c269845c01b00c1407020034030041d1048807401d60540c00554800d0008050348075101c20380c98030240c001d0000e014200103075103034001400480c1e00503a094048407201c4c5810044103869444860090148141c03240c80703144c444030f00c402c10500c0b0344145041103401c40e101a94a480f9140007815100300d031000d9001090145c0c00180f10341c9048410700c0d21909038640070300301c0c3c0d0b0317568401000f00002c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 539470989 1250 539469739 539469751
    0x607021b090c160605070c0203010f060f170c1c1a0c0d0903022103070f0e0105040b0d0f0c05030a1104080a0303020901050c01150608130302070e060a232e0503 70
    0x110203c40240818102d00496000d182551902c2103620303036500606095400c0c0364001e08071039043c2002000303612007482d03816003140e0849044107408510b00c00c4550510042e07151507035001181907030007510049020281c580c003610400d00c3c8070038001e40a8458480d031400f211400c00d540005e1240e1b2902d0a8a50403800700d05100344142d0b6440700321000341030010090204059048940401004202504030501c0c0c08400c65908084c64481540310000341144100d000768410404085800844604207030041442201407007000c0c0255101c1000c02820744c5c004465425140d030418107032000350204101240c06031000c42d0f0103451403602c0d07038500350017039400054158100700c3d0030005000ca154080c4076155500c0014003000988500c2c02a00401c14000a0002d0006225807400c50300041d40000d100c3c01100d4107240761a1250ba42e80340011981060b0707a1101c1d4031484c0e011189855190100d4440b074940000701c3d0f008111803410b002901211102400950200c8007000d12042158082c0f0040c1d54400e03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 539472239 1250 539470989 539471017
    0x10f0c02041d06090f0303070c022209051603020a1202150706090218060904061a060a170109020c070603270305030403021507210e0304080607021b090c 67
    0x1280e0116007250401102d65070244064820410a48414000142c2090100e4020140b03226401e03515506e912010b800748003400180c4241034110744071411a00c80d1080c41d0304107001180341070100c0c4409420a1b8601b12990f0050360300d00451180d4801d41c0c2415640c0142003402b02c03e081285c2141e103072101450503a4070440090f02c42089091040007071401c584607180c04a02c4038850301c10701106e48982250071100c0c0a9040c104440c1c2d1712551840751303106400c054089802031f19000d094960041c074094a5401242c00a00c0030f0300d80303801503151641c010000b94a03508980e40d4407104400c83c003d4030032003e02900144410010741c0c3c402d2b04810903100f00c4820b0841c1c2013140f40b90711201071101003011030104002008010505405102c100e1203401e145240b1240c03480d02100041400040801500303e4600c001c3c83c912080348503501c04d80c9910012802c5965807a154403410740d4404089034000c005120700030112524140c001411140e40c44050060089034032400c10b80c200c150454a0301030124 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 539473489 1250 539472239 539472257
    0x10204080601030f0c060516060f1e1d0708030a11010e030a0e01030b040915090f0605090715090b1b03070209040b010f05121e10060803040f150c02010f 67
    0x2400740a954000c40c455120701c01840504d01d000c41108219a010105018040c0000c0c000521480741d00110190710400c00181a400090754000074540404140d6015014070440044070244c0e0344000c0e4850303030391580d41086106040c07001c0d90303660950190700b078950000c5c8130490f0840c1c01055401889a80340300049200e40c0402103051450b0099041e20000844403040f240255815109d00e0395481020b0750700303011600f001d4481035802d2035115803281c9011780e01d007441c0041c001117140f400d240542c051814031803400c140300c40c00d81d62000350040d002841062041d1010781d5026000c1c0c0c10031034003002c43c007600b0002080412180388000c07c20b0a00240401c103d11401603440101980c46280300d83e801c18040c0d4100515401c5000858000d45d0180c7c140e032206103070710000019040201c0000310000440840054862401c24000031800c0010a04081c80803c0031040403000d002601d1407450510041c1d0b035030307806188158104107180c0011070b402034000000f5501c90b002c80500010746041ca0140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 539474739 1250 539473489 539473499
    0x51914120c12091f0207380913020705060703061e060804030e030d02010f050a0c0207140a0509090a2f090a200712051201090b0d0c030317010819080c010204 69
    0x441c4c941025200058202c0b4005120003280f8421003843c240381c0007800100c0588100805180c05810ba44e42c00d194003012030600016a50940e550103168132402065444491524146a076181c050320f65401090a01002280242c417500030451206030a1780140e04403454280141d07001c000c00b40c010340c200084200c4000342914100024001003116a00015159100c044488101e801c0606020010317030400d00c01c1100d01e0381c00208002580e8540da5442e04100480c8000b861040c1c02d40c1c4015003203440d401c00c0008507140400e400018034080c568010b000d20403000030800c09090401040c01c1c58465401d180c0044c280004150341c4240800000603801203002c80081c000d04403840810702440000404508009044050f081107803000d00b001410001c084490040e4400d050184000107555a1120b811581c1c0c0c0341c80f11158150010b0040b07003000d840741001844c00241c0041c0c007003da4544400000ca101000817501402c5440006010540800d5690314a150b80700750342d181c41a640910000c20 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 539475989 1250 539474739 539474779
    0x11030a0819021908030a05010b03060a140d1e060b040510030303090302010b0310090203160b19092705330a080d1e0203090f0409051914120c1209 64
    0x50624064a00130741c49150480a0000b55041600300030000a02401031102a44444d1044005e6a04041c50b498002c3d00d4a0045840400c1d00030001d0318100d00c030034140a624070500c03c510790403800b5100901c0101c00f0704040c8020b4450507a1064119401402c041021030f12076400044c0c0c50348640b00114610924000003882c02151144020750a80c0d254044821451f080107880420840c00c442090254a050320124007409010b9007c03007000320040c0b6020782d01d403184500a001d001900c500c40005031a180400500705200c480e0140c001d0715280200301800e9412a94036510800010304071140711f0201809038040a140142c80c2d0401d02c03051001c50300341d10502c000a204242907480e14000e030803001e81011380b443c0b000f070001c095400402c81242070303460702d40400c41d4600060b600842c00c1c401c0b601c0d2680c40c114200100e0301500381008ca4a80c10021041c00c80c0360551202e0048901901c240c1004001c7d5100701504030b15a0b5215088002c00803004070040c0c03411010003080c0c0c042d03d46000c54030139 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 539477239 1250 539475989 539476033
    0x512060303070f0c1701050903090108070c0803010303030f2706020f0d140a0c0f02060426030f0610050c071a040e07020f010c0c020f010818011811030a081902 70
    0x4d5480482c01002c1c04603031072208003a51540358140c001c2c003847c10f150003000c4e100d20524499030304104800e80020007041c000c4140e06400c40d0f2100745945d6039039403810010000c02041d4504500b03182080844217480042060042580442d10300c566000501980c03004000e40c002c4080d40080c00341440000e1240c0104d00c1001c1d48841c0c595003003012450803410010840d8903a000d468248a0109500d6503c0c0d68002240c56003c3d50004d00400480d55107039040b4202170701211468500d4000004024400c0c0c0491011409202c040d6135145410a4009090740d1500501c8135040f41d40d03019400801010040540d105040d00313001014a250a48441c026a481e4404030340450259001c00380c3c4003001c0d4024401d0a2210046103451380d90444180d00140800361080b541a04218000d0041000c442aa8401440790b5846400030402d49000031039882224000580c00d50780d0142d079001d80807990a010883d0a0b846500055042c40c2c1607141201c01003081c003051481c000c6214541d0418400b0803d02140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 539478489 1250 539477239 539477243
    0x406030b13020304080706021c06030f030929160b09070f1203050f03061917060f010b032805010f080607090312110a020d08040312050a0512060303070f 67
    0x3103100120a0140324690241120031030000307104100304030100b074036a0103035200c0c40da02074405640c1d4072001080301a804241c0380011411454918000700b0000c0504c0340454580c4291141e1303500301d5542c0007068140150400f004803010540c1384105105403244000c0001d15007081654061600c540caa1602c0b1450845200c803040c0d000b0306c824030541c041494010b008005080d510027400c912550010b00600502101c440c5002c40813012a8942c3da03142c4440403818550703152900ea03d580c030340e40c000307450360181d003626800d000c1c00d0081380e8035450f10004241650b41d0030040714616118181c00d262000466481054250004814000702102c2d9009903402404071032440e0942c1b50821206c03504080300507081d41d080c440094810000a41902a4451380340c04a0402c0600101d403400381600f00070800c07000a40c03098508600c1b03010094136034003a05c1960f004094001c1c40c1240c001c002d5401d4807070b08803144046a0280080344d550302e4040300c01c3d90700000c05401d50341840140e55455141c16400803007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 539479739 1250 539478489 539478491
    0x31e030408010c051b0d14250503031617011202010221071406041109090a050f010507090e010e280903121506120506030f0312010f050916030c02070902040603 70
    0x11407107080b9031a280300c10010194046c00c03000e00c0500014044408040144c0144000400c00481042030702c52200145041210514003108242c03410310303241d40c17045804c2c950350704c0154001b045142c45140f0744d1480f54403044002c17019908011000d08004c0e80c0e84000c81c1140300341c250220001c00380000881c22a8801c60704151608050f140c040007044000c101c5840030b50180d020000407558145025004260903201c15610340c0700c0807030003030a04018400180c182d1145030711844600c40158000c0384a012107548034611984c403a141008015028804c0d100160040004501441c500840c0705000c40c4a5502c044040c03c0c80030000c009407a0300050582c0440c00c0b2501d40010240700d401000c1900c0701c005182a03995003071002c00f500c5100a1400c00c01c130699294001503540c3c4003081900032a081480c1201c0d124142d284401c03501c40c0c400d0007811407a442000001909040c040c078400d00075162515402d03100001c10300c0482c0208107211003007003140300381c90700041c04079103501c002c0c000b40c082664 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 539480989 1250 539479739 539479747
    0x6010602061b0a030e01150b04030c12050607050309030d09050a0506011a040605070602070c03150c02030405010507120c020a121a06030a0209070c06020d0e0c030606031e030408010c05 81
    0x600641016801461407200c500090b1405200030324150444007518968200080c1003504c0b0f0500b0750050481e16880d01c038100381888003092490b0540098000c4a10960544444a03168145000c200303510650051181d030103c3c010506140c020400b940c1d20841500c03c4905100c0071404a20079070305a11001c0e102904405840400c0c468107011039809049590750841030485294401c8130144a07503c114001c000c0042180010000d0940450b02d004c1e400c5140c02c411181c03a81070012402c0303030fa429140000c910b42400703085094004816070381201d0b0161201820040d0945a994903c0020b640102c00c100d0000501d00042e43c9044891014002c0102c415403246914548030010804644035811881d002400308915a0382c00545a0940b681c1503820030314076121004280d50402d42544000d102c10f001068403000101141d2054003144a003030f0899101a220340c0500d07449010581e00715405401040c0170540307841908200021480c0803e08881c90940e83d41002401c40e12074045500000d10001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 539482239 1250 539480989 539480999
    0x180c0c06010f05010f1d1c200a060e0a050609040e010c1e090f06050a050d050a36020616080d0b27070806060910080106350c090a06020601 61
    0x28020040704c050b00f410549500e6544107490307106c0701c200c01c0318840d064501c4240c105d405c821401e0f00300250301c2202c80c01c0341101603040300c14800007403c000307004a03043d54000408602c1740840d0700c240341d409001507000c2410001800101e0f8444c40c0c841e40c0154aa00990003004024460590308100545c0ca024480c2c0c522003000000d54001e01d006402c00803020b40500260341c162442c1c070100c8034107060a035a40c081c00d000a50b4035001d0b1000e181002c6190808003c0b60540380c0d0054900f01c40d49580c29071100d02c000b003552031007140d82032454034409003540b1101d0050401c2e9005210420090704400c0048030325603a01d00140d032080d00d5230980c0b81d469400a054505250360003d9108500070705c0c0300c040303181c00404401c4001c1c0042c05c400400000c4400304440d42c5a141c00c582c20207030064912018050f0202015188490a104400c0007414602400740c42d0258032140e580c0e1a12003406244c440701e0341007018552880b01600c10710034100100000d1000c0c1d41d4112284004214640180841d98504 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 539483489 1250 539482239 539482247
    0xf061c0507180c0806040e07030b0114210c1302041208040905060306040b131115181504091a04051f0504090c2309010929180c0c06010f0501 62
    0x2c000240b865080400c42480283c1124120798803d2040c2d070001480d0440407080341c40c2c081181e10103001c55400c140046054108080c1c84046564140c83c40c00a40d4003860041d410a100d0003035101c104e4010922100e014030f4511074203c1080c55564000d1b06194481c00c0d0b440481c001140c0855007400d00150410002403180510341c0d03c580c0480152141d40b0301074039001e01d54807001340403a040000764840321042040441c4442e5100d030740605110740c9100900340101c0b151b0310041c100c51440365811403e2210f4134100c1040088451064012420140703001030344030241904030142c0166501070840403103c3d44440c481c05203c1c0142201d030545540f94030f2854009840341e5089a40036500380000680842c02c005d00c5107040700e020f10310307048000710710390030080b120b200101040758407001c200000548140c2a1708490f5007146401e5402060541f0a040031051454501c40360390002110b140080c1c8143e80841515440ba01c0c91074411b01d84148102a5810540260845404928600c2d8148900c0d684 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 539484739 1250 539483489 539483519
    0x10903051b19151101060b0a0503040302061333020f281d1c14010c0c0210080c0415020303073e10060320010203120f061c0507 56
    0x6400503090b040303420403104410321500c0c24024030500140f450350940101c025804603004101d1282403544850203440700803d60760040c1c500368014882c01000c036101c0f00120030030700c1c00568042c2c44c00b00d03000d03601818900c0302740c14000340c0900246260804810b82d00c5a0004243c1c80c101c01c04060f80d10540c80304105c20901c006800c0d5161104086690314801c0d4004156110700300e803c2a80d0081d5080032000500021841c1d1440034509a45104040400404d94103101e501d403d0480280300c030b8450464120b902d048082c0700650311940c110000a05c1ca8051440e441d00308805500b032070320b4151201442800c7d440c1002c048001030340300008000409902c1801400e44104100c0580c00e80c85100d9140d46010349594504a001c10580d800002c5003002046210b216140c03c40013800700715924100010311040c4004030504204c034290082c00698800b00c2100c0c0f80b116444030080c3d994649c04000041c04100a05071500007002052114200c140d80188020b501d124400404c000e505140304c082d00006 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 539485989 1250 539484739 539484769
    0x10e0d05030d24091104083f071104151e060305162f0c0f1f0806150c0303060111011b0804061508070e1f03080702010903051b 56
    0x65825401d0110f120404110011030b4148040443c80c40c091400c4055548169401031031184542c0100790020a2646000744504074540c00070040e8a50024120764130407805c2042c044100c50820403080014031400160002c80000741000540d450661032819900c103036600244100c7e00c180c001c4a0361758003a00d4501000e05a5440c06101a0a040e0140c1c1c030344985000400c0d080c800c500e40c0e000340d202e185081401403c0840201c01400f10020141e40380c030b5400180000f4082c16080504110905014412100180800c0024410300310014000c44103064080d20a543c000d1403071103c41272000844000c2c0a6045045024513928109400058003c101e81d42c4074181c280d041c0307191044c0c10220a54429240303016030034207044a07a124640640104803080010b00c2803c5114008100a80700103175200c02c1c1c83c900d4800090383d03282d21075484041345050050701c4903900020002d100041a01000e4078005106040c043c10f000d442c1e81c0c0e05030408403019681600220900c2c2c0440b1b1500e400e00044222078 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 539487239 1250 539485989 539486021
    0x5071b181505150d11040f180504020901121103011104050906010905090a1a0301090c0303080a0e0303041202031207080702070506180108100b0307020606040e010203061e010e0d05030d 81
    0x140b500000c940024540a018040d48001041d07243c1d03c204250410505c902e55100c03901d9a80f0385880b02403407100d145004405000b1102c5c9601041d82c0c203d445403600854000301064842e07882c202074680080700c400c43c100c2d0340160703680c14801c580c6c60074081c080300c1c102d10306e5800d9191414007081c025030b10402040d00381040307881e042c20131194440c0110345402024a001c04a61800c030700307003801c1001c080151504c0c0c0561804200754184206d9003000c1c01035038031a0f03a854403a51038060884d020358801d814014110307002003011a00152008492201c1d4071046d005a13801c0480680f40451546000c9480b00045040e290800820582c14000d90001d0541101c820342008a00c801400000f5071042015040c08000c4001c10020800c00b090f010080080514482c1d0343d1030413002c02034450310141e54850186042c880c003100d0084042c02940c0c1703d10000380c068001c401465640914a6003505030385030610030f0701000303642903440d5038104e012170318018001590b440412060400407034001d02c506070054 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 539488489 1250 539487239 539487281
    0x20906010c03080708060f1801030b060109030c051c0b040c0e2d090312010803180d030c03080406110c07081b010801030308070917250501020c0105071b18 68
    0x25040b1610f2500260945007585841d640d0201040d901d0b940c0320605c95101250003410070211300c040c2051816640329003425015034a070b1500644040e1030b213010040ca4014507003c2408141483c1e00041c809a0b0790385030b03c01c070150040d143c2c0c1c880340005440c1070340c41540500c0c1c14003c0807114620107800426288035100c03074a0008581d450303954416030401c0303500c00b6418007140d00b0035000c1080c0c843c820100c010345901e0f075035550002c2e90b513a4400c005e07044804486444442d141e1400f40c10041d0481e40540321078500310890742e41121a002d004200301c4003190749800b84038103c860395020707110b2908410000e1502c5400c2c600030a191600500303592503010207131041c610032070340e10199490449078181424000e540f6103240550b2070700c441d40c000b50310340b0942d00502a0300d55400915081c1c034000c0410310503a2412000400e1444507094000c1c0750150b40142d5520b421544980c009109040c003075084650072406412400c40d0b98060756110800048445000c845039a44030701c1030001010980100c0004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 539489739 1250 539488489 539488493
    0xe03161416050a0e0402130c111b01050711150a030f0614180a0902060307030501051011030910090b03010602061b0304050a1112010606051309140a1107080403030c020906010c 77
    0x103842482c080c130216014184080350464480c10031070920800d00034000d0020a8072007000034060300c00340c10742d40240d10400d407001c0304903d80540e00811503a410b0355910303d40580d580358140030010309000c480c1c010300c2070f6503c03c05006c098405003180840c65903000c940302402e40a040c055a4440d00802e441344c418104014481d503e220210800c92115024007141d595540c4815000f003000500181d0000c0f400010040c0d80d0398945d000300c0c1039502c00c540120f44055503901c100c446401c001101082d5038000c0055a01c18a00f0442482080006261250b802600c403883c80050707030002e80c0005c015911a038188101c8880c5440380c2070828038000000c0d030031841c003500d40365030355030b91b0303603000385c05010b6584168005403140c3d8515040304513481f0003400030980c2c0350001081544440d0342c1d9030081d44000400b09011300d960140840c0b0304251000c622541d11501010002400001c10070f141d115008c01615000030705040207840158029102e100d45004030f40180707c80e1202c003d00780c80c100302030710300c030040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 539490989 1250 539489739 539489749
    0x1080705010e010909020f09040c020d0804170405040609020c19050705010507062405010305130203060f06221e05280b150d0605030c10030e0316141605 67
    0x800c5800034a050b001851100006841020745604410a11400060b1005128510b103000701b20300700080e5000c1040f0407901c14101e88400039100b008000550305400700b8081500c451290440c1c0340c01103d210b2910341c2c1c0700001001c80d05517910000d0b45580101d040d080b0002c1c2408640401c20031036600a200348440d9407815194680b50040300d050081c00725401c0107200310f56120030100350f025540e400ca403012000c8040c0681c0318600c00c00d400a414070000400001c07400301c581c50a5540a03008200680b10910b010310052002080301c2d4101031845d19528104200211001d4009054040014002128280c8100e494a0005042801ca040006201e101034050042f070a88450040360b22030310b1665510400302030000500e200b540840e4000048050640c218010422440151402c00c90280d50b001031644a0260b0351400c3e030310580d656400c10849029400032000f5803240c0083d41d1070960300c010200080c400003081580d030405101202070a041d81000b0300880010500c0510084c3e914042c0001c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 539492239 1250 539490989 539491003
    0x21209061b2221060b0a080a0f020f090709030b0702060705040b0d060e1f09110306010503100e0408040806100b0415020111070b060907030902030307081602031e01060605030108 78
    0x20310810318021191038080040d0b9403100a441c88440401d0110509448040105524002901c0c041d290690641e12460031101c0c95048030211000341c00c100d881030300d60b60807200300d00200f41d0300441603101e41c486568401465910a4600382c5035240024154284521a01c03002030280003550300450510094642007014cc408603020140d05aa8560600c80c41c0d8014201c0c662000c0a100090018008009507841c0580803800300708a240940f00d69522100040d00d101c10110020a4400c00110707015520030f030001c603030010104807601e1320300780e0381d0f0300c61020304d83c00712802e80f0707810008a0240274183c0c05204003604404a5950782e13248a0519242400703a100d0303841203609164641c030030610000d0007904016070005d082c030040c6403145180c3c1005920020205d07981845444603c0c0014020b41c043c0c8114401642c000d00110308050460b40c0d070340d8003039000e00c1c0d000b81942440303c0d0050040c0d40400180705039450500c41044174070b42e80f058050035940d040e0041d8040c400c080c4010700c40c103c0c000940c2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 539493489 1250 539492239 539492257
    0xf0a05060f041b0e03071d071b030201020d0b010809281e02010e030307110105030c2506050709081f020f04031a070504032001020c04021209061b 64
    0x501600c4140000e03120020103504203400c641412000700c080314514101ca4040e100395240c0030b01a03400c0740c04045d182c42c45e038010039000b9150004c455001700320280748260300003680e040c841004500c0c134010301e00070ba8440c10100c0c0141e4000230f24140f01d0000f40116500c091003820700d0440c90415200103916002001c140304928461112008401c500001a0004540d04900d0b040752011303c01507003d0441400391810b9002c6040807100d8840c3d410008101d41210b43c02c0b801444544c4110b000444060307001030000060500c0a000c12400210b01c14800410b650141c04004004202c91820300113403030b40104030a0920800d4507042007040c0d40070a581c1403007160303001480c00205038400c01d50024069490b41c1c0c40d4505c000f003070210802058031016000000361001c000340503500c02c1e404840c0d5101c0c501005000b010042400c1c540342007651105141c3c0c204c14015074480035064000f0034102c2c0c0140d1411424452580103003d0405400d04c1b01c660000b56002d0307444255840814a2140c80c4212546 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 539494739 1250 539493489 539493491
    0x705010b060421021306060207050315070503010b1c050a150801050603030706240807030c0906061b0f02041107140102040614030702070f12030e04090309090c0207030b09060103120201050f0a 84
    0x440411540c604101d05103101c03502408201d82c3e507d8040096039840c4501489000c1d128404c0b0b00c0c0040150100300522403c003d94a00d45943e003461922402600701d45c4140e010002c000c10500309840444c05030512860140342c001480d91580d603c5c0e606161500d43c89899070364504002d2240c3e80d00c000c4220342c075154005101040500b00c0198000103d2840214000b08820304000070039402404101d620407030b4041c11416050640790b0034008204c4240b40301c1c00300070411100207414410341c2c00324015503144c0529180b00044500d500403c0a603601d8030103406c1134010005069081200302800f2105000c1140000c60505007030401c0070f80284015036110305981c80c084000b54441d44200072040243c803901c50386995250780c5030354401140400017000c80c0410486510b0130f4040c1803612592017050b4241c0c5e03a98007404c1c50000c80e50001c10040041070210f00a042000c00821039401415000300102e90041ca01c561442c02c0c009423294281000300c04590400301400080c035400030700c2c07030340107290140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 539495989 1250 539494739 539494799
    0x151c0203060a0c1101020d051819032f010606020f1b09130623070e0306010b1e04080a1704030f081612020c010f110a06050c0702150705010b0604 64
    0xa013901c40c0b0b03800e100c0d4451076600000e41210042a2030300954000c0101c50f55581c030105000456a4889026440c0102424004240700e40401e03c2400020100881c2c0081445154071511000203200c1d500c5d0b810f111140e454070420000d95038104221140124100040d101410b0300c101b000e03500603002510b0601c11395200000c1000300040e010300004c202d510420401c282d00108220807101e2010f640c400460702600b40005031198001c9c40000301c0404010050406a828146030801c11341101002045820700f54400c65900080e202c018400b03070400c14024040e18180346401400084280b00c500c1138240709100400002e02e1028080d05040d5110190369210000074480340c60400c9801c0014090480460113401d04a40104000b8490343c02a03940d141e0300a0096400e9905601003070704031403a944100c080394089843c940c810ba80014010451624101c0903400003513800e0640d12100c00c1c103c000059000800c0000d10641c3c3c0404800d64249007010300e0000020743d00b00c030042c50104040b940355 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 539497239 1250 539495989 539496011
    0x1b05040e010504230a05041b05030c09090102041a032e03030c081e07050706020c0d030c060b190f06020d050a050a090f0f08060108062e0e151c0203060a 67
    0x20380b80c40405494410500310302e01e01754440700c1c0905001d440a540b2074544100f1030007041c1c1568803203010f48502030010b101e004250010701c61702c040d0007000041a55400d00000c42c80300045612403c2415609107c40c1d01d90804001d440756407990034284888030301c0c0c1441003a000f50301070505042103a80600708201c104041b4100240b0601c103941c8071740c2800e0411b42e19501d0700c87d44000505995070148040f1107655460300c0c0282e80e140c90b6008004d9024401c2d00307036580002e00c40ca07807110300e10744030b00c10220709504010702080c04404200b800852192032aa800d1110701c109550b0750300204014130092a49020500021300107120f1480841c0070030a0001c5c2d03040c0c0c418002d011350303c02030200184400655645203401d01c08010a4020b11515009003c00010f2041707000403a0360041e0a50046c9018003114140068214014841140e00e12074030394000040c0088090140c0d441419038110241d0345000c100304120b9000300458072002c0f00e882048003080940c5001650983c03081038250300003007412502c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 539498489 1250 539497239 539497271
    0x203061f0e0c0d0b0f0f1504090c02030c100b1026090d0912150203130519120507030909110f0f040302010228020607110d061b05040e010504 62
    0x340e007207484001001001d12190090100c0100511140c8040070480c4006030001c00c2600404215201c1d031120f40d00780320070138a142c8180d41c1c04030304444c2c1c0c2c112490f003591040707040240c0d03500c1811600560404100719100c140f091206454035003c5a00401a00d164000000c80403c00012a00c04002015504002d41e00100c00c2540b030710800c41880d901d941c50400b500c550744101c4441004000b6807001d03800150384120039000d0910031b074062800720815140700c01d007400a4000808aa0348041030b081d41e80e010a40510401040f1201826441c207040024100440c0100f07841303010307a041010410981001c00d91000401055584018001c5141182210740e1100c07801040784e1a820301c0b000040070b107444282d040c020400c0740e20030307000d1361400a000422000e414449115008160328202c0c01c1c1c070011705c1c211005110441c4105540d00c1d010110b0004a0410b02c40100106c429980c2d03a1038029100b0020703007002c000c200303561400c1850203040208071403810310180314040c000c5840d80139588103c06a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 539499739 1250 539498489 539498551
    0xb16020a080d02040503060906100b0c0606040902041e090b0c0a050306100306211a19021309060801050727050d050a02150a032a05090d0c090c110a020306 68
    0x1800c0710081d04246c4108ca40390349080d91111455aa1050002100140307181a00d1008002d80080c024940d5600244009003100c0c110480e4803650b1001c00040e000580984022840604940059400010b00d031410300200013a12013074001806204100d100c940c03100890b03a0068098070082c0b0b008050440030390150056800c02d602c018410100b00008034142d80300c0505840c065030040528201003011400c00751800c3c2c408144000c9180150040c12004d17400614628818818110b0203035035074501041201c041d50448a50b90b51660b050000890384040409024210601c000d29082c200f881c03100d0a25403d445424003c1c1c194500110a00c40107122092980360083c10042549503440100450b0b035000b00340520109152003001000c00c405100e0720580d003411036552107031140c2202401d8034507800c0f00c0d540741d5000320103440c0c130170020f204d01d98120020000c41d50041078604c0460809005a05030903082d4040f6071110043c040035031740c0011166006500d42505000074900e2003100051011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 539500989 1250 539499739 539499749
    0x4060e010605090a0c1b0809011808060709090c0f301107020a060203040803040b09031e011b080c040902030915091b220b01050c0105010e040b16020a080d0204 70
    0x3000c6070404c038104055402c800c5044001d035440080001400c0e92000300303040085000340a84900b80060000b550068215041001203542c0d0020fa80f03680b4003009180060494400380003030350035602040903000500a00c0b5116400d428420780d45c2c601c3c824001e00d007840f410962030718080c1075030703031882a482500050158211820303000d10049250802c480040c1d40074800481c05103044003400a2403d1020040d0340940d001c420103145002e20f0000c00340d00b2504a14507069041c000d007211350f020290020340d54240500ca4800115240c0100540612000c0c0501c0000c814041302c5402c1100b10441401210141c0f0b610743c03401a100d0301d0350b0710360310714011128400080e119818401d12112160000d01c82d2149040c016540e0911900c4100740b042d100d035009445050794019106034804120190040006010185001810254811201420b41e5403e078061001642c80505020500a8a10301c2c15402515500c0e5007104050010b0000c0d9108504c50019041c600042364000c4150529011900141 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 539502239 1250 539500989 539500999
    0xa060c03020c100b0a080609060403030f0633090308120702071a0d0606031a011119230106030203060112020409020a0303120c0206060f0d08130e01060e0405040b04060e010605 77
    0x124400e15150b0042500d007030245d10a07110410002903034440015400d03c259140310150610303840703c5d6800c1c0d01600075650301052039915020003140b501c2c80b02900d1108244600e0002c02015041151140c0060f1a02407450402c0540380c820300109240314100d440024491b079003d0240d03511a038080b07042800c50380040c45061040350210104c5181a405050b0408007850100072280e60781c01e094040b542e1400c01398190301041250b41503558041e20440b280b07091000c0684280d0304200d0400002c50801140440d0200328115440d00d072506a0440f40074004400c5008000e01360441c0c0020350748440511403c030120060103108411500e642c0c000d005600c1c0c1c003030500b10000341c032454003070003410040718420842c6140180010b4081d10000e0f489000e8074000d8440c00c80f00c045841448004180b4503c240e560800c2081a0780c0d00d5034803541c50714002c007040320142165506022005043c1c0c038040001c2ca1240381000240004200e141e5803e03500186c3c0100b000601c000e90f100021b01600265124540c44 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 539503489 1250 539502239 539502253
    0x1215121f0e0d0903110609210708010509030a02150906010b180a0603020c10051b160c090902030d170f04020f030a050309150301030b0103060b0a0e0403090e0106020f0a060c03020c 79
    0x10743d0002254002d407845071800000054403c01400201c0c003400d209940d0005a50303240640181e14a40380e01890340260003604c0c03c06499007d20b509495094070501d900d6030000401e000b6039a03051080d900d0400014804400310f06060340400d139141d0042c090503103100c000207120880482c3c11040104034a2002c1d0518841070341e5000003400942080e04855494000d000288840310600c5c4140c40c800c05444495103105484401000750541020104e94444590000f000300450f50596203440203010400c004101941c440c41030506014440c40740c1e0b13081c082d00789804580b1034050140554044040302a00d1002e90f00d40c0002400e4403680c2e0301c0941c0502400e0300c20301c180b14001c1b0042c138010000b034880344202810b0104c1d106281c4001d00c800340051002400500c0090f007690048010084000c040780440f54a98070072114596041d541140840d80e07841d000c00404001440141c010301650014000103021040c40544614070200b005290550754421280d08601a0f070544a0020fa148115040d03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 539504739 1250 539503489 539503513
    0xc03030604180b01260d020a060506010903141c1d102715050412020f0406031b060807050301210606080f07030c0b030712020706060b1215121f0e 64
    0x45101d20348801d035140c10030380e0345c202d880200010040384241c880c1e0b001340003049164450300000c00000c0c4c415810811000300001c0440c1032001c501c2000a515030141074184120074800301c0f011200c0003a0742c00d2000d48111380003002c0722600e0100101c141580d4501540c181000d00315010f0301040105041d400011103d4001848400844800d0328605040610402c0c0d841c1f905440b240140e10410f00112040c110321001410030149201c040030014001041c09900d80d40d9803005940c5540000c18860740b501020860b59034813061013a040546420000d281d07504040752040440f4035121104511240b00d00b04ca002c0200c00c2d4001e400400c9248103442c50b480040c40080e45a010910050711000081000400d500c030305034040b240103890a4461140c040d0f541440d40029410058041d0b40c2c243e561040003c1074481c010050101702240a0301082c81c3c5004581c030a00294019a107a000d8002014420083c040000d480c00c00c481260a0489880007041d12000152416130350b480c0300303405074018241b6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 539505989 1250 539504739 539504759
    0xa03080d020d09110a063912180608011503090516091410140114130906090f09081c0e1209011715060f13060e0f04020c03030604180b01 60
    0x80f181340308031203583c00d203540d61034100c0d0402c0f090401c0800300303c0000720102600520115405a071120b51400c4c0c1a0480300b91241503128801c01704613000300d00704c04020102c010b0202d0349100a4941ea0508003540d505080c110200400058081c40074190ba540024051110401120340754607040080802031503200d0811001618034200c0e0302d004030018a002c601c040b0f040c4041c5105031a900d45500e4254450040110b4403154540295001428101710001d080c080d0380000c0c0c0090704040e000420300d20710f4a101c8404589000498541080c540310000d40015010703821210030305109500303075000040c001a00b80040048003512035441c480c050064081e050b03900c4c090079041c80242ca82200c58501807189000e281400c4a9820004160500c3c40d2801d00d0214041d0010400441c809418a0790300844e11000702c6690b041040840c13020856110b0b94607144442c840c4010090b103040d0b041c10850711606540b0700000e00780e28460354445040e075050f00d8159112072041604011003004d80e52750f82d00610 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 539507239 1250 539505989 539506013
    0x1802031e01140f0d050a0f210e0a05040903020a0809060c010609051501020a0c0b070f060c09180204030f060b0319120207051f0c080c0106030c050405090c0a03080d020d09 75
    0x141c060040c844809443e40b60411414610a810038040c1203010595a80d25946803010301c0100c42ca1442d000c01079085201c12170030382e065455a0384801c1000b00702e0340200031081c01a0703480148920709003210b400000785e0200da040750301a0721015040c0c613841420b0000c0c0050040c0e07014042958030b851400610703090746401080c01080c90790010304c52421410012a103510b1802405442e640380442c040203600307803920042c20180d0207104105541e0007250750740c4007aa40e200d02d82500040c4401fa00388900031491400c60303040910b441003189086e1942da507a044507480d8210242851399284c81120706500d041c0910180a1a6407085a846101c1441c0c10b41d0861f4402c0344a2005110b11203005c2164103040c40121040c171113080140b40c000352004821079540031041422100e156050200071030000c000d001d050091031207804c400019074103180610045400040c8242e1075580003149140c016100c04072100c040d80c0d001003980343d85520204201c0040d20510800c25070240c0ba041d00d113014000002286 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 539508489 1250 539507239 539507279
    0xd0e070302040c080c040e070e100c1104020301081b0604050303040312080c0f19020c04180302010e070b09010c080f1206032a0d030201090803100305161802031e01 72
    0x40110300c03c3c401d012112000100c1e525041990100401d0208421656130b060717000403140b1300b00700700040c0d40010802e4004d0707203c040408103140c0c215070000c102241503d2041200b06175011400d5600d01a406641c43c11170703c242200c040801c2036500503e1b19110211006403001804032a5516070340c1c40e1200e00c440235480104001124500810380307074180c4c10200d60350a598040700e9418807800814204110b01c480241c04e05511410801d04650344a078000c0c0300b0052a4811503a42e494914103003e030a450321b2594595154100303801c24489500684283e8860545c2171800400c100d040f8a0012030701d100e89842030145990215626900d9071660701032a00c5104141c0544e60320707241f03021500d40174000d80c0c841d01072080046080106d903800d245400146550091002107288412a1140410b030740c0309551014405013030501c14400c3c07010400210b158007048945000c4403620f403802419592081a41c860341b2550000701003414244d40030761461407160940b403081415651500111458031030f282d12 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 539509739 1250 539508489 539508491
    0x120d17070f090605030c271005040e04110a09020c07141012050a0f05010e040209070906021f060b0d0608070602070308041415030c0703020c330d0e07030204 69
    0x34a44900ca90300999a450003900e510119504040041d90b154000074a580c0100c0c80070302180300d40341801c519041c8201c020795134040302c2c18090400d001c406041460f02106100040000f00700340300d08004034940c019000005044200c048100003140c8a0196004154860003c91080c000010100301e1800700c803048031541d40350051680600141c501e4001011020801301102e103644003620fa00b101b85c1c084017030076002030351801c103021580c1210300c00e8005009c07548081c000c020450134a1100303242c22034118100302582c2481e14800a42c2c03900c0340c40b040d5648402801a102e0040b440350068406441180585612541c00030b402c1c2c4c008241d288104201c900c80e0500c0001c0d15800400d800c401d503030b00543d0071440c1c1030910341e2031001101c1040896800079401100c3c40020440c01c0069401032012855032903440410f410001e141020300c0ca00c4510482c11000c2c0205070040b03a51002c0c2ca050a01400070141c45086141c2d041a80a11446082164240b80d2403000403603010440c03c044d00c1c03003120 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 539510989 1250 539509739 539509741
    0x1202070501090510120b040615030510090b0604090c020a02090c0c06151005070507051809150f06010804060b030f0f070e04020d0201120b0619021c0801090b120d17 72
    0x41000701400c1d09003e41300220b0883c8503d4100380007107400c40207001e0400b41c40424816964001540a45d1004400c1000a680c2e44203101103c440c0e040d15200405d0084801c1c448600c49800044041c40303944030350f150301a5101400da604900910003440b880e900240f8248051501d601106200d9001c0c21411809008510008400e2100040c19192001003d00543d000c0c19a026041c1c560703500c540703820b890038422020001a61b64880851044803800d410142c415801c10042d80c51500c1c0307034041c48140c1e103685102003216040800010540c490000d10740010140c0342c50508074024031440e00000e401d4040d05111490600c030004020a030741c800001283d250560f2246031103000c1e0015500250b02403d03882c0d902c000b66104074400001031178030040c00503040002ca400188103900c0030789580054040e00790404151034050001440209010541026021120f400280b05400c14000c1e4080c03142e40b100c00c5101c58a82011042c150500300040b981001e03051080a017008000c03680b001030030300d0b03110 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 539512239 1250 539510989 539510999
    0xc05030706031b080103051b280602240a180506010303260115031e02030907171b0402181503040b011d010303140c0a0308040203071211040506010309120207050109 72
    0x140d0740034101c0747c1004c003a2003840640340300e084410007a1598607501182d8401050401d224010160051a000c0c030107400c2034030300d0040302a013000c0c41c10343c03032854049050038078030880b400d0080c03803503441b0403a184001781e0314600301c20384060010400b1018020707116900002c020160001015002d0982003081404e01c2d00b1003600404040700240620825010503c4118880714000e4100103298044070002000810360720740c1d04001c98004503101c404d02c1d4049001000345818400842d07000126540140c005da602d01c0301803140c00310110400364019540000d9075461071b0ba01c01407502c0d80e020002e00069000c5400150710300e4581007034805417a80031104000041c80100c041d0b10412540030123514035440da21f10f0300d0540c0c44072040313013050084200420040c06030040c00c0c019070035038601c00d84071440a400c1c01d00600d403620b2055000018455110007400b4049080c042541304060811a004035a5583e21001200941000f1100811150f69020724146164020500758140c0e5000c2c1c0c1c80f05041540c030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 539513489 1250 539512239 539512247
    0xa09030c080102180418140d0f03050606092e1205060102070503120c070b03070305070e090c04030206030c0d1104090c0c1509050a0b0702031b12030708040c05030706031b 75
    0x2000580b46004d2007402980c4841c18150080c41e2000c2103004107040b900c0c450b4a4030540307c80545003090040d007100e980c0712441d94002160b50071190030743c54100494901040410780520501203504c0c851458910f83c01a050703504034020301403128101044442108150014026105011172200740904003c00a04103510015000045600040080a00449002c203103683d03030303208060014950041c0742011034201e1001000310b001e102d159900081500e40801c0003031000e0200d2840b648240d145906002800071040d040e81c1c152501201c190b680e83d1590144941503125a409901950b82402c0f0701e51843d0702c1c450080d2049654600c01800407620f4540e0443d03040c001100000d1020821428008105000f40c1c03000c0d00e010b120f1030444c0c200b040c1940700c03c03082a82c1100e0010041e40006240718040c110805200100c05442c802081c0190081820020b00d020081c16230080000d003000082c20312840c1c401180c020b00015003030b241032a071074a200030094400b0a11102e61200f440c40008a40c80c85 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 539514739 1250 539513489 539513497
    0x31303020f09040f170724050f0108030a031d070f030201080901050c0f070f06050f0105100504050a0b0307021009060b0f240c0a0506090c0f0315070c0807080a09030c080102 76
    0x1100540c02c10f070400c50380d143d000c3d51030b0641600ca140e41d8107106120004007c070400d5803402140c0460001c0c440c1d1050b40c01c0e001d0350802841241a81000d500400070b0f41000400c3d94417110950402040030722aa05075070380311380c1428040d00c01c0c5100713010740002e03482c0607070704d081c020b4a000f80d03106140781daa5810481e00740e43c401d69030808000c608111191185d50254098452117129a46c3d51200200300d84464050f41c1040e101160340d054514010030641c6071841c00305450b00a00d05282e81064580070002d901e55045200c0c0d0500352000000052013039100b8000c0850700c80b8200d004200c8aa1a07040100041c121105d81501030300d100402e100d1640361400c44242c0000403d4068034000440003082c509070f42059903511440e00c80d45441d003002480c24014144142013450040c035240403000100a080850101404d009400c180b04603400054108082c40e4002100e09007154039000925018200d8491000c01170100c90f400b01c0c40c10311540d444082401100c1c0503a2a002519441d0700e0060b00f01d00c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 539515989 1250 539514739 539514743
    0x9030a020304030f031e0305251b020a0302030f030304030207050a051309054806120402150c03030a061a18060d1b030507050304020f0906040e031303020f0904 70
    0x8030911040000901d040f01413a205482072920000c0400040b840c0400d0349006041400400c0d01c6108011800c027011141030380c03d100c0f12180c3c050020010501401e406a0400d00500011444c165081551070b41c0c0c02d6800110390150403220702c1d52503d00015100d410994046005001e10707840080c151900800082c140c400c000c1c45400c00c000d010020400401d0007940c111a2070182031120f0386e420402d6400c40b441e8040c4000241d6000548626201058071ba0380b2850000300e141c1140d28030300d6140c00d820b9440e030015845060005032038034000105c0341c4110310500e5001800025181920a00c044059030140454800500c03485841c3c40400e45c10b40b590072130208183d1002e201d18000b8184404e6040001c690280038140b0b04140c117015402602d400b40c2a680500c83d945c8505807420341e1501c200d6901ca80f17140741c240e0650801da400100d850722003804084c441d40040d0302280071071340c8030b6120444c3c00b03543d2000c803982c460845200311041003052209038032400000b80d0881c0c0b00e05050846501c40c036 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 539517239 1250 539515989 539515993
    0x3030b0a150c030e10020c0f04050c07020d08041206020c0d3002070c090606200a110316140a0909050606010810080105040c0f2102012001060e010e09030a02 69
    0x90740322031040b01e1030b5006440c150f040010782c003181c00e000d495000265180d08a01ea000e010501e03c0d88080c4100b1142078509140903a286c50100b01c52100c0709070984208541c101c0311414500070310300308013116010f02d8000500e18180c0c000c3d84020440b0640c01004408058000d456014030100e40958044000600c0f60101e00d40d040c400f40b000324007040580e030100c00103140041c06d040f1540c80f0f4001e11000e6030007408049584102c01d110258003c00700d1118403ea00840100013601404515110254124000c0c080c801d0389031000c80c0c039034040c012401040c1d1455a4140307015601d41921520005845155010703524039100440c8840d0540943c0c0f8a990300a0010705c1070341c8480e00111011140103100000380c06050b070300411100c00c2801840d00450103015900c01e01400c18420504048942e030003514481c11600441c1d0104110401e028131068090800e10100d02417145c1d0103640c40d02c1005c07001c0e020b510b001c20229505002c4000b481c10fa4011840b02c03111030392105d00603540ca120321401e5030003513 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 539518489 1250 539517239 539517269
    0x27021206040b01090b0c0604050f0613030807030605061804320402010504050303070c0905071d010e27040b09061b030c120702011a0102031603110f120703030b0a 71
    0x10305150b082422200410300d040e2401c01d03502c2e28080c01c9034105480c405502d4001e0800c2c00240541008201c0511403110090f1005080031072803000c440a00d440014140a19040044c081038040e51140000f480c001d00007540d0340182010701d0414040e000c0c03546201d41c4ca840e00214030558130248680d54808034020010707441d1814128030149a4000300201d041180801011501741c034144040c16841d071141c65a40c40d070a0400c41248150348c0c00a021808101c1410507043d89480d08143c12a0071440030f0800468009117400881c40240181074001c400d1032051004075041070020960610441c0101849040303915442e50700c684402007a0741e0760145244507601030281110030001140c0000183c0070191411403c03048c42000f4980440700c480241c1d648881c0d440200340300f00ca10500183c401d102840c03400c44210003501c40320003528805020841b04000c2051a00b0003000a002d0400317032507080310b64840f440c251040381036006540880010b42000b4082c5510705010500000b039407400801140c2e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 539519739 1250 539518489 539518501
    0x50f06010b1e160f0b01090606022e09020301021c05011a07121101090f021908030d0207140a050d11070302010804080705161e1d0412090b04270212 65
    0x9400004081c0000c20a03c1101c0e00003038800c2c1031200074a031044c4500c0c01d0f150324150424007114041d034000300564206540b00c1d8600c00e80200380100b095260b080c0b04200c0c000540059004140c00c0d40e000f07405610001d200005d100740104450445d02c030000051105030389400340d40c0a9003510400316110380303074180f0400c8001002c2c140c0321103980c200d40c902a114a114540d100e82511501c03036050302c4207103912007000c0940c1050080076102e0071360722034541d400314900005155288900021702c411181d001c102c6e039080006031090718044143c210200c420001c3c040c24001d031581441c1c0c0504002c203001c045800105140800c082e000c0b00e805844030403050f540e0392180c2185900c0300e90304075000c2c0140c0030380c1c640c80d000907130f44140517110b5402d405842240c910410360030340c41c0d145c004854481c0b041c2c0003111402e610301551540302d42c1c0031020304000010103100380c0d8a0341040d00040b4400d10003003008103610341140c103d10807040442c606900e0b216421a0f09004a10a00c4610a4200d44030000240 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 539520989 1250 539519739 539519797
    0x80715090812070f0c0b04031109060d02091503070801020c011b05070f03121406031002070b18070b0a05091c23030d0e01051609050907030c02010f0603050f06010b 72
    0x102540201c0600c2e254041654a10300c014840c0c1c6c110101480000c1418002d0110760403072804201000d0b05c6004003410020001006504c214400034412071440c80060240140200034400c0e034040942120f4245844041c014044d401c0154068615072a05c1c514084d003002c21100b603d0810703201c0d02c610f0725050060702c546a0110003c14180c042c404220149021346148d03128100b0118284000b900550901380c1c00c00d41041c1510301d000300c00c0c500510852001c94080480c0c01d411002240c0e103910f403640300c000c0c440d08003005940070742d00301c0c08082220118650420001c008410084658100c1c01e41034219104c1400040030000c2d040b03048055900d0b05c1d411404040e55969501001240c0c108256402e0300c1c001c0d11482140f04d00d246c5d4503103040c06202003c1000d805c030a040c1c0f038208444003a04040102c0c482040042c2032400301500c445103404803a000b0740c481c0d802180c4440e030611069450341000c907506c2200031001d840c40e00c01c00000150400c1d144099644102008209000301440510481 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 539522239 1250 539520989 539520997
    0x303070801031509020a080307050607030605030304180f05041202071e060c0609150c110105070c0b100e60030303041b0f060c020907030b030601080715090812 70
    0x46030f8556a40307200c409a03a420500000404094004650b00c4290707103800c50509074003514400030703d414000f0600041d80c0100645080d103200d4070a803009680c580f04071102801400382490903861820080c0420b0201030900002041c6540e001c44100d56510b0140031882e103941c6c0b141e042800601c2405208842c4542c890007122401044081400255601e5895407400e1101e05941e04581c0d40303008500c01e0b80c104c141704049070f100400800c82490f0152016110304c1880c00c00511300041c040001e80ba43d040d00409401524a01409526500d80303480c10761780e4080c0003100d00420510075068080c001060313886403181c4440c2020000c0c140403008080e10040c04158800d1b02c0405c000065548145e1000c10207184214040d43d2580e0305503c0d002d200b410181441d412003440c1d00c44850042c083c882d0004c0d0b00c404010341c15140e12401da44c44200850045c40c0a24607240c3c14010700c0700000c0d4403100091542c00384c0f081c29070441c80d15403604000b40d90040440c4205c6150340c1008400d0f00e04541418060 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 539523489 1250 539522239 539522273
    0x20f0d080a0c27140103022706070b310c0b16170d060b07050a02211c020c0103090b160e030607051c0204140d05030f070602090f03030307080103 64
    0x41410001c1c003501c14210340400f520805401d020110802c401c2d403002040c6841d401c003e09045240c000d060000003080004503007a10806411240314151035112030045600e40c0d07400400c11001c03400d01100c100c3c111202812082c0f0b264884082e0701300484901d401c0b0b1402c061b03221a60480e5285043c2c640110381d0000b4a10b040090414444140440d20920b1034070030900c04910800c2c0d65011381e00c61038007258126044076104940078041540014000034440003400c0e0100c1c0c601100a1245500d54200403090f61141518003d6228040480d40100c14030941d0200390f03020307503001d50640801102250101000503210183c0640450540f07881e0110a01c042e0700f0070f01d003800c400021100441c0c941201a524200001e4000980c4005241c2c006400e074820b13001c1d80000d5191910702962202c2e8550104905071090301c1000032401080b07c100100d5601a08001d11103442d040705052a1000f508008007030741c010b140000e5a22250325021048920908168444581c01d900350748031046218148812 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 539524739 1250 539523489 539523497
    0x180601020f010c111c080a09020d06060303030902010e150901050d0b0301091a090d0c02060a090e1509060402040302330301030602180a0b0901140f0316020f0d080a0c 73
    0x280011000e014145041e1a0f82c1c8440082c0011655041d250000740307800380140e50031207620b01000607407104070aa00021440c6012482038010700015480208684000b0119032901000000301034264020000c3d00d4001d0300c07690328a440e050240b21449886100081c40c113101041801043d42c0504040c01499000c01d900060201000c0702113402c58801c0d2905459503907402800b0034490781c07120f40380c0b0346c801c032404060204801400400f601c90101548002c0c0300c0d5902207140b2150b980b00300100e600800c80c5042e046006d007000c1d00c14440c8a0340101d9058000e922010008045007400d000701c80407a907001d004803402c045607569a6036000f001c041520b13140e80701d0100414081c0c0391a40554040c40c0603040050b507400c0503079a0064050007064008c0c0c041e08041d01c2c204a4941070006551001301c0a08020012004c3c10140ea02948504503281c81000e401109102041c82c50f2010921825410340031035004c2a51140b90580c0e501e445c5159030009054075002654602d00c5070042e0308002c10a00b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 539525989 1250 539524739 539524753
    0x30c0d0309090603061d030a020d110102070c06121401050906040509070801020315090604050f190e03030a0f0b030721140a030c061a13180203030409090201031a18060102 75
    0x2c01c00540d12982e100369946916900b40020a084401c10414071171138610066242484040001c0c1d140d01d011000390f0280718072455a810511402e4041303c03c42035210301042c1003541c403241c0150070340c1d2404e5140c0c4070b41460001803224201c0c181031070328140c410081c0340900940e151003c1001901000f080c6a00f18003e111001035640003d001450007070850206000d50043d5090078000290710090034035100c0c90900c0d051002588150310443e0300064542080c00148200340d2448002e40150304240015120000030041c1c211800e60261b00301801c0c100b020302003808a001010b80d510428011030b10051300e100072000174041712028188030b1611500103010300006a84040d402c0501080b0194080340e0810f402000300050361054041050f6100e500e03440007039110020900e0458503810401003e540c80c83d87e82464080b40ea407044c030303d80e40202144d98558460003140082d00e403580c0304a0220f41071034000c200508030303014441d2034504054800c01d10340c0c6022507400c0d64200c028001034198040d0308 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 539527239 1250 539525989 539525999
    0x307031202030405091003152f22060917010902101e2c0f0904120801050a0501140703090b0429070c0e0415021b010f0902030c0d0309 59
    0x5800030112140c0c40d0040d43e191840c0806104298030018015004100518424000500385202c0742c1030f18904000c0000d4405203010700020f0a2201030b01030014090f0b01d0301819070000401000708000c03c3c800c950000c00200100039517861401600600d4086041c901041c0500300c0320000c1c00003107051746400820039410326000310710f542e2482e0f03a5040000c1e034115000c2c03032071203840c0179800c404240600e401d034818002088900011152040c0002185500c1c950071141592000007e20580300e0040c0050310604003440c1c060f030403040b2003100324081051040001641e123802c0c0c2c0c3e0f030350480c2c0f81a11514101071307021400158079401b036201201441554100030816441c04000380c005400d82040c103189441c0740c8040208605020720035056030000821080740050800800f40c41125403600f9011003540b59850685c8403100000040c0394900d20100d03035078003125004425000096400340080004180f41c00b500c4040d17405020300a501071b800015040190b00780040c04035840350182c600001000d0700c030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 539528489 1250 539527239 539527253
    0x3060902040b090f011d0d02040b040609050405061312030e030d05040507050427110d12030f0b01080f0730060302030111180405060409021c050616051206030703 71
    0x65080707920604004508800d084c244510740204c0d0b01004d0a040c0881420721004902da42d01000345070703015074031480e43d035411501c0329001038180301002401480025110030510000381030464054800340b26500100f080c071607070580c0b9414000d802091258801a030118150701400c0c0d280b03c600510b11041103140305941041c483c13103020390701c6100a031003490300d420100001d480100e0b808844070810409990100f40703400074001442903004949020404e40c2200184604c0a4018042c0582c000c2e075143e0300201d64158040d180f19048203004005c00d0a250004580368041250301c0074107a101400816559801998181e48081b5607400300c1c604220b44840c10000c204080b0040007015031520418421841d0a004050650301501c108a04241c0c2406000e05a1030601460b240650341d200c000c40e4043e12950441054284c000d4542030707000e00c00124a022501d072403201640c072b500a01d00840c0c0b0003100e07003084244266580e5220350030300c911012901060700015003016030500c540603000001402c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 539529739 1250 539528489 539528497
    0x3040b18180610050a0c0f02010201060308070f020a060503040308060123040815060409120e01020109060e0d080601050309250f0b130603110315040b0915010e0f030a0f0303060902 79
    0x51803401d48142e051031418450702d600d245820406101c0140040e20080798415202280d1a4101c8080841c00b800703400180d005045a40014000a41c002182010b00402a802842c1c5600c280e8040c03601e10750700d04003200c1a0109a0f80100000c0103140810869032103001c1d0500110108850a02000c0f10194820104d42c131580c0481c07202d4200011204c0042e4901841c1c0c1d600c0b440a5505005918190341c440324140040b8207540c0a0001e00c1c1c2c0d074005582d100f5840000d2080d80000c041002480d006241c654602010504a000500b081c000840c035511a0341070304d005090950041c100f102601c05446209030b511000d840c8943c14022000071448040c8020a00411164040c0c0d41e96000b0411500c1c40100b071a0401003c2c9030030000070103280585075003107a521800c103822441c003904a1000240207804258603260348980c12605100c0210340f0b101d070301d010400007625071900d06036000702030100e84007004440603803603003210303400e00c0200740208411401144030749030014545440d10004422071300 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 539530989 1250 539529739 539529769
    0x706090c09020a120b12120c0102040b030c0702030c041104211223030108070303050a1806032f030103032d0201050403090e090606130209030f01020a090f0803040b18 73
    0x140a081455115200351107141700d00351844030515104006440e502c400800c94070840b1a000a80d40c1107104082d0b068038003418800e5040c981c3c3e07060000009403550017041c002d922a0040c00090551407400b407282108480d1903038062400e1502c4d10f40c0da0560301c0440f140e4290f80080545564000a2100c1a07100c01481561100e41c401900c0d41013141c210703c007804002c00e440340c1c1000184819100012210300301da0381031502d02d42e034216415003105c11043c207142020131110320a80202e103054140d000f0301c481543c41900c0c00d5200500c542001c0003e462a01105184d110404c01440420310072110350b2074000358034111809003042c01c24100c0060105600130300044c0d644c0d00074031003052782c00354464009281c85c51030800d00d8240130402a80703076080a002c15204062092041c859901c0b81d4055034004c450040950f030801c0140030165000c2e61103c9002c42c00190181004151408031000c507105407201d25008500b810f0400c401812164029600000f4080c0c10713468071000c550780ca084000c4404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 539532239 1250 539530989 539530997
    0x180806040b011706090a081308060703050403120605010c02061806041706070509090a0e0f010204030b150301061212120e010b0907090815041506060c170901050706090c09020a 77
    0xd071419640c07550070054441800070f50b401c08400d20400000015241d4615034120215a56402d00089038a4045510b07510041050096200b000011901940414401d0340079840302c00e909a526058a011180316014250100d54050705030360141c20710710050301c080c61602003000c1031104800300242140d0066440054580140c21022801200902407550011400c1c10600c5c02c011990300040d0126a00501048149030354104412a12604100d5038541c0383c5014021581d440c0c07a0f0402e00c6d02028121049202d08841c41a038442e1410148540004c03620086031142030624641e849405031b20700303440c42c00100000c50300380e220120303060302c13620410404100001850b291041d09204001000400c44003e12881c594100410000800d510b9000e0038041c14145040d41c90b40380070007807031038031101541d41c051528001003815134101d075030710001074045d40307141207000d415030034130318051059000813400540c003481084000341307182d004054090304c901e61107800951922200c1041340c00c0074203010002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 539533489 1250 539532239 539532241
    0x804031101020102030c1c0b1e0102070e13031b0519030813210c05061006111c0f03140702060a060e0c0f07020627041103100303180806040b 62
    0x800c60200e00d0040c04000c0c0000d40c114540300807440c001340580142c940340c024900744d04c07a134925030079880340b08414001452002003450030810040b151112002d8070b400340c40b44c0c10011403800e03d41c03003020344116540302103a03040502d550740c1140c076102607601c02c4c0794840106043c8400108280000703106c180c807184e580d140503580350800070308100303001c2c0602e42020440b1800f0008500d904540daa00512806684605458510703400c441ea0824080060510b000d804184501d03204584601005c45d98035a4510003d4410034142c2a16201c03403040c43d480c0700040702e01c0700d1030690151420000f041d40300d05001541944448140680303003011290300300182c2190080220f90011449841c1c081d01400219503510305d09001c12140031310408540c550450404203400045503a14821500442214654494980c621145884084080b003520a00c52800c002030125040c2c80002503c1c0300320081d6403910444c9103035031400e60300c0020304240241980510030010480000803c440c03400f89214841405e09 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 539534739 1250 539533489 539533493
    0x3070806041104020a0216090c1b0f14030904020f0304050624041e020c16060f0203031f1211100806010c030e21210705071710090b100e010506070605150904080403 72
    0x41041c40020703405007084525a450040b4968bc8003040040340d0003070320018014940c40d1098698051040309a91042c00020100900c0c0c4100c405940124802c0040745c0080d100c0e40358605200200302c0c1070704241080d810300c1920702c0c0b6042e0040c465200b908000c0150046160444000740d07800a003110380958003d00280c5480f5004089200c010400c03498548200301404000948902c00540350201064110215103c5034607620423040007001102d20f5121442c2d000d103000340e83c00106804561185411038200b401640c002c10400f0300c0b6987c141d48100006400d17503020f40303e408840160705e0b082003034040805e40780c24540700c406804c8100b03c802031018103510403ea0201d45c41030b20018490003414812000000c1e400100a019074101c00f030400d404984c0c0041062804070201c41040c40b003400c01d03c1040500050001c0319000d0f0440140d8004015280c52051807900020700c07403d50888020004a40403600a500c0f032a00034210032050000030300c2d10000076084484c251000d48500d4400242042 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 539535989 1250 539534739 539534747
    0x7030c12090501050f0c01020906070c030b0c070c05060a030b0a090603110a2412110304061401080d0e06130303110f0106060504150c020d08030603070806041104020a0216090c 77
    0x140c0c20805190007a0710794280000203000e07021742c40405101000210b420721000d80d0079010744030003500141040b500caa00604141b0070303179080d5120030396540500201140c0d210803510210354455421102c1001c1c40c0b841e0100b402080d41c4007031010342c101a40e07200030003c103542d40140d4000500c1640400700f4070074114101744010581011740a40f040840c0c40c420001070416a0043c00a0507074540d2803401200c64420a40d80903036212001e0440516010407950518801c0d0007450113540204c008200c01c41c0c0042c1c0d8442c0b924028007400c0080c4d8866002c1d680b82510880c2d0800303880c400500b4642c03c0020804554000d020140c0040700070402e130507000e00b13004008000c1611512040802807086626103003000e0081d100328003ca07900303141696601c0e03000d2405024100760781303680a080e000485003203040c011400d030020390f00380b407181c0a8043c0000d000407000404600841d0009521340407141004100720081d48410b480c482540a265202c8000c1544a01c05c071300246005000480c1017081020010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 539537239 1250 539535989 539536013
    0xb090f0d0507050d0215070804360f14010e070e0102060f070507060204030818010329040b040b090a0219030e1e0c03191106090d0b0a02040b07030c 65
    0xa8040c050184040c004144001215001c45209031138910543c01e450000c1058a14502c00c0360114080c005505004c1102800040048806120341c02d80303241d400c804400c01501103c0141c68110038801c0f25118100640c1d4403491540801003000181c2c0c80d840d40e140018510241d00c0054190910b4003000710523608407803134224912092028186914000c4008002d00401070150000c12401150303620400c20349504072005583c11101c2e0517140d0b5811407024020050455015001030306100b00c0b4126065500019180e110758400c0c0360203006012001c0c000146900a20300e940700d030310f440f030102e143d40b01c489000f4000e90200e24056921030070500312901c4010031000a004240c6400d080200201d1701080c00c0f0040600180d00b4049881c084034840e14200c1ca650b8065414002d075407481141320000c0040c0103d80e44640340031900d8581c2001048000e009011019410102d2840c0080014440b0040244e000504550050405c1c0c0c6507ea4050150800c950882c00314441140312018809040408 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 539538489 1250 539537239 539537269
    0x109140c040213090908090405090604030e0102060714030c0702040603051e07030b010e190e0d02100605100f020106030b01030609060b0a050618030109020907201209120a0c0b09 78
    0x30340c944001c2c000341d2400141248910845155140c881200300b0130000c003207c0302a00c000b0800d01850034105545600d549040d01c040b4040b92400f49080403a50010413424840e1016465414608540580b00003030750740020f20402400c00200300702001645c42c1d00c900406580640024212040f02d4410180b41c5882c0340b154a030103a02070501080003c40111500d419107803911118003082d1607035002144010440708020b03424030301b0041071510150001401701d108041c9a401c84010740405000c52080740c205025681d049001c64000198480c0141103545411001d8800090301613680d45541132070210a8008885807511551800c0034090f0720f0203050307106a401c0b100c2d051780c10310300340010b80744d0300c500c3c4103c520038400d0f60340384c1070310f82d8003035011203d42ca4002d81220b02601e40084020030744501c0887c54032a40045c3e0f440d4546920b400595821f040840c00106442d001c0904100980588240300b0010a44201640381000a9000c40040f00a011010225442d141c5c00400c0020b440484d40b40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 539539739 1250 539538489 539538491
    0x705030f031b0f0601050609010509031e0c01090e0c0313120306050a05092403010207081606061a271306060201230f0c0c3301050d140705030109140c04 67
    0x1c11000000121301181100d20440e000b9503250b0642d001030700d55020300401035601d40600c00d82c40d04e000a41d10395100743c00309401c041d15491844000151460030603030140da03400b21002c000007480c0840d01c100554000d46400c1c0c40c4240341c001685c2e4903186e14000314141e40040e45540c0300308018140420507801600301182c401005150035048481185030a95030283d1400e0300c035100c0009510f0a504684007030350412001961b032080f40d03801245840000750200c1d04645080300c0040c82d4081c042c814042d0910051040303241c0b001101024024074002c0982d03000d012242d94403402c00c2c4d030b04c00c50080882e24a1400209829207081c5000c0d0845d5555041c1070b40071a104401c44950312001581940e2017820035500b003020780c6640c881c05900340100020101c240c440c03058036222442d1103a40320030001c200d24040100049a542c100c281e18039081c4031ba03d03005808456824002003038940c0b038103010381034401105c1040c0c1c0c3c1c0b48000303425107102000c143c1d080248040c40440000c428040442030f01c6003610 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 539540989 1250 539539739 539539753
    0xb0112050f06090403140409050f09070b120604141f0e0601120e03070c260304030b06092a580f06090507030e030306120705030f031b 59
    0x16100e825100041c00325203c0d080d190000b03010140a5540c040c50849243c41103600c3e1a01c600380398004050640742403001001c40c4d40011a0700700001006019104c0c0b1070718807410620711480056070003001034401c59005480d01d04101071115645c130120700c1100004040700c400420104c0c4803103180000d4011501e400c44d920200316050360808521000490b4010001031000b1803040018190300030044020301c0e031800c0d880001048891140e40300c0c034807c0c1d6184a01030b16240e0000117962807040d44002004a512500005e0701c0b86042014198040880b00d042e6688009848251547c03c0d0713070100190b225000400e14110703601f040d121080780540a075903c1e000d070b07000d490044507032414600d41012030241c0320740d12542001d840340522070b0f828507802c4040c080b0406080d0340c40c014155a01031250a00e01d02000030740a00d00ca4001e901005407050b002d0f42c510f840b503030300f805020000e10313529508910030013900103480c0c3c40401006405213074001c042c54580003280102c1c222504081001c140c10b900c459 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 539542239 1250 539540989 539541001
    0x2120c0a08091b010509040603050d02010617150105011115010b0316021209061c0905100b0f0a05090a02160f1a04053d1b0315090e0102160302010b011205 68
    0x10100f940c00380000d081c5103869840540005018100031740005260303020303000724680090740540080c825941540002d01d06407040c5c00b804c0355a00000c0142e81c0074a0b205000401031540611180c070b1403000940d040d1000000c1da100a010707405c80c2a80700c05441e4100008004200d1002190841c0013505032000d0301c032000079182448001d000300e5003514403c031030028080048814032814841c480c0b92040041c030001c02c65082843d11200c410754a07485041c2408540c182c545449006040c00c1c240042c4020300c014242000e0000e075443c003e086c04140c0c2ea0800404410030038601084160038810120107900702140c0c03614070003c1850029581c000b0308140b0602c00043c030080381007003940c07e00081c013003851800042160540c1c0b0466400d07545501c40d003d80c56010011a03000030140351103014115240741c9040b0703000c608640c0241e640c06561a05e4090502c40081a07400c43c03c41c801d00b510006d814001c506401a12076281c40100701c01607990b860350407200d56004903070010b0048000700100030500d403034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 539543489 1250 539542239 539542273
    0xc090e1e2406040b10020706080a0506030d0e0112110403110f130b1908010c020106170705060903030702060f0a02190c0312020f010218042406050a0302120c0a0809 72
    0x111584041c01d0100c80000d266403115801a10743c04001461001554105c46000e9144d10083c000d410005103c10700140d410a41402028001d40c0c0180041c40803c158107405c40d100400320039114100642e660804102e6050341c0180d0004036003000309541d8492031850090000403a2031100b600840036092a62015074441d8440003440c2040c901c0810b410340d0f084002881c407250b502000c19104413041c004980c2c41c40550217540b2095035a0000c0081c6910351824650000b0510942071480d8000030301030001c1c2c01d00308007034402151702030100c03800d041c0250300207034454010000e002482240401c4405200342d0420a022194211100e500041e0344507440303205040c4c541d80809810726407690070072500c2030301c20004146800c1c41d02e4000c40d152802000e102000403410b0b03000074820341c14500c0e00c40d00f5101d071150300340032000300c54140c4103024a051811388640c1c101034991400c0c903034244860041601c010150364424040401e82981d0f0300c650f0704002d0103004000c0c00c040c80a91100101c480f5032011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 539544739 1250 539543489 539543533
    0xd0f050c12040501110a0f0206250c170a05090310061a030711010f0b19053703030207060f05031e0c1c090b010503030c0c04090c090e1e 60
    0x103080c12801c29699400c006015102c400d200700a0800000746007401154454031041e0381c01416400e5603803a407142c2181e96880014982840750f46003260081d000c089008024501c5040c1c4601c0e10142101c0e040d0340f11407650303080001030758007090000800514620b0309106a6080c1450061700300030107070401001c1400034030304886003141801c0c00800700f110705000d40704141140c0c0510f0024094844441e950b87c0241c00100c550500a40d40d804901d200110314000000c165140940460310940c07070607605d0303030305042ea550b10454085a0401c0c803180509030b0090342000b440c003d400604005150080040091901101170300400005005009040c5446001a00010348011382080b85460318040c4041c81e1240010086040c003503c00b00c1c00481c0f05540081030350a000b4004500d0980c0d81e0400d2540b68483c14072485442c0d00504c0d0001024900f640c04a03c4c013074003414040003102d89691181d022244950f0b030359034080d4021154800211103c1c8103000304001c1d0341000d000d040418a070400004a1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 539545989 1250 539544739 539544757
    0x31101032706021b061008010501080703031209031b0503120123011805040f0501030b09060702070608040816060b0a06021c2001050106080f0a09030f0804030c0510020d0f050c 77
    0x14000034483c003130004603d29001da1403e44420360701141030410818401d1516442005825420500001040305021444200f1617070142c80c4d1a095151345440c0b60004c21506d1000c07014024980d071400944d44031600036410941c0300300010350761000035000c40c60300340300141c0c44841c460b443da0062151103030400002814400c020300b801980c1e589001c00c80025844c09422258000d4901003298203a04903e030003650403240903441035407180c2c0340d8081440d03c0e810b0458101000d03130310580003044244d00ca03c07138166004d401050722a0805100d000c031402d4a00e40b07298143c829540b100c55110052801140c2c09004009500090000811005408031400550782c144401c1c0441c01098101d5541301c020580900c1030444020807a548c1c440700003a21040d41900c02d0034600303c280c40025a100d60b2445543c8040b40c040e201c02c1c86800e00c00e803040b10f101000038800c030100324403240004c000510810020020304071240001d600c8000c43d0613840d08942103440d11002160800d03040c090480c00140071106110 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 539547239 1250 539545989 539545991
    0x411040e010e1c08010b0f160c080d031a0102070e1501020102070c090e12131208071401050601320c2803090e090d08060415031101032706 61
    0x1a4040c003940180035646100e020b9018010031195681a100340718020b54959440e803c540380d8942d140300099004a1910090b03001041050440501540502c6408113102340500340b4110b448610325410700700300034410740200b0784504007441039501040e14411072240a200501e055460405a038000c14400340c00c240c0301221160060515901c04c0d0120395107103030842e011090083e0f03162903a0b000ac00104200e0040c038051050225003600a04080341c0141c0000107401080381d00f0144d503210070340c550410031540c04004000300306c00506290300c0b00700c0322030030f07140001f13414a4040b0002d4150041220b442c0c05820303405194880702402c40800614030070741442199220170307210000320316121a03220142c3c5201c81c80100f1450a10b204044e5500c140d2103036940200341503550103d401d030030105684e00c8a1035004081d1540d4428401c1110b5603128800500109091302402010300490599410589210543d202020901d58150090340d6101c0d002e640942e000301012818421a040091402042e103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 539548489 1250 539547239 539547251
    0x30a0e132d060b03010b03010311060703050711041d0601050a06020f2802030304090c0f050a05071106090604080a05010b0d120f0314131506050f06071401050f07090509041104 77
    0x8803460340b0110140c108100c060344c1e656101e484c584a1031700244030031903481c11600c02c403d425003004401c2d604203d5040c4c0b038160802c012940e5003039150304102c0c03103540c00941c0c505040845d4140fa122003491814a48003801b515418003060281620302a004807065512164825641140018000950f42a0262a048801ca074407400c0071383d1407000b45000c1c0d4180700124000c507880c02650700100c5030b00902e445002c05070050315405d0b42c403409544203003070200da030a22008000c207010308030098160320000d10003490308840600151b0309400030f40080e030351341d4843c03141002009824400c00200001c01c6910b501000c2140c0d580525103009d0354020002c1120b440803402809020703402803103800b012070094039182d1422610680342050003c2c015210718541e50503e4407502c2d001d20542003941ca020341440300b42000081840801d80c030400c2c1c115181c1c40750000c00851503400703120342d5008001d54407494400d8106020b006103070384010b070441c620810211040c800003503d0b811007290141d8058078080f5503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 539549739 1250 539548489 539548571
    0x1416050c0904050f06060d0b070f031b02010c1403040b01121403040603091506060203092101060902040302090f070e01030e010b0d11101103090f12030a0e13 69
    0x30140014501a04401e658040c0400c1081c0812000c8042d505201210b250f0ba440c00d0411150300703500c8001510242c04600410010741c4280020b150702d541ca81008100b004440c040440c40100160502c1c0050b513440344070031085035100c00ea010b07000c0b40385d580450850409848a175035040041c03082d00700303003440b20090700200b000100e81c0740140501101071300d0f140c9984400c040e014222050040311203030740c06c041c403e04a00317251040e081500e01c55402582800141d41c2440300b86500140e0f4a200f00564489852207401e090145001800c440320015131610315600c140008600302134071800b0740b00b03229002c121909a0004550320504424603020035502071400c0c2881c01082441840c0750484214401d010034001591f8003071003940d03c00d45540c202d401e96010111042010300501c4a41600b003084450a50310b080500d0b41a2010028042c400001100d0005403869222040b1107001c2401e054442283e440e0548500740785035445001404030752010306102c890f11050000042d140c40c5110784000c5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 539550989 1250 539549739 539549743
    0x1e090304090b030c37080c0405010905040c030303150f0f060e01050c030304110d0f050703050c030f071511030c070303090512030324100e030706020c090a09030e04020f09030d141605 80
    0xf503045c0c80c01200c90381034a804449841c1d00820745220f008500348400051201c40600c03035103103e181c109224920160544c1c0e81200984000c1901e101d07080000380001c82c18110034044040204160315048a0750741c9000b0300078060400d044801e9050103000e1000f0b250000002c0210380d4810b6100500d540d80300041400111105400c20000c4d0031071050320307607000800c800080d000c0b0135039008008564501500e0001c00d940d5982c10300c140034582c1c0006808024001d00d1000e0852010414100b5512140707049a1040c555004002c900900f58001c0d5010424907403c0f140e4840a0171040d6144541e117070345008040e55a110141c51a0f14644040c54107070100090790032880e118000081c848001e0341d02301031004000d101440c608910038000d1a2000a849000080e4480c4101001d0080b41c0540d88103030807400101440d00041c3e00780b02c0b020207442015a01c82c401400e0394040d04c440541c5031a40c20003818540b0500444100600403410300c0b1500003040d18080da200c0c50402804a02c114450f858018 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 539552239 1250 539550989 539551069
    0x140717070f090f0b03090709060503030d020903011103131a0103030806010e0d05010c03021e0a020d05070606150827030f09041e1b0302031e1e090304090b030c 70
    0x140d08100714401c04608103404c4801140180681030031615146d4558a911003210514443d40358554410000d801c140e0541e030f000391204050040c00044c5e03003034008882040e2030b07004407160000e00140c03108030710030441294070b59205140d00c040c8030486c40d0305680d0050b0a0710000b0300420305100d40703000a507a4541c0d45901c800340d8a54400005c0c0704103503604401601a41180d550b2010780b040b05048980c204010b90b0079584203424603401080192040350042c1e5281d4441c41069807010b84551002c510716820000300c18500410b5580c007025482c0c1620340764014a5081c02d0b021848204c1c400d0880b030200c0c000306032081d0900409000740d585031032100203030092031844041404d2000380c3c001c03455007206030762083d498401c0b903e03115508410041d004400302c0c802200c0401031064060f61000e41a42140b280c0e0b0381c442501c400c80381c00e0460b048100c3c451080104c0d4011940d0340300140510000120340100084544140c0c01803c1c0c8950441c00181c4180700b541e014032000c5050703030224100c81c248104003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 539553489 1250 539552239 539552249
    0xc0803060f240c2509110c0601060504230904030f180e0109061e030b0a02071a100504090f06020a0504051c1b0e15030102040513140717070f09 63
    0x2040c40c21004000782d0340c1e030340000031402201d00841d0201d080350039000c10146100050001640d1083d070034125103a000f0314032035440146020050008031082442000b159020f080790b40c4038503072924034024002030b00070709154600040b0b100800e000c2008da00c5890070306400a1b85410303c0d01820303851500c11150304404c04240d5003080800000001c40f00800d0424505031200528240201501c4a00302e01403885a001b140c10419840303030b01000030607091070b40300c1c6d00302d0700e210409450001a42c840340c580600c0500030052002e0b0303960520000080943c500d80080c02c5c2502e09001d1800c0701d4813241c9507030106034406406182c0000d00c07440d0b503d10680480340030b00402803c450088282d0004e202c2d080070165812200451007040403600f8025202c092421280081611051581d88018000015081400468056409001c007148944e102080442003042a41001070001183d100100265101030000b80c140101075500e0316007030781c00c580450360201d41801c1813070341e070f1903a01404c4030306414075805 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 539554739 1250 539553489 539553529
    0xa081f0b04060f08070602010c05030f0c07021201020d0f06052d04060b04061115160c200901330903020307120b07022b0c0b250c0803060f 61
    0x843c0140c104040d40003034610081c1141c20007500d98406900b2184a461b114000c200c003440090300d10044401d0099000801483c01410000b8540c04595040032160218181c4e035000320710708017a61a64070400b103100400c0c40c403c1c46414074010100700d03004850f422410014181880880d0303001e03c45528600300311310107402084507942d01c2c20046044d800500800000856440f0701d248070304000100b04c41c46100c3d1100f5003d15407650b2015041e81803c0e4030111090000d00052000480c0020071141814000c0c4480d641d07503000c501c070070450310400503042a95414000410182032000400301021803901841005a8500d89028103a0300500158002541031180c18400f0518118021081043c5442110000815101e00c40c0c02c0e600c0d6203d2690005440c1001c00502441608001c01c4410400850a1040d0f4010007500c50400c90380c0c08442d5448100001c000000039920310504100e01a030240c40d01410344181542ca00040703100c0075107803612174440010414650742ea81c1e00310741c1142e075041c49 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 539555989 1250 539554739 539554751
    0x24090a03030c14162d0806070f0921140a060213170d180803030a0605030d1403130201110604030e01030e150408030705070c06020105150a081f0b04 65
    0xe001401880c00c2402224004242e83c0700e100c0400001a070450060440c040072226542449142030040c01001d14000d20501c60b9009020542c03603101802c0054030403000a44241d141c2250b004d00141040c0c002d903020819480c0c03003004690070b20501c4000391884a4078906032200d01e403c205c00703242d90191950788240101c420031000c1001c07650050803485d1041e4030071170140f0703980c149062501c564142442c038160000d140484130b0510942c100c00082031401301e800201c54032601c807103246400440340d0141e41c903650320040c840307407504019005011200e450440c1035030941209220355400007500003054210f00c2c860070400c42e8080d6540707500e01000710044450030f20741824010100103100b00294042854400c51050075a004034001e05c16080030340c0070240c07a86556844c41820b9100400031420450706001900c0024024403a80c001403810b58000704050074010400c080b4642d4140d00f9a11681031034004004103c40422003601c20041c0020070500c403070f285510070024118001441e03074054030b414 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 539557239 1250 539555989 539555993
    0x130206040302220f0b060d0902040e1204090608030306060403060f02040e1906050a1413090803091b1c020105130f12050606040e030313030203070605040c0e1524090a03 74
    0x441110503111400b4184001651803000b5001c0350620301e51103400c14000c02408820b980150071280905100ae40001400942c41c0030303e90601983c00c800350f043c000c0004d400c0017511028000c04005d0401c00d00990f10358101907000a16602c118800100119101c3c104903074601090740c161401003000704049a0185881090828046468482641c19619103200450345040410010742a07907045240c06510b81c445004111032200d507402c6141490352285412000540110301450285031804020308501c0050f1603001140c245032601203000c1c406582c41c80703d01410700d20403464165020b0030100d80d101c624103034603485a20260811028400b1301d40e80010201000300444c00ca580c0118165030540c2c48040400098076020320889481e030b4420f06c0480d011007081d020b20811148240122807a048865a401d001d81c2e50407601600c1aa0001c10304022204429812980c000c41c040800403540cc14000022038068000381d400d1400c003080d036140a5000c800c10f0840c0d0051000804595642d640e034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 539558489 1250 539557239 539557279
    0x1f0e0408130f1e06090b0d06150203070507140108070c140601080321040809120304081f0c0c03080109050601030605031b01031503081204030c06180b07090b03130206040302 76
    0x340305403682c040f800c09061000428200c12070069030031603501c1c0c906107468030703045071401c0d003040100840c010780e81d4500280b4080e0548030b0500c0e0800e103401454580c202d42c10034a0030b144040e8404520f5119a234850613030b40c1c0e400405c8591207091801d0490049040c1d06280821141d0450301c031845124002c0042282140007001c2e2400398806d0860340c09440d8124155440004207031030040490000340801c8800e8078010381c02002c04140c0c2000c0b6400d00381e0700c070b5600380b03090000d624100d250207802602e92803809541c024540701e000582460b01904050b60703001044036a0512854103502d0790395001ca041070307109410400051100030102d4640524081c90040d150180020982c00f00b840c001201592080c08414002140c0e00020000c2c1460019100f240040790010030031000c006141c00c0070000258a48512020140714002c080300002803072404018a40c00544010140002198100410130400c400c43e03038040111018250703c0740f680e10203d1054055038000039440a8a254181d02c40044 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 539559739 1250 539558489 539558519
    0x1202060f070504050303070213022101080c1c120212070302060115030e0a110310050103110f1c0f0807020a03030f09120b0f181905061f0e040813 64
    0x6080a40d1034903110081c081d22035101d81c0c4107890305500b003400050b0140c6009000351141c000154005458003c4a4010045080301c0300d40007102d9070b0507040148403e076802c00403e0950501692006280c45034a0346084901c044060000d0041c500606910800d510034040404480440c4441130388a0308235140103034451509005008045001c0310002032094840d000c1c546410040c04042c0106510305d8441011200038241c0168041c481d002400c220600300b032040b40d008600a00c196030100d400c800800200c26442c00303441d03101d0200d03201001068074801c07082842e026408900101422828030340580325000f440f201039441803404400005040d001507401d0003408103070703035501d281c1501c98034400d80742004048007900d084030000c005208a5528a1a80c5c2c2014600c41300a021178100100c0d14900f20f01b03000301031445503450304c540c3c04000e4100701c041d4121000d010091400c2480348e1100bc40040c0d181b003041d000f10a500045018085031004503180404d40481140038152540004510828 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 539560989 1250 539559739 539559751
    0x131a090607141c050a0e04150303230d0c0806031209040209010e03030f030609181203061f12060e15010819020d090c050d2003010e03040e1b03040309061407120206 72
    0x1031b071014401403510784264003400082400c00c00c0403038210344040b29003900d590300711486100c4450051a826050701b0190140c4004140f02040c0d601443c4402007000e0f070040c01c0c450083c4d00400921034010102e034281d40e03030b0750070644005881b010f05500407560003140d84d54140c0c040c000001c20040d01c4880a004501c01c1d5401e1f6020000b5454882000007032074003c01d85108650020701ca2a40404c000b01d004541100006000101130480c01d00404200d5203004240c4011400030a14507110758101e000d40d6001700104041844c0c0707442d00b1020481c0c0441c0c117400503810401040005203c21864006011051004042c219102d588001c030403402042403000559404100030707000207691a14a0341081d000740d1042400c01c040340e8400034890303a12540c01115605540b500c02c1d160078080c2c100080c100500c5d41ca180301d80386044c80c00440084480156091400c01010030410020076001190b550032141c3e40c0c646180b055020b84d0040c001d070b0185050090206205d618010480340d0300080f4240101 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 539562239 1250 539560989 539560997
    0x90914060c34080c070602070b0c03040512072102150a05090d02013c020d0f0c03050d02030a020c0d022a0a030602131a090607141c050a 60
    0xc0c40e40002070101d8081c0302c0840421400910041c12140041407815070b038aa4001a40700720080c05550304102a013110b08804090303806010304024140e8100209402810070b0b8200303524101d00300710b01e69100d02c05d44c003900740034200114842c0d80c40d2008215120040240c0186258018483e01c260028980103041c07d03441404801c4001c00d03c050346004503818003d1f151182843c18910300c0900c058001c503108183d05020031407030880c040d0141803041c0c1d07500c00340001032441203024407400007194070f03070040786c601c11507109580c01c030800c6401c5154809000c0160400079009111842c0488c1d281c49101c6a100b4550b0022080c025903c40c29009854004070400c1503611003056080c0c2203070399084084d004480ba100031070081d0301081e00c100e000e032001000a401c40c10156140d495000c141e910208070400c6c1c54000c0c910410094400b5945090301d9100084c040d0314102e18080050b005000b060030160a06003420b15082170203904010020000c0000344d05141103080303103600900240c10018454001c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 539563489 1250 539562239 539562241
    0x13060f0f05030112110f0306090312100303050307050f040b0714100902131d03070b060916090b0d0b090f0121051b01020304081501052b030e03010609091406 69
    0x21a0107502540c0c103031120f64112400c0d002098450b101c144802d01e6000780c00403d006404001900c1c14094144200d598800541e0f989840d0822a80c81d460300411030f1041d140c00c0c40382880002d91100480380c1112701850038944800b12181400c7d40b61082d98004040f00c40c1c00234150082201802041108580071001e03903200d1220b100703400f400d541810500075802940c0d100c03544485e2003103900c1000b14003400345040d0420452005042e1840c1e1240344240c620740b211070100a405c0c684081203940c8a5000f80e03450b60a0b80500001a104020702c0c0185480440d020a112031020044d901a4066900041c803a02075414881502500002c00380503524208c480c180c0303062400d1910303084000fa410f030300c00010085d003484041d40704003484101c80c0b0f1340d0440c00104000903510300300300040c05170304a160b00303100707803d5240001300620580ca8581c100c8446049840c1000d0300d00d0b0381c10341c0f460300d1038060428110400c8000c00086c01412a0703040000e6080c40e1003d0031051002e0011480d110200480881d80350b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 539564739 1250 539563489 539563517
    0x3030306091824060b0c280308070c0818010e120a0b0601030603080d0e15160806210106211e020d06110705011512020405090313060f 59
    0x1e403040242040806004005484001801c62290764101c400c03541c8501c0c0e9403c500e800400550fa81540f0000d9050008504180c6c8420184070782c41610043d802d44028140b540d001184405440c5013001d0306001104c80011141e5024002c035000320365001540703e54030030b81c800c2444607582207603800d240060010060b456060911010100400e503020004206124080d40c41c041d03408001008503041544400b0000001400b16000c1d00f48041c0e00c20b00440d80e0441102d01c646040207084600039001c0b400c1040c0310040084511388140380810340707050140d50b915500400e5040d0381c100781880841884900c2c16092031019400141543d1821000c10a08140003000841106600c0c40240001540c20303c032200c2c9c880c5800305a1440d500c041d1480b911440180c44032021100f9540245010020018481e403c0000c00e1003140345540c0d98035420202d85042240d805e1582e40d000d032009000395a00c801180c014681002600c0c103004011150080041c0c1300e1400a01d08007076146c840000c03481c9c4404101e9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 539565989 1250 539564739 539564741
    0x4261c0606050c1e01060302180403030b0604051302280c1b0b09130e0303150906090103080a0c15093203030402010309030309060c030203011e050f09040c08160303030609 75
    0x700b01c0250f04020002007141c4c040e10015074582e1a46048990b41c0c60100200580362201e0b600c181215420607100949440d080190a83d0b0249a03118807a0008000911450356003001c03451004d0000c0600503100d5195840402135208415a4060100140c061420009a00c4005000140d2003003c0c22070a500f9070313100b0021300320414010f558007604248070450441c1044200420308174031501011500c025852215070541d4001c4e02c0b412010701005400141034200891526040740342510f411410b907146841e07109287c024003003d08104640034440206102000000c0c03011203910361410400814245046200040b0020356801300710302400ba0940300401c0b969012840c2d100c100080c503d1961544d004500070a0800012014160307140c1c10100460a0342c402e02401328050303240180d4a506121010075008610030705158035148491062017551a00e0070b0b1104810740940315020a52918a4000955031032034109201902c11f80b008258800f5140301003000b180d01a03241080702c2901d80c40414 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 539567239 1250 539565989 539565997
    0x16390f0501020901230405040b010203071b060f050703020c04021303140102041e0f030209041a100501030f06030f0615080a030c11040606020c12010e160f05010e0904261c060605 78
    0x1725840144410007503401d094109c038642040c144140c0e0714100c480d64600c10000465501c40310f140d810079805001c103d4205a107008085d51038204941007910f2756400960b2040880c20a40c051038002c038010507441071949110003e1035100652000500350030580b18000c1d00f05200e0320059000b80c0c030300080f940c03004500c880c0036124040342c001e02d0103044d9024000300000140045690343c003085440d0340d242158030717066801032140903d81c52047d0302d44800101600c0303440054401c6140f500744200001509003090480060f0300100c007058404001c030040e180026251f200c2c0c0740c00d0240c00c00400c06c155001882c50101e0f840795070344102c4007403003000f1300040303560b14051140964480d01300a01640b82c241c401126240707002002242c01c0ca1039480d802d052a01c00000d90402d0f226020080c049444040d203894060701c800c0c6003251000d0850000172f018920040d01c003170300610040d90701c00d02c039030001340c41070b00d41000e85e42c80f140d921100ca8550341101c504140542560350314281004c280944500200c1d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 539568345 1106 539567239 539567297
    0xc02062712060921040504060303210209060a0e03010e07081f020f160606030203060c030108010b010e0f040b0a08120316390f0501020901 61
    0x101090001a48a08072250004020000d007500300041d2410094001011803840528003d4030310190b02c5607800c0140c0041c1403401c04401d0640046605074008100340000031008005401c0320124003400200a41c0150300300401c401c002c1c07180c1d6200f008120700500001d2012444c40c042413034107400313078010f103000c2c2c018050000c51026040039801c504500110305501d001c84030714603000144150f4100050000c400c04c03282c010702a032980302001071a406022030b0703810708000000c042e071070300309118090b10381d8207116101825500c1000803074070480c0d003e0003a071401d8104030300b004082c14005140035000301440c0300005407110200f0110340c030400768552550340da0424688203017080c00c003010f510081c440300c2550142c0c40d0a000e800304c40071032280b11940242403403c042c242141c0d0348000000c2c00c011078110720b03102840f030f06600034401c1c0c500980b5510203141c602584c031920880310340b0380 = true := by decide +kernel

theorem cover : BRFrame.Cov 539388489 539568345 := by
  have h0 := BRFrame.cov_init 539388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 539388489 ≤ n) (h2 : n < 539568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
