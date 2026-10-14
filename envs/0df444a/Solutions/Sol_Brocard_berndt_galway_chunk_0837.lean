-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0837
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:04:19.604104+00:00
-- url     : https://prove2.me/submissions/af85c06f-7cc3-44ed-81d8-cbbacabff4e2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 150359712 ≤ n < 150539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 150360962 1250 150359712 150359719
    0x18060a1e0302060304200306041a100b0408070602010f06050a0e0a020712080103022112130803030a02040f0b090a120201110f0601060f03061202010309020d0605040309030b0f0f06 79
    0x40184020245554403500e81000f0351151011040c4030a0203405451410081032821070030b1200d461000815585003001c503001000541c01d84e80c0148030580e420040c1ea0480f614020019400d515800621036070b40003600120f03010350201c4810842c0c168240115080e0400210080001301c0c00c050115901119034044c00d22200f80203004201c2411b000e904403411690051fa00240c0c548510100a14800e800c1c441640b0030144820b50460b4a603000c80f25120103900b1800030030442c11a00c2103101150016030308000c1900d4580d60024140e542130004521850221000690b5a0300f000d00c03d621010311500280321100e01442480440d494104d460000c0d103003440c42d5140504210720040301c4841c0111f25504180c06012000072040c1000102d047c103030303411500c801c20817001200e01101129081e10421a0501007002e0020255002e40c1c8002680350010340003135100c0905407175544c16144c050b5001ca00090f6074100400a02c85616407958012503455030886681c01c1c0009c0200d04001c011308031912 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 150362212 1250 150360962 150360989
    0xa03060207020310060e0f09010c090611070305010509150c07050304060c1104150302010807020c030a02240a0207052b0209090c0d060203090d030b030d0309081303060b18060a 77
    0x943d5004c103c5003c5140650105010640d1284846c400d42401990000c5a043d4031001140050406000784940980b49640c0d812a40f85400300450303083e802580c854645001e009008230109100b03000e01845803000900070080d0700300c030880d6030b90030042c0284201800101032014400081000c802c031812224a4507006100800764141506100d07001c4103003d40c030502c0c1c050005c074000b03141c01c019400c49001f602c498400340d1b6640000e076201c1c04850a010307419001240540700600e070240383c40034511040a003102c03102c040c0d001400c0941c3d020501a002580c40588100860b1030030034035016480c441e028588036412700400d119041c84031840002449113590200140702c070b8804200031801500c00800880c408801c500303100000350f00641788000e5a000d20b282034440f29010b03020700b41c0c4002d0064000c08090120020460003041007035001c959000c000c00546070200e02245000002d580220000190314880d50f00b000040d4003002c1078007541d44200d031708001180d034454869004403403102a5800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 150363462 1250 150362212 150362227
    0xf0607020705100f120e0c011d1008180d0908060c120109091a0a06030606051005030609070309020405340f051e0318060c09030622020d06020d0b0a03020a030602 71
    0x42c5c0c284a801d0a4104075440c2c1610000c2150000814030072103802a01d503449204924107101d030104400b540000c0c0c20141c41503501d40f0702481903421503848801c030201c2c455502089503805090a088a88c0700300083c80d00380d0140083c6030309020064201100d00007161401207441820100013505104004407250348600b2182405005455000b9100510200e02d42c1481c01d0300c4100c1c02415140000c2e0703403c42c0703440d07004562410640070030860100c1c0c0b82c80e184d0441c2e480358100090b04000914800030540c452b101c10740144c03507901030903010b48050391101061400361800c1c0300481d4920b09200910300029400e00e4401508241c20b02090000c03890300c542d9400d451440312110903150103e003d10349000104000560f01d802d0038248400072044141c3e1025265814018003901880809a41c10b40140d00490700e8940070103801d03009034003882c1c6003030030b6400e171038000600c011b2890b00150380c0d16800049403620445c2c280328040100d08203c3d554642e02e421038003c60707000c1c0c2c0c4c207000003011540d0001c1c281 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 150364712 1250 150363462 150363467
    0x309040e1f02070507051516150c020a020607120c1e1208040201090e072003031e1513090803090d020c010201060612050a020f040308130b040b0919090e0f0607020705100f 75
    0x55607014003440e80c20040140341c1ca0909524201006072138416070ad07007441d40f20180e00c0400c00d1074103241c00620301800c101d1940c0312421801450362103a41071000b0310f280b201c0040c2e100784000c0900100000c842c0d5046103282443c26046150302003071010026036408201c0141e0b00654490180c540b550741c845059030701e8507001c0d00d505038840405d1402880c09891070003200d90000085100b129807442e4042e07101c528000301605040143c0700154030301c900c140d40e4161418824468140061031400c0451020b0a9455800c40e542c41610303100b070356410030203c520031503404105001c40c0040c280b000708031941c50298014100380149076070075403060b110b2002c601c03c2030302d40c3c0548503400b0403c071038142d80e181d80c0e2901010540c804800c80d01c000382c441d080020500c080d1400d40703044a02e14414030b0b00d085484000c0019140c942c07c1a030700c1e000b00c1c3d6400812003d219103d1070315415610402045c20f440c1c4032600c43d02e00300b80141450115402a442401151140c8000100859150030448040100d00c0805d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 150365962 1250 150364712 150364717
    0x30b060c03070606080705030a23010605040920030607121107050d050706050a051302010c021302130806060f0609100207120b19050c040b0c0309040e1f020705070515 73
    0x50100c40c80045940014001c8a0788010704903089031045840d143d50b0390f420305448450307040c80900302c141000214070180024104205644001c00f00002d241c0f03454800240c101c5001201c01d03107070810a1840c0a101810f21031442c4c0324400214001c02551030f111400402d640111a2040403803910b074801e07400850f500c4000d507190319610900b541c44d0001080c40042054220240503680075040c2004100c1c004003604c681030060140c000002c0048100d81c0041d00c854010143c01ca0704402002803824190a0178400b8012051441c1c0034104045c0c60012901d00d4a00090001e074426900c1c4058011607590702e1742101e8041b2010b6803001405640590181d060030882e5000c000901c004070303000d00c20891448140b034441c110540c1001c1441504014003011120101c910b842e00030303010441480303082a40400f40c0703101030700c0c0400c036460f140c01c900c042015188000704101059007c1035272610081d1600081010b0192100c104604150742a05c81640c0c40c1101d104203401040c801d2068403400640c1c0c0c04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 150367212 1250 150365962 150365977
    0x15032119050a0f0c050a02090601051207020d12060b03061207081b010f170c0c070b0c0703030305060d0807061802030d1e02030405010903060507180b030603060c1207030b06 76
    0x112032606400c0e503200a400c0364030424842001a40102d810203665000d130301d074012a550048000c0c5154512982400294030001d41a04d051190522643c4102082e80110620a00d102c4d409030050242c00d400162031001405500e650407424242d00703102035041281620350144044803207a40707100c40a500f407401d18207540c2017074103180102c0382e0039400101031000140102d0b900380d9030b4941074102c5800458640c5c0c81e803102400c0b2016800c01094003604a00003802c0f8400002040d60030803a5074000c0d5400580c44500e0780131040e084406c080003410703018803070554801e038199910205541695110443c0b84100e1800a02c2d855542034640d41150240a195800740d0340030703044500300c500e00003028100010904d00c040368070300000c2e0100f8003240301100366021520180c46c2d1900140c11540c4020141200a16403410085607204000d00c00310610351a400900c0d0b500c11195072420040141401d01c4801081069100c3e010001b98120603030b41c0c03454a070b1080b0743d0300d40016048000c08c00030b0500d218104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 150368462 1250 150367212 150367237
    0x613061103010e061f1707110d080f07030e03220f180501090c0507020402220b03010f0605130b0d090813170f0307020907050f04150305150321 63
    0x4a04510a4a00c20b40144130444403100ba43d02001d5421100600e8003c14000213a4416040120b201512400315040f03021406c0050328548240d100b02e1802508030305107400582014140300d90300ea5084030254000070245024441030482c9031400c1e80ea803090308603c401e92541f1900e030361400d02100001c00081e00001040029140c4d0390820107051002d910700382c40c980c1346032100005100200d0f10030751040c02c8a90315520305000458007000020741200c0000d00e0b50115601250502450302d1003c0d1014102d615080c949070350400d0162a084c1d921600800c0c1400317402c200d03403141c00885803020000c07a007154003101e548081d9504244040d040140000300805030114010100c40102c0c86200d05903074502c464010102c05001c0c0c010b6847d04146000300242d0001c00a500150800d521284d80c0401182001450410500302082c0b90b036101d0b070300c503880c3d08211046403650258580565600500d041e840c0c590b041840c080001d8907085194030f420450007000424100c00b046001c2620807500783d48 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 150369712 1250 150368462 150368467
    0xe12010f050114040c0807020606060906210f010e040c17010b12030c1207200117070302070201111f0b0301060902070620070c0b0d1d0d0809010e06130611 68
    0x903110391107908492408680b2a5003000110015944506c000c0d038400c010950061105032038003024010158092441305130001010000340468585c007552503800c1987e43d9a028103280342c180c0d07a03a00041410b801000d0826121402e10000ca080300420300b0940e00040d48400c0c86004a9407118010104880d1480d0000381081001440e80400310290114055950a64144000860b14030f00346201309200100380104245055043e59806845840d041d201030504420191810160b401806411a450800280c0014403a0210b50f48042d00e10395450210300148090010880100c00d020052204081c0715a520074a0000f5603a00f50802c900905601314215990603080c103200c0040c2405801c107104140e00821000c51110102007220722a40d000b40c0c142d488035017488942030071079001d444400c0c00c55031112561611a8540c8044140d800119001010555807102025103095001041d12105034134000700c10710120801326219500003201001d420414405141210003044850026112281d01 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 150370962 1250 150369712 150369719
    0x12070908010e060a0f020405010503041104061a030a060e011409060103200417060103020604031202010204050a080f0c0126130503040e0a051605040e13020913110603070e12010f0501 80
    0x81211070040c401d4103400c0c44942c0c4c01c0c001503821b034800d0f8424540041c004000080100b40561902e5020707013001800031071115500d81e02402280c104640b0342808050010602865030300d81d102c0d881c000c0400b09410300242d8505261800c20071200c140560140707480c41c0004030941c0c42648100b0b0358010304501010392014400040c5d44540180c024200e4142220100c403090fa0307000500c0310b0489500500070b07407515045949040d24840c40104ca101959000d020214103039650a01d4540a021035200400100c0c2c002100249480a0101c2d035a040c48a0a0360441800b45a4a20381c1c00130241c0901c0c188498031042c581440c669110034000e002d40c0004180850251491003440740510a4040203011540350301192000c4c5e440581d1078900481c804000421000a054001c242d000e40b001c61603021521440c2c0205044103012196803000301ca40d41c00c0c1380c0c02c01100441e802c00080c8181e0318542145404103001c1c0c079100c180d580e03482c03003a1110423403850300c644250014405200c0700360041c80907594 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 150372212 1250 150370962 150370991
    0x305070b07111507020d05010204050a0611010c03060302010e040c05040b030a0204050108070219030815100809010f050408040e1906090501060f0201050f07030513022718031207090801 81
    0x44200215008100300c0c418071010324020140d240d02c81e003c080c40031301c0c1040b03e608004012403046422100d5540078080007a1666882408034010a1f050f00d03800c41c03030008102c03850300310351a069010702807500c0c1c4441400541d03400100e45000300d50075030b0000f66007031b4490720070f8881e80520f5100c0b40090300000308020000b01c09401400c1100d1003078071901d800351102201a038690031b14441302c14100103604075200110740b199400642140b01162803400003c4400003085003072614455800219070394a05214580300b0900c515020305401c258200002c4c01d1550341c000b00380c4924450031000214070000b18100240c01c209030303569010b015408114040e42d4828803006000c007480b5541c08110800702d001d0b8072a0060040510601904040c001140c0c0c070001b06600038071000e007450701c00b48920780345000180c403a69085a1f9001d01c003050380e40d4807004920300d1250403100604009200085032240780e0016000004d94003810162200606242e94103002200e01e24640d5001c3d01040d0f0030039009841180 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 150373462 1250 150372212 150372217
    0x506090d0c121205040b070213110d151415070303140405010b0114070305030f090c120f0f01060605041a070c0314010c0513051201090c0b030a06090b0d0b0a060305070b 74
    0x18400c0c400e0f14012a00d0200c20348881c040ca200c0c82420f060204800f00044c5003801071201c25040c0521b0003e40782c0b503005040440e43e04921034100c5c1c07069581c2d40f0041c034400340d0012132000300400c040403909809900086211010b522035100c1c8950004a1b0080406002c7d80002460340c0410000030586d26103818414060010861060702140306102d00c803040c2c00e161004c4440258140c0c0340c05107076803194080c50f40703440401481c0c031946018079084018940c2d160203403031161504400c018422803000c05411410b00600c1802d07041c441e03240030001c020044d0002d081c1c03012519039800c007204216206001c040f80303101e180c0008003411541d280100070062692600c91088880f14000c000460820030140e03094862141c10550442000e80100038a10b1703d114101070307642d800c10000c1010100c982c2d038550480e41503040180b00c03c101208216240c940341c030440000b8055090144a4100c00c4408141c0126010102400300c42e540d0000170302d40e403941d0f0003100040d43e0280c2251440d650f5500501c80a4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 150374712 1250 150373462 150373499
    0x605060c100507030b06031306140c1b060f1603060302031002120a060e0a0c1403040c080d05070b0a090f020904080406090f080316020a0e040302072d0506090d0c 71
    0x4918010100350f4603403107031140407616513010380014135646804000c1c50790a0300c030001c100c690722389408da409083d038070380105d41c0d008580c00c003202a118076400103d450a411008220300f00c0e681b02c4010002642901d0f0085a08080100740440310a46004e034100c000d0030303103900040c1d050b00c81d0001c10407942690394010000748951003018201d94540100b4030b000c0e0703400b07445805603c00262010903040b141a512404001c02281092031003d200c80050000580040f43c1c15102002420801c2200384820b0001480f01c81c00340c50030030300e001c4c590317500e403030740c0100140c480c02449646041c007108021035600c840e607030349030000c180c1c4003645803a00e00441240e009001c2e0200050040301c00040c3c224450f8407610680d02d54001950815161403101c2c0f0840c1140790069920400c4500009650703040514602d000354041d07030150000a040035640c3c0907030030142880c41c0f02120b01c003007180b913510015075100d003e030358048510039a00d10185d8005003200e5410000034100c40444400012004910041d070f081d03c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 150375962 1250 150374712 150374743
    0x91e07090e0124050d02130905090705010c03020325050a110406090c14210708071707020c0906040621060606050309060103060b060f030711070905160c060605060c 72
    0x80e030f070700e9109080c01104894180e044941841050754103050040000d080c0c000c040306801401e00416020246100007568807e038044e0741e5820510500074410b0110303201030107080c00c00a44484296900079542c4c881d014402000d2001040100742c4a244d0401c01c0b01015002001c5601d81402400c1601c1884000070b602486686000000a4418010700414425041e83d817103c1e00d0000c1c1000c0320503100da01c940e005103543c1402001d13003081c0600085015000d1603060b91040c40c1850003031000740085c01d0300c06910000d503030900d080000b65540084d0380c2121031020f445072406503c41c180414050301d46500302c0302c4a1000c3c03407681c4d400c510302810b8446001d801400140301403030351071805840d10310058400700e032290404030042c40400e0964024171849200688110301d09a0041c0d001c126580040c1c442100255648003d80003801003008100094455920304100904042c0911051800442034101c00c4c4101202580140143c0758000b0f0024007003c0c045940d152610884a901c414940c03018110 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 150377212 1250 150375962 150375989
    0xb040b06041d030a050309070503010c0503041b030f0609050c03010204090b0a0510090e0411060a030207140c06030a090203190f0c0801020406020613050a0203070e01080d020309030c091e0709 84
    0x900b0340009101111050520018524161340d0b40c2c4110b559900080c03801c0c40910a004000507961001d2040603da8143d42d03840c01c1d2a400c4c01d15040b034641444208440000340101d4040c804107a400d0500660180c0c401c0001a54a019150003824054030307007a0554154404500012540300d42d81150a203500112440c50b1401e45480400c02c4000300c1086000008840d08010710458240d5400141c01a0150040d0300301c0814401c0011202d0384a80030b5000040e030040303020420808800000c1162510050107400107a61840204155000c0240f00c943c1130750325250340c0d400f5900e082c00a600d13031100b40ca80c52419448981400b110b0a005208221152004960002441c280c103200380d0b01540c45507405810540c88010304003100002800c030998090107a11030080050350100a0030004103001c0f5064502c0c0c1d803400c80c00303d091000c2030500c10f081d50410000c030455030342e0210700480c2c005800c407000ca00070313298002e40100f00c00c0c3d00b003640c0241320780450a002e02c00c0c1c0c011703101c04101e800c004083c84 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 150378462 1250 150377212 150377231
    0x305030309010e1605221e3e0906120f070c03230d020d0507030608030702060d0905010e03030c070506181c031b0504030c0e071403040503070b040b0604 67
    0x75035403131040b1041803600124800901441c9041a000e40c042d00500581100f5030b00100842e03800c546a84064040d000b54080c011101440580522a064007654482c02150501e000701e020207840d06600201a081154103400901c080903016200c0103074018003810384030f00621007140f5600106a40042140941000080c011481060581c0c3c03920384c140d440000031090791103160012804c240103030244607402c2c440b0441800343e610103418110300000021a40b810461702c06400c48000707400c0b96925820801c00180035807515411a2080d008600002a80c56002e080c9035004000c40142c8803a13502001080c4001c1c440317450003900c000c500440945800741c494070340741c44c03111140c1140020103402103050104854101107825440003541e040200c4e2074030044402c04120442a94440301040001c00c051003448000b0324910050010101d100045042c03010000e02482c2c140e9881c1c0043c030700b00000282c02c001c020310945051540c031022007013480c10310340b406070803603241110b50360300031440e14840784e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 150379712 1250 150378462 150378491
    0x302030403060f0216080904020f0a0201141b090603060d050703120e100f0e010c020a1206050c040b1611031b030f01051510090509040b07080a110412020103090c030503030901 77
    0x491701c1148030304034988129003e82d101480ca07041503113440d41c001da0911850721010315040c01002c81c4c4440f41d0000030610a88250002c41007800f0b040d4200c060032114074a5070355200c0500300c51844000321074141e126901c00c00002d001c034207451801042030082580000421400d01040380c1d042141c0d40fa015040140300d0280440061305000d490002480660000342d0039014500102c0521700601d0001c01455207500880c010f05070b42c1d80402811020420103405018840c401d080c3c01130449140d1f00e180a15003041d1039024003402591180b4400484e0000c810007401680004035864080d05075207404901341d94400c00500c01c5c4081700d0190082554980080006116051003096035600c0d0302c4070681502e080c0402c049011a000040c0440017001050540d15120218800c602c201d116450a1900100c0103112039400f4100b40c103003904059000032510065000d850035a41904000394040c1c8441c00100c010345900302c3d025144542101000c420703c807000c070043d0700c902901c80007405440d0560112 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 150380962 1250 150379712 150379717
    0x3020324011505041a1215130912180f0906051002010b3003041203030608190605072c0108060a0321020c130f1506080406270302030403060f02 63
    0x1402c0010b01c0402042c008110038107100504070510641c21410090f210030403d0350329809540c2c070b01c2c10110b540011101031a14801410000789012000e01c031440d003035612451170b0341040072428188040c20b000403034805500c2c00701e1801000c640041052407640c868001009020030b0180707a0082014400c074901c280e005019205018101a0000920249010030b000412180e010055034200840401300d83e03041c0b082010301301410441c08404442c5185103000f4007281c0581e440419242c0142c1c0a516140280d03a800750304c0c030b40d045800420143d0720b40ca0100c643c00901076205060b2648900c0300b030060b9080b00820490800d0a0702da00e03026481d5081045100c00c0310380310007494007840280c2c0b03001c0140b0703000490700c400a150048a03c814250390009407078600402000c0c40055407450350002d004003d0140741810400c640c1c410050b01c0c10120700501d842001400904807070344417010f0f80415202c180b0511100da10a4454441c10b5459180007520383c1d00038441610303d107040002c1c0b00b4214001e4801c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 150382212 1250 150380962 150380999
    0x1b08070806010908060a0c0e190906050d020907110705090403050a0206011413020d0e060c12011203050a1d060a02030a14030907210605040c06030c0c080409090206040302032401 78
    0x51089680f42007000c40982502402d0700c1c100310380b04600900c1d13910780980c40040400840c0c0c881c9d83d001e0a1038000821242958800c601c500307200b8605101680f5400c2003a50420058644085007240f405055445d0040356440f0a8120900c5410442030540c00300240051840590950b4416642c030010746021b41101210740740c0c4003214141002c4000765643c01029001e00c04000403c13408460609181426001c81c1c0170300d003000d000120300700c4464001135118054141420003400c60b07080703910018161302511144001703100350005220701814006080f0b002100740246416a03801080000135100c1c0c0140c40190045001400400368120409054a100360f50b03080c000c0040610b84900d45216182d501816981400306d032001c0d401203107460243c548518007505e0644081032410000404540c50003104104100d0314059100001b03003c5822141100e28181c13020400352250b0000405c0c6105550009605110780d070a0030125151240c02c1003110302c1950303c0c9070b8040c1e0366440c0204090800c1c07130 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 150383462 1250 150382212 150382229
    0x5010f06050c0f010510150306030b010909020f040501230a031208100801110711011b0b060109080f010603050706080108060a020a090b0a08091006080303060d05011b080708060109 79
    0x410900a50740300d00003800007040150202c400e00352140d038405086440a540003200e401003103506004004c03d04a9105141c80300c0e1074204061880d640342c980342d25406004141c5026251030007201556601440307503881c000002c00070022540d640e1109102011140c6e0301a54000d40c8244040c000e00d05001100100c3e078100100004054035400200c44a801c02015940b085403010030103d9041c40920441d211450920016659542c1c917081403c1e10352109004141001825540c41e42c11044603029201c0d003e52010707000c426511104016207a840c4030343c00c44405417160003000d06107110150011002c4030300403801d440710103444003003c50315a58240140c2005a10a0001c2204084140d00078a80030110785405030300d8a80752150f80c81c40d0f9101100c1c50b07000802d80c4091104480003400400ba8003d02100100020b61500e040305481c2d010040034030b071080003d601d02605111081d0003000d1841c045400a85d074060300c9400150181d401502d9180002e001d030f01c0060125405404100192031444 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 150384712 1250 150383462 150383489
    0x1804020402070507030f03050702090a0c0f0c02011b0c150809120706090f0609120801080a02011103130b0406030c0f1706030a02060f1206060a1e050705070b18040501 73
    0x25028400a5440702c00110703010f101d008000170225800c2d81d480181c035840f03961119683c0800303004000c0070810150550712003d142a154006e01038001b00c3c10041d081c2c99003801d0345980741f20300060720301c85104104011951080050003042080840f580b02c1a560f04600d12420b02daa0083c04941100382120752a00715403020040b09021203181015200c014418000031030001036960302c0d01c4603010141c100b140c2482c1c80e0403c8108000311480101442d904901d800d503000d61400090954907800c1d110007078144045c2195820840c80d051040b81d00131440260602801c5546048422050f41f06104190000707141c41220b0701454030034104035a50074010b5840d5002c07001c400d8403003a8085800f9000c25410b00c6000000350068480340040c10b0608804101152280e00703649006620b6072008140920a40b01048440032580e0020054060521034040490fa81040000d080c2c69034410008081c00e5440380403800194511090700034042180312020036a40019001c00740010f482082c0544003000e06007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 150385962 1250 150384712 150384721
    0x1e05010302010c0f051c0f02100c0207150504120f0201020d031509050c07020405040b0a150b0712020a1406060f120601170127110303120a1d0312010e010518 69
    0x444402003050154086d546a00383e0b48400d581d01140590443c000314602d1001e1001130350b018400c001804c040c03400d003800044500c5030000d403121814054110031400e00b9000c0341480384520259030181a1106034a8040d618a041c0700c00301042d540c104900604c01c10f569041c505201780030328481000c0d9200100c02203424100c0e0480908001000421015410b02c044400b695590240900540c002c0080c0c80c820f05090244600741e0784c454030356045101c80303600d0402102d100d55044030896500030700d00820402785c90000301d00701081c1d0350f8041c1c50b07011046000552480042070f81d6000c0d800440341d04040c43c035081c051003024082e900798044541c100200400c49640310311441500d2040010000520002040019100800903070301000403440540c0920308010f610349910a24880440042d4100b041404074081d26140c001d2107a0216912001c1051201c90103541c807144283e5440c0c1583e0310341021440c18981c1daa02442150f00d0100e0480c000145420f05072511a803d200400c1c1c5101d06944 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 150387212 1250 150385962 150385973
    0x71106030705160b2a0711011101020a0804050705181303180e1e060d020108091906020316140a111c020d08150d06050613020403080d05100e0411150d1e05010302010c 73
    0xa00040300b418440107044080c9d000c2403c3c401400242825120003c490520341059440c141c00368006a006078441c0043c0c4030040c0381e5040f0107038400306e80710011400080e94034040b1060700c4248683d011000820502003100c000c5842100e22906403018040c0768000d000d000186d00070400d40c3c0164004080081c5c0d8809540b01d4200c1d00d90000030401100d8105403030784800210181d49030b20949221f0703404010b01501d815405c2a5580070286450126020703002c80c01650380504c206418071091003000c48510b40304401c01d0100310310322051401520303c40c280440000e511010007440c2c18000414043c0025000c58050244050b4118090040075404810f51390b000000c06020b000b99520800b0f580c890b03031030f032210b82c00100f0103148a0f055158440800c01c1144040d120060000c06240840190034072640c11070b010740c15030168000040c20407a6405801051140e900802d188580c860001a00503001600e90091103030f20820002d442030050b0403080b0642103403c05e00000f4002001095510042030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 150388462 1250 150387212 150387233
    0x3030e010f021203100906050303090901052413090506090c0a0509040e0f0a1a090a0305030402040902090403030c090506030c16021807030b0411071106030705160b2a07 74
    0x1d0480c0112031815854541c40d81c65908112850500d8001001e01400390744243c0c0140e80040905074019800e0010510000d0a58a0305000700c6001e91500030540c41402103001d849041032900302255a981e003512605018407a02a00403c240c241c1060082816414030400c400d100305505181e00c0d0503d02541c0048400e0f500c4800002e42c01605d9161003d44100c06100c91161358003c0360051900342d6192900c01410789540c0b4510700034855a5003005a5030b81c0110703000f40c1e40e542c18900300e42e0700e80c5d0702c1c80081c0061002680c00780d00009118100010190568400741c09032500c0d4803080851a0b85504002c0c40744030481d40580200403c0c4031580645600b018074003880ba2000b81120403800701d10301d110400100480307484001a40b517503d0320205041a20070221031004801c40b00b4940741554551820b5404041c69030b6000c0c2200100240600f48504181d0301100901045115017500700d040c1460909419560111024028841d885011095180452503110386844441c1449055140c020124 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 150389712 1250 150388462 150388487
    0x50a150c0318050a09020316021209060702040906022a01090305090f010905060d05072303130618030c06050907050d0f06061d041406010807090e0109080c100507020703030e01 77
    0x111001d981c0070039039554404100004d0260301000580783d00d488c400300004808141111801e541100000031038018120085541c1c054042c1e5035076946a8003880410f0080c1400c0601501d12480030402c110a40e0702d400191380280d04581207184250051f4445508a450882000b8041181008914034506200c0d000c0659844c0506061448558800c0400d1066110020450071035603280d01b0803c400340c002550501400c1d0584000000f070160301002801880b0240c8107141c0c24841455601c200101500070b02540c49048450b0340c01c0369114500641740312076800d8100d8181c0e080030b0014800d1800020b0382812114018114002c4900a440d9200e4007522a5000c0d610141c07540004105021011883c40c44401d14101464803454142001008911380794021200c68114800400c1104c100182c0041075a5120700c0019100e841c8406040c010308103d01c0013000c074a00814440c080c1040451540d048400411040c0880e690f0404100e8403403c80b408020301040100b038140c6042d51160701e108044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 150390962 1250 150389712 150389747
    0xf040905010e0a0c0603060b190e0301110a0504060801050d0f02090421080702250504020d06150314010803040f0e06030109170a02072702070503070f0606050a150c03 73
    0x7440e00400010308110f40200140c800100c901c030704101044d4180700380002031800e98a00c504181c0b09803450391500804480c1d6800300001c01e068000c00f65400c1d40404801d0b4140781c03003507965640c00240600300781c01510840000c1954100001401d0030312076410600c0b5a4048104500020300754200880064003800950b1a1092031502c800c404894018011842c10b00380c590050600e08800002c0c078010b10300d0102210340c10000081d110160f03008001a0651300201c0700036803a0459000460700400d100e43c0800005481c0c8002030040c0342d0954131100c034480903000504182d1b03880328041c583d41e21403881486440802283d08105c0c440c00e403815036812030001000414000c0050b290306110755103c021641044500140f208487d03601001a0340040110f02d041c02c80c0031500601e1003000ac07a1070003460100c141c0014281d000c020041c03003162440c41e4001d40240b074503910780c14008024001e5018543c003803084090040352441c4050440d040010b000d84c0c0d030307251682c03003650200d48509842500c2280e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 150392212 1250 150390962 150390971
    0x207020f100212040f210b01141201110415020f03070209190515030c040c1d1906020a0c050d02030d140c030a03240b0403030c1a0403020d020106050105090f04090501 73
    0x3a1690510010002482e03401600d4200c24201004091304406c00014041c82c030903294803c0e80050032510203241151201c01e007050805000b100030400002000d00602450352074074011100c5d80c0099805441a1074130b03c421208000c4602a059a0340c0701c098070340d8400e65009201e010014034103d00800e50080350b0000d03000304034640303901c0035065510a0382c1d10558000c42c2000030b840c504042000b0140054201c2d4103002460b000e4070050143d0340807018500c1180d02c46000b002460301c901e680520345081d20224000c0066461500940b200300e80b00003152400e15043c0f001030b040c54800c6441070881d0300240035107103544050300240d90b590219007407541ca89205000f244219a0144041d01c2d54144a49002c69508a6441c100c003124400c100185100126a0014010305040d8411f9a050740ea2508104030b00044030704006000f00e03242c101d61003654a1080c200020194080340c0e2070403408854009024480e210401500c0b0b502500c0341c16a00200c1d44500d10045141540151804c28010342c00001d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 150393462 1250 150392212 150392233
    0x10518010e042f090a0306090f0503071406090102070c0605090d060501060e011205040b01051903050105041112071a0f0c030301030f0c170c010c02030c0d0c1401030207020f1002 78
    0x80035280c2c2c20311580c814018000c0a04031103c0c12512039a6001580010940b500c40300d00b00017150790103d40005400c040e40c80d00103000b0008002c1484102c00d400504903500c802d8075180085c10b85942c3c0c1020400b44c040c98010a521000500079140c1c0a0741c003440e2034070603030305103141158160004214554844044142440803400078400c1034040e004941d20001424419000508900b03900315207401410300c6c1c08100004200341d1400581504c40440d400000c003803101041c901d0602c02c6030406403155203094140300400404400c4494002e1007962940340d004210600141c9030314040c422800301901000000410707001c041d0040a21040c0d256866080a4000b410a0f1a5070403d8104890030381180d43c80605024040c02010002c0645000c059140c030480d60034562101440c060290600200d03a03290030441d80c0620030084030038406041468030303500070b043c040c0c00490244614490300e40c681d042c00f4603d511038000c852802c1d80141181090050000a000720480740b008800c0841c014131042da07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 150394712 1250 150393462 150393469
    0x3031006081e0406060503010b0a03120302030421020601060806040203060109030803092a03070e010f0e06220b10020a0206070b04080f030109060501090b0405091602030d020a080906090c010518010e 87
    0xb1400381d80625400034030f0a05140c10b2500b111200010f82d485070264280c2080022110394241004d42c4581ca800f50326502c071413030036846040344032110240b03070344420410001d07659000506504070b03101b5660f540d880d034464000b444200e10055407032a0006500b80c4080c408030344000020340d00701c01903c00711050b07428049409400b105604811800d000c1c4813240460b6946810815040640300f40c007100b000e00c1d490042400520701580c429104a108014000340c156a80c404100c00e040b0300065018245100101c000780080c07801140551080d2000350012881510001e950340211354041c00891600b0030580701e03c146c4140050080b181c2610070090250711400981c060340c020048400701103401820503001401941e1144c0100403054428042000b882d034403400055000b466034034140c124002512000c03401d501c41d401c680c4569600010700c403080254003440c018420307400442561101d4031260203198448403080103440c0091828840042000414440d04c4410201414007102081d88031010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 150395962 1250 150394712 150394771
    0x108060f0c1b070f08010c1e031d010507080a180b06040204031b0f21060b031518061005010503040b070e1009080f0a02060406050d0609020f0403020a080303100608 72
    0x1c580b05500940c40401c10040e80c140214041d10403000240415040110024984080902803004076008000040c51040c060b0b401400024822a9004400000a50203c1c068a8190b03181c00015903610700058031000940316101c660314400c0c15844901c1c0b03041c4c07501040000003030001e5074400e508120000008540d02040070059802d0444100343d54036045c40741803408951341c0060f403c0c00320b0810381400e88182018801c501580708000003040c0c1c1d02d103c0403a180622a08661480034801c9041c40010303407140320b4803c0b00c140c1d42c1088400d81e9560069512a060042c4a81800b02c1c5003800401c0014500e0b01d1082d910403120725180c0c603001c211500240c0c0071054144008086000402c0602c4080c00c2032000091682c00300c0b000707122104032540460f0b054072841c802d520401c100800c000d2500b1805030071510091040309400d54554400c40c00000f51580b0a2004074419000316000085d99040403003a00e100300c3c800d0040740100c51074558151840c5200800741500c070000400d024507011032000c070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 150397212 1250 150395962 150396007
    0x1803080f0912060103060e0d020f15070c0b071d060702060901050903030706020307050901080f0702060103020909010b041b02190f0b04060e01020d050a0c0207260304051210060e0108060f0c 83
    0x718105940c5a102801c0180201c02103007150400340ac0c01c14135580014010441a014a0344903100740d03940c040071a140d144514008100070300003818450000d0b444541c0524209003007a403407014000c8401040054421220b00a400c49014013200b0390a42c007940c00307040c10150245c1620314250260343c411041f40c0c811644080461b00220348021203503401a03503142e03c1110704244210314108030101942c3c401c0e051100a2090355000e0000c2c0d50040290840c0c441c9800180c018403100088681c4031400c81b100d0603140340144210b001d42c0314403065181038070000c0740e08181016502c18081d100c5500888009005840d950b44070040c800030208244028032820108440c009402d080041021040d05c801c0684401154480c00c014030894510080c009141008888100d0120b440c6e04110381c1980126841140e00000c14010328034400c801003003080080d00520020024140c454103107142040c82805054480c0c1c0c003280000751440c5884507900d8105007601c0c40c190030301407100c000300e069401215 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 150398462 1250 150397212 150397223
    0x90b030f03032806050f0d110d0c05030d02150c09180a140c190503041e0302030301170307080a0e0f09150f030d3f0204061803080f0912060103 63
    0x1401c0c0f0301c0f00d0b040e100802a05000e01c3d242806100d15100001d104044100f80d40740c82581101081810084075803009034410f43c014081c80c4e608905820640f450a519208050281c083e01104010051000c104c0108042c400700c03524525440e4005600b4160700300e000103941120901400f044913101c0c0b0110903201c0c0b0300c2840c0106042914a85592800e074001d030840324203408c02d2210b14441009200f51142c541c2c3e032464010f449a90318140802e000ca1148502301800000c0141c070411f0550200003141a210030703900540d51001200411075132485106405015000244040d0170740c1c91140f404c00e0280200108100c0f030224543d030014503468001e4480d0105408071a10348a441e061a50003010803060407005080041140d482c050300042031151aa4418045084462800c518000e4450f4410b21103440c1e42039500c0c0d07119000b80c020350250084402290a0040c400c00480c050030121007031f02d9108003480e0400440101400f200c0d00101d161907030044292210008281d0300708140ea00860003078 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 150399712 1250 150398462 150398491
    0x50f130c0e0f16081512210306210706031113090c17010308030103140709020705150c0702130e0a02030109050d390f0f03080f070c0b01090b030f0303 66
    0x2a8800f103641221880c51014410080d040141000040300004070344502a2003801c0400d01000409003040c8400c143d07040c1101c2003540b40c03078204078000301451003048182c801620301c001c440810319608500410040c0d56501189050010b24030a40101d0f0606402c2c0c0d00c181d040420000101c800c00f07000b900941e202c2a5a80040080c080e8032080c1140d99031820740071020355504580340e038480f9200c140409022101141d05c01c1155620410400c00241500c41d000c5450f40410310340350703407a143c030031903112a000013805c04190619480c074100d81c07070107074000c003031421542ea40b100c410050503900703250780d60034080c8060300b50241e03d01303004561605120308041c1010101006000d07001101c44242d0501300d003c0081c0c00740c170b489800803d411020007040308042700350700140340040180e40c006000410070810002200100f5400804a03409032044a9000c5282d80c3d030350b942282c001ba000786000d000506072800400c2400304551042e90700c0803010b41514448e80c04a151a407565000b0b90700303881c240880 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 150400962 1250 150399712 150399721
    0x5090a12050610060f0c0816050a030503060a0905090a0308180f16120f1707060207061d030f0702010809070f0618050409020904061508010c2001050f130c0e0f 70
    0x50401020142c03586040491024451500007048001c401c6da00408040c0c0c009003642050007090783d00a0940c1e407290490300805210b1030000d013030f50400e89116004801904000c5001360403801054440c0440a0040540300066201121344010190041c001c1415107841711052542c244501610841d1701c00043c4401605008030410f0000b0981c0540e4411603010010000075481d002001382c05500030054540010000100707400c1845503000c002e05052001986504002c51a000190300e221030040c5480115042c1107055104d01c10716000303004000d030800c2041c0040d8090999150846049003c496000d81c1714500c1d0341d0b1020003a0829004030707500e80580d107000003540c020320014000958060004c800e039540403d07800034003d0001081c603070300c0d603101c401260b14602c03001006100c000700a000c1440754030009004074800e0088102010149400301940d81414056540968003c040d0200781e81c1e40c500b141200d41d08010f03401c441b8103420500006840d1006000c090040034010300310b00c1581030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 150402212 1250 150400962 150400981
    0xf0f14090a0b0f12010e1c0c020d05011103070309050c0d02060d0c0504050603040c0e090c0901060f022103011a12040837110607020601060302031f0311010e0a0b03010605090a120506 80
    0x5043c0141a144006407016251f016440395a01c0d440c540c2c15112215085c047d450309070b004d410303950955464600b001c410410100c3d4960426250540250251540c624400b0300340144100d003188042e41004003009100b03442c6003960320494442a0307a141484c20702c0d88500008595510640c0d06880c050365402c81442a01d07070400402d81c0258100f802000104038680c045600c90405101d00400c1c0604000c406940900a00040404040007818000030001030210390f202d60b0428020800042407080441c40b4100006048427280754900c640c2229503950b0342d8a4002580c42403032441103000e01c0202034408080c4e60201c0c0c906241d1000041d174144200c0c0c030401800c2e8a03102192100541c041028000b2040e004141d550645025150241e940e80d24855120840c5d000d10800c3e0403030044800c80001406841c0c1405031171000240d0f0340e11044599101080208565070080b5807203003900300010030100d070051000b8010520701624060342c0507681e41e00041c4881105100f60b4540e00090108100c181 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 150403462 1250 150402212 150402223
    0x501030c05120d2604050d021902130203070212030910050c0702090a09030203040b04180b0a1d07120207050a0b0601030e07030206090a030b010f0f14090a0b0f12010e 73
    0x100c19280c8140c400414018240e440c05000381920900c2003140d00600341040d08200c0c0500f00800a10038400c4d0b081c5031500780e80d6070b8201020340d8014014807401c5400585c1c4c02e403001c2516038008020116180c025a01100207500140c0410203510802d001c10141c0b1217982d0103148911903c00103031003d4030b40e01c8017010580c0c20051400352828020410308006070751b80c0c100b09400c2000c1100025030141103180c1a80383d8800d603004140400740200340007548402111072031500d00d84000081c060840da10b010f00c5000941c40c0038a10310701c404552034040c2200204102a4009214509201c500120481e03000407a80540001c0c0c48580000a01c5400e22040030342c0903802800a1030204184031202550a85415581c00024071803a0300048403a22a610030f0417540155030001601156540d50707070035222542c1038600c01e440000725801400140000301c1c48840300380c110050040c10f403507034840810100400040c03202300e034000c0d01c0411104064032400d240820903107614000159460044400a00c1c00c3d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 150404712 1250 150403462 150403469
    0x50609070302090a02070606030b0a020702010e0a0509070819180b060f030304171c0207030c090e030d181209170613020f1c0b07030e0f0c1315090501030c 68
    0x3a8030500007003005071240d8801d81e0341301c01048001038485529181400c05060f00c3c0d40040e043e118500244038100080342d0040c002c803403007602c501c24a102c551003030121a41040c810258040b1009000034000741c050007540d68040000380294416a02e82c45209003184d000c012000000c40305084a80300b0800d5403e4083e401400880e2003d100316082030000f99a40b040d4081c512560440030450021039204000720020310034402182421425403210095070307054248005e079120b1603504000103080003180708030406a40d00c0c5015515200ea0394070700c48090704132009440504000602c0100121350350481100c42c3d10400e6568600c1c140c40d0100040746401e1108641e4025000103080c07061382c2402c80318010f0080c3e41691400d10400c04c140000b100f588060020141803081032500710100080309408510442c00350310108054131031200619594004001c9100c00c9234418001c0780d846181000100440d042c4502d0007241d0b81110380300d07101e1000413607800402c000c3c0c0c95000500070030a055601078041c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 150405962 1250 150404712 150404731
    0x141309060905062803081207020712050a021e03010c030510050111100b0f09090109060c0c03080414030d060909021302251e080309060f070903022701030f0506 70
    0x890400000203918000207081030301804c4081324030074200c484440c02101c015034020400540728888000d203415051800c81d034040040c0034581010540441140b008982d4581141c000c000c8210b182d401d11403160201c0c0b21003140306110015101c0f599909000354410350300290742c0455681810300d001904200700350072140c180050342034400c8101b0030000c1c80040d2004e21400118080e8050408901c10b03100710007541c0e821070031843c01c0001c1c01d0415001624024401d060070005407040f41822510500007010003000110311001160100d641c900380018403d4800003580d02d09483c1c0300e020003c8580a50100441c0c0b6120a00c4606615000e03601c00c07120024420700307500c0c200d00800600d01040c05c1d1082c40079819080010041032207a550328030078a00c901003130030321f1a0300c0d8a0300302031000b60000c03070f0b40e03c5503885000d000648402c0c026481500403801921140c541904650030030a098000c3c2c0100b100c04001e022407440020144407156000318050907001a40b400b282c1400303030034440b009103036400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 150407212 1250 150405962 150405971
    0x6070206010602100b130903091a0f0406112d160e0c0a0c05030f030109050604060b0405011202070519120f0207090b040e0a080310050405011401030b011413090609 72
    0x20a802151950314150180b034001622090303000024000c0c100c2104100500b8a030543d11f208244d00b01036402d054030782456401e0040140b03000c8102c140d20803040c14111a080c2848204103043c0160606c168071b42c81c4005480d07841c248444c5045d8900d01e0000381c0504112155000090207009000d0701045030b050310720b0b0180507420400366001c101e102500780d1120715000113964098078403890040303094a9204050301d03075490410801f241c9642003802111380d058a4100414107030715040c4100401c44034100181410140b5002c011340e5000c1c40d51031a5101640c080000d0f04c0014000e11062003103022985914482590508100403070190030841003060010001c0b505000e80c1c1c001a2620443d00001000301d036041900c0c011401422403640320003050311400e5011340030006484d010314420011f4803c004c1c10517648030304000030ba610a00c120910b980e956054518ce0b9482500f196402d4101030500301050b894201104255902018600c071186091007014050450a4003806008040741c140c01e00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 150408462 1250 150407212 150407219
    0xa1704050303061018030323120601032403050a060b0102070f050f13020d050415090305090402070602040b03090c090106030e0303060919150906060804031d01030f090302010e0607020601 82
    0x1d54920000d01158440d0241c8880510550321501070a1003440b44074019075501c503500d140103804038a00349a01688040400b898203808000d50040d6a0034481d0308040c2c12498642000542c003c02e10000c0d50b100540d20400c901d441400440c0c200c6000b10f100700000e00002140e0300340803049880700c0030b00a046420015081004441c6546d201083c5c90707080341c4440082e0002800075504030030306c100340b2840030b0020075140359824441c0d1040348664040c4500c0250641200000000c8504c81300d8004c020500c2072008565504059002e0a4402d200301c1006240a40302c11070701d81c46400c00c0700c00007020ba01a485040c100c1c104010305a0041c0320718141445520090103015451340002001940185004800203401d540144201444a51414010004007951011225400003076000b128481820400300290303261092001c0391041d901580c80301175541c030501820295646003000c82d41090740740c10700c0a00c0100c0520035816060b110340c00008803982e15490044c2401801000e40d002d40d0400c40042 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 150409712 1250 150408462 150408473
    0x306130e100b18011e050108070215060d0b09061e06090114010c021e0a23061b01110d0b0901060f0f0314010e0108060109020306061b0a060f020a1704 66
    0x40d522268080100b1000a03030b0700410000d000c0c200a4030f50180811000243e81c0050001002c20302c9014051030200c1e603282d00042d501004c003542d141c4010303070229003e0310302c036038074240450b8200f10020011400301e18180c03699180da500030349800d03550350400000d105400c0e00d0200d0309800c80010005909003443c0c41c90001d5081001449040c0c01c080218201220981c400e94501d00035941c0180400c03c00ca80855040e10500500b0b1b80c03540c0286048540030400e16050801d0035a01420071181c4030914010700305212490300450341c003014882e000400ba10b8079160038007a211100001d017058948491000700c908094820742916a03000710b420300300500c44164071545907034141205041c40702040ca0341b40001c6008000154144503180c84000c0081a0f60061031100c0307040759506022502182d0301c0303c0154040f84401d803500c81c0d0004c020401354000002102400030740726174071015a10a0f9003641c950710140c2e88a82c407018040359000074100400e60b0020301b5680b20610744840c414152400d907460 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 150410962 1250 150409712 150409723
    0x1080715020a1e061e0c110c0613030501021204030e0d0b0c03090a0501060312020c031203060d08040b180a1e170c1f0806010804050a06050c0f0a050306130e 69
    0x5010b00b2081c000345256011202c8650340c8081d80103a00700060b1000030380080d041001803240006003811b12007525104c42c855540b80fa44c0040305d4001d80b80d401030318410400310b41c2c404d8076143c1c0c12114800c0004046182031010b00704000a810b04e54042c0e1500e49001000101000e81d61441607003020442400b007403501070401da000f00904c40d241c0c0c4c2ca4603012505460403800c000010815803d0403000300c2000351242ca442a04001a00ec0701c142034000c3c0100340d2100700d09080c117070070b6141c01d03c002180340c681041e1040581d401480c1c858542500c4030008072083e400304280301103200f5516000074041c01c100c8402001802254603105100c5014400380c50368914603c500307225509400003424a01d113050140e0140c000c0010301d01c580ba102e1021542d503040d40c0103030003080891140300029001c1d5020f070070030a1190382d0050103002042c8155550500800b030141154201041c24425001244140c1c0300070844c0f54440d403185501ea1801008016008409488600425040c038081c00c0e220b00c0005007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 150412212 1250 150410962 150410983
    0x1903080106080a06180c090f0303121413030807090e0106021510050d0609020604211104020a080402091e10140406050f09090a0b040605040b07110c040905030906040801050108071502 80
    0x1801300c6c9540e0110f40844c2d0000e516003201126410504001040641000c0a4800d80e81032202c1400940d03000c44c4c280c0e102c0e407000c40da4200d0b421804c3c1d0004001038840c68215038400c1550520311090764407903c0806900e00300360840c0c80982e000f801554a209406603280f540110030341041c0c81c0e96820000407030076000007908005c110940b100544c00441d52031070b0550303000e00070f00d06e441d1401c40307464031648040d03020308034054034581d5580c900345d0740d5411700740201c503c0c1c1c41c46070b2110f0907507844603070a200c01154010203010550109241c581002030541c0407150180300c10600200700282040411000301c200f064200d4406c1c1e182050401050b110014802282d5200702c4400b1525945c50480c5420070106c600002d041d420780c081040701704800c6600280c051409403014900690b9414410b4501000d504594699544918980c3da518900b07600b01c034415334030810580e410640d040003c110190455000007009944a0005000401080003140d0040c1920514440c9030b42c40b0160282d21040e8070107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 150413462 1250 150412212 150412259
    0x30b121902010c05030a0503070f030204050904080913060801020c010c1112030705040e011d090105040f060b0406031703010501230406080606090607061b18090b031903080106080a06 80
    0x52500c081d68029501e1030041134110003641d540c2c644c1040005e01c1c5500844451011610403030400701136600c00d00c01e940a569015000d072032551103079110400240c1149184603130041c580700403034203415031902407440286942000903844004ca848072500703544c48030000608212050102034540c24000034032030845540c8005107503803901c070503404560601c19a045001c071038102314000246402244019a0f0b010b03c40f540880003034072801380080c20703110140c1300585410000045003010a42c194045000f035440180f00080304c036920b98581166003007140004140e0b1f5008401000596085a05408100c5500e25001d41c4030344100040342d07850085001e040c0c1041040400030310a0380f43c4008842d00d0340001861030b5181c640e40e240c0700780541204402007264540303080e503c1041c1070080d85400030b2071040c5100c1019003820240108010175000300703000d9141c0f145224103c000001c501f84219040c5c02a13444400d2981400030103002004080c043c00281c5d480e02d101081f51100c002a814208000007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 150414712 1250 150413462 150413503
    0x60304020301090209040803100f061e02010f110c01060503031e09190312021005070f0c0809040204030b2401080f52082d010b040303030b12 62
    0x1800402c2c014244814001d400c40c000c4002e10042c805100c001c0e51148001840c140b152079120030003410340c84090b200c0d1b40e01103400c9086285a02c00040305a10549105e0310001500060790004070043d00c01020f1100c0c01100002205a80c40170f003800350901400042d0000e510b010a100c0342d108400b018600240000b090200d062070542d90750000c4034402c8425880e13081d040586034180005100c101c03003400d80251040c0a01000b00210301d024452040600e61245d62024040e80c5041d6003038422004101e9480e00200200c02242c0c2d15480904061401803100c100c151404000c0899007854041e81d00e440b203858003d1180740c580e0306c1603005a00442800d84140b075070f101d0f50303460304003040c01000c2d03924411503405d4604889441100502e103450f0100c400400500171815844a00680c501207010016450f4070016030700b0203c520107902d0781d01c01406050120054040402058082a000101001c4001a040003419410700540c840d40c481112504ca003456002415652000540340c501e2010401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 150415962 1250 150414712 150414721
    0x103020307060815061902060f0c030711070b1306110604080403082505010209241e0f07030c06050a0b090106030c260106020f15070305040819210b0109050603 70
    0x50300211380440014040302c0e11200c2c01c1c014000640303a031400510040c03042c07a000403c5136840801c40f60003203d00f11007151568403208401c85060002051400441c4240200007031400e940c0d5006060600340c2c1c2020b0700c10181096401490082c0d1208914a00d5121000f1300003c41c0c102001c4800316a0300c03050096580140b803050345101616640504000b43c2c80400800501c00190010700301080c007161a048003801e0019040c0120b03d401c601c0c07035054801441011044c0d4007540310403d01c5025108506d0420602094000c0c0e550320040003100090020b80c040e40c100045405000d42080e0540c5041c005d80c500300d0040b942d88541481200105a12081440396007401180e41c004004002d25958000303180701c00071910018000c2c86400700622070000c0e1800c28100125000e01300080b0030310003000c10b403100d0fa4220301401d80a882912040b2082104c0010034803016101ca015000b1920707514441100c0a8414805c01c0030f642e030800c002c03400e0050b030102c10f0b80d1242d0740e903003640d900720b613526181c0e02d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 150417212 1250 150415962 150415981
    0x2030414010f0c020301020318010b01020a050c0427080703020d0306180932060108060c07030c05031314030c03030906250b07120c03020910080a2405150301030203070608 75
    0x83c0d8040c007035015440002032106c5403110744213141c880ca0b940750081c020042150f00483ea1007140a0015020340c0014140003a1450640c100030303000ca841c9900d41d06210142581c6407018802c1610071a80c000f800100b0004254051040a803a00074506040201c146031030000004000c11100b041c01e01c2e55500c03c190f041058650196800800112310141407185401980030034240e00c04440807a84603440000030343c0580002d10f00c0c41034034803102050400c0c016690940c1c0180388c0300802c072000d002c280814000b050048070309500906040030f90600c500340c003030705043c1008141040b403402504100a0003100f0345070181140c414812450320101550f40b4141d1702445030034091001072207052144140700040f5800031420942e25a000c40810080088a4083c0e089214440c0e040390085002d4a101900340d0040c0b088540c0202c5c80540400d40140d2100f0030045060351710781c2e0251238902d094040c0054106175107400500c034128665545154115000261307500098451711041152000006540c2c00c0b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 150418462 1250 150417212 150417227
    0x60810080105070908100614060f0f0708030a14060108010b0c191a0a020909040b041a0906070e03061902071703070c03141608090604120b0a0c02030414010f 69
    0x4400e0020021401c0460005040d06003603c5255240e1203503034240071960700700d44074542c02c50380d55000c00c800b00c90300030007484059080641d00390701105060011401c0b0103a400001c25030f5034881c4035015030707903c0d143c05d44008440284284080020303607141040500e98101e500130781552004119507481d54100240146002881030348011483c600004140801c4504100c41c2c5641d0b405021908480c2e0f100617140080340100c640c3c1c994081031100c085408112002d001680050180c0b40c00e03148140c40c581400701c1c600054482c2207555000c1003c21006070340c8070648003000d060407000b60640d41800626088442070006885004550008840c000c0123041100314040c0181001504e8591800900161906961130000d401040f00070754640d40c0300300700000b1100f081210000e66034044003da03c3e0f400b01c03900549070301600403104000103c1e27003042800d402c51100d441195640c0c40c5140040c0c241007650441c4206105542c4207200522868031031170750101c0c6003903083c44c200c40b2103848080103c3c1d044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 150419712 1250 150418462 150418469
    0x209040617010e01050601050a020c0603060607020d0f0c080309010504050906010c140f190339061a03060103050a1401060306050a020c070605040b09130e34060801060810 75
    0x71444110040304000040d04a5009543c5203002003001e9070f110310042d2540d2240c8611400103030401d402c01c81207454004041c5401100c0540340c0d606001150b0b020526110141c5001d031035523080640308000300054480c044010b407419101541c141800500068101d008500070180300360340b07940003e6682e034410280f804036140c1018591b1003040d401e04074140c591411075018a0b15001e045a4070380c2c0c4040c50781244146030390540e1808104c0380a54100141100340c030b41034002c1703903000950f50070700000c501a400e81d00c503000e28800034185500c901820b105108040b0307024000d42041d4010804140d003c1400c880c826041b40781d0001d01900c044959005000e05d4000500315450700081c00300504046e4068505903e0f040200c03905161905016a0240100e12070811101c500300681d0300581401540300560800d0b4001c0810a071010304622400c1501c0a4188900161010031004030080c00c20514020311088400b1210f001d0f06000c00200035190500494050110f8400401d001c0c2200203a940c005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 150420962 1250 150419712 150419729
    0x9061a18220501050105070305071212020c07080613050601270203150108061816050c0304062102030105060d0c051909180b0a031103120f071509021302090406 70
    0x2003000e14902038000c1e4090205040c04030b00d82400403420354002c80807141c9041d059210142400c4a981d250340301005007114032010000c0c840a0040071104500141c907101250f040034200490400026500d416402889a443d003d01040b422011400101c0c14906442c1080401e0710428100600e140c0110405a50b0000d05440001003045100001d0280540c1710001d907105603403070710b51900b00024603920040c10300300307400103030003240031201420030440707aa0301a400e11604007034443c1007540c2103400603403098000c2000d50720754441c204060030890074508401c0d0801c5007154106400f08919004881c148030b500c60750741d034503035507101c0c05401924902d0040005001c694039a2420003031000e0118482c000c0c483c600d80c1851612a011405400d520342000741110314854034548555484520a545441c0c05000b140038030044003140800412000100150083d030750800e074a08842600f02c4511041902461310004500607034400601011303012001d00c0140e182e507000c000050060883c0d5000c81d41 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 150422212 1250 150420962 150420979
    0x150308040914070e010e04321611121602090a0c081812090a081009020a090504030206060f0f06071b140a06030f111c0609061a18 57
    0x240da9065030402c9282125840c8001015100d201040e10110305685159022548070340c2681c0143c206030303129045407074a5030101c030301c48011035410300d122491904084d18000b4094040112610490251207a0a402850035040483c442c10301c03d600c0303c0c40e16900e40f40c081030010343e20490541d007840051240360020044000e80c100804000010441912011b020130782c4400000c8554504907005240702400340007402c181001030b9440005a8840308210f07074841914031001c03d0140d41040003964051940500007101e0f07545004006041d2825404800307898100320030000000d50209000d038000200340d820350082a2038800080c106604000d52540080c1c0101d03a041c20b01c8800c01f0003003255802500c403840040d40300c10408040144200300135030003800e800380030802c10b031003540a42003603000308400107080040300d4901c401560102040303ca217040030009211310b840c120b00c1003100070010041c00b0400e070351500380419640d0b0703440d40d900c00090b10302080c800359245084000c1134050f10010000d90 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 150423462 1250 150422212 150422219
    0x3030d060603050f01090e0c040f11030403110f0601030c090f0f36080702010f0203090418031101050f130c09050705030108060a050f0c2512030b06041815030804 71
    0x500030042140d0039810702c0d12044c000900101d4510518424001e803202800300144100144805069890a103010f403540c2c6e0580ac2250f0310101c00654000c3c0d11960301d8419203006000c4441c0760044c80700c200c8204d5004800104001030031201c0280c00c840035440082119102054060010b000141030303074422500305525080902e40c1c1826145887c7d90500c2e450140c548a4101007122150402004129003401c00a01d00958004d203180b80000d03850384110792401212001240946498044d070b0f0550040c0034044d00c0405802c80c1c1c89201d2848904000c001500d842d00c510883c4250250008000000140821042c41f0a09240002804143c81c040c441814100340003403050f4001d01c104401406158082514440b060042034000c040764500b003407503602d40140309806a4081480d10040300f550b00a40c0c00b50034607e0840b400741c80d025215201801d0340b41e00c00035080e07408050503e80b1a0000700410311915212401180740d01100a000180044000e54224221012a04050300a910104001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 150424712 1250 150423462 150423467
    0x1260a080417070b0d0b0d050703060b0f0d0b010612090503040f031e08040306052203020c10030b03070b0307030b030f0309030d0f0518011b0b06090f0f070e03030d0606 74
    0x344102c0c0c520741c1540d884032424848268846405008107100c021042091500700402038122402800004184002100595403620f28094040e0320840341541c40b841c5968040c43c01103200e23950b4410945041c40c001005542c0d1809400d414001c190600000d2401903c12807000c0d48040e070060342c800101c0745e0355502d500703203441c0c050600d100884182048000c14009501060300c01d0581ca5805280301c0e0501c0d0455030f0391005018005c10141c0700da1302e15040424403110050300070100754065000391407048455014050a040701c008d154080c182811645051924001600011500c43c80030700f0391207484107002100500300e05120294144a05010454580030200c018080310604500b16295007401400541318021504072a0002c91018000b05c0a2142e0899130b0414800d0f05141294a1546461225280114490007a21054554420090349040410310b464001c2a601c03568095482c000d6403800c000d13500244103004114286500080684040007582c02c58082102c0501280b610361100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 150425962 1250 150424712 150424717
    0x1a04060e060913080301090b03030d240504060506040501030e0102130b0c0d080c090f0406050613080f0f120705070503030706050a0507031a040b0a0914040c06080c0301260a08 77
    0x1c1e0344141410000304582d1416450052007280d80011424196881c2200703410003029650031f95030300b5000410503207103034003a944902c01c91174800c002d1041900f11a03202d4000203140c00c1d041103000d146001d0081c4240e80e0780308203a034115582440c001c80c038004604419406030060400314041e04401e07070004500480588058010131000310102d03810480903d1044444000c140c072030380d210741800c0056000500340324078004550107000d40080340c41680d6002040e816071000501c2201c049520301c042c099043c05200403600c1c1c1460500420b4903500022105803621504203180007603a4001683d1000c1200a000c104001e00300181682c1e1203c02606220018100450320b0040e402d18100004105900078030680d0460390342d60804e13201403801c1c00240300041c086045080c1e48203035104000100014507000709542841d180c0e0820303009041500c1d00d041c90004940040007444803076800c0000c520070400c00d5074111070f03030030f03804050501c6a610045030b864040116402075000c0d00c00e07808203000f5403200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 150427212 1250 150425962 150425971
    0x408010603021002010c080609181c02010b010507081204050709020708030a060806090d03051b030a150e0c03040b22110a06050c03041401091214060a06030b07031a04060e 75
    0x41c0c140581100d0f0300101d00f225100c10301c0d1b82c085500103011885604060f03880e1944a14a034208003000700c980c0452034603007407003050502c4207000c141c45605413080d428046d14101c42000c1c2001800c0101e9650f9054190061101e801102080080002c051101c00c0051074010712441b2011540d4011504020303095500c222400c0b400075080c039800213000c000000b0854802c40302000940034010350100b08a02900c800f61413407078880802140c0c048104507500045000c0c80b58036100280164280d001001400341a0f4041e01d4541005420060461560700460360701c04e90204032449640ea900c03009150404904d0541e400d0400294003800400c07850710780304000031004803880c180c00c550303904044900d40301c0e13180710520360780042c44200720000142161600307403041410004000d940b0ba103a07003031088280c08810790312070360b042c024610f01c80002e212a54018035507101c00d0111505607240c030a04808042c000c49c04159840c0c01c10040384a503801d4006c1c14000c010001c2c40700c980e0fa440103806000d420780d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 150428462 1250 150427212 150427219
    0x1b0310030314030105010e01120e01060e19020405030a03050c0115030602071b050616050705101d030703030c0f0501090204020d020c070503010504050d0f0905060d0e060601030c0909150803040801060302 89
    0x1c82030310803200302d0703402d0340e0480704140c2d11040320603d0302c00111004814400c1003900b030380d03c5120044414100380140000350091004102c00c80c600100012030001c9020303601d54010744100020f1003561004955610403d070542019561030070215104e900402920740c0400e0018240c020120402425400500c4014003802c588412014816a240188121441650f90014003007240c0d03482c100d1980030303141c09180120292403205a4030f00118900f81020f40c400000246000b81c10300f100030403030b9440c070603180c01540148001d906541e4081d1a0940c16080a407403800d00c1c2140104102c4250001d5099580c0030300295292080124488040d4010f03003403c0344240110803010845090500ca1039201d5600320000f4600d00c140e40300c042e1444825242a2010856014408565034480b000102030000340f0410008099511140407424020094900c41c101824020046c110950000303860302941d60103100043c0079803098034018a507880039804190309000118000401c880d065000034201e03802034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 150429712 1250 150428462 150428477
    0xa05190201030b0a061d04020d0606031d0f37032c13020a140c030d0c11060708070302041d0708010f0b070305210a0c020d0c080904051b03100303 64
    0x4104207a6a004d401200006824050f8040d040c05024402202c1c0300d002600061a040d4540513183c10380d2000d17040a40802c0c0c03070310520001c0010065601409102c1180607010741c400c612384040e00e0b480c51800442184100d001050080d601d040d10b0741008205019000c400041c1d5440c0c00307440c1c1e00784403041080742c1407220045416102d03e284a41c0d044003005000c5034903918150307800d800940100d00110200b10203106254a000400b5004017034040c0840700440d16010030f090307200e00755100244510204600520a001c0e504000195140c04c0561030500c0b40559035881421802806168011615808071001d000d40364848080c0640c002e440c145c0d50103003983e880304094800c00380148205052501c04120020102e03204001401400381c060058a051b4188013682d00040c000039108035007000d545a144850494041101c82c0310401c1c1c0d030810b240100943d032030b1880300b4000c2c0d4551070701464441001038801c50f403102c2c452a207204c0c0d0321409904c03030034040031841e8040b40364041200411100b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 150430962 1250 150429712 150429731
    0x90c030e0f0f010507230703020114040c090605040e03090d020f03100f0c030203060a090906060b0319060512070e040516030305030118202803200c0a030c050a0519020103 75
    0x101d181d00440000c0746c0072642501c640d00c1503203a5950100105030115582c450700c882c050750700724140c1d5001c6d41c022815101240e0400f1800c1080342c5050784040e216a10b440c2101c042031401109942c281842200c002c42000381c24004102e8015591032215818010b001d25490303a0162680314004a0200c00c00801600c1c0c1c0703400040e030481c0b2040c1c1c1c00b1540141103203001c0150940f690000450b5510980001c51116500c004264041c2c000707031503a1889450103120f10990071214400e101c02031808070b40d10051003515448171900c5403464003510201d10b41000020b014050f040000c0c0181c8080815040c55250303403410010708c40c0d0804c4c040c007001c0a0034601141d51503c02c50103031110501d00e000744450600f010344444645a441814808120b188580c82c182c10908607840703010408103251000300344240030300340d1586880c10030f00d180c0b000c0d020103104c02c42c1d51040c0011700d40d14003541801e01907203514990410b28644840c9500003050b5105468086c3d000301d111824445155200382c90500c50782c5107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 150432212 1250 150430962 150430967
    0xd020a0e03070b120a141815100b0a020106150206010302010810031a06010e04060807050f0108041709030a0501290603092d01020d0b1507050601090c030e0f0f010507 73
    0xc0d40c425551404000d0020b880a40040c41c581368200050079000252140e001e41050040c00c01129121100019001c0052220405020403800b080007045108006e141c40301c1ca90198558600038040780c0400860b5100549000350f0064002e00b5601000b040502031500000b50344c2d0409001c220b000503500000310b03590010207140d00013540d03800800d100c030041148543c094203100c000e014078104020041e00c10030b81d485510800c4040e18009001d41516401c02c0c05000d548480f01d03085c5810000c44a04107c041002803900904840707151408641d16482ca0000030303e440410b91014001d5482d00c981944401040c4a280003101455440c58a8402d100410440c0500040b5007000c0250012913050b00d82c0030700c4148900b40c0141c4854490103801124803c10300b203800c10400748090707664801078002d540c6040840d030483c1c8114040241e00e03041e000d07614141c990f00107201380002035443d055401e42d054000c0d008502c10f503440e501220080321401d00781070756640700c01001064039443c000220b03000c02e1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 150433462 1250 150432212 150432223
    0xd0503040b060d020d02090f180a0201021207050102040302120a030305011410030b030715031406040b060a0f030908030c19080106020a0206070204240801060806070e010e0f04020d020a0e03 83
    0x1d80141898500307503500800d020342d918103070100300d0740048800c1480340103a40300c101190044080170342002052500502c800410a0500c10001481e4024500c1100607a40090042c0c84000013150b095298030b02460298060701071500000d500103420b01c2d5640d80820000b44203440d0178000e1342e09120a0b41d039040802c0c0000300fa00d20413500f044c070500112020f640a07412030b020f20000a811502810b59400e2070b1489000c2c42c50f61180081d4641701034a80c0b0520f1100210f400000489042280b05280f0001a40ca4403d0418240502c1041610306e00c60900940c0441c002c5600100c4082d604d18014000e0001e9500c01120340001d5240403080881c514412801070307060f030b403290b0010310060b0326035020040142c02018007280c5c0b180d00e51900c0345090400d001d6003c81c0c0100d20310582000750921051509640843d0002d8485600080400000aa100748a020250001e0030810f011200b0140850501000008041c0e005800000c401040c0304140e4010721680d00c3c0b6982e1440600d541c0420143c548 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 150434712 1250 150433462 150433471
    0xa020d050f1204020d051603031706030d0f021c1e0815220207030e03062503090503090d0305040501090806040b01030308061807090302011716050c03040504090809030d0503 76
    0x7254240106040314401c25240c0d508103000601d0000c0304010356440500e04030100310015805070a041d0f007001015040b40c0300c1080e0903010a45d0341002c0c82c008021982d610250008141088412082c100758076000340803803481d0f160100d0302e0540d030310102d031300c058010040300c1c0d08260440c0e4248002546140f00b20b08850003111381c1d0140c0c000c602e02c4002080110410281c1030380503e0b001c1d80480100d54118070060160603c20785841c08140c80400405041040007004101a010286001c0791800c0b01175042c800400b00313500340041d0342c46039402c0c000e05c0d40c061415419081240544881c0500d608417002d0320032500c00342c1c2c0700304602e900e07410342584814007610000e29080f121801803001900424550f6440305024050b01c44d4405030b0f02c401c0154443c10380b11040401c0c84500b0500940d64005481c0341000807120502c101410b000700c40307101123030380c84607058204140800c011404020034011200202001401840300100178101014280e21444101d4400d100d40019548014000d1003500e105 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 150435962 1250 150434712 150434737
    0x102130b090a05061e270319021005040e07020606030c030a08031303180e0a0b09041110051323030706050301060302070c030206030a0c02010b030708030a03090c05090c0a020d05 78
    0x181d1900c400e201d4950425400309040d0b902503d920903505c4050406003850100b100a802080c5001c01034510030042022452030003508a4007030800719040c0d50504803150b035815580c0092515031000100e4a50245802640c4000d240c4030501c0403c0b540026054043e0398200e050310218611a8101955540031002c024075442090002074504400d0a0801000f54000e04002d6200081c10818400c0f42109070801c0000305200c44c00d2001300305a610400400d4030f0280c0355200380e03041517151000103003d01000d00c3d11a0300f0b445907135460b0038416410b17544421052288640e102c1d40352105241c810309500d4a03c43c49141358520060103280000b04107003217600075203880b865039080550490180d40701d003100341d80001000030000b0050b01d564008601c5582d8003440090b1031030000300001d0958800b010428804c2d40030f1305007030140c02d001004030b503107001070381c00e0008000d0090320f800703c8040758607408ac81d0300c182400c00700441c0004890052010440c0d43d826280311801290064403c3c0c058849815031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 150437212 1250 150435962 150435979
    0x301050c0a090608092506030c0504030b0f0411030d030b031002041d0a06030b07030204171606050d06030501050103051e07080601090c0513060302090a051f0309031b050102130b09 79
    0x1d9140921000c94124020901b52144000f0b08450849800e51510400a000b002008100401c0e40e0500c181002581c2c203280c59031400703155880c0c24034200006419980c1e0164000d02003020070850740441804103902a05548140d050203c003d002410303180c03a141e0181c0500610071a2119103442103406440c007001013035a200c0008010348071190b5008081241d440d0750303139002202098824400c58480c0c039031581e0150f591401c21242c03400b02c04403010714030b460398000400c1001042c100149803041d1201c2d490305944a40a80c0710b182d0140a96a002410355480c2c04004030600c0070114103510600208000791640031040301c891641ca084600c48c00500d9084200140001801c940003000944e000e072400c5814800100040e01c0b400301c00c0e6011102181d8001980406401c0145411005090813a40000740303e102490102c09810408031303100c1015501c0144c0301c00c06004101c11007100d81501c035019400c50703261030654000d41c0481000000032542c00c40016180076141c08039000504054040c68 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 150438462 1250 150437212 150437219
    0x405041a06010504080318010f0c0b0f27030415020303010602070303080604020c15010306060b0a02150405070f0b0a0e0f030a02042d150605030403170406090204020d02090301050c0a09 81
    0x60003400c060481810404200400680314038100042c0c240c0d01c1a2244003921245100000b40030490312400c450140302040917400c0210700c483c41a1548001d0038004a812941c1d68080302c0e01c0040141c0481014070080c80f4401090603000000d070081d00e480d61032080752414044016650b90000f4403a200040e07105000910000b0310640400342c00c444050000350400b41c801e034580d41445031641c680304041c0764600042041c080c0d280038540081020f18609803400748104002921211041d03030344042d003090f03040450304001003000404001d094100070900a16268084880980c4c0072288100010f0014101c24101d4a4219041c80e4016002802400c0d0060389034244005040701110301c030610131b000925404090300303280c2c0407222095241c000107036030a00c0524100110b400c582010703017040720510400c40000d030086004084030501d04d000003a01e55a910b480409000c1602000390040c2c00810144840300d242d0300035010f082030440083c481669000c041c0900c0d40140700840b03000604115040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 150439712 1250 150438462 150438503
    0x90a0504020619030f05010305010b13020a02070519081906060803161b0312090801140105060f0711061c0c02060403050a0e0409080403080703180503100b010201090b09030315040504 80
    0x1d81c80c0c0f40b142000320700c18100300b07402001c44e2002d034070030754050351a91080b400c80d15009606050214001700b0450034420b10120095840c415800f41074020701200504c084400045149031008126078022600e604900d040341c2da40410f01d4441c01c444c80c5040040115440700007205407800240c039002981c7c001c0c0401e40380d4101c0d0591074080c402c01116040d6010010130011760806040c070415450700e200403850914803608440603c030044407224400c2005105035074486040300d0722200c2034a6503541350002d504102c0c0c20103114420056002600107a180c007201203045402d140309504805c10044c031289600160f0303d941007250002c000403020000c04140078041d140108031000040c000080700c0e03411340d684107503e0303005400030b0b2081800840c0c0c1000b0598400c0c0310303146112801d15502c40040c030b0800840d03a00d4017410b180060032511440180f07840d0b4803d42c00090703200d400c1130980c1b20505020904545946c000d41e80e408541040307010a10a5081c079008050207542e00210908540c035100454 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 150440962 1250 150439712 150439747
    0x70f05010e150d0c050a14030f040f15060807170d0804031107030b2403120412082b0e0106030803010b0f0c0604030203030f060d0818040204080102041202090a05040206 74
    0xb50814000300f4030440d015040c4038410000e41e4107007500d4880d50368051440140c95540074016a604a0340c040007088007142039180c2068000d0781c0044030039a902420300e8104028400411641480791030084001000c2c0c1e000168141102c0e440509400c0b405001081d20f9201ca0b044024000440d07804004100041d02c188141c0e41d4544810301568007440d12503480c810007041c01d0b101d072440e12001b03105c21811100b2601313208084400480081503d00e081440c031840e40c1c0154800c1682e0070628011000911800e9401c50b048100e005054411000c41c1d401c0e03810030303501000c01e540092403034423442824a107014450700050b43d03002250745007103a00c0e013098051594461103020105d0715090162260010302080b601c2c0c0950300c680c01035601c0f4604144410301c090030007424071f480358500c5d0850801003800d000460780380414181240e90b1050304000400c010340304952014000f584002400202188411400281c40707200306c4080301c081e01c0d900144010ba0b001074a01a40c400000c01c40100d00381d444865 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 150442212 1250 150440962 150440989
    0x6130201020c100302041404020702130b0307030b070c06050f010f17100207030c051005010e0c1803160819081629040203010c021b0f03031608040602070f05010e 71
    0x100ca0b54018a1008100e4609100007402d010035004a400d200744107001044031002e590984086003002c0d03158001540d11413031007004d10030442c0ea460a42c0c4607510144415009560403281d420240e00340b0035401081e01046903002c7da490703890305000c03640480c21001d4481c12202238606103984641802c11000c42c03038020780c403515001e20030a4910805600c05001400d056402501c844070b075141035040443c18041c0030350000e4045072614005020014220401d242c00c50340502405417244c240c1d0704107070250418042090740c10300c140040383c1108410b101004050f12410b40c145c0f00c20501d0700c2d610080701031050b080142500d45c00e20031048108240341800300707568000c00850744c00340815103840030540f044070054241004003108100c1541404d0003140c2c2c2002051005143d0b0a100240300054690132200c080e100f091600c14410140d42c040040e1a1500e481d80c4815905410501d81008264001e124000c05070003107070b0303000032596080e004a01c1116810784501e03074440507032020071000048001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 150443462 1250 150442212 150442217
    0x302040906060503190e0a0b06060c010614031905151b0703050703080106051c02090105120f040204060b040602030a051c150303031508031603050c030c16050604030506130201 77
    0x400103640e1030034080e800003801903485041c0e907402e02008800c060410350a6981c82503062501040c0140800503400c2002c0d500045144601e0f114000041e5207442940001010f6600b0900c0200701a201114401e010400440488080001128101041c031741800e0b400f820b0358100c1001907144580c20249aa4800c102000c403c4100314031452048807900315030720980c0002e0b400705200c401c150304031074218003500382e600701141000c21408420445001405260040d00d401250100d026409a825074414143c5800002214500300c101d0202c55078040740c050741700321306081c4002480c48546045409a070092707400b43d803900340344460a4400ba8003446000488842e192100009181644120040201c00117000d00300b05185050080948000c280041c4120382c400c4420005190004100d40000880c5182e2401041e60313030400796403500640f41104503d000c0000c0c8000e140001255601c40801003e65a040307040e00d4209218103030040d408001c08960064004c190f0644840540361201841407 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 150444712 1250 150443462 150443467
    0x20a02010b090103050c100503060d0f060b030a031706090402060a0f18081c0206010807300803090d031503030c05070b0408010c08150d03080a111801110a0c0b0a0302 73
    0x1080b024442640192120713040702059a00301d103406503405100d031525182442c110f04029001407010300c4081002014500703501c01076000c224998101c110072001c01030645001401c5400d014104071105c0d010800d15541c450001074445c58040407550045401401c00c5042803c444015101d03000740400711014030111144202e075440012020340041c00012000d481090003020104c5511f10040c1020019500001c00501c00c0302000141c59040b04c0c8080c403d4441d5110b48055070f014145050301c1c0003401641c1c41d41040501c01000d000b50701520324a8122003501b054a10110704031801b845480c41900c0c0d903001c08001091181852804c0343c0d000e0402d444003a682c2d045004065031165200c3c2c81180d4548095004480c0c0010b0703602ea2185040007002100007040740042c1100003d5100203042c4014000803c3d12074145901c0084c03904507801080350307a0707a20519080180c07036525206038001200807a030505040404944080e82961004030b10060074100200c402c05500b10185000816a09 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 150445962 1250 150444712 150444731
    0x3020301020304060b010f080105150715150e130b15062205030708160306050c0409060305030403060f181103030f0d06080705010507170a05040504051e0108070612020a0201 76
    0x1e10003180114132400000840c006540009050704421104040500101c40010803031500c503d00d403112800c600c2065542d41d04d60034a481145074241e208e51314456440d0800f2813988604402450b41a00c0302e40c8101500d541c3c80b00d2000c481c0c2c004a1000411581030789020a8006040b800741d04050a4010034150420400700d07004081c4c0d51020001241145981800300824103050114074043c04046014050140ca060310100c184101c070701c0700514440e40d80000400d07140380102540c019100b03145050000f581c0d09c0c10207035581e0b00700740000d0701c84034074080d40742114203494840c0030307589440b0746164062400030b92100c0176440c140c1620303940c240c0002c00c200081c80c913444c0001c0c080c44019000004a060800a1182c03500c91203800031410301108100e00c4000c1080e00900611065400320460360702c0c00e2080c1c0031991030155622844e000b0741404144605072020341069442c18400c07071042c1d09640c3e030722510240e03280c8843c4100b40100305d080c09144203001d0f1a40080c6004541742c000401e01000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 150447212 1250 150445962 150445969
    0x210d0c11010903090e0601020d08220803040b160801061706010201200301080709020f0412050a0b090c01141602090a0207080403050f0c0103090c05060c0a0819030f05040b07050c070302 81
    0x84201c0202c0c00244d030080b09000e00b103a0032501a82000080c8020054509600c0000c1c00140c0058051101d60780311072850640100036005c2189000c0d03200042507100d05143c0791903402080103071095407600c0d4018100311000c1d803107404401c1c100d4845030307102c10081c080601906540c0202820b098115500d40c6000000d03402002110815600b441c1c07000340e540e40c9040e90240c00c003800c507040703500312a004011807901e0025481c10b40b026150700c0e00740c5602d0842c9500d41130b03140c460711a00090051103600d0410140c460701041454a11400380c07620780798500e46030000c461903c00c800c198400711503e040800c2c05810b1043c0da0030b5210380300d94801031401c1001d4403141403a800c580d204552070762189141d0500d441c030a00120360300d200d0a0030144825901540c4c1c2c644444a1401200d000381000304464006c010204034140500b03401485290366900e5a55034000703c840d042c03007102c000c203013800315404600d500c1d486160701c1103400032605022600d8180049407650b00001d503080e074622a40070080301503075 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 150448462 1250 150447212 150447221
    0x90c0801050c04090b090105010c02120c031207060c0c020108070318050a05070501170105060304080a0c0606080d0905090c0a030c050409050708041110020604082101080f210d0c1101 80
    0x10221034a895901d080803100075176680d40c01e514001c0906000404c01640c02407079071106603904443d001e0807022001d405d986013241d81e01c051070341846400c060120150000c0010a01c0900130300c42481210001c0d001501c0400300392900038001030302c400000f06281c0c407130340c01001548605851143ca00505490300b0303180c0030301d186081c0d03690b07081580100130560300904064140700001d100f01c3c0741e542c9460005101400010700140c100400001e4019081c3d118090700020b980d0310100801506840c2c0d040d062341d82c03001c1c07005d000106040c4900030030035280402c1da0b01e1086812407803452810308144000c401520b043e034280c20600105200104041041d03014103880381800717960301c1c6201e14140c00d200001c580c509800343c0c060035904010410b46640410843d51064200e0910b83d991050118103100010305440f01c602d0f58000e500011a80e60008036030821221892800c5071140d514500c48500c01e000004643c07034500e1000c0000040021480d00b0242c00c02c200ca080c807a00c250b686607440c50948 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 150449712 1250 150448462 150448471
    0xc0a0905060f0c011404260d23060103140103060b0a0317030a1116020907270302040c09300b070c02011409060406030209190e070206090105040b0a090c080105 70
    0xb1a01003600c2541d1107091003082c01e8000d868040d142c1500f003907214450f8150f184504082c9900c0201880c00d040754586044581e02e4440000420600903680d0112050740750415a10b500c409804012034540e40c803038022111505401c00710f841d05646155250f1004041c178001c0903801c8030440710300002066803102884103d0065a83d40d44c2e407450001800d20071680240e4100000d03000501c0040e0741ca48091034042041e982c1600d00411a480303400042e44c19498100003001c180c00b401b0b11007500f10082200b100103ca03c00da4003032207107031300c4100103039510b40060241e2440031000e000400d00a4040c0484061019200c070541c5c100002680c49113549194200c4083d07002c0307159000c2850855a005a1080c4126174504440e41030081d0500069490311036032007039108258020819054581e10443d020f8529085180c0031540103542e100d0141d40141c0c01c44480000d03004000002d10360250602030703244515401642e641041ea01c80c140c41000300544a41510070500342ea0020902035400d20500340503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 150450962 1250 150449712 150449737
    0x209040b0d0b04030212040b0a080907170a1523220605060f150a0f03020c0f150a0501030503090d062d0e03180f060c101508030705060c0a090506 64
    0x2d92600b400c0107403030030f03504100c4100342500800080000610020666469402e249000451500c2e00340380e8500d0040c940c0c100c15a401d03107034400f0148101002800c2c520481c4101d110400c2580c04109200444038176001e1000c09911403031080d00490038031880c0030790109640c45040d10600200c8480e480524038030404850311941c072418000d8500d400c3c2030039861610122032001107a0b500b10340444a42c0920b0604505000f54680342d070450324005e8050310040400a0200d4000049400b46181e54000d403030403840344032540b60046200000907000d0035050700d4203d4011840d003403800c01402000f90820600741c40241d1340740e50000401170240144412404410305602203446034803110fa0813610200c3d244040c030307030042004000a507000d00340d1483d139450031501140045824070206400340320b00900e002c0725000e00e02030314000300400d130b00c0200711010104180381c65a44910700640e40b0b03c0394100152140d402035000985000ca40c80050462908134074004803442c2e0344901140c05600b001c5840780c039 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 150452212 1250 150450962 150450983
    0x160605100909030e01031104030b040b060406080703110112020c0d0201052502280b0702010f0b090112020f060c0109051507030606050d050916180c050a050d0209040b0d 74
    0x405803030501114054060000100012562aa800341c10002407005641c14143c4400108550062103020b56000b5500050380454900d0140351401c2510012a1428403661802e0000724001c240001d4540c166a402510b0081c80d46054005441100d0032144180d8059001c0000402c4001e06119249044000350000301c1c003403c5ca208071000c10304803503900b41c804402d0314002803402c96000a0314810401002d4800c00700b910303580343d44441d81940507006070004001801b80080d6540c15400329640c02c40304c110070440c0c41008800c110301d5080c01c3c450000f1200544201402501e070441e0103c1061368000d220600e81500d446440f420b4409145055071190004401091212030544140d07a20811501d020050b007414030501400324020840510b14140da104002110300c10200042c290007440318000c0500c0c143c2d1b45151068010581c8200400715040000c1da10000d40500c0586000100b260ae80c40c0c204224802248029080903041a500030384980a10140d5242c004100203007a0080182c0c01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 150453462 1250 150452212 150452221
    0x120f0910020c01300f0b060406020f060702011406040e070509011206050604110f0d060f0b03041b060914010203040902030c070b070804050c0d060e0609071401020c061905160605 78
    0x10701c500e410700014103c0502d00a41e00d0300030340c440d04d01078420003039201000902c03409000c3e02d0310044c00030010300c98012000240100380e41d07400081030b100d101501000c98010380e5071007104038240c42260700200b4a12229030085103407407030146c0000700125545c4040701c0a00e0740c2e60000901c10340c401ea2001c1d2607001c404240c80b09110305402110b501402c01d803024016032220324000d850502c2618003d5407201d0000c580c42d45070f49155007004000b80300c03c1c0344802c411a04e4840115076644140e030700b211f800c51046a6034805c14032460000d4211242516020351180c42d000b100809c03009010412030450000f004003148205162018501800d03030180aa5105c0b8618507180c10782c0b58010b07003000140f000000400001071000502450b00d040c0c01c2d10494075094a62400c0d0000c0c2072210720309000760151404226040f02c000030110304660315505d04d540e1400c02038005907203640507020325582164040001b011110480030105aa250341407600705c1c500900311040381030039805400c0031181c264a800500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 150454712 1250 150453462 150453467
    0x30c05011d0f120403030516060f0f1a01020604030f110102030c041d0c03010902070807060c020609070f030201091505040b03010308090312091f02100905010506040e030903120f0910020c01 83
    0x40752004488801080f040d20811100c212a0069100042c00c01c00001100550848914035249540c0e90140301130100c040c0c4000207001030300701701c600785802e0781c074140503445040d030320701e9000d541a0340c181c001c3c14036a01c0e503890032114401207448403810300010121710305510b9004d20046200741c0c983c869281e100d909105540f150a61a95039560b0600f06143c280a4918501c00c100c0c2c0c111144404016680e00301481c01000340c1c050000b0180101c0c1c600300700c54007815004100380348500302c460b0903503080076215069204034500c0c0307000290000b0100e00c024403000c03c4903000c0070030450650818a080030754070307203000f205d640c000d800071100400049182c01c03a42c141040072110107074402c1d90242c00c1580f40d90201e80310b090000b0301100500400f060315001d50f80203220150401103a080d00f4040100d05041035406400c098403060f01451422680d8040c3d603c010007641c0314540014054080c86041003455651504588005030a004041110380442e90742e840c50704154501c1030b0081c10807950030700b002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 150455962 1250 150454712 150454723
    0x5043503130807081c0e01090e0f060a05030f0c040504060b041d010f0513080703030b04060902090a0509010515220909030e0301110f0d090609050303090613030912030c05011d 77
    0x1300c444d48610144d0340d50f80404c4556540311039052920008002c044001207030081103d0b030105600c0c450030424040c44200841c0c4031441850140d54200085035035400b40340d0f495448012a01d80d41e086002690031500c0d2a0304140d0b0498007d80003c28280da03510000760407103031682e44017000614203034003950b030301c14007801142035a001a4408100d68541807090101c07400340c0c290001c06c056000511003040500907440452a0b04026004100260f15a00e01c280290b1000c07962030f02c241c00d18a40050546001424141070381c00c017520000300c0401c0110f13001070f44d4102100162000110003043c03040040b595440400074614480041000c11980c02c0c054402c800080900780664181402d01e1a074190410403100e040b0204003e0559501d4400d50b40c90040c0b8200100800c2d45081081a40901c480040590701400b1544140c03941501c0d50716490083c402a64001004604020002c000d441c84a08901100c24001c0c108201000b03040ea45450071144401c84908081d030b11014040e039952800c100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 150457212 1250 150455962 150455969
    0xf070201050405150a02070510020306031b061b031e070201030b0f010804030f2001060302010e0d15020702060903060907030303050702070f0e0601141303020f0105043503130807 78
    0x81100b82055240d00751a050300c02c01019404000d00b0109072032440d07aa0454000c55000004e41d20700d910700d02a0341e00070b50b0081d19600d1103441030380a008580010301e01010103804006200b18981b252103c4030011108162400004500051201001d85100c0d460504004605086c01c941c5d03c0406100141c122089400d4150103400c0c1800d0000ea9640c006506a40298240c1880c0c611803142560446007095450b072517804c10460312100c015103040540180c02038038802d0304d80418109101d801e01c0982290b446000e46801501540001004c0650b8020810180054141460401d1050100e442c010054030600407a40c0000b6041080c194584038040e040f294a1000d00340041c038141c0b03841d60789115405070541c0c8040d042d011a555038094407071541d02040450b00b45494091241c2e8400344510341d84002c2e0300840c0700d042031140300d611a00032101030384c285001d0318000b901410242154400122014092040050b41e201803d4200b040982075441c0b5100e2840300d5941080342c00c60502c0c89661 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 150458462 1250 150457212 150457217
    0xf0501031e02060408070e01051806060715090f031e0509030c040b030f0d05070b0109110f0c1005010b0d1b0c2405070801090c17070c17040b030f07 65
    0x62001900300c1200ea4152503000c6428141d030699400000c50324400e03540400b540303201740f000014002206480680c100c6a049880c600030362a6108001010002101c215a02c45401c000c1d035070005080c0c1404660380d21164100103000d40890707560110070005054103a010503a516044254944000041c2e10030a240d460158186012000405d1344d40308840c1455105a807a01c015490381d860800281000721407070300894410420414015140751701411055448800ca040007145003246400f40c0d4050018150007103280ca64590741c0d44041e0741103c118080c5034092401c5c0e1040300724141c003440c0d01911030b02e90000d54888218580200b2281d00051102c080001d078001145102c2d000b40150426542254000d507032002005142d01030741c5400c014400d200c41c500801d00c440782c0d5004d40307541d050380c038050307010400f12400900503170720b00000107041c60b840c7c0a10780014008074405c50b0407140040c840e080c4081d5100f07102d01300c040d81e80c2041d00a0001c4060100800c401c0c41c0030462101d40000b00350 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 150459712 1250 150458462 150458471
    0x10f0908090607080f030a090203060109110a050d0e070602071d0402060904200a0c11121015090608060411060c120318010f05011e06170711030c0606040f 68
    0x1a0364015803806541d50079480740c1404034504082c40014011284030700075030001550303280313090f1050400030f15048400343e00a1085600201d400c04240c41254117452240c02c0391070401040300c3c0201c500368031075008207889540341c451300300241c0c0b001c10545014280c0398019042c06402c00d00412000345c0e070311650110002e40d0300c0a200c0561680e00c02c8443c2010140ca0109108420b014002601200c655000a40e06000261108401d07030001c01803149511822007200700031101c40412200e906149401303402c5411150814040307207084e52010a440303540d421070711400c0da6910707101e00032200c40394440d1143c2d8001c181004100200343c4041c0e00c058600b1100c0034108210350b2407040e6107a079602401047c0c00e0001000c07540d886841a1041520318050000380400300341d410000014003821b100d000c005404030f4035550301d0404600a2030050ba182981d8041d210100d050203c0c2c03a1050291902c07061008840380441150b400380002c0801303410a1005003541d00307120040c0011980d12a1911280ca89017 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 150460962 1250 150459712 150459731
    0x31606110102041a16050601091a040c120b01030b0d050625270909050307020f04050601020a11120601030c06091a0f0703140d14060301020712261305010f 68
    0x1c03441c00d0390300c0b84035404d44545a5842c8240d01e4103032284164043c0052240000020f0b200c003881d08020380100c0b601c04034820409925060001341c8580007402c1011450455030812008016840040c81000502d0040340b01c003541d201003030050741072007800c0e6582d421801c10090220a401d11001c0443c1115222401c000e0101b0401480764202d0944210055122aa075504503400111020003034003664008000c650400e00e0aa0b99a0b8040c0c0b000324011200354002c011686007230300c1a18032803d01a00601310303e0700c103030b52240c0303220700d0003911144d003c40b8000811540e12410040345002e10301c614030603100c0f2424401c010b0314000c8a90b02c807110850714403e9003400a80610305403040711102240c0a40c441000d0300d400d440400c43d18000e059a18030105400c07914450340c1d00001030000800d0405801030b00e8540905082c0d110703211014106c041c80300b4813080d02070702c1170001e0200e4040c404616507808440110510080350191148500482001c06007030502c0300a1090002c89031505000b007109100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 150462212 1250 150460962 150460979
    0x4060f1e0b0d03052703070b0415031401090c0210050723070c03080f091e041d1b0102030c01020a09140301090b01150e0306010305010f0510030302062403160611010204 74
    0x144042040d81d4410b8001e00440b07440e04c1e207a1701d2940a0004040d50b0040c2d89880340001c450f0024482c0001c08009940580300d101c0c040d01c03403d5a02000d810344034540e6802c2070300c0038002e006450103000451003031511891114646c3c0c42454090840c603602d044a0801c140c000c0c4e021031960785002a81e04508001c00c1002035840c481180c100c1341c0c403034107047c0c1b94081049034030b03850302440440c0341c9c101111421228094404c2104040021030441302001440d000c8603c055a445e0a0800f109071540001d5400552034507e170386000030080e05104507442c10090b002c0e03072426130300406540c50101d8030b92a4280040300381c581e18004e81d420158020403941031242c031200c2805506100724603401d5800561b00b4400d070b20130440710040c0100130f422a04217582d6860003500070504501c0c110350701490000440e02801d50680074400300e03905030b0300a0019485011280c2841090310352080d455440000d00a80300307403030030300483e130250b050406090301c0c0501d0309402074000100c00760b014503180d104000c02c0c000b0b10b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 150463462 1250 150462212 150462217
    0x806010509160f14030405010f0f02130509060303071b0e07050306010807080606210a050112020d030f170f04110303040620070e0c130b03060d030804060f1e0b0d0305 73
    0xb040d02e0146458032815070140e840c2e41c510100e4025214000007008240901500600f1200403c03400c20404108941500700890003002c4801045120081c010800c40c07426403120340d0444801400e89281c92001c0d69114608840740258a1107039114131810000031580001c2c150f03201c2c0241c200f5914500c1d00e03c00003000c01c0e0004000405010448000ca596601e403103060701c2e2440c007081544040b10407001b55000340100e0403a50001040c1c24a000440d030403291300d0000b103141d580601662074880850760709984164442545a04015040e4036800c1500c10700f0031a0742c00b80f20041d11103100c038202030600300c00c2041d00c110b650740668400c1104004650b40800042000030510b10b41010710009003001500700502548646824510b0303101340078504500304000c0941c00c000d6070b02d10000030f40c1c40040786954002107408540c06880d111030b21000c64010140d280d8068410480000d00703055501a5008550409039140181e51020a22807254580c82c071540b14584400c84196210403070315a401013292 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 150464712 1250 150463462 150463501
    0x705040b0304030e040c030608071a042607060e01080f010b0d0908070813051f02030a08040302030912100f0b030a060c091a0a081503120c12040e010806010509 70
    0x20384001001030245442154514840c14008005001140384400003d015061a00840c0000d00402e500001c40440f104141140004002c0c130850505142070088400306052544d02c1c180c201900240f000c3c840c800703200d00406030507962101000362030f210b00010404000103008941c1500240d005200c2481c080c020388184c086007200c0840c8019403807400c61360764028218020860394000c64180441c20340252420151681640e03000c500030b039126001166a058668501c0141c0c10411220901d60700c109070180e03005000380101c9181050a02c081101043e030143d200f0801c4e0420382070100603800a000f6045d001000340814446000841c00203601c0e10b00d01d000090695994010400805025015003001444091042c0104046004060607654440103080340000e0407140095141016501c0f41c220202000d00100080a011150380d45140d00c110040c3d6840d12030b040040f559840c6200081001c0c01140c1d000b0b200d59490a801640781000680000d0710071b510100400203109128540c95020 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 150465962 1250 150464712 150464729
    0x1514030a12050f0403061a091608060609030d170618060f0a05030a060b18093a05040f060504030308040611040905090a11030f0309090903040f0611010b0603070504 72
    0x101c00040990311489020294002080045070000611509510860040c040102141d251003002010000c00030021106007042e401c0c3c43e4007401c405403103440c030305910100140181d403030a030400c00024580440d0040380d80006002a0850000d48040e24507242c0000064800c616030b01d14620800c04840c2000300080d001c0d610300d9902041d641d8518003040010f00002d8191405a002410600058510300724001d00030401c0449001020f825000c402d03208100c02c5000d090340c440fa2024280d00c100b441c0001010241c1c0c00500b4040800707021400c125681d9241e156075942c3ca141c440d00c0400748030b007030b030007081842402d00007000441d422602e6030343e000e40e100900098069a1200d17900081c0220b42108003007a1502c002c122915400003130f900e000038020f104a030007580080081658a9211180644a0341c100340012402400c2c0181101d03001909902034034205611040c22104148a81d4050f000241d46c188802114103001c2c03180c84c00410b030540d4403600d1480d000d440640740c2e20992003103502 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 150467212 1250 150465962 150465983
    0x7020f0901062109021f03050c0708030106080615190e03070b030c160602040303030605130c0516060b1e130b0a03020d02060c0703030819180206070512070302011514030a 75
    0x411040f0707074407074554164014071a5409800044d08040307000600300410004c2460100400e480200718016503000380c0d80140d07070900d141e090080480301528003412481e042008110401c00e90081030010300320301e51000c2e0320056440c40c01d400050401000040701c0e8006c0d0010141884180c501c2c000310381d40416102e405980d00c04d00000103030119010700c80003601a0348007003408410581e058010504841045540320040e01c002c00b401d408036010b00301c0d00c10115804100d90001044d070044071224141c0681c1c000209600c0d400045050307405000305051041038110506280c2d0b280c105071083d40500c13130520070480551058040b0f4056076003804080c1c4a4940311038031100319079540f800c40e0401d1840c24162088155a4074001d02682402d5034580e5a0404055440c844d030300042c840e40a0491492140c038040b00d01a0b000d0169a502c1201c058075980070340703908414002c1c02540280b1800c1c0c8241e0000641080380c3c40c900314100b565401c1041a903548201242d0b0343c5d0b900003014283d01c0d0300040ea03081d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 150468462 1250 150467212 150467267
    0x140601030b0a0f140a090c020601090b040209040e0105012c22051504050c150702040b0f030316230303060114041a04030c060206040f080f07140307020f090106 70
    0x303050756269071100040f01400f0f034000c01c04248082c0345030511001070702c446580a4030385807031030142c80c50580f4102c0140e110400401025071240c0101c0700140001e0001403a06680fa0301080a8a0180c18540c066039102c400400c603d0440340c0c504000952842c0c1c000001084200d104814000d01501c3c50302c079440d00800c004441c1c0c0140c3c1c401200150b00070204c5003038a2107442c1c010701c0030004aa00359542d00401074195103e0a20f1012101020018042d080c503228450f420007004050104055401c03480200c840c401c00d4500300001d040301440d00212080c516003506d4114a90300100c010881d280118400381400100000152074000c402401c00040c0501207800320305142c09954061040310030170500c9503144601c910020803c5d28007400d4010200e58032118280d036503003800c2d03a0092400b80038101e000d003c00c0311500505900d03044419010702d40285074941503800316240c8024000390700b001900904600d4148240c0b140c5080a03106d0805035850f000003e0031080b50000b0800c02c8129956400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 150469712 1250 150468462 150468469
    0x203061302032203020a031709070621140a0608030a1403060d12050703030608010c05030c0703050d050f09010b01031b1803020d081201120c0501050c011d060601020d03140601030b 79
    0x14083e015140c072080201c20140e0038001d64541040c0c0c8240c012414803804008040a82a1003d100301e040b0001400c4030f91a2110032900c160440c501042900d1030048059030000584c003654594040b80320101c0107504024030413504540040e800326006038001c1102c0c1103582d0f00321b14900742c400c416a000c0b513125030380c00d070209a10a0780c10800030f10301e0a000c0108c030ba002d0b8120000e04042030281e41c0c200071503600d03030303002600322540150618041a018800600410722142c01009514468a080750505410350110341c15038000762801c540000c441c0c0104202000d09104030a00d6010928080c805034030314040b4000007000d0201d0602c1000070305017001d0000c0104010120003554054000740a046460829840c150801c0d00c64030300b4401e0303500c0001240ea482c82c1c05c1d180c4190700b240c070825074a440d020054a05070302c00b08070240e1554035411400c006400c204400c40000020b400941168600341e40020b007850107a60040b070030703d80b034080028806440303160b44030f621000c20b08001444400c1c09000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 150470962 1250 150469712 150469741
    0x204020d0207050109060204090e06310602030a0614030c0f090a0b0909010902041503050c040915020a0207050f1009260318180601020a03030c030b1302090306010603020306130203 79
    0x341c51917080c542600100b0201c1d6000b0021542d108004000503400896415103840b4280d60100c0d200c0740c200c50032400350300070b1400c050303281278004000c00c1d10102070360320300085e1f8100705c0d0070704542a500c0000f0880b981d5502c0900441e06002c4028141c0002c0d02000220388007454050680903202c2c0c1c50000d200c132500ba0f4003a102c0c2647c018400945031403c1c06501d8041c0c220107070100e01031707828100100c0d019500d40e0b02c0340054aa200d806040d00880301c200780303c010400c141c070568072004546801200c2d100360b44001e20807100c01c2e90140a07c1c3d401c01f414001501d500b41904c134090406410204ca90a078000f1003c026900c0040060000c083d1900c0c0e4003580d64611108a640d60100040c0b03064255400070000c03000d034105942e05042210060f00030010800304480450141e000000100c000074420386c8000c0345d1000d14180050185408008a4141d88001802c1011103600080f046003510381000958010005482c0551070351401d000814034040302c03180841181500400070075500c2d0424040c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 150472212 1250 150470962 150470977
    0x909030503361f1e11040f0602030c01150f06030902040e03030c0309011a060a08130c080325030203090d0c0b1315020c0a05100c0c080f1209030a0204020d02 69
    0x240348259a40078003143e03100c101070307020714100f01030301c007900c0f807601c40c8a000c0d00c03a2040070304400c0710a1481041c50a0040c25911001c541180810040429440c111710740c00005056654011a00e500c120303000c941c01c4402d5121080f0840c100c070303002000400011024141511841e14010480c168141f0205014000c5d040c1110454000482040100c0049401840c0b09890400c000c0c040c820301c0c2481c00e10050007070072495401103c1000043c0413940188011600003030328a0201c030b0320f514a0b0300d130030405014036001100550800100010a4400042d400c4004040c2c1d440004211041d030b9400b0b0760303a101d0030860034055140010709078240810203082c14005e0040d100c21540e200300042c8880c3c55082d0301d01400b021200205103202101c0c1c8000381600b4142c10107000300403401e0504080008015940b080141005580b400010010b0714100001c001080d4150041c4a4040300c003c00798101070782041d08410904007031103403101d655030000310700380b0884d01501d00603503407640c00100740d010344540c10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 150473462 1250 150472212 150472291
    0x10b0a03110a030c0f050f12060f030105010902090a0609080c040c1b050c0108011202010909050603010b03010e03090a1d0a05100503010c0e010e0103060503030405090919050a0201090909030503 85
    0x5848110340c3e0f0141c0003040403405641d01c0300310390440a48103641e90300a031265aa0740d5841800450788588044203d180c2114004001c020880082c0300000c0c29544260482620b05801040100103410140075010151a4500780300c0005c6007018180369648151000c503902c10f548400034211642c0c043c00460958180c04440c0c0d44078032155050081e5250015000e03180080c84c08800007404a0000b4448005168140e44644c036091500c400000a408003601d000d47c59517940150343e2099900f4496081c41c41e1105002e0760300c55820b48100880394019034000700075145024091f0701d1078583c2d4601640c0c0414100c00010b0113031606142d000c5454035507000f05030503602e00140b0000e80c5802010301e0303540b000300b641c5078103a4010280045003900c0140c231615802d80d10902c4207211342d1a05000c0568081410030843c1c0b01c1804c40c070200c400c1d00e21405000c0d99940c110408a030b003503503070007141e10016104e14001880840c150395030080403440020b110026200450420819451011078484803c4c925030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 150474712 1250 150473462 150473467
    0x8030615070507290903030d0b13090b010911040302010f03090f120c1104060501171306141005090609070f090b0a12051e041205040302060414040b090609010b0a0311 73
    0x1e044009100f00f01c035582d00d6440d2908a29825021101022200402d1006d4040d500340780051100d000a0300f20481500e070700c00b5881c0b2408205400b0ba02c01c1619081c0640c120207200d500d0180c001c000c454a65803581d52503902000184050303600001031200d000d20501d1700042c07861450900d202c090034040d00c001d1402c01c48412400440d94400c61000da034500820390711000c0f4001000300422211070384a141d0114604101928501030b01c0c0c0320b04c0b64843d02080c0e29581154059988000b180c1c4040d60001d65641d0080600600012985000c0080c080a4560781235900303048000402c00300005100d08104041c0e03408140d80c081c0705c1e840031001824424032148e100c000700741c400303000d1800020440c0051b500e401d0010b181c1c00c428620144003e95644600480c5440c0d40c0c550750281e00c080030b038a106024017003100200689941000340000c0c0402d400050001100c1005c220a4502d0780d0015413091156800f40030050391845200c1d0304481c1c5c4510074580d83c943ca080103178041c29103002b00060b004000b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 150475962 1250 150474712 150474719
    0xc070e04030e04051305060714040b0c0304030b0709030201050d020307020a060908030901230c09060f0f09041119120906090501050f07090b090f1201020c011505060708030615070507 80
    0x12600b00c00b00200304880034000b5075503d59941c0210761100c0e402400592004d404107180d207010341d030007140104240c60070a14040d10b07041c00703601542c09104032154a6200040400034442448042d640101452829420003455500000c101e4018040701034480740e800004203040500070000c01c10750755406001400850241e041c2259150411900071030b2075401c150070154054100b10013040814106102b81040b9241d01070600702c1508114580c1c0c1e00a07108100e220703840d20f01c4002a10700310f4010807000c0e80e241da0391b00603c81a65041c400c20320203444140000b4403440c072554500205409245052500c02e00b90030b82481c050050124081d00c07840c64030b101c0e10207220f810740081d48122031131000c0c0d0340c00c0d40341c4d400c085502c00341d140b003100c03620030040c00f44941030718101e8440f0081c3c080c024079400729032441620791422a07101c03104002e5181c0d034a0000e00c00100004a01c00c00900e001c4441c3e90604009031a0740e6581d207c01010b15202c0c41c0e00c403000004c00121201920803040d000700071102d00944 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 150477212 1250 150475962 150475967
    0xd020403120909050a0c0219020a0302090f0103031407030e09190e01021908040b13050309060a0305180102090a090213030c080703060b0405070f0f021c0207050114090108010501050c070e0403 84
    0x50782c1c000c10b2080c0341400c3c000394100c1c40b17500034042800900e9004016400046400075015141024201d030301c070310030720310000c050f95841280c98000c00610846ea5002c1d490741ca4003400d020b01c3c02e2000314196100b0b018030401300e50400c1c06d0560181c015503116145a868611540c1600c4e0504030000c1c0d81c500c0c1c40703142c0030310100540c0130b08050300c01d920007150009159031081d40c90080454004107001071030b02c0011144119184e5140c06184a081140d052001400000300e450f00818a05400a5520380030070141d05100000805400c005000840c80c00068001007040324843d0300541d00030b1070f00020000000816440b04100942e00800080400c0e912911543e071900b0440c481a5402410701d0011075076481c00d0b114440c007035102501c4071083d4102c0e5800544000c0256000c40b019030103400c0c400e000daa81c00900712140750300c1d59409848003a00300320000d842204c4c90604400248014800100d690341c0020001d4152031003428500c0e114114030b08500d06d8800950014496602d092050008054 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 150478462 1250 150477212 150477227
    0x6050118050603040c09290603010b031605070611090f0117160c020301150e1f230414090709021903050405030c10020403060f05060a05060f09030115030302060c0f07080d02040312 79
    0x28541c01443e03449540410040d03d4042070098002f561405c101142001c40500504407402025044c69400c00c1e13203c4d01c48508450030782041c884500b1002a40c1030442c0b0b804840700d00c00349800d08001459131056662840c20110040c00022151550040d035003c8500031080c0c0020198000c0003440b05248910034101e40b020365100e103000014000b000b140704200d030702580f125004111400804040d207410301c102000b960310400d210f004c2a16449005590301c0710300980840e0000744148030701e503040c0381842e40d1400c0000d60254041500c184000d03419500d41c43c1e5600720b003024070b1401081e640c0b10b6040450a5103e2401d441a41c0c0c070500018030341c0082d2540192084a000d11010031140c0c40112103002610000c56882c1e0b030094641109000780d01e002da010303040e04d00b04440e1007400c06400300046800c607000031032014940b00c811102041016030411a0756480844210304a080c003074950714841c603c2c083c085004020980102d0040401d201e16419140210b4002c4960180b40301401340282240 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 150479712 1250 150478462 150478511
    0x4030501050906010b0f0f070f06140c070b010e1e01090605090703110702130f0c02070e10050306040314070602030a0e0d050a05070b10050904031206050118050603040c09 75
    0x354203150010306100700c0814814101c904019105107440c000c0c0520515030343c0a4181860808801c0c0102c101040306076224a950601c02c9000060316504c6e09080b1001c500300404400e04003e08214020008080585190444030640c0032034240d601c0c0c10301c01c500c400084040407403041e080c0c0b000008020800b0b0b00220226601980e82c02d146441c1c0310811000e440a900a500d82c41504011400c0142440030800f28095801c01002070034654100c100c0013030781c103080f07400d5005034071201d401d204091000d890b042d00218003488840d6854a00b0300030a4070f40500034405010300442d0000700d80d1640c050b804480d106a40407108541d00d15001040310020500340306058020701c50703001c420102c0e9018008544100c00c09445683c00e110603542c60300445980240348800021892000160b1a11000c3c1104d010f180b10352140b0b5070002d00031201c0d00c1100e8103071741f0032070400030458145c0d0741d62002a0a1501690810b40380f880d62a981c50400c3c481d40c0d02c0e568810b1100301d162188e400d000800444250024 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 150480962 1250 150479712 150479723
    0x1020f04140a0518151f080a15060c1505010603050403020c100e190902130e0f01140922030206060406230105070f0c060309020f0319030503060d02150403 68
    0xc8814800522010a4080c00f85030f820814240c000090710002c804110340c0a1403400170100500d17502ca0110722075560354050114000c00006000c1c24082d0003404455020451610411001c070031203c0002400600b40306840a002159018006210b0b1440c0507a07409081290b06001d6540e40311001001000125015401030051080c0030181d0719180701c0300316001000e5691a45007800c10400c01c818120003c11400600c01643c80014091000340003810400c84212601080c091400c0d007610110f09000b401800020416001070001018400140802c9202600c95160590381ea4003846115941c6041d070710a40c1c841c031082803007055330016482c1c1c8a0202a503041c490706039107a81c20a003030b00d8100402e51181c544803403004200d5104001502908d401800c404500c00c1998544825800341340d001000000c2d02c80d94101c00390b041600d070050070500c0c01c1d00140340c07224520f40707041040c95500b10000c0c06c1020006c00303c0c1c01a611103d82e8070445400030b01d4112070005d850140082540148012100b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 150482212 1250 150480962 150480989
    0xe060a0b091911040306090606060216030b1f09091412120c03040c031506060e09070c02130e0d120b04050403080403030504080f030705120903040b070611040801020f04 74
    0x2050400003949800b03a4240030400224040c0002c40002400c0c19020b940d01c10801400000040382c0107004982c06180111000100582007020003030400d000500c041c074810783d41c83c00400010b51001304c5503a00c1003d20390b47c1c0940e04010a260000e280403980b103400c0745402d0911040c240a0b181e0032096a85e1041012901c01101e101815040da0207900003825030070364100c001464501504004541c803d00c43c080700e54420303489a84603555507503900003059905994070720902c070080d001604034074400000c4a1000c22403034440001024190032480007405604007070306178217401d80c00360082007030400d0075005c0c2c0c0c582d080c101d50b004102c40316100312442180d0800f68413a13900d040511816004a4060342c50700041d60b03507500d050700500301c040c0048420700400c02891849001d048051402003c80340c2c1d840d6a0303820107491280003664040c0c002511354108000400402e69034108440720540d01c4040440c7c8121980740d0880d06001d541c1c001901940002404603076007112030000c200b610702000340d05a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 150483462 1250 150482212 150482231
    0xa0c060f0306050a080a08090303191e020105010f1710052802070305070b0c0403050105010308030412080108070918080708130b16060209030f0a080310090e07120507090e060a 77
    0x80c1d888a10710410203a81c200c44001c1d070210304120024580c401018044ac1d14144040000e80300c0c1121020383d40001411244004220801da1003440c82003d1051009120a5052615010b010342e4280718400340c0401c140d01000808409101c100510092507004000c40e15050b26109103c0112490b0084501a100103030720100c2998829201c5094240d501d490405000c1c2e070341c82140481c05046080018000c2c800040000c0090103618046c600c600881a207a041616107682d248100c0740c00c200c24041107500601502d500010380701c0c102e071079680c004030391504540c034a01a41500f05d84040c20346017001030b0140904c1404001480c404803541d03d07803084c071607440c103004070345002c0c01020307086100d0140c0351000030428940162841c0700d00141601c0c41c01e04950301003887e046007420f013100e01d01408410847c1c0343c030044a50100400c4e0008050105150205400362140510b01402d840c1d0200f00300001c3c04c0c00020002c0e4005800315038410041c12500540ba03a56581007181e4000455080c0b00c540c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 150484712 1250 150483462 150483469
    0x2091504030f020d0218010305071d06031f02120a06060f0203070804090518010c080708010602010603150c050903030703030207050d09030b04060504020301110a0509090f0f0a0e0a0c060f030605 85
    0x1101140d811150349102c0600950030440544500c04041c4e0b404812101035400d542e092024090085215800410031940340106c0311003280c0c0c80c5860501c02040c258100009034401041500522101e52000900c0c45000030102c8024041c60854804c540150310400460500e660f001c4825500c85840e804507070000041c00726603c2c0304036000105a01d0041c8002c020344840c40c0c000e5904000c803802c107200e0055a145c02c03030342100c4600000100040b404014403002c142c00209050241440340700a10449080d61140040395803c03041b04081c1541c0d858401031510312400030350b011502c008081c2c0703903100d0140c00d0040183d008440305407100d015131403103500740c05d000d000c0303135011650301c80740c580d6103592103403100d800403c0700074416609952240168070385030488100409111429894a40e107410396002482400301004068895003002c041c01d0001280c000700100c2d0b40982d070080d000c00c0345600b81c076803142054840e4500400c85c0701106030100301d942d085001ca4102c558517030703010414181d4483c100f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 150485962 1250 150484712 150484717
    0xd0c0e0316060f080402031f0213051219020607060507092c011203030b1c11060c03032403070306060608090a0c06050c160e100602010b090604090f1401020915 70
    0x16071001c070f09200d55054590380211602544070340000c00352404000c0c2d10f054000c49500c10b0f10590b05480d400a10040f941d14000f4068001d00410307149c10080f610a01003640d40d0b51400400090300841d91a100000c40d075605041b100e41540c450f03c00d00140c1032180c0c2c0608122000c0c010f1348101c03807030014840c02c02071049a240340645940362019080d64a064002e0951925030101a001c05d62182c11031800ca85402c031820402c4008401d0385015a00326040c03112228011555441c49000c1c10008075262490010950382c0080511200c410740d502c0d10040304e2034001c1c6068070103030103002c0c1c0e02c400014406194000c0d0b0840e5110380301d0b8181075688000d10381e00d8081d0140014100600b205040c13204c54030680c00b5150344802502241c0e180d900c00004550189461360103607400b0361760030b810004200c429000072030041c0f5150000340311840c1c0140000c0d0340315200030112402143d0b9142000103010f00410481c1c90b194109203c41c42000404440300e000c0d40c00700c055a40100d05040c8580a0040503904 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 150487212 1250 150485962 150485969
    0x60414011505090703090507080705131b080603033022031215031101032004141c03020109021c080d0c0201150605030603070506090f150d0c0e0316 65
    0x207141c8100390422081041c030000192440080560311202d1800083c03040103034201820f04c40e4000d140f036501d007208010350b81070b0600f2004111820502220307038200700c0101014014000f802c0031403071a03958002280c994040d20180c04408419040c0224000441c121009104500307248032020a644440d21200e11002c034201036060301d1200d060610200e4411020258080f83d080400b0810b0382d0841c080c9058611250410765100281d40d51500c2c0d60340c1c1500c14019040300c903841d10b81c150054064003256a008501c901c4940100d9110aa420b0b42d5a0a801100c0150302c200138180840e41070600038003e0030f21070350890240031a140c00035541009a00b000d13041c16400000745281000c1d42500d40040d00180410f40103542d01d5520310040924030340d40380c80192040d075507401d0700ca00c0e0030030400d494007080380d020a002c2c00c1e08101682d460744400e50f03045c0848034160b4041220b260049041900da100381c0e1503015010780380441c98041254089045c5044840850031110216030080202080f01c0c583d20 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 150488462 1250 150487212 150487241
    0x4062303060904060e01150503060912030103030f0201090204090609020901060504120303022101120605070503061008060d06060b07050708061e0705040b07030905120a2f0303040806041401 83
    0x78526107401c9084950080c800c1c4030105031480040a51802c0d0b6200d41c1029813100004c100a10840c182007200ca03030300c0700c1da007402024240e01c0d40b25040840e00c81808040d042011002002000074000d4200c01e86070769000e44104000020b5080680c02030900c050100d02c2201c2c0207000140140c49502aa029556130203408038803050f5565081c1c009501c80b4602600c049048032001c919110051880e6008201c90803c85224519a00c0e0450803641c0003000042072140c28402d0110b1511407030400b0b8164034903410314500c0d50315400000f13024040d04c064010030b85070400030003050100c910340240040310710510440300e120303884a40e011346840080301c00345000301c22003034810020340d074509116030401140d007400c40c070707050300c5218141c001d90150700f05501094412070f0030089801d10341070304149001b150001d0b001c601a00c0e5107002c80d6210f03000c00340b0b10400425600054030003c82d00d4402c0420700040c11280d03903641d43e004068444404660039a41800004254096000d06000c0d44069020701d2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 150489712 1250 150488462 150488467
    0x92f0a0302032515030225030203030402060c151609080c15090604080a0501061a070203150a0204051c0b1b091507020306090109110307030b011820040623 68
    0x3111824200101009001070707102401e0800114440800c2d41407403851920b0b6170250b5a490190001025421090054100c58484d404410003080d40441a690400e604491440da03400c21140d000f4904400480440d500c0510001800401da48071414101c0090064807203960065546c610980c6443c0840407403034129044903e0070006844110003089000301c0140303d0303414243c481c107260313113803100c130310011105695141024814003100301e41d01e09a0746204c000403403500c200b0354086612080c4450740c010740018010041180d0100c141c0648018000107044145c0e91100320401524517901134809803242541100440c1d0840c00044c50000c0c1c00d040248018680076010040c80403000b25103042a81045040c00100c0050b41c042c00020700411002c00003080040b4181400b040300162000c1041c03007a8400e400800005142c0d04040c4e0440c4d11b452800c007070b0507038200f5078100505892021102c60b20b10210300c20080004507000340c0190356003643e4102445220310925004070031158480170150106 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 150490962 1250 150489712 150489733
    0x1703090f0d050a0f0602041a04050f1011031c0b030d0504170a02120c031b030a1b1706010f060203040302060301050613150f020613030c020d030201092f0a030203 71
    0x140c44120740600c980215980f24000c0e0311420200d030140c1e0011a015900010200700482880c2d9210307160010328510645400d02d0030000403801242c0c003529034020305050074040b03901c034003030b0a08e00c25004000090b40c0d580d040f04a2a4034410070300d080c01e020410703c0c0211020349400c000409021004840c0c0f50146000d051182e804201c410406460300188030f482c2c01880117840b540b4107000f80c1c007a07030360090609009981c101814480074103481c0d6543e010410700342101c0c0e6030004181c4d4480350030428203510544040d4400090061580002d4a481c02041225803208400100c00b41298000c01194110985840c0d081b6120322035480080c0d0f00150500061080d440c0841c000c020202c1d01c900070050302c6a60340e201d540c01104042100c0c020400c8403c0003020b050301846425408000b82036141640f1120360f802400d0464500b0001e40180720350085801014001d520201d051074010648a1007020702559021090303c0403548894080c1482c914100e803800c12104c0e040a4a50040260204240 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 150492212 1250 150490962 150490969
    0xd03050f070804150b0a0b0409050a09080426030f0705060702060405030d020a0507020307090c020c1807050c1501090510090203070206061302070f06091b0305070b090f090906011703090f 82
    0x4509209042640d9212000c107030f689a000d50780061038000380c12508c6525100d50502102d00040c4044c41e0182001060340000321b0b06002c5400790b8580d080441072201290441d2824407000c9145035501d4403002901c7c4104800b2407015010403403003481218001c0d0b60701034080740c075814140c50041030381e802801050700c0800e82da00501320f848010b180c01c0d4100310003600060f141c40030380e43c080141a540c803501c5d4804554180004a45020241d484031800c0c6018040c22400e00c80061480d010000c012a58041d0a801488401c0d12640c202c00404d02c1035850f10250402041c3c199080800c2d211503807000540c0507590700a1b40c0c031940301c41c0c016103100e584481c180b0642801040070f0a001540c20490b0380c00240c807482c1c0c8880e41c1c60160200091150036441c0490810781030280760502c40d1081141040003030000030300003040c0e91125885030344480c031020101d0340042051002c598060401d5003040f00c10040024418101c07038025508501611010303000a0300d074801c202d00300d07801c0b2490148200480c00c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 150493462 1250 150492212 150492233
    0x30b060609041b0305010321020c090a1104093213050c0d060203090f07080303130309120302210405210a0501020a0815040612140c040204080d03050f070804 69
    0x210141003c212440c0511500241d4042d8011030320100360703644010f00511410300000703000d00c100140020744072004010040d40d00c50728030041c0380c400c076501c00c000303102540d00380c01c4140000e000e40512519140c4800b0070f200540b00e10503642e00d095181008050f51071000d00c98054551601c1c104103e1076440301600940d055810200580b00781c402d03040c0c0c0700042d4442601544501d4058a4010b80703904005031440d06110048800d14040c0d07000640a009462000c0200e94100b950104140420b145910341036071100144e50100d403800ba80c0f00c50a4040c1600450b0100821038400c8041b40b09105401300301500c0e0046000b031a40020440850368202c0c2a14601e4001400c2c880c0120303007141809542d01d90999004c1c8100000040c41d0405001c1d0300b0003598280420001c049405004860130041c5809262507589805055400c0328416045010014003900c0d9a00b000504290750307450b00d401fa081d61761505524030800117450000011120301c0f0b559035103400791100e990b4000300d070b444070b071116899007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 150494712 1250 150493462 150493477
    0x1508010b04030209090c150714030301050a180b1503060f090f130203010e07080705030d0305041703040311010c050a0e06120a020306061918090b0d080a020a0506040c0302030f07030b0606 82
    0x602c105141211306a647c140030007481c402940300c45503101454902442031952809986140340d10510051140d907450700c080318240c9a1038284403508028010007400500325600c02c568100c013480400344001c40510004504c01c0c041030304c09030800303115601880190304c07088074034514050380c2e0341c040340c0500d0300301156180700f600003030010443d1140302c0455410f0504903400800c2c190b004c440304100d5400c0500440d07c00d070505050400081c84c068460040f00c3e00081d0480d15400000070020f401c0500801550b2407080101d402080003580341940585550303c500c0c0c1010105410301408038151818804a80d040f000e0264004055103039605c85602940014140c0341d40148184022030014014050405608102d661000c003140144040102d0b03901d0140c010581c0d1034100460300703400d074681074031001801758003080c1c1654804651004a00f0104225402440360242e41c1c148004d2080880409055900860035a02202049140585e54915900c002001d20b00c03808001060343c0303000806171610 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 150495962 1250 150494712 150494731
    0xe22030e101404080601090c02060c09102d08010f03020d06180b09010203040215041d06060409020408010b040b0603160e040b060705060405011a03030912160605041508010b04030209 80
    0x1c1a003002c01040141d002900820f80030f9002000420100307005000317001a00c1e40354000b80909042002a841043c814412081c0c007840302c12004607425442030300301e428041c2c1290031200088885c01041c455411004200e0740001e0304c14000810412001540c1408807980148250201c1502d55680005420b200e1822043c200141143d04d0201d000e44420381d1081f2100d6000507500c1c40c0602c10011031844840f11940c004405000a002100f034402d002030301910b1010501180c3e50311403002880c3e41c81150446c1d0b84140c0003040014510a054100d103000040440741400343d802d01806102150204030b944400e00926088010742c800d015954420203188054000f0902038004408504594016001200c4030b50165003080309001d028071030040074241c030300e86442588500c04002641e0b809021011842125034016119100e1010064070026036a50746a15103210754619014003942c003d031180d000d00548480d500300740c02d4130a0f41b08905035150144198206411602031003210340008025511 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 150497212 1250 150495962 150495977
    0x3050604090606081c09050604050105030a11131a130506030a090c1d160e010f0309020d050a0210020105090303010b0d0b0415090c050c062a03010e22030e10 69
    0xb00390240554405040701c840246103981486070000118140740c141c3c00c0030082c40400c00d01103035030f0308011102202c0091070305903180c2e00c58a4204004004070205900c11700c0000800510310f00862080f01c0495154044d003400031051f1b41907000c040d12a0b40540d0400c3c001510080c04989440f201554020059242c0010012040d079242c0e0480d05013500301b26014400303840c401040100500c4d541d60300484103d6560440c1a1024020b40900b641845941c1400341810703420b900d0324072030b0b8482c0032200d8000b0700d0107070004064204a6203550034110140d00030350000503500040b60050180d2400740d5502e900451950386005480303900383e00a484d00e003c500d03440d10901400d030b42d260300452001c001c012000000a5140c08080004c4445030b007500b1052010600400440301da000c034103103610400080b580c40060503404e05000000d20904a2941c031520088004a41507041084542c0300304c500c1e06210348003030103100c15501803401c05000100050000300c0c0d0440c440c240191451001621401d0164 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 150498462 1250 150497212 150497231
    0x1206060a1a032a070303050a1802030c010e1206040c08010b060a02061501050705030d05010501021006030312020c011503060b030105130f20040c05070215030c03040f0827030705030c06070303050604 87
    0xfa8543c1c000101600007035201d009118910b0b0700361041604081c0d07c0c103454450b1322090b60201c1d44a103c10140310b418065652140442c6445502103401400c41000a40352030f0304e0305181410469000d070103028095841e2454080381420207008898082100350001c01c82541c4074441007200c890160801e0b81005014002d03080040d40800c0507040a902d80300b8007080560421b800245071580c02c6600c02c0415003070000c2000400d40040d060703003244081180150391540e80320300700ca001d054503220b0748082c19a120400002e1050650182031b011034220024819501c580c0312080d203d04400f82c01404604c003160075174000904d07032001100160210340101c2c080810202c00501201c840741104000300b5400140d090442c41d1040c403120400c2c00b503051150543c1881d5403e00d074180001003008060070341c824512410301c0500010b82c1d00c113002038003a1040c0707086034000d013050464030008094040d10501502003014038020808158129010b401c07030303003800d01d940c0b0200c7c040c00001d070000740c0040c5e0301e20b06807 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 150499712 1250 150498462 150498541
    0xa1a030a0f02040e060f03010c0f03090203030f16110301060f1e080f070f08010203010b1c090209040c050310050408030601031a03240f0903071106091206060a1a03 72
    0x803c001c04421044458034648041840310320b140590840c1e1103649081945031072250000150031106495240c001000744d505d01c0402d1039489840c086100400300411580e0a4841c240f070b40000c030710b1150040040c500e40c44c1051600f030760307a6401390f03c40b082c0040070203101804000401240c240e04864070026542c0ea0b4668403400c041c010029a2a660040d6005000da140e046604200810b280b0008500d1985400c601d49007601501401010a00c0c00f44600d003a4884581c0005090b01c1d0018071001003420285050700c4804101c0c85001c1c001e014250355081e4900d0f0900c9090304c96904001c14500d10390300c5600450003400b5070321004002d90754042d21074030305442c10014841031102c0608000740510348001081c5103400d005203901821900801007246044001c002e41c0c5480b40d0003606020701f12000e10000f100c3d8082c002e1031760b030400e00d107415070021410001400350081c1e40c103481c1c480015803030713004286410120320b184030200b0004101088004070004201c40250141100454141040e4601e6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 150500962 1250 150499712 150499717
    0xf0d0203033601020d0e0304080705010e0604031e11030d09170102070609080c0712080405010c0c0b0c0115080c0a0311030a0209040503090a060c0201170703062607050a1a030a0f02 79
    0xb4500a80d4080b03182109951507224101802c1d080d80d000750305007890520b010f039407010b45020303c45c1040810310000046456440a980c06554440360400501c0c941e04d090407542803000c2c000b55003440256801844074100800c400c0250515130b07880b40c03503143c05c0c05a0141d18507020b03a17028055650812150b40490080d201e0316124034480c1690595820512409914080d029040b41c1c041c0c0d840c28400074006403400c0b04036000c44400703003000000b904250810505020427548049900302000a0101c8119010b41c068004004002c0c000030417203440352a5280d490304002c2c21580c00c00f013000401d0021448002000300c004000900301c030180302d210340c00328808101c1074034100d078103034404030701502030f45490880240136045610f00490118a160002050034030015205d400e0304036084049420f0611a40007900038000609140700e81e5081e4000c1d142d00124100e1221856014580340400d16140420081013190204c400650b50580c0a9a2034045c0354006411581d0082d42c1c4c011a14095a00d80013 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 150502212 1250 150500962 150501061
    0x3090f030302060a050c0c070e090102041a0c010501090c020c0d210512010b0319020a1707020a05010501242a0b160206040c060309080702030610080f0d020303 70
    0x43d1115080240382c550980e44041c24000c1900424401c1c8140b190001900d038045500e154030018480d100c5100050091180782c101e81d10a00c0542094075805141400501d41d84900100801c86070f07a89041d02011140356040c0000140c120b41054007052501409095005004d082c0315100e03005150310410741401104103641c045400800c1407100084a030f44680d004102c1c030050340c0d1441c81c14001c0d00c1c1080c60341031402c850981e804501ca25000340b284030800041c00501c0107007515403c0ca0f80e0060b54070715407580c00322080d60174080003240303480020800a814450700342040411101782030050301d03c110701218070141d20303920980d2281800c00c580409280030f0300404041e412818003901c2d00142600900c070890565220f40706020001d61400542400c0340c01924002641503410b203401d01c41841000b1010754503104500034000306041e0140c2c002d040b1401d4004684404044000f6942c13200603120300000903070818000911200705601042408008400b02c1d10f200c45200507010182641c00d01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 150503462 1250 150502212 150502217
    0x20105010f0b0301062003070203060403021b01030b1f02030d0906060303110109150e01020c011506080f040b04030e1f02010614010905130f0e06130203073003090f0303 74
    0x10010000c030302244090801511504000320314640c10020050f00802001995100410075119a10340110b421f005445d400355008040c2c640e1b03401c050070000c1d9a800c40910540c0392002408481d14198024418404000000361001d005207400305d8410752100054074240c0300b58041009070206420140c415440d0082c03094600144241c01c508000b000c603512622030400c40d80c9005844c8002c141c8110f074002c0091100309002c1100c801d8100446c0c064002c022421100b9824007081c0c80392140e40e1035111050b42c03900e694a0007603035580c00015280e082d0544002e4174042500c00828003107403281c400c814841c00060012032441070902d80b0441c90b041103080c8000181d6403010f05100521203404110084102460020300060600303001400c104410490080c07182c1c0d5170a0300035014807807078002e5182805038005580745032070315250b002070a02c0c0200c01280b0a01568002003540722200002603602d4410042401e0800c8084c01c2079184240032a4007541446013004001980904104152014503c02e9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 150504712 1250 150503462 150503471
    0x2031303140d0305060d150f060b030610020d08150d0c03050f160b0429040e010e0f04080d0507110f030d0e07030203150711060109020910030c021c1e0201 68
    0x424629051500c2e04040d10101400c0c4010700060b07688001c5020041074014844204c01d0140507090070061012000d084400b605081c00000c1c00060381000e1071044000351001003000c4050315040340c0380c5d04045441404140c60314045032014010420a20003501c02601e0031f540c110b4a52101007500300302c0d0307108998561010040d49c03018201070014140100c010342d1403054040c200303055032600f0b000b640078480c0e40001d03110702e0b61b00004144001c1078002c0c0c000310b50030340d131030b9202c4040032040c8900f40154540e0b042d030080455081c035800c0200c40e108a80004000d170030040513010030300141c07401400500400150b05201c0d200b18030140301c0300b1114454600156951000300600070160361002c5420b51064001d9101040561004500c41c1422400b50002c1c100301e0362a440141c96012094071400402d01c580d900200e41d050f55035000740070010088807103510884c0c483c0801ca00b65901280c0707100050300300544284401100e80c10440007a003d9041502440307802c1c0c0b425020418440035182e0050307449 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 150505962 1250 150504712 150504743
    0xb060f0c0c0301050702120a14030114010815090a0b060706050a061706100311060c030a02030a080f1006031a1320040e0c070c0b070605040209060307180207020102031303 75
    0x8005801c0c1d0100182d0080c829807400c0680651142600110b02091010006e07407085968407805e0070b1604160b00d00009510f039611800002040c400c00c50629001c2544040414041441c3c543c031142c2c16513000704419003580d200582030300070300614480c09800030001e00100b00041c003280207107880b500c01001c0004003103103400c40e802400399061034445816080030741445039825002140720207590b001f0f11540f29101125000c500035101c2c40c001d4180c98040410362101c940d07808002882d003240d440d038038404283c40d42d41c0011882c1c0030a6440304441c6088510812825000b50419100750680c0050041601100e00c00328604804401c0c240c900342c2e903614100700701000f1501c500302d4412a00c0750031909003420b0a103507030b6603403030080e10328120303004041001001c00000308220f001030039260604c2511683c4926012014100a4900f03c5c429411040007600c076050001e2143d0403110001e04c0c801c0c4069130a0803c4009521424050b81140000c109804888500400101c0194424410301c40d08115 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 150507212 1250 150505962 150505987
    0x9050d0314010f03150b0a0e0f0106031104320d0503030f010e0f07030506060d020f0a12110a0c0204090b0f010305060a0203010501080612101e1406060f0d0b060f 71
    0x5800c0b0316210751601e0300031310120307041c004040c1205202110001e504511840040c00e00700f003540c4401c400182030010050056980d0a40f107040302e02680701840405450000844140180c1c041e1203100c6034280c407500740a120b0603071020381d040c0d01e440342854130002e1346001c0707151001e452409403460b80c00002484202131200d00d1044c014a1440f0050001e418840c817110300c018000b8109100301900d0780c0200d8981d60b0744504585056030302040441d900d0380e94494601194000c00c1c26600400d099014980c00b414040c0504420140e5200c040b03442c0110881d410f803202c0c200c008040e0707006540e680150001510031414680640103034034105c0e4056255241080c030b8503400600003a8664010310040180fa41c00c110400d4210208031084485625250b00051030703c4540b04452402c1e90408070041c1a03d00e40c4409113080b042c500b181400b00852441030010700020984030181c0002c3c0030000c0701c0e841000c030300141c03001458224000c50b40c007010200007142a040050352910036603000880c0c488104 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 150508462 1250 150507212 150507251
    0x1a03030406021e011808030405030405030a06090501180b18010b04090501090c090b03060402090c12070f0207170601120206070b0114040b10080609060a03060e03030f100b040501050d09050d03 84
    0x5400c0000740100c0c00c070305c1102c42e070060031503c00820901c07000c404174040203070074429140a00701c0a03044504180300307030620b0400340c25680025555035107000d03545955804002004010b443c0c00c03060000f05a00d540c240502016407600040006543e125401e0443c3c0e6580d00500b01c0c964001e40000c14081d0007400c00f008425159440b6050246c030309184607803135072008668554445d40448008101d5a10040d80c03540c0e82c403420b0010500802c544c8104058580c02c000381e60422141c0e0b5080b1500030381c0b200c0c5026501321078404402499800300700104000424900140c0840b032000d46001c2c10030b00c84d9070701c011b0400c0d001c0e0040104141d0390424041c00e400d1034841e50740c291740d0840e039142c0c0c00802d880c0003030311101c009002c2170700802e07807000014015254400c03c04002c5900010801c000c20000c002107032a134005541642019401c4008142e0104001204009131140040340906c0c0c14540001951107030300c140000e100d940e4556000c0b0010903001d1280c0114010036407400f1a00d603030000300d40c10951 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 150509712 1250 150508462 150508513
    0x5030f19090203060421020f0a0b1e040c0e15010504143001050714070f0204020c1e010e0a120c0c09020301332c0907050a0825031a0303040602 63
    0x154001d1034a000c40303101c00100210595001801400c81d0b403a90840c0032000c00e2495040d610918402f4280300810890a01c1001160b1405694011503110089001010800c14003003500080c4240000d1005805c0c95107211203480c0000d04000034048050101070f6858001400504001802c01951480903420b000d0142d1003203d515021590b02d03291030030706c030b07070307405290400f8007507002c050703007203030454469904481201812104544208110000b42c4251542c0554a04055400c001d1440e01c000d5000656068071790b4404030104030003511010884911100403000ea50680600c400003911a03c148000d5010f011240c90064140d00c0008103440c0000113148856a0b032011740e02070a07542541b02d003840c8241800388090040c4400805100101800e144095640c04842c40060100d40b0350402c0040000c105c16440f040003c0d0368800c004036009850b0010008800e09016514030114802c5d8070080803034102c0d0800c080c3c04154200441d2075504036412007005039004043c1d00004542031030401a0342c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 150510962 1250 150509712 150509717
    0x10914042d18120f020109050304091a090105150d090c060905030c0306090303131103010510030215030103050a030c0218090309040e0f100b010c3005030f19090203060421 75
    0xc40c406545aa050304220354030f1038200544e001e2500c2045200390405107001d50044201c0ea00c1d20341304c50a0000800040000c1d88a5130780b10310b82404075007040c8840354106c0300000c01010a00070108814540c584c011101548419a100304400009440c500c290b40a0400350396042c83c280e0501c0140761510320240b00241c807070b074010b500b0012083c1002007200d0f400050030034200405015807033b0240420440344044c0c2d03415400c26040001c81c615030184102268022519010445161000105188428000605641c000c0084007001c203006048103002d262001e440a03154006000c51800305400a40d803040c4e5a070800100c52800c1d2502d4003441100d110600064a440030f92200c289685400300407140302402d4442c9102c1c142680501c02410b00242c1080000040142d10080c80109180d54080c00804009681113942c0040c8207800380c910030700da1a9510170311a11405407600120110210352401203454681d8000140c805024160003903100d60004d81d2544e41d5028000d0744070700c0f110b429604 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 150512212 1250 150510962 150511001
    0x3040303080a020712031d010915180c09020a05090d030e0112020c06061309140604021003140417040f0b07050606030a080a080c12010308091509010914042d 69
    0xc1680e03902c005d1031000d00e5080015500c0302140b890b80b0030741210b00c11244d40c1d5103400242c4c014841c40308400329000000b80b0b010003103c111a855910701c004410b10140008461140901c000840b640c014940c42025080003410f0000e003400084040e100964101d00003003d00d500502c0ca540c0001002244c0c140c0d4400030360820480d03940340d036035403c0c00400c0c451044c1202440844403001603400302ca4416000b00c445211010210503407a40e414065804902880030602001c0000340700c1e11615044101c41c80202c03420fa02d55481c3d0301c4100d07400c2143c104611204100c00a40348010690003002800d00e06a0f541d119100d500b811400e0034401800a4000d03041494044001500f14048030300d030302e0343c500f050031041e150388030351105900549a9101000c1c05100c00401070208642c007030621804c080380d2030340c800201110608424003c0d420b00e24046a03940c0c4091213070704203d1220701c001500142000800680200c144100011020704008071600701f510001803c800500078407034180c11101030f11030f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 150513462 1250 150512212 150512227
    0x60406050607111f2001050c040b07061d010f06080c030a03050d061d01150e01020706030c020f010513021e011b03020c0a060807020f0f0c01030b0d0f0503040303080a02 74
    0x2403191150207070051501190440c00b00f042da840000400b040c0080c84084902c8800c2c00c08083c000b00264584403030700e1140e140c2e40104421050103203c0c0301d864035941090400e8507201c002d071402e40090b0400c032001c0303445c0e036091241c04110303500a80e0300700491000411f40d211402950000c9880e207402100054020842060151300d000a5800c98a0760500d01140c0c3c9a1040100d50300500343e07030700030041041e000c1981910707101c0007900d483c0c1a43d031320101240000e080080280c0d100c2a1030060140941c0000908201c20703402944040313010b1031140107883d4208850401319003100c0c1c003211122820504039002d003042d0305103075a00c035121094200609405800a00000e00541c000380c2d101440da5400a400c0010107100b4040a1040440588114005071300c0c0c21002d40012030854040b001807154002204002e28000380e101503c1c0700300800b0700300620703040b40114040c2042d072224a400c4401d00704050002000c2e940d03800032141c021409180c6841c2503103401008220040d0100070801c1c014130522 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 150514712 1250 150513462 150513469
    0xa0507140319081e091503130807080d270b0a090501050c0a1e0801050d0614040b06040b01030903080c070507050d1101030b010c0b1623040f08031303080c0c04020415020606040605 79
    0x507081d642c40188071f6104d6492a4405c4103800300240010568440441c084041050300340280c03d2800c0083c0090186584500c000b4441d0394000740d0660300720404201035408950001411a04645032110110321034040b92145405e44034161036401074480c00060207540c0c03030f0b801845c180c8440b8200800d5103a61588842c001c0003001d06005551044940c000380408200e403d40c0040e60421a001e0400040c2c81c0078207009003c1c4204442c2d0758000d40c00d11014001941c840e100302141e45e030b49612004130580f0361341ea5044013a001024100d9252160381e0012802d0780d151a60242060702c00c499100d40c039038a1130300040544100e1440d5070b06100307040c04907400003124544480d910040c9a00c441c0c6041c500104200c6134503500350b00600410036045150540c50a0f810000c1003134404120f0160303042652060010341d0703440741c0804d15018041d42c072400c0c0f000448210041410750300304000c0301d0340c0310501c1c0c00090803603011780e01484110003006141e42807160180007056011600307c03020030683d858171021 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 150515962 1250 150514712 150514729
    0x1605070509060303120a02030703180605070e0901050a1404061d0108011413030c03022a09090d02030a110a0803070302030414010903090902090a03140604050f0a0507140319081e09 79
    0x446c6081034000c000940c00d14401e07403042e42804078600c1d411b01000850704040005040039280c0744002070241f00052024204018010b041310b50203803d006100d4035021401c50420303904503101d5401925580005802c0c030b90610079011b1500504000003803949810300d4217084685515042c0501c02507402042500801c40100d4118143c2505000c0c0300340c03140c2c1c54100d040180e0801c400c1d02103201d5101c24158401041e0160283c584103031864550358440e02041640d41c07175554042030040e8810000c540d455403140020205c10405001142d0002045a03580c005642045500800091340442040140203ca030b5800141c42c43e84070081041e941c0c1c4e510000d00005490040c00c0740581c002802081c1a180d140f000001180c000000e0301840c100480a1501c5202c19103054a2600c100d0301682c0d00844049004a0703010780c041c00800c50380d4945842200940041ca034020707407602a0018403030039130500b9165800e20030302c100107041e52410105481e0160880091036003100c00414401c4d60015200c0484 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 150517212 1250 150515962 150515971
    0x5060f060702010521101e03021207080f15130c0b0c0c040614010212030f150402040b0d09170705060c1303050304060302070c05040b030307020d0503160507050906030312 75
    0x450326681c0d0704500050340c00d8400c01300340064948804454298025858a42074090310001010701e5089a840510140003901d41c080110204103c050030001807920b4189030760303820442d070f0944400960f2000914144140e002c0381510039000740c60000c01c00a43c80074100c2c0c0c8600c0f1090007904d0321013035450341c001380001c3c0d0140359040100010400c1c40b10404010a0706503100040086c4021030311001120b4060351078500403405480307400a010040c42100c001d5038428410304884c500d803542c2d0120544400c3c03020176540ca803c66820000403c04201f100010800301001110104480701285001003810050440b840d00d1f840c400d200650000344049207558110038140d8a00e521100701d24000200c80350b069100074102d04c07001800040458258014011040c0907800c10310715542d0300e0b02403209030f600d000100b80e030503001040040d006280012000351300d680102c00b00c9003000e5900340ba100056803090000c0d18903a015a200300314620308280d8280d0b00c05000e60107135003441c0e204800340082090103807 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 150518462 1250 150517212 150517219
    0x30a0e0406120f020307080111070204050a02030115030906060339051e031903021f06061202070303110f090a080309030d08040f080f04081c080712020d050903120a05060f 75
    0x201020f00f5541d08100c2000940b030403138020000c844461144030910351240350304070301650800d400607100106900c2920b040b100d03420f00c0c20b00030382c06c0c20303004a004000026040f200d15650750008070104891030050400c084845c9031070100c0c41d0441c1d400640401b1b5600c0c126400b551051405c0c001d175140e00141e03c8100c01e80303c9142c41c14076050b80010b81881c101340038900018025000c1c40c010f150380001c5440c07001c0000070b600c09001403030139203017070a07141c0310b005450104981241e859000e102550007403214034064030700086d80340340791000d0300d99960105a251820718404560359402d8a0310491841c01000342c04020740ca44115800407075100d4001104150a02601030009000d208032031038000d0445510014141c0e8030064440311351865007007030159241e00e11800313404840220318683c007503452000b0354075070760459958000304a03100600300701030030ba200d5000e1083e44003510081c002d060040c85090051a11548070310f6800080300401800011194205814030825484e01c1340902d03401d001c02e8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 150519712 1250 150518462 150518483
    0x307120501020409050705092b121205010602010e010e161401020a080705030409110304051209030307060e01062c0105090406090206030a0606080106050f19091502030a0e040612 78
    0x141400390080c000c0340c0c070000445090030100000c280e403100040c100408101d51180404590b4100140700705080c100700790181040008607000b103540440c034034107211103925010082d50810103090b400d81e9020f80c00400540e45030042e81104040078000e050340080c00800030301e201c00501c03101c035814242038442e00b20000b01800c24001030ba407090101c11155504111019039824075072520700c0d944d9000d0710500003564640055040584410004c40c2e0080d40c0040041010381000038480344541d01010242c3c0c0d045c8000c120303c1c0000b070b009009001075030603600000240103240c4181d0700100b10413900c4034504170800c503050000c0080b90700401810342e0b10540c0e600000e87d449141c44002445040c102a40c030410101c00c02850021942051096486503501c05080340d9075408280d8160052008092030300405016610343d0341d400780f02c000d44000e150b240040d64039640d880d50354403d0b1700094202d070050b00002456480380d600540301242840301500c2c1005050718140c0c09405009100720000e18440e0300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 150520962 1250 150519712 150519749
    0xf02120c0a120302070c0b03010e060a051f02010b03070602030309010507030912030b030102040509090a0c091e1112010b0c010b0f01050406081302101d240c030c07090b011206050307 80
    0x944c1a200d400381e01c50000030074940c5402140403150424030403810030f1070b900303000200c407070802081d0441103030000340850384500060794490123800445a4140210765981c14820880d40c0c1c04c0140b00020300715600910703520308202114900b5030310b00510079400d0506051640000a594400081000750300d487c00043d04070207940040d02a11681d880305a0154003d001c1c0b04000801044075103420784103a010021860741d0b081c0c05825181100107210030450711013205c07000c1d944030741c100031401400741c1766251408185210f82904840c00b030b0805242801c0100711413468500134400d03246500c0003282d0209220750040002480c3c3d10560062500700b0000c400458040380b00c0c89203003803015a0040294039840b8034440014509071400d0321144420014007102c180398100681466042001896010701c503507000380003810b2a500070036210b62984410000c0c1b185040090000002030501850089403003402a800100080b03000d0320088651864004200030660300064440d04407003420142c0786403441c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 150522212 1250 150520962 150520967
    0x3813030801060807030f1a010806010c020f210a0b091b09042307090b0102070b0702030601060507020d080309211318020408010509010209011728020403120f02120c0a12 74
    0x103581c0701b40f819070418062182d01a000341450032022400c1e40c0325541079071000011103241341410000f94000c3e60307280b400105810310303c070550a001501701d42074226442c0d100b4854071303117212103006980d003e0720b68040c401c4440b4280610305070a50304c11403540d144000b90000964008000c0c0c001840000194580100072070b03d03411b040c28041034401519240e81e900c1401c0c401512401101c24018002d040e0040b4500c00045d040d18042c980203001000d80d031b1708140301070383d855004031400d80e4070030103c0e2001000207500300010342c41141d24030301800100c0340240c01c2443d071a00480e40c040030641d0a0101c10340c11022403001300100d8200b000c900c144c18000c2d900b0240284035940044106500748000c002c00203e0540040024210070f981c4c815038941444a01c90f040c042c252000b00c0621030401d030100b200c10404031030124040c2041d0005140641d25a61600d110301c504080c100801c0031a050801c07141c0d01480031602c203241751f00701c040ca865811003886445090341c040c010612030016111081e03661 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 150523462 1250 150522212 150522221
    0x8040b0f0402010c1a04050d0c05070312030b090a020403020f06090d3327150218040e01050f060102030435060910150b040501030504381303080106080703 68
    0x64008415171001d00000d010841c01c000103c03010340b261700c1a44c0603400803d104080854541d50000f001c1c0c42c0d1181075583d02030241115601c60010144c640701c8240441c1d4459403454001c03803240078016912071031413050040303103105010814487c02043c060280c103502c6042c0c00550265101c60003880040c030603c1d00c0141d00e130641545010130841c4010302c40070400e180c1e2002143d0310345540045000c4503140c0c0e01840690740c08000600100c020402226101d0b05070300505018460034207241784000001010070101c6090303a440c4110303a07441e0700c14008101c150400054100c2821300c00303185000d041c0066031502c0380c1c00240c1c0440c0c40a204100680d040f00003104041c000b075422003a551241025510a80d80d54504000100264a003440e1420700500c00c3c0b4202d001c0350141d0700c01e00c2c20507141400540003090002c00644d8081c03011414468040385080c1040d811a00e5070300021980c14048070701941c1d61000402a000c10746500105002080d000400e0504648040c40c1401865981040403800362 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 150524712 1250 150523462 150523487
    0x504020c010603050d0c020405102402190b0106080711030a050708091002011b020105040507060305060103090f0303051504090f06091b080312151e01050408060117070608040b0f040201 81
    0x81c0107140c910200c0c5c96001201e400700c14021903051066841708407050404c41c5c8544610000002040310003260b035000610400164902801940e0141041107883c42d00450303483d100f102d60790403290043c800c043e00402815001401440d14089801d007410703c441d580e1080303480240c2481008035640d402c0001d002c0860340a03403c0600400d0401000420290207050110402c0c811141401285100c040c4144a41841981c00a000341607ca00e401d03c141c2c0104000350582e410103031505c0544006c19004600680100c0c8265400919454840071200c6400800c5001c0743c0b04038104003110020400c2c6402400e05241c004500080328401490b1205501c40074400d2040388856072000024030040c080040c08014910101040059940b6040c000c0031904000403282d0182ca41c3d0400300503506a94151074107031106060684c80c0075100d282c41861b20809a200e001c40c1c0f040b041c83c0e8800c4c648184040d5000f02030303c0c1054480e5042c982d6955450003802003000c42e802d04550001015613210309010300d4035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 150525962 1250 150524712 150524723
    0x60301020d0f02090a170604030305190c08090f070807030b0606040e09011415010813030201060b12010924030807020a171005010e0603030f070c080601080d030b01020111040504020c010603 83
    0x4200315280da80041e40042490511a42c030111000690748078010704030800d82500001f41c5583e81d610b0341c2c242c0060102074001c00180c0105600700d101401d00d482841d03944c03481ca4890303640703d1610614440c40d20381c048420592a80165404110507031001524209030b1307500480103144c42d503450021950501450b0b01004818101c0424408001350650200004074000d0740703105281c0d034030b00001444500d8480205400103c104000070703040c0007004c008803c0c243c8648004030b41d050fa0342070748100340d0b08803214010866640900410811800740b0441d112440c4c02c0600250900002c8200143e080035480081c0040500085140c11541c1d44201d00c809040094520180c0321451000640d0368007440201125862600d00041269901c0c0002076100740d1000340210301d0b0010641031802ca135040410102c2d80d016a002c00465241028480e46010f0030000005080301800c4480041c00e035a07050305611305591400e00e002c2841c0e6060001c94003070302e20980c0c0140c4d0315030b16074600c81c0c018585c0e507001402 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 150527212 1250 150525962 150525971
    0x3040623090315190b060403020f0d0804061106060405010b041512020a080106111c03090203010b04050403050a090b0a1202160204110405030c0411070605131a0103141b09060301020d 80
    0x101241e0118030900613200d14840d00e00c401c085035418005c0743c4c04905901d07030040341030108000615042000010845000d8164070b1070200036981e00300280c1250708480086408000e003440c640c40200000c503071000c021981400203500d0b020001c4020700c00c40c012000c1072400d0105803244280125040b142081414504555580702210b00070810b1400303004603400146002030191159000042080c080850840c2050a6180ca404c05a0081c001e201040741c01d55240c01882e40d05e96030310702c121489940a0f449456864410820007480e40341175800807401032405005903101c00340d100c0f00c2c506814060750300059850424036138031150340b0b81101009520a061200790341e070910a48020b0802c50714158101d0381c0940d0000100702c01d0360003d54020803400d03024001840415002d80019810450076080031418040f181c580c0c80080c00c20503081606560000700400030450242901d8950082d2100500b00a4407210707a4448041d180a01c0726214030644c0d008240b40e580c0a504030b4a601411200412 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 150528462 1250 150527212 150527233
    0x80408011d030901021f11040f0305010c0206070e0120010516090605040605090d0c0308040603090c09060302030d0c14012d0504080d05040c05090a02130602030406230903 75
    0x3400390644952400c0e569a00c150000c070740080010039600e90b2001600580200000d24801d1000454443d043da400c41c0c1e15441c0111500b03003440020300152013124055045c80d419414400d0039101482c1c0e2120456100b81c0802c84400c0d444140e030010034500f40b070281c0800269000400848202c003410300065440d00c420b01c84c0ea0f225050052904042c9911000c1d441507560105031524000d500c15500411020040d0b0341c0c507890103410000203580300321501c1908e2601c036240d0404c5900190031210103c0d5449500c81e09016060b10010700805400200340301e61400e40d0f005c03c0e1a0860005040240f04810400100300154000c1d00c201c0c020580b03000f04004c50b1542c069003006249001c0300070b012401540c84d4040c180607801910305c102e800081d010b240000041144004000c000e109480384102030001140580c0c841c20441e003d030030400005601e5500309511200124956807001040d9401000304001940d0400c800404140c2c180d0302c500040d40d0100b444102903c103148000c0c2e498040d41d1440c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 150529712 1250 150528462 150528479
    0xe041404030f0203041802160b0c03040b150d02060c010f0e0d080a1505061605100902090f010302010219051f0518030403051216021503090c041a1005070804 69
    0x144154002e503110b003114610300720103030380328461402461205d21004400200d100d159400030b11000001d020900d10500719074856107280c2c481680c00c0c61501000000b130109014094030780300c2d000400200c10b500380b004000c00040c454041014000d02807140800d04600145080d88102d20a502418090024041030822141c03510780e0140204041010b0304085003864103544613118042084000704012035003000308002440e00002c203010140044043c030500020814802d03011480180c882c04514500c8510400000d40303030080c91595038880d00d500400260381d0009481160301c5209500d4210a0b4290900a0601d020494409604c5004100441c045c884c103030300143c490514500c104d00c121003c003280984920517440081d03c164000c40c9104140c05041c00285145040e41341c4603566172200c1d5000c00da40c0c45011307401640c00701c0003004101c4901da0901c229402000b044404006201c0290401c115101c604002c10b805410510075208401e030156040340d00310354001c0c5015413140c0e60b59010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 150530962 1250 150529712 150529751
    0x110109051c1106150303131203030b010206040b0a0e0a0501050f06030d0f090501080a0612031815080406020d020717030a0b06040e0a0f0b04020c06010807060c050a060c0e04 76
    0x500c1c41c400311800080758003510412480425089000240203503407100d00c0804e41c1c0b40011020154180000c0003040c0340c01c4126806040200a00440542c01c00900e05028003158078228055056400c000d08000005e40080030381680070b03080d070a0000e118207121884525100011130010410341c81c0005020401c000d210226200d00d4045085481c41c20320710204840c40101d4441010109082e21010322496009009080d80b100c42030100148150b5a450b241c2440582d070f070300c290041031480a8100078148501d00307650182040c0c030700701120300028100003030842e000100084c0c5a1a808107809040c80000d4049412950300311140c86034200d503041080030140d200f903900d03141891602003082c0f042e05008080c0d44c200c80e1102c2004100d80c2d200207000000c0c0c03c00d0008206030799520440b096a45c3e0b141c0c8050218031648400400440d030602d00c20f18036001d19900712205000b07101d4906400140c001811800c056440387c0c2c00301d42c81080100581d507a009503030689510604200a071030108805241c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 150532212 1250 150530962 150530983
    0x302070c0902070503070b04030309061803090e1501050d0e030f0414030120070201020106030803090d030f09020609120102120c07061404030207120203190c0503070f0b120711010905 80
    0x20300c4100c607540c1122104900c100c490061140e00244507010229204c50009a40705000717080115842a00da42e0304001c642d021500c40c400714466082000c01d0682c800e10030380240000080303200f0380d41003109000c1822001d10034001d0409c100010340340142d90f00c0e42c00030074050101c1d404980d00c52961040010145d0802e0140e040961490701d0056a00e04e4140190110340b004124079052003190014586003541c4007407016815036494020000c002503501009511404811029203a085d4800c03070002c0c2510100760034400c10328102040207016070348642c1190007a4404980c00720714040407006045c007a0280c030280000c40503020080011920005c0700502815214402c10013072200c00500402c041347c426a03010380142c0c0240024000b10407007103040d4448500003011a55011403000c100501a000000c00b100c3d05205180d08020f241820840c2c4005400100a90224541004100c800901541171841100384d5028081426140600b04a281e00e90325540240050f00301810540e546184464 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 150533462 1250 150532212 150532223
    0xa09080d020a031701060503010605071b080d030c0314010b13171507020a1a070903050102030a0c09050109030302120a032c19170f0903070806010501080f1e180d030207 74
    0x1340080c00c056410b070165040e1045a150f05085900b444411140ca402c41482103d0b0311514140c3c0008003070303200071090010500c16008221040b21104002c06459040d0820800d050419420f042c804014170740c1503042d0360104000a880d020003103407008005055502c41e00c034600d041c035079201a80d400465081030301100b0155120554030303402d03803c0380e031038210032000f4124802e00740d440441c8005044900303810160500c2d14503e001e449840c3c160072a03000351109070039076070744104108489801403031100040c0400d01380207071030710b10b10b0300c2c0039445004c44210b0030b1a00c1c000280341c00d4164000d51003048440301c0492400f0f01003104a45010146021030000d9145116503020011009400507548400a502c07240402c4c400641002d160b03040c1c1c0040c400c4503d9100140410207841d2000c2000c5070043c00762800038070301940b40c02c0c000b401a00000c4e10310001180c0c00010172049158440d101030a180c404003081565a541517040550804658038041036409843d000304515a40354000d000315501a1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 150534712 1250 150533462 150533477
    0x50a2012150d080c0d110604021002030d02040609081011030703020a0c0f0f050c040b0a0e061314010906300c090f020a08060a210303020c0706050c01150501140a09080d020a03 77
    0x15082901c61003451b02d40d0100a0b807000d1300150050804a0206444403190300403603061403a4142c040090382c00c660806000118030702010804004d0400054001c102d04050411400140703c000c0c0b6818071005000b102815000900c10005612a20400202d01e80103503083c031707483c181c0346800000c2410303400060343c80d07100c1d10b5003854080c54544106682c2803001002c05200e28580440380e01151030050884d907010329010101c003802c0019001d01600b00301c0c030000f42c424641c18502c0200407076a40e034000d441c100194940071048000d040300d02d0400501402c902c0341b0000310b9480c06081041658001e841c426092501200810b42c035600070700011005034a441e0340c0c81d9201c0c01803116204240c415114119040046141d800341484424551180030f13160252504000b80b0095140800ca58416000503000040d0910f0450080c0708030301000c81e80f00781c00c50016180c40c2c00207210710342d0700711288084840028000c9200b4010101c00004120b01800e440d080d0303028800c041c1d11041c8407d0141d0206004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 150535962 1250 150534712 150534733
    0x415080a0b03070513060e07020102070308010b090603040206030a09061407030c021c0f0203040906030b0a0b0402030f16051c060e010605030c0409020a0c050f01050a2012150d080c 79
    0x41c0122180004064000d1400b5407501041010b031180c4001d014100e95501c0001180880615012030312900480d000980d4810003441e0061407020160300c8000c042c54184012003160741c0d2402100d810680444046d40c03280c480c8250130008000440004160380d1401e2003030715209034181c1c18540b01d4500f64a00f0482c00228840590311940602d01d0082031111141e180d4103002c1c010300c62440c00580c03d104483c106612250f8003011500d954009440c188641c20402907001c0d02400381c0c128080c07050b6402e41c1982445105005407c10140901492409040c40207100d54441d2054980900210a02400100702030303c540000300003a01503218803095140011a056000b00200c030301800718520700c0d81c580b600c0c11241e0b90007504024103190402c20200300b9440810b10820025901174105000011203003082c1c0140310446010612a0030b400001d881c041c09802d10a1040e1448610010040c145903516551170000c0a00c42c0141d0070340c8107940d6049036044c49800740c058011803040c0c4003160405180c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 150537212 1250 150535962 150535981
    0x31d0904150b060f12180304030302030409062114030d060f05090702030a020607031503021008070305060f010509012f0304061101050103410a020a0b090f091308041508 74
    0x851307000c000003407420010300c19500488003489a01041101b00c0e03a02003446051000e0450344141d1041d00180d101240c00d019810082c4110b400400c44131010000380c01d42c3c080c0d6001000076010016042680e04413440746844000c1c001c0f43e40c040115030040000589030040504064002c2c000d590140300454001100e0701c2c0000100c079806d05503a001030403180c1d9440e40440140083e80516000c0744501c5030300100507165556034607102c1d41c043d02d42c101d0510700801f00400b03e401c01060303d48203020001700501903907049401c13915114800c1c80c00d203451424801c2560610241c0c950158810341c910003000e021400040050400e560040d0f941c000c032440d514484600b039a000303003c003038940480305400381005555003005401d007810b00701c20769440226481c1501407514000402002c036411480306103007186410920350024040c03c0100f94205881c0401084e00449a66036990107041d801c40030501c80807081d03181181d45a80400e6141c1d43c1e83d220501840d1500e5000d08640c08207448030301140c01c04a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 150538462 1250 150537212 150537217
    0x9051c0504030b040f05010f0e06060d0b0a0b0a0812040608072303070e0d120e01210b03190303060905010e04120e120a0b010e01080f0a031d0904150b06 67
    0x8040d03500c0504050a6860b12168483d001c1c1044510f0360f400213101000490070300500030f141c9003220001031040004513201c0d003071002c000e001901c40c0100901c0500000c40009001e038002161080021b10f4480c01d20108103200e0113508a50340c00c0c81383d00c0c4c00d58410301c0708000900550b078080e0340b0700351b40b42ca40d075000b0b49a9001e26405c10310300c098140c1c00c40c80010144009154000318915040f55a282c05102158141e480018281e031a40e000b03481d644269500181c9a4000700003e00c0c010000104268001c000c1038400c9456802050b1140c002c40b13034035682084480e25200c1d0140b07a216400840e4a4060010002c1e8824138907483d0500c40005001810f01800768803540e00080d00200d003a515140c111196000c1604403075008a00001d41484000b007001a90412445000d03248515410701015005003d0141c1c0a641140d01406000780222004581c01ca600740e81410300c011006480c08240421130000340070345402426070b02c01c0209020040d00c00744c2c1d246072004000c20241e02a042800090b2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 150539568 1106 150538462 150538513
    0x415090512060a0e0a0f02100903121101060f06081306060b0703030608011103090d08091014070f050405030307030503040c0b04030506040308060a05090606070606180905 75
    0x8281d07900c550007840714008020700001d03c05c1d903100b401c00956880300038041c200000c3c3c284d20a60140c070001002c5c0d07070700c0041034a5041726100004d00e80301c4401041440e40d800e01200184404e003405601040e5110750382d0304201951059041c0c0f020b60b4010404907401c640d500400244210300401800755144255408030b2524070303042c0c81c00d0130359000d9021055168402c00503c41c0c40c0600007185968019141410803940c0e559024641c1444000f41105075000d040c900905071030440b4601d0948a051151a104910203600108448502840c0101d0303030154001c000040101c0d02036400343d5805842121603105854885555440c940c01560080395154400014481095041903c45038042d1003680c0f00113104c0c1c40c000004042d41d4010f01220701440c00000c0400074000d0b00d4004602504410103500251000307000298001c1a10540985084c010311071544c03101410b006d804440b4 = true := by decide +kernel

theorem cover : BRFrame.Cov 150359712 150539568 := by
  have h0 := BRFrame.cov_init 150359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 150359712 ≤ n) (h2 : n < 150539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
