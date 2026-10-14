-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1842
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:52:25.306973+00:00
-- url     : https://prove2.me/submissions/38189556-8201-4bd1-953b-d00045f0cbf2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 331115107 ≤ n < 331294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 331116357 1250 331115107 331115111
    0x1d01150603090302010f020f0d110901051606140f09060108060c16030c022106090d02030f07170a09091802100311120a0b09362d0d02030c06010504 65
    0x103d0904a0041420000242019000140e400011800e000203002d8001c00c02008010329209844041c0203031080030400ea010800510044564110754070003114000e0040030049421a0748410400d60752070304032041c19484131550705200130a6000c200f003602400340c010040c0704508103240f020040303003c1d100c02e400c519140314600b00d0425110f900c0150515034060003105400c0900c5548689580703c4006201091080e00002480c80900040c0d003170403001c5680186140500700071207048168808035040d0758070b5445802c1c1c4d81c1d12101c10700080ca044101f50b628181032904005c158003d48103502c3d039220b460903116440001680d14028004202c4529050029061503180b23030310340c0c103805034003503030b4019586250030004504201d0300120b8411000f151511a1030340da0080400c00c01c00c0b0444403000e00542c400c840c141503643e12118800030003006046601c56103c920203144c00c94400084070200740054881040b6a010801c0200c02c48156800594106240980c0d03c0d641c83c0014814144160703 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 331117607 1250 331116357 331116371
    0x306060f01300c080f04141603080a03140403090e1e01030609050f0d090308210405210a023a08070f0c08070f0816061d01150603 57
    0x42e009549403002d03000c0301c04100030507000391000300516100700c1602082c0181020b080807251440340044c0c81c4507600170034090900c0c3e155034641c0c1458004010341030000388120f0301290b40d40742a64481c00011403256904664030080c031007004050714440320305c03880c00254180a000010360400160404e46d00380f50860540c59482500e0704420b11148880c0500c103004480011003809080c1d000f03007403c980140c0131500c074500e14180c0295151380c03070402c10000038000d08050000031a1a4003c16101301103500c652410b81500e43c000601c4201078504554980c0324603081000b034400001900e05104412400506181c03407000003944a85d5524009400c0e000c080c04540070030312000e20104684c5940a40d01d0684500800c4080c0882101f43e40001c00704503000704800c0c1d4503118010904007d40c5c4405c54034201040e40e0394500200000d5901260011001c0c0007140c2023a802400314a45107008100100b0200803104200b0310004031082001407503411321380000c0d00002151266000c4070350901d07000882e4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 331118857 1250 331117607 331117609
    0xb0a060518010302040909050c0909060f011a0d05010e04050c04060b070209060d0804080f0606090411040203060a05130606030e03070b060108041a040b16030e1002131809120e0306060f 81
    0x5d1144e038000c440c0d860300e0800e07064184a00003600c01c440e80000c2c0c03105561034035182104c5950b400109d07207213600b06c1c03000001031054110b11031800038001c60840000c2e0038040520f15203002d6075403d0700b100b190f1090710810002406010002944080c00941e8204007290421080502c03912030410080c0c05030b1141408182d40743c40b581b510000142e000360115444a80303032201c0702d850340095095413005110702c0d00440c59501c1d22180c41801a030b070007005079040d48401c0d0244006500010310f0180d00010301c11000481c3e441e9003071080c0c1c501d401864002003060074880094201c3c0c1c841e44040400c0e0f482070080c0d00000700c0e0024171580021003400e102e28207076500d241490111100103c002d1050a55405200400014400c42409103101040500100780c00600481c1200c40194a82c0c486620480b4081c28808250f8002c100e030b080401324a004a44d216120700d004440300722203a90445940e10300d80c60910040050b20740d524032040c03070818108103104000030317601e41d0b02030301c801e11400407202c0d03511031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 331120107 1250 331118857 331118861
    0x302101805070e06010f2f1e0304061d06071407090e1e0a120311070c081c1106040312090b090607020606120304150528030b0a0605180103 61
    0x88150300000301c6402c69220030211100c1002039543c2408221300304c0c506040d09006d20131a4001807182001c10b0a100c03032014400200006007036100701c0f01d0003501820780b5044802c1c54191a401031080055a45a190480041c0240154100c01c401400098100f9546035a240d04407020107820401d01c1c0c0000c04039010850804201d0380c01031500030328106820724408408108101005c0095100e03040034804590b10311b0f00c80554443c014108d182c03c0b54410300580c0281c0c0150000d240001c0d000703040035826614014014039a4001c521b079607009070171038134032016a2103403075000382420300e00000d00e5048184801d0b034805014100805101011440c64000e504c3c641c060428250840881c5d80c548c02c080b40030fa919200c090b01c070743d0300600801c400141c1a01740a0103a80324000d106e80294940b070720300300c00d986401e181040790800b042030030060070030410150414465440700c00308a02072081486070300a0300f00c0303440f04109406440d241c20704000040c2c128064500e0f14040c54260040780d5803000040380 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 331121357 1250 331120107 331120151
    0xc02011118030c01090509270706030609060605070c030602070f020d080c06090c010207060e0a0b0a080703050604090308040605060103110a02030a02010e030301031211030708031501030b0409030210 87
    0x44600c801180c00e040010300c00900726480d000560980d100f0101910044955290307030b0084d15000304030b50002c6a080c95003131510140c400b600d101c402c130900584200701810480c10754896000079072620000d01042c44503200398002041181407961500282c5d075501404000e4520000d4665540810990300340810340540d8040e041d8010001200790065107007801042d002a2005602481440e000940340500000c0c02d00702860b0580040c40c469142038070848007a28207c43d0709401c41e0a880001845036a26009000b02c1105034a80d100b6514084000400f15800100b080c1c0c400c9003091010300200c0d41281030643c0041c1c1101c0c02284507175174a00168007400e4900084103c1072030000d0081d90855000c00a004500495802800160190300c00566a8042030201506140d4043c4d012424240500d246401c0d0200a03c02d590410b15251100e460a4101301d03561403800040146202e025a8103224148001c08121401c2055005541300290b48001c4c0040c6112800d96646050308800b0040c6c402030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 331122607 1250 331121357 331121381
    0x50d08090a0f14010c0309170c120a03170103170903160608012111040207150c020a031e08010608070e120a020103050c0408031e0403060c08010f0b18040c0201 70
    0x100d1081d58966440080042c0780c4604200040c1200062510303620400e096500d440c0c0554901200909000003040d81c400c90815511080c4550325040b81d840d2030710103800008214210140c04603008074207019000c13000d554202c3e00c0c0541100c2c01807000030011003040f0034000c00d99040540701c00b4034002007843c4c03c4d4561009243d2003244d50000612541c0f104440f81603908007900130000e9091040f2542d206d003e1000004c0c0080010205030011b81400d40c090680d207800303070420b00505d0104102400480e0f076a40342e07100058200d00407400a068002102600300c0d09142d499080e04103540c00b00070710f42081806031004021445c000f11740d4a52240200034040b50000342000d03459440c0c485002e0f076500b12020201c2c0868103010014942490080a950446070b608014502d440300e021008441c0403000c00c41504c0c40f0348107200110102c0c0651103281d44a441a1300e80f4142c81d4141044041b01c9807041d4041c183c0d0b06c03002c00c2001c030700c40d001900d02505c8150554000c54244117203441680545040320000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 331123857 1250 331122607 331122619
    0x63105120d021908070204020d14010305010207021c051e030c070602070e072a0c120f031106090a02010509030a143007030c02040b1002010e010b0910050d0809 70
    0x103800100804200900e5240294084a192608507400d034501400d2090001c1c00c43c41051103000302500700358004003150303c0b5009000038098024900001c03a001e007a0415500d9a5006c2782c0c0c041107061000081c10003d04116240f0542c41541e030f1202c3d0f0311122200c0090000c0349150f550340e000d11082003074800c00540d4505498000b03485c0c0c503000307554216912904030b504c0301003030200308050f024258150205031902c010bc00405444401a40191321004085500402010300001e0710000400b070b0b610316610a0b014000000e03980e040041403041500030f8a601900b014080c80b81c44d000000308a041c0d164203082c6141c40740906000030307050036441e18000d0319600d1510447d81c0c02e144007041c001c1e84143c5c40052811130107000d142d0114442604c107003101c0000c0d0f0402802011a025203d000c0c940d9100410100b0f010b04110049603c250901e28880c002d41c2d110000050042d10070b02486420840c195200031951804a00a08841314148901c1d40521041098807081c018001c08aa40c0180040c1031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 331125107 1250 331123857 331123879
    0x2150a0213180f1506020a080a020313031109100b030105011409060c0c091b1608070606031514040209010605160c03080712031a041505030111070203010b063105 71
    0x386000d040c0110f4102103e6140003441280402c141d0350003000d0350481da008006612155076116280d5000d4a60781c030640c80103004c3d01c08010b0000034080e0280d2b10410502c800c00070100c0034052828030280140d180803038903140600c03003140e00350b0590781161024a003082d000401c0402c40f4050f4804c0203042600003030b0015500f544c20300005481210f156099509400c3c1d07a840b5030f801076805a617400325400c100f00070064601300450740b14503420100d0040000a1500540d60b4968080360102d901c2124014114040315050390042d02c280e511104418030500e0548c5071070b030300180755110f0500a41041c04070200d40e4641007010510b60040442d4044a0540c030030b84c403400e011074107401400c412101040c1c0011504d580c0d621900400c643c10101c0d0069034a0010001308100140c80032100004000c40d26880000d080d603002d01030040e5000700000f8990f52000310340145400d584484418034040c0c0e1040003829210100c01007100a0079840c3c80d075503c054200008881c0408a10b80d20040e400001116 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 331126357 1250 331125107 331125149
    0x209090a02010f021c03090c15080a0b0a030305120c1201081b180f092103010306060f06080c090307091407030e0d0203120907080d0215060102150a0213 67
    0x34516a440d4002d88800031001c02c0c5a4049076617440303031820174441c50f00020074a621039010b60000304000b445400b90f9909a0b445030039210105600c1680200022402000d008030415a40314908140b9026038100a000b070a58a014020380f081803541544120a00d00140300e800d1160b080c0c40003041c185e40c0100c4996907510746582e0300d200a032214007010580039001d076442c0c6015428142d041481500382d44181d5036400e9903400d0428000c100c0d100501070036200d41d130484c658102d00e50004071004841c603245c0d419828240115001d41c0c02c40142c012944106100160b04243c16070b902c6201d880e0600e54a414040c0801d00300b40541d440038261508042c817401075065180042c1f4462002603808020062042c1d40e60395807203034103003003440141c3c00070041078550441d442c099a43c005031010880301c0c4d9a80e660400c5182c1001c40003e040141c005030b43c100c1c08900040300c15500b2481c240b00826050072039010344103c0030400b400b840145c41d80040c0000322400d0101c0620000d11030041c440d42d102c51030314 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 331127607 1250 331126357 331126363
    0xc04030204091b060503040c050424081f020a02190f020306100e06040501031205070c031b060f020607120903120c030e01060504050c03070f0212131401081e0c07020909 74
    0x1095403c5a02441000490990321520a4900c156003000203014074602e007405000c0106060440107918000036182c0c0000e1440c90200040104a0800241050030b00d14007480044c5615401c12a2414010031030104850360010710410541540e0300082e03174484003403420f0b0b4140a030070742000b505070080308200228070582103040c00031a600c0030b40d2402207a54950800044031030034000208080050280b40640324030800180c085280b1031242d0800e065100e031140c4000c06907801c1d030b81030480c9150b0414406181d10807060813044007140010001c2c0e041020002d0207410650340705200c4640d44107141b005042c071880007103100e04132021040092480100d4020090708170b9060b501120340c03c04500140f60b0429116070b52281c42c2d00040c0c1070858903507500c01c456244101040b00110700c174101e441c0005000c554018028540c2014020fa10540b43c1404020310b03e0489054905120328982000340c00c02101c441d55112403034500c40c00c2d91560341c0c00d5034052103000c0e1f1400a900030503140c0030000c03019400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 331128857 1250 331127607 331127633
    0x806010810230103110411030a061502150412030f1803110d0905240c0a050712021807021905030d060906051c02150f070b060102060912030c0403020409 67
    0x4008144155025031102807404240b02e42440d141c19400030041002c40c610580c41d08000100900105d0040318007501203c007500165001d5018aa840108100e4290340380545164554980091b0805c2c412881d0b850644400c005c10182540e645803440003030280c1700b9840000d20005403001040300783d0f640c010b0b80c20010003140c0200c2c0401c2d0901c5030f100c5481d07030000780c401608074142d85400c07a139800e020902100d0041d4000000145078055800c1c0980b0744101c01078085050440014407a400480c14164a000f1140e480116690307072080a000140c1c4419501600307030740c401c0403041c04503103031403400700c6c5804008a1964034040c04001044c00b000b9000c001049000d2440c1300520089c1c0d20344800c00112240c0780b01d8281d00518908002d0490020a000e00070064001440d00390004071081440c06503601c030030810300300000002020b1041045400e01560002828030040800e840c1030744e070081d602d00c1c6052240300d103d0030110018185070101c004070340103035902400c10b104149080c9410f42c846850313 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 331130107 1250 331128857 331128883
    0x40207020423060a081b0604050a03032d090302061809190f05061f14040f03051e0c0d11060a05031e13020609030a021509040e011806110408060108 65
    0x2c90000c0b41251030300c2c91a000686400b60007912100814000030359800c441c0b4414640c01c44828030000846a44001e042030045000e5142c104071b00300d01814284402c0050101684110141c01c140b8040c00d41c4141520140c980c1a11003e58520000c0e1801c00a00b07601e44203640e0040e501d00c01c005100c0e0340c04100c5019000c10540600c9041d8002200c4d0703068440840300682c1000305146000f584080450b400e581c40e505609106030710f00c004d8039124107691b0040d0004485508480402c00400030204200610304881480300c0c1c0c40150343c4001952941000c2c51024810340032034005106204400380007a9170340500400c80c1c6d40da145040c00c003404541007104c21080a20159105108141c002805180b0481c100c014000c0c01215980c2040941c3d040441055018420503c0410060310780308030b800b010032256001d560f25072400400704001d440d0300410080c11641094400191034041d41d40c120082e0390f12801c04501200d038220880d88501896004108610840d00005441c44010845486d0440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 331131357 1250 331130107 331130171
    0x41404080d111806031b16120c020f060c010f06080c01110d020604023705090703020a0c110607081c181515050d1104051b040e04020402070204 63
    0x204200c110301d5070280b121100e06080f15416101d62a00d004002550700a5a00c5029030105420700c059071415005400441040000e032280c04080c04891502e01142c04158502500f04021076400f068101d001c1c0c20343c050080c203000c9152480524290416036000440c0b2604212443d85d98a020f0b0396000c07000701950208900c40040d40344040c0114a6442581d03a86e0024503060b140c66003440384405c0c0d451049048954100c800003844105103011403607000c044030740b4040c01401c0c802080082c1c58042c1c0354805061041001111803900300400404650b00074165840781c0c110100415070340e200b5150b00500c03c40000134804e50015000a2a1001a1100004210002030303c00c0340d1400103651500504039034107550082c05c42ca015904610003409140e28085d0341c3c10b03507900c04100000e12040c4122051482408071150f00d003440d20507a58040480060f20546451a1400c2c03c418440c80c01059105504040000c09540322501211100c1b0f034090010000e0b424010303115016424591603030a2011 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 331132607 1250 331131357 331131371
    0x10905010b19210513051219050c0703060501030c090501060e090c090103090b0928120804062003010e0601080405030301170a0203010204080c03070603020c031602041404080d 77
    0x803248029a4021a20020390902208040e0b800382c409089034042d008000d10300340ca100031840c0c994020180561120b058155480e401e503d001420110420650f0129080030301542141070100002c0c1141e100d0503040040c0e98002e401540c1e400c3c80b0300b90704054540c6041000002c00c1180743c13080d5404507201004100308990305e6071402c03908208007078a07840d803044071080070072002c1d1408802410100014100010041000e03075407410080c03c2121215070035040308903a51039400302e0b16031200c000111325a90011000c0d40f40c0e2240b008156602c3d50300700f008100c0c40020204541a131008a0388104018040c001000800b0052070650090151040311041178020601c0c0703502414580e0b01459005001c1e50440e0b0070506e0b210281248a24074550521a1003c400b015840070300c020009041008090b059401150302450b02d48038566100404240c030400c840d1201c002d001c0107650300c0a00c89981030721b803103421f0300010307016011892a000c80c5d2041c540a0004002d44e080003055894004407062180c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 331133857 1250 331132607 331132619
    0xb28050405060307030518010c0225080a0803042f10020109033908090102060106111b04060503190201030c111c11030c060f010509070f0e011e02030301090501 70
    0x1901881c810580c02400500206607a6400394000c281c0c058124010031403d0348034280b0160a43d182030b41d88401680007107912030044030031a89404035401c00303d80103030f101510380cc41c10350380c5419500d0301078032552011001c40c1c1000a0940940c0e92081c0300b5a00f01444103000008580c0031301e0350b6981d05d104108003002c49800c41d006000d001402a050788030031440030050b00701c1c0d1440658001202c141c0030703481d5541c0b9501c5618081c07003c0d00107015043e41a12400d03c04006442c221043c0c114030705204550703415009200c0002201c2c0c403449403d0040903680d140101c0414082c1c401c0b50442a4540030b42d041107040c003480c0402c50000c0706d000b61703403e20540c20280d206507004661500f181c8402d402c696051614000b83c014450700790605407400c25088048548040d01f150091014840c8036080403041c0030140f4034a070202c40c050582100d036541c040c02d004c0000f4240180006103881800a4400c684403d0fa000f0701c1580241c440182c980c107154403900c1002900c03036009003d00702085190400100310 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 331135107 1250 331133857 331133867
    0x507030501240207080d0503090c040e030d0f0615030e160b04061d0d050a060e0318090907090213050411090a12331a09011206060b28 59
    0x100e81035500d56030103440c500c40c00b5036032100c800021142503109a21000a11135030070010300114100320741d5015240d0030406001410428824050b5219500701031001d02a103070007000704c1c0e201d01584580015404101900403020740001d501c82400f031840405a241c00c207400d60810300484041c403040d00c81d0800c400100d00c0401070b107402031949a145c00e000a100790750084004e4950820301d45416100c480c035820001d1a9840c02c12400c0301e06400400d4030108000b01d6004250001ca000805141040c4102e282c045601c600c0c100e2541c03003091110082145081c080c070006015100860056540b21005c114140903032045100d1075000e6494030005030604140d9006540c1600303401403003107803150700e0030242c3d02c4002e52000003540d80e805078601f8000c10a0710420070100f80507401c400c8021000381c81c002101102c3d242c5441c0104a11001656881940d40c20089810b490084800041200584c1001c9004201c00c2e08089614580020140000c40b03001c400040081c03004103d40031146600001129 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 331136357 1250 331135107 331135109
    0xe01030f090b01120c1a1201092009010c021008090f0c0607080f0f0703021c0302090d240501030c05210c09130b1f21020909010b120c01030507030501 66
    0x1c2c501c88580140300781241c3c2e4148140d00341c0207900c00c98505860301400d024842c2c065014a000550001d509071040021001d000d00512442004001805030f015100e0312006000c3d203111240600000c1003422030307000c0d020a05032550040c100c0150070ba400d02c0c0203031000c030301610000f000384110300080743c080800013032403076041303a01030261802c0481959404500d500442c081d0f20781d844c803c1c016086c041e4010000341c4001d5010b5030040014001c5846103100da800b0308100c0e182094010040c0401c03d80396600381d0007485d58811350000c2c2c58451080040170a1280b0300c803e18800d820000000140040580190300b6100c2c1154a25032001420300c02043d0714090303220504050300400072001251915041c01540913000e420b805030400425524140419808c646100071031001414140d04103d01000c01304c0a0f21401030149082128400b4101c1c01201c1a000240301340d28590001b14100c5080d00100701044000d0099106501c4d21008281c6426606020300d00103031800000500c0e0b03504c01c1c06114 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 331137607 1250 331136357 331136363
    0x10b07030210050901140c13050108060319020307091a0a05030c1e191d0105060901021b060408030f040915050a05010c0611031501030b0915091305030a0e01030f09 72
    0x3602c0c0c07048010702d0080c00000703044c01c40725581c0c1d07900c41a007034122211003845a03c440c1e03607840d916046480d580000d004103400c500d040000318010000070307860015500302100741c95460182c000340c9601c0041e1a00d44250072150032141800d9901110905a2008025006040b600c41e0f0340b1345d4072801410b540703590780b226059000807400f8141440b0f40201103400910318010741002d12548000d11510002ca44580c08903490710810300e2442072072110303a01070300d001d0502194840d02c0c01000ba00001d6450a520a03001743c3c5104034440035581eaa1404101c030b00a1480f442501d840300914494815aa0070610031241003a0818983c0b114860550340510b09a40000300043c0c04541040011a284e482090342141c045030390300c050300700f40c0300210060340c407810050072a50100311000c0001019a078600c2c0035940614005030510421841c9003860042c11041501c26442c140c0d11401e41ca944a00b8600000e00700d4080007419500743c584c0084086080a030a032000d002c1c002d4001b0070f43c2c0440310014000703 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 331138857 1250 331137607 331137613
    0x1e0a02010b09130812040c0308030f0f0906070906391a01120602030712060305010c2303011a0403060903080103060506060304020312030709030501050c040f0b0310030f03171905010b070302 83
    0x52960103201c845e4140c0c200d4018480300c1c4c842070701c80c0d89d242c100354000d5031194108400001007006410040ca01c8546c4411084080c003420304200c10090032a0380d250240b0028099903042c0c01d03010411800900c0c1064002eaa4100d4072004001c00305042c000c54030302d0a071104000082c80c20b49617800c41c43c006040f00d0201c00c0d082001c007140d44551000b5000503100b5003c12103040720b1042e00e0700321406044061030040000003118003000d14054903640d080c1001042070740d9001446d8034807016010a0f2411580e40c13428a40c52000070f04500d40c01840b61741c1004003e43e191500d14400d06511080090580380316450030091912071500300040c500003120025410b41c800e8640310381404940c0b01440d0080c0729401c0280d03986840c0c0d581c0e1400e660301101c000c0e00d80140407508224041281040200800c000802a480c2d4203010701c000015101d54000030345410041c0a001c010188924440c3c1c11250804400104c10300701201000108003407602d4080d80c0b141003c0000c10502803160844011a501d0f8000b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 331140107 1250 331138857 331138867
    0xf030703120504030c0605040b060102071d1308040314070f05040e0a0f0809100302090315090604140307080a050a09060302040b070b0a14130506090c060d021e0a02010b091308 77
    0x4107005000d00034001c8003003080c820021310000380b0034055035024030312070320301e0f00c0d000e18002e0300091418040364040711032800c400c0c2001020505000030140c006400150041d048100307414900746503c215800100007406004038203200b44400310304401503904048160581c40c0d41d6004000c26511548850503141d00100341c003400007180920003c09151140c400c0604050940380001c0707402c0455404900440c0d000108458540780501c80e0208003400704007031508500701303c031001e80d46402c0140003c14100c1015a002181c075420002e0321805944958000d959003140030008101d0b400090358070010032078100c00800d10f140240255030984664425042c186202501d41001000c4050656801d440c1e49221603461030f840031540512a440c08410341240442074500180f13805802401d40c9420b8105800000d41a52208102c0307100c410b0b03e45015071644862802042120000d1b000712244441c00104030340e501c0c1c1c064000340f60b14901102c0748415030b914100d0304040f200c503404004000b6201044 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 331141357 1250 331140107 331140137
    0x1101022d01090204060902040602152a0d0207231f0c090504060906030b01140904120e18060424030321020a0804020406080307020f04020901140f03090f030703 70
    0x10481400c0d400898494401d401140131104140c01c04c0c0ca420390000703014030a068040020400800c002210000c0e149026a0090042c0707207444540303e1042541030310341c4001b01d00c180c103071031001020300340441d42d606140c604041910744c026048000340100c02c03966042120045144c1801c1c90003c14ac15140c0b180c41c52000008106c40c413090b0040c080b540a000c2102d481e03610442014114201e000a400e50550801010588050303101c80b0b61102c15080850598480101d000e070456071010200c100c40c0070b1048150b4942c40310350003d0f0340040c0615248c0801900c0e121606009400035682000720078140041804510200c1c01084480555240c0c1000002d02c206038094121510822001c48212106104016a4884c1410000040514040c00b0541c505440b661000b4802c2500441ca08219540840c000c0a42031040a1050354089501d40d4142d006003181c070010141000402d0703803000b02c094001c8075a001610901c401d8450340150460005000040340c81003500b41d00c801d211082031384 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 331142607 1250 331141357 331141423
    0x1003050405070e060114030f010905100f06050f04080a0506010501030e0102040303021f060b0309061005120a0f06060b04080a11010306061b03030612150b04020301120b040f0f050a110102 82
    0x250405040040c09546e4031000040c2001540c001e008400000415500d4000f40909a600142c612f1200020360f41c400c1010315125104a8111840c600700a500e48201003408601d6001e5548002041e00440c0700d07600400a01044660580303500340c83c00c00291085108081c01c0f4000c500004000da408240701d22080400c0030340c2c61080c040d02d62008100c441d1500c403030764110b400544090711290300141c02d00c00000e004600c00000380c50196055a140c0a000c0403080d9105c000c104060000403007490b1300400c0c00b4240d0130034400352500440166665907641941030b501d1103500d106950720030080e40603146031342c401c1c000d4000b15155555480c0920b090420128500408000110300381940c5140c000b0350b10354011140c01d2500d020300c400c0050083e01c4042c150549613008041481144100014418041103620030380a0540020f407031072450380c80b4034110f88818504480517200e25020072081c0200310300054040402440380815000c002a40401a0f07a00c03441071114072070343c0c0005240c040c0700c18511 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 331143857 1250 331142607 331142611
    0x4030305030402210a0c0b07110621070f0305010902090108060111031611091f1203230c120306030307020126010b031807030807020906030a0b0c0301051003050405070e 74
    0x205040151205000e4400c016403400310341d41e8884c5c00960301c130401e02c2141035106000f072002c80d140300c2c900758903641c803148031102800b2060701c14400070401d000c0349501d0048810503808441d403003100702e05043d03101411555007014108006410030002040840c6d160080c0ea28030b55040c2c503408070700d8507600015a00c150304656007000c0c51001b4000441031032501c9034041c008a000d14190b0340c0000662080c081010001820034140041030981507000d1545910301c10211040e00c405030021000a00e0b0450340c20b0700b0078270305034100386a407149540441e65150080051038280b4080703036418201419a0602da0000303c170640d44c507070014803032440554028892100035200c4100341c942001d151409000c00000d0a8006240e0705001004002c90302c0d540008002501a00d1001080c84919607076a0141504c1507920080c05040000c001c50403c1d142007280d607084940c0100c94240300c0c03900f6202100c26810910507503101e5160701724111101d60082c42202d008903000710140503a2424050500d10708040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 331145107 1250 331143857 331143859
    0x100507021201020706051509040308011e0b030a0c090e1006031512050a02011b052a0303030403030b03011b050304141f06090507050c0d08070e0a090b03060a02090604030305030402 79
    0x40700418162800f8401000b0f014410400080c1a05016820030410040d080002d4040c0501e42d043c000880e8010b05035a0440317a409000c050b07161441c4a003c0965586a07010b0004c48034003205108013800076801403441c6c0d40956403895401946c81801000030b0b003055a48003141c0046040c14070000e4800d420880d5400289100900710641d522030341c44c049254000c0a0303940b50044c1100904544c0e100342c80c13186100403007142c01c00355810b42d1a41c0e515010402d00081707140691350400000840c000c00c3e80d02641400600740c0740c8910340b034240600585084d4240b58401c1d443c3c14041c02c06008075400160201750b5a94502d410341c1c0c1d81d0b03641c5a4031000740b6094510b00d84202d1682c11210003001003940c80c95171000c000031401600d028458000e50300050454400d2120500865846d0480094040902c6800c0e01d8030541a40360780d0001d54152240d10580394214010440114010015030800400503405030215002030b500c04480c00200d000704520550700150403c81000460702c01e2003d140c000b40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 331146357 1250 331145107 331145119
    0x50a110304150c02011805031b1c050304032105070201050c010b0301050106050c07080102031302010c060b060a0c110a23042705070b030702060a050405190302060a0b0f10050702 78
    0x34440000c120079840c500034241c00a034050a0f40c5085580c03243d07840780c062882000320385070903080500080e112030200d43c0140da00400c0100f860001da5521803e22910074035a12900c0110104d4241262607a0083c082079922000c80d10301c2c4d00d0181c04840040242c0b010325910b0500307109035a80112103503400100034680035074891071000c05a503420f101e00740c02041c1d661a1180d40352011074015080101d964440d10981e441441041800021003503a141d4555091806a0780c0d5262450f0540c000e00d500c507040c640009002c54010046500032001043d8a4043c200c4240c1006440c02048000515070140e00b65170944454018954491400d81d0322001d10001d2010404030401d4290301c4c9144418000200c4852803c00c02c007091040034410440502107c04c2c03ca49549402c8101a65901c2c010340000c40c1d1a640f04002802d1001c140708031102c01c0342d500c5502d840c02c411030900035030311401a02e000c2c426914000c00040a803a00b20040720070184050605014041350340401d548642028a060ba0411 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 331147607 1250 331146357 331146359
    0x20a03120f2f0a0b180c090907060305091f050a0b0f030a0605270307060501211b080114040b0105010207030f080a051b0102030a0f0603050a0b04050316060608100c050a110304 77
    0x90b0104000c4e43c130541c03074851102d408000d5107914620b0440101c440360700900101d0180f192a00c004940388081c0c0c1d810707080c04580d644601d042c040c50a0b0400c3c00651140a81201c4660780e041107402443c000c1c400840c1c1405880854410006502a0080c0440e41607100c1c12104001138815002540d020400440c55110b00e00303080403204580100c13580054ad9a040000e1400c10405140303d0a8003500d8500030b04100c0f0b07031035082d590a0b203e44460000d04a4a0b01051800d20031319010a050301030b020a00082c400324000e1800b001242a050b241200c048080c08000f0885510001c0d440d000c50360003601c0c68503032104a854842c910f51000c5041803c00070200034280005030911840e030000c0142100059807407074404125003c03110038a44540d0a00d0501c0e000300f0100714002000d06600360025011032080c0c6461038404e103584540701400d80c1807070802030303034409000d81680400708660b121015a01810701030002e5000301d623904139103034001c600244040040d080c0f00720001c504d1015188101e80c501 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 331148857 1250 331147607 331147613
    0xb090118050415060b071a2721120105092e03020a0e0403030c050403151a1f02061e22050a061e0618020a050403020a03120f2f0a 57
    0xb0701c10f103400c252032941700068540104100c0740000d500c40c14408000f0041401c101012010030641500074220580c502c08107a00c03450070034040400740c0040102d40300800441008402803503000060800d0040803907200000f0b0318140a15900c2c440c07202200007000c8149010000e2801001da40030a00c4540f0089402200503110b031b410780c901500240e020310041785440d14008080d60750301401d610821205000400010b0040828502d04940c0c3d164041151001107042d41e000c5004207840070381c01081c920808904000815580d104403c0316802e450140e45e0344115410b40503200300009604100074000542c6400c06842c03482e51002c0080c40441403e0507030303124289804002d070015281240da4503183d401a06a000c06070492441002091012510b48030030311812801ca110b21800c81070b0001100d03200329210300704540255500a000010054407420403903117051181d004030000c00d03422810801d4440c092080120b9840300f521103802c07000265480080c40d040144458803131449041030000c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 331150107 1250 331148857 331148861
    0x606092209051e07150f051e130f0b040504022104030e0406060e0d1403071b050315091b120d020c090606120c0702190e010302040b090118050415 64
    0x642c0503100405042100f020302e61400541904a6074055000130020010000030581d040040383c943d04010724418002c48040c0d5940c41030108400b02d28000d4094101025051009408220010524003844a4440c11b039001d0300764407401034465401c1b0910040001e8a0150002c0080e40d441114120108020301410390182c0e805450440109000c40141c0c00181041e2084800600f054504105010100c0340802d07800308450310040d0102403015000754034600104200c5150a910070100204190405201d900c10a00da014031803290151103408121403100c00c80040c014070f042805420b04900c0003003041780c40c20038100c007c2d03000440640040e0520fa010f00250741614815005414119031440c10403041100c002c000b079224031014044050510f502d1004954061810070320715a42d81c41c0b03400010300d06070b442840310f07035200c440c01d80102e1058109201c00d812a0305c01d0318144043c0000104001c1200003d000c1d507851042070802140035030080d42c1000b50424006c80d200600e80ca105543c00e01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 331151357 1250 331150107 331150121
    0xa0903020c130b090a11030402040f06050d200a030203250902030109050610020d020d0e0f0d05070f0812030c071410090203060a050403091e090f060302040e0606060922 74
    0x8860340d501e40c00c105207424030129045e40710600c01010403000c0418414040d40e80000340001c0d018039a174080c08407498410f0b40c80040039000041410140841d50728004440c04540c2d21186000710300304500c40303481d003412140c8405a82e4018050044d40b0685c80d0780c1d003484101c121182e280c03c07000880011304c0c40c09900c01907000c1c1c03441c104081000d00c3d01000b40301c04e400401d5030900441d4004041c0c00489035011501c01d200c0141c5240c42e03030384044140000385100025101942e0301050307601480c401c01c500040c1003001ca90a8004d0a105540c2d20744540f0388a40c82013810034200b000030170001c0d089154090042910610800140c91940d440700f515070b240006135000720000c59500c035501400e6140405c107850384070305100030a21152401745d9004200107030610a1103003154a1131210000e80c40c007095002c018101c042001c000705542141501c01803d80d42c030060780034074900b454400146201240c054401d21020304180d10781887c3e1000d01012145a1500038107800a0b44030407498400c0c10300400e2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 331152607 1250 331151357 331151389
    0x302120103150b0f010e041802030f0a0201090b04050904060b03010e07080c0f061305063010060503041a27030909091902040f09120f030507020c01080a0903020c 71
    0x200b200c0402e490104121601450410304c030303920103200401d2aa9100100e40c1161001340c17030105a0600d00f00300c0000c400d500881c025814083c0a1200c0d13400c1400203411901a4000d91301c00c102c050b601d02101140b40300318021583c000700c5e80c1c00010003103120350b0482c0c1000407020b40006082448100d031542407407181e07007040b42e15802414840c0001d183c014501c010149040350154646030020542174150341701803003481e02800001c59803030f21000806980010f1005543e4600c044104040d0b80d143d04084215082c0c1c034076001081022030034601c108143c0e841981e00103840e481d030301981a0000041032008103049040365281140607584044180b00713030826031b81940199159180c042c00c219880340c1c024200b984a522074001c10020800c104141e124268041c0c0300080e6007a400204100a00307104600500740113810b403000315415900101050039103410381c0d030800403034a4120003240c451140c203c01d0760004000002090120580784d000c048414481d004440c400c0d5150008500c1c2102251003803 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 331153857 1250 331152607 331152623
    0xd0f0c020904031e0f0c0b1018020d18020907080603030d06061107060309021509010e04020c0303090c04050907180212010611070807030812060a0807080c0111060103030e100302120103 81
    0x848900c0050b130545804040300c6041039420f1400d20b0000608000070f40344c02915801121002c265401c07910301d904405010048046103c00802c188d010010303601044400004900e0580c201e00d0840a680c81d84034015401402c4804684602034210b481102c0076020a6250104000b1446440300c01e12030380d00105680e07120f424011002201c1c207401c001c060b500031001c2c9420203800600680e18000351f03660904121810701c2d110300807100101c802c0d00c40000307203540042c40003035524003211000024601c00c403c50800c4078103040c1d142060105031102612014419800300100380404803210b000410900c807050b0300107041400780c8c071003227050070402e070f1222010809083c0146459902809071a010344040d03001031200a1460742d038a010791140d2215005148964404503c8907642e4a00c080001e00590702103c003000c0d10783e02aa42c03a10702c00300f0580e010809090170751000c07100200b55581201d41580300d0783e108020400500c003004419040c000d00b095402c01100041c22000381c9420b02a40c014419 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 331155107 1250 331153857 331153877
    0xb0a0e01022506050a0201060302030327012309060f040603050402011209120509060d050a0204140a0302031b130504050606040e15010512070515070c170d0f0c02090403 74
    0x60b05140c1c0403140d04020680703410140004000200125046a400e80341c00307565150103000807030040c4a82e400087d4140000035800b803c0441650040c1a03181d4001d42da500114020fa006584500005030f9100480040c82a401c1c048038081d1302030000c18001a25051400c22019440da91591140e003201c80400d41d144e00f40030655900c24440308070b1001d00c840800080d1040d8032000d40340f140a54880b0200540040c00d410b0710f8403100c041c3c40155a843e803080c411030038030700b10401c080d41050060040d405000310b810402464005800d4003200d80160143c94615145a050b40c4c0342c100b814421908030401c40c00002c4004010f11a00d403066008030003404440c2441c504110179607201001048160b4454a181c07400c03040010b880d50304607070084844039407403080d640d00d103810030580f640003941c41101c5900d50582c4519060042a01501c100308003562603490700c10b240320300f40c10b0300075503031050380300345421403201c0c0c001c10440b07000d002c1070704042415203142d5001a02c0c2c1ea4080f5012000180031040c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 331156357 1250 331155107 331155109
    0x7060509010c14040e070507081b010f11090910080a030c021306060e090601030e030f070c050607052802060417060105090105062d0f041703032205070b0a0e 69
    0x89410380c601030902c0c00048041c60320b009004140a2030045c0c0305804910f03008145124000d1045499495000076115294401091103a15003426118901c0c02942070a2130207d000c1441e01c18115a80303101d20a050400b040c070028001807940003400c801040390b03840e0010905d401c08024950095100e9a0340c80c01007071840c414411014214108211a241441024081c003038106014021502c41900c0c491141d5907000012405001d4100c454a042d00000070000c00107520107008224580c0203c0e200d100303035541c4506016040c07140e6580a00a0b80260700801c0d42c003010b0300c40b00d281c810646c12250050380007135000669a03510035400700203244140c034600140083e00340200303401030100f195010305a40c0f501e004200c180c4500c042c0300030309400080c0311040840c032201c0a000c0203060010010786852540c00b400d8200d80c80790050f5080a000c40b100da020140b0004120b0b44591902c041504c6981c8110740280441d40080b241218140503403040490583c60070005007416042503600c00e01601c804030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 331157607 1250 331156357 331156361
    0x3100e0d0207050109030b04020d031806111507140310050a09060603050603010e1216120807090801051902070510090c0f0506070203060c130e191407020723060706050901 75
    0x16003e00d042c000c0c144400c01c0032400c0c0d001c40b0303a802901907034501c4004447e80b500f11542842055912204c0381002030210b452075100c403403509862300c24011500304900da80c000e81d102d8002126020000742140f6403e0402140c0e2001541c1c00c02c0c1e42c032000014032a12200054520225900000717200c4ea03440c401080505c0e03141c041c4542200c4194000c0215601c51842d21751120f2076001d603080182c90000e80d0303040414034000200502c1e60012411107088040c050014480b000940d9080d000800059004c1503e100c10306c1a40c2c004c082000950212001d80540040a90000d03141501d181c0075559101c0c3c0d08001c203010364490b04c0c1c85070031503025075070400007441c4085c480d80c1c101c240075010600200005803070004c0c000e070308408401022070b2140c46030380f0141284d0585800c40d038850008041441409540601010344094083c1d1090201d0100b030f900d5001415421070302d200c016407250408102107011301010000035100304400214503041403002c91403aa01906044480710364440c10440505028 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 331158857 1250 331157607 331157609
    0x20c010f06241805040203011205010506030d1d0103091505011a0a0203040306020c0a02030304030f050d08060d020111070510110d080f01030b0601021c020c0a080601060906030b03100e0d0207 84
    0xb068121000780002d010b411820302ca80c070319003041c0050901503203000b14140521200800300200107558035070311607490380c00c04001100308969540c2841e0110300e642c1b601180780305003503545a1794002038580310819010321083c05944203061550f01c0c0a4040030031014004a400c054242201180c40e514103000c101c0c030081070f004100c100480c18042c803040180d0100c00c039011607800040160f102d040050b841e9040c400e104000944c1403200007000002c009000c507c4825031802401501c0074000540d6042d0703215032003200c415138407a0340200351000541c05000928640030007031080ba05c20316140c5012031400f00301c0340d0710440800c0389050040c2c082c1004001ea141d5000c6c1c28070b07082c0700508005506172030126060000500c032403c05000110564403c0102c0703050078038250309204c0c031128980c00103902c0c0d02098140a004504004001c03d040c07500288450403500a40e58107002c8030b1408008900900200742c803240e02d80070350364074040f01c240c0f00c0c0189200d0041c2200a02071006100740044d10305846 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 331160107 1250 331158857 331158869
    0x70f060506091602152205060703060b03041104090f06050112050f03040509072106140f03010c050d0902030a0503030108030406110703020f010c0614160210050c0724020c010f06 78
    0x220fa0301c0d4020959021841400400880c000012540c560b04644901e03002d03407804030600540d0f0849040188040011018050141510704008150b15900100b41a00c0102da018002c6840c3c1006410282401d501c1000c16a006d60f41701100c404441c1c4d525800d03a00203038440f22205038002500e8045c8981480781c00700b660321040066181510f444041412400014400001d1040101e010040c500d41e080c1000211084d6038002c109658840d200540240040b80800e4081c0d410760f07800d642c060070305109946141761107488240c2400c9603407507288068800300c00120303014005e12150380d000402c2040518060005140516117031810700000604000e040140390b0682e40c04070000b04090303203809400e20b10b00c200070310700139a040f107450410001030700d02c0c02548010306105804008030094281c565486070ba01070790a4cd03503400e200c800020285c483c2692a948800c400700480c000060203403505c048803409608000c83e440303c841c1000340c101d0f003001c0002030310b0744d4407100010355200b81c91041e0006486 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 331161357 1250 331160107 331160131
    0x1401020c041812141c0e010504050a080c0a1505150d030504060810150c061b080a0f0e03071b170319110a030c050d0503060904030f05070f06050609 65
    0xa1041d495241040900c102078428800e840030040320750311a20030078003000c05071300300c0079520402090040400c400360264910070510304403072030160100c107002c0c0a005c0c80e0000c00070564035804c0c0d00c80e2803a40d40000c0e03086540380304d0111000006070110035103880150340700c44006920b01d002650410640e4070a80c4851140740e109820200182d0400261819076105103402203035592907444801c04000160031214180780f0f44160881600d52040c072008815202e900c003400980c4801900d8000c440c1d001268101107400f5100040750f588503580145440743c5041c001007981c1c1c861401d51400c1d07600440d015200b156a030700740e076198072800d444207c0050240d5a9442e42e82c03071810003102c0e124003443c5c11a42c200e158501c0c00341855481000308441c80d0300060b0607108400e4540c130340907050480c0c2420888490003140c0c075140419008400b9039205640141954a460751169002c0300c90452a90036081440710038070400e03010819810b8440025841528005507504180c02042044a0000c0c04030700011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 331162607 1250 331161357 331161371
    0x120c1d0402040605070b0726100f050f12030d181103070501120b01020f0607030c0207050f0a1206060306060e010302181501030c090810060f1d012105071401020c04 72
    0x44d512000b203511032900072130258800d07100d01904850710b00100c4200a200c05009a002c0c00010103a603182d4010085404100089030b07a682404e0018102ca10840394400c5034400d90210604060400c3c80b20140d01074152803034020785483c0070003190118a042e500145500c802c0a0030010700310040303820b121088000300150b62600000814016850a5800c00c10352119062501a402044000c00c2410132805490b0a4982088000e0060249076034040043c441c050300000c00e4148262558503a04000e0f1001c0c00c0301c5d0801c5c95413105008210b408881d0165107090000100c0c3d0a44a4038000e40b070240401d040320352550040100500e2040503114520320b07020188a4072400c040c0041c3c8007100300f030030003050711840c150302a41c8400d1541e0003c0600d0040110342d440403c0294000c409907246074160403100c82c0c66030b910319889600810800219000140144450303040c645000303148019032150000e01c241140d030707514100b0001d075002044140c17060908003080c2d038040c05045132084060300c04001038 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 331163857 1250 331162607 331162619
    0xe1b13171002040e071409040501030503090a0e0609060d150c0519180311040e0f060105041d06010605130506070b10060309080706051506130513111801120c1d040204 73
    0x201340060441000d105002004442c0301a044003698418000108100a1980e590a200e500d80d882100994031410320200003041c145401202076008000107008032882c0d59510381402070076000107800380d074602c114450364200320105000d0f96840080325075a031034951150310f007151044204c1341e00000074400982c1c00242c0c1451110680811242c10080e0f00700f80d00d44010103d4001c0c0034424905a441c0114505036811420000b4168101c40d4213640800c17501100d540c07030b6080d07044560035551140e00103100401203240f02d0006802080c000030500980c103659807001450951040c403080b40d26803600c030704000a8a082c180314000800c1e03181820300035110705588808071442014030003001c099a4001144810031040f0000081c80800b408540d03030f445801c0140940368405124041c401c1e8076036224180004464014034882504107090542401c0b9040981d491011541d0442ca04202c81142c40700c803548414081c03007103181c50b140c41d04480410b04032768a90241d03200024041c01140100010020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 331165107 1250 331163857 331163879
    0x16050d18150e04020906070c03021c0b0a0504211706030609030d0e21180102010c0503040f11090114010327080d0f110408060a060e1b1317100204 64
    0x640c00307079403030954140c0551900203030090040030394040d04208045038680c200507101e81120141c0e030088403084030003052001d00c204c012440960081003440c3e0a40810715041030754004030342080c80f1f07460f0000d80d82002144016200b003c8980700700004c61100d15120002114010a900940c080d0042e08980c41c04010f4669244510072580b00c20b039540b03400c2c1031903250061003000004410021490400c20802801d6880f94002d4036820410100c0d008024010f5801449045444040743d00e03a24113550300d40e12502003606c0414015125984d59100c3d001c1035984130b00d030300c501800c2401d44961240921400050488120f40c200000704081958405075409944c2c4d007040307500d54041c00c0260741c4c080309040c0e18040c0404618040810341013620009605602c040034005850101c2e0803166250358400c4154240d940503c22400009034820105003561400c0010300c010191007070085140029a0020618030041d030360140d40094030610a00b50548810b10504591100d040010350406041c10100d50ac = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 331166357 1250 331165107 331165139
    0x81c0903020c120705040c03140a021c0e01090b070906020705090f040b07020a0c15030b0405061003020307030b1e03150c0a081905040309050a0503011812030216050d18 74
    0x111502d0f03107044054415004204007005000c0103082400002000c100c00f40151a200c1b05940030803400b00e0010307104030300174030035111440030912003440f079000c002a0303941c010020001e02803419500c2d5840c40c40072481680640b40640d40d41e944d2251141d1410400a06003401c941190b44206520424400226102d5140d9504590889900c0c02141c981a40c2680340010030036000f0400784030780400042c0c640c0481190512401c880c0c4041c002e0454050800080301d000301d800e0b6901408201b001407a05109501941c3e004642d0b080000c0c921140c0400034030512000200c030f44446001c042c403a0002d04080c0400d50010031100c4414191b42005000307072109001e5210800200000c18000a009003001d0100008081424004010714142808c00901c016110b000e682d028001150000030a070805214280045850f14401180101507a4400c40c2e070300110078050040603000e100250344139100b00e02400907140f20f10014003d441d01000f000e0035041215a80004285e4502c404000035042111005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 331167607 1250 331166357 331166359
    0x18050409030c1515090f0516020d03090213020708030a0e0606180403020c0a08030a200304031118070c121e0c0609060501080a02040e07031101080a0902060304081c0903020c 76
    0x11000b03415240c0f03418020402c24120a001002100d8001001100c0e40c0c40108407001c0d4003014059941c40c0703000084010049401000141d00c440d003c0c070304652280c1c2c440f81c1c0c0c45100030400010080035058200c04e03604001d80942302001c0c00018041c4600581c40b5a03944400250301403d6249450f4000a0303805900c020071b50030540d5101e00040c1014030074005408181c0340241503501058681104942d01c0c2c20030700400b40490100041301c0c601c88120121000441c1d42d2000461a0030f042d030b656420041605480150000c451170800d000c1200f2200d9074500c03508980d03984250384141401c0060b21031840448240034448110f580c1c8102c0c481e12540240800200d0034030008540756460300340001c0c0610700014004c540347c100081074415003c00c0801003140216010f110042e619080c4035180c43c40d270b02c4014800902029907550950250902030343c441825000083c419281e50042200c0354000c45046644140016000c140942100450713900240e03030100c2003205a02950f0082c0d07507041d901e0082 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 331168857 1250 331167607 331167623
    0x5070e12071d2d01140a032003010b0d030305060109090b060405061c0903020c13050906070e1207080105071b0c0b0f090409080706060b18150f0a18050409030c 70
    0x5040941da2814010700c0c41061040602040c981420003c08100038007441000c1c078881e88030200540f800e20788180c00d42e9001008000281d050018411104001d0940c10340c00d5500c44041a0042e03484030f92001829020352408540361074840e00040a69045030071a020a5140c90b42c0c5144507220389003034805955080d2b443d130340d0303500b011b01c40c140e01c940d000b1407080c04240c00c2050840400d0307408a0795042c10081550340c001441c1d0400404410b9070421200003c3c030354066000203500c1c6e8400c80c43c2c046948006400722280041701e03014a800d0051079041401207070746039010300c042075900203503818840c0c41c00c1c442c3d42c2c4c9088041c0d42ea21800d0700284030b10511030350045100680405104111100802c004008000c8141c0e02d1030281942c0e04640e40903071307030103241c8800007420380381c010704441c072004440c104e10504514a030300b04840300180d86038040c48070341b0500092200d414080020305070050180c0702c9001c1c0d0a840c2e0307402c181c0c40c88180c00140c041c60400d100c24000a8221302c1520149a0100311 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 331170107 1250 331168857 331168861
    0x5010e0a111012050a1407050906190c12031a0612040204050403270e060609030601060c0303020f03130203011b02101109061c060e06010c080c010f05070e12071d 71
    0x1049032004050b0001ca40602c4c6400240502c102c01c03980200500703d0a82d41007201030360344140071f6919005100ca1b5503003090040001c628020b1380307048510300042c100d081c1903020b441c190700c84000110802401c039012039500c0d55100701100d00300414012000b01140c0f81072420300d1802c0d804400e802c024200a000e541c03140041403c0602458400e1104640030183d805052056031070803032100b6161191002c2e40f802c180128800d4103100e070854a881c0c40103002068070341d1038888100c580714146102942019828400a0700140c0f103680194054000c514241620303000c103004040c2102c0802c1e41d00d17803005180300c0b50704000c0f680101d00750500f03001d00e00000400300b0120300c0601c09841600c6040303910800004446200d03468207140e01007200040c2e681045a65180d6004190080c002c0c0e4210340851255032100e800607500100528000c2880d000101e4115444012102521010343c0e9040c04103045c9640c86001e42041080495804607a00007482140c0c5803a40c4100d2262504142e0b28040b88c203080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 331171357 1250 331170107 331170139
    0x1d0a03020105182e0e09010f0b070807080d091b0807140103020415180e04030c1e12120f110f13080712021c020102120d060503060103050a05010e0a11 66
    0x780407066803644c03e4162132051000080c1071121031629060000300740f8190780e0303c0c03d90400350940c40c1a92988403210b84418101049103502e0f4002c003004948100c0308000d40c0000849140140c050064006004030300c3c040f986c505030360205000441e6080f109600b440800000c500000d400c0112984145031100d075003502c1d40102c02070301c107a412500e201c03500651891786181c0c0c407080b103901407210301c0c084901c0035440d8004405a0081a1006400103075280032540102e003101400c8031a40311844441d00300640559203000395141d40c46801c40c04500f1042141c40d01f0b020b40c1c010340c030100049040800c1702c101441c0c00c6c250300380540d681d55441100045040c1c03404003800107415002d402d0031000c4580050ba2041c49104403501884228007804c1d82c02240005012050406886664142c018000305040825100403540002c40d80040071500e403100050151014400300d4061401440a881c040d41641801400e655604c05085240e0f032000c046c030030108242500801c4034480440322441c44600c0f0038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 331172607 1250 331171357 331171369
    0x905130c0905250206072304180501050105071106090a0509090706030c090303021209030a0c12051002072415080a0605070816050a0504091b020c0f0f0402070203030412031d0a0302010518 82
    0xa03c0320311f0200c00002c1c0100e883da407400903d460040001005002c140e80303c1c40111110b0040070401444601000100841860410b01a159020004d0400c1c144c0703980c0c800c00030348119000c0d02d42402e15006038106101e100d030700d4020010380024900b40240083c1c61070354002c0d41da14000c980c3c485130b00c00100c1c40100d103503824802d401002d070300f04040780110ba84661904500b980c0d9100d080364580b10340d1140c01e240d10114025071b5092500001a803141c00440400c80003002c5000c80c030101440e981d180207120345241d000105000e401031000900c410280d901d4440d0071a40007800e030350306103e40e802c10400301014881700d902055900d4540141c07103078042c04c0309441900640c0c0181c00d649040080141202c1d042e08919492020580e08440b00186c40e84280a1503200090b007880c6c00c5940700c2821401400d00c1d800a2010078809400ca9103072035580e4a80b105000b403041401c130002940c807a06c10800c20401c016684074400100c45507070040b451a40023034030500c510710000c400341081c207013a40466070b148 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 331173857 1250 331172607 331172657
    0x9050f0f06071406040c0f082a030114090a031409091305010e12030403180501050412032c10020613020904050a050607180803040b040905130c090525020607 69
    0x60004c0310030a0801e484e258802902c04e0107413102100944000003440000040c031002c18004442802034080303c900080300000d0044800c070781e015074998080a120301e13444042c5034130074545103002d010b80201c20304d0000d0181001041c80d44410005000b040c11654070300441d550002401264090440214940383e40074001040c0d1010090240340300000b080d04507007006500c42c5109030344d0841090a400c03c0d02c19400c06601540780061000d001c18068654140000d02c0080c0c024180a401c00d104129100490304240101d800b5101400c07401d40718070305005070b800414903041d0024000f01e15200c2b20300d403500d80301c0002c060b10658000020500f40f00080c00f0140069801c05e06480551038580000307443c140c02c1c0302010442c41c40d01c1c01c0001c0c0150f0040181c2d010384200408441c81e09140c551410007408000d06225000000010700b00c0001d410b0280d580001c041c0d840c0081900d1600420242910030190000b40060702c050403828910f41d400300303606612801605001e9038100d00c1d980045810540 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 331175107 1250 331173857 331173893
    0x4051005071e1203180506070f03090c090902030c0a0e040201050304240b032814010e0304081c08010b090909010605030f0c03010b0d1502180604030303020a09050f0f0607 75
    0x1c040e56402400030b000c00b4102822515101030084000555010440c9022040080e02a801c204003040712a841116427005100c070f0391501160080c0c803030f1180b62501d1129442812885e0360791a455085060500c9448500701c011140241d00901d444008000514018402410040000000790400440c40f06181c0b01000107070b48503801d245030200300401000701d01103062086c40350f8002001c141910141c00c0f10f100d201703803d0850000103a6a281c1c9010840156050314079501e6103800c0c0382003403080020b44010401e01000b003007024240800c0c588010045c007000741c10040c8000040c05501c902c0700c100c5000fa042510780d1445030750748410942c014440b5406c010b030706002d5615191241980043c0e0111810001c400030490076082e0810001c9032800141c000308102c52903490840141e40581c00307000000540c0e82082c0c5d01140c014000744066009800840c0407d602062200c10540d00c4082540642030544000101c910304600141120b440605490700c101000546201000101e124030031141034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 331176357 1250 331175107 331175153
    0x19050306180406140a110f030c040504050c030a0608120a0e011205191116140a0203060a0617013312060b090a0507050304110d0c03060506010f050405100507 69
    0x406160183c06410342c0c104c0200400c08483c08a51059518496002c0203900301002510700701180791050303044c2e08003d0541100d13410500c40024240c941d4003685200303081c014002641c0c2d180580790f41d401c4490f1508000f0312640300c0350000060844c803e04407070040740c4a06210140985400c01242d018506401d0004440c1c181018404191800c4440d10040d450030f00d014003440c06118103c6a05006e140040785442c1c03151007200c0c0210300382d06842c40440903d0310a880508541d6008640b131700350240d540d400f80540c0c3d918104500829004401100c81c140c400a1007507291000d00641010019400d505440803a865618040c1d00409001710040c881e001507c0303500302d194100b0400030700e280e520b03003401001402c0000340420f4881c8100780c07180920740c4801c1d095466589610a09100c6440c0c0d86400110305070803080420741e0714080c00000c620030400801e8518000000410800000f40d624043c080e0610041c00140d07075590110080c8465450080c0c5c4403040da050140d02c07084080e2100c22005 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 331177607 1250 331176357 331176361
    0x9060d061d0d020111030c030105012006010312080603010911090a061a0d14040f080a03020f12010602120703080417090d0c0501091a030a091506090914031905030618 73
    0x400003107036104890600f83c0081080c20703a0303120a558203210440340200660001c000520642d801010121310744203090651225144c0034400350b41c03400500780c1040d2441c0164080d01e11301c3c0383e800044154404015002440751444965808c0361101040a0281c0702e210780d000019a03842895001c880200807803002e01c0c03003001d0f5800c18100c0e0356000c1c08140312460b0504003940348a4450050180c000c90380030108072a01d0025848400654020b207900008050302008203020f0b030310184d0064656050300d03802c129419450060060b1810041828011101d541408888040b82c0c100042c01d51058000c0d10948020009030391080c0e843c42942d120307030744c0040b0b030034508000e10405e00f2001c020744200fa01e030401c20320340b9001429203000141441192441c0104001040324505421030001548180881003290203034440040942c1c840741c000f06880c994904040d014001c012020016010019010b18607154011444040703400d4420000000d000c800000300f2115103d0b03461b1500c061650304a040114 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 331178857 1250 331177607 331177661
    0x31f05060625151509142811030f06040c2c0406031205030405060f15010324230f030d0c0c05090c03070809120301150c02030304030819080609060d06 66
    0x8041902172402c080b40307000c00e02450001d01404840c090113000c2d1203505070020200310302e61004802403d46102e540c4448103480040c41c108013450040340c964552a1061800006100441d8410350001c4200030b03a5500140b1084c0d5462050140304244500154000300601d01060241c0700315031000300041d150180030076409a101000e14000e40c800c00603a0f2050301c611102540004081e110512100e00e41d45003640591700a41c440071060400000c4402002d030011210310f02480b80c0c1d449080f010201039000b003030425503003032000c00603003046403c6015040410b010a0761002500364090500c81100614000e010005e40224000c120061101d001d503e00710309082442d820546902c00400d00d004082002c06001081550984600241d400e040da882c0075001c0d9203588121020809021801002c100583c505000070070103180100511541c075101e8540001d11410345c48a0602000b070030005002041d95602d0b01182c01c0a01120801c0303440d29241014802012440c0300744480b00d0070005130f013400c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 331180107 1250 331178857 331178891
    0x803060123070f0c06020f03161103060a0e21030f040f0b10060807022113050303070501090b10081c0512090105100801060f0e0403020c031f0506062515 67
    0x15032849101c4e01d481c2e199030b501007070b81e55000300f0b91700f01041e030003c0c0500c2042c0c10701d8506d21054113000754449000c2c4681640483e0505000744c4940790301a407039030310444002004000c2d0905203412085e0354840b0031101c403500c032141e010103404506045070303050100d41030242440120002c40d41002c0303912143d0600401d0b18148110a20442000ca036101c000140d5540c008038604060104040600415421410400351117511a25181800f150039040100c2d40da2009c2018240441c03084000040d001d01c0c0303040c40850524000d0009036084968001444104008109040380800c03440030703050b80740c200003001e032054001c2080003035107040000200114031505400103402243d00b81c0c2003800050b1078070b0006003a60b405009401c5009010002003004404119840b9400b03030007441618864410b141c0004d04005000150340f02d40c80760100800f200e260707035200d0190004030407501d09140694154500f407440c00c00922100400301500d01903002d002c4030208071803020455010400c0280f0b001255891 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 331181357 1250 331180107 331180133
    0x1110a110613030203070f2406080c0301060501120c020a021f0305070503061c02060702220608011a0103090c0f080a0b060f010806130207080a030506011b080306012307 74
    0x20103440748201040007440d01c618078140c09074069014525200343d98896041d2a60014021940c018003107056080802194904400c441007003040440c3d40b45c40c00800ca407801d031014042c14070991405c007013080345c1e03030300040500c1c8400c0716100b011540c4564200142e007004840100a034016001840d00208406008400b034440c3d9103e440c1080340752030704a8210b9042c0012107074290817828000341c901032100c201d8021901079200030002458880141d000c074100300e10102582c200004070b02d1001c0340c554554006c450282c401e001c001c119502000d1a42c501d2190300d10a0700341030596849141003400065007504019100d0032005400140c3d0b01c27550b85550302e84210b82902d0030042000852124688984507104440d016035480b443c52300e82e08204048a0001807914206940c01c00040d00054001800750070f55800a440028080c130f407200000d805500c0b81038001162442101d501400203c1640031f481e0000020710305440e05156044005c3d00b010b4a180c0d600000b1800400d03001c1c200486d07555072071 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 331182607 1250 331181357 331181387
    0x30903050609060411120703020d111c05030403060e030d0e0606010e04021303061d0a06140702060f16020705030601080303100e01140f0a0905090705090c040602030f0a0201110a 78
    0x498035581c400c06583c8030b43d0309990080c03002080811120316072410050344814140b0501c161f447c11a92a40011440c2840d59401c40b2402c51030840d031449490300265405075042065032a8520706500d07a02c0d15201c0c440c0e80401061156282103130030b4840c0d000c1090388c1071889401d030200b02e2801035641659032050704461b070354001244030340c0d000b4203030816000303640164910807080c0308601c2c1181c0c5d41601828007240300c021584586484816950010404100c009004030070014585054240b42d04a22800a00070070a551012040c0580022042031203544465006240c03400780d03c9031801281840b0300da0740182d40c144110000440c0c0360001000850080d1600b010281102c2e40e14140b41c000d101d001d200d90f200d031000034242445141000b4400c202c0d1503170018500c02d181e603158820741045900079105c10255174030940041c080c90910101d0030b07070480791072a01a418140f0784403009650b0f10074030400c00005d19012a003880b105000350000c0c00403401902403d0388036200c1c01c07030060040003007203a90 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 331183857 1250 331182607 331182613
    0x4080c131b0305100605041d060d02090103080403020a0902030c0a1103090a060306050909010903050304150902040603150507110d0c170a05030717270f1b0f0a0617150a0303090305 79
    0x8045014070100c80803542364491741da8202c003100b080b440312030781d0080400d0381200940d044d42d0010f948111240f4082c506c50041c0a4940742140140080f803010307500300303680300e5104105002c40b031400b540503510060400c0c500f84c400110300503500c900b103005141905412000c1032101281c02a055040f400030741c5c00076160454070750340f010301e21401d0780c1c004400507000c641c08001003001715100740c59031070740b4003040c5502052124075640454100d07020b5500654100031140c82402c5d4017076440c01100d4104030145440103070300c80b040c0036080d16003c400c25501c0c18024a4220a0104040103410340141201c84500c951900c2200c10042d29583c41110903000148510401c0480c00b800942d2883c000c0c48a10100218202d400d049286035802d00a40d02e015407050a8005100000400280d49242e2065017a402c08401800602a10003c601d0010b84038060601c003d00c5101c0c0d000b0084686810301140c1500c0d1034403624400c20001d040407442c075421041300d000100c28103030000d81600c11a4410411 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 331185107 1250 331183857 331183859
    0xe0c03070905150a18031a130807030305040516180b0d0203060a0c1e020309060f0d060303020304050a0504020c06040f03171003030f0806031e030408060a0e1204080c131b030510 78
    0x200070700b03052170f40030013014a0b044000360780c0503402e50740b441070784042c02189040d90942c880e03c851000340c110746421000a074890b0100810480140301c0d100101c1d034000450610913040c0303034603c1000d0396400c4814044980d1080003480c156141c2a018000b281c0140070b5641a003013200500d405054004076140100f248200c0b0003418410b46002421001e005501450900000c6001c0001541c03240c080d4008840d0140702d806e0341d400c105d20550008520a070011655249001c041c80304941440c2c0c8550f00c113600c107200d240700702030001c200c560b072007071388240303041c003001503600d800d5811006090304001650494410014503595808010050764000c0d1510283c1901411040b16400ca08030b8080785c2540111207100d82981c3c440400c04c4110342c18900b9a0304064503a003800d458210101c1e5424542038894003001c1d400075040c01a0403644910b030700c80c40e00d040c4c01c00000350303590740b4041c01a80c0500915800c1f40d2904550394801b0702454807484a1400180c581800100a00419030b881404240d02d414 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 331186357 1250 331185107 331185137
    0xa20031245100c151b05070c050603101508070201150501231b01050406150b0403080310090507020c090f150d0c08060c0d0c03060e0c03070905150a 65
    0x40000005803103082000030400006091001e044102e424860500c4101e0002900007407902915840c000f004500000e0711030325114055150070301c0c0d50901c4040c0041040f03604081b032401c001170800c0d10026036400c0d64a480f58000844000483e5005900640d5401c2a845030f0f1a40b210302c0c5c500404013030740203003c0800700709126805402144a2980070030a1050204480041d100840c0110b50310f142500d410107140175000710b4802d1811403120f03134bc3c0e55510104410440c040c440c0c0e84490010300520310009040c104519050312032030001605c0d00c0b40100014051403040441a40a00404030080c866818070840103980e882c0340e01421841000090005141158007400e11031060741202050b505200b0300c10140901800904400d90381030b0918800441c2c00102001601e0246108003041a03451a400c00c6034070860f100501c00604042c208681003001400902010750044003240400e42d0360b40350800c0655007400154400c6803c40802d001c0d00602000300e40c0600303210221501e0700c0342100342c468 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 331187607 1250 331186357 331186447
    0x30d020706090902090604030b09010b031b090906010f29070309180b10050c0313030b0402030f03090a0308090105190e040b010c02030d050a090b28020a200312 70
    0xb80700d151b0070600c103010400110710703a10052900081950000548601454042410082d0054054248811088552010b401c1220603690b1107841c10b4050481d55041403442e5940114a00c13803681d52052508111071314042d11a5803c0c8140070250840d030f9100c1035440d009d40400362a00c07803c03c5200c80e070b4402d0301140d01d0314040c54582e26030007030140c0030781c001001c0169041d411560301d0001c580310501640f1501c010720340c4400042c600801007015540307041c1c410180340940e0303c0e03002d84035a0030a1007401c10300d80f125000c0e4000e9070303803000e01c2c142c5032010000100c40d1809030b02c100c59000718024900d0a51340382c12039141003031000140c40500002803071000642c1c4c880008203000350158450384003042410b20540260500003000c0c07071700003040c41d0346825050940e04118900b258103c1404410001ca40250021a00031510b80c0003424140340245c4a107140225004044622024030003445413056400740145001c0c0c0429041080d118444840b82d000c0305004400b601c01d103001340e544445181c011032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 331188857 1250 331187607 331187617
    0xc090515030a06020315061309110c0607051e030a05040203240406090c0302090703020904060f21060b1903060501050a05060313052a01030b010810031b05030d020706090902 76
    0xd0018102040c4640d03c001c000d5100402c4440030407485140716846a40e028010b105158812030303c04051401c058101007292003c042c484030758001000000d0700b03400c0c0400d1059118150b810320903101d0400c03800d145070391035081c4504e0902d01400070801c150000c0560059002d60700075000c40d42144109110700c40540310b9a421101104103440010340090700c3d603040100300340c1c0f060324540c1e030042d6264081740007110159400c00c0441c1d001b241e8212141000d04c10304009286222018607080d14010307800082082c000c6071015505803164000d014000303107401ca155400400360818a03043c0d85500450040b544c00d0004461081c02d007070000810b49030042d4984181c950007071240f465a1550034103800321100b500700c2250701e801203861110070131001c411006543c0304428002c185515440c000101180c0c010204039043c4400c0006001c170814000d074000098030b23807258401d1041d05600c110900d0080955021030303030603c41c40d50600c4021342d000c5550b40884c0c4072515240b420720349408604003030f8059 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 331190107 1250 331188857 331188859
    0x5040302120309070b0c010b031507230f0307090503160314010c020303060118030f03030b1c03050f071704030516090b0d0210030f0603200d0b0103030c0203070906030c090515 77
    0x3016105025175162907004000d403e040c1c900000350503541d08042818821b0103440d01322020500c4080115694100100d0103184000d05010020690342086102050090031707807150007480040000380d5407501422507603016004c010215400a0042403d41090b00c1c4030f400100c800c0c41800c034940c031180105000340c00707411000c2c3c0c010f5804e55071201c0c01101c031212070300301600d00814500c3c0000040f5421544c03e080090107954003041081512052042c409507600701c00c24210300140090020039841400c0c1d404603400500e10656642d428100309403500c0c0591826402c1c0c850001d00001040800240c1c0101288401012174446641c1e41c0500308444100300b000340c120520407003c0006140081c4041d0000f440d0781000142556040400701c1164a01d0300100e1b04015501150302c03004400c51407100e8010f01c00c40f50013581d0001995540005030043c0300080038444102c15000465805000324400380c01c5451040007299540c0c189440245081d1145030905858031001c56070582c1d044d0b50307140d010300e4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 331191357 1250 331190107 331190113
    0x908190305060a1712121503160e09030912250305030a080a0f0515040b223201030210050304030f08060103110f040302030106091b03050a18050105040302120309 71
    0x403402e058a2003918604400301c109008110013100200043c1e0060100165408031034100c03854001131030790070076462400301752281e440707d500603600d030724402c220900b641d442b060108016114404e080d8039602592005541c40f040e1b044202c213044c5000240901000317800c44801c003281c5280e90841c00d0043c0d4174003000d0f0190700100a81a1024001d0241da60050b03844500003c0310010a28544100e8806035422134101c862007800c0600ba103024020750442c0d980071108185c800a00b02006211581c5042c2c90300003198031000d0b03032222410b106410200410000c00b402c8096007200409a4100d032090204901c515001201031071150300c54402e03a44182e07419210480b540016200076070394141c00802c450304142c1c80b40b90a50002c444040900310742a000c0302c05640312811841050b080d20801c0c0c025540c0e00e0b10709150422884a8075014000907080b90400185645481c00c420700581806200c40c400d011200c7c0f50b40e42003110551102d0300c507074025070035501c8800108540c20203d12064030030b03a032694 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 331192607 1250 331191357 331191359
    0x307030f05030d0603030509090c0a0c02040b12010c110106081c180302130207061a012a0605040f060e010507080601031a030106030323091c0212010908190305060a 72
    0x501440c4461181030181d400c60341003500c520140780035510320780c00480000c2c9011960761020700b090500260070141a540c100d0034511103880c0100101001c6001920560711005060507907144d080700c40c03500252010083c01903000c0810054206e440500388038075150300e0401d00050070140401c0342845058200e0002d000401140c2044911034610244c213540c9140740b19001006a4550000e0700342900794400c050f855280e01e080400840c2c919490010150381c80314030158150b03034040c2c0c03e58850007a02c10307521240000b01c0701c921810340c41c040005002c90702e0942400180400d10900f40b44403403103280203100c00c4c50152030081c02d98100b034400304049280360b404074856600136008031040101c003103e000207601e00035001a095850950041c0d0104000d0103034121b511400600b42070318101c284210621744140030010452a01460054180010000d888502159226240001090401c4001313016009107410310800360391192800751038924240d0321580541d4001d010340b41c4100f50003014180c0079 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 331193857 1250 331192607 331192613
    0x3070207060c1a01170106081f050415050403021b0d170c0f030f030a06080a0b010e0711010c09300209060609090109050f0c1c15080f011406090105030703 68
    0x100c02040800c0711019020501d007420802070340003d0b4000d1641c00180c25914044014450031a5840c0d0070075803458022039a80c5a01d11030034050320f04461040b07500010550380302d080c2050011300700030745600302d5400d000c10700091641c00254850048100104807145041038820041c4019590100030054683e6112841c0551915006411a24010b40076140011014070344542540d200350340402468a0110a02030200510301c034103000f03440594020005071a864075040d2030303950144940d403909044035000440e071500c24038891402509450003440400c03820000985102094001c80000322810891250009000da10b4011514120001c102480010303809106098500501e480d80110080080c0c0c403054440750349050080030b1034600064107041041001030308410240030091038000c24002900c00700d0030320450181100074420700007101d02c0c040a11a15809403548800c00b2030246080c030154a1030190089000391000d034000004075074940c0204540840f00f0b000705500b5500250f414400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 331195107 1250 331193857 331193867
    0xc020901150c14070b0d0204091802060304060b0f0a0e240607020418080c0f010f020f090d02030a021009180612080a05090307031208090a050627060f07020708030307020706 76
    0x400b280c0c01c415141c0441d2a4920385d4045d13807080781c0002ca150340c001020883e0b600107205103c14107040d070310003125102840d00055401e000160002d0b058a03980c0105030003641da8420086c01008001e00140c000716a80d0034141d41e00c440c04c0310080300740c00d500b031020400f0101120040c4441c3c40020600340c104403d80d000c0c00b009040040724207402009a84001020443c1d810103032103c03661072002441d20301841e00c0342c182074030708000030720a6040c0103010700141c10680030280c0d0103010042e1001c9684803030340d00010349007200342c0c10042e4000425036103400720954003181110554400c0944a500e03010400488000c5682034850340c0351401ca4014000c00041c1440003c00f207804152901c03070300b803001d4007002034105001c9910854180b001080b0702403032141c02800140d0320400713040181020041d5502c0e12511440300030f001e1408010341510481417094030790306107070251015070111145031034240300d60141c100040e03800c840580314802000a4a120010803648241c1503540070b84070b10751500000f519 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 331196357 1250 331195107 331195133
    0x70c1203021c0608010617010507050702042708130605043c0e0a050a05160f110601140307080a0c090908090909010c0909091a0702030c07060c020901150c 68
    0x1041000b42224405101d00801c0050000726000290061420f844c000b842c0100e11b0380c0080c00d90501d010070000542100548441f82d4064801051340e1a45052006c1c50b0032903459210910000345040341d080c0704d00d1300040d01802001a10303404c8603d458060070740c1e4a001e64450801c001e078a081101c07009a40008410103c2c00465070070091099900c1c0c240901d0b42101e4001c83e07801d038208030403c84101410b009540c1c1003c1008020032050070642807400c04446248107000500000092131090f95124400034040a01d404054070030359616119054444004a201c040c400d01c2001e0780855244d00c0420f0681007075500140b03c03501503240005500140003802c1094543c11010300008903103890f00c06006d032281d80810b000041d450700d03448005e440c0c040d054000070100c41c82d100540002585e1244000f0030b03500f049220b00342c41d035103802040b0701d18468a495100903014418001804c207811600501000b0f00c226803070301046c1e80b2000041c000e0700f200c42800b40000d010070100e00c082540428404 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 331197607 1250 331196357 331196377
    0x9131a06030406020a020727090302070b070503040e0105010f0c1e0221120405010f052206051b060708040320010e07081c020c2211030f070c120302 65
    0x801004400080c0d0319800859041d5115078001520b28521641805184080d0003a000707402818200703481882d01d8008059070b4134400f03541c0c81b50f0101c149402000b0100041c500300c4005941d900851514035140d8101c0e21803000140200e100104103076010b40d640010b0810075564800d0ba001c0d107031f1213003003e004a02c42c107441c403c583e841d000000360303e0320048104a118040c00700380c20840f82401403841c0840d01c8440014410060100b03200c1d07607a00c9200b11240d2080780c9003103502c81ba04d4204001201602050801112007110800180590800094817800e1044903003811040c00d020a09504d0300c004590240014040000281c0002e0141192040d10a1010394450441e60111041c60844400c11041000c1e58019101048100700030454000201c0b050103003800320070080c40300a03540d82c80000f00580310f810740390703501c0c1800c901c071040e10660181100014024002451a944100d50060754041048103940780010901401011407a4160303922884c640f40000a000c0128000c0d00041185 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 331198857 1250 331197607 331197641
    0x6030f10031b0611070b030a0c050d06080a121706121606110c01021209040b0d08030a05041118040206030702030412051501080718090201030b0904060603050c03030913 74
    0x10011030a50340420401c0c107141c80c0321082c8035060442c00b0344511802c441105aa50044a00344403a12002040e0b94000d540702c03c011805c08114081680e1601070740d5540010180360080000d00310b0310024031000c00d42e0144981040c072011030311044958070004400002c2c86450038011403514240a8020f51610f03403000d0a40380040802c1518001210f002e92000002548049102000010910451699003000d0000b407041000c04000e204440c000c0c20b00242c440c699590056840383c49840000030b245d0790150303803107580749042c0c103080c802003d0540307080e0b80528a00054038035034180000703010159925491001400d035a15420003040f540010450001c40c00284000150181200121141584144060b03c60b6003525907500c01e1400050307001466030340c032080d0204410544c20545008e500c1d118080401c0590300c6000581c0901700104c43e0540081c0d0705420001030007000d0780403800b5a442807040e070305110f0025040660320b0045541c0365610030018080c1d00145002c17a40540000d948980032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 331200107 1250 331198857 331198859
    0xe0406030609050f010c020a050c15070b070302031f030323090d0501060812070222090b3d12050f060708070810030b0f0a0605090705090103060b0906030f10 69
    0x4640a0b1920301d88101c1d4181d221103460550580d007030190841c0c080e01440140701400d66500d0320b075034420703031100322500408519040b40c1071341e08000115a44c2ca5000400c3c0200c608207400c008000398001ca4074200c0903c0c907040741c0d10804110714126812030b5016070b102c40f503015901014544000d12114141c0030148100030410a5031501c080001c80340c2d001d0070000800c24580b0b000c0905102c440d091000104000b00001c00041c0c2d0f810035408440d854650725414002c1c00c0c000e101000340995600503059020303130000c11449011f032109005880c801145074141d00034003a42c2c0d0581034034135000758040000740c8440c00c0c001e102e400c1410340c080d00d0140003141c010b49000384503a42031100644202000845920411503c103802054594201260100300000d45145496610041c7c10140c0301e20748110920005c0340003101160081005004020b1000f07003242001407000c1d003103502890303115012a0500400003a00ea81c400b040d0f810f24100900182d1855032044405004000001c194124140d84000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 331201357 1250 331200107 331200113
    0x21819080f21040518250c150905030301120f0f0b18060106091202010212070b1b0a080412120606080603010e011104030210050d11030f060324072a030807110c010e040603 75
    0x91003041645041c2c42d03100903210b140c1018880402801e02e800c04a03270408110000041e40081140d046910300271508540c45203a240c40d801100381008041c00c20f501748001c940500c5512030b5100d005402d1280206e613a03a4108103107070b44a020900c02c1e500840d080d4a404c0080710b08802120b11118070510554005007800c410f0700c800e0790001d0030b0a84205031038804000c0a49502410002c12179990218035003040072410008254003402000140341141403808400040d0060342d03030700ca8010f400f0200b4407410341c0b529801407030000c00300c8002d4843d40c2440c0c1c15007243c00e818403840d889030090300e840030700d0315040d40c0a00400c40d00c44500c02040202c20016020503102e580318071741280e00c0c14502140e0300d09004205062020025100c1403098005100e034507090704900d44601030f9240394980d000070540e2110019078003200c00200d510019002d25090041c203181c1c0840c4550900d120b500d0f04100303602c0c0c80d1030403164045801c014003916132005035580410742c042c40000008080040c000300d00344ac0c032a9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 331202607 1250 331201357 331201411
    0x141309111012060e01060f050f092103161b050d080307180e15060309030307030908040f0603090b01060f02210f1801090504021819080f21040518 64
    0xe070060200b113030010014031071650b10001161404150f03182c074600740003516007031021034411210241c0c42107540304045910013011b0485040105140e000784c82c1c176944110507000049150110884003007001103803030309100c0c2d2840c0f2100c086e00c80103404089100615500c2c030072140d1001d0200014801a0034640040807800c01d4108003400b82e4103030802060030690301c401130100b880030210f84180b20a00401103201d00000036a64090994139020468900c03908210714148540c1d044044a9800f4007804a041901038200c4506d0a00c00c8074030f540c041c2ea03150303800ca078000451903012005810520382000d0f641000c80e98129100c02680029103401400440041c031030388005211482c14406121040e901d40c0c010b811003000b4401035505520b09451002d8000b48401074a0350383d8881c4d0000814145c07960384150800014016500403079404070024401b995640c80d1514a120714402001c040350540e1850300281d4040ba04060081c0007011a210070103000482e0042c092456405000c1507850b00ca440d030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 331203857 1250 331202607 331202609
    0xa020319030206070c1101051606020c16080a03020c06030c1909151403060d110d0321140f130c06050a0f111b010909020414130911101206 61
    0x1102110091100d40e00d0042c1c1001401003812050080640040020814181600c2107040b003d01c0c2c055034aa0491441c503140b06400d8401030a82440850904491000000d140345c40c071958140b03461000795035102ca559030711011000100140c016222503005402c05002460304007001d50301d024140801360540300480030780103e248000962400003049164003482c1f40d0100036801d40741c50711245610104900c1903100c050213035801403224200c1070f000d0005980407100807603001400302c95061880d081c001c0c00c012003031403680d0306401306038242d1407904494440c01d0f200103441c2c80300e40e4031070342c84d400b122814101c024100402c10200310103100010754048103400240465032141034031880c04980c001c01e1040880300010602030180c18621041200050b6581c000c3c2c40c880015009101c10f1004071140c14160303020b1155240042008a12001c42203104001aa000d035480807615a840030b01c80c05403a01c0700c2010b820394001258802c1d850521003002d0050f0185420300505030702100309428112441 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 331205107 1250 331203857 331203883
    0x3042102030d11130608100b0d090c1212031808121503010b061b03040b07060f0b0603131709100504091104030b0c1c060305010902030c011409040e0a0203 68
    0x700161031044501a0b20810700c0c8000303030048003814000913030007503804000c0d41e01400045c4000400061414282e452000028160103d00a5250201850f9180141c209140111082e0030903000c0844d060100405180519030000d4400c21082c0b03d0100580040001226503416200008444000304a61400403e003ea06c03650380034440c0d18154805544080c08141e00300d100c2d03414000740490275590706050f0790400400448012003103880e004858514030440c0d004411408010814005205c01d540c440301b45c1c8020341c0c009006d05a514020000e042c40126002d00050396a0410320002c180741c07511443d05024050b05040c82c2144540010319040c0c2c400195600081001500b0300002a1a014400026070440481820b060459642c071100840082280d4000d40f804030f0240c8804071030701e80724800e1200c14102004100e4490a15034060500c41406078040c0c0324a00e00e113421944900400c40914094002c190300f02031071441004040d1903401b030380300c081c0d00c6100071070f20160f07400b8401d404150503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 331206357 1250 331205107 331205113
    0x1060507230c0f04020a022a0a1212020303010e070c0318180b0f01020a03050c010605130f0b01081b07050123070f0302090607060e030d0c020d09080109051203042102 73
    0x607080041143c01c200b181100707406036005005200d003098000810800d40e054605400850714054020020010381901040ba48013a404070b0004d0503104990407110b105004004c6020301c840e9641d030aa990388020300c94003840000450025202500c660b01401d420b40c864034210280581c01d40c00403c0c002c0403900448180200f070f00380c2d00050341041c450311040714400e950010342c0c0142c03400082d4446812100c080e091003800134464086800a600401c007501e801082a043c0c00d00d040440401403104032000d682c50380ca002c0004040b90700a111851241012013a0703040c2202d82c802c5900c0b8580c1082c0e9044038030f0346d281c100c02040c0c454603000f140400d07803007182d10407101e1030094401001c1c070009001c01c400745441003103008410b4907a00b04448c802d5800080124803242116186c91451107144101e10003640381c038030300d00c080d585d01142e42e48850303800c1d0351a1112103440d4420340e0b080300c5010341e0043c100d43c00072140540074260200610f520600644110818a440409101c3c40240d58139031000160 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 331207607 1250 331206357 331206373
    0x60f06020d0201060f090b121b040c020c0a17010f0f0b010806060a0503060603070908101a1818010b03030f04090501060c050d0c060b060c01150801020a080106050723 73
    0x16504101d8694291514802849003070b1030003180e0310318494580107040f0b0a5494a00981080e00c44520360201080d6400840340001e000f0084248011044d1880510030750a001c00740340402e10001d5004c1c1440d80082143d207009161200454001c0241d40b1144495521480320310300061603480381e481a00f26490300421402960000101140c000401c0d8074492001070003d000030603448020740341e018000340c500b9a07880c2c43c0c50f441034841aa4980c4800110322450b80e040c1201e803050741203858115410200c80c41214804420004c41c9544d0f40c0c0b2f030302c1200502e0ba00240d40e00852460000c000c42d5008000039007050003101090543d0f00514001400b40400a02000301100c076101d0180140603600e48030800d01c540c3d554064565161007214030410a40141400a00c005640300300c0780ca8100500481d6181061341c07000d0b0103010981c5d422403c003222040d0004048406008441a00307100b0f944901040e82050750075540b9400c2a407042d40c1290f55400c10140d00040025440600386010000700f4100d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 331208857 1250 331207607 331207619
    0x5101d1501030b010e10060c020d120e0a0902030c070f060b0306090d120207030c15110327030903030703081519050405330402120a021c0203040b220501060f 69
    0x44641030f40b0031101c0030920006c01229208129810060b0f842e90701e05503603005035600000b8410480070030080c11940c2410201031100da04034204208882050b1010030295030340e182000d0490004030340c0720700508420420640015440407c5100390b034410140003171070a15050100303203406012202c0a900da40708071003507503480d030704142d8080044056850540c82c0c1040e61b60001c2507500c0c0c0e03050007031400c411002248031039202900300d2200c2c4480c80054079100e2800000440801c1c542080b00d100d2000c0e20070f03044c40c89a0010080f2a06c00300080c1c004c41c5880c50f20b039000c13581075500802505011858294801d400d90f9990410006040e549180c50445030610040008442000c2c0c40f40b103100320106100b03103829006103210308102c05600f0707962581ca80500d0108001e403040f40c0c940b1108903821401c000740f8000681c0642038010030848040300100c1060040000c910082d507000e070489480b107001480f40d801c0a4484a0340c04144242049041040e42c0c5080c2591543e80001c551000444018408 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 331210107 1250 331208857 331208873
    0x100509010c081008070302090a0e01050403050a172215110301060e010806090f070207031b060305010506041413020c061303080c070b1306020408030f1c0905101d150103 74
    0x242c801e02500c0d00c0c0f45402413550380c4004610000f4080c035460f40000c1d41c6000c0c0b0398003201c1e1900401c0300a0001c0e15046c070380101a5441030005c000440c008400300800c000c000201d1510405c8100c001e60b8240407051100340c01c0c4e0041c1c0c20200d411201c940c40d12280f880003802400e1b02e00d404011015125418480040e20000030200c2c02810400c1100800403141e49400078560005c061000760211911607803000c0f0704000d15508090310a1020140410034008080004d00840c0c585a40c104540d9803a041003108600c030300d100302030b040705105e070760b9402600e00304049004590b5280401441c00342c0040d43c4900b8500101c82443e60351075920900414550031402c01648070b145001d8103860000660360703007051080007501c48050a03125008040c10812941c0c11540030f031910f0700890741c68220308185281a58022082d018a07104407074107038140d14079a4042e5802c1c00f90700801400c4d0240300c4400c032a00800c1052141c0208203081c480d019815103041c07003c0c5608903580c7d10b140d00590b0441c182241 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 331211357 1250 331210107 331210111
    0x906050a12020f0108091e071404061a03090a14010b04050a18060504020f09090d1b021005130b030717060306040308040b0711011508010f06060509060903100509010c08 74
    0x64241d0307041031480060b96a61001c2c00000801d0905e480c0c1c58a84402c0c00b840c02c2d109040660802c03c1c0e00c1a0802d0b018030006a81c0219502140c4440c803001c141410700040c1d86243c8282e450b1500d607002807003c0991014003540d4000a0203040300c1280c1c1154654038021104683c0c4c0202695680751f00148509103030260700d5000a46c4013003407000483d080061220b0184281d000f408665903100401c08541e02c03082001003a00c001810a8410b0805402040c0c440c059140024003081010760303850340c494265601034038000e8000f00b080d00300da4a11101075a10707a2040c03070150324408018101244104116000d1340c017407446551400756031021030302143e401e444080c24480c403e0707101c0010080041e520030b02d61070b4080d42c020500c0140c1d8446190079205200642c86916065082c078a00b00100c12010b02c1103405c480c136030303802400000f2000200b1402c50710103000e0407001500400110030b590400c400103002c0450090308a4040c1040e0300b01e403d04840c41901d00d42d84a945501900d104258403882050b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 331212607 1250 331211357 331211369
    0x90a0f1d0402130911040c0905091b0a0318060c270b03070f05070507080615060a080a021606060e0a1113060311190c12050a09030f02030c06040906050a 67
    0x94150410b40c0018800c401910b409028803900c81c0c0f4598200200e00c042d04400800142090010f0014040c02508146031402101e00818140000840b031544281150007040705040b2503910f02a00107a084014000c2c0b616161a84660303148230307000140803845000d00900050b03541c01c032047c580c5107520850320503004240e40000303880d000c2400610b03026800ca03034205c41c950801664841c10f440c004e40d142e008801014140703000e13407000081ca031031001c69554401c00d08401c040c5c0040900c0000c1105030301958402a00082c191000038680c8419680200101003610400c6030381c0c810b040d80c840040d12990b0708020b211050380801d002008146001e9002c5c0300040e1310100d418000d0044046000d07514074882c00c01003540751011451400e030b69100700c0380801c3d800302092410541c0d8030006001c03217002034001c480b04d0f04a50703d48050a807140007a0b4007045004d0740c600b0780841c0707951609644e142c605070090364540a8523007020007540d80c04000340018400a000840c02901d04000c1110b82e0030f01d68040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 331213857 1250 331212607 331212659
    0x406151d0f01090b1312050102040501032a0f0e040207060209130204061d06070804030818060a020c0d0501060b0a080703150608040201030e0a02130f05010911031308090a0f 76
    0x16000740c0e040ba00041c107a0b18520000ca40f124805500000c2d6080c2d0b03680450806c8005070040414000c0c10b40042c070a0320001c1e2824480c0c4901315034500f041c00502caa40c04840009501c0450545109a1036260140131500d8810400c250034000074003240c2c0007900840314680c0c001396040d0035040440d00c12032005400a400c6041030304d441c1c2d0260444403c0d0541c56002e890160303d40700d507651a1403e50361035942258002d6150f907101c0c034180d401a406803001c0700c0c1101c041c1002682c6840c0c00412180311066940c0a050030640480c10710500750031f02c02c2c040340c1d995200c51010075104141e00c0500556601c13544c0d03801a500f084d00c8060200c1c0c0da203012035140386202100901c10290410296a04681c4c2864001205003804900c1401c0c04144403000f0b507c8291002001240c42c4240c01c0110410203000c010082e599940061004861000c1d803015100001400000c66608050719001c0c24203015000513444c01c4076070400602102d02e80c0d0081a207181000d00d052049081c00913410aa01c140d84000d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 331215107 1250 331213857 331213879
    0xc17090309010813240908040e040614010f12150c0801030201091205060606031504050a021c02070f1b0906030503030103120201020c100e0708010501030b011e0312030b0406151d 78
    0xa000c001c01d0b110401c1c1c90f44ea070420352482c04000c21544007911007600039400b251123076192100000310300030940c2d0946601381020380012215488059a43c1200c107200905580a4a01400c1d4007800c11a20fa0030345a84850b402c0744001d0920a002c1c50740803032401d80d51000c50358154170024020703401a8100740485840031200b000040d4000034099081141183c5441e00c1c2c3e6201c008121504408949103a0028180002c0c082c084c800d94000c0d041040a0700110f20300b0b0050494110200d0003a040080d28452050b45603c001c94003036201030401c0c00c0c550300d1a00d490b5071208240e6003a0b401c00ea2044070107501c008010024001d044942501010482c4025031800410b81c0785e10b55124010000442400e550300b0030030304080c034104008802060704030000e000b2581d490400c1ca108460034424282d000d0b8400b00c80000a46501443c201540c1e031100e110480ca2031038510841c000c0c41c0c542c1610f80c200769aa4004a00c549000f104c2c40e002680300d40c0c80001001d035240007111800300130114540140b41c1008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 331216357 1250 331215107 331215113
    0x3210203030a09150c020d02070b121506160b0412091d0903190302072001050a080402060403020a03050d09090e0a02061e070c0e010e0411040c17090309010813 70
    0x840750002e050038030119086100307007851540c18507207a03105110720340b405400901c99900404c0301040c0c04169000c0c1d03243d0070303a6203d0462007817181d04100040d200307008002801a41e0a8032030168048000740403e800c01e55507107a0001c101c0b03044a0242d50b1043d0341c81c10041008000c0008180720503444c41d124200c645009400c0c584002025010040f4440c52400503403040420410780703280411011841420b07404506014000798011601900d1500e91702c90580c0740500d41e40c0c1c0088002d83c060b5902072910224031001c03560183c02400403603005804001c00000341c0da5858042c005980070b01e0142003040705541001e01005542c0e03110074442410700c80c2c0b0072100c20740800d0009486405071110b0340d4464640c0c6580080f41e14a02d0182a103440c0440c07540c0c24491090802e03000d55200d08640502c42c3d0b200c540c4014074480488005140200b04202c45115080c141c004c0c41c501c0703804e81859840c03000360260605100c0000ca622041990010a4400456901c03d5031603400c030020100010404619407 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 331217607 1250 331216357 331216363
    0x412170703020d0f020d0e0c090c090d030c17031806040803131b030506090d0305061302090f090703020310171002070c0b0f07110f10030c0225032102 66
    0xc190106040e03002c20b0800c80481c3c0368100c150340d42c11000013195a82c40c6004d81d43d0040524500d0840035100e11450250541054204903005090504c03400703040040d91020082030500e4034400f28208401005c0b0328002807400070094070b482c400b0a1343c09869103004d140003404407440c01c40d007840a512107010f000115050004484d00b01d1001c1842408401190501c1352a451807080d110703582c1c0426130383c000305206000c1000e50090007800c09a0702e45801118048090350025520141d0001c0442c410295000281e070041002c807501803c0c0f43c1c1140d0f491800240360b018110f03507107404240c00004000e09608204890006000d511454a1014030343e914100c0da103158010380d50041a6002070716405010341c4d0126800140000362200d40d845041c00d00c1c000490b045180b040b111038000380c2d5480c4882c81d1034200c80001c2140940030003401c0c20343c51412005001c5180c2c1203801c1d0300a004042c0040601c088140001c0c424603a14940c16a10f10300e041002d60104150011a0002c1d104c510402c25a001c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 331218857 1250 331217607 331217611
    0x3060612073027110118090204090e07080c0f0103110c0a03020c10080103080f0705100e07060903081215030703050a1103060f0f060f040905010e0c1203040306020c0106090e06041217 80
    0x1007040c0340c05092100340140c40002d03045030303000c000301b07103852002440400710340041054491100e018000749038556481c3e0740e14403040c050a420741e040b001c0041da036030a20380c0140c1040181450040703100d420001c50301a9075480b84142c0c16498000407881c0c8241740d01001042000201518100031402d0445401414400180001000342600040a10060b10100d00359107005800c04140e0f031035100071030141d10040c1030202000e401d9028080740050760301e0061031208222031b080602c03e4076100240d0300100103c0c030300a2003801c03455a040407074520354804116100280d4803480003811445002d04040d4509001c440445100c2c3e84034104002c1185c801c1c42c1070b030b0b07045054810b00c28007545416001901c5074008000b43c54003e440c00030301d04140041500800c0201810701d099845030b003000f00500c0064030041d054012658400c10040000407010341c01803031110700310800052625200e401080c00e55100b08515010b42d4405e0060200b80014250f44002c0c41002d070401341c3c8021203540305640742a04c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 331220107 1250 331218857 331218863
    0x603111f02030d09060b12070f0b070b0612210a02010608010c09170106050607060605190803310807030302060705250303140f011a03060612073027 65
    0x150383d200001c0085c150003036400e41c4c800416a042c04900c828040c0d45e60361451040f0468074820041c0001c42030500001c8130b030255044541c0108a907039140510641d00c804c02030b490089d2084660042200c124811041c01c040b0700035100c650381e90083d000007801e43c2d14070742001c004c591510b103402110540018844048a414007213500f40e130708001c20024010411580000c0e0481400034904080020710380c1b221003650001c0714204020b80301d100700d00c880c5400502501005500c1040000c0503000d6581b10010240c00a191072204906085000300048100d0f6104c5081548016814001c1540500020358441c259183c01404c1c61641249146603104446103042d0402201d100141454426004000c484104d40f4a0b05280d0410065014044000744566480089181080303002454801c01b204c0c01010010030150801c03d0034a0031040c2c41030003038030307540c00e00100a0f0358008008500320301032134040d03034900b01508207041904a032059489480e40d500a10380c07503c10708035071142d050000601041d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 331221357 1250 331220107 331220111
    0x5100302091f050f030906010f12020109050f0604030606090b030613030212071a100e0109110315010e031e010506060412170409090605090c010c0b0f0a0f0603111f02030d 75
    0xb4282100780c1d00b500c24844040b07200280041044007045000071140c0c102c40e1504481c1031144d0f560705200072080a5040b0017030005006a000b00540d02e000e4111300720240707004002c2071505540b6039410013103420991000000684403103040340d140c0340500c0683e500800132000300c11140d00756a4001d4032a000e45845941d058400309200c01846008100b00103002801288207946040006161041c54458422400b81d41c01650001c90040d90500a003130b003040c08940c142c0d045884070f9102d5007003410a956418108003244100004a039420404002e07000285000e140c0b01102c690040c6081d110014601406180108010442c3d0203582c2100b181c556001451888007140ea9110b12003140700d40c1c0c6c00300102d94140f20381c3e0310500c0b001d5031140d07020325044002c40741012103050054034010b1f030411000d0483c44141002448044501c01c03e9035129207a00400a003402e00e0713820381803c45407140c1040d00d00d4850345014010504111100d03000b403d120704440f4103140d41c4440c0c02580c070321407031600c401056 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 331222607 1250 331221357 331221409
    0x1205011a03042d080706050a0c02070b070516060504080c010527030c1909050a06030305070f0303061a030108252d030b1b04060804060b27010510030209 67
    0x49003c0503129400e800e403814901041c410300700044982c203c0c0d070080c5e0790107203000003241400e03065100c2e20882e000a9006001802c0c580418131040307030420f14080c0d42c1030203a10046106195401e0000c07014285a40f41c1daa1240d06200c18a803503c280303040d450b414040b0400044c070502c0441d07034441c0203402070940590000168480400c0c00d0055000465801c16018982918060541a034040569401705410012540e9041e80c11040c0d07141d034400034011490402820010076526002c4d00c0d0b106000e0f081c0422590b0781c1d1000b00140100704010002038010120050010482c10b0002c1107001a01195400c0c0040748800744c9042c032444d6204000c0103020114000c0105040c05803000308080c0c111404616040c2d4900302511007034012582548101500280340c210b003c240810342e000c1d9000c95070343c2c4006590300c7d640d01c03004094501c4403640c0500302d20f903c0d400c168402c448202445458803100f860130751400050200644100714031206140c018410006140c80710102c0c9190408400310141001c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 331223857 1250 331222607 331222643
    0xc21030f0c07060c0e01020c09060d0204091a1006140304030806060c0111030c07030e090c040303030c0e130603060507030608060606030c1201140a0603020f03070e060903030a1205011a0304 83
    0x10302c41c07803034000e00b450300f0310802c4004190040001d43d007070f0314281c00b616100c1d003e141c10465014400c9810b42d0b440102c61080c00c015081c15800804c3c864410316181c6008600924121031583c3e0807109a80c20405045040c0011a4080390160190b103820254a085040681e03000e03000c010003c010034014840818551240e140c00d411001034504020600ca58904284140d03114950151209602095155000703000e075040410500d8403070506103020900f058115074044000d42055050101040342c0c03200c440744250707150900c6172280d031071103540012920301d580f07840003d0300c84c0149101c2c281842c02c00e040085040100d60281e0009003104c00b59034944d51074214801c20f02428604100171050f403000480c2000c0600c01d010341e443d0080b186101c0c4a40d03034910403001d07841810b0308051490010700c0450001d600914101445003401001c5504050407100801e00e503402ca01d1f2801c0001c0c0401100c10b450683c68825180940a11501c0641c603001d1403c40c0d900a10006d8001014441105105419 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 331225107 1250 331223857 331223881
    0x30050315030c0a060e090907230d081b1c050a0804021309080715020702060d09020109050907030605130e070302061605030304060c02010e0703030819021308030c21030f 74
    0x1840000f8404654280c444c1002807102115150b56030040b0480d80100e6802100058098105c8080707605c2c200c104007103d800c868401d440f104a15403c6a41d03d0000c400181c141c2c0054610600385180704181d02d520400198684480500100b0032042c04603000110182d00000701c580c0140242401c10294840b8804a5207022800c0001c00c40700c2d00e0800804104944171000304078440c0180c0c030540c003030000100d140d0201d12039110000e500000800025824442c82c2c1c10000281d40141003007681c03190b4401c082003588004a0720032001a41e078260071720051a0031040b210740040c6c0d182040104a10318103d4603516200e50001910402003c50100303c031100f07910408180d258041c0c203403074690038a0301d450030181c039442c90210f002d54244090201e0440c3c00050860480380c150b900d40c450342d140c0c40101e001a4040c0078030504850f400300b08071203075800c401003054000c2044100450b0b5903401c0081060500080c070501c0803010350a1007046030b10345616000d0720b4004e030104d1601e00315a210241d203149 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 331226357 1250 331225107 331225123
    0x61b03021903030b120c0f1201090204050403030605031221100801060e071d090105040b040b0307030b01080c0910140d021e190f120f0c033005031503 66
    0x40280c1d19680c07001c20107600d6041801d01c0581540d540c0c0b002240450304544400c60307810340319002030340c02c003100c4494609401000443c0440314000514076000e038001c42c0036200d003110290007198945c001040a810308101780c83d0400c1621411505201c52541c20748203442c0d40007080d03810451603c0105214080c078011940c01408003a0007003282941c2e40c41c10907522103044500b60089007042d850102d010b0003440d50f2282c00c2e28000c0c00240d032030b800d081c200b00042240c82021500075503612940e081d02e032003c00225019501408140d0203039031411114a281c00907074464079018401d0b003030921068121001c42007042c0c80c58450100308c003000300c40100e680c10740700080195104011064098425010111000034510250740000c4c81a00c19007030380c1604241c2d1b115202001603140d0080241c02294004944113500c5000c034401c070b40c0b04c40c0e03e0f10440d041140c1c0017510709200402152040e0240d408400c100d0b21211150312640e101d4801000d410750100801c1c16600a00d80c09400000b65001d02c0001c0e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 331227607 1250 331226357 331226383
    0xb0a050603010e0103170a1704050712050705090610080a1a090412090503010e07030609081e03160c121206090c0504060201150308030612010209270a0501061b0302 72
    0x68076581d4607600403265039000e201c26503104600e2501c07865029600011203031200c200b40c450001900d0301000030524010020f0003510035001e1683d0118007002005d4600c011280904002c040c010304000410040e0b00001c1d00842c864000080441d0301c441d009000d445d0720120b81e180008042c2e1b507030700390744088800600c40c00c3e0780320741d00070100300410404001a440ca40c426948803040d40d0303160400c0c142291501d10410305168051601000001d01c0d580121a1044c40b801081d41409600b46000f540c0d0090401d10004908003c0100580122924000c0e00101c1c0d15140c00690105030f03882c1c102c08103903246035203c100600c10416164040007500048018081c8060401040300b1911004100c0e4100d8040c2c40c0055080c600c7d04150300d107014402d201965000380c8500c4c03860711200104031030140401d01004103950240b00701c0000e6981c1c503800402d101480304481030380011041c0040100000101405540c81c500001400707840c2c4c0c031884141c1a100320b50a0002d411907142816843e15001d59400c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 331228857 1250 331227607 331227619
    0xb070507031b0608090a2a03020406090501060219020904080a031e0b2106060108040c1a070b0c03071e050d1505012019290402120703080d0b0a05 64
    0x70808005030165080d0488000d540e55513040d0b140c104034951208181c200103401d41043c82544444c1120104a2042c0040002c400ca1825036581e408901910782942c0700b611043d070f0f548010000075805003d003401450901c110443e168031140e00168a603500076101030106900400d44074080c44c0268401414480f01c00710f00300806c8282141c00e8080c28010503524040d0841400105c0307182c21400641c408407017224003a2074240d50314401125003402c010030a803100c4d140d5200c00295a201603084081d030030140040141d980d0102d080c1510702c01400f07030030b4508580c0308004020043c1d5003c20711042900d0002645640903030f1220040307910780602c241ca805214901007070303400e00f082d4440d8000c1c201e6100b070300d403200e20402d00f402c18420340d840d000384003501c0d401c1000109440030710340380c9074010140308080c00080c090b004404410035a006000c05601200d128041c08190302e0840282d4041d5241d4000074512203056507a00f80c07040c05204003c03c4480d40328034862610f0b03544c446620015200c05041 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 331230107 1250 331228857 331228883
    0x61e030809060405041a100302270d021002070609061704030c030e0613051002010c170a1407050903070519050603040501020c030304030f031404080403020d030201061505090906030a0b010b07050703 87
    0x701041c0286141c1c1b4600c600702e0548441d0289009000340d8848540348298640e82545c0c00c5404403000c0d5804803016401400380c21440c00581c0d030b40e00c0840c91009168001e010243c106000a001100d250b0030600c1886a500f2868100c0381600b00ba03554441c4c1e140c98002d260b40c50301d02c1d09949507403100250075030115001c14001d01d0303200e00b215120b0440d40102c900da81c1d04000b40d84207900721210001c0f154000f8150500305140c50341c1566900d600172142c1d01001a210031400003000035110141e4030741c0f001070000912412103150401045014042c00c88900700035181601c600e4940704c2a03441114090340000c4002010302070f00f0340c103484c403054000c801e803a40e0b80352500c0d000b0030201040d04000042850516410030203008010301b244a254440c081da850581980c08000042d070034488100c2c210f40d00c842003c502c40001e2180314220408544820b034071607113a8002c0110b544c0b8001c110602961282c081080403515814901d41103603481105140d544015081c49418140a0340010f001400c0140c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 331231357 1250 331230107 331230131
    0x150106081314010e01061806120b0420060a09050f010201110d0c0509060a0503010e010801051509130212030d1d030f0a0207091503290f10080f0105010306061e03080906040504 77
    0xc0202c7e0206219602080300d0f60b21200c0e0468095142d0300c0c00340c410041000010f0000e6010040d2450f08520052803106482e00440054015800745002c2c10006080003010090350601660b240c40306c9c01c00f4002401030301180e91031a4041d0150221014100f6100c104098205000b10110f450422015058940c1d03041016006040303580700b031045402040b50311000017102d91043c816180a810289040c076803c01c41d400802900080c003800c00002204444030560051341e44101c403d0282c503010303000e15102c1e04210901000c681075440c0356050401400d110103d041b401000f00c0b4100090aa01c060f250401104100d20f0301c00213400c40d20b2080c0c40c1c40c504c020b003480c0308560b0034102ea11a5510701c0101e191005203410150740b840080d40c2c00f000311000314002240c502c617810b0b0300c000035642c80ca1041d5a1041c80c1483c0008440c1d0030007059640388010310510820380540c0700035044840d0a222401318072849800140107a2001030007001021680300029614035082b2402008010814421171100c10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 331232607 1250 331231357 331231379
    0x180b060306101409060403081218030f090604050409120f050a020c090406061706040c061b170c0312090f070503030a050307051204030302090901050910030f0203010e0f150106081314010e0106 84
    0x6a122409c80c0162000220350200303445154001e02142005141480300c407a11803111604501440d5030320800500011403032f40c90768400d59410314007a0340d10440403000320901806200700750075018100201006490052500010030114040c1c0980d16850180c1d12406c0c16802802260406840240101d85120074014002450313800741c2e00660740c6000d0f11350780390010350740796000c81c07010900d6450036075103030000c6481120007a46015401407080d2405107004802c6055502c0464404020345001d41031001c2e141c020401c6c0003400607448000c0180c1410320001075564040c0c0d066000c0cc020300000003995445c4210180e84868603090581c2100342070904d4040c020350005c000650241c000d000c00010cc0b45840b42c85140240b1111080030001410340e21000e0000c155444203a80640d201c05820100030400c102d690110307080b600281003418035592a07440e0703a02c01a40f1540800c5050307001d0000800b41c03900134044a96002c6c082c0307071428420b00c0c01c250141200441d080e80c154a0304100040d06a185 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 331233857 1250 331232607 331232617
    0x6030f0f0706090b03010e1302130203011511030906040e09011b0c0501140c04120813031109010902070312020304060b0d0803090114090c01030b010c0c180b06030610140906040308 79
    0x55240e0204594403003c0400d8140007d104000d070509003000441c00100d00c18941038113043c000750808141400c140050002e903882039100c41842d001020052003810303071004611650321810b4014502c0d00380c075100000c8e6580154020706007001013407008110191425804801c0460101c0d000c402c00e4071000c000909405280764044e50356501740914201c2e24010042e001d0b2190040c03542803400c181c1056200c1005848840c01101c58180c20011450100502e507450401540718400c20300a407926641030014194041e4022000140180308a40010b070304000403c041154440c401a200d503120309044000d402c02149264200c40021040d005200f079a0004501c6a040381000340007468604640c0074202c0011075a0710b859170800290012658442e4100009600301450814100f11864640c110480381c41c1c1c0c0b001d205c8a150000300000428a4010102e000e03000316080ca0661400d0000316100034414007803001049480714262a04103401029140310359009000300d500c6a4413440c0004055100b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 331235107 1250 331233857 331233869
    0x16061107050106180e010b0312161515050303030f010902070c091a0415031a0901111801020c0402160b06031e0c120c060a03020a03020702130c18120b06030f0f07 71
    0x600a00d200184414000c03071004041c048c0c002e000301e5561030301f6070600750813000b80e02c81e1101c680c00800000c0b4a000c100c640140e50600e40004500d2003050f500d03501c6080075840329003c1d030401d01c00c00c2500020001c0c16811100242405a0b981420345019501d0a03841e4020300d4a0713510380402211611040081d00b070303100c2d00c1070710f0421002c0c113000d012a1030740255101c001c00c0f8408541c142c03904001840d003034503013005845001060030070282240013115044412145040401500e070300c1007660b4100441500040162003c5181020301c01c00c20b060031001d10005401548243c0100e440e03030b00d08000000d00700c41401500848505803807226515611094042413050902c1119000c0d01c403000701e00c6032107000f002030416207022151441a4065000f009500c000e01d64240040b10158407603440f1100340b2558010b0002d000720b81410050495401e0300b96288040c9071101c1c00b13108216005100310072403608245280c00596035000020f140500c141c24100e2640603e4a403102c40000c002880810303108 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 331236357 1250 331235107 331235111
    0x204060c0c080118030513090c11070e190e0f1002071104060605030708150a03060912030b06040506090a0b070602040524270909030405030d03021606110705010618 72
    0xa6150005426284500e40b001c0c50390304c8403001c0c2c400090148004004124994402c0304103150383c2e08060049a06003500385010500ca488940000c2c041405030001510840000391254200002001000c14502c6001e841840c3d03034910a40d402c000c1040001d014845510886034194a440da120020790041d01c01100c0c4241c2c0300910810a181500545c01035610641c1c03000d095540d82c1000312480800a07013150b011504070340048080e40c81d11400704001d103014040210701c40380c2d42d14008c07085058152502e0101440c05501c43d50790f0f82e40408642c03c13120200e840c2610b80d255080010b0004001da070040a000500103009010044076802400c2201c00c100c9225084541185c50742000051002d0341c00c061070020040d800541c0164440005100c003643d621000b500003c030003007030340f2070010381d45012251b00200d010805850108401d100b106021701d015810520a0315072210710010000c0020445911390700b0113101e101144007038920741c1da0014000d022603556503003465024080030000000c03080c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 331237607 1250 331236357 331236359
    0x3211b0201020d0c02060c071e080f1201060c020306060103050903040b0304050c0411031b07031103120105030d02191103010908210606040302060a11160305070f0e01080607051c0204060c0c 83
    0x1070000c101b15116000003a155480c2082503a1688001110f149521845078150b40300e0502054100020301a0440f0100c610b90307540d52010020000780d1416031082c402c1040c1a1090001330328042151600158282804a4940c4a401c0d00c142180140c1d002a10f21400c00700410080c80740c00296840040400d8908002400b0841230909442c80219084642c629402c854044640c500100402c1400d000e07103804005903054105032170560744013183c2030702c904400700010f2017145030601c200b41404800340000c00651000f0440281c0440c0c1000024040c0241c032480d200c03181e1402c1d04000d40c0240d002c101a40da0300030030042d1031300912070401202581d180c10360005078242000021601900e800500c00c0e4140343c440380040300c0080500398116168050341010b440c44961000540340614401d0000c2d202c0b1504003210a840c203421540003500c1000c104004101f0540c0114074a600120b41e854156513034115289400b881d26400d440808541e8800031703000841ca84e0100d26895102c3c4500d80c002005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 331238857 1250 331237607 331237631
    0x4030606060509060f0c0a0209010e1f120201080402190308070605010605070c0e040c031b05030c0f180c120114040c030e060a090201090b03090607140703211b0201020d 74
    0x18002d9400154110404101e400880c010b0742000c3c6c07001c40c01e0441202d49010a075070102d80b06a00a0340000303100c0e61044c05111048001c1c56086000b5140c11035403203481450070400c04445c0c20b000e00d0180c1403041c004041001d40d142c1e2040d920a0090a10019030007507500e141c2f10105501c2200f09a0b10103103860004106240301e5021501030642040b0400b82e001d080c90102140040090412603940d22701803000000a659490b0060305074001007503191a0030300e020280342c20134101380e00306032243c00404e8103801c9503a15400c0b2000303050101480b83c41241d90306104c56070070b445400c00d000c0d0440d1001f000040c0203c04105000b2070090103950600c001c00510500350180c1d05a00c2c0c0061494211400140c0c81602070f0748004c02d018014501541e400f55541000000b80d4801e49805400e500074204004400b6000000089200da185980d90300c0e081058030020604551000260301030180840308030f60991341c6801075010308401800240100342280c002034001c0d13111400c0c0d044031500300310303118007a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 331240107 1250 331238857 331238867
    0x90601080a02211f0605040e010b0a09052a030a0e0a1a09100e01020a140705030904020d0b120106051207030c051c0f120e0d080a080406020c120403060606 68
    0x2140742d02074050540d40d60000e60300344605414007001e500c540314003071100d20102d10070b00711454200a0903e00186850a2000f44029510014101c81841c1e0400105209580324030090004481c0350403030010300360b2208480c40d01100d00c1c101c60000020703100c1407248001e440050045004e10b101c0a410003004c2005070282303440708100d40b070160003854103c514a1914841d0349845a01c0495141610995074941640104880310a044140340f62350214080f43c1c0305800c04150f0980d41c1c1c501e203070300e03041c40c2546d070b6140d0740c0707119485407540220b4002ca20420f03d01180d41058440b940000d11031085c405036000418000c26503845200e00c204100c035044554541d0104084050b40d401c100304000250030101482500001c0d5020b083c1900d4503240d804001c01c0200b50000040351060b03000100040040c2001404502400c00141c405e10a144280c400640301d403007180c428608a003002103c80c0e40c4d40c10028001d018205003940c0740d005914212103503c89010041061343c1c4100c0040002079140c1004a030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 331241357 1250 331240107 331240123
    0x240115030504082a030f030f2211010903020d06050a0605040e1009020d050d0f030c18031101140a09030201080f1b0d110a09140d1106070c08010204030b09060108 71
    0xb90f400300b00018100a610441a0000c0844c885052030240b0902d2a900d49903902c084900380d0461804802e02c00413600001d007180c2c001030880300c61150b920311004083c0b282c1c800c0315001003208036075410021040e40185952401107800500d103050118050400a020b05411201419014501a008107151820744144140c07540f00c40000d0103110150089000100781143c07050b680080c5212651001034010041e119030b600080d903a0b10700380851940c0c040d09403000c002030201405080c501c0342c441d84009a2065080701c1e04032107041e0040030900010b90390114000c03602c0c00d0368440042c40c03144164111f601c01c1c0c11240b00703903030300819580d40613070340d0181c0f4000740c034001c0703102c0d910b20312804004c50303540060310107041c1000380001c000003180c2038000503070310040d103c0012448008041000e01240746d401820580281c071f08100c0c501c4d8690303800f030030440350b10f4a080c8030309400729100c1c0602940030300074405045071034000c55860ba160304158806c1e95003190781100900c2204004200e0032004a6060 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 331242607 1250 331241357 331241363
    0x809010c080c0906160f020a0b040312050904020903010f05090d05090d02220c020604031101020307020c21060406060f0824220f120e0306061002240115030504 70
    0x1191500d5516120b01d4591084440c95400b860038032401c004003075591a030f01e01492055a064a004903581706005216100d5880804050003e2100304045100c503051805000c1440c6011603031155200f00040003409180140c035019840c0c05400d8640480307683c0058042c07032001e0700322a200c00807010111290f215030103806810440c3c66010f00014109002131041c0c0390400301e9520610580d4281c41802c44000360b82507070040c1e000c00d06000c04e042d0407040384046401c60070002d515602e05000041e5560b000c5800141c00340c014610f252020031000b403c0c0c1009c505a007401c5e11703c0c5041900740b120213014140189a50f020070000c000800c18000140d5140900c02418000c00c011071402549002c540020980c40c03659981400e004c0e00103484c00210740c11548526441c68010105040842542d01c13820030718010301095400601850381c001a8095224004550404040002d200100e041c40350108698100c0c6006c000800b043d000c00520090584400f1152148400d200410840c1611340682e405 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 331243857 1250 331242607 331242617
    0x9010f06180902010e0d050309011b211b0809090c1306030207020d02040e0307050c0427052b0f0e01050301030201080405160602010e01200405210610060809010c 71
    0x96010500c0702d81003009418014100032a600e503524000c030706a1030b150b0204403519000080d600c1241e682007800906a9103c860200c80302185682d101c00e4160043c0a107042042420140a80c0b158810011094a41d0740d10710700e10040101e900d0800156080181c9061190351403600040e041032004098501030f030300c81c1081024052506009800039405010282c0e04250325500090140c0c4981c00b400b0020440c0300010769640071541000f60500304604001c034840da040c429014040c1d174203014104620080c10040c0400401c0c2841e0a5242182c540461210074036410000380105504504510b04d4460325261704800c4084440c08a034064107002032140032540a00051015501c100a1a64401e1040301202c0381c80e0b010720345410741e40d00540d12080050f0b458038105200014203003c1d03000403180034a0030721500e40500b4416070460003240150381c007841c2d840c02e07807081c4507106504a24410510006544603424a801e084c00700040d107004c1c001c082003203000441d0346480d052155020700782e06907480b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 331245107 1250 331243857 331243889
    0x40806011706040b070210290108040b0c0f130e010f060201060b0d050402031504240203060a032a0f0e01060512010303030c0509060d0f05010b120609040c0b03040b09010f06 76
    0xd401c81c0131000341c40102144a511002c854001d640d00c2406460300c0e44030300c00030030a044505046030b00701c07041c440c00c0d041201c1e441c01e2100044007080340c203420013621001540c9840b05507900c16464041d01e048214010504800010721200d560303a124107880f020701c0d0303d40d256621941c083c2c1c01e982240c420503040850400401c04441c09982c40150000e00c020262003100b50910801003141c3c5041c1c030f080d1045048040c00d00c14100c012a076540c1e4462300d000080d411450002c1c0050040b846500c006800c01201c141141d8480748081a400c0b00d49111503061107000d516085820120700003800380727a44c04c0310200c00104038035008009032050100c2c240d43c142642da086960440c040c0c02000f20103c18440188804c00c1103945540140c2240108000005192101c510202c42950410390120340da002c5c0030003070300000407251b1440d580d0180c0180c41c002c0135504ca80c5000f0007145010b6010320141c45000c001d10007000005d064036402440304034024010000b0200421048440d144280f0410481081c6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 331246357 1250 331245107 331245113
    0xb1216020a170408010509060f15030c040c1404030605011406030f06280603050a110703020613110603090a030905040e0304260a0f051204060e0910031704080601170604 74
    0x900b010b24140300c503440b8181030382d6600403401d603101541c0c8039405401c56001c00413800340c1001c009038070004e44d80852a6064510012036160750700c060381c0a00442c0c82d2003200c2c5005000b442c3c1501c005182c440d039141d0742c0c1d03500d080c80c400900080c0a23040c00702d18812940c000314501501524054070400e02d10a54545590013008440c400c4040d180308444900c000000d42c100d0500728102c02403100780c40101d10703803912a0548007180c11950301540d095000307004050201e503000a4040e8001c90302e00d0112882c03005401c180e40800112a11f041c0e0054001003001450039021a1f02c0c140c90348641c40310f50031035860707030100003d81d130154520411560062200b04903800003105960134080c00301420030036194615042500b032400e50641506c00e8a15421084d0030080d040107000600304110814608141c240b00009000301c0010090324410401e20010900d240c5d28400300d800196031000c480c0d290445003804c8403201d40c106104580701802007000009040908228001c00d1000410250115070740b035903 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 331247607 1250 331246357 331246373
    0xc080a0519021c050f010c200f03091e040f020d05060a15030b0d020d050a03080f19020c160e01090606050c100213181406010318060209030102130b1216020a 69
    0x100641c2c0f85d21a004d102030301c18100b0b21605c01b000c6000d030784003038000051070010480d00c0405800c400c131507404010b4444c144240071041d540b5020089600456055a144100ca000c29035030b130485a0041c03921424800c0300070a64010000c2c2039002c40d083c800e80c2e4548041042c844242c0c4524003200251600ca44506486903000e4140343c5401400c031800891181c001c10800740240100301c0300c80d446040700740d0070300d1b401c01d0349181e101c8182501400103180130454120712503000040740d04c4058000c202c9481c581d4090100e03030680c40c0c0e0700300e580701d519130f0b10146400180400c0c800c002a80786800b101180852098085030344040d011801000050389106000d8002c0d480a40c1c29640d4103021440455240301c000d0303890445010740c000108801c1800d40f00c0240c00040a0b000a043c18601400c048810070318010240040e50007810040e10b0b00400c0c004640a441103a01035003541c005044081020b407104000782c101e0000b010703142080c030794580070102d51030921800418003690000039000300140d908 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 331248857 1250 331247607 331247659
    0x142b020a0f0e010c03300504080405040b0a0303020d0503070c0618060f020906031308040b0c010c0807030c020a0f080c030c070807090204050a150306170c03010b060f04060e0406030c080a051902 85
    0x268404041d11a040c0a00d2800c50347c1c251350449041c0c8001030108898a002e001c1c0d000c3c3c01400b200d1400c51280b82da980603641d110082083c0b424894040b0000f40820b00a4006400043d042031003031000f1168418a01d0010358252401c0711418540110140001858420359041090140003140f460f10340181c0070000c400b03920001c80b0f5002c5c0800007c0b80c140c501c1c4018140380060040040340109200c40e015101500061003081090301d01156590403d50004400341100d401014240100980d818091103e114500400d0703480d210010f046110200c0018002080360301c1c038420741d1000b5440c0c1505c1c0059200e140304066010980d41c1083c45a4021240e019031420030740d0400040d0951350b070240c0c0701c0c80e4080c1486c0d990503400181207032415050a004002c64010304640700c0b490314680b011001003500640c018102040154046a41d0a4603158030190256801c400d11009440d900c0700300d2680c805182000712450301440c0318241c0030680c20340340d20700c40550080500448445000c0e514052401e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 331250107 1250 331248857 331248917
    0x2011e1109100804151401090c0207030516060207140a0303050c1908180f01020d11010e160f0902040b0403030c3f142b020a0f0e010c03 60
    0x1003102481c26600d0601d001c000051549071000300d442d00b0305201c004082012180c07014281442894440c6842400305141519a440e500007544a03001c10224905002504000d04c60f1264214520050000403e40e50882c0d1440d422211250b4403101c07046144088521003642043e03100e0304c2440001c1c003680151002d07594a1045640c041d240780030b070312501c602c5c591013520018400100c500b00c01102c4c85411450004c265845080c1101620000350361f03541c0c242001080202d01500e03490f1400080d0010590740d06140708840c8034078070480700764800142d14401c1c80e410410780800081c00301c100d4001e840407144604191130801d80f568400307440044a099040329041070220907805448043c1001c20309043c0c0800300181c1030391240b046010801c002c0036a590a0018900d04140c142021000b00c41043c80d03e6603001000017282a0040b01c2c080c101e6504000311400800d059014170b0b4001d01c4540754607050b903035900401c000c840c01520402c0d400e400140c0080d00c03000000c80f981582c0a141418124 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 331251357 1250 331250107 331250141
    0x1060503040203251a07030206070e0301020705010204180506030607090306150b13051e130b06070b090c011e051e1c02093a080706050405061602011e 66
    0x60f9410700380391180700082c8807010084d0700d4103004192440d078055a0300b201d0605072528000e1152000380d41d40e800102408208070240c101e50026880039010f0350741141d481002592902e856448014105814101c0400702d90328181c0000c03520714000580b5401030300552a4030310f059055440d900c019201c18482141c100705013a00001c0c610710f43d00e004098005081000307522140c105800c100d02e1406d24006925a2107030103400840e02d07510390100104130340620303100040350043c03480803074054042d083d80904400550000c110b03400e075010401c6d413a20345091340c03619901180010403410314608140d000700001e006000b000b0b000e8082a4a4a515440920100341411108861569000040c4c1c2c0b035140000c0c0c000c41c2201050030b0061400084e031208070303d480100c0e002c40e4040300b08645280002200b002064002c24180a60041118a4241c01503400d0201d482c042c14400c4e610001518583c05080b1007007000c503502d0b031041c070030044480d100c1c60085500703d041d044200c02605040c1c0c401d8209070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 331252607 1250 331251357 331251373
    0x6020f070c14030f060c040501050c0106150503091009151a0a080d0305090f0309130603080f0307020d1103030105010c0309050d030215010b09060a0323101406090901060503040203 79
    0x540c5001e201008080704005000090488070506040610242142900750300583c140f00c41c258809041d14281d503003c2c40c00c5a00c8003040c0c14100ccc0508159032000388001c088100c08602c86900100540c40380000380121403c000c5500240030495100200c0500403000006501c092540c0540084c000310f40d00c2002401c201014800207240307105260b209180d02e9011081002105406000703042e80240300d0809880307804080f400e0b00340c50f03101c0d03c4c02103441041010f2104200144950011016640010311240c41d001c2c0c0e0303012400141d00945185000d486140000b40b001d070311407210642802d149101540c116440c020040d6000c101d01c00c402c03001d02540d03810214040e19103d40440c1414000d50090112030205c455007520281d068105480941080228007840e8440c44200c5140c0001031a001881d218010522100c1420075440340800869400610401031441e112010903030303e8042803410303045000380400c56248118030f801074118041c0401000803134002c4000d582e001d03002900350749034030b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 331253857 1250 331252607 331252613
    0x5090d05160b0c0f0f060c0f190201020a031a0a0306050703090b13230604170d090506010302040b120604080c1603060c0f0305011d060a0f14090c0906030406020f07 72
    0x1600786402600c80082c000c40c021401c00c000308541801244580090b101c08229405083d865180c02400350f8611400021706100070034a072070844206204803018034018445a070300080c080d51000003070b540003a0820102d2a88511410403410040030024842d904452a56464074003901004090206050781c030040320002c1000368015034421150040e44100c242420b03d06104131010b4015a40c2c14054140c0d0582010500080c006402603000800c031058190040d500c0055403092407a400b903594144001d00303040080004005060f28406c6506100c1c00c0c00304400d01002c800101001080350344010b0200c0c1c0841c01020041c80001c50700300130749007003101c44403c40d02c0423440340d40f041301c000b6130751f00040c03100c82d600c484105010840c610701403065525002c4011444103409400801080f0701c0310101d4960740e03c0320a80d07401414090b1908a400e071743d4010100e440c10352000510700907205600010645507143c01111003000d8004c042d10300756200e584401d0001c5d0003030f059802452000700010004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 331255107 1250 331253857 331253893
    0x10020c040911150a050703080901090c0303031a06031e0c07081201060215041203053303010501050a030b010b030a0f05190e070f050f010c0c09061a0a05090d05 70
    0x14a0055203007416604122003800a0b0103612200d4900152050103411130090384001240c40b01601454080082c0d21003c14441c01800c210500800d442464800013042503095001a824603a0618103c81b01c0300c400380910201b031004440741080c940300070381080340c4080300704903054000f141340380b469040c0030360b079580c2d4181a4032003d90041800b001100400c611a810482803c809401c802502c4084c20540d80d17891020b000c407100c2005064680d0700065200c1c9040c210070702d003071109564100008024080c071610000442948030300075401d100020484d0700345080d69804890f80700f2502540340c4e1800048041e1600054425829a901c42c0c0d0081d4401c0c5160180350f00030079200314040103414101030700c00d0440f00d160019041d0742d00403e10800c2400d160f942002d04075801616945000c0c41070b000102c441c001d10850041805845c1800440c803c061640b101d8152000c2c1c1703124009034805c503507552400e4099620a40300141c410486400c2508040701c04240880c424012900302c40703c81b44036110 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 331256357 1250 331255107 331255121
    0xa0b09190e01052703130e072c010f0203040f09150b040e01061b020906100e030a061a01020303040804060c020f030d03141303090e100305060705040504110c030910020c04 75
    0x3010b044914413402010915840b400c80001d8000041d032501c150b9943c90480c00525121344030f121407403040001c511031b00030306101540344582c600c103401c5040080c0300206100c455031545800515000b5400070b14030700010484055400a540702e10f015458401e0301001340c0704440c10508141c0e00c14000241c1780c1900c0c400b41018144800d1003824541c10703e20014001051a00d1000001c201c1240000142e15103041a0703404c8681a100305401d8007e40000b601d00c9807100d001e540d014440e9500181c00c0c09031560290084580c508130100d59000e102c401203969010036100a400e4603070400c01000464048c290101c5a60b101815030b051480c40c0340006424007104040150219450385003101849055940e6954449002842d10722a20300e540c500801c0707c152030140200501c842d502103461002c100400400840e40407080324002d00e400d10340100303540c12520a880c0036a091901e41106070103200e09881d40720080354011b6050807400407c010b034a080d542e450300151701800f400904181c5a5018440d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 331257607 1250 331256357 331256371
    0x1f080a0f060213031e1a1e10051203030609070e090a0506190305060a06050a0f090518010e0f060702010b010c021c05101505040b1c050708060406050601080a0b09190e0105 75
    0x14001d80228142100b44800c1191450300d041c1d480c3e0104207c110001070110035050702402070400c01d43e6440081c00f04035403290402c551166035280d02200d104000001584607950a8030401810b46501c44141c542900340d50640e07034410040e000080e0204015841603074000d07001081c03000500307030745d081a041c0d014558105641caa00050704000d4a40540d02402008040940e182c00d1854035107004004001d001c0e0265400803910f850114401e00301c15041450030f815401d000f00080407104c40f01c02e43d00d8031007111000d00b5002d0080012000b43c010b204880c40c4c4141071310b8260748440c0030342c00c2149403080020380c503c541021440e8200442c00030410807010303440010340007c031405902c04050400b402079000500c503e050540301d00003038549603c0707001031141c01742001c0e40000103860141e003007003100c0d003200c10b41e44128002c100a015194000ca40101800c0e2204e00e242d40791689080c0a684840081a41120101001c1913100840c80484080b00c4585480000d502041c2d0441d0303402d4070380a030740032 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 331258857 1250 331257607 331257653
    0x10603080a0f030b031f0b030a050115080d140f0a0c0f0b062404120201091503090c090504050c0f0f0a030c1a0a08130f0b1f080a0f06021303 62
    0x40b9540e03030342600c100700c55504c00720010720032109200c0000710004500440070000c1c2c2d07107854000109440400c1000f06090f4080d009100745143e01c054180d4800980c8540c802d28400d40c3c50810341903002d0400e201c1513508030030b001468480c614010307241c540e00c480081400c000b81c054013803012506215406044601c601580600e80c24124108511401c5400106000498603104210f401d03043d403007194201c520700c02e00d030420809a4001607a0f00c4410f80d11200209498101c00d0341044e500d944115a076511511054040e55142d81c0680c0131940112001020b90380094036402c60b07850800340c0802039440061911006200320320201d540c203c0075074012900040340c0c1400780a0f00c040018140c07005400001080c1c10940111002007030440080e000788840c04c049402c0c8420b09c003111201e160041c0d0031a07114022410940f0144402032181b00080d034a42620b04c1d404514801d0101d075442c4a941c01c5407082658070941d4030703410020b520070080040946c124800c00800901c9a210360040402c40300d40d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 331260107 1250 331258857 331258877
    0x601090f0209060405100c020a0305010b0103180503030f040602040503070e04062415090b04060e010e0402040503030912010b121507030507080403230d02041703070206090d0302010603080a 83
    0x1054140c48208450814490060051403040c3d00c40e041924129401100d441c20009134014003540d8036002088080e4001100070408800c0c000150030000c0c91a00a1340c007005003105088541303100ca60304072802482904100007040c41d11104088054001d8010b15005180660703075800a4a03041441e0b000e500702041030002c110500c0468800d00d103000500c005800d2000704280382c104504015406000340341803c0024840405200300d1035440078100950b04140c0d2283c440d000944881d1103000000e00140031003c0d50340b061f06281c000d5400320b800c05030085050841c00e2040025281001c01c0f00d2030507660f0703810b12030341c690b0307440409028080c1d0002c05002c04601e490100318121000034103140505d4100030910503031690194a2a03071042d09840c041c0b1020800f56061080700000749000d0943c180d000c5001d10190841d030b03004004440d5a9801c641c040704140341caa54aa0059040c0a9805281448420440e00b007064420306014400d10002640c01c0c0c40742e0311303054250000b03000c03500003a181100c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 331261357 1250 331260107 331260119
    0x402090415031407151d1201091a0f040305030702010222080d0c0809040b060705010c091a18040209040902100504091d0627072c04150f110c06090106050909070e15120601 75
    0x42642e0700c1c2003c400b6201d503030328107524003a124bc44041c000600b000400000180c400780b017941606c020450260003030181e07045070201c2180d50780680c09200c0090203111380840e141070090800400b0030f80d00c0442281070942e15800c0000828041c030b6600c3e0481070400039000003d00a01c14141d140340d0030346a40c101c190800800c82c5607290f07081d42400c0c10010403c00d160800010100f00106d0380022500035a4070848072012501420001c0f000035000441030202500081d04a070144c001e84414000402241d0303200da4074480349030040c84125400303400400100c4d81d58468010085000d02c040d08020100810407001d45184c40c002d0b600c031601050038407041d0100c034442c06613810918559180e600466013080d440d078074042028011042042179641210751100c640350780026120b2110201015114602e0640c8161540c1045070b081c0247c0d480e101000c42c1a180c81d240d618001c2c12584001c1907940c0c146000c803000c848003c0c00100700c0d0001103110100544e900d00f40700400c0039640d0090081545821 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 331262607 1250 331261357 331261373
    0x30a0e0c03071212090b03180607020102070b010311061c0e01142e080a050123221505040f0c0e01061d0402090415031407151d120109 59
    0x30312041c1c8260032010080004808080071610002c2c0c118590b1031000c8804001900d85e40055030022074010408410098919110340301010340d50821001c2e40c5e9030f644ca025040f4200d100e58400208418040320051000c01c00c1200c00e04500750018110510345407948100c030b032404148803203220105d9282c011010340c142d020300906000c8940d015051403941410000521408028003580c8562152200b141e2440100e03010b5902c000d040c1c20703041d00c92000700d50416074003a10404046203503542c40480c2d605442c3c0b100e0388513503105440c008416011080010341075040f00b40030040607114034540c0000f6100c0700055124950290340b18090520781d5000d649090a03040502c0e9002841014044004000d8103401c8000a82e10000040c09466100c4000000038024014040c443da0058981101c840110200a030841d082d28021003059001004582042e5900c903040d0084c140c0c4590320204101d00c80e40200e480c50f1201203040c0c1c2d500c08485400300030444440c040010040260344422011003805841c07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 331263857 1250 331262607 331262623
    0xd021c0510140106030902011701080309120304030309030201081003051516090e0114060d060603090c0902090609010f0c1b06090f050d02010c08160b060a08010b1e06040902030a0e 79
    0x4803400d100300b2411a50404991405110300014542c562260001710381c410303840300d01e104134640120b505550315403c0103640c0390807104075203018610f802100d1010380d0380081036804481d4541e890001d1641141c0c011070b00c00001520f5195201c146180200001c0d41c20310600360801c0c0c40030000d401e54075040707104003240d5600b070b0200814040c1005091100200c0a454181540c0b6600303000100480f03d00007081d8188105054030090713078a07043c00810701a81c1600400710090040000c1c40b0900d8071402a14101d20030f28020710390040b810003103440294003039420b000800481d81451908244a0307120301101200c01d0920200890380c81d00e0030312401c0e821680000180044460308800a400d11010660806103500003a06021f001120001003101c0001140c440d1011903030942d603070000c14a08a0856501070b54514410016020f0200e0702180502c01c680e01101d00a0001c0381000300041c02c01c50380c40e03554103090b4010008000114240c074060000354061914231400240071909188003900301010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 331265107 1250 331263857 331263883
    0x50f0f120604151b0e0f03030c0304090606030b0306070905010c0807050d0809060a090c090222031406130809040f0b15090f0f0102030f030a090c06020303040b071e08060d021c05 78
    0x8001c280d000c0c82030f8441d40391030704585c00340c5242102400c1e0b00002882c50080115012903031200180c04520300600340c1014080b03d005072414040b400d5000105070711071a084909000003501c41c5010010366118100421402c0e0241a40524041c0292101c6040401138408079021942c12070034885018810040c882d40030701144402c0019000c15614031000380d92a11444014940201b15004400c569616151040070510342140e9501e551b8a4121000b24035017050300c03894000c5000148081c61900700c40c500940c0d108048071319007000b45c41008000e001c00e10042e0a1640d450b105040395884401d64429001080c002898442d5202800c024000c1c0380032581d01d0040a00606492041c0d80000503540c074140726a14140c1c69690f820318620091a241c9801b52581422510015100d07401000850140d802440c0e20031059440200c20b44940390350b80004401e04841d00c0c0c1c03101a0034801d8074403a4128200070086801138002d900092004c0c1400c0d103034182f10307028020320311040040400c840080d101c3c0f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 331266357 1250 331265107 331265141
    0xb0f03010e0307020609030f0105070207081b0607030f020a08180405061c020d060902031623010210020706090812070f110a020d050c090a02030105010f0306050f0f12060415 76
    0x1c41c0080a036164000c0b6800203000e244003045500c081d0f80c1c02c3c000324260b9050349008000d180303403213280250755401500c035402c2c2e240240302600c0809000240c0c1d080f040800540740900d040f0032580c1c101c0c3d650710514003440450065280580004142c0e0004058828659031141041a8a41c0c1088112b40e4040c281c1481090031051354034444402c0002540641d4044500c00000003e03801c1c0304002d0000d181000f541801952510100c0085c107040b04401d41d0000041c00300e40c2c0c030b25003003406550040f100060b4056802540d04010001c002e4000f4508140b1032900070916032641d0750703511440d0700802d8031130890400707450400809640c0b0500242d820750b4541750115080412018482d00d4280d41c0101038010301c8106441000c1c000c2c00c01c4081e6100c00c0140070391400340b9144603840006d40082c050280007560240c50458054807038080c81d000d840d001811842410b044c14100626032810000d40c0d50450302d0149020071084080c808c6031301c2140152100700300f40e4907415051003111044812542091 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 331267607 1250 331266357 331266371
    0x6030f06130215040e01080109120f0804061e0510080609030301060503060d0201030902030a060c0e010e01021f15030506090c22050703150f080601080607140706060302060c010b0f0301 81
    0x11580028070304015030143e0741c940380320303401090750078091140b600a100302c40414000014240015441229414003d400d21140c28403503070780441d1300e580c0b1444130300002850318011401162440c4d05c0f142c01000984590582000e009100405079401285d164003c90502e0b201005002014400c540c0e1091340d403c00f440c55981480c0e0b02074000c0c00050209400341c10030131071180c11a406076000700d05064004045881c852070030302e400000740003001c030b10310001000d40360b40c42229401100b604086c0e2005030064410142c0a4151282d5070100a030034041940c0c54130361011a1100800036413015502540203418245003a0802c540350140d10f00c007590043c01c0030ac455407020004c50164081d000364070a004070f0b0355103600f1003c4001d00124001c2100705c4030707000400184540b05494220494124000740c9100341e0380e03a160a6114841116000301040c030801840d0380082000008003c1d02d8850040002c84030780340e402055541d0049400d82800b13039580c02180d40d03e89000c03210400705040440c000d0140f0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 331268857 1250 331267607 331267621
    0x108060c13140402160b0916120b0912030405070f0b0315010c1b0f060e19060f0c051204050405090706090504090213020c03071709090613020705010e030306030f06 72
    0x440092141c41078510740e014000c425543c075601111420100c40380185401140390030800075185069441e41038520508000c80e8030414882155411200d01030000910945241c4604501e250001e0908100780241e044004101c0f100030050b40c080e0340a14010f1444a040140c900710402d41a0400944404180308001400000c203031010105a02071034144070108051a01c210070203081c0c20740002d2100084030102d44800c0c2c6191600031100281e030358000c22046a0203014803040da10038802d107840071350542400514042e80c02500604c000380340c0303282c0309030b00707070300e4890910100c0c0b0000951440000790070499454180106900061890042d0004500c0c0034030140c03080106126083c0190f40b12690a0155a15510300c0c500003150003009540e9000006070080d100d500500c0102d46991001e092411040203181c241c840104c2d015040c0400380d1103d000b000510f9211000840d05203800700f09050003d9801c0c025807050b204488000c54490800000b0075082020040c598141c5078807030000c020f03007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 331270107 1250 331268857 331268887
    0x20d030509180411010f1101052401030b0a1217030906010f05101d0604050303070803060301150f050d020d150606120c1e03060f12021807020303180f0706080108060c 73
    0x4c0c01e09007800c500309000d03040b040e1460002080f46540b02d510300301c20440c00e10403100c0d4201940d40400c80c40c001e0325841030300540445215400d910f070088801c0070140b001c0d00c510003203a41c425005121007101903001d00d4100042e9401103e01e820326400160042010540c0a0a100040d0038203c920069113918290001c14011202c0b0700d01e05051020100003540b5181d83c4200c401400018040d0303540c5403d0f0741420300941d4400e6071614000d40c0307003540b0001c02e0050001c0780b4082d90355602c0c010350224908820003901542c7e410301a03034850806400f010001d80f040441070000c0300503480201f41a480c0030406401503101d14a01003140d41450001684ca0350720140c4404c030303541c00080b0a040e0041c0d07160b0071001807010f42c105440841c031000021403c01c140720701c10304d0840c4c8210703040340c2407450807039264a0503081680c202d0050380c410300101d480080540c50544074081014121081030601414591031b003c9551710034804582e8100c0144800a000d01001b41e20940301c80c200c40c5030189140745082 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 331271357 1250 331270107 331270133
    0x1503120f040807142808250501021204090b040f1a0f01050a200a1406090d2a020117130614010e06190e01090209010e01090f06050c0a020d0305091804 66
    0x90607020344501784c0b18007401c00703d04024000050880e61004244107080800314860780300141006001880040d0707662001038031960000b00c0a5115041030316100e1000040c00001500d140d03c651188100c0607000300307910030b85586d60b010740190501d02e11b46609010140780c0300d02d011410014200644083c7c1c503001080c0701411031550490000b01d01108804074140003032140014418502499070380d500300300000f8814021050703070f02070f114039880c01c95060300d43e6498812003a6104c51030000d078840c140c0c40201442026801810058090b005406014900c0c52088502c00e0105c00b414400000344207151003a1010a40141725020141d41407030b00d2620340200050959200d25000200d03081041c4145e44101c3c020700090310032010395610784010300d003c0e4021802550015804130007010456100d007072101d044422800101c0029820201c0c22206944130a828000c184100c0c0341010058031420b050300d042601035070b9100d03212243c4800b00072403054001c1d504143d0103102c4040c04085000059600 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 331272607 1250 331271357 331271389
    0x9012a030e160b0a02030705030703090317070312020a110a030f17041a0c0706140403080f04120302030a0204120803010501110a03090e06120607020c12151503120f04080714 76
    0x758503614a03250072446c510500c0401042e5000c04250041016000301c03034082600c0c4600c500d1050380300300c0851a110340c02085406000141201045841101c45030b006000c241031074500810035151025030507180c121001070860004000200e0a00d90962243e07201e1240740401d800c11125041c591910851007181030203c0c2c103004003000101d16058000070469140c503511550030310000503404480d0140500c100c40640100e002080003801050003495141e100c0c2d503000003040d000142e890b0003203000b03400c02000036000c0d80d0300b0040860354000000b01080440d100d0f00c5d80700d9030b9605240005101d0f04144440c1c800e6a48011418000260003484844c140d9105224024003a9602d0700000c8801c02e1006600310540207000c00c1c07208040c2e02044038201900f061360303803030712510803c4102c550f26016200b081090400b280e01242d0408001d9140504100009084a031102d2101c684070505900181010b02d82050000d002c0005040a0005100401c40c5c0d03013425480b103c03010086440000201030f04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 331273857 1250 331272607 331272629
    0xc0212040b0d091415011a1b0709020408010b0a0602010c050706020d09080c0102180a081f020409050c0705010c0207050a03080306130e15101d09012a030e16 69
    0x2102c008046984041d02a68100c0c0c0e41e82c02c01d00a0076100d0391148207040c0c00b08409000100007007851045c40d2401c911004408035001e1a1200c25010120704007050b81c8500054015035400007803050090001d0b001500000c1d0001443c0848031040204195440d8800c00a40e41002600317090150402c2c00e9401c200e0b005600541d94064a5050900500102d10024030480020070103400701e25055014000d0b00c9265540d4603003810040040046c1c9e03801c2c0f8400c200c0298400c0e5080d03403c0840307050f07034200305003908440941400d844440d10000d84804481c0b150300000c000c240380c401c1c02401d000344c65480c4c00c0f500241c05114100f1000c0707a003052413804080c04803c00003011452644400300d0000644000072400c000d84c0c0400480c66031258903601e17040e85400500404a4800d628440f0000115501c1c01c00c00c43c0c42e200300344840b11302100020144042556203500c100b54000c1015035810864400c181200700001903164040c0132200c8251020301d0075130150350a14490034807990340300f0603110114a9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 331275107 1250 331273857 331273867
    0x91b02030337020307030c110c011209050607020a0210031109010c0203100f051e09030909060a0906060f030509060906011e12110301050f040f02100318150c0212040b 73
    0x304014403424818040c8a080e80b07030650b0707904041c160301a501a4a03195010700170301e0a40e41c2d003100e00d00e040c0c8071181c0d40f94103d805910fa40f98010106518000514840851180c4058580310305000f0112101c601503082070b4100411440d1002c41044100c1041c20100090000c8940841590003207410180c180070307115a0041c00c1d035900b009120b4080403a000d0034004034001d10171102c050001544c081e18011001168070140310300030945140309992500c020345c241864502000903019000c1c042c0e50b0850054000418054020b0140d0700141100d611048000d018101b03000301101c200500b0005d607170b0806014800c0e203003000305680d070440700041c1304103d0b81803240700000b04565190384030640074081950f00e0317420070075503400c0707074201204c00c400030040c0c1c0da140c1c160740e11a1030044500030701810091241400620b010006071403a14254640042c0001d135101082e2407421081c0d40035221020300c0c42d050f2200110038010a0310502140c405080729001c9004090800d0144bc040c0705444400810 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 331276357 1250 331275107 331275151
    0x607080a09020a120c150c02030c190f030305042301020d0c08040b04081b0d12120f0513150c0509060c010f110a0e4c030204091b020303 60
    0x1507141d018204c1840611001d0381c8a01d405000c501c444d114241c407212042d810714030a5170180045081c8240c01070b003d056900d6120301006144004440040300d510280403020401c082c1c0c5410400c007075440380c0c80e40c41d80d0710b0030701c040c43c0034103400f0b20700c2e18160495000c828003059a0216400d102884607082c010341006039450414100d02940d00301406400300441e00090322000012103405070110f00001c18030b1b51055138240b040004485c6809410700507499080324419201d54058444020701c0c440010706120b500c0c40d0001601d41c2514251560a900e40203c414840f6025010000d48072100c1c04000b40620032070054914080e1501291189001080c0004210b8003034210b40f19130144480200807110302c1054030b4202d500a5000300700000c110314452861402c0c450540512681200012136242c031010414440440301050280101d00c00301c08206905080c1c1130940c6c0351994180c4015860b941402d680b90202c40758680324000d02e040f9101841d101c00e80210072a07411460b9000c00424100ca588 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 331277607 1250 331276357 331276369
    0x25050f0f040e010c0f0e030d020d05070f120c030e0909100c1106010803030f0c04081207060b0a0f2313090c0b0d020406030b031c080916030609140607080a0902 70
    0x107115807071035404c040c04441520380c0003c1010303942c0300944070301c82004544000c3c59521491250302102507440002d400380780501540240ca1040d200310003902c07060440da51801010f2195a031030b0780101e00c0c20315003072007010f81103a491003403544240c88441492400850556842c20304100041455950345100d04516104500b00034030620b110080300c0302540d550503440c3d0b60b07a20440d43c0b003014504440c0131920076132228046408071102d8030028000781c400c030982201b0070350180c5800c488080d600c0c0004940c40d121000d01c44000c11441d0340701d00041e86450f20b44100900034000c0d58103c20550000e0709000d60310030044203080407007032000044210003481e0140c0c004546800142c03401002145200444d0b169400410645400ba5010b000c00b00d094010306d550b40040c030010b0b2501480c2e40c043e0926907481140c2d56a0700004803012501a001a0724210070940090341095070056100c1d600710742484808015040c4200c2410000d100d84d2414000c010142a000340818800607203601e071246c01c1d95100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 331278857 1250 331277607 331277621
    0x712081003020312040e09160302060f04230102010c020106030506041b0e040f11090f04030c080d0606050c062d10090c0305070201050c030601140c010e0a0525050f0f04 74
    0x381c116071600e40f0a1280c1385540c2c01c184103202107410381d000003030341d8140049455000c07060452900102203041d6420003009800411850884c01c80c01d00000846651f030820b01c800000c0e00e14aa0085281498002801e503208008000156070408100b000001c0d800200164401c1c1c000840110705261796031408000a515071000c000c1d2010349040c0b01c03e01c10b0100c503e0404910500640c0c80c0d400045c028080c500c58219400110a050b0400150200b4020030b1001006403290341c40b2072510340c101250000f00c82e0aa04000c00203040454120041482084002c0e00540c40e4480d01d1811680b00e00c40580c2c4a95200a240d8072110400104d9039282246810a0143c18828001d1040d00d50012005009140440d40d032001507083c800410303803040e50182101d000e1030041e55244000403480c0c40063b02c4c0c2d070001450140315969140c003040c96020601015044910034409401407640d80c0d049078405140c00d12028140b000b4a450401c143c0c1d44c2c0840300c0c81eaa00c020f07207850800d6101900001e00030992 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 331280107 1250 331278857 331278859
    0x4060309020f1906090e01060c140f1b03010e030f0f0f07020a141003290f030d031d0601060e040f150807062a030c1509081e071208100302 61
    0x80c611241c0c01c5040e030110781c0030590384d040d5502e81e0304560702c402d0722124140a110340c0c808181503084007404124504d0741400032500b0704003117519000502d41c0d02468801080d10401d01c0c044440c5466026107007c0c014040440302c040f0066041440b08014059188030b00d0094042c440000101c44461b05c030b041055406160b0024100803050355510100420f01898003540351040425400200301d8600030b01c075480400c03900210464402c0051102502030101c100e1201d58400c48a9400c1140d0350380800604d400341850b59800b14405140c280b160517441d01c400c81c20034158200000501c000d541c442110310b0202c4003141e0100b40184002c0c5048010200c1c42c0c0702800483c0b52241c0415500740008400d000c4800030b036121039101c031415890307040f48072550400e0010141c0c5010074101180c450001580e801d8000e62500744954100c07048403044a9003a20704540c1a00f0102d400109103003910000075001000408051401a403903480009001c0c403409902c091200c50750111b5600e43c000d000d80c9016543c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 331281357 1250 331280107 331280119
    0xc0601140a0306110a030b1c0b0606070503180a050108091009060e1e07060e01080a0c0302090607110406171e120d090b060f03030307030b060910082a04060309020f 72
    0x150700c0c4c1034036900b035100e15031303500110f4240000d681e07090400c04410785000a1101100054501c2541e5544424074042c1c82c00354401c50510030800851002d00052100d518030207088103507200d90100380020100c882d031210341405840e03010030419a80c0421001d421a4008400007018a400e1816400900d80d0700c810180703500ca1690b01c54610b604410032620381009000481e510300b65180021240782200310500307030008101002040c3d0003815078211505200306401d025013040c2c0c0007800b140007070300807003000d9406614515000070705040c00c0c1b003450098044080d101c3c100c564200080796480500e900740380c0841c0301d149400c9441100501449045030325035245240d50b036000d00b0021000e021250f10a60302c1004c1400801d826240c9415249910748010f0046c60441d079031341000364002e00c4072a0300b2540100c010460440030342d540c0c4480008003640c0380c5031450142480b1142010031034002e030311103080030480c00b03601c0c4440b00e0460954044a1a40c6000f1900501901c0842e007011045401c46030004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 331282607 1250 331281357 331281371
    0x60315050a1d03031008070b0d2f120c04062016060201021803030a0905101b0b22020310090201020c0301020a090e0c0a0806010c0303020c0a0302071a0c0601140a0306 73
    0x42c00c007000540c000c1c0344031004600165110b003071050b11086988036500c0380700e4003009a205140096000490b03034484102c40c042901e44415082042040040e0030100000360010340a07084014007114590000c00801c2b100f07042609000c4040c0c44281440d24152030700c0b600c01000d03894450108110005180c000041c541884e595980107030103508040c8001c003001c203110303160001e182400010344d100910725035554196949040144450b13002454010001c01104101f40740080c02084048184103110b01d0324100b0902d440009800c0c950600619090103d82001e01e541c096540002c0c0125600140030000585810501c01130b031505801c0c40c0030540550020410049160f0840c050328111885006a800c4c2a510319907408298030a8180c0703c004242404081003495210b2440605c01c14031a080040c03a00810040c080d18001c0d040c00110700507444014184020480300000400d140402d104640c01e1400e114034043d25904140981203e040e800003410f40e0301da82c0c034032000000715000700381040070b9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 331283857 1250 331282607 331282661
    0x203100f0b030106080a0c060f05040f120209091f020901020703051005041101050708030c0d11070c05040606052a0c27070903150c020f100506040e01060315050a 71
    0x50090440a540b1075407034880b0019042001069205401e540911030103146410514150340d5068602d0070041080814000810b2510200250303c010785080107510408685501c10891401ca0043c240342c426004a0f22550b00c4060000c0c91032140d4020380400f5031254400c0004078a000b000380d00203000da102e120300c035038540c03111035200500440c080e060f16010003201c9401501c0c10b1241101c000d08400301000060010009400a01001111400c01140441d4642007914150300940805d4a050f044020100160300d41442000003c10b8036003041d908107040d02110062001900381400d01e41800e900c040408203406001200c820380340200482c840080742c6040c00d900e034048414402c0c030303556003001084000b40500790103411660f221120408a5800003c8400070348484595502548200b8041c401c940e05c0a000d448c401c941405070008052500c030040006840254040f181c459141035414004a42d9180c070f018a0004804004202500c0d409440c03802449808c4a110202c80804c09043c60 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 331285107 1250 331283857 331283861
    0xf060a0209030d122912010605060f090d14060901050a0b1c0602040b0f0c010f0b1f02070e0717150f1e0405011503051e0106120e070e07020712030c0303090203100f 72
    0x3585010790f403203106e00d5141010f1908039a0a07008040e03001f1414400d510450080a0060250040142001c91640c074156500e03190000d0071803940000303030000404c1000a000900c100c1e903004900c000c1c1440070b03241c080040351100c141c031a140c10f08900010102802c0c02082c0d012039004002d0a8402982d41040d6591072186800c01d040189155080c0002e40180d05858006c20b4a02403000301285281d105050000085201540c021403e5000310307200011074039543c480c520300c0307400d20ba1100384002c00901d6101d11070080042500015030000c15807101140c40e1200d1040c000d030307410746a440c3c1500b00c04064410440c8240d030601ea00a0402c00082408400a06500151450f94070300707210940302c441e41303603007100c01000008241011207001048110f100b104039140301108600300089803450b14024a0402c0304c107801c04880c282410f02805540c40e8100070440040c41c2c81913610a88004940e0b0041000c022250080c08254940e4004d4066540501022208041651082114510645010340 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 331286357 1250 331285107 331285181
    0x30201060503070b0f0423030f07090e0613061d010e0106090506010503190b0423040b0106050c0615121006030323030406020a1b050f060a0209030d12 66
    0x400307805100400206030140b007090720303a21700088441c1814141007008910540d8003a04481044503032251a240c19074074184410b04041801501070003900b4144404402552030441c02c00c00d295015000300032120f590010710310040c642c01080850580c1812015010325810900303014019413030400350382c003501c00540c0300408464080105000541d036a43c01580c3d5404101d5440108000e600b404c1b5185c0d0145522403002c824008000045c0d01c0003590300c8111907820842d0344550314000805100500940d000050f004103524603055140c103d030200c0c0d964450201038028261070b02a4003002041d6500c4001c504040a03010f0100e0350f01c2c1e54103240307074409004140b00030f03408100064410310358210301e01e040000c018022006a89191203903a46d200095006595413410400410754078190050680c46049000340100300070104d07001000d050ba402c20101800c0801468070400680160780c8011580301c41e01d00321402d1036200140200445030140000b0b07124080041340301c2d0883d01c5080c520400e485 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 331287607 1250 331286357 331286359
    0x6061e0901021f0903090501030b1e130e0c030c041b0e030319020d08072a06140405070e2401050307090305031605070905090705151c020705010b0d12110111070302010605 75
    0x1007047d59a500550859214500a540100406003054204805000d035406813410242c071041e0f1340d403001c044040c02c6441000b000e140320740000220010a01e401c1003211401a0201d03010170034030144442c1d41403040d00a11400061040c00c040211290b030b400e1040d120b05840c04941e6030301c0b01401d910000d46500002607204040b0308618003013a0403511541c00c68040a44600390600c80802410003840301e80b648042c2140c041d47c442020002c4d00301a006024043c5210348000c000090a102e6280c0d01060300409842c41c0260740300552400c0042418090780180b000e0070480d60b41e41b620a82161040c9140e000036100c1d21000031040c404172001e8944440c941d002c0d02c1514030705a10f40c1c070041c09440c8259944820303030b400050203021a251059000e40044a4001c00618002900316078041d11401810f401c200720394080f4255061003402e0251040700d0f070045400b41da0302e050300d599080c1c86000c4240c035001000100c1075580c0d100c6100350300c2002040002400310b80c5558441c03070000c1c085c0511b40034070303 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 331288857 1250 331287607 331287617
    0xc0306080114010e0c0c01150303050406091202090411030a0204090b0702070503072301110a0c1406090310021c06030b090f0607080601050717120103020906061e0901021f0903 77
    0x101501503002c00d85039050b03895541c1042180d4440d500240420f03002651a04025541d864844185034980700e95034000b075100381c4820741c580386801d9000e0703c1030402d544640ca4241002a07032800503650020b0140c0c0c0300c0d0f8004c00c4000c1114041001c20318050102070000d41191402640c40d051100241029214071502d80c219000d045d120010706885650303034480c1d0072148404a0340c4910102e029040207018000615004801c42915514540340000010b8140e0304d03050b4404081c440003d048400884420080c0c0e521460051128080395681003168002c15440d5404242c2c240da10856020b000001c15050106225083d180c0c1058240d400382581c51200354820009515556203001c90747e1482044281ca880342540d5400c00151500e1b03002241c01c40e44036256142c500d41a08020015124083d40d00304440650b40c15481070003a8683d003e0070741d43c401c807001e000ea0020042c0e44500365215080313501c43c05e900caa01c540c00507850220561228140c2c10481c03020007030740a001e5031020302c1c0341d400395a403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 331290107 1250 331288857 331288871
    0x30615090a110304061a1e150702181515030403080601030f020703050c0c0102070303090b130306051815190e070b030c0c0c040606080403210501060c031805010c020d03120c03060801 80
    0x10440407904a2103464045c0707c982c5a4200d05103401c0c14611114403981d0f00a034502001c9a00286410704100c0c68071090b4015141032040d216140c0c46500c1302c08406031000c2442ea0046889680b0380d0000400c010100020a07000580c280d1203500942d808021002d0f055450384410b18014145411405880c0749904c102c0d801c0c001151700c0090000212078058075240c0c0c80d10304050308a9220b610202e1081440c085203800000012110b05c541d030322420403182d840c45809248054a81400f6051004600a0320300f8800d210104440d0640300c0082c01030035000142070380d10600d0781e034100002036000b0081e8190110804c003411828034010010580b0440984200d100c8050800c0b086038000d0140c00c0c00110200006030003e03000d503d004009451400030901458a01040f280503140240c011000080300c10803034034201604144961401c0400d0580d0907142414a00000c11400d10000c0c080c1c452905907111000b40750241c07603403583e04d01e6540c0043c0a040f80210f0054003400c43c3c1d109440340b40d882c08030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 331291357 1250 331290107 331290109
    0x513050411241908100303120e0a06090b01050111030708030f070531090608030d0207020a0b0a030605091e2d011211030615090a110304061a 62
    0x1084511450740045406100c811810a00c0350000d5641d40c000710b0700301c0804511100e0000035002d0300c19207250310b440070400003105034001d0032420090301160042890300018800290032444c5501540b0b030000d40042c80c00d1098003050b140c803810102c003902140c500320740802030007a50181d15060303c00a032580c00d03224040c2c802240c0d9a10a0b601c000e41000e800b400443c0c1215044104240c0002003882c24905011000b03205160192044400e1880340e100445051240000c8500c5000101200c006c2000968a403940880c0c90b842916020b9109941c0015401304540e102c03010140a08420001c51382c0b1480e0600c0080c0051046009441c49050b03504006009a1610303001410742c02400003441009032240f0040a08016000659249146c03141042c50010141240013900070b00c0d03005407441da1042035040c0000080d002524250180c1c101c80c0401048040c80c140c2071800c0c600945242c8543c1c0c0e5546200c41c000c1c082d900089100d44800018082031011581044004041c802085010520510 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 331292607 1250 331291357 331291361
    0x312040b07090611120f07020301020a02070e1e0103020f0a08160f2c0402041805060f07020a0c030f06020912010e0706020304060e06070501021b0a0b090d050d0b01030902030f01060513 81
    0xc030051342d00c1d800358101e1440c0c3c4214101900036110020415410501a50300103421382e0000c00c030000c0107a0180000304514010424015081008100443c0301c1d05501d040425030007605010203402600700d451402c0c400d483e92100303a0000d0018074180d0b084428440c4900c94402180c0c4102050070702b00c0480820310140d60501140951005070389104000c0030350310385a0450400a000f80c1c1c2c02a60b40005000c1002990b02e400000d9200da07003d04407500d0460100d000804000d80b2040031940005010f0000900c61100803050700c0d000131801c041740249250081c041c0c0f140c401010b400500180c0d94040e2031105400903200b0402c214159a4aa611440226564040d038884c0d000052043c886400c0729091250003012114001c8002602c0c1c554810100710120b02100c0c0180011f90014055100380114002c4440d001103041014089485001728004c1c154000c3e12840040d460390b540c83c4103203a0307023381d1013045091781c0a410342c4d040201c00e01101e0b008000c1481007a014502103039000d0075082840c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 331293857 1250 331292607 331292627
    0x4050103121707120c11030f0d051503120309030d0627050615070312020a0e03070902030906040b07021e0d020d030504022b08040f05100c0203060601110312040b070906 74
    0x190361a511003132101d0103040050300c1c243c100e29041c020322500424150806000a0840c0b0100b1080c1550b00c801036829081100c00080284d002c000c6800d02030440c0b0313500452000701108540c0c1d44991a6118140024198401d030001d8003002d600e08a4005980c140b000a8102010300c0d02c020500e40d011306124440540f6030844040740c0c0714410120003031507450441d0182055070b01a10b4040310808a07a060881240d01c03021009001c104508004c140900d4200b00f54409009904419030540c10440d40555685c4000b4000409107104e500010388414801c12400c0d4031015403c2c440c058080d1005803684d00c4c0d19030304228034014016690f41c0c1c0d038041d0084c041e881c010740d0301420b0300008404040140410145e804107550451300c074821100045040000900003400c4202c0303c0e50050303407514080103464055070300a2001d200460000300c0240e81e002c02c1440e4030070b00030308008400c440c60380d0032103086214014000c40d002001d00203000030300990445840c4522056118254403984580041e0303030314000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 331294964 1107 331293857 331293871
    0x501060e06310f09050d0c0b01080f0c090a060b0f0a0305071706040506450f15010c08040e1006051306030b060702040501031217 57
    0x500d00da140c040750b92410000c50940880310946101403041d05620241160f032200341585100d42e5030015102c02d5400020b1700d0b91490301100c01b40101c0510b00b819202d41c90700d070002003501b03180054189c90450500e0024100c00b49404204000703446c00418046c0000d468000004040700904050040c002110002c151108070312400101291002048541000201091400104030544200b50008400d0307901280783e54035a00465603840102840440203001340c13a944182140c1d109004500b807841c600c4821201e46140c01c201c0394490140e43c04d1030400b407040085501c1d88180c2c0780c140e00e9400181000680d24000741c0782c0c40415000f950000d04c20301d20304000c001c07206000b0181c0b84050807840c107006092054610b02501d4406982c0140350500d0b58805d44400d0a90358402910380c2a036000b8000c3c40765686038074000704080440100300011418440520740800e003602070385841954 = true := by decide +kernel

theorem cover : BRFrame.Cov 331115107 331294964 := by
  have h0 := BRFrame.cov_init 331115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 331115107 ≤ n) (h2 : n < 331294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
