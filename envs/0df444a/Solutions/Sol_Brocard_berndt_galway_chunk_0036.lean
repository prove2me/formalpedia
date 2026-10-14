-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0036
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:29:42.501039+00:00
-- url     : https://prove2.me/submissions/b422f7f1-10b3-472a-8ac2-cad373182253

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 6294971 ≤ n < 6474827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 6296221 1250 6294971 6294973
    0x30103030c0614180f03070c03060b010203040e09060103030905120a1101020c030d030609050705040e0c0c030f03071d01030218060702030106090908040e090d0c020d0201030605090c0702031203060a0303050c0a05070e01030203 99
    0xa045c121820010044440c09034004904202150664a0307850251500214072811880208400141e1546092180307000704004805007059515606000301501c1c0700344c000318030440c003400040414903030000312194030680c80007014410a040100503810324107a540c6858050044980c89400c00303625038800d605880f40e03500704109030f07118001c08840364060342c001d44411102c02d1004c680c0d051120005407000c14447d03000c07a480c106030901a203a543e00262820070225103043e0201c0b421000009181c1c05d040028601142402c08581c03440c80c481c1850791109001c1c4000141c10025510207401032009401007030800e08c18213145140450b890f901c90710407402291603040109612410210b454600d509040c0d540d2028007046400308201c00301d40e580700300d0505a0f90440068184c8035405814403074403c440c0c010380c03508030500605091002001c41c00035081d90070410820640c0c0c91800c0842920b40500c0c026480d40016908a0718080e4181e001404c0c511481c180000c24200c41c0001c2030699100364 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 6297471 1250 6296221 6296233
    0x70504030b1f050d081614010e0604020303030112050f010e0d020708070311060904020d050a0b01110102040f150504030503030f01030204060b0306010c02060d06030803011d0603070605030103030c061418 89
    0xe11442c0ca48101e0b59030080400c2c0e072407200f040b40380703000304090b22103a004030b20f001e00e00100580c0804000200f10030031503503409014100c140b02d8001380f29200000c54034002034102442c0960000c0e4480c8414011800e402c40f0040202082c402c00700540a8019407e03002080031002615456988030082011500148039855003c9000540420700004603503210071303d000640038050801641b81c100652030b0342c005900344984100d04c1581e00445001d1100a140091602501000105041000e05604040b680100002c1082020032900b11049840010fa4008000100354003140c2038801c0390b0002c2c0441c8400300074408800c43c40c2c4c0e41d0314100ca200715000c208080e540e0086401c01e0000b1a0040d021030a41034a902c0942020001043e940075400c000090b0301e61242e95102e04e070780082e003202e1349003284504401e82c0354581002c0f540d0014800c500805c1d00d117103084c00040c010712050000904000d070b16807209040048540209a0100c030301d403800c074542d10f0400c903580142040c407108018248612 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 6298721 1250 6297471 6297481
    0x10b0102030a0f030203060607020d03030609051308070204020d020c031207080112080d05060102030408010905030d050604060510030b0303070204050708100f080d050c030408010501120c05010e010c030c020102011103070504030b 100
    0x10440b10880500d884401405440c044158000d40001f0240c03a0446000c2051500699841c2d011649143c801e40300042d43c81d0600345548200c6000800740f80c144c2c603a0200038408601c102094442c0a503040740c1c05030365201e070401910701030f0040c4e8440400502c0040341182c002c848600500380309503801e954010450303a960020048407068801d01038000d02d02089280040c4202d904200c8c0d00c881d060040341c0c40d10ba0360f01c2200d42102d402101c103440c40c1e0004202d10003034034914058260005400c440c1170081390f09250004e000f240c0c54556180503d03549015804054030b090041d608070940003030080000703242c1040d0203481240c00700c0b8241486911640d01158080081c4206003d030364109005140d0401009c1c02502c4945c050690018244010b000005004000740903540c041e10b40343d0001203240b285032070b1842d1500d803550001e506022189a400529990001034001c54940500d0f00c240d4424403800181e00400c80030082d010007900000070010310981000003001240d00c80e007c106147e03030310 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 6299971 1250 6298721 6298723
    0x303030c02030a0804020f150a030608060a020906040509040c03060c0806040c17010b070507030507080d0207060219061a09150f0102010513030807022802040605030109020d1203020d02030414010b0102 88
    0x1440c4401c00104d80340c1004900582000c2e040103218000140071402800da0f485154003550f044209800f000a0b11180184148142800115042280d00c101981040c48e14000075080740244d0050074014600080020b00340b0031035011034001190030002c01c11604540c0600146004812180c0380d01480c1004c0f600d00c0e00d684140ca40c1c1850070715602d10100a81d003001e10342c07040e5600460080e40d8a1180311008004103400740501d20090a11b080240034803a1007070406410b10740c1e0b43d0711400640d040b01642181407001d4403600d448a075407101002940454030345e0103034080c1d80e94520064000c844401040380c0d040248800828803101101c0030708807005900012404d84a080341d00d4126403030448544c00c0020300500c04550080300900584a2000d14005010134076400b20f54480b512a54024440c2d0070360034144a01c00241506800038041c41d22160081100210180001405e0300480f1000800307261080d41501c80c8248503190a655a045c0340c1030507105003400b845a01a00c0d4a0038a10302c2e86980 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 6301221 1250 6299971 6299977
    0x60203032706010302010e0105090406120209010510080a09030309120f11010e1b010c02100509040507050301050d020f0a050d0308010306180510050901060b1215030601050607060203060303070b100303030c0203 92
    0x5907041c0148080d0313003594011525100004a10303414040140208800c540e11402034201030320f00b101010076030b6040ca004101c0c0001041c1d2106001d41c400400d248892603000410940c8941412800304512415150842c0204483c0d20302070710740b084541e60680b070b040d8032041d0840c1c14003440e5181218160007190b01400c81d0700300e540d000307425406080c20394200010404100b00c00030b4141040e1082042c1500072818200794540a03100080c400550708213580b41c03030b03c2225040301051401c0d90543d81003a0108103040004a0041c0c822041c4000c3d84030142d640501000142c000a071203100108100e103805000c440007030000701e4880c1d080c13083c42c0c00c900d00c80d2144444540d40180c01031071040c1c0e281d071000e40104409080b2600e19501c424011506030075810060000050808030000c16150400114171509180480b46100350024001044180d8411003500c00043d002030005070b9940b07403600001d00d580f264400082030030301c0100400c048119201540030459020b61801e120101c1c031408103d8a80c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 6302471 1250 6301221 6301291
    0x50115020c0405040215040803030106020609161215060602010c021009020105070b040f0203030f0703080f040305040614090a08010204030308070e01081b070209040501050703060501050c0d030e030f0406020303 92
    0xa440201d09005900d0035800c0386403c1400906940314180818034410b09940c401d8110501c15440003004100d076035410819641c0c400440800383c511802c0b6000040713048180d41c4038407050400c0c80e43d411428030114680c1031821140404003003241c035a44120203800b8260130443ca40141c01400e150300580d849a00071007200a82c165526881e00c4080d0b660004c02e00e2000c0c0c4140c90b5440309950800c0181c80c100000d00070721308510003041d00c941d00da242c010901100240a182154079000600002a4218050300d094451608002c13054032045108600d0b00d0080c07407042c0d46c1c0015001d9002030b040f074042d40204192802542d070511950348081003a034009100c55017203400240e40c03000282d111341e00d14107000316004502690382e240401a40004164410070303036040d141079644000b484101a0107100700030041400382401c0303040403100411162941c10a448480a0648444e40004030b4003040c004c42c1e4004001c905070320381312601c80000035078035001140c43c2c1150b504000c002c180e9585c0041c14200c044 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 6303721 1250 6302471 6302473
    0x7050a090e210d060b04090b03010902030a06020a030e070b0406030c050a0807030c03060504050711060603070308030a0e0a0803040602040608060609100f021204120b010501030506030604061503080711030105011502 94
    0xc4900401004201e80060081604030181030100860f58501401307988010b0041000141c2c445040030109011500d0502a4500c030307a1420340c4840058a0115640c10720035040100141c96240d000c609801403c000140f800031405681070101d550f045030005081920380760365080041d51810901614240305409080d00494201d60014020300d1094000b018962241e240c0071983d01d036a900814240c40c0305071150300c0400c1c04071140741040c0100300140d69000504600400c01d00c0d10f50b49a00c0b6003840060718440c0c080b40c4460100c490100c0c10880c507101c0550140f4803e50303900d024149000290410700503800001d401d400407821900e422010386100400080805c4002540c0302c02c20307501601c1718400b072019405600416030b6144500e00241c80244440121540355200c0c03854038003e1800d0580215040c54a00028841152000940681d1182d8003090015004011401d100c045880b02d90008100201c0000c440003040b80c1800400d4144030190000d028698031140e03464070800301c4925981c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 6304971 1250 6303721 6303733
    0x40b06030705030a0b0c0f0f07030f0f090e150a030302060a060603060321030e030c0c01031103010b040312030f020a030c02010b0a030206220b070f020102070603020f090907020f0604030207050a090e 87
    0x800c00d4105c401d0740001e40d40a0340c070300d41861820164040d401c0b1307050704203604202144c4501403580084000c070f0031012518084180c0d00000324060403c405a015100301410300e04c0000d00840030b12441c0c42c904280082410104c640d80e883c00954410701181d01154032070030300100042080c043d00070103081c1d03035101c425a481d01d420801c1325400c1d0555030001400301510381d405060203400900080c000d00e6060000b40800703800000c005000e440b182d48201000000820040041040396070030b5805899100910b2084021015000c4000e003403440041c4141610028a40542940651080c110143c45400902c00d012101007000702c3d0410728840650060f02c200000510300c4594034241003a001032407050065592a8034524015400c140000c45284c646101d02506542e010006880205101d203015440c120b088000b2400d603008284425003e002c3c16404a14000c1c0240000d207106180481107403030740e2400f42002959015940725450096800c03950216054450307015981d801a42c0000800b1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 6306221 1250 6304971 6304973
    0x305011d03071a06010203070b0f06100801050a1502160f0311010507030e04051b04090207060605060a0c020d170d05010504050105030d020303040f050304030b01170c01030e0d030b04060504020a0305040b06030705030a 95
    0x8840f034802005181140807c00860000400c0102c0490080040c080c3c10a00352603c4000c1c00060088061000180008100108034658405800c102500c405520f10000e4500b026410303441c0041c00c1040c00001143c64002090b11450700c0140412640584103d101482007100151020310403c0c02c0500003840300703040c2c03c1e1241000d03001190032601041040c038500c4102c003140a003540243c0c00002d07000b40c00081d2002404440c3c003c0c84054070301110002d18142d05280e02400c021941400240544424044102808402d54040c1ca8145900020603602c3d0700d41008400149000d024191241c0e28050010516040005015000c0d802d02d4000b5855501e458072282c101c05d46034542180d09200c10040800010490250b82c4d00070210340200c8a4109021030201741040e05c030768641c604051030100b00300300d000c800092040724000503081c001202042600414080c14141c0c0000d0f40050001a00034403507541a804031b841603000703e031041410b441e52000c140d00d50203144a6207070300d50b1090721468 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 6307471 1250 6306221 6306263
    0x603070509120c0604060503090609010b0315070302090d081c0b1e030c060f03040506090a030c1101030609021801030506060903030a0f0c06050403030b090f01060203180301090203070305011d0307 86
    0x10421102c003412030300b01c0c80c00c00e00054050703031068008000260700401030002083d001c12005070002410740082c0400c04808004ca42e031024140c4401080045000105800364000d60484503c0000a0501c1010710b03443e0030080c2c0c255120aa00d4a022403500000000c0c00216108806135803074000c0546803540c02400000003140625591103515010303c034a00310b200e903202001082000d6500c2049600d030328184c00c1490030850010701290954208810410020394040000d1820641c03000741000e1154000c00101c0007031241d600044241031000682407105015203802c1000b81b042640c0c02e0040f55903100510041d801007514140c0c140d8014040715a09a010700f405a4441ca140d00e800300021400352119802d5484c25103099010a0340d45191080380d042c000c01e00d1398040e1000c0310031500355140000080d81c900c2006103441643e950110202c0d201d950039080000c07003d400808031481251281040350003010f0005021072078103044e1802d029042008820303528640d0300310601848402c40d011000d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 6308721 1250 6307471 6307489
    0x60c070218040605012315030a090b010f1e0b070204020307050708071a011203091401050906030103050102131d06060715050703090506101a0706020c0616020106050603070509 77
    0x101e9119980140000c0301041200c540c611442c010800802d00b54075040c4413805c02e01d503589001c28884d0b810a0005c007640c03610701420320200d1003040721a55982d90042810000c0035100b0300149400b00380000001c150081100950a50b18205001210807240c2d00b40444600420f10a500e4105014800d100c01752800364003641c3e2069260502c240f90201320342e1901060b51080030212551018107100c04007020380080c3c4c0c00e024010120780100b4030f0700d2a40b009804103100d84101c05c0007401c0307010100e0b40380c0d01c904252410240003500640e10b0f5612864490702031341012150b0003414900c0c3d4000240201a032000030034045400301c81125a813120360601c686035110076425500c92203c0403004a14030118468141306d14187d94000800100c01e00c0c203141061005071a599149455810600c100e0061000e06404010f580802c60340e14182403800740080d01800d41035215900038002000750080d5075941003c402401640204a02030300c035410800980400c0c0d6120001804c1800744030154204002c607 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 6309971 1250 6308721 6308723
    0x20c040605150c070e040302010c0807030c05120603030904021804050f0103020a0315020906040303080411011806030e0f0d0810080102040b030a09050a02030f0a0209090703050606061c05070807120e060c07 90
    0x140c07440340b034031040e060780e80310406d90341200185e40d00e49082000c6c0c0d0744080001d40010b4146810722030300b840c1d46001095401003d0b0030924140714000801c0180da020011a422348402800c00d5444410110102c9001d81c50041c0b11030040707041c04002540da0b80c40c000f020f4141c80d4010300c61a103860031500d504400c580044281d1412940c200921040c0f81d44010152000710310030750f03070190303103160902d05000b5030360710141c10505220091003e0303038603000440e0500c800d0321542c8c81e001440720004040c651601001445904260194402050b03030581d2142c050380c1710765038070804001090341d10700760207080348074610818140c00c41c00d20201d12084070a40000c03156030702440c101c61507140c85400082c104101e841410507154040d2034482d045042c078001d400c0d800305009001e000b5091079500e030b42c0d80701d0320010012441100e0019940f200d404051550680700000208104068a8214409450401c043c4d0302d11005c101e0101c04150b00401e540540307000a05004041e080d00d4441c84080f803015085060 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 6311221 1250 6309971 6309973
    0x30301030317100806010b0301060f09031203020c1e0a0209010b090f01030b06090405010e07090b0702150703090312020604031101020901090608180f0102040f0501020f0706080a0603050109050c01020c040605150c 93
    0x3c0010303140c0000c02c15180039001e00c0301d5855503949009000351490702800340903011b01680765403c2000c554072181034134114809060242c2d951100d40313200c6003489010380740c80c4003094004114603080d20707001825000c0c25200742d40c8400a640c881c4034070021802a2138a4a41c02102080005281c0d4070039000041307110005040642850051800501030781ca00b41c001c40071880c400d40030411101c1d44016014000c001c851a514680002500460942c01d00b82c02c0c102c004503000154030080ad4828610b880045801106411507043c0b0240f00948030b40f01501d041c2c0000300c42c0c0000000302181842161444c510503180c81e80b4062900700d0580f035818005110300e0b2204440250a021b1035000c0c000b1000960050f000186d46034205199455071401c0303600600c0c11588407240907101d400303000503a01c041c0c80c5a030808544070344e40d6030200005001c56420080045d42429500400c0100c0010050302e0b01600760261215400070b0340c188400c950261280d581d2000e5442004001400c00b040140b40e0401880 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 6312471 1250 6311221 6311251
    0x50303030c0d2d0b0f010e0a030b09070513020d050c09031f0e010603030e030d02070810050421030b0a1703090f0a03050d0f020d08060d02130605030d03020903010b03030301030317 79
    0x703202241c00e007443d000e509102030f482c0c0344d40c42c2142c5000000801074080c00d0a050503000900804590b00f02014000240f080846d0f40c0880c521490821240000b0301009003106100807201d002038000c3e4000703682400c080c500300400301d100781c040b28064036000d007805801099072024080b041c422014032038040c02c030a107603518448525248280250300c042c500a03150412040484010f0518001043da403480843d048440c041c8550180440c04c0d4054424034540443c0b40e0b02d540c206400c804401c0b165070440d80c100c0c0350080c480250190001c0060380412118032a0070b50382c88814035103c0011100303405841d001041104114030701107684805603500504111f82c00d070b0b00c0761760302d44c68601013003070b00d0001c1f80041c111070016660400c03041703ea5460711714080c049070070010003052000643e2080244030710010f0240c410445550392000008110080885182d0105680d0103802513108400c010300a50901c40103030451f09000007280d0499500d652560880740344905a40b215000207080903880154031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 6313721 1250 6312471 6312521
    0x3020d0f050108010b0f090c04032303040306060501030c0e0109090c0509090c070b15031203060402130611010605010804020f0105030916030501021809040b06060c070b040902090307050303030c0d 86
    0x7031103010302070a002c000015108850390300304000028115110781c411f0403a141000001d446d003d064030304903a800b40002c0741503400000b03500d0300d540f40d40b0080844e52101003000030500100c0e80004048030000c0c2c03000c0041c01d50343c50003114084034103400c20b4081203174500100301d00c0d4155031150380e00340b04a1418a0030b2511000000e9090a419504012407000101d07a10050044445444d60092004e02d8070ba0a142d80c100c01080e141d42c030418120746d5010020001480c84d440e1030301283c110046082c0c41c8241d66449000240000902c0a0400f815600c0c0610124541d40981e141e5405030b030b0024002746041c0c14600044542c3d0b8002080c181050054405888040c80c1c04401c0c40c1c081c4d48160000b507254129a1a07025101401b1030130769214060210900010a031240b600380e40002c1c0955026984110350303405c0a1030031007141d01c581485400064001000c440b02e602502d000c4c40700300c003030b1000c0d20f035101c1c20590f40e8081660050701c8400200006540c40184d0303440f40b82e05844aa09201d903034845 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 6314971 1250 6313721 6313751
    0xb03070c050a0f0605060603090c040b040e061602070603020c03030c0315030a151b1b020613140406081501060302071b0b07060c0306150e04060e040c0e0f011503020d 73
    0x208030b0200c800c00b070140807050400880c1e00480d5401201550360307900f1850544105565182c94440c01760040396204058440b607202c50f0071030507080c1460801c0300c05504007040b6600c0e0b05204040c905006005149010407010300c240225855024180010b5080d03031110001219280e102508124003525400092041e0740c5052100718070141c01a0640300c2408130f0b402003142981c500f484a480010092001d0900c04c0342c00c0300821610103000680041480c202d807001c14084c0c0720b072003c10555980c0b0b01c03c00081178031106040c0307049200d01395824413000c1e80d244143c540c4d0341c0100c6c3c1b05014030129100140b0680d4460381c00f5003001401142c146600c075181c0824200a0506904460700700880003d25a0502405000341d203a486a94502001928a050000034100403043d0b00f01d0b0420039a035004203284e5032141c1000018000c07242c844565424540f40000384402140316088100b03506d070700020145a00c4d200c95034103da110906540801443c1a0214001c1d8401c00030452242d5070b0b03160080c40081 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 6316221 1250 6314971 6314983
    0x50f15060a050f030c1203041703040b041202010e04060807030201020c030106050108010e1018050105100c0206030703020f04080102030c030601080708040b01030209090f07030302010f0f020711040e0304090c03050604050f040302070b03070c05 106
    0x46c80101841d03880c0e0602c48290318002c110010485507600400c02000105c04440c01c81d001c503500c8010250b403c459910048410382c1103454400e0740107085c05404110718201054003011603100745c080b152900c0311041450b0036907407284205400302d0100b9004000103003c001410b0740c0901e006d00d07446486d03515609040c000540c080c0c849440c0c0c035135410050045040111a03403200d410380741411501c40d0700d198005030651000a100e00101600030804200c2d00a11500760b5026200c4c2100a5459251441d05800b40d80c0046a200740000c0f04200428103107401032464902582d007080000340300380c0c296002d0003800c60340544500003c4c451203a0201088070240903e0300650b00c03a900220304003d007130845400f5601100007004200b441000003c00207120110320144041040e600400c0c0840501411411402503504c401c106a0816030103e61503641a4019841540201c42c00c1103652604140104007130402c0381e00401503401100700b4488510807101440c0c0c0929580780941e5421030700e07510f417810b00e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 6317471 1250 6316221 6316249
    0xc0a0302011508030309060106030c1110090303060b031006030b1f020a02010305150105090d08040e0c07060510060f0c0c05030703030201020301030606050d0f031103070609050f15060a050f030c 85
    0x41d5541450000100c2e041c14581c0041c41290001c500b58104800038645810040c8100340c00d151f80c50004214640c01081e441c02c1b4101c0130400e690000345240c0300301e0f0142204403403c40000b40351900c0480c0b852a0744003524050010800e209181900f00300043d030080c00207a46090307100112001e50141e42d040041d4448240495501911540c0920320014041d2040070300000d00d12141c074410b1003a0381e40c5c081c00342d0b101d45008980030401c0e0111410641864800ca40204020003640b0b41000b0183c0954402010200d00c2408108a560b4031041c01480c01c0440b4090074001400380b004149000344500c410144050140415620b00c0741d603a8002894200305a2007100075075000b000410500c50603100e890000d11007640c80704280402c131740e54103c03030b07040c000401030610002d5440003103a03040c10000c1d25000341e80702508014038941820055652200c2c81d01010a40c030800c41240b18030700d03442c40c0b824082e00028215105490914041000d441200c000180d0180300713108640d281c176502c0704500c00ca08 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 6318721 1250 6317471 6317473
    0x110304030e040e031602010c0212031207020d0e06030105090411090a0c0201060807030201080c030a0605040c11010515060313030309020312070c0e0702070306020c0c0a08010204060f080f061002030c0a0302 90
    0x107010780c1480142c810115042074560030074018030104058500da1806a03a509207000040305030b80b0700c0012640c051048019003184004203061210110f051a200d01840741038084a003852407030881203c02070100c3c4e8505400030414001004181041c2c601260810300c01c03854100d4a90390320b40490713607401c422543d0f0481181c5800081d4920768080c4611000741c4482c1d0301800a050950700041d01d2000003070300f51521820000300041102c0c03899401030000c0e003030042c028800070300c178070301c00030500800d0780f003000c82035482d00000c0340c520682e650304440c0e0010007802243c21680e460a841402489008003a014140c0703e00907180140c0d000d200290040101e80161512136906040090020340c00360041d0051002070400c1c00201a0001442011241d00410250795409416445420700c090084480e40103000c1ca83e010072011019000b8100f03030340c403640da000ca050480e810200c440960076581150007026000124425041c071032252540035100e170040f41c0c902000c9500341d520708415a0015001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 6319971 1250 6318721 6318737
    0x50a05060a110f03010b03070c050a0309060f0f02060105060c0a050601030c03060e07080604060504020d080c0607020d030209011d04110712080a1b0f02070b0c03030603060604020a0c0f020411030403 87
    0x1c0104900c11000188510180b880c109203e950415105101c18019040c090b200480014003840c814405045070580c0801901c030944120b2901a2846480e4010b640110b107624000c04100b6106940c6030180702c070540d00519140e4070b42010300c4400d030b02160071440903000d00032a0381d011030420800c0341e009510504901d003040b8030307500303042c004c0f55104030260016030001581005050000554242c005802250000f2151030f50b1000850007103050304011311209022503042221440862518420100e607020703286c056101c9135085040380f08009105000c41c020300c3c2d1208403071049100240070180c015100240c080c4000401c25440d80000310100c40c410b4480d46807400c040c2d0310480e0799400c0b04400c030080c49640c046030070129581d0068461801000141032200fa8114400c001c0e150040000c403503800d9071040524284d641326803003140d0142c06880b404020600c02d0501d0720031140f10f4440740d41c1d074800842895845078850342c1604010303640103441d500c054550741c950b03d00840c0501d03c29151401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 6321221 1250 6319971 6319981
    0xc0f01060806040203030a03050c0405040f02070302070501080603030d0504050115030807050c01170411011707020a0506060306160f091517060d020303090103020c010e03040f0f0e010602070b0306030109050a0506 93
    0x42525015041403401d40c00480c24800161000420b860b80747c04503040c0443e0310340d6200507000b00c60103543d10140c2c0c054103000346401540442c0c1d000742001c901990941d0061502c407001074030200800d440c0c09425600802a00c0d80740707002644001c1d00940310724000304801d00d60035001d1861007419003003518030845c00a94075003005820894205415401c0c2000f012042800e0741802d607156004002402034404000b01078100d82c41440b611140c0501820541d00e64240490b00a550301f1400d00101c82620070f03540400c00d545000203510381b0403402d00c80c0101d95050b440307104442c0d6442c3d0b21000e0092122a0a000c5a0445034125100241c0820f0b076802c0d80019103100c2184503840041c149502443d04400c0100c0940c8010003260410f0b02e003801e000d40e070740b96241c4525004000d08074070144503000c08035000c107076900d41000603401c032018594100f482c55203c4042442c00360007842040e02582c00807600b04200b00c83d4070081d55002a00800000d1408c0b000c2c0c43c0c03039080c4009400c0c1100c030303074000c001000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 6322471 1250 6321221 6321223
    0x603021206060a0914040303020d09060911040630140a05010903090e04020d0b071403090604050f06090d081003050109030f0210060b07150e070902071101030b010206040f080f0c0f 79
    0xf00900140f941407040021100042c44d4080c00500003904140c2c0000b81401100703850f80104204a0b0300243c1048101841c1c140303440c009481d80c041c81e1046041510000d45c1c40c1d0002c01c460041c40144a00e5048900ea603070b0b040506103802e00741210f040030400c5401040726000c0c8140f803a502c0c0118008110804a45001001c1c40d000d900402c25450300308043c480540c580c00c0c0f00148407a8030804c0e0030350700c5d03c481c4820ba4406c085140c0442d045000001044015840490030502a81c4500100c0341710b81002444651501801c49004c2580c0d48180320042640d44100c10194124081d4069021504c1c3c6907180e240c03d540c00144140c0103d001201d5005059504210b015902d06885004009850404494036427612640d50040c10307035420f0380c2044104c0f50381c030b500900c1001c401608031804541d07165005d4000e0b40000d1030541303c3c0d5416018501c115400703805a140c035404145d0207491b00d41d8450740c0300e0030250030031181074807a10418450721010340c1d0b03060300810b00d8152030402448038124817000f03d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 6323721 1250 6322471 6322489
    0x40302010b0a030b040303110f04030305130b0307050706050606041502010209010e0306160509060903010903120c0c0f0308040f021e0901050402040e0c0f0c03040605040302090a09020102031c060302120606 90
    0x1c00d02501c0c250804201251046140f40d81080e450f18000c0385071a000e40c49142c041c001c500c1da0303122030701d40010004105034200000348010903851758001c1d8007590311071710417180f07000c211a41004940d0070405040000d4580e8840790303201000900f080c0c00c4c55182c01a40c841005100b0118001d03030b600244581e515a003100f40c10380d124000700c0040c290740c50002058a449074400150606014010510800e1560382606444a038034018008100c8001541030052100c24071641718481c0918249161056910509414028507040380300c14542c54516602111404402003003560f04082c80c0c07116400580d580606002c004801c1d00300100394404034400c0224045060b44410b103c0c40c03041000f040b9440b520745000783e00900d201511515415980048105842030803001d9101c0e000020380860342d60381000c05403080e20f00039640c2c104c480e40c0e441904e20448203001c8000e40507074802e00850b20340a051254402c800c0400c1c00011855994a601107503140d0303510300030884242c01c0401007050b00d040249107 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 6324971 1250 6323721 6323741
    0x2031201090519060311040e01110c01060609090c0e0f010507060e010515010201020702130506030a050307060c030c050c1209010504080a060c0f0c030801050603060607150f060602070b0405040504021809030304030201 95
    0x421131305182d03aa90340c1d0442c1c01200400d000d15100c040c90760101c40c00394080505450381111b255034605650407494005c000d0384c0204400b0030004500410802074503c5a802c0c45052622505c444456107420041d0039035903d5845410420104036000019015000d543c03030340c80300d500c00480d060034026803509051240001c050304680c03050102d40f001d60385481c008400d0319100000014039845250103e402c046c0d651401030600d1200203007080420540c1d501140c806a1944c0c0d041000000028040310580b0910040344201e6011201002030a656103004061101c0d0504145241c0b9640395045420708840a80540f111079441c0507010046812904400b0030b44100e1034000000c000c1a540034001b4001806214003801780070000a4290315540d0071200f08541006c0f808403003420100c17017400a001940611490340d0b050007400110b4034000183c1100351a000440d00d0308050800d0240801400014010b0341e000c2d80c0781110b0300000b0b886003200c90080400c030014655910741410003034252100342d81 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 6326221 1250 6324971 6325021
    0x312020a08030105060c0102040302100c05060c090603070f090503010c02060f0703020c060403050d0902041d0706180513020706050903031b0a0905090405010902120304030308090714060a020312010905 88
    0x5640001070a2808480c10342e601107501d9034a80040160f6180203000380d801c02034222004080751140030341c2041c198400c1e02d03c00c1c0308540e1545d83c1c828081d8100c1c00b810150981012013031020030380b407a00a81e09042d05070420b180110391582d85d0000a800d4400c00340004016801120034024081100f100345a445000c600b4254980f1002c90441540c2c0c1c00001c0025082180205101d02c0282c810341040007050b80050080c0001006802102400c1307001c8280c1035514070800d980001d025004521400d0b61400800c1c0c00c800603403501c3c0a1082445500c2d00c0c11501d694200702c250001089072040b40c1c01820400000d5840f8a01034a6000313130841900d02c4490810024003941304400c0d40b154502043e14016244101d0584540c82c00f1409043c0c3d1400080d80081030100d11000400008003900031a4069a1814001e0312501c90080d2544518007541c0c03403082c0d201519400d01d0400300006c018495151040700c2c5004941d0b0b48907a0740c14002e800c1594226142d10a00c41d0740d0248203054180031010310 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 6327471 1250 6326221 6326233
    0x709060303051c020409060e0906070809060105010c140303040803060108010803131214010903020607020c04020412020f06130b04090b0405070c0204050a06030803040813081b04020d061707031202 86
    0x24070050181d0003030104080d0b121075601400d100d0312035160141c1e0000e20710014244071482c1c59580040e80b40c041140c4044d41c910032100003c1e00544601c5000f8061510400903064903400c0500442c0e000c50660b5040e51500855940c80e11000300400045110f81d002d800801d440e17062900c00100826410303405090980d009100001c18660300e842810100d840c41c43d0031300310492891030210b0407002d00140500307041d441d05a40100b4150042011071192883c0d6003910001a000300401080b400b03140203443d00500c0c1c020400700142043d0a045010300002004281080e40290b4680d80c69250303501301805c804c4005c0703000c111500e000d01070001d00070002c83e410b00c510b19000000400c0e00c1564a0040e2046031075101103882c0c0c0069600c40009150462170140d501d180ca0b040407190b81d405806c4211524040d400001514140032503100c00070f11020484265607900c2c0401c201c065041780c10f003100381640d0345100042c00d50000d05180c01e00b4840034041c0424514505050350008400404407003590411 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 6328721 1250 6327471 6327473
    0x5060d05060c090409020301020705011e06140f1816020d0302040e0f0606040b070b0f100302101202040e0403020d020f03030606040605070f050303040c030b06011d0103050901090c12030207090603 86
    0x105403980c2c81003062001d5520742500c08005400707000c0b68440a07405501c0045d0407801e100064000d948642d20b2400c203080758a144900384070481c2e0b1540b0ad0202c0c01c022040c400d81813481c08480340c204407000100782036102000c041c48440304000680e00b40d04228515602c4c071510580505c54090700d28624102141014074000074003c02100041a1024030058840001d071f49a0306d003000e0b40c0140ca035554003244c99481078074103096810000d80301d2001d42c480741d6001030340108030810f051040e01e5000c1c02a003003a0380181800c2c0d4040514044500d881d540034480420000c2000f14641d100b680a80e000300414001080c020f1709104100030484116041001001000e48171142243e044a03c60720340140d4418060420340785140c0d10300c0d4001c003540400400c0c0700501580f6a03241003603a0142520039510b0701e6840055a000c0c4148000000d0030300b800361094002e6020781c4c8040d910059400010525456995508085402c150003402c017081030302080c0c105041d0704100c102c0c0503040c0080e04210250031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 6329971 1250 6328721 6328723
    0x2010605010c0f12110102040b0a1e09030209040602040503010203070302190804031d0102010905070608070f0504050306010605030a0b1201020c010f0b03030904111b0d0f08060f060a0c0206031302010305060d05 92
    0x40083c090901e280c14800c0f440c03220300c108943d40c00c401070075008640326170b22109800c1040d8088024500000d40310001b441c0d4551101d03110b09912402c2ea22501c0c80145954284481110010001c1d5201e82d424880007485072801c1c00114840c9220b650016680c0784401c1c21451480550113910b820000c044041000090700304295025000804000c0d041070000000102c1c05400c040380c00a2841c0107000d130000da001d800c444024005c110641721003441050402c000c98907802544542ca234140e2100c001041264018001940c0002d1001c0010a10607480404508840c240301c50840e05a980010340740e50780c030b03028821110400c0003200144011941400003d5403801403401d60744c415540c40c40384d51000c400c040c0898401012030b0f0708501c1200c4a05e010180c889002480f0440464604607040000620130150640310380c000a00c0000d030b50b510402800100c0e000811700d030317003441040e80450001d80e076550055480b0766010210224940c43d80d1000500391000039240c140100e081020080001d44 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 6331221 1250 6329971 6329993
    0x905010b07021509030f0102070c0e0601050715110d0504030807030b0a060905100e03070602030702180601120b010302090406090906060e010303080a090507050a080a03020c03030c030f0304020301060515070302010605010c 97
    0x81030940c0e071500e03100c1031300c0024100030b041450441150300c001003200801462099280031184000c0300054117580354401921303148540680140265000c40c0c104200c1c41c05540300d99001c4008041a0b400c11805813402022202c01b60340aa02050410782000503445e410300071a40000000d803034014445d49882000340c41f1040501540340b0802d0b0807000d08500c5481403181c0c80740e01100038110761003d5618040a901d0f90f120b0f804c240d029081c46000c2c0a0b194110011281c020f500c181d403900c191001d0134a00380010204143c0c2c807410103400700089902e0703694500540b006840200000102490b0614201c0200c40340c50344445d1016441900400120f90441d10742d987c01034280401007450000c0d40f80007800c05100360411940103420b500d01194050300001e8800c2c0c160321076001c80b400841c0c0c8508041c0e07a40950740c1d6010031903004110038204440d00a014640040c0f0140000c540315454100040c040311904940c09600300010400c4070605509004450060000b0b0074048200703110b0b81c685140740c02d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 6332471 1250 6331221 6331249
    0x510020d12020c07030c030b0c0306010e0d0c0306020f040f05030601050609060706060f0b03180f07050d030e030a030c051006051e01020f010c0203040501180b040e060a150206010905010b0702 84
    0x681c03521800d03000c0559011034820b00e503001c09443c0710584074504407003007007100e000a5411403070050001c3e441d05a80011240143c205840303040345051a0010401010000442254040003182c40040082c6040c0054060680b20b585c041c0c1d2034609100540260141d0740c0e0002d4400c3d41301000400417a00c80c0401c55024160507a030080e80c800720350610b070000c1d00c510b90200c414180488000298017a44101450061000032407030401031521044495564607030045c8440a03400c101c80800c2203141952080e22810b220341406420142180c00090405401c800c003940410741d000b000a041010074404440125140300d8200200c5050901240490001c020030486840e0000303a01c21103a03000b00521441e21128400901c503040c980c96009490350458131603580410209225007104e5010900820113445d1640451402e107854400c162183c030340090710f01138001c1d040708000315540720b0314103c00c210341e1004d4005213402c0d403508600c2001c642059009058090702842100c0040c2e682c401e000001ea = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 6333721 1250 6332471 6332477
    0x30f04060302160f050c09150f0405180105010f0f0e010b0a0507030516060f050c09060304060b0103060305070602150a0606020c0906010201061710050703090c030f030e040504060e070510020d 84
    0x900b001c03900ca0341c648540500040c0c041041c0384c0c041d800308200010f1003060b5a5040d54400203079111401d00d8400c2c5903110622031340c4200413010314210707814143c3c00b06031f102610304401c0c8130885184c81c0716404c4030700a030000080c01a207442c1c18407000901d0500000140a004003e10041d03150044006c0d131405034612900c00c2080000381a0f081c5403044050700c500c8558020f103401c40d42c1d00c0d80b409100800d65007a040d90340740d080c400010041c00d901e1096900d041e501420300d51956179269035100007800700d00a00381c18103641c4d4202001294042000d0009045640c00820880144028025100700d000780071082f81800e10200f80315040c1e02092803502150305880321030054aa1f440140c2c00341000d500001c0914010181540164000040300c580404411f1020402034854a0046003a2100d600c0d025100b44480034041002405060130007030300c07038001d180c004038022500c000141500c0bc10380303055a0083e151240f00e201c01200b03000c143e00800040b0f801108106840703001039280c125803410380041c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 6334971 1250 6333721 6333727
    0x70503061503010608060102010609020c100906020c0703031101050609070e0105030711060a090c0e0621030906031005040516090b0a031806050702070617010b0304083603030f04060302 81
    0x466120220031907408030340e031990240c0301d68446600a01207081100c1d05401913003001400520846d89100701c554a440c104040c0c2103400c00000d4080180c801e03060700b10385899080044a00b180f1003880014042c40c4280e50308020305680030001820b49802400b511302c00d01410301805001900705922890401c020b0810781d89958034420162004061001c00391513a02a003400c205c0c034502d440d80f004440034402c4606d001090381701c4000401020084034001e80200c0d88a480c098555680d4030351560160b215000c880c505107d007130108009400c152882c14296804242c207004a03d8030f03004155018108507182c040341c00030030100415107034541c840e80700f25400008030034000c1442504606088418a0202030312a8404e140c600018030382207400700d0050081c8900814120f12036441003001213003ea00e5148143d00709144030120340e102420480e5030324010405085040d03200015400e045003494a00318034038000301029031a01e404000804d00c240c000b04103500702c0c0030420085c0e4082da0760510340141c03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 6336221 1250 6334971 6334981
    0x60609040303020c0d0207080f060603030d0e0f01020f03010f0501020c010206070f0c0503030c030109050c041505090406030b0907031205090901030609030e1504061202090d0609062d0506030303010608070503 91
    0x240b040c2d90410030305018903a0f1205c0c400380c00007064001c075001c4c20221144040c0321040c564441100342c6800394940c00400482200103940c0d00904810f11841d0140c030780051580c0d03445800c980c00421041940140400100464a5840f105100903c000e00140203240c030440d0000f03494160040c07061090010800c80854035034402d00340c05c4041c07a40201202d5890031b058200314540d420034442e040c0360030305200c00030f28180203090a5070b085902d044e080c4e001071000d101c8c1c00d94140d0849079030540c006a4506001020552000d4400d0280c9080800340c02c640303055090954080100b0451300013440010050131000e611140c2034a41140c0c0c001c0c1c07000031300b0700307492a080701d00d8900280d51541c042112200c10b6108d0709002c0c0104100e99441d1134000b00110302e02803103001d90060070780240c0d02000031103418010520729001852540d21507040011a55070803440c0c0704034150130b280c4165075100b40038040ca81c110b03c02c1c410590081c0c000c80c015811580b500f40014502d060080c4803400b00300010001c25 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 6337471 1250 6336221 6336227
    0x909030703200106120b130503031801021204031101060f050d020f0307090516020c030d050712020c100309050c0603040807080c01090c0e060319080a0e0a05030708010b0111010506030606090403 85
    0x400b842400e407009000c65550b40303482d9016600412020386c0c40c0010100410070071404d000b0140c41d416406030140d030a5a0f00c000c1e682061190f0380c0ca40e00900d54082209600074034050f00c446124070700c0380d19a040350005c5035480c1c80c210740040d04450035020240d40c040c01596160716101c6650b0364110b5400721044003c038040b9040001540c00160850308207400d0100c00d01481400c50345a2140c8c1c0c0c2291030091b00d036810123a071180303891041008180c04204800100d003604003040b41400c01401241c1a083c40c41e004200362a4440c0e001000007907482e0030b80e20070000e042c44110300c030700e10071215103040d030501e9205e161140c4144c000003044890000740c50900f01200f9000746074140d400810301540f07103948a184600035802101c9003882030040c8042e12600c42e0f0100311014149410440c014200800c0e0030302031304c118582c02280b80d48031a00100000d0965030800006003e03022010020800202240005d000c80503a200181820390520041011580340007880c260701400c02c5900c08415146d45c2019 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 6338721 1250 6337471 6337517
    0x20705010b06031810050601170703090f05011b020109080a05070c0b030c0909060102030712030506010203130b090103050108030a0c020d03030209030105070903020906030307020f0d020a080d020d09050909030703 93
    0x125006030012080150540b00700001004006003003064941d071240e044141700848104903141408903091041010b941b1018200c01603015103070781070008045525841c1d039020368009000403941030b91241c2024042c03101e40040715840c1641c600003448805029960f1074414000d42d0741c00010001c011aa44c001d0088101440c030007804000140e540e0390038249032500c203036032101e107003a40500c0c00c500101e1f811307520000494036503d030041c04500c82d40281400442c05808054500f40c1113200500c00032041030340d0700310168014103041f81d0490365400f07000d00150558905904c480030365001441011642a00800c2c4450820ba048a0409902d8036034036047e0000d004120820360150701c3c2200f00040c00c2c2c1c221445074207881c000c035060042999040c0405a580c441c84000941004020ba9003560904101804603221440100320101084d2204519840d00c0c4200a1160043c0d01803030000301c1f1642c01030301d200c02504059444500c00c1c036200f410950b5a2141f04001810811348180d0020154094001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 6339971 1250 6338721 6338741
    0x30a0209040c15050904060f0b12070e04021206030c010c0305030a0e030d14070215011d150d0c06090501020d091503060e01120308090102040f030b04030203160c030b0901150902070501 81
    0xf241c0e140400b0481c0106941c0121a1080c02107107000c6004c619880c1c0d04d00300070201c40c5500c5820385000003541c0c01d02c80c10000584024140106801d01c10781a0f6100d0000e0100450101800401c5251007002c051a0402d8900c440781482101422480440e038400102c83c4e000e030070400c0128070120100d030003919511038500c4000d0258a0503208030b400452800e141d5020300c0072a800c0321009443e0341528000424203128000824034095003082500e003000c0109030740304041c00c102c0035105922002040148a1a410484080d03108041c10310a098103c0c6940c80a40400c4c4000c0030300c1d51810002410038020340c02503c0d89e403090045d10000d550301c01c0e0031440241441461070406035944404070318446081c80e6045004c240800c2c0021410b100502c00d4030110780480e141024500d1031a212440c44540c0a4410740c1140000c1051241c00c40800e0005222203204440a0317100b02d1440c00c0403034902c13001070800802a414409200b15890381c06013002c0070b8683c07031a4010b03036445003850018018011030302 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 6341221 1250 6339971 6339989
    0xc0507030c0303030203070e090c0a0c020109260f0105040503030403030b03100c0f0909110702060a140c031809090a030e0307030605010909170c03030705090d021f0914030a0209040c 80
    0x1004410544d054010f140039048640356a1903a800100412007114000c403161056100107000011000d032240c1d00300002a4010f04083c441e2589400d000c02000d0a105030069003000042c10029200d0b20402240f4804642903008000742c0c03e050b40c50b01e80740d200140021302010303114010882c2c1e940c0c003800708005501440900b088006284400509070482c7c3d8181c01001ca072a40358005504441401080c810144a5101034030b015107a500b009096002000000e08106005035120560555400104016043c40f0f00654480c13082da40511812004c00e10028010f200200034011503210000f00c180c0000c1d45070800501ca1a203803400300b407509003a41c0c0058003203070400d400081d07458515800503c1e664000d44c80c00340031640007440821a0700c150b08484045a10070400144030798407400250000c4840240080201c0c915600022101c000b041c0d4030001d880f00c803150400c006600001d08c0c1c4000c0c0070521054840c0311051001a494104804010780034542c140001420010b01d18540005440b01071 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 6342471 1250 6341221 6341243
    0x402070303090c0f0503060a020a050702060d06090609060503030a0f030b0d0308040515040c1205070902070602090f04060b07170405030613060e060105090105040b01020f010c03021309050f06010c050703 89
    0x3080003409403031040301c20b540306030b514040401c0c10720002d861081552030140041006e52658040a0000c1d84203031074074010017070103124020041c0c1d15840101668548407202181c0203042c450f10004841140e17004031b0001e81380c40742c1003020761004030640300700182e241810b9020225082003500a40441140603034084000d1012804054000718084c4c000d50161088901d10040781046095105050314041c10f0500307540c0c2e0410480e5001102c808101d8440d02c00d03569465a81d4044a040c1e80000004070340c150f0300070900f03103906c1c100454071801c940e00858050081c40c0c9805101c001c0d80c80f5415000e0040322186110b81002c280c9403045034000c1501078110740d8545411404d524075078440100845585040c0000c0c07070500800041d08a061300c2c002020404143d19003c10400207041c031500180c1580500440c54240d12028460047e280030f031520702699416254441b00c02035445900003400c054034200510848140c5500c2d6181d0000b400c2c20700ba8002e07052030410034074052a0754001856192070b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 6343721 1250 6342471 6342473
    0xa050405090f1203060307050913081b0c0102070302060405060a0e06040e06010f0e010206070507050a12110c03070b0703030b0a0306020c030a09150c0201050a03140a020a1b0312090201030209040207 87
    0x91141d104800302c4151069914034180b900c0c000c2c03205444050b0f150303101c0d080510070303890110740c00340c2c0107114003200040c3c15090740c2d102c4007141c1042c03003107079408000384481d81103041051002501c450400d10180003150f09550000d860f40c041c5010b124050030700400d010380d4803030044110b100300c10402000c0701e4940e55501d100c2898040100c919900044050580306107581c011201c03039580040507000b0b00000d81c2d8004080b031b21604850b2060350075100f03400401000c900322120340d507412041d45d5640d4082071445d0202610344284280824002d60064808010740d01c0e050060364042d030350602e004103889042900203123130f14816400c040e05c00da1000a140384c1d00701c000002011220701d99124141040c5e515948404001d4030300c01e003040410200c0d103501c001036120303000a107810001c60500051248001c81c80d0044000c08840b081942540001c0808403960400b09100f0f0340d1240e4403102e0210103240ea002801c50411074450b0b040340d82c4038989841168025010b941500758040c0045440b0041 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 6344971 1250 6343721 6343723
    0xf020c0a030e09011a030408070210030501060915090506030903040509010b1812030d0e03040f030b0901050a0b01050406050901090905071e1b03050705070b040b0c010b01080105010e040504020a05040509 89
    0x203424114041090b19698088074145501d08038100e541c81c2c2d01011000c101c54000c010180d00040c8101c07503ca008000c010011f03510550b140108600c01c2da00001c1543c14240083c22000c060b422088100155a01c0b041c4925405050300c8161801500d0068594980c001d03050b155002c1c1d41c003d1603103c50780c40008500600c900000d41110f110401d11111070a03403010902120100306100c4084541080100c424450900d40190130658001011249050341d260401210304407580c00444406030032000b446454207090040c1034101100880800040d540b150010704030388203a01c0b4800c06d0100219040381243e00881c55840141103d11040c02185009040100240b18074503410003140340c070554182000d8032450702c810b4007402c80200340740d82098540b02642c582c2c000b000111546d01c00c0c1c50000c259144100082d000810342c6150310798488480003044c1c0d003034031502061340d4100040200100000e80c0c3c00400038482100079500000e840d240c900200d940d00040e600704030341041c100000c0c4006018 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 6346221 1250 6344971 6344983
    0x5031b030309010501060302070b0708250e030f010b0d021002030c010606030914070501080a0905070f062105041203050c090406060f0f0203070804030b07021c0503010f05010203120c0d0f020c 84
    0x1d00c0d02e008000580e2207800c183d089004809000c2c04040c11000000d140038014010160056007000c40354040d480f19408540364020b003019008000707210401d1415490404014840c5150444d800a00c40c55080c00301041140c0390417880a03209444d0002d205060714000d00c00c4440043e0054004d00000e511134030083d010307000150040f00c4100300f121618181440125010040c0c9405039100030083d1a40d4011034003074983c518050311680102000025008085a00c580051509803a07200700035054898440d6651000b0410341c11460034030007048009611382c040b0101c0c0400500b8006140e44510030101c10710f02030004e040750843c0c6040d90209909820002402008039070313650b1100c2c2c500400c50304907180c2c01402d10051226506010600000300301e0031805034002e41c1441200c13a0085401c00300d01c62240007190764804a0700000c01030120592018001000c0c0100b8002903103011002c154500c82d00000a04104145d4000b0500c01d003220b085400c003005050000e41e0654031400c0c5004081d4441c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 6347471 1250 6346221 6346231
    0x80108061614031312210203100906140414090703033b1207050607081e0304030918050402010203030a09031e020609010b0d020d0f020d020a030f03090603020315010c05031b0303 78
    0x1412034600c09a01c5032091083d440c4035010701640e00300d80c0d03a179006c91700c0181d00040c103086e408009100700400d50300124490040141492041000f4145540d0b003030204035900c000c80b2480743c001f404200400c2000014201c07086a034146031800d0041000007503000b04104403403c0030807100e06000741541c59442c07106052040a804c40c0d05080900c0c0d150542239441600d8420319030840000e1000f04081800a0043e000200b83ca444524400421201d4040c4030380c81180c1c02c0340445e0801d1818440e0303181c59840900030781c2111600308410700b0127400107940ca0100a1240c00b0803903c0d0071200040610920700f4403102042403030301009101c0c410364082e4690307200b1999482b0b550f1800390954074510300b401c0986000c0d03801403c4a894691103454140c03851300d0050b000c0e40c001c40003004280040c1c03151240c10000718000c1e20a40000e110619004040c0511070b88403104250050090101425645515800c4014242000c0800700b00c40c2c42d0007421401034178545a030701740b49580c840d0303840e05c00800114869 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 6348721 1250 6347471 6347483
    0x40501050609090601080d0c1b0e040516030201090513060305010e10050603060403050301031b0e0403090303030e06010b0405040e0c0603070306030c0f0b040902030a091709010905010801080616140313 88
    0x2662582c402135035943d000d100f5a1349030342c0800c0f19504507034003822003141c40b80d0050071003a030721503c8450012800c1c0080c1e0b1264161151520400c424040709104480982e4881080340c0c42152441e0002410b40350203009041c071401c89001d00401d4201e00754411001503038404003c0c0540f940801826444803c140c2303040c1411401c000020350189004505280702d40c1e4180c0b203060a590a588500b40109900e9448048403076141c180801c4a90111035803510540c82543c1c6d5510346400d51030014140d880440008005920010060110801c240141c4d81590750659001804504000a062a1000e40708000b90000f2000091060565041e0040401d40e0b00925912811503901c075603010070440141b1a129418500340801e10042e038a980045400c588900404070700c1410340d45540c8030006540000005c011000540b12102d546c00040300300082909007010500380d890311510a44400008001218804501c110210054018428521041c0113601700070307181d240c0391603c900c036a5a0075200365a1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 6349971 1250 6348721 6348739
    0x203070e04050f010308090a081c120507020a03030b0307030605100e06030303010e0a181202010603060e010e0307060203040f0c0906060207050f030307020904030e0301020a031b0207050105070809010e06030405010506 95
    0x45041c28066240a0f0051a02420140e80383d515050907a42050346450b501a2500f000000c00321010408104120520000c144181c2c44000b0090b20b0000240b0132a80082e040c9004c01c0035080d0081380d05a1310a130541008a0113002d01720002c0d00f0306500d908010400c03841d10060129011000070740c0002c1c0d510700f04c44c0b5a0b480e25000c0416544c1e00003445030382100d1074882c0025881120350b40080c17200840c1d0402c0780b04a07001c1030340e902c49aa8514a080d800513903503400304006100b81401000369440e4080005c01030790048415150f1244501b01c405025035800001203400c118448403a00d25241e041401010001d4642c8800800b9280e20b100340e0f4010700c644000443c081c5050741d182102844000c0c011854020b03d40c2c203001015500030010750920410001001d070b181c800b800100f00c50325190350300188000081d52a03c030340f000f04100c0401158072034581480a660400b0813103075a960440b0000352140785140c0100c841c4130340c1c01d90703680c3c01507404024002005070540110b40110300859207584 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 6351221 1250 6349971 6349997
    0x303090708011415060708041d06010e01020a030c050309040207030f02101401140a0b0c010207061d07180902040609050402041d0606100201020903060108060105090a020a02030306060c0a0b0a020307 87
    0x420f0b0386401c950600e0954046000c10141a0f001980f0324091101900981c14102c0b16100e0b00e00f213412940c130400740800c201d00750002e800e042c002e0444e4045000d080810500880705e000030b60340c6041100041c1030101c000d80c10420f0040800540e910351034018815075485a081c64020011813020903418090310818540d00110700c0580185503c0c6191921042c1c078607071a00d480000d580b06000030113900b001180b80082403030401d0000074110f03411040000759481d842d92a1000c00c540c081781c0654000c0280c00c01c000c000d5407002c28141d0440b0407407942003401059044c41d643c024250341400961040c41c0000020b40c10190750040c601c9a80211010015a101c0ca00100c0211800d01895012a00014002840d61a00321010240e40046100050411001c000031a281900c00e80141c13000d640000300411a529100100942c0650340e00c0040d070074805c42c0031000c0d580340005014a40b0542012507445181d110800a601c2080d07000f241401c1c0718200340861a009501c00c2d00c55000207400234034410 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 6352471 1250 6351221 6351223
    0x306010e01020f0d1e050c0c0f040f09060b150405030c0909120409060905010e060d060e010204030804080109020f010203130e06010c1211010b0a050303030a0504080f040e0105040f0e0c19080706020303090708 91
    0x1d80328003d00d805840d544100c00208803189d82e140c10407551081e41c81c5008020205603105004120f4464100011180701d100c08014090f4000700b0203450310070040206010310384005c1540b110003401905c0b01c05050301e403041e10604280c1003246003032014030b001c0f800250b140c4940d0045011100140c10030071199803241440f0303545d02e004803042904000f03000c4501000a1031503001d6940c52078500001402c0c291650b42d5103007603034444d44c4046c0050391900a20030541c5800007003061000000d0005518120780d005444408540a120b0000c010152000140c5c0300d0740070712a50302c4ca280d400f0410b413013005440d003405406034903a030030a2445503181800c800c01c02d05000c240d00c811b83c0c3c0024000c5003140d40306e82121014040043c0304480e00c290a12006c0d0085418a010300081c117115124005d1035810301003030201700ca0301142e509080c41d0401010260ba96004200f403c00350b00f081d01c48003c0d0640355540c8084600943d0b000c0b55680c4a207940009001e07502001031805640602e090b110703001c1c0c2d04c2081c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 6353721 1250 6352471 6352477
    0xc0316020a09050702030901110c060d060302040f020301030b0109090204020d0c02030706050c090a090f020403140303041506030b0a0902010309050304171c1403070215040b06120604080306010e01020f0d1e05 91
    0x40302580c0304001f1807032158002c1500c00d01e640c203030703404903164640c146020911b160810309401403119201c51302441149002d0007000010a140b4100b1420b562458075001c09002040c031442840c6641d9112200640d01c46070105c1e001210b1295040c800a001050025529408120705650151601c0c011a0035440300004642801200901c0a002203040824490081c0710a035880c0314802c0c2d003000700000240340307182b000b20900f503042c029540340c1c40c040c1403084c013100584042c070710350920701202400012408140503030401c1c0d2800e000100310003d4801a4000c064240d80500301d03202c049000500c5108a800e0340d5900f40042d000c1d03510740c0811034000c1501e0f080b09181070000c2030f0a1140c0c0d42d03881c925440915844141841214005034410600d000301c88015101914201c1401c0100000c0d820b04100340001e105e01e150041c03081d450242c50307240841c0405800541003180c5591548041ea02c04c0291606c0d0703502a406032030850061301070292404000f0084590000c00d5242e2140380c1038081c4050f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 6354971 1250 6353721 6353731
    0x1030c0513060303050a050c1509030a08090a08070809031e010b0a050f060405010c080409020403030203030f011d06010503060d0611070b0601090807050603040309080d0206060f0d0c1205030c0316020a0905 90
    0x5e050404540c072906440c80c1e0000e030f416403600d10500c1001415044040190b40c054418080515030341e40000030024444c0704001c00c42800707503120281c0200090203120880e02c0d55900008030b81c0e01c54001d040040e0501c861128010036a203541c54001d02141c2c07040d0302065210078201d5100740c109581d01c0600102e0940b8402c0d0f66804081807004201a5000d208000402446403203041d1400b62202081c1049800c20307082a07005a00100c2088024005a00d4182c05804455104025011460740c103175542c2c900180094100130000c4086403ca0b20707804040c410240e4082c1c818000341c40300004100d040d41182074195a414213200100d12954003901c101402d842c11400640422030500040c00708a50014004034200150400001076034031084c03040614256071075014015034101441088401c010703002a0520074400d440000e0001030500700d0395400c07156414000303562100c2c2400c0007030943c000c00e001c2e000d50303000000d2405800003540c00c821006902c01c0360780d510380b180c80356030280444400f00e42c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 6356221 1250 6354971 6354977
    0x606110a020a031103010603020d0b0103030201050f01030f031107080a050c1e0d0602090d0b1303120507050a0806030a0501020703050a2604140c041506020f0606010801120609080301030c0513060303 87
    0x82d05001003844102e424103943ca001d030001c102540d6a5011480070b10000c4d1059406a801500510070513078203020b91a0061880902d880c040e50550f15951901000e5107030003018005080c2501002c54000d101403c000d00e001801e40c1d26484030350030060345500501107410b1181800620542d000710705c109151140e000c000d04403401440361540c1d19030082d480071034030507400a00c440d401d0002542489800e07110741c0c181c1c284d82003020703003c0ca006003406250702c19002000e8108020003882e036a2001c16039070240c3c0c00c0c0c074040645072076075000709007030000c10840030700b055000090040c1810b0f0003200401d000003007543c518070241c082203409154500111400c00407064148003140200d1505c00310101c112515106603100c0303a91140000701203a500011248a041c41a4402c0105503014440b4190800805010340028a00a00020000c200500940000c4095803c07401c052011590044022079032007030100c1d680e035031a8140340c040e2000c148225407081ca0b0491200c40783c0922402a4021294941c0b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 6357471 1250 6356221 6356239
    0x50d0c17010908160201080702010506011b08070203070b1207030207080a0c0201030e010501060809010c08010518090703120302131706010b030901020702060304060e0c0909030f0307050f0c010606110a02 89
    0x3040c034840304022688102664035406114041120000141101588807981d40f0082e03501d07200160003840e004005209691511341040071690b00a21306124894143c07828210035602d500e0243c4482c0900380019406105616010400d030380c000e07005251500c0e10513a82c564075900c44034206e00740c0c03091090040010070240200310210340148102d2034410320504002c01d030850003030350150858801340c0c400000681c002c03003030042045080c85650441802c52074030040303a41c1002c01007480724262420b001c0c40307207401d400001c010540600c402c00c082c603884000f4550000c4207000c000c020390007003c40314604000c071660004582e17404115942c1c081d000b48000d408183e20342200340c9166040209090394954082008000503a80d8200a40c451845000300140154001c110340b482e000325100d1071030140e00044244000c1000000032380d10074400d1140542c2d543d5a400004945901489103d0100031074042500400400190804d005072072880e548ca050015441c0100c694460820070085c0d0090462 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 6358721 1250 6357471 6357479
    0x41a041a0c030d1505041401030b07030902060403080d0213030b0118050915040501020f0403060f06090204050102190303020d0504050303070305070201060b0901050903070e0c120a090b0c03040c03080a090609050d0c 94
    0x140d00300344100b08201c2101e03d0300c030f17a0301e2010070142c560801c401d0110900c158010310801110342e00c1990070504510b0b0030004208640d0100d0b00300c2c800c03404050708180021480002e00070194040320003144020700442d0005582e440d051125010a004013424401e00400360b143c1e01006101c1c042c82030b0b8400c0010076800080d40a040721000e409002603500c0d540810541d000783c180c80c0c00400c01540f0803500050384c6c0d00780c84900b0080380d4550700b00340212401080204a56a8000344c1c5000094140040301d98031541860103030001d110720022000081d0428080000384200440a58481c261380d0314240500d5403040070407800c1780c03034901543c070000b507080c000d03412154803036405440b54070809021149001d0300c1700b807041c80030780084441082d40c03a80040c000ca03103440c03c508460f411800116080c0049171040d510081c0f2280001c1448028503000300000d030921004144000046420488e0316035603506070300009112100c680201c0d030111382039240010341d900300781808100f40741d00b020003c41d5130303410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 6359971 1250 6358721 6358747
    0x50a1a16030903140301061d10020703031b0f111003062402010f050108030304170304050c04020313020a09050601020106080c0a0b0309030c0d05040e0703051308030606041a041a0c03 80
    0x41c0d660181c0030070851000c8211303101200c800440c013a101076143c041c060840d04035a5003011074000103050103111100705030381d4060b800180c50387c140d83e414100404104060011040d80c045c0780340c00035080031481940c1a0a111000e54130340c41c4480b0a031011010321050710341c149d098507000d1240034030426032020f4511208408a80403112210b01e0b03c004500c05004c18032810a1301e2080e0800754041d00004107100030022500303203c0c080c50f21651390244c11442c2c2a140d0949480b03903400b0581c01f8a40000000381d00e0801c0503818210b0a900602004000c0d84a083c000010241110707458055840c0c1074011652070700020300c00d0800003008256500e01400c2910075002c641014040400c24802808490510f0000f80164044120144e40d090b0310b4a00c1c1403401c100040014000ac411b15113000d007440507240b006041c8100854209142d00d0b50f9844503400304031288101d80c021140080c588440240c0394a003403000f0021101c01803020591444010042020f0f0b02c0f5801c3c0000b0075170f10412030074514803d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 6361221 1250 6359971 6359981
    0x4060c030209090a0c05070209100618031104090c1706040c170303040809061608031f060804020d0c080102130311040501060203070b060f0904030c05010e030f0405040b04020403060207050a1a1603 86
    0x1202c3e01d00355042c2001f6a021030280141941e04070102c2582c450148041c603800786000f405000c80b040b825107007500d03644501d1450559003920764003a030b464004581c103004034041007000401040700d2903013120400180c0320341c03102802e541c2128105155080022211030845119081d40c1c0404051752a6403501e40d9400c103294040c90055401078028046045086200c40311890050700410495542c1e00e88015103120108003000046694582c1c00b40511031144d02c07030001584541d05650305003400907141401c2d014484241d02c0440b41e50b00014200884011883c030752000c882c070480e42c0318500105282003100b80c2d002405030000580c418008040131030661420682c00400103004406c082a0000c04030fa15054110b601754080360a0560074410131100348980034820203a00069401c00310f403100e00c00303030a20852044ca84900d0303e40c0500e50081d9119030440d00119441101156220303858600151640500e49d416144c0c0580584402d500e09144040c0131701c51445c0000d05411000c3c01042540104 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 6362471 1250 6361221 6361241
    0x20c010b0415140d0501060b040e07080f06060c10020408010606030b041a01081906060804051614040f02040e01080a0b010e060a0902030c09121c0903080a0e01021606030504060c030209090a 83
    0xc8400c0003800124038280700c2d1f5405081200b500968840c14107800600c803101c040c0c04401046140402c01191814512909422403001c40b0099074900000121502d01121800c800e007580340b00150000345240d0561181c0c04888203500c0600c0300300740090421084869092110400748107409a81070380d076200d81001d40e807103042100000307110700143c02c2c00021941342d41c000c0d0780480d44000c14041401420040c03d07916100b1840011001c2e0706120015540e100700e21806802540c540d00400007451043c3c054901a1101541c203042569440c01e2065840b8405c41050b10695000d0002040c5000d01d21612031140c400907002040382880c165044000394001480d0380f00400052000c3c503071a1b42c031146002088142d000c02013103c88a140c076100e561030f600842540500c02e07841400c0000a500c0000c5c0c8070030307845604242e10302c841d4900050f801c0011900c01411800070307065001c50140c2c0c2541c00180510f01032801008894803a1101760102d114000c01c0c5548941140d000030080b50194108800103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 6363721 1250 6362471 6362479
    0x5030318040902010c060f09030e0603091509070305060f0105091807050f06040302220b03030405030c040b010905030303010603090507150210050c0f0c070e0a050f0103061104050a030501020c010b041514 89
    0x24928503140c1d04212100390380c0719070007d51290480ca0525900606110010b2012904941366061054099554444000c042000042441c0020341c101400b403004c1d02c0110f030010162604c61900a543c1d0748800801d0040510490341c0c100411012060a0071526000e9800c40041c0345d5141000100840a4095040d140d4040401c00010006840b01011200a901c01206030000e0b1551030840005441818a20724002c0e481440100aa69000a1591161842a14002103048034034004907508141ea0b00216018800000000b44d41c59044d88102e190a01900954801c6510792a0741040e0141c0120a800140d028601c48250200076911158021480302452032811181b020442c5850b00704140d981c6580c0c201c1403041002070340107040d080e030207074040030304100a1030441d030b00800580041c040900710582c3c0f5410070340756141000031a006000024800c1d80c0445d92468818080d602100c2c50032125402c20340c4440e83c501301030140007026043c5041e40c17036502d4140b01602150b607406241007640 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 6364971 1250 6363721 6363737
    0x504020307030b0415020f030402040b100e04020904090204020301030302100e070605030f09010b0406080a05100203041a1003021806010e01080708010b090d081b070f030803070e060702030105070201150503031804090201 96
    0xc0141900c01400012200c0821036140c2c41e00d801003004450420000301c2c0503410de42c131964142c641c44001c44c2c200e10f004541c01a01c030260500410010031098200039007051000001006050f0009614900d001400310240400c1d08a000919242c00f15885480302007502440410389188010300e8085d4004906800000e20360b669000003002c0c1e801c40d6000a540ea0131841c055000d0010500000480e40c0140324150710350b04040e550385002c1180c1c1c8640202d400f9000001c03414046100c2a0000150f03001440c001c000e0b00304854214030340e801500c50502194036440e00c07a580d9400350306140e200f14082e80325800160300c1d10314069015441446055030108003922444009004031014008a160541e0002640e1818108840ca010010707003110102c0100d44404000094000044941c08030162030410b80ca40214000720380c00b030142c814000e5040d4201000c10031955030540c07262445102d0482c010541640c1d0300281502d07489000c025020f010502d0708483c005003001e402841e500da00c18900400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 6366221 1250 6364971 6365003
    0x50409060209030a08090301060602160603090305070b07050918070e0402180603090304030b0106090f030303230901090b070c020d020409030507050303070801050405060a050310110c0a150e010504020307030b04 92
    0x81044c0190b0411591200041120030326810240300e03107009061680000c00102a00c00d004c0401c030807051190f2010962101d080400301031240381036a407440c1c2e0217a0560b0840c10201e00180041d003010450038026103500740341540500010800c2401403010391101820000b0850600c0080c0d8450b50b44181d140040c84400c20158450078001c41c400c400c01800b5540722030451600301110041a0300c004104403270b0721000d0121418a0038050201d0741c0c1403c00103510b581d144030b00300031055a0f19100b00300b2050001040310015064000030829440b5864248042da074074441940e000c041da21000c2d401c40c0300201484018209a404401c3d40780c00707420305909081884e580c0d285164004c869203800184c0d01e600401030307801c0a018194022004588a440807414400403036a07529642031603890140d11200c0e100f21a400700011124906005000c0d218240424100350b010416814140510540303410810071080c141071040c036015603401800f81040303901d10345809851140c042d205568000101040d08 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 6367471 1250 6366221 6366223
    0x30f0403080408250c080106180e01060b0a020f0d03060617060402040503031306020106060c03050a030203060a05100c0b010e040c060507060b0307120201020607111207060e070e0f010b0405010905040906020903 92
    0x183e0004244e0180030301003141e440e01d48a00d01846d88400d13256810280c0c18000301d86290b12100445000e00000260944000040c6024012035030003503030340c480d0000c0c103914095070210740c103100300120303008844014405203c1102100c07005d204480000740d5015160520301010502a500014010400742c2010384800002e42191b006404c2410480303203c9408011003502809458000d00d21400c050800c010152005000361003803800f02c00400d0360000c0090f009030350b0290048080d25000d40204560349120801401c04034200006680f6010910000540410243c280510a69000188190091910030155001d412034070b001c403140380d20b40105020380c1c0c40402c5a240104020481442400b00a000182c00c00c030b00903000c501000f5416481d03501202000a03003910040d00c12204c90344d070784950b08020000f44030f02194158280900d00c40043c0408414000303c0c051000d00001030b240d0f90f618140300206209030320546011800f581310401031442c1c280c2c0040380303031401020054074080100b000a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 6368721 1250 6367471 6367507
    0x111b060403060f200a050f031e0a0f060503010203090a02100c0803090106060e0301050601090501110304170601080c0111060708070e03010905010603030311090108160207030b070804051002030f0403080408 90
    0x184100c0c544c1e804008080e042e900d2080c4001c5040812140d1510103013440042c407500c150001819010000004160a07090289281c058900507042124080c02d182d100c0300c0240030407165095403070f8101031011441d89010320032640141c03510001030121030b46c070341c2c00d20500b00c8850b16284280401e0001e00004180c0c10002503104401800000030030070708283c3c000d4200c501c201e143d0784c0240e140004004d1982d820940c1401039070001d0900e10702d818150381101d4178501c20340d00000c1c1c8500300008440c10602000401074180e61501050342d08a00381600111503001d88050440203d600410100d2205070082c058950494800d18010354030302201d801081c00d60700179900c00c480c02d1399904c0b410424103a0500c0303003211a11500400c1807501003141d00007441c1d107101a141c0343e001c0c05115148a0498000c201080042d036001d40200010f240c044409400100c00712410b46a07030095400e01100c0000c1c078070850b071141700021f207500c6180d100c0740c80c00c0b9107040340180110f40301403040201803403902c40d640d15 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 6369971 1250 6368721 6368741
    0x60406020901090e06010e09090c030a140c01020d05070b06190303020c03060601090f14030109020406080d0809070f2105060109021b0c0d0803090319051207111b06040306 75
    0x15a880c105100010f0001d02c45600103004034a07804203100c141d03a400f010496240703070304075048082038031002004d908001d820584039500d440341104000401c030000e030340350705480c0c42841621403c4085800590311020406040d8000a004010760b10008a140650f5500118090303c0b44901c2c1384414000069501d0307540040d005070b80409441202803500f00a4150b0121342807925a030458a0410f81040c100001d002c0d4282c99110642807441646003588038941d220317001803003441030f16510001251078049d40d0b58140700040508000950007000000d030f20089070700c030105140101d882d01080d0b9240c659070b040c003490001c0300300503044040360f010810140600810100183e54828030042410903805548040c03a05402c81c083c20012903582d120005091034100e41c405640c2d9441d4000c11b410341c8154200c0410710302d00481000b1a80e544540500304200750410003001a4032008002e40b588040700e12184034550201c20000809005213140b01a00040500703050704251b1280e9a00d41541e4000070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 6371221 1250 6369971 6369983
    0x16050f030406171f0501030c0201090605040605040210030203040506040b090a02130609060f241404080a060e0102070203060705210a020d0c0c030f0305060f060c01090308070e0a0909030509030604 86
    0x2070402e0303d40552007040e0f0304500302050615030046a64103041c45141c2501c502c0d4141075460b00c8a100a500030340013a10340300e510071030420880c0307010b19100c002481d09079410b034066952001d41c120101e02902c222400360341c000c00240107940c1d907030f501d2102c5040024440311903130159500100060300c81080b1010b4205000c4404070711503050660341801c80d01e06500000c403404a6240410a5070410b0790702c60010403100880084c4440038035425100c1d92400d1440808490b0001400105004045501c1340454480c80301440010b18200781e503030a0340942c040181d496003040001c180801e015a001b041207844580c1100004106030110101e072a6049034615605a00010080c503150014840c49100c1031550501210581d280d40b4001d041e01501a880024940d84074040347c41d5589203000d01c00300300c3e001401d043d5a094800b48160207802401c40440102e4401c501240c42e00b40900681000440050310800300d051030300307002c2e00c00380050400a609000b42041324118a4800f48009882180540 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 6372471 1250 6371221 6371237
    0xc0302040203040b1f06120507050702030a030806031203090d0e040f0e0a050f060702030f09010302130303030207110603090c06070c090507020607021005010b0901440f0c16050f030406 81
    0x2024810f840014800c0b8504c50040c070030b09101b216000080800e10540c0900c0014072aaa4441c080c0c5161181c140044d47c10310440c45060708040d4003c81c01e6210f280150265842294090000040b0740419140800e164000c3c010480c1d105104d0340c1c00e245002c4c001000468000745d03200507501294241c002088607034001c65660f10512008016900800c60108020300c024038220800039100d000c0c0e40311408000030006000000c1303a2103901a0340641850100350392500b543e9140c0034000b035204000481e031460b94078817004000d160500c1680c0c81201c4000150a11131864010002140e006003811628540500b00c04107052810744641440740344c1a0f0001d08031420401d030064500081786481035071343c0307040c90b0040c0020300403141614000c4600f828002d1100b21084009070710b0f000e0b9805c00780381d90003058a12a000105690400519861901d0b6014094032030396040c842034001114041c074010010400504e841041c0600f10f00c1c180d020310240c5400650101555046900c65400800054251 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 6373721 1250 6372471 6372481
    0x30910060b070c050607050c010c05101b03050a0605130b0103020c0d020705010809010203040c03030507032006061002010203010503061302061308010f062c100b040b13060c030c0f0c0302040203040b 87
    0x44034103c05003108035407081c1041c0c420f5441d5a5544040c41c080d03410458000a00400c0000401072207515100c602400d02c8140002e4501200d22101d0b10710f4100064100404200340042901c19481035890140100d00041c0d50b000e19032000d00b00b03000101e0704040c0e017004a1004118180b0150707450000b154080c2902c2c51815000602c0c0d03680103046003440c2d034070400a1000040c80c94483d1307000c80e0341c581080358842695080584055801d00c410307104007040581d50542d10b80000c20440d00c900c20481c0c40c009106401c40049080340000d0087c160591b10401c0401c20b001d20400203070380400c0c40100664600002907500d00ac030000d05510480e02030b91036070076840540c151409403e02502403900b0348000c41d0a104040c0811441c1d541e9107080024000e00411007419140b4214005807207400011030352070f0f82e01c0c80e084000f0750100c404401c1e548018074010403510300c54154124207035095a14440710350b00a1711070035007040d104c10b8112001560350800000585031400038610590142841c4800707441c00c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 6374971 1250 6373721 6373733
    0x70503071208060603090303040f0f0501050f0103030801150801050f042702090606070203060727080f01050114010225031e020901060e01050a03050402041401030f060b0102030a05040b030910060b07 87
    0x2e04054401e00c13040c0700700040001c0000540354010382019604451401600303182c400b00c02001c00c094519401c01081201000040f0781c0141241c1c82a540e030f0750307160b03a2680d80c038801c01c02d040044400101410010050340c07074216a90038002000810026280504a040700700b0712607020401b91000c0c100c803584000350300d820a186940300d041902c01500d030075000e90000f5124032006042000780300748000b0807071440359040d4092018a40461001e5080c80d1100c500c5030303613004040c00c040b14941c208030000c03035014247c40303014440079410703001880403206400749503044000c030100f40c410003d6640300020116072901d00090865642e01001e40c0402d0060041c4410050141c005c42c06020300c010340042166400000c6480c0ba503400d2400007515101d40c070008002e01540d50444c080f8a40c0d590011040c03101c513010070000d05210361000c10804007081c0c01642c40f40200700c600c202184d01440b04011014291000350351003c048000c4e43c010305901b00e018030407500240c0140e4101c0a0210b00b0004001d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 6376221 1250 6374971 6374987
    0x7020906030f3708160303090506010b07060510030b0105010503280506031b01020303190f020a02030307170705040902210106050c01141504020a020304080a08090103140402030d0503060102030705030712 89
    0x3401d000740501a50039442d12031481c03141170820000280036101c03210625129601c451900d55001c41600c0c65560340d44002103164100d050251480ba240c10040f40b00d120310301c124071003100c1e40b02004400c0350307203004019202500b00400d403043c110241e04051005400e052142141d00d03404c20000a81424008203040c68982070307108103d4002c07484100b940550707800106480d40202c0c40c03c00c0580c50855000380344044c004480108074801c3c0040707014410300e0340100c080d501c03507403607a500c401c10046052410408002e00b40c1e4501e0101d0340c00c00c018014041180c0041146080d07541c0280f40700c031640001030002d07000c00d9001c1c1000400c0460701ca2004002805644101d03440c0a440850a0421143c1040b400392949041485241e00244021409000f4001e9a00801414095529124250030700810343d511885031680000c0c03914910030800f110443d5918051034002d8024446085074800c180e40c0d943c009012036066210030300c5000000b82d010070090900c54400d81c00d60b0003d044a10313000d450382d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 6377471 1250 6376221 6376303
    0x70b010f1a0304031205061908010c0e06120c030705071410060b1305040b12070e0103050d0306080c010c0c1e030b0601020604080a0c0611030103060506030606030c030307020906030f 80
    0x410400520000c207174002080d085141e02d00c2800206616135800140300f0480c10007201044140c0b035000050043c1066001800e240840d40320002d4010000c810000c8611440d00c07050780b9280e0401c0801d144c03281240155610510504295140014686910079522031124000406500040c1d10381c030000c1e0903000d01070040039603201090a10164850803850302441e030040a020f1661819124496502e604030984151034080580303180c41d4441c1d099140a102c2404156000d20036980a40102d80c881d01c0b4000c22546040b014081c850b1100740111016110080d094a40307400c04140444c0e00800701c0d081d18000880e0090300c108142c610310b0000300c680c00c000d00c41070540d00418100b001040d0380504036910b0041031302c0e0002c81d265103482c00500400c030078600304140c80004030012017000b4582c0c1c800da0040ba000c40444500c0d9490004040c2e0f0741c5020540c003a055041440f0300c100500341031800c140c00400003401c1d200450504a0010304d8483d644248810302958002d10110752640204014016 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 6378721 1250 6377471 6377519
    0x1e0307030e010509250902160303110708270301020409020d050a0c050307080c040e15010201050603010b150d090501090302011d03160803070c02030a03030e0c18010306020708070b010f 81
    0x900d80b0030a641d07181d0300c0300c0d8110000b83c8600d490f45d1414000420840c00500007940c030071500c0340003016142c0740090f1070309022008a03181403120018601483c080e074443e07039401845140380200410520121458101007004001384001a100b0f150ba400c0c0042c001034000389100585900c9443e1029007521400761150349218a002d481c0c101c0d0650103400c4036403003011410031150a171100012101107125039400030460110f42000d10059018450a414441c02c00364028401034032508101800c8405c1c0c0310b10a58040c01103840c0e400c000c08404050055060b079070a0000310300101762642e9007076590a1100301d00503590b5028140469214400b101c41145010004504261404549204984000f9006045014003000003804140318181c1d20b1486a4050185c0343c0107286840e02034054600c94607038001d42d0040040d000740e2801c1403c4241c00300000144400900d902e0751b102e000081d804044240c44000003000685c011400040c0701c14000c01d03494009210043c600141d060401020300c4040a078 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 6379971 1250 6378721 6378731
    0xd0e12060703020906070605010305030405011e021b030123010306180305030601080a06080a030206010f1a1603090506070b09010f050603060a0510180605030d05070203030d020304081e0307030e01 86
    0x10900014915031140c01400c0059a90003e040003038118001e07568003e20031403d110004c41000b20210140040700c800b0388800ca00310a03c4800860b001418910031401603211009048072100c1642421080c0c010107000020722000a03140040700c002c61890241025140724010010482988034013400980200240e1410000c1c0341d40040030351201a1840c3e04010328500800c011201c2940050024039812040303a44641451402940740d8000744900d0b03c5504408000080b09949032905034100d11042e404913140942c0440c59940400c0f00c0d01080e800c014a4001c0072805458102c018030465000341060742c02031401074100c609490b041c00181f00400c0c04c01d020f000c03440d100054040d811070381c0030348086a59070351040d040d2055140c81c0c1c4095115406201001e80a250b81d078041401c2c1d030320039070507214540152101070b21180700c0d16a00941650080060b00c0340390180782c0c06582c000e44181070707061405204903a41307200482101e48807100440d00005001041c0e4140c440c2d103500e450001c0003400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 6381221 1250 6379971 6379999
    0x2071805070504091a060d0c0906080c0403020603040c05030d0c0507060923041e060302010905030d080403120204050303070602090315160302210106020601060206100308030613020d050403020d0e 86
    0x901403885100013007600e40c400c003807000e442c1c8441c92440c61806080d054030b40701840342030302c0601441c010000100c1d44080000c11250320410340188143e00c1c02006510709883d6a00744600e81d440100180c801d2640b4200c04a501d41e018403586030891000d40d1500c000c1d1446042c040c1c03e00190364498014032000603010084007011203c01d10480c0c0c0540e444140351000080894090405048161550151036180481404007139002d441968000e03650748494a03251360506075a000781e0758012000c11801c000150009108000c11501c41c0e940c030001500b4983e852022070308d1500607541c211402d03034000c540d100c00c901701040891000c0700c0c404004826420583e900e0083c0c200c0c6180450105500015490012030110701c49040d40c01d480304d01c424241da500c0324000c1d29032000303000d40c10042c018140421900140c00410b0000e482e0030220390761554032507a040204c00004415640000754081c23010004608480c421144164020340280400849038a001080d80388000c240e0741c41400e10b02c800c40 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 6382471 1250 6381221 6381227
    0x2070602061012060b030601061806020304030f12020703140102030103060506010507020a05100e090a0e0106120809040506130c09080705040204080c0402090402040302060c0703030305060103020a0f0e040e030a0207180507 97
    0x20403030795541403480f0118264188a0007506000300a2501403086d80000100c03940d0044064014601044d8030b07e81640c1c5520080762284250b100103002c1d006070026840201d20f10015800b40d5585c0b03070045822880e82d945e5170003500000d8050b40c519995004c001001400058041c00b588040f003480c00c2e5107803c2d072a038005502c0140d00c1c0111802556803a130035141850181c0c030501d804040081130100d480c948001c44c1d402814aa043c0d04c5059400e0640c00640c5403101181b41102582c05000c0034140070240d001c0c00010708000f016268405181c3c2c5031003035480800c1c401c407000f00e03d0a03075a41840c2e506101405151032401d81c0540e00441c070400041100c004046560b0401100072600944d90703002410026000e402250806540440006411912038000040f2982282d01c691000c3c0669a18000150220b00400500e2004120b0810000000c0342c03060b14041d02d648070040c000500d006e900b61140e1b14682090f030641c0d0250b0301c881c900740a0500301682500520907484400d01031482d04181c02 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 6383721 1250 6382471 6382501
    0x1030f0b090f10180204030203120406081906030b07051206030606060f0d0b03030f030a0f0207020d030305040302010f1a0909031e0a0c02040504030c061406091303180311010207060206 81
    0x215007401001d1001c01c3c80719601040c8400100152006038010507624a4458003c0d03115100880c4244244808803c074520a0019078040b00d403551607000c42c1d6902d4001c12581400280c040c030700c03c2c0d5500c540100002e44020503007401089a651541d480e0500a00e070103612500140c00c05200e0b522040803c002a03840c072040712840d25610355100c0d00e42080119a2014242034a4115414040031070a080e05002e500c002d1131140180320018400c0c074180400c100700300c4c4a6031401a4200c5811f00034100480d00a41000d90424031130701c000203501c0c1c08030145404031488549600b40842d46000c00309072a1510b01c0000c1d0b0032140c280c0c003071458044400034070790210f00881400e01000a004c113803042094010524030644a80281060145103000d250080c03081519240880d610b0380742c1321303c00c038507442c90031354040c03040001502144403a2034001004610311600c800c124100192940320b0200c070824580400002d6210f00340c6103002142d56400641020b5080e00300f601150311503000c00000300680c40302 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 6384971 1250 6383721 6383731
    0xc010c0806091305070503030c01090b070305090a0f02010e090115090501180302090603070801020a020c2803020f0f0301061d090303040f02060304060f021b0705030706020703080903030c0604060b01030f0b09 91
    0x3c00500c0885629003141001000d80c440c03a858040032030511b600381030640200d0300c101d00c02c5100c4401c0382d545110a42c100ca03001c0c1c4142d541940b224602000145040b400040ba03180141840d0300c0480241c0c001a8601100340c0100c02000310a41c130340701d501d0b42c10034170300005003e090038021049940303001e405000b5007451001038401e15075940842c0e8192028130180014200840080d5650a100c030307800703540c51084002590140b000c00c017140380e03284081650a508070109442e43d5801c40c0c65a020400c04845030801d480d484101400d030080e141c1e509100c0e49000b0401c4103103000303074100e401240b40080c48008081280d241c0081041000180080303010703800c629412500f40d91603843d9810540b0051a0302405100340310720005450401c1004154001a0400c08000b200c401c503490f0701c10306440742c0a51044001591100c0f00600c001604003000e4900564090120380c107000b44904d9180c036250b02036605503a103aa4035035072080341e135900d801138484d8401d0f4100c0900a0207801d0001c21824840242 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 6386221 1250 6384971 6384991
    0xb07140304030c030210110f030601050c0604050d090f03030807030507020316050c0405060103060302220f05010339050409080708190801080309010c0201030b0d021207060305010e090a03050d0b060f0c010c080609 93
    0x940ac0e46e0103402901d031051120002c440643c507081c54002c0e621003050300e4100c0420b0040c203001507403118040c2e92a056a5156440300e00d180c460040682c09000c0c040d0560003035000912088060340c0c1c1852501d614903001d4002031840703680f090f0a0208484014105078100f42c1004801d00140c0c403031740c2415a03604040984503241c4088400210000c01500810401a038206000001802000e2402401c19858140d006074404060352154403100010740c2050903180185400300800e103050313840f0540b402d000c0c08000e4036100d810341d5410010360054825190554500043c140440d500c068040c2c054000007000310320389002040060000c00c0b181c3c100904141d00d60307007200c00c00d44954a140550aa01500c21801100c1c0c030601c2c0d030745a2000c1c0c0248400a8648000040c00c1c2504e0f0121501405c5400054244540e180e101124030b03a02054030080307146e894003c1101c1c20b4450000400459142c80403c1e034550f0200c07c601c83c29100400041020040110140280795a40c40c1e00b03c4e410201c040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 6387471 1250 6386221 6386227
    0x2060c07120f021c030206060f150c0304180b0f06030a020c060a0b030f2a0a0e07020c0f040c02060117010e0709020d060e04050a0b07140304030c030210110f 69
    0x801168603121003900181c0c1454954520107081044030524200c2d818421641d4132501460704043d02d014400d0210041c0043e40314002040e454288075250004d0301001400034240121590451581c5900c000c40c11a269880060100102e940b925510320030101201c900f0311a4900080001c0c080d1030a041ca011b100e00341c0000418507000c0241d044034101c0340d41c0400e9030800d01d80462540010704010030214003a0241c4d0303150321303013101c00400e03401d00e00b4042d081221003048429020098400010124603000343c1404400b2412000f00701c0307a1031007040e65034001d1080d0116401400b00d00444805080e008a0600211212564011548a040d151910000341c0e030b400c11844800d000d00201d080ca244103009450011902e411150024240c01d600568113004065031000c00001030002210007506a0b00414940c100040c48401e82c42d0700542e440c42c05000500000d00b1368140c9a200355021004030394071070800b00806405003d039400b0f500021030100b007101c00c1c60b404502540301e00c24074800400000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 6388721 1250 6387471 6387487
    0x51203030a1e0c0f0206010603021312080c0604050604020a050409110114040902040311040b221a04050c031608060f060705010207050d08041502090f010507050a02060d1a09010303020a0206 83
    0x1140820114100c0302c1e4240302c482d000f070380090641403008240c280107029110012400794001d008a4030407490768a034030891039140907680391401c44480da00701da041c1001c101d5100d00c58801c100b550700a901920146c4003500b414410020000d5196004c0340c0180d051110707800108081c3d42c00003c0c808001c0c01c0c5108503417141e08001c1500e218035008410b0280c40800c0200c1403102e0300000c100804003d41d410400705c0b0002e010044070030192004c480c0310a02080c071000000845401ca030f04580e084030007040c2c540c0350503800038041d41d80c02c0300c2030181d283c008002c0000f440c1712035085000180160a02c2003050401d071000c180155640740c405402158005990810071401f54101c5824a8001081c0c07080180074010007084070f20155010348052801700c10a40040142d40b01329882c1550007411038456408040c010760f410341006809030307924080c40e500030000d0780300d0000928818a40ca1000128002401d00c82545d40d402d00c0145400380c0700c0340c4018000a500003031000074603030301111000d0300d540007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 6389971 1250 6388721 6388751
    0x402030a0203060c0901080109060e010b07030302090402030106030507021b032e02040f05030d0206070503040308040501090f0b0709060c0209010603020f0c0d02150a021201030b06060702090c0301030c051203030a 93
    0x203854020340510451040100c034908580280c002400b01344c1e21615141d81e00c840101c2030341ca450240c64001c265410042011000d50740060130083c0c1311b030401505041d1040300080490308242d02000100c1d03194070070081016414040f18000924030401c0340e400c24900b0010951302e04100c10304002d00401030740041e20f078103e540c00321040c01e10f50317403002d664030398a8a00369500d240c0144a001c2c041c2c440d020a0010490001c10900d10a1165607546411341c0d665860848000d40c1c054020307140c0d5503032090024017140700414115140c0e402000c6194080c1003519008142240075400740b81004a546440c43c010396423081e10318110340440c9400350b114004a4003010243c401da000c800d00b01c0c445ca001c428003903038001c510704104128001ca51292a603560110f00706910440048048050340e01c80180000b030144079405403c030714060070440c100f61480e80422507510040e103022901d9540400108100b10a0700c4900002d48001d40350b0400c0e6200c1d01e00d500d40c3d0b03404090703c40912907854400080d00356603 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 6391221 1250 6389971 6389983
    0x100b03070201150305010c0e0102030c0c0409110d0609020114070302060a02090f12070806010b04050d060f0e03040306050411120a0602070201030b060f0c100c090608060d061104061b0308010e040203 87
    0x20f0500040250070350320b2404900030203980d0084400306141c04038a028960000c801d55610340300020240c003a40349100d04000c0100304c40394003220458603400c6580b003030f80c4070f20700c2a40c2094410007000452214034000500442c018111004581e942049107030006540450900d412043c800000b5032070b00480c600040c2c440e101030004030b4100045109805156038001501c030700300d03080340d01922641e0f62515900d1145104a0240781e4100c1080b43c80700000610903484071840414007040060044000c46001d4150b901a60003580d0440c0c6580a0005003c0d030700340d841c00c1c404421101c003044640e00c01030040c5c031000a4400509501e074003050b101c003903900075042480042d0006103040c2e510742c503a056102040c6c10810003004188101d00c00000303850b81c3c41c41201e048d940591128050a842c0510440b5204402413590313803c1a91000784c240010780f14001c46508006103103000751900d04118000740b031500c0c2024852003010340520000c020a420240f5681074521001498544d6580c600211307241174 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 6392471 1250 6391221 6391241
    0xa020904081207090e06010e0a03030806120f0d11030a02060403120e0604030804060e0c03030d020a12020a0905100e0105090f01021c0302040f0605070b010e070210060b04031703100b03070201 84
    0x3107020340400050344d501100d510b00b030302d514200015460710703007038011251404c5100c0980e4201c4048030051000c1381c0106022640090020495420700d941c21090758101001490400e1007640440d030a241d1040c3c002c0201811059004011400d0001a880003503894201038000307001c0c48440340a46499520316002480000e08100131640f0608040c54020b00240007160b040d90700918010b441035400d9408207444070591401001541080b00072044070009520080c00e103818040e04c2c1c0342c4c0e564030291500241031038a9080c0c5400090398981428095210340c1c9544500c20001c06001c82c0c80203a8010342500c5042c0030039a004541e21801000503440c0c981d2180c0c40d85020350070040b08000d0300d40d1580041068540c8420b0032100c440d0341d0300094a003400340323641c024184144800180306000c0f200305401c0d404400317407049580885181d00640c0845030a500040d02c0c40340000760520a000d18248110b40e040040c103045451454840c052110020780d502070b03003040c10300000128025500c00d4102c410340c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 6393721 1250 6392471 6392497
    0x30207020105040801140f0a090201090605180a030f0201030608060903070f110904060b040b06040311130b0603040305030106090f05130f0b0a0803090a05030a02010f0f05040b0a030e120a020a02090408 88
    0x90140f42c03010440c0f04040b102c7c4481c0d103110070002601d805c018040e0600c019030613107a8440072414950142c6245c4c11540300c02e95403925440c2c040825541c0d40260710011400382c02c20400c9802c50380001010b960080e00a0302040d0710803818010702080c00000c0b200d00315003100c0304220404c0145003000d0400b42c000a8aa4803608180034482408181e51042120b8081101d080007030107200000d10105000f540f1000c0c060301c0142c140c4039060b0500c104040c00c415054100081e11044000020b002a00107980a900003039002c00180300076a0480c0c5484090310000c1309400f440c038600400504100040301c5070302c42881d15400042c1e24052290082e01c2c0700f06000301070300062602c81c1c0540b03035a50801c610707062041001100000d5541070200d0311a040a4041e5295421040180302c145d401c0b00c21600b00904106d800c01c00004c9148030356000c1c0a501049980200d1840814510b003441c100c41d40d0a1800305250030080203033400c2c0c0005d041d960455055070741c1002d55440e070522841d640280340d412030705 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 6394971 1250 6393721 6393731
    0x4082107050c0c0f0a0303050708040504090b0405071a030403050a020c0406080d0201050a0209010801031e081204140c010807030e030706020706020702010219110d0f05010c0201150605030c030106030207020105040801 95
    0x42036041409440010b458908441040b04240c0402400c820000d03205600180011424800b1921400080c5a014050500e481c60716030380700003140c21100b48a20554079040540c045c00304000090040d400207264160581c0b24140108502100034400580014244100043d0a441c6280280040da4007030000400c10051255035480032500ca094694018005506c2c180018400150300c0c42603a8000750103944120b21607017150b8035414160044000e1062403400400c103000041c030b200740104441a03d111b040546800c1a00d840c94000322100d0100c6c2141e00070804a2101c1d0740e100142581c272264502d004109085a04039050542c4540d800240c0140d00002c1e0382000d1000a400030803449100f0790032200d00c00003001101185409006000308078220303203145041c140c80c100440062080c01045200b46400b480d83d01c2c6c42c2120886103201d800342c4d440e9a55034800b881c0c081c4900006100d9418464030f0361412080a00c25440305015150074907a02040020542e44107005a40107810751a00800c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 6396221 1250 6394971 6394981
    0x140d0b090108100c08090a140a240501080303060d060b01030b03070801021b070b04090203040303060e0f070e040902030703060c02030f0a0504051005091e01030209030106090f0b090708040821 84
    0x2480318040300f0030449050808103543c1d120351141104d1442040d0040150a0f900e103684e648610307009a0325100c034124481c8030100e02c04102c4201c4000209120064800840f0a45000000a40704160f125940d1900180100005912200040003c259000d000050a40c0408006a0040000f80312550b01072259500c04079150505600a102214110403000c2b0620f841c2c0d540d40c0e548101c0d41c0582005403000340000c101c201110f03000366400078801c0c14003184080c0c68402d01b0420410440c4c03689102c824070424040c080350443c80d8200703002c0c0141c0e0140207083e220b8011039521486840014401c5a03100004200d591086c020380f0300c503d9010301043d6807119141d00c000c20783c2e082800380d9071007986024007884145000d0b2044442c6440064000c001c80e0804400c0c01001c40c01d0600007905058081200207200d5130284070b08400303400309013000917941c1c041014500803105030040c01401000602c051259450700080100d80c410361107501d40780e075100c8095804048181c0d444c070100b10030004400788a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 6397471 1250 6396221 6396223
    0x20a09090f05010f0b0105070b0406020d0504051608012007060603020d080309010606020304030b04080d11040602010207030e0d0b160201090209010e06030c0301060b03190b030f0c0a08060601140d0b090108 90
    0x60070040c0a50000c1c07107660840b07801e640c12124041d038943c3c081a030400c01200041d40400020350721502820740181030070100f501c54025141d00b12811141e0b80c1100031246040d80c002c0d0315200203006460020482210340c00101a210324800001400c040b42c0410100e04201180d000400a9980030b0000d0380c1d40780d003d00d0901c080d9003040d19061842d5080c0240495400d2001013a14100c87d041006043e89882c0c98864001c258131004141014a03203864000041113420b500030001049281c1c0016910800c60400401c448000d26a1503c07800713100c4200800f0032614403509810251588030000d440740f042c001a40102105800250000c85000000402c4000c003902d540c0324500503416100180010000c0600722a41750096100a04091000c03480160482403000c2d03054245020014140c10001c001914001a0f40348000c1d042e03000100d6a401403e141200500424a9400410043c00d00b500080c110041859510a0020700032416209082158024841c41d00300600320700a1035845905031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 6398721 1250 6397471 6397493
    0x6040b0403080301031a1302040b01020c030604030914040203040804060e190b07030305070309030f030b01050405040608010e010c140904050a02040e09060a0b0303070317060409080a02010c09090b0108060409020a0909 95
    0xe0b00d032080c4040c0c020049400c1c100d502482603001110154002c04181d0809c80142800c2d03e00904512818103001142e840821000e4007030350103912a02600c92514175003000070081101c0090040e0b005000784000241250140c070155031107410100c0c0404156000f107a11029040c944d10072406405500141c20b040d9500180401e9009940c244104c0c0d441c1c0c40244e0545120312401800541c2d5644011881c520a6000c0d40d504c10051400c42d18050750b0b000010151102e42d0009185a5541c1303190003140c00c800d10405409410a00b80701a11400d0300581ea121400fa40e4504c9000c0e9071900c1c001288003c0c281e048030040c090040207803003a814900c00055035032004039544503035185000c1750244686800826100ca041e0b0542c0c400400b02c1008149100d0711034003620080d007168a90702040c0000c0d071a080076107401641c940c0001948a02c006009246040c1d0742c0c000cc410900d0300038450b00d581d80c441d0b4100d50140081e0740204e020007003403020501102c07003070b8401c1d4400c51900c3c055001b0800c081030301c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 6399971 1250 6398721 6398723
    0x9041d07031505070801060e0f060904020a02100b010905010903031107090c0201020d050703050115050c030f03070f0806041104091508100b01090509100509040503040801140402030d0806010203160206040b040308030103 96
    0x100300f00c1c540d04d0a105517400c3d03000b03000742c83c00709a005003651014540340c21950140c0d60003804190510340410045400d03030b04810440005601b0418600f011040b45205000711102d00b4038003500528070703010001e0403402071400058100409200d95114001c401c1003410b00a00c0b8100b000c10000c1e0301c0c648001d00030341003100d41c01c1d40c00781000046007119201c1c0c01024140c61b540d000d14000c0054070802640c0552000d807021001d03000070700202c510b076001003010b544a50000e4031079030104859a0350081141a00070700cc0c1b480343e85040141ea8540f03000100780c50658a041c4d0000a076020000c01640040c3c031590300550143c0304242410134040c0c0c030341d040341c69188000e032215220300d07495104200b2541c20494010110016510040016141c00d0105540103400341007545e02d0075844005260940d6010200e0b10b01e805116414802182420080b0041c40701540c54841007a0600d200002c1d103a21468904040221003809214295a41d61044500400d92400d170241c1d11603880c900b4031501d81007444 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 6401221 1250 6399971 6400013
    0x309170604020f0d030c0c1202090c030c030609180f01020c07120203120a140a0503070818061512010e0604060b010203042d0306050f0402030c0406080309041d0703 72
    0x11146a501400081850040398000c0c000041c40c0c150509014a0012401e400d070308105194201c0c502049030121b2540160030748203240c03000c05110740107100404030f000c0c2000350105420000c01c140300c0b903242c00342e940010b4200c03251905c0b91111080392034240c034a5450458030303014100c0d000d903e0200540c01858110018030a80d06000d54170717400200e00780300079140030b9059048035240541c1c00b404e540040c801c1e140903040c5402e6002040d410845280c1082011401280b000000e100001d500036140b181c0c8001c00c0d00c0b00a60f0082c3d00180a52a02c20143c480f0480307140b800314040d40d643c3c806080300701110700840208180d00941200070b556000640342515206d1034001c10040d554400b00403507068480125075031110a40302c2c2c00e01c131b0303103e8038007080c40c072401c040b521021000540d5030150500331405400f00c0320580c14580100350911000da41028031441c03030604200584000401074800d00101120000350041003000c00300c042e0034140f91201c5032401611b0001c010440c488654040a4804413 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 6402471 1250 6401221 6401249
    0xd06020f0307111209030a0605061903060c08010b160b060102010209180609010504110307050304020a0302040e010209010909021c05060d02030d0918060b04050607050c060a03020414030106050105070308070c050a0309 95
    0x1801480c90348226001740e03030035070081c500e40b4001c1065900000e0b00604050070031109400e841d805d000e0080240c1d00200c540d2615429800243c03035111050030b0150400f00051460240001c42c00c00d040c03000c0201c0141000c600303c000881c039a000b90705884034074801030a110713042840341483c011a40d00c1291030394810500c074000416241000c1c440d04134001d05011006266465098041d201600002e2049030b0100343c0032000f01c0140c9407800b5010981030800300258130380031178038005890f184040e003003504a1841801008158004e507410301c038040034031507000201030701d0300c1020801e44002d40901035003621a06100030a110707400721440086030400e1007180c2d0884604050132040d038501f44107040350350b90300b40030a100c5460301c9002000400d2050080b42c40b10010320000c95619004000380d4400f00c1e0340858104010420b00425100204084008208950611001a02c01d0013055000307000c000b01c1d2400946698007508c0421407080d0040d0480307410200c0f40c0307001030045507d40100205030f00d0f50 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 6403721 1250 6402471 6402493
    0xc031215060908060c030f04150f1e09020a090902060c0303010806040506090309031b0d060c0201050720060a05090f010207060207060605030c09010b0f040e0901060914040b01050d06020f030711 85
    0x31a0b5107000c2e05c4c2c1412250b16648035144840c886150103803094070709010070b440180944111b0711030001c0c142031503c404516644010070a104042540004d204480c0c2840c2103000181e903200d070305c041a103041c5100000e20700014000310303a09008000244078244400000850400400580c10784518460705c2103030400d5482902c081d4890107091800b0343c15600028030b542e212843c0c16507144982801070f0070080e5801c02600c441e001d45e1030a00b4140d0143c0d40d40c106000b0519448003280c0b1a1401c41c552481e11034441040c55551018000e100e000c80f6651007012800d884010300100f030b20415000020b42d200c0400d800c1c03060095009000031159145007040c00036041c2008110306140680090070a10540c0c41c2a144e484594040340c441241033b02d0800001c01d4007503403241050300428001c2c0000500e40c3c00c0030469011030321110a00340191480004100000d441c125160f41903900545110002100901d0003d000e0301540d00103100071000401040300c020b5011092a01d0b0150304002c4840341c043d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 6404971 1250 6403721 6403723
    0x6010305010c1d0103021612090509010501020109050c0405060301020405060408060604050f0c0316020c15030a06060203030c07030e030106030206120604050a0203070e0d021203040305060103030e090709060c031215060908 97
    0x303640210070700600c40c528140f4666000e82e028141440d11800b46040b00d000e43d80d2990600740c80940f1400101e010020280054140b503281a07001d00821300081040700d12584941c4d940d001c84142251084c1c0e1107a000a401d61001e4055038001c2001401c82c07038036591101d81c0d01d52680790460f41c180c05035240c02c00140070480d0145410340104c0030090030a28584655141810451907400d6120562103801c00340810f40c0c444010100ba8110003031902d81d00c3e410803c90310b006a0f9003c3e4403c10855209101307100c4181006800c0b500020341c1428107408070f040c8500030078007500f1326030301c040d6202001041901d401031000402610600742142c08200969800c12642d040b1300096030108000750448008240a0a081e208156002c5c00140301440415014030840d155922940003102c03a07400c9440100109500010b0305500384408032030440d0305103030480000705000160320501d020031814031303421014580a40904001d14034622410700a40d070100414500414070352083c07600091650400050384d0030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 6406221 1250 6404971 6404987
    0x4031e0e0a03080d0e06010b0406081f05120106080105010b180108070f03090501020c01180201020712030509060304080c0a0501021e030c070b180604151109030706030f06050604030506010305010c 86
    0x4001016052014103588800750681c22004c2c1140d8040d584000c0c01d01284002c0001500800310745440581c0c45007480002800258081c000c0078881215100c0084004c03280011042a99015074030b4006881e101e1038403a02602a40d03020720001e500e40b40011813010a900028100c2410007410085002d8494004690320740007100c15000040e0030980d24203241e8480d4000340e103200c1c01503001500f03181e040f0700c44038219501d00800440c101008140d400031940c0620501c40107224410300d125a40006480c041d2a07031065240c980e100d485c0000009040009420542e2030450441085a14420062601c54000e50146072a0042c0701103820510403180034040403a445040600c40076414903c60b030761204010700c8058100044190785985180f01c1040c10018180314034007030079040142e601e400d4210740c00c0f00c007040304610540038100209403440c3c90019252044441521b80000d010301c0711308200c00142000d03001540d0041000600100788080041c4141c1a0781c0100000c100e103100c1e41e10281c0d803800e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 6407471 1250 6406221 6406247
    0x100605030f060405070c0b130c05030708060606090402041d060a0b040f030807030c0b0703060311010503060108040f02010e060a03020d05010b0702130b0102010b0a0b07050d050a17060d0b04031e 85
    0x2404600060110b080030f4100d560001317480c0c1070261001d00c40785d8952030b40700d00444165580d00741480480c411f002122801b0390080c003041d005492940e081207819a1203000040159001c0e44000500400070389407541150000e01c2e0b4503410000204003c10044500502910303035901c501e0031070201050080810049a0843e88078100c150b900d549150b40311082c1da0040d000079000e2104404518002c90103100c1d603648900281c0e40e002421500303510f4000d070109141c44030141000014420011640d8000302000d40080d0041401c008080c00d03880121282c4d44c600941541000022618071308007a09138003d0010319800003410302240ea00c034400038806005113040651312100081c01600a02d9280e441842443c4c018400420b0002e10500440c4480c2d201d81d00a5030700480c0050a6001d002c400e000c0303071b134886d402480c01618101e10140d00905124104100c036540a40e8a004914941c0d1079440910025600030034210552a0a09010b08250750980050b95603440c81000190900c0c41390b10400401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 6408721 1250 6407471 6407491
    0x108060603010b0a12020913080313060e0a08070803060409080a180e0405070b0a020f0601060c02030c01030603080316090315050906090c0102060103080309010b120c04140f28090302010510060503 86
    0xc088aa007c02070f002c0f201800d640c3d280a0489500c4010850000c010b501c075488001100100160501e0300804803001c000e41c550107a0400d00991001464140403120700c15080320846d078607034840f000000c0050440e140010218200001c4c00b01200f41c000c0340d0a054805074004403240d256449001c4003074100100d40041058001e64801d1180c50900790242820204a10444a04c84504180d1a14044080e045200480c1500c114002103250401c40190310380e8003840e0a0100341d24650360f01807d808050540e0b000c01c80f4a54001c2c6445104058400007185c01ca100b10003c02d4480d42e82074014a030903240303a8028000c20000402a550024a41a10310010380c000d0100340c0c6162209005908058415003c55407203001d00c0c8150341d0b40c82c0c1c4d01c5034810342c180003400c1e080380c1c418100700841c1c131003104a5083d001001c04014500c801d200c040d0741d002c40a40060006645000f40ba03c10102040340c0e41e00c41140390030304160038981d056000d244580880401221102d45410043e951800100c40190348 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 6409971 1250 6408721 6408749
    0xf030721050a0c0311151903020d09050601030b04050d0207060e0d060e061f060207030201020c090702030f070f0308060d0b04030f020f0a030302090306070c0b01030305030c040504050108060603010b0a 88
    0x51030141589842aa601503000d03102442410b070b0300c419524a0319442610204e680002c459454600410314120001171007050381d1401c490001811043c10011800e0400e00d5800301d001d00e81c10030250071425249501009550943da1680380500003100c091f9404d46080c0b00d8010a0a0882c2c0005a44c00c25107038a9200c103c3c00007112020010042a0110100c030a103850740c03503038001e50300304100d018001c0c2c5e0121960400400100d0302c202281070190311440071980003000801c01760340c0108902254100582d48080a40e5400d00164690322031a8074500c1101000150360007070040e13070303010182501d03c2566000141e03166002000005101c1250280001f20044003090000740104000407614446006072180428a400301c1800c01c2100002940402c0d0000340400341c0385400d006d0581e205225090001c1040c545488a81c1c414605000c010240321000011404952201c4241da00508000f0010301c40c0750384512507643c8400c0709443c100d001c6c0d0f09003440c00e44940b80041d503840c2607030501006542c1e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 6411221 1250 6409971 6410009
    0x3020901090f020f0403030305090f0c0f04090602040506040f06030b030303040b0c07030e030f0703020103060b0408070b0c010204090c0518010305040506160c0602070c0501080106030515040507050903010f0b0f0307 94
    0x40145854989605120f0342044428102c50342840a070004500035240007610385400681d1030300b070032421480c070319464112076040c482a40d24039407089400e01003520006803800d85d07817403c4e000078400c4e900499071040b00803074000303142d41c2c00d6000c041c02d6421540d024482e606003c818103940c0d000540d002042c01103041c0014441010720806404441d00a141c21000500b01c3c1000c6410000751040e2489941c01c030303010910544d40c260044138014603007490080d18007460080c07100d840f400c2c907000e1a000c0301c41c0050400f00950782501a140030b070240040800200030b510340080d0040d0b22030f01880c207003200e540c86041e10640c040d10450f88281d40150192181d50748284c01000c41d0740c3c10404480a0100103805840404d04503c060102c0c107100c0d0341d1000b1100c6c2408000351112005901c00400c15044c007041003400300c5290f0328444100403c3e01c3c0454240c480300b13425100f034011040011780542ca064544444a985508400031400040d103817245080d80300e805154840380b4034050100c001c0900c8600d02 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 6412471 1250 6411221 6411239
    0x1051003110102030904060b0c0c030303040f0602030615040905070807030c0f1803080c0105041a0907090b0f03010e060114040e06220b070806041a010e010818070b0310050a03020901 80
    0x241c0d94280c1407041e2441c0c42c00c00c034002401c598068200b1103095501003003020214500308403043d101e00040b4003d60451600ba56104412411507000030301c416008404240180c8460b0810b0381040c801c94040381d102c50710740100a0042004550020003d5201400304206038001c0c820301c075000581d90740d070101401510b613003030781c90008814040000d049032000c00004500e48001604000c030f40e240c004160f074106420408003001a02d410508107030245020720510003000511601141c09901c0c0100c4d0303201d5881e0002d01d69411041e00c4581550800003600b10040002c00c0c00c038140c8080628082c01c1d42d10038400d0104030f0710404c1003186582d0100001c91071007507000e04e03181c004172080c800c4d188a0030503980d10050b00d19820707100c80010845a0b000c1c042a46802d000340740f08141c0c64441c500340368480a00007444180c003011100e0501c9021804070301d422400c1003001c004030300c5203400c444c02a81c1e250030041c0c0541c000c440508030314101007000325151a012007003c08480e0018407440c002c0e42488400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 6413721 1250 6412471 6412493
    0x60406030213150b070501150602010b090a09020307030818030105070203130317070f0c030605010605070c060305091203090a020102060606130b0c01200307030b0a230402070c0305071701051003 85
    0x1120922443c0c1002031403160000c014031020340310b0700002c039a1900b11a402c46000c4410b03001101564105001c01c0e0f82a110341480980c032022007000840c0d14492400807a04241e102e0304080e01c520700004401208d8101030f02d451420036001d6000700070340c0d43c0d43d000407601d030302410390600f06103100840c080002c81c40c1542e01e0312184a9140c1e542d40b9000c441da032100b200c0710200e00f00300c1d04122940b808105001c0c46204850042c021130800c07034540002c680c1c072049007100381d0081c10189030b51080400d0700c108080180c480032034800b0301140c1e42c9040c002c1c5159134455004d0380881c014401d64000401c10700341542903c3d02c041300054105481414400c042c10150403200030a02190750343c100d610310000310410781040824000602c65502c1c146480000c0c281e590b01d0000c2e40c05003242850030004929821854a0030244480020040400d040b0000e00640320381c0c08003030052100b44a0100620038089414400c664031150800300d241e8080600c0707401c0c0da20445100c00344070103240c0d040020030000038072 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 6414971 1250 6413721 6413741
    0xf150111070b0406110d05040609030807030e040608070807090902090601030c0512040c0603051303020604030806040e01090606260a0f06020c0609010f0b030f1018020d050312060406030213 83
    0x250798030151a242e14202d2508244d004000150007003010000000042c040101d84540510307140d440d150030501c0180403001795210052056100260410916104030107900784103100400a211003079440c01515a941080c0c06044d007640031340c580000c1c581d0424400c0c11500c590182a60b04659142d00c0190010300ea140006030078402e0030841049064500d400c4144210302c01c450341c0150380e040560003000c44038010640210b00c00c90454110100b9000141168059818584841d150b81e07001c0204d40900f100c0d6580380082e40c2008030160810079240c0001099a5140325080781a408080341420032600720040405c56401c5800700b100481c00c1c000c0100c4030325005042c054174202c80007175440d21b0281e08903404900750750b580b4a11409643e040c05000e5850000700e00a2000768452401640c0b103210300b004c403042459603040540c0c035041d58813107003030300203134000341080000341080c148107841303900002d061198488920700083d81880c082c85100c0550340c015042902c190345400c4130300000c1c08802d034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 6416221 1250 6414971 6414973
    0x2070f08030601090503030a0804120f08240a090203041a040b0109050603030909090a030f020102040b0417070902130e1605030103020105030a0905010c1101050a0b0303090d0c050a03060b03060f150111 88
    0x80e001c039158030200b00411445548d0361b180b409501d080e042c10042c001c80d0580c0202000107900c1c2c490f00c480d41c0700252980005c4840c4000c00e8500f040381e01e5100c802401840f094000002000c0060107001c25070203180710328028144403402025510f4034840c2c46900303d400401803a2400010700a142d0f030703540140e44c4501d000c0c085a1030030908030b0004164100483c2d104565501078040c4001b0103621440b0140007500c80e00003541454105001c050b99170086018098030904110303041480b00200b04501c00c001c10702d10804550b10481400352000d042014000d101c2260320500100d1840e1050380d030360034000785c15a80ea1609607400c40d80111100e90000c0d00700250300d9101d01161020400c203120b414900701558075440e0050a59100742e40c25200c00402c02c001407441e0040040290720b01104950800071b00302d850002000a52610030302004480d0003858002d8110b12001c0300708403084d03105e400c030340700304400700c640035030b90a0031050780d01d5401c070b50b10000100c80c0e5110b102c1799402040c2043c0c19070701e004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 6417471 1250 6416221 6416237
    0x521040b030a09060b030a050c100c060207031815020303040f03050903070801050106030b030f0a080a0c060204060905010905040911060c0c09090a030e01020604030801060f0509030f010603110402070f08030601 92
    0x50548100703400554444840a07a80c900c0f00007004070911404039a44d80681c060852200b0980360151180c0c040000305000b2138074031050340c0142d0702c21107070f15001c1030717002c0740031902c50000703050013000c0940c1c1c1403d4080d201010350b001b06030881c0700800c410390121168001c61030b40d5150341d40c480e500c1083d0002207090150074000514207680901100015240c000000501985040d40c000e05982180c12550301941102e10190540c500225075040b040d0307080024a669062000403c803034401e0445009000c01d0710105000c540c01e54405c4011085803026070703400540e07a40320800c000c11118040e90003030158401c00a41060350511030041c00030b11702c06005503141902d4583c00b1070042c0c08215440c01e1b50b901300100600070190840146e071900302081c40104101d14003a9405403100e0418001c034414004503100d1404201d200d41304841425902805075100000070110385400f0b44598081181d018241701d80d006143e080a01c02e0380c1841e0b82101881d110080306490301180d541c00540614100000c00c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 6418721 1250 6417471 6417479
    0x10507060207050f280212120403031805060a05030604050604020408070303050301030c08030306060313050307061803032a050702040b0a0b031f060c0201030e0a020306010f030c0803030103052104 86
    0x140702034140070380100090460b007880300c0b2103603081c080701128003580020044400620300721070000e2107403140e905a440e5021484021201d511380450034070103801101c00000c0210816602041d901d1310681301c40d00860400352a44100a0140a0188520300207502800040c00524082c0c2100c1e8102501038401850035440748500c50414000f82c0040c0d021850000c0100100306546910314000d204081c050b42c15804c0040000b01e25120181200300260750f07811142041c00300074001c881007141d00c184104481001c52028544440001c0800c0d03000c04d02e8001520f88041248000180d0300940d2660352b2411a8480801d03241c9802c03882084e40c000da500c8000c0040c50321802e981e031001c0d10f082c0385043c0d22850098042d60b028194803c091034469249081081071540107a008040d0070b50900f0089400c1d40712428080c5020a07600300030354184031b000d000155a40d01c1001d40000d503070107910525041c9032a03000c1c00c0e070b03244030078400107017135501c40c0c48020421182c410f06018801868003581d0300e440d90b5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 6419971 1250 6418721 6418733
    0x11030601080d0801050a0e040f03050f0d0606030b010801080c010f020f010f0509120a0206040206220608060102010c030605030303061216060201020a0806030109020901030605070903020607141e0714010507 90
    0x9070816142540107900240c007441d00600c05070b0040000710340d641d8110f810300000c5009144054001002c205480c2ca08c801014020010348500b21500001c040c1c5800f40f240e107641c060242c601c20040861329017107800d0701c5540b103000800d044e51121001811800700e020011111031160305009c0d4110f004920115001c00000c0c020394483c551403140201c4c590600c850010f040046056000152680c100003041c91a80c01140c040c1e841038048800c07513103490b01282503d03c28481149100c01000710703000c010030300b10340104400740030700710a03802000340c0d688c4690107900f01d54035402181e82c142d0044c00041d0082c6400340c0704105016100017643c04d846841e031510f11100540c0d401500250b5008243c4603d00e0b5804840c40354015000c8009103c00e80d5181c01042c030100043c003003d8011500da20010780401d0140a05100456000d40080d03a2200d80b401c004000140300a401c42550041c2c1c035400550503081d4901111401094000d05000340c81d100346038094042c078481c000d0601400744070740000700d0340c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 6421221 1250 6419971 6419983
    0x40b0303030a05150108010608060d0309050904060501090501170303010306020c010905070b0901020d030b0105072a0620060c0a05030703090b0103030c051218130b0d20030c0108040605041103 84
    0x42d010419062090076014002e180d82455030410a43c40d00402c881303a803122409800920958500501b0403460400320ba104d100d64103e5904240f50b882807004022065100038100c82030741108100a98841841040481c2c185e032600f01c50342c0c014001480403400c180c3c010b00300c0310003200c00018403145568601d410404141d02199a400d40407641c80c0c41560148002c4400c5940c1303107410000000170038000780c56130040c0040a40350351820300700140102d6881041c83c0000400161850460340e403140004c045c1d00f0f18241c0581d0302c1c90160003041c4403800c0029954000d0018030340c6d45080410391142102c0035000104120308054441619001240028903807034003844c007907551480d001441e804d0640c035010070748018034a08a01000310790803150120806240c450b1085417102d0b2138414551002e005030800b24802c0e940815080b03807030300c00c0240c000359900c8030000798190303640b10382c045c40101074480e07402030310503404203486100060010318039903c0b042d8010300c54003a01844140c0d500c0401e04d0b000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 6422471 1250 6421221 6421231
    0x5040c02070305010507050a08070c14101d0703081b010b0402030a05070206070f120903030e0f010c090602010207020a050409031b031805030303011206020f1c02071101030504021e040b030303 84
    0x70704440d0080c010301c035081c0030b440d5010071981043c0707281a040100090600c0e000800d85001c0000c06001241004024456480444489402c0716a115080a142401050143c0e60401c4640881078000c0704450081900411680c01c0440360341410551314000105400f5910691110755171500d481030182c0d5503102a41c083c644aa100055516040c10040d06d4a080901342c0014405d4240c2d1041d00c840d8800303102c41030b0109220004c40e002a0601e8280c0c050f0461880c60140c9000b0002c207501084415840700c5100202551241c1856541e504140d08030312400710080e40040301441c00780400d040a821203204180300317142c08501d18002408a5851003a040c0c070880009008040d144244080c0302250b1020307000c200d0240d813840d4580318480c200c2003500307180108104d801152454185442c1c0099071002d041c00240ca10744000c40343c49050080d40900300454240c100806008900d5120b84201c0d4400c0e90702900e0701c071014180c0a41044182c042080456009480e000308200e1600c041c0301450040c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 6423721 1250 6422471 6422473
    0x60106020607110606030703060b040b03010e0307030206100b0a030c050f120603010606050a0507060903090f0e1609080a02040b0604050a031b060c050d081009050c0a0801140a0501030209040605040c02 88
    0xc2c2840c2c0c8000b003010421902c40c90081c0c0c84181030200e107960100f110360071641d0042000541c0005c40c7c01003406410b042c42401c2d4154600907202d17400110110050031040c2c0b10340c0c00e482160343c802448043c0b01c003003809411001c0700700b8408262814081c2c2e008103408840c40c03d0003814450314100b000040c2d071040307c85a07035052444090060a080902590001e05042c0c140310b410315820700c80045c000c1c010800c014003c5600c440302c0c0000d01d401a4a04000b800b160203143c20003946644000e880d2610540e00700c0c070113420410002c90340d244114a00401e4941c484042c120300e9a09408100c060070b20102e103154841d0701044001201c0d1780302204c10b402144110715406c00e020746510390170b04400362640000207024010030003900250001c01d5403142d0441038281881035859450401074406503a4020180c550302d07120502105001000142c040f035049551010f00c140e0321800c5c3c102d00c2d400c821200d40e402541c1110103100541c000d40161041e071030094000511156203e001400f82c800c108848005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 6424971 1250 6423721 6423733
    0xc03040f0b090a02040c02030405030307020103110d020301080607020d020c0906040c09051c03080108031303080a021504060207110f0112020a0c08120603060a0209060d090602160309060e030a050d0305040201090806010602 97
    0x1314101405441c2c401941c500185060070315000c003007900c9201d0300390001c3c109555200030342c40c6ca440382c2e4180d4a040d500c90074215125070b10341468a41e518420740341c80003d0710924254440d56480002e0507248104041c0000005898400070f0001030262003149100703000d550310b80800c940d11003050701081d07003040840da0f00c4003020508020300850010b030001e9046400800c445035828000c080341d40c2c2100d50000da09680d03003114100480c1018a4000a45034582220303003840240112030f00603180315405400ca0518604c1800c1c01c000c400010311501e20701003803005c1024050441700750f0147c86040154280281140d0082d9039039841d950052880100b80d00102050103502e0908216869010389000300442c0f9014860f0001041400351448910030759840d940f81c2c200304096038041d00d681d03034131701c00d1000084912440e02a05c00d40d0b05000b0b110008c1c550b820a00d500d031030f00003032002815802c030300584940042d2602c07c9003d0000140240c4c1480000c00001030059410404203000b03001170f5001e00340f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 6426221 1250 6424971 6424973
    0x1b050306011709030412150f0b04050105010f0806010503060f030f160e0c09060304030c0602030a0b01020d0c0803060904081605010b040605040207021f0e060403030e040c020d080c03040f0b090a 85
    0x602d542e240d095034070145990301000340d0359000004031400e440d0b071107841000d2250b05284c40c10410b1540d80d035124510f81809611140280941c02c0884906c1c0d0898052000303030380711070044903410342d454503400001e480d00c00410b00d0303540688000c50700004050a1400100607000202c2d2900c01d003030310343c00b4041e030012000807007822458170528050560701e0350364012414080c40d420f50728040c0c2d0b8291131003204000701003801c03d8010b880c400b11381d0398000c0e0300790748130b24200500c00014003003004060f000d4000c103200601d03441d201d80c007110301032680a0700060030340d02c40c0d0007842038820000300116055001001071b911565118102000ba4610807800801c4070780b9008148000c0d41c0096002900850042c440880103030345120102080e55401807080c440e14110030780440e000c50320074a0064101c40c00180100c24540c0c04580c1034a64401038405004001c500748007217a40700c5001200c14005000840071414131941c0e50011170300940100320018035250191240c0c0f110b4a001d450a0b225079000d400a80 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 6427471 1250 6426221 6426227
    0xf030a0507020306060901032109091b020705010e0d0b19020f04090b100903060c03090204020d02040503011508060c160c0f030b090106030302070501110709090609030809010207020105040510031b05030601 90
    0x940e11150a80d000c081c87d501d184e03507002008488030110038100d4401c61094803118441c004a0000342040750080c401e1007039a42d00201c005411454107401030203640b802007100c3d4003c0c149a000c0e020040c0442e0300048054494003000d04024080580107141422807901d600c030f5600281c4072014000b44603da85a261807204c10403180701002c054020701c0c03074080701034406420064003002c582e04400041080001d03588114002c040c1000c0003907106101042c102e81d00c0c40030b0343c050425030b40207800820500c0c9050640490f1010188107000c181d5200310001484140d0381406428030085501281445150f1a50b84890103100c540044150b48001c0c0d504106200c0c00a00c855000388110b40200000e900b10f85001f5200c032203601506050041c0d1070039506003818200000402400c590f6003c1001106a25216010b40150b61040d40001d4a0b1400f08110200c10300c00c648555505031035003858140342c130040c40100054240300c9018566a5207455424a8010114420704042d60f610307140c1d203140420001d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 6428721 1250 6427471 6427483
    0x5030906130b0a020a02190b1f080d0e0604030c08150a05091c05040801090605070f02150402090c04050303030a0c081e0c07020316060306030c06030203060d030804050f030a05070203 80
    0x38000042206945501150780b12100c282c1042c0c0d083d03000b5a449903032440903882c041c0b0004075028034984205c48042488882d98002d405a2403644a42009803404181c104417688540210700c140e800203a1680c20781030240b00010b091420141c2164145980c0e52907145042246a0045100382c110241c150489040d52020940c014481d6034104060300302016010390340c4589908d0f05e06816450340f10004064011010350717004210510003030200c1d4085c0e1801c403010f40400d95212002c144040c18614246001003031034a401003903001c44800540d9035408101241d000034018001d4420200004a4251001e10017503104403407580700031030030848548008040020041840400b1098800c0180694400d81002900b0112107101162038400030f00010703040c4180d005c00303082c81804c40d550000d0101d0b00350300f2800849002cdc02100c0281d07607607000140e0982c4800c540c3e295004c6040c4021000080c000c20aa60300580164211a0040d51031038030781d80745512401e50100440d4021034440c046282c20014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 6429971 1250 6428721 6428731
    0xc0d0c03050316030204230a05030c060a0302030a0605040e1507030501050a0b03090309030304030c0807060201020732010c02010207060501050f010207150e100801030312150b0c030403020306010605030906 90
    0x440000510140c500070031a002c060030561030440015050076869200360156000380068000d0340749000200140251000650340c2010700844083d60001054500454141d507c0c0c0f10240110b45091280f0384210006c3d440140b05111003551028013080c103403a544602100d214924004040704001d502d0f03502c0c210f20004180804050804006000b5600c07104070090841e0811040c3c25241e450740d103000c5045000e0754a04603094400401c000040c4065010b03460103e483e10419103401a448140032801c0c1d02c21000080c1c58490b0b268240c041c1e01e1a0300314003101c901e8400d00c01203080742c801c05019003560442d082810050f90082601400d01c07455100b5240104001c441200000c0180c0d00040d4443d01c0383c1c801e92110580484004e0015400740040c007d52280c0280a020411790100001e05070420a004c258002109040c03c03090038185403040b446070500c0d1b07040c00059145003002c0000503501c00c0001b100180810f201c0000141c4042103c203000c1d0800d0b480c0c9644900d4a034170810318103080146 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 6431221 1250 6429971 6429977
    0x60c060b0306040309090f181b0b0a0e10050c010911010306050a030c0306021e0a03140c09091504060b0c0105010302011713080304020a030b040303050402090907030201171005150c0d 80
    0x3404000f85d00031942e0b90481c1d1000202007042000c03900c0781d000514562061088100d4000b1640b01082078100d00c00c2c00f54200d81d90186082c0e501c1d0608410140104c07481c020205400b0b9401e84440e103080960020000d146180c00782c41e040b4408422070030f407200f8a40031a43d01c03408205003911582c25004d2500684402c0c4c400c84801da1441d00d4031480c0d14558400540703501c2d4001107030302d51405403048140c0d0000c0c0e4650a2951840c11290050040034070000b20414203005402141c1c0100710780e41110b07a00407000700390040030344800100090442d4002d0a1701d6109641c0d550000340f034008100980b00c074134501000010558510700000d0002d88483710103224011900d400c10442e9900214041c800c560800481130f169500c3c0e102044040c600e64001030800c002000412040503415040310340b05a2081d62006090344502c10701d02c0e590040741c00000d000c01c21b584121050758030400b4041c0ea1103520a00348540403603481c00442d085540c0080d81c140c08060001d008918080c00b00101d0709a01345070b103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 6432471 1250 6431221 6431233
    0x4020412060903091a0f030a02071208010e060406031211030c07090b0f0103050403050a0309030507061e0b03030306030d031a0d050601030302010e06160c0203010615030906050a0203010e070c060e07060c060b03 92
    0x100c0d175500c12040c005080e80f001101083c0c01c1c162a906648100b5807103100051264000040134044c0710092142e1030340c0d202e900c40011403134202409000100c80c2d0260054000400000b010344080301040304044080c40705220892030000e0421000c0300400030380d40c0004040040c2000c2c0048402e601a000c2d0505041c001400000303544801161513200152070005543c0019142c00c4032503108402c0040c0031941015590f100100303148a0f903018900400e9000c20001050905040d201c0c04100e40c5203506401043c2021803843c02500246150022903106d1800d00e6400780001d01c940500250585150384288014006c15409100e20145001080014100e41c40c3c01030150441010b543d481030208854415800c0031502c094000a01400340000c5007a000001e02c0e20050080600c14003e5a8043c1004046161010544203e0b0f041c2c400804d141a0325a07104801aa03000c030a80c5000c555aa076900240320100c2d030188560000b03400326644084259600313083c110240d03030310200054441d406c1a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 6433721 1250 6432471 6432509
    0xb03010203040b061c0606030b0f060109053106030503040512070806130204020d0501090b0f0904050c010302070c0806010e06100206060a03120e1c0209070815060304020402041206090309 82
    0x5003410f2684124212104c4203004249216154400c00710b481c0140024113209000c005c00043e007844611480c0c00204c5201c00350342c1d010044a4032400d901c2000c0c0c100f030080c9101c1259907200e000c1d80e0700200703008401040650140c140c800031201300d54005e4609400208085c003151401000c0d8151034501d1310007d090440c01c0c4001d0036202c00002c1c0c6046032421100c01c86c001151115010b541d08694510410445903035500d424201504400c0000c2d4454001c0254600861602c0c00f5064043c079081401000d01074603020055000f9844200265a0b042108030300003010b072010000e0901074102510840490b04143c1d0a106040c0325001d00441550044001c101540e124001c4032011250042030b481042543d1203000e9030810060080c194010411000302a02c41c5ca044480e410182d2082e01c40c0e901c0c0380c1e900031044800680c10b4070214200b00d005540c1070140d10f0480701640d0054001400140b1340355944414042e80c8070440c008541154880d291b14051580140700a002005401c0c8041440201 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 6434971 1250 6433721 6433733
    0x601050909070b0703030b130603051e0304170708070603020a031505010f0315150206010e090303190902010512150909030f07030309050703020307030b0a05090d050922051303030b0301020304 84
    0x14010306908403c041800014075202e604040100758000d03242100d850900310600024000c540400e0b039591146c10500f604001c0ba0319a80c40052521401640c1054200006c074481741c103070a148003003203100344040480d4500040c005103009001c4e80e100140d46114204002d030954154000c0380c5046825400708010691700301c1c115518001542c500020520512040e0310100a41e50b000300300b02c0c000361003070000c101390005155030513568443d07803d020b150742d40c2160640d81e120448409000c4803c201030b0145003661a008280360070b105040417824003006902600c604081180c1056442e0070745070303101007a4100032070469045407541018600d80f03c049030885805206128008041541d2072003550300307000d001c2c080b880107980d0040944060564038144120000705c00d0360342006203860080811030007000081c000300c40301e0850300c03054244143c07003040015403204101d00140c0518014071950b01d0240a20035144528444a0403095000f1607080003400c60319105200c90003030b0f204100307010100f60 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 6436221 1250 6434971 6434983
    0x9050c0d05060411070602031801020d0905010e01090302070501050304051c05210412110c0301050103080318070602060109091110020102040609090911040905070909083103080903030405060403080405030601050909 94
    0x28101b903002da5280c40d013080b160540f262040d4a50300319440031a95900c1210560089000103000e100240b00d40492280844d088401c1c1040060160f840050200100d50082c40550350140c0a8403e60701c10304100d04104804042a0300100002680010b50241728501c4042205203400b00c00c0c02010305103802c0d9146840d8081b112144800c2c000d036820808010700c81008a854000400760082c0403030359503843d200b0002c0d0415600da100c01c0000080010049200003144411180e0a5000b4000380e440c2180030002410390a205860182c032204d83ca445507100c1c102c40c0020034905134001641c2c0d9190440041054043d030700503004c15401d04208101040401e0031400e07081e84111342c0022001c642e4a4050315000040d0308c07810102e42054140c07010b0092000c090990000c40c00358040810451448000071400c40300100c0307100700203d10741072021914003005000800d0015048914154a440002e80340d034200d50f00c04c8680d4100001d01740107a040071300607240100f0041c0e4144485040500905031640 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 6437471 1250 6436221 6436223
    0x2031006110a050a050a1106070c141309030210050c040806010504020a030e0a110a050a05100f1809060f05100203070f08040306090506090616052209050c0d0506041107 74
    0x4a07103448401c1008144044500140e2120445050300410303d0000c0d203c605011007607450101a46c1540c0c1c40307080c01012610754581c4407405602c1e03182000440e1600c0c0315006813140d0058801c80d49907810800910405221500a0b001001003440000e0120150790001300500151301c400e001c07c21103441c2c0002c003981503032001c54000d0380300c4089140403002050169070290051140b0100136061060204c400c3d01d8031501910b1264109881da8103001725001d692281d00c2e0000000610140d001d4824018403400d108103207807500700c0740c4a07007684c0008019150484100c0303541d1000d00f0440250b291035104020032003510144141d800f5400e0203500c3c0d00420a000d4280ca1203480b050003002074003000c56000c0c5501100402100089040441d52800119900b503003d100394804625401b401110560464030156500c034030381003440f1006030100d4074515960500d856282404100d814490203a140301e1001c1c0340780b103501c4d00042c103121000d40321b010304076501452624010820b201d4a00040f10012 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 6438721 1250 6437471 6437477
    0x313020f190e0c120106050a11010507050426030a030b030606030609060c13080105150102010c0201050411040b01090e0c0c07060c0203070b03150d030807020c060906030103020904031e0801050108070302031006 92
    0x2d03580789402e8201e14820744007000d03011020b0b88000308400d0b4111010f4200100c2d1580d031100f00501c09400b0900b2244143d8151002c10000d0000300840558010260714180d402079084030741381c051501940c40c40c6c000004c0d407004641c9030510403c00e0300301001015070000d0304400814040c00e141011076200d41014112208850300010001c07180d040013aa07120003480c0c0b48000300130515044e80d04484201c106c44480d4010f50922011038412841401618000d03034204000d01015410b80d42080010304c0031001141c107000c920b80c2d001074024540c9203454811010300e0740039580e518500d40c102d400c225081d0005420700965201c05000358500040d0001550025a82265252154055202c00c1072080d6403050344401000724600415a1090700c13180a02e502d6004c8403e00e00700c0c20100119809440c0205070003482c184010809480d1000720f0640082c000d0400c95444040e618000701c000100d5403486010503901001006203583c030003684c40e0b1004041c5411415801c010340781c2c0c0402c50703d9106540030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 6439971 1250 6438721 6438749
    0x7051801050904030e0a0806010821091509040b06070b01140a060f0807030b03030705070906060f140d02070b090714010f050304020d03021c020601080607020102070506010e0406090204020313020f19 87
    0x1464a406c88410080d1200901b164280e694480441c0e54070721076042d5000c60428001c8402601180c1d1409072084003100402c0c403002032405060124031500000c030682e510907240c4200da052902c42c01c005008940c091821004558101002c000d2204d0900c0b20036809020016810450168894001c0e141e501581c0351950554480749811400351140b80e000e20b9050000084c1c030010407800040343e20850302c09880a0281c90364618042e80c0325401c50340c0c07860103d80c01c1010b5194400681005144448074080014200700282d103e00c0300d01001100d203105107a120005c144070700080c094050407100c20901e0701814441d402c0307078001c10798040074000a005030080000002014024004103484807025400590030780446000290703a08020b10070062680a10340204009600c180207e8845035007100051032940d1034030b4108996200018016108141c5d41e200310b100507540c41c001180207980d51008411580c00e607004005507007020020141c468041d0506180e007640600c000344d41141c046035a1301103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 6441221 1250 6439971 6439997
    0xf0608060f12030d0605040c0c0605100807080304031401050415050603070302040c05070c0812031b040906030309030b07030603050601050d02030c04050708041b18050601030b030105090705180105090403 89
    0xa1800c404000b50b00000d034908100400324008007500003080c0702c2000f40302d180d58a50900040300e0501d0022000030f8000450308001c0b55032a000150460701c086400340304503556008107400c0c1945600f002d40c071500000703810020f101d240070045011021901c02003116003060f95074501d000302070102540ca40c684840008803656030a10003c801190080c00c14400c8280301c401c02851648140c20855905820540104c0c202d031002602c00c10a0071140400e6245895400e404c800f01d00c0d80808136511400308100209a8403103600400004501c252101700c0081d0540c9480401100c0003450902090f01d401402c202090001400070304440090300c91500d00803003400824145030018403080d41181c01d100034003400c1a44041d410b03200d14000c81288820031100c0d079013500180a00d100c0c2101c804241040c0ba0741004180d8031151f000703c0d05060010358003c2c1c1e603010070700790f078403c4482e400950000b8208021905020400d1a5a600f07041e250000035810500000c00604000e40090100908464022 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 6442471 1250 6441221 6441229
    0xe13060b0d030e100302030402100309020a0b071b080c010207030b09030405090907060e100504050108060604032307080c06160305040b030c03010302010f0806010804030e0303130603060302030c06040f060806 91
    0x55248080030303000450703410190501a041003604404180501515044070350300c0f510901c282c82c000e5a00a042505004d1091011005070805880c2641e01000c0e2172000503c46000000611780c10784518110704004003c200c41c00303d032110542c07146046421032548111203a0340803c200c001e40e40d020311450b02a46500e05164518041c98003c039401030040c001303102c666240040c0c190b040b600c2e00da54580900b46010b040c880c000e218040a0000300d2414001402690301038403d0030744c04130018021030b05055503902c801d040c1c03240c041c1c034200c5e21442400a45652000500c1b0440140418100500074000120b0100301c040c4503584860700000c3c40d120181e000c16100e14103c800500b01200b105880f42404141c0c0e030410741c000c2c44102e003c1000c40f003052444901803851680b248005841e18400b9584645042e144030350003010655040c00108002c0500b88094440880649829940080e07841d09510615150100040b4428400c0b14180801c11034003104914840030348185240102094403000045 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 6443721 1250 6442471 6442481
    0x306120309151309150308030403120906020307090605040503030d0b12031c20040e07030e01230603060114011407020301050406050703050f041509030903060e0a0b090102040e1306 79
    0x7035901c580520a0044a2401c440242c03030400e25000440e00c02950340c20400c01181c420444407510003a81141c10004589980c001d0341e400350090400710b0100b4034414450b07044845c0e2681c00c40b9078a50200902002542c45103070b031b0024205d141891032030705080c040003d80c0c0740110060704403810384900c14a6840c1e107920003402d04e092a044100c07178440f401b00fa4207101c8042c02c0800c21000c0c0740b134000701d03040d0014122940c075202007800c0b00c0c0e5032a00b41016035014012038000c3c00c40c424943c64100342091a40b0034031802e141c651350100c100e41c842d50420303d5010080030180107644290708c01d000500000300390a9240e180c05100b400c00c10105401e12000c202e20340035a4102130f500d546020100001d012803074012512a49069030204000c1c6e03602c85a00580103c1901d018000348040c00c0c92a8004045502c01402140241010306200e40e90703a4448058406500e600c44d5280c00c500703140010004030410482e00030110200035400c0a051010190b10440028212001c80d28100c5551040c00f48a89c44 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 6444971 1250 6443721 6443737
    0xe180c030303040501022104020604060c0204021b010204060207050103090803060405070909050406020d0513030c0b0a09080408070e060d1101080601031413020f03010b01090902070203030f03010303020a050c011403061203 97
    0x3520b40700d1416040c858000d4020a00321030152070354840d01850100d1344940d103807103640d005001c01d09040c01d05000f02c8a01501c608100e0b08254208030701c1841211440d00d45102801d58400540d49506002c0000e0405410b44d014a06050403d490540010700017015242d0010041c1c40c00126651510000c407003064050f03014052061130700c0c081c4004d10140340c008000b1000c00110500c10340d250720040310b0701103c5071840500021492138411340025032000343c0d150401d040d020003280460550f00c40b040a5403060b484003c0a911640c4100f010440c82c00100707901c4041110815038000342d544840b12103004050369241040502c3c00000c01c10f038080e5002020211106040c20f030245486400705059118550041e0310406c03281a003203000e0700d014044c000c81030006a48a40312240b8016910010350891107080341d050105011900c50b40030390328050b41c021806035006002000c05410000d0a1002030341c02681041a0341100070304810004080743e801000070344c2c40101910320300d41c07041e06600644034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 6446221 1250 6444971 6444973
    0x90105070206030907030c0608010b0316030e01020c01050a050601091809020409060912020601050306190b0a0b0a0906090e040f02010503040c030501051f1e060c03020c060409021803070e180c03 85
    0x1c140900988002809820b46e44030301d04c481e401b13544921302540d012409118143c000402000019449005c02c603284071921254100802c2201d0f4100848e403da800850340f0b01c0c0560741d28020040c020001d4040c10b50085400e017071a4034150704014070185961401b0010410903512810000c00715141c5500c14141e243e0002d80400c00822146440c00100e00300c0b44010300103200300400842c00380703404221707030b405a0b00000c00c1644a0720b503210584040c0081046d0594480c00e040400510200003d00804400c140c03951200d80c41070070000080c15148883c1c00c0349807460400010080004e54820800340760701c2d02402c2c040d4a07540e440c60408100c455036007000300a07500703100c2800145441e0141c0124000401c1c10200c110640b10340f07040c80e61810f044103d501400340454101300c00d41c010382074000160b011b88107a550450f40317400401c480398042c0c2e01140c1c0d42d039070000d94601e030104400690140e07268120080c11003140b9212544a408134082d0021900e00c514030204414032004014441c00100068 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 6447471 1250 6446221 6446227
    0x71a040605072604030b070822030c050303070207051005040303090e040212070608070f0305100521061906060302120a150503010905060603010b120a030c03090b0c0d1101021806090105070206 84
    0x11490f03d58105100488510b001100480c07003075401a800b441c414160210b8131071402c0782d00001c00241841c03041d000e601b848910314559001c103409100461158010f50028200c180c1303000280701c642469030760341d075080100c140b0081c00083c3e07101c0380110807140d81c0c202d2080e00351900e00003d02e00e0506802c0001c80341c4641c500c00030303c5a070046642403140803a903e40c2e61417940034550036425500100d605145080e803580061055161880c0c11694040700420410100013006c02d51600d03140c000c0c0e5030400d0300c2403803400403403000c15280200d4010b00940c0c9070a5040518041d0710120325803014203505072044c0c940411b802c0101c88800010010803000b00284403071206414000d03200c1800360b41e198000d5080140b00442c81c2800400c404c294510080203200b20082920102d03200324188908900300002c02380d000a54000e2003000c0d0854421280281100c2014450082c006081c1c41142980c141d00501c094001c0403240e041c02d009001080d00c0240e80c0c0d5100d40700403500c0d48100d44009510801c04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 6448721 1250 6447471 6447533
    0x41502090103290915030606060c030708030106030b03100c0e09040203010b030304060504090e01050408190c0f0b0604150503030403080c0703020a17060105060f030601050a02150901090302071a04060507 89
    0x4849211a4065803400c613542c4400481d542d1030f5641182c05070f05648003202084039414010010a0410048001c1e242050301c035a8903824603a1003130b80020b0000f0b4a6190380d01c4240b8048c80000540071444408100e168039541e00a0701402014a0b298460361021700050b082d904d080d0000c00f1466401030590380e440e9250900070307105400070b0003445440340c606504814040e005101e0706020381c1e0000c0101d0b00b0a500d07000c042d044a134418100608100320005120005403014224081c010f00c030b00c1d0300c10070780d1401d14240801c4862a5405010f10050b8032010045030720007008840a8a400050003552620385200300c600e00495135000070340081405c04005a00c00400106459194480003a190181d0340c4804010550150181101801000300301080071580148010202c8d201c01d8010759503124442c140c2d01c0c4600200702c402e0318003651502c00b600109039041c4407072805000040d1540c0f01501144c0c0ca1100c80d40581d0182e9001d10000184000c1800740e18a61040001c640020300b03019103400d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 6449971 1250 6448721 6448781
    0x110a0504022a0102040302010503160302120708040506060d0b06152817010302030c010503060319060b04061a07030c080c060109090309060201050f040615031707020102070e041502090103 82
    0x1151941850b001400e40082c0d050103010f000715000c89070143c0d642400e5032034080c038580071462640d00e404185070f420480c08400700300450b59a4401d82e4140ca490000d4503190820310301f002c000500d41407040001e0280400020181107445800400903a54501c11143c0246500c22034410254145e01d004040c3c003c180c90443c02510581d2400410b50326625410351004882d094110280402507040c2c01c210300f111401d5100b00c1c027031580490b004088030b078801c101541c40161000c591800b556040e44414a401450070300340a90350003001e0114040c0c12017400103d4002d05801802001010000c0300149041403000c6101505c46100790300003039a0155079141c4800d401001c0c45d2400302d010981c82140083c200d0300621825204400c1c048130a6826a20760359500000c4c0390700c0c2140c2140340d000600210200c1d14520f40c1112401c50050000d50790700190001a240c82140d40c08031050b007101e00104030010707045a05044500b01820b40150329140b500d00180c01078000e481c1d5000c08500c0040d012003503000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 6451221 1250 6449971 6450007
    0xd05010e04030e01020601030804090203060103021b010621020306010b03040602070b150307090203010602030a0e1302040909050f0601060c06020a0e06070b1501030203060102030406050d0b04020309060711010b010804110a050402 100
    0x80b0a480d00c0b43c0f601d0000006989443e0248005424818244404c202e02c103282e40045901000501d030040c50a039403040d4402c4220148056030421360764907407081c040140c03400601c4400104c241d881400004083e800030744c4e07503401405250710b01500480070800300141501500c880a5005c0b400717070b5052406418460307240c0c0598800900c02e1144100c001000f10041c030840e8103a6900d0fa0180d85801c140240c02c2d900112400d84041c0c10000c50804858199102c2c8003030009071600b13085c00320b00802942001c03440c0c4800031201d8503142c0c22090040000e180c1120802031440e81c070110144c3c81c0d01c4802d034281c41c44e0900020083d00014001003580810540e11021441642c3d00211410f144600900440481c01304460480c0941e104001c180805030007400600340705454a10045040000340000c5001e07078105440c8226240d100c00c062000f0184c1040d40c140100d800d04c0d0003003200451000c0000c0000d08054001f901042850400c02c00c1071b1144400b92002d000080d10a540d81d04410840703600001d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 6452471 1250 6451221 6451223
    0xe221404080a0807080103110105070201090801050a0f060e09071802090405010e091507050a0c050102040b0408010603030212070c050d05101104080c12060106030e070909060603110105130603050703020d05010e04 93
    0x3e00054009044a0b004400e03190503250480c419150400c100c01c019511648848020b034188900103500240d410002d02865109400308032021030220100c1c110b03070042e242e15410101401e00c0780340410030407240006030030044800c5200c00b445804550031124000b0b22074500b0300380c0c22038240400810202803103203046000b40044011600c800c4035258004ca900c550070356581c80007580410050805910569980a0b0359004100042c5000e58412103011154080d900c003a03940d0351074440c10400d03d5014480e1009804081c04603510308011562071200280340c0c0d02a9034480c0012504110500c00308010bc8142c01d40c5082c42009442c42c0c10012020607000391250100d9480303140100c07021410191100c001001d0154018012642072200540140c0603101e2004118860140001000002d0f8040d03071400034010000000c00c0c80c00d50400d62020f0302c14583c8030741400020060b0442c0340301d628118004035078480c503001a690b207904504801038803981f1080c0d224241000004144456000a542d000b6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 6453721 1250 6452471 6452477
    0x80703030f0809030901080601260f04020907020d02060403051305060a09140d05030d0b010c050d030c030606030203060303070615120809030705030606060304030309020109030804090c08070e221404080a 89
    0x1603a80d10100d603913a10490100d240001c084501041d015409802600724209120320889007180074144c944a1000303040300c6045c4141d1110080c001581070506c4130680081c204c4c4007800d041d405800002e5a110800390009080000000b403449445610b0b0040300007600e00104441c3d030310700001e1001003644640e0300481030058109030140b00306c3d00c0c200e110a1a5140d01a000d0350a10b00b1640c0340c42e00500921580905200c1203074000e80000304180844080c0306007030784001451151042d0010112005174120006040c41003082c85015680041626402580248045800056040c816850a045a014a80d03045c500034004040000f082e025140403e0141c1c1101c4405503201c04069440320150f03103c0783c2140c420804074000c28881d8000495030790040c14112480e550f29900d24040351322a501124110342c2e00c0d606003000d50b078000e201942066152401c0b444128492001071860f0603589170074402d260000410b118400e400360000100002455580101490142030900f0140d01203a006800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 6454971 1250 6453721 6453737
    0xf080f0a03060504020a120e030c01110307020705010306050a15020705030303010b07060b0a0302010e1201060e04080a02010c0f02031c0905071401080703060807030b06040b0a080c03071205061b04080703030f 91
    0x3c1e0515100380c0d07000101582c1c0d4580600c8000d41103800815603205403240d940410008000c1e008401d010303000858500c10a882d0703032442c0ca00002030500c3c005070080ca0405003000b00130403265441c0003a15098900e200b1103401c81c51424070082c1d00e8220b01c1e6200e190036010200000460300450f80180c042c8501550040c0242c150f294100610352080f400001e01046075000784c2034039824425042800c81919400000e50746882d0802c0c0b540284003290212444e0000164001d6229030a02902850b80e85900340003040da000010080d4403070180503201d08201501d40128800704050350050240c4940103400d5031050b0f500c6900c000d90307280d000c0c03101c82e010034038450110300082d03c244a102c1c1111440c4002e4075006081d036030351100001d005410396074042d8982c11100e00030354654640400a049917801803042007551001c0c1410510340d0751100e02c4500c48441c409010802c0415500c4d884403001914078882d0103c082070f0401405241c1288120344100700010040640243c9200b410100940740c00310 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 6456221 1250 6454971 6454979
    0x6060307090b0d060c09030f060f0f0203130809030c090108030a020115080c01030c0509040213080f030a0507020918030c0105060a090207030e1011010e06010504050903070c0e040f080f0a0306 84
    0x80d0b900701aa81900200301544102c0454030076480075520044034038110500300da0765280c626208031054420f80c0d100b950b980409555144a02c90750181104505045d8114640440c1080c490120150054030910f80003d081140e81c1d4140865040304400601501c203079611141e8890383d03600106800340240d07103490080920311001c240c5110848103000300504200422900450140405050003800d0001c2403080b0440c6a58500281c903d00d2004214403203514074207403400d407610083c1a0219030a8004120040a50b64000101c914a03501650b0701f4925450750340c00b504020101180004490101080d010b455000c1034100c580140e8003145c0f000142500c410440c0b04034810780030010301050301c0c000c1d120080c1c00c0c030300004400326080d81440d9990300d07041c006135429104c18042c08050750300b0980042c05107181c0791041540001000700150308100d90b542e501d00120855000d038080740b84240000404001c90282c03002221944081200c0d1103c02144982d21a600040d003030138086400d18001107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 6457471 1250 6456221 6456239
    0x1205061512060a020d110a0c03080604050601200a14070603061a07030f030b03070f030303050a0e0706080c07020301021206090a0905030f07020406050405010f0501090b030108060408030c07050d0206060307 90
    0x40100c0c150715000d070440740c40348256040254000c0402d4036400340c407281c0c50800e0030094009002206401d840c4c0c5581c4001c945401008144028403003407180c2c5c6001b042c0100781c0d911184c00840c44058409100018404020040c60107046074401071401307004501e50300c0c4a08000c06c070081182c0450700d0920501da203486000c21929140440245250070030301040002c42e20030a00841580d0321410300040c58500c00020905001640d00f000c041450066010020164144540c2c0d903c06111801003081d4007401d14a580c542200740700e50402c00850401007041191b0703403000c450030540e0060085650700012241803004c10300483d07000f07100348005800103020b06181d010303807200c803544207000d907140040002d4064415002480c0c10313a0415a00c900100c1c10392100d1240d0f078040c180d210a24040b5501c0c00c1c00050444d04260822244040188010000d26400081154002c1e5111b0704640d1290340300b40410f502c80c052940007904520480406032403181c0c0218103203000300030990554520356114641170b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 6458721 1250 6457471 6457489
    0x602070203120307020d031a0d03050c190c03030e060f04030b0f0106030c020c01141303080301150c030801051309060213050306150108010e0a1b0503060f090601050d0504060612050615 81
    0x3c0c00146e0031480c11010324a10070741c0042c1c108400c040c480780090120601050140841501c2100071600001d00c1140458080103507460046600c00d442c02c0ca0030b826a120441d00380d0070710008007844816003030458240e070b40005880d4124124004c480c0c4895603410b101040880960f0a18000c2a00c000081205032080c0500001e000c42da40007070000c640d00c00700450f291301d84007030194230340b081c20320145109040c019150b800850165811507101e5041c80c42004000408a07815400d016803c00050002034201c0ea11504490044860884c0002b810707032040b0107003d181000510181c4000f0f9084000c04a2070301900541d0025011035072241d444100300c00419000d260120701250618004000e1101d0341981142d20401411b400704161020300c600c1d10503402640441000300308080100122800c1ca01090030081200300c80f828514202070740042c04a115a0902c0c0000f1501d940008040c081030340c004400030f04209065a02c240124100240c4070070301a29001d008000f003c91815180c5803e40407 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 6459971 1250 6458721 6458731
    0xb03181902010314061c0503040803070b04050d0507030c060c020109020a0b0304030210020405030a0b0603011107030807080f010f050103020a0201110406020a030e0603010e060603150a14040c020f060705090d0f06020702031203 99
    0x1c99442d006c21070340510f028039000c00c0116600c1c0b2081001090801060005e8061244503418404103402c00d8a030047c00c08024441c03c408102003806644c0100b54010046031405400590015910700e15003012805020b407648041c2d00407681700d0000031802e04000c02940300306d000b58240c07034200385880a251301f41d2080c3c0c4289603043c0e210310070400c04119040c0c84603400100080002036181181d480b41c4503a070300700c004154040380c01c01080144e00c6811000d0644d1002000c0600e50303696044c144125950041401014101540401c016106038004d61010822190b8050b242e621240e0340c80c00290b85492894080b00000d041246140060500e8011f80e03050703845c61181400d0340c0e502e4174188100740c0c000030300e01c05460840507200315003a21135400c080058050754001c08880c41d8210240020f88451032440c0085503c00104610000390104a594104809203010f5136200000c40000707101d03030b1412001400506002020600300402a40200002403090f0140d07048031420745158072540c041218 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 6461221 1250 6459971 6459979
    0x603050705040b060d0501030804030215030702031902160b03090d020c090a0b060d0203010902070b13050a0201050a0207030c090207030207081606080a180b0604050907050a0b0318190201031406 85
    0xc8184501c0c42c10740c003c1610701e00060040b038100354408148070251075080c1c1c0b040da1280b000090500c01d6040c42d0610040c070b414881c0b0344d5895401d106400070f50301c1c030a0041d00c03150080180800c04840f44241700c1e00325100c00c403d41c2804070300d1326100703861000d40c4246c9030561503114071070102070306078000300300d418424100402103091035994000b410054a5550701080d44400b003005400c2c1d41c08118030255018013211200182c0b58101840c0c492103028010385014130742c08040c1440800a400021011103480e42031812030f0b01c4443d1680240c7c608034403600020501d01c074400c80860100b034254094806940681e0840c1c4030303160307140503454031391101c00201c40306045001c1d0b00784600c07070044c800c40380c00c20030154000a84030080c071460400c00070090360448110380428103005141c078107030160980007800880581201c610b441c0004100181c640b1443e0144680440001d00e04010300d015503000b22140400d07540f48010308101000b0221401c00100c1c04245081c6800b00d0160f00c1c0008203202d508064 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 6462471 1250 6461221 6461233
    0x140703080105091b07110a05030d0203180603060904020409060b121606030212010605030709170102031503010b0f04050901090203060103080c1c0f051605010606030209130e030a05030405070503060408180301060305 94
    0x21711340040c1c2c6c0ca500c01c03916410452030b00e000603075524100320701e445842d0f540e4040c540312025040e020606249096280d8070a510074014888165112560b090300240c1c1250005034202e82071800d10041c0250310301c620b031300416411120340f00c0c041c041801001410b6414541c0401600d40b50181e00b00c0c02020740c81e50300c0002120050159034014401140c015519080081c0030b181d541c1d01c3c1c1d80c040c6d03500b40500c07410740e50003200740f212801c4450600f00f1202e20450003448030803985801b140f03080c180506468810344d02c2d1408500214000e40c4680070b001d8001c0c05480c020743c0c603800c0031030995001900c800150b04c1485c10203030011900101d245007000d403d44e10041d0340071822404450b550400076004e01901c031046400c4c0d00142003440703200c00809a40d00c0c0036880300550030401810250110b54109101e0510200b02113200300402145c042060606007181c80e62241d0912510b002c004d50480c0d50075214401c18002071109203005407948030010013045401031a5001814246c8045200c02895544030b1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 6463721 1250 6462471 6462473
    0x7061103090601060c05030702040501030311010c0201110f090d0b0a0b09160e010e060c061503070906050a03020904150e0102191b06020d1404110906060708030109020a140703080105091b07 83
    0x105d00750000c280c001c000303d0741030491940002d0100c40382a4802c4001c03c0e002d0405a644c100c082c011988166030500007005031504040500080388510641070018400c00540c2038203954401401510158115030900d090703240c004031000041613811011031207000610005140c0c10f02440032039650000656501206803180f40c01540d0700c0841d051030503489001409500c8076824100100340c8140803c0f44201882000c85c410715080124503041000c48a080160a01207030b1201a00c3c003045030390648601000c2c0d1b8690900c10b0b4681d80300b5840e1501c01e800e1440d58480404150040c03e100c620020380980d15400f4940240c075025000240340640400c0c0f00c0e40c1340c010409960203402c12101d040c002150078003458410b07605a0a0071a01111f088403130000d401c2c520705000d280254050fa054510a181070440e86903201540014850b4840e01c9400141d40c0e017099106158650300c41c00f80b0010251180c8031840e01822101c02401214000e0320481d0020f00308640b40210894031228001d041403401c021 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 6464971 1250 6463721 6463727
    0xc06030a0905030d05040b0109020403081603030603050d180e01150305070201060504091a0901050705180303090603040614060102010209060706020c010e0d080a0b040603020a140103090204110706110309060106 92
    0x144046069503440714803001103801400240341c005030b80340000445103024540390101400682003054001d2040c8004d00000d0151011545c0d003152042096020b500030785000c8024101c2508002c0060260814202c0c070342d0340001c1011110004030301c02a0b00b10351620b0707200812103401d00c45c2c00844060900c008081c0c600a611503508102c0520010811070b459038082802d803000b510049a9058581c4a070a080052601c0386581003400780000384183c0c10140802401402695044200860038000d4495903607000c004441600305c014041ca0388a00d0141826001401117212410a81803080b00240c22507106108641041c140103001a080162030b0b00c402c8001e412004048556643c0e0f9030038099000d03020411001805519641c040151405d0040d410903540039140c5940202e04002040c00140d44240c002d1060320042d085607a5100034400c01200039100a079006504145002804a05256040c00408040b80a05418060a841c076400e41c01944011940000e07240c008000600800348 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 6466221 1250 6464971 6464977
    0x80601030b0d080f070201021507020607141309020406030e0c030304090906060f080d020d03090f080307030f0603030e01020c0118050d05120a0c0b070c02030a0308090f01020d020a0813050c06 84
    0x180900b1210a441c015600e50032280c0c04600b1200c0c2618003c0340740d2045603810480424060030600101520341000c00d03001c0c7d0f0b94200078006d54103010f034120b0300c081c403e080481a1100101d95403028560760f40c0c2e4040503002540b1502458001a0030301500268445000078904107061015008500d050300e881076040007070020f2001185c105488040c00224403194000480243c051031020b49001c00000c1d8000e458510010901c200340750a05c0c03c1d0301c001c2800141c2c140606d80d0480d040751390320744d15100124028004070305041111807078000301100385079109000b5890003c081e021250702070f1015005440c803042440b0b503911180030509082c0311500b044810300c2c07182445078044495140e000a516a6142c1100b400c1d100080c0300c88021200b8005e401c00e26903003206076410245511116900880d0f01c60310280c0010301400002e07004520b6a010030814004c2d1505080c008640320100e11404001951001c15100001141c07900403d081c6000103800c4030b0426400401091662804400e00400e90 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 6467471 1250 6466221 6466241
    0x6010306030609050d0818030d0207020604080109030c060507030213031e150b090708130f03020c0a06030515030303010f090e030f03160206010e06010c030c020609030d0206010f05030109020108060103 88
    0x40e25100000002405030146100c11403140e0081c00716220400002028014000c040c144140078100f181d030200ca07400302c212a1400c401c04d1001d40d49035103900100d0071130700c610b031b01031082507103480b54520a00d03034400c8c0d0000b88144194410311594466042c118141c0c001c0c411030344503244400e0003c00014002000300d10a08803015468000c0070340940345d841070002d041e0109207a550b02c80003003503e6883d0000000e0741c80942d60a01c08150308000d5500d4800c400c1030a40100703a21240081d090038107000300800d03001f40c2c41c000c4c194030229880b007000801414065910b41e0311440080c50800c6140b0b00881900e058441c01010140c1c10b03840c0c850b186014001e500d0244a190004021030481c52490000451042c12010012001d01c890007000a1a2000503032104618503000c00901240e683e00c80c000d00e0311950945010010200356000050342d40c8188010300d58103116420400c003030b4503008141c45040780ca0031050f800c0d9180da680141801c0c5c0d480b50b00000d00040b0039100280d455806980300c0e0002c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 6468721 1250 6467471 6467477
    0xb0603090d23030c0307030606020a080909100e0901090309050301050103050c0d030e060301170d030606091e0509040b040b0c030108030a051804060b030109060b070b040f02030a05100507140c0d080601 88
    0x85440744800180d0343e000b0f80700c048407058008100404075030140580402086144010204c5101035180c480c200e0041e81c0102c0d2042100754041480c0c0d52440701002c2c00303040032165003c40e83c2008046180201460702c421008a406050002410724040c03280034122500f20300504400000d1200f040032034038111804405200a41e0703145890354480c5d20280d8064540c9042e02c0180300140900b9038034004103450b42c0d0003094107002c018841980d0082803802103400d80b10340c40c00b180cae0494921f40c16501c010b07002190401c280c00100002d003d620803503540940d02944142a890701d6903056084a44424001d07505154001c00100001d41d100c3c0c4002c101880f80041401480111500060f040d107c046d48085c4c0f10300408030040c0300c0c0d000c01d442100001d0035004405d0b481d01d030141d9280001100e00400142010110164800a5413000e0010f107400ca070740041500c0c402d202076066100140301c20389117000016055100380340347c807200d4030490306903d20300c8004190b94500c02e00201c46652000384400c0c10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 6469971 1250 6468721 6468767
    0x12070807050d050f010501030b010e0c09010f03020d020c19021009061d01090e07030516090501020c04050408070f051c030b010c0209060120010203060f0411070303021e0a020f010b0603090d 83
    0xc0941c281b0600b40618410404201c41e54540950041440d101a25501040034100b00010040c0e07002842c03080100f085050250701d84280c420848024040c0100102ca50700650350340056100300c455016001c0d81c4200c410910180713039640125108540c40c0a01c0c40818666440310a512541080340b2541e1001490444881520b401c41e04a966204bc0c0c0c08802103601c80c41800120303070015005081c901600e15000902d0362410000075541c9007280b01c400d01403030341c4a010800744500482120a4203404c01107c800f494010f180c007654070b2880840c0d00075000001000745074402c6c030900034170000310f10503901c6924809581c0c0070002c0004001d440c59040c4a0803501d5a171604c50001120342c1840c03455400141c46e07181071402c1c400c0506040446074030451900103e150002c12030310668150715098030340142c580001e0054402d04654000200460920115100400701d50014000316013454900090114200d04800e00415010941d800ba2a03508205151022141710b00785c1806110800c0040d041 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 6471221 1250 6469971 6469993
    0x30d050904060314030703020606010201050702190809030d020f011802090103060b01030f0f06030b010e0601051207110a06050103061409030f070201031103010e070f0c05070909060f0c03060512070807050d05 91
    0x140041341968200c03100c0d08045280b030180344d01031210527801242800207205529140b140292640d0341641c241c280c2e403075102a10014401c01e0b4003034411340000507040b01c40a540120b8040d503551010043c40c90550300f80545180ca200716030707515480d015809081c440c81070342035540700c0d03015090a12031641003595408907802c2e41001c80c00341d03c0d402b480c0d215000903610b0640c1012040d070702d41604603500e2081c030301c000e2102c9640d1000c200e80c461095424010802d864201044810308089006c0c18032a20070000e070a03041c0b0140c0e0b8800f0b81200d1041a040000e20f5404041c80404281210a014150014031181c3c05c981500e1303000b041018414940000c20034640700c40c40302960001c0e0090300341492018104641c071b903004100f0000c146502e0403c0c81c0407014079550681d03143d0303003030048044d51910f80c2114405c001c040d8000301d41e14060f5020034002002224002070040000d44a4640318202d1850a0007841c000481c6e400300b9541000090070155080c42c0500501c590728810407983c6101e1004203031703 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 6472471 1250 6471221 6471233
    0x108010c081305150103030e041103090303070e18010605130608040201090e06010909060e06010f0507110d0206190305070315060215070509030d1112030f04020d060608010f051006080402030d0509040603 89
    0x85d029502c40d498090040c1517031014042140c3d02d0003044a85a001042444140c0390000141d9911440c1407402e141c2c20200fa80102e00328400d2084402e2040c00c1001c004290b00d50064090260180d118801c01c240e1580c6413011607502000f0785010303000c5100005d060202075404018103a01900c1810032903206940c5000c100101c4109038042d0a407402c20409100ca5980e202c0c0301c60504145901c2c0c030f142400c8217603c58410002501141f80d1090320341c00865011522090150303844a810300e0301505400710307401d07000703070140808a070220b0000340341801510303c00c1004800c0c401a41c000c3c2d4020080441c04600c2c01b41815000345c85007003440818004406141d40822003400c12005540d100c010b480f0098505501d403113001c2249420001c428420400c150110050341503200e0780440303880900241c13504242c4002d03c000d40080740d45509113000001c4025241c0c10150040144030030280841e43d5602088882d04004e4078000e502da08214685403070b40e803044002d01001e4800800c00a0401e40c1c2e680e9403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 6473721 1250 6472471 6472513
    0x12031a030a060b0405060d020a090b04091a06010809030f041703070203010c05040e0604111801180f06080609010602030a08090102091003062303030a1101150b0705060108010c081305 80
    0x49030001d0f11880680000c2c01c01c2c0c021030360040e00941d0b184d88081480d03030010314801c8003070140780e1005079202a08042580e44d6005007000c0b640000210140020000c600c00003104100c9031107000c1002c680208091600c000100c403480c0110782c81243c241405c00d00110700c0030540d441d801d00c0510042c0100005aa02807040c000c1000d0b040c1c031080c2d82e079443c0044000c0200303c0240024481c5140074080b2440c1225401100d02d81ea00744914644881c05290050f10404900f0054042c5030311086008601c680c415000325041d903001d9150300c0c1c1180d40328010060410024000c140c0103030014130003401014080c00c6a03a420012010000d81414040008240600114204800040d846160412030340320f980c400f4000c081e44e074100c0250f6020314480407a50b01c0c41010070100c00c2140101884400850a521071400e80044180d51070718641d40b000d440c4201d0300700000075116801103070000152001c051180d41c3c804c54454a80b12805e54684400000d2640fa4050946030360064140c000310100c10000c070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 6474827 1106 6473721 6473723
    0x60303020d0c0201020109061407030f02130905040203120a18050303070b01050f010302040e040501060602011d060103031b120908010c0c020f060d0207051504060507030912031a030a 80
    0x100e0051150075030288c12030b03140006180c41d040080341810300a0302d1956003440402640078414040f407143ea00d00c1011111003400070001e5144030b801080d4081d0008040e20301645210300e009852354400340b542d500003070030100b941207201254041c59002c1d02041e4011800c104103641c0c0c90500440601506102c1c1d8080468192540e1180d012200134104d411100c0402e0700301850700320f01921031070181700055420007450a1543c01c00c9000021034000f404001c21840c0d10310340382941d00c1801192648601010340b020900450780640140326800207960301e0440340d0b881c200034030f403c598581411208100c507000c0c001c0056a10040c0402e40e02c03100310b45a642c0c0348490700f4401d000f03128101d0b00070f0031400f0b41030500e9001c4194040803032040340640c8081c06075540d01c0008800312440079030f00a0241d00c882c801c664549203e9070081d2090f072514074280e012801385000181ca420130b0410 = true := by decide +kernel

theorem cover : BRFrame.Cov 6294971 6474827 := by
  have h0 := BRFrame.cov_init 6294971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6294971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 6294971 ≤ n) (h2 : n < 6474827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
