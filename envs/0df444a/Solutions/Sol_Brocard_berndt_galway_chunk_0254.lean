-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0254
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:45:43.546966+00:00
-- url     : https://prove2.me/submissions/14fb9aa6-a2f0-444a-b87f-7f68245baa0b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 45503601 ≤ n < 45683457 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 45504851 1250 45503601 45503617
    0x20102010b0d0c091508030d0212090109050c010309051009030e0a12150b012015010e060a0312111608010c0c080409020a1106070c0203061b1806070803040602070b0c 73
    0x2e0f04502c10308101140005041c803005201490401a00020f690b140500080058801702007026980780d00c0c1c03440d01c40329420f0262824030702d82e02d400381c0f5401003480801d5131442c41a09190200c1c0644260400304e141400034070481d8210361515607401c08050b048070440d80c03114003c0d10301005031a5907000945844161090282107400c00521000420b04554040441018141000311600c01c4040c480d203103032692034050044070307800008400540c2500541d4140100800728141d207062502d0400300301c070305a141c80f000300f0880b02c8428000c0000e0041c01c200380800540f070111440b5089583c1d010407091102d02c14000700d5440d00042803829441400c2002d04036400100c0540340600e050300820007580840281c104001d205200d140300c849040c08540e005150382c4d580c03a01181e002e030040500b0441c1c06000c600c4031a51581c25105488036010a840d0406800c0611011416540d00801d400344201440245100000400c02c000c11502d90301404201c0c0c01342c162070099541e0000c0c01d074480e21603065 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 45506101 1250 45504851 45504863
    0xc031006080304050613030f080304050105010e130201030b01031107061d0606030304150201060e0a0533190e09030406021b1516050115080c0303091c030201090c090603020102010b0d 80
    0x4207102c2030410b13100070a00b1100c0502d86c0d0038050390f2030301d82c454480c4103400e00711030100000060000741b042c24060b481c050021902d5180c59400d01c4881d441d00541d01000082c181612100c140480ea0b0007540b0070181100800e0750b40e5902e6030389240400007001e1200c0ca1030707601000d4141c00030303441900040e154880d043c09002103160508041b11140e0340b2022505203400c641d2290700201c0c50b001c16400c03442c0111002580412907080000c1c1a013540c07141c00d0044034004100e0705611501c00040c0c2000c0c51040c00c2915486e0528003c00b440c08260f007182e4100b0300a0000480c02d00c042e00704000020400c9400c0e075400d580142c04401c8011105140b84a25254040a100440d461002c0b904001380b2040304440c81c011050151680d0b200d0039039400c2481d2a812410a810800804000388083d81c001c2000303d02451500c1401000100340c1441494001503046015100b070003014001d521242e8072507007041c1114140703039490754104083d042c1c0f0300089005500b081c0000740c41c0c0c203081600101d00343c0c0c071603 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 45507351 1250 45506101 45506107
    0x106090b0112060b030f090115060e0103050a0b150c030705030a080717010b19021006060201050a06061106071b08040e010f08010218220501080303040204060503031809071707020c0310060803 84
    0x1140c00c103050940030381f01c00302c00e560710200b06115186106150006100ba0340702d00503501c01c54400981107840041a1540d40d42c2010b90000c0159101031381c6580000d42c0021881e22159020440c2d4998001c06038000c1c514800010200117494010300c8952082c0c65580c0d40b2090b40122001c8a842d0b640280316000c402c460600158410b440c015010000c1c0380d10300c0c8101ca03008840d40d402c41d0161905584404050f075541c3c0107201c40866035008000150905081480d099152010042e070b5915000340b1344000c0081a0840260a00c1c900103884001e90b08091001d40350b9407074a0483c0b40c40c9600b8415100d04444040000500c1a0306000703941d480c080030700c04071f840d0060b80d90510084150300d884403a1840070100f10031003507440174414640a130400c00020f5840789010310511084400c55041244241c0c0140b0605035202c0c80d81d900d03480014025103080b845a00c6d03200c002d4a10384400e01101c076980005100300803034607600040c6c01054010803801c541c2201200e41c0300c40d04a4002c0c1c014051550410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 45508601 1250 45507351 45507361
    0x20310082e021b19030909020a050d0b0f0d0804180e0307020f0109080709021b0f0d03020702060d09050c0f09010f03030e06041d041101020105010b030a0504050f0106090b0112060b03 80
    0x2d0703014004100e024129a0300c48160806500e0404c0e20011403029240340a00d0490141640211114042c3c18206001c51504829180181050003000390358a0740d80d032145e400b0095034a44c00b100c141241e80c050460b5010b28035034500800540c00601416000c400c102d04040c444010a0068a09000000000e18545003245e000d00c0007010302c0d6604a41030110078180010001c10400039840104500300300182c907100d81e9109205003045040340c440d0281e0008404800550300807030200410ba0b02420010390752075031840130402c1801041092407205103054840c0050000100c0c49618034a011100203100c0c414940030483e0040c028004d044149200d0081400041e019003201882181c00401042c18260b46810903404894200007120600c44118180000c11007499901c08104200740004e02c980d604020b2282c805010082c01c080419440ea004101070090030b002565101045070f00a0202e1030b200c0710040701800028100a000515280e01da141410031403103030800380c0d168601e5062440c3c0350 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 45509851 1250 45508601 45508693
    0x603051b100c022106070905150301060f0f1e08040201120911010e04020c03042d03030210020706021b010203010609090603020a05010e0612040f020405010602010e120c030d02031008 80
    0x548130045040103841c0080b1416100100a11481440241c0d03c11508605000500441e1074415402c07498101040c00103100858001c081107850403064584200030580000b8101d13083c0d040040c0741d911801440072520349281e40204658803880c001c0e00c41c0c41043c0200325454044a4807140f010b0b0441045200101d181d40c420090850640d00042c001360502e1401600c590840e0710642c081c003924032440d0006809800c1020f80070b0070841e07030810900c00c0f01d071840c0c030040e48a001c0030701c5184030b01c0e50010b00e000400540c1c4e4103030b90b011104030111035500203845007894000c0d4000c0c00703140b01007880d2010001d40c40700507004a80c16258090120840585001c0c01924594680c0420a038041010301108100401c889402841a07004042c4150000c04a0040c08201d42c03041e0040401c590504032540d14002c400a4001c5000d087c151070079030344207040d0a9145c194010000c040302c80c00e000109000c0d4a40388664500c0a42d0341160568043d40016510007922569165410389480c13034605500b07010f105 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 45511101 1250 45509851 45509869
    0x20f0703230a090e0c0313080309071d01030204050903030411010309080f1902010b03010e0a150204170c0f101b080d060801050108100204120b090307060c170702010501260708010603051b100c02 85
    0x4913010469808030303242e00b2204033303810001203844201e16409004100303603d0580181a0002d0200700a5451400d2903151054884d40e2034440360b042c103031074106503010000b014017100e41c00e81000b0703d29902c540b0a0840031084200a290402c019800c00c54400481e00d07040c412041401506401032100c0030580d65980c0f0300e040c0d0642045400d40d8207110008114203000d4040c103850040c200a0555900420f04010030141003005460007035800300704024016030013401c0c0440d070002402140031011801e103880d080c2442403c5d40030454a09040001581500c1508100d051b5a40c49050310b01002c60342c0215000c0f80902e00c12890401108034080021070300d000700694001200100743d030703e00042510b1740c0050fa00c100c101c07000016200640448000560880705410080380e1000b40b00b41d51404860340b01c940c046000d6003c0c1110056810520b040007006400c0003000303802d000340445540c07070401c1a1201c4401d0031030321030780700688020107180c545420041c540320341c1502e03685ca4406650702440b0b85a2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 45512351 1250 45511101 45511111
    0x910031502070203120d060605090907031d07080109020111010c0f051308060403050909060a0f0b0f091009150908060403201002040f0504020f0703230a090e0c03130803 74
    0xa074208007010141c3c0341408038900715040320a00341e5803098840c129400301d84d0136034081c0040060501401d026692840e0100d40c02542e0761401290541c8401d903206c1c10148001d518121074807a002d00004c0070803040d04002a254000d032546c0c20851b03c20340905003a500c0351800300b00006c42002d401c4811a0054000c2c0c4403541c20300841d5141541ca40d40540d1411b40181d9090700440c6001c80c10100c5840e010303049640c4404165942d0058502d401d52504d00b0701c046010720079482c4408100001240f0304031098481c4030702d0081400c00000806580940341140c0ea000b1500c0f100c0e281c8081100d024014003980c4100c07100030000b0403d5070b0f102c0e1401c841984580c03042010b0403c44440e03107105814200580d043d500b120200059039103140803804582002551b108900490051200c0d1140c0c0c127080040c1d40c01580c00d401c014850841ca8206022203000c0d002c0c9000d01c58902182c5041e80680c086429000d940c1c55091000e00c507201c8412421060000300d500b400398261501100c0001000c150283d03400c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 45513601 1250 45512351 45512393
    0x318030c0c080604050610090e060a02030601050c060c0403020102010c0207030b0c03040303060801140105040e150606030603010b030a1506050d0807030c080f040611070b2802070509090a06050105091003 89
    0x1280d122400c2c581040015502035607103038850b406211440045a04000c000c0c143d4210802420b42a8428241c0310b401c0104035800070365021001842ca40d009104440d106100081030303c1051418080c24122500540020f074015840e100e01004a00d000107890f00540750000009c1c1c80942d941310301240c2d251300050084041507125100060b81c008240643c800c030319076459048200d07605000a010880e0310360203001d18035031f000086103e6075100c04884640c000001390b501c0b550700d98445001c03a0250030800f45158040c030440748220248495020b6844200203101d40501180da699020030104000306a800742195a0802001000034007400401c1c800c40d04c5110b4440c2044010440c0c00300b00d4000307500c140c0c00f14400c8213000e04008010b11204c405004080e014a05050180000c00f0040c11141c5000b10410412059214142d000300045030080038001c080349242e01e405400d04d5280d007110f0034111062400c080003c40c0314a4001e03191032040d1940c40701c0301d00381d903d1600c41c0c103250184502d0080030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 45514851 1250 45513601 45513623
    0x601031a061f0c080d05070e04061a070203163b01060c020d0605011706100602210c030301060c02030d020c03030d0903090b04080604051603080724050a050105030d0318030c 76
    0x9010310700070340b001c0303179544500041510700020040c02200c030f041c00c11480790323203001c070240b00510080042145c0d8030143e203840c51325224107202192500184030110700d031504c411a000104401c00785c00506002d2000140081c2201c2e0400e10700030b24a0403c1084410741703d0410040c05803610842c4c01c07490583c0020928092201301c0c4c0c403404c080386c00a03001040d89580320801c501c84a00200300a60304003884040e071190a604d010b000a44811071100381104511102109424502c541e03801da034061a00c20080e00c0d0b403941c1d100c5d0054421403541c0e00480c0240212059079030618008201d020941502030b019515004a43c00e0303c00c0280011070045007402113034000401c05c004500080c06c05081d030b03600100810704260511921b008480aa8582140c19100041c0005150b4100740d64865600c44450410007000c030b8120410f001c40310984c1c8011500e04003c00c815881c8a40105048807815000e6030300441c003083c821401e032643c4841e216025074080a2100001b0b20441300000d01600462403800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 45516101 1250 45514851 45514853
    0x4060f090809030c0303120c0a050403120f030c080709060302031b03010905270c0423070f0e040204030201200c060304050709050c19030507020f0f0601031a061f0c 72
    0x1240d084010650312040d0228912a10b41820000030341a140c00b20011410017441e081c900c907032000300030b15480c1c80110106101195501407002e560203564013a461b82c55503003040344001c0541c01c25020303800001b0306000d001c00d40b030b45c0160041400303050070303950326551681048000d40107548040c203140509401601c4d800e0a03141164055400703881020008201420b040c80c0003c1b440b001034142380440c1d8617056044070b01c003100050380c2e000c1080954001c1782c0c03d8400d8026003000e00503403a0560a08800c0010402e4103036100f80041000c007040e03100c4a85485018050104900841c04003c1c08211102a100d030710010308407011254400c840c0032a001040d400d4007148060b002950121841c2d0701c40c0005004002c041e00500e54040c6502004505000340c1c500f0000840c0480350007036090607503a501260034688280b1019505000c0303001111035051222410541e541006d2006440183c03558980302e8121942043c82c0d409286e0040c00b5140039005140b074000100c0d00403803a030341400150303000d0f00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 45517351 1250 45516101 45516131
    0x516031209111201020408030315031603030e090c1e0d09020301021308010b03010c080f1e1f0801060b07080d0f06030804090b030a0305161104050a0519020703080604050406 76
    0x115614421402c8015200caa10284203030340e008681440ca190b4014030050126035400019a58000030a800e40c158800040d0b01285c00e00c003a604134225440c20a9801005240d00301403030f1000d0740300540e030041181d901e407602003160340500302c80c41151503101d8001011a911980c050254150715120000f4541d6543d40024220390002001c000b0b24110300a04005902e02803141d00e030749000541c000d01c1031950b44000209031640040c20f02480c0c131135210115620080c41200321402c11203d001541090403c1c020501041d40207003000300c4491604440070403012818002c4d182203900c4190711905029881d0b0b141059074110144ca161013603514180c4d6403e944080c01b03000020750180030746917550fa05240900055644003903016000f1707480201c4000c00294407208a41c0e0b4034403800c4403422003241e40e24100c0e510784403660016500030f04000621104405550150740580300d022580c0e4a00610341075200164041c8440250125548000107100c03803c05410030784d07100780320301c0e000100402c040c1c140c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 45518601 1250 45517351 45517361
    0x120906073f05090f010606090303080c0c011d010605010c0809060a020313121104090f020613050909030d05011203020703030509010c14010c0909060503100902041b020604020a06050a05160312 84
    0x181640780d02e402c1400500e56061011410300c1d00c208000b40301d003d0900c1e0014040c02c00c2d512005040200510011345542440c80c140d4104c5041d800c020b02003c0c0b0641b0303d54024005031440a030903035180410000d03240d0700441040707138030550100003582440c101004000481d0480a40c500a5000400482d26030000c5803120001070a902161410012050b0800c0e02c680c3c4100d00440340518500b046003070100f501c0701034020f011641201c03029a19a1031002521400040d5400ac6401c54416010b11003c00001f0018002c0b046044108221682e6210031803402c4649491016001d600051400e0000c00e1050008181300c0700d040c100b015102c0140d40d250706101400b2074988007140d546424004035150b0005828004280c0c800e800e112190034440026102c8150303401d02c04000d980c03820200110744a40e0406400303405281d11003501300400311006500e0325401c482c00c911602c0c0d41000860820701680a07600d09020300d60300d103404d0811032051041c050b84900802d074144070507802d801304040d2490080e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 45519851 1250 45518601 45518717
    0x9030f0607020d0e09040f080405060708031b03011a0d06050d0302030d0506040209031f0b0a0e1509100e09070503070b0a080c0403051213050301020307030212090607 73
    0x500ca5490100002410302014680380b10400c5265070f240d4181d9603d583d00990000c0d008407180640300392a240c490300300e2040782d105507080703070307000c511041400700700070103544624a11891080d1301080d103414058107100074010118007a0701c8180314108188400d0140c002d94803105000103115465000154407c26202e42c200c0042c0d01c009000d0101640c01d0081641145041d1001d5050440203000242c85072012030700d00b102500403a0440388880e0840d000340629800c050f09000b809038503201110400e8104403107103030f5420000e950a015600f09074070744511900400d6001d24030603003400040480414041c2c10003609110b5803901168654003408144010300034900c07030350340d5421160300243c0b0b100303001030554003030780018003041020903c01700341d180c000507120b200707645c0da13500c81000321108810a42040350950702c080308020301d50341c05a000340960200a8031214181ea0364030b080d15911507044445400155080001d01945d45689154505102013121209040d000c518500080880b510407 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 45521101 1250 45519851 45519853
    0x1e0a020d060b0903010c08090c0d05150c0a0206010806061c03020a060c050a020705060304080304080912070b040f0504051603020d020f1306080f04080a050f071505010509010f0503060105040b030309030f 89
    0x2640101031326007440b0700e8403c1c0da85410814042e20b800102d940c0c455000c482c0c620b0050710709803440710800a00740700380500d55441c0224210f045c240300080100700c1e000b1308512400761252700e002045041c0f00140c821b105401c01051202403104a0026940b40c40b0740c0c0390200c0a504c1402031030000110240505072440710b0303655031182c075040303902002171510314a544454001d0008100780301c00305001004980d07205070090020741da10300c4240e010036450401c64000d81c4040c05803030400309680380c560008000300c074081050032210076103c500300002c45d0000d4400c0240a090a6494505940250040d0007803280465005060440d00360711107034558401824034a0140301e184040c0f002d90740242c40541c202e00c03407000c5082280f07801d030742e941d826128801002c000e00c50041303083d02031030440c141100c001139030054154203481000c0440c034014060130b000741d43c0305001800c00440d46240240404003201d1000340201030a912303005c00e10000700207007004203805001c1001440c0306610100461451811800 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 45522351 1250 45521101 45521107
    0x30703030b0a0501090332100606030f06060509040506010905060408060906090a1203110706110a020c01020d0c02130902060a090306051608060f0a080706020706171e0a020d060b 78
    0x4410890007400b9030700207a040c04181003060021034040400034140c0c100700b080140201601c8100484400754031028459103100e80e0200c007000c5480e5800002c01c40b242034405010104841400038140d9100303010b13003000254180700003407251910b90000d039080b00d818103100740d005032980c01007145a4419001403a80380e0080080c885001010000c290703001403200f001e0060780202d551380c0e010115140310a041090340760491240f0009214003140c806d1548110200000c072400c04450050380c1000000c40054061400c160200303500100b800710b02e500c450f59a061901d41583d0801240840c080300700c0d00c0d5942e44401c0344c0e0050b15084000c2c11a1300e0f0136120144100c1c61403030040d00740c400080042513850707503070784dd8840d400c1e4024600c603802034400c480c1c01403602d03580c90100d05d060360300c0e40c0000d0b804d1017030160010326603402092034000c0d070721903650b040b402c1506503204d190407003c1520600210a0444c003000c3c9a10040c20540e0341042030700130054581104c540f81d00054034800e41184400d51400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 45523601 1250 45522351 45522371
    0xe07050607060c0e1f110703030504120510050a06090e07050108180a06090c0509070c0c0504050408120a0b0109081c080402060c03030106030515030a02030c090a0f110a02060903030c1e040803070303 87
    0x1c40b91204031b00140e800141040341c21990b00a00031b006620401d0360f00c0c00300720b200404000702400b451440c0300707004c201006a85410300040000e01010b100d811149450400002255480030400d0300c25075406031038079507003070b26076092003140c541d40e25280100720f0040507001000540d045c02000301060186644101032070404040010100020b080042030041d80b03840c41c8001110545c04404a50040f200000e442d696424004158440d00d513035422044825800c02060070172a42c00340e0150242a030b160040c040d10b50081940c0c0d41d0301108040c188010540d51404201e100c0c1e6410340c0d0080c406000365085c0398800d0f03241d0b4a1508203800a0010941300e03010881030942e000005040020101d0040020b03032150b4011944500403034421502070110b040000b11402c20a401084c85030440e00402c100114403401c0a40e810781040c071111006000740c3c404200b070088000287e0340242c440c45111403402c401100d01050440801d8944580400c0c18000000c0c010414000340140502a444c0801c2c40075030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 45524851 1250 45523601 45523607
    0x1503080301030b1602070b090604090f0501090506040c020601050f1914010210110304031d1002030309010f0603020306010e10030c091e0e0d050d02090a0611010e07050607060c0e1f 79
    0xc014202d0003030070300359003151241c03e178002a0a000c40c0c48004246070303210045000b081c440e01c0f890b00319240c400e08020700c2c0101c0310540d9011f0342c1240c000a50400007034a850040100761030200744200c0060f40504018001490003030300d0000300900090801c10103c4841c610720402001030740c00a80402180b081e40b040c0380d601801021015003801d00100308034200510144041c2c04040c0018042118040089403c40e0341c6500410b003599000741101004041c560001303550350701c03c592445c90b40d402c0071141d0f40b851500d4000d01041d01e50040c040d140982c02d0128100072260000c1020800301c2c010b070400404500e1100d0362074080c10b074101c00130441412004c421900900c482c280c1101c490b1400c0110901050081090034038a0303202e14289036103602035500c0401138000e218605034030212212000410303039040039980c000300314000002e0245000c0c00242e651a00784a100f81d80c1c005508020000c00151160f201c08074860042c1460745144076036001061400c00301d80c03500c040780b0307921500c1c110182da0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 45526101 1250 45524851 45524873
    0x10c0c1202030406270801020c030403050c0922061e05061942090509010f0e130201020307060c05040503160506090d051218091e1801150308030103 65
    0x1841c001149024504100100703442e01c41400f08114061020303681000307540d40d55408000302440f000035900d601c41d1000c160b840341e01510046403e0f11a104501559040140c10180314242814840c103844028030b003840240100350400312030650b510682c070441d10300300c00c54042a00e50302500000c0c5078900b0744180040f0b0180c490a089500504207410403100c40c4018040c055056002e080c09100000841c2040000741c090f0040740105460210820031503034440c8071401280e0381120003410030390780d808075131146480e03e001c3c03c242d007001600060105000e1500c0084200d2040c81100e280c08201d855103012078054081c0000050030001c0d00b0415460300f04139001440c5908699500103e00d8200000c2d800c0c4290304d1050b000d80c4003846580c050041c1441031010a426495809680f85951100d486a003140348810300e1042c0c9408010031184040301d210302c1449c6002c031104500d5600d90b4a090040180f95202d44401f941d2201d20190680c1072100005000b10b10520b00f482c1c813541149031040d1000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 45527351 1250 45526101 45526133
    0x90109050414070e01050c0105040602030a18053a030c0e0414041211030a0206060103140121020f040e100606110303010b0a02010b0904050a140102090609040e010e010c0c 75
    0x1418929289050580014040e4111206041140d0b22501100046ea200d004218500099500c1c0004000c18840d15400441c403c0c0c3d4000801c0100800a5040c26900148400040c285910580200c0035441c921000c002c0100840a0050080021700c41d8005e40e2402c60180500069101c0d4125814103070084812080613034121000d10000d640c4c2500c00f200e007c0014005812050207021003a034041c0540132440500780d408007600d81d00e0365921406550390740300780d4030240003074a01100c0d0200c105003505941c0c166030148400325000351400000010700c0b55100c0701641e02c2281141c4118869036944955116545190040c2c02d00c00040d042e9901142c45540c850000e011229100c0034081d5808412281980d4100307200584601c00c1da81d0490062620002d15508050880103101c107014001500c0343c0143d1040041e001c012100c0c8105a09074040c0c1d000c05500554184210b0301180b80130f4001170303d24685000005411061601d080d401e407000c10604c0000300b140788102c1c0050004107104940300f0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 45528601 1250 45527351 45527359
    0xc0109051f051b030307090609090c080f0406060801020a0c0204060b0f04050613030606030803010e07110304150e13140109060b03160c02030a03050a090609050a0e041a040809010905 80
    0xa07081c0200c0304903107008a0340d00074040003000aa00300d80c10b403051078401888a61102241d03124a04074502030f00c1304400d030103171801154410b40001818280f0340100303001142503684003034a60f181c41c2c0c02e00300d2882002e8800c031440c0380c07150340200b82c4400900c06800c1c0080140e075400c800f402e0360300601040b55501d0f005007603030301c8040011141e807050010443d411680d0503601a03a03180000c19410011900320742004100600703020f000003e215000c0040d60507150700e81c044080316103e130002138500700f000c16405440c0382c105100c100180080340d5041c11911400c3d00304040c000051100141d0075005000703001104560f100700880c089500b6025541c00340204060421045092004216a9001c001c05160303c0c03101310340300b0b505090300c11450181555400b03404c403424804a0329016040e5007003402e5020000b031006100062040c0309500c618104c0b80040d01c0085154240081c000c15000c0040040d5020a0600c0360302c01010340401d42e1038800e6010320380ca01e03200c3d85200c0004048401661200f442 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 45529851 1250 45528601 45528619
    0x507030c1407030807050c011104090c02030a020703020906040e031215060301030302060c0f0708030414011808121b0703030204081009030813140111030a05070504030309030311120403050c010905 86
    0x1c003110070111840150907080030841d0703545140c030031210b607c1009040011542003a14008085102030060130560b503080d8401d01100e4007114040344c2d00d0080e01d82520059201f41010005030a08150303c0341c0002003c3c1c00402d128940c4c0c6010752031a0301409540350890202c030304000c95003103d8100300d41120003c84400740341d5455a20000d5a4401c0500445031101001070081c171249218011102c4281d40a0f9000e40c40e07240c9030078400042600d15101d00065403c9c1910284001030240307803680d5003a40039600a081038909401048030900042081ca66040c1d007502c0c600484007039030064400c492203070768096612420214000c1c200105a40c01000c41420f1426190010750841d8805901043d5540500a940a18100b0b00c1c0490000c66209240307529203100f280c918014035005502c5480580014000340e1500001140c0e1446903100180004480e4582800040d11510382041002211000c43d04c110741042c0241e40141d109500031180360340041c0c40e9018958001010100038030046901d488 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 45531101 1250 45529851 45529877
    0x13140a030c06110304050d03020c121903030207050708010501080601091a0105070f02131104030b010503071401080a061a0705010f0902100e011202030405010b030f010b0604030b0405030903060702010507030c 91
    0x3201c00060081d5801e110f00a9002c142020003002030b10020b04c0e0046c40c01c05003240d6814080e444051031781c0740c140a001c01c6c1100c960350100024840c071100f5503141840b402c0c0115a203040b402900509070498150240b500c0008051509001e814040c0201e00041c140035450035280700d007101d03402c2215107014a207032404443d49a1f0481e003034030348858002d12588103102030307480007600c140c520b28101104a8546071181c0d41d01d528200252043d01e00c43c180280c55030340c0b906c04059607003625100350301000c007070754944008a51140b49210341240440102040041d11a1540201030103000b894005208000c03880c5000c1c0202402482505450b5220410621403183c02003400b40440d4100b0030140642e59015000e107901c11540d41c03110071541d00e401c44d1a4101031501074082d103100b0440c1ea1003480b44130869284c01406101e0078003500d5000705101e02e428515960100c11210044c03080d00c4a000a209107005c5482c1441294031030401c0d50b00028403850001c0c40034040350b007051001e000700040c00390703205 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 45532351 1250 45531101 45531113
    0x3011701140402010e0414010e060a06051c0e21070b0604090323090409060b0411030112060902040209060304030206090d050a050304110301060b0408030903070b070206031302130213140a03 83
    0x203402c1502860103015001c030b02c00101d0050aa0803e842c00402c41130000098040035040501c1d00580040f40c621206680e030300003c907520300525003031203c0b4142e91407010781403044d0343d0711182c003401d5030100703a40185600c40070750b803000141010034400c8120005070300000c00c8885003d5540c480c0e0102c0b810081c1c5049518010445441d9010011107440f28180581c04e070300c0b03010140c0e108540000c005002c1a41c03140b03400c1000c0d1800584581c02503041402008c1c0034250b04007130f02e06840c030701001c400c1d5001d040d8980c0c90140241c00e105070381250742003000003003503210b81000b11312440c000d03001800f0700e01300400090b181ca4180f66203401001300501400c840b0f254043c00701c0c2d8000d50000d140009541d080400640100090750280c2242000002c00052441c4044060110144214140e80c0c840d82d40e410605076910805d88002c0d840002000001c1c1d1000c6511f00182d11036001611041104120080e0142203910201c6040c01d035000307002c406c00468107841400b01c0602800d450018040c0d28584c1e60b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 45533601 1250 45532351 45532391
    0x6021c05011d180f07080d030c1209020a0b030f090f0c010516111f0e10090306020a0201150f080c041404120e031501060201050603120307140d0c02010203011701 71
    0x180461088000103d80b200301e1009545045a0305881964040214400e00d43e68540c0c01d8828140f00d0302501c0840501e6a0003446500541c424584848542d206000384600c028415280308030f038482400c5102080c400c0290001d580718481302208807020b402c00c80d09083c0381001c1c2d401a414540e01180000c02541d070310409a800c86c3c0c0750107208060102c402e240030382d40307403c03100e00c500d410001e403d441001e6166503038503001e804035198450031340380045401400071030880c40500c0400719158500400000da01940101600d40451000183c03489590b0b0203c00030719503da02590703050120032424044854103000300440f12208a4082021801c0100010701c80c040061010b40710b401d020550803843c80c02542900c03007040e001020b40300440c2d0080c40807074400c1e40078002c5000640c40c000008034242400900d041c1d804825a41d00c9041d03654140c41140c3c0817074141040d4117460014002d80e400f5030b015001301840524a0340000d40c07030790304120071013070041005158200e50781c0c140400c40021618214079 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 45534851 1250 45533601 45533639
    0x15020a020c031f09060209060a020102030403110106080309010c0312051801060e010e060f121002030103060b0102062a04051c05010b0108010f05090a020912070807050a03050705040c0309020d06021c0501 89
    0xf000c1a41d82c401e081c030710000d00400640e00d8000d400090f0340c4004035410350095104070721039180c00c0000058040103d080b10070324000d600241e80104260074442d800351003091a082d10901c0d0804c01c0540000c4a401950700a5415450165402103800128034003030017070030080c040c04920402c1c42d600d00000840340d840c018001d9401581c1d002c00019454441c48291000300003208221068200380000b1000254030911040e100706150150700c0380290310110322140180d0036100d4400041d0503900710420100300703020105200610400001400b92504001d060021401d44c174503a0700c402e09801c10500351400711034550304000203c030052005114006c3c4101c1a11006d441c00340040d9681d0403800d000740b02c1d40c04440da126180b07205205050500144010a456030203083e079052036580c605000782243c03070b400300401c1600701c81800d124904103984034589000c17a9140229181070300340c000c00c2e08121000010f440700c0b80c002032440c081496811440e00c1600c1c0500381000507601d0f00d80c001221442d00c0304 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 45536101 1250 45534851 45534913
    0x1090207020604122d05030901030b03190605090c0103020403030507060f020f04172104050121090305250c211b0e0a02091c03090315020a020c03 64
    0x3180c0c015074481009550251280318901002d03820720b420082c11244c01d14909020690040c004541c0490204182040407580032004504001c1d00788015009080031003041070f00b5214441010500c294a8114401d146008000c00141030500b11105814500d4400d0701034103040c01017100b00002a808011100c1d901d8010900065480085c1c20743c1000c0e104024403110501000704000c00c1d602d942e00300440f01c01000340304a0341c0744e852180303a1100d0809031080c40381481505200400c01c95001d210b03000c00c040081440f520804a018020504940c0324090030703000600081154450000e021f0300e0b44504080390360803103400407050f030745100b9000c0c21401341d40c0421425400c09480000e400352050022680711750f500b011420400704490b0215000d201d405071000b40c05020500c001014400c13141c503108050f04015100c003c0345038207644074190b404204d01700020381400002003600c80b08903c80c6401c41d45405a99003d545100034a44000050224842e80110034a45c00d800041d400c2c0504010b23380c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 45537351 1250 45536101 45536107
    0x201050114063c0d0509060106120b01020a050a030201150e100b0f0712051903050103080714031308070302090c0307020d030b06090901030f020103060816030201030b0402070f0b0108010e010c08010902 88
    0x6101080100750180f0740d20b985403000e0032030700c0808540040d098407842c41e001004181d4850241503514402840b6010100e20002c240752503c404541014401c0d01040c01150a01c4560755202c61600c003010f102900141d543d203650700106c00300303010a900100b80c6010f00701860304008a680600708107038802c1c0301c8620000611825940c600c4420380b07981c1d81e0000346401030b0300401040a0410f520001c1400c81811018406081719402803140c2c0341681e400224450404116a4401801510b5861820481c1c8070603c420300b210030b203516150b0003070f00003840174082145c550f00c1404451040540213215890051040204403540000c2e0b1030385040c7c161038007081515a020104105100301070183c0d8000301c80c02c0c004024003d0304078407241d00394400e0380d0800c45140d540070983c0d16121f842640780d042c5040340804002540c400d4110500f02840248014605125070380c4886110801140c11030b1645c483c00010400010f007131048480b8260280f00920442d130b40c1641c010401d110500408041ca035001c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 45538601 1250 45537351 45537397
    0xa03051210030b1f05030d0c120c02060f040305010b010519030510080115080606010c030804110604050607050a0303050c16030c05150108030d0b0301060b03010501031806020a0e01020105011406 85
    0x2041d0910300540d00a8140e00682c01d0480c40b0b12216884881c0195013000d0710702d8001568180090714a010b40159900c4c0c10413000301e5503450f20103008181d0848104000843c0d0b0724003696820005160400796152669a101d24524050f400d4400080c0c0313081c1808170a00400d800840e2803414894004180c2c54000392950359502101400303c0560008140796191507845803070711490b40c0e01441603481d680c080b034401d03603550b100444100301c44040040014a00034003180000741011504500c4410050034913007050740f80c2c07012400c00d401a400c02d5030f10350300007a003440038190107100d21a00401400141440c14401000b080029040440010200103006088005000051203611220640311040040a594034203a00c0e5494100da0b00d0309180c1c4d4604400c0d242036140510074030044420100102d400d42e80b80070011750050207404000000b1140340a038200020302c1034401440c40d240951110714000c0380440c00282181c00580000f00c0020f88525200240d95a071415036201000c0044ad0700102e002c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 45539851 1250 45538601 45538621
    0x1140c0901020a141e030a050a050310030614010e060406030b070c020312030403090303020f010e060a0c03020c01050702010203010f0e061f0507170319050f0106050d020405190f080a030512 83
    0x3c504000b030710361048004d40707903032164001c81c44140003100c08005c500d00c40720141c1c2840d12031080c0ba44510110341c2c00c0001341820340c0540c2c06140e100040750206800c290f40c0f526554140c4441c84078802d900424980140300d03038221004a1034010780143c4041080f28115910360a0602000d07150000b07000400b00e0000031541c0401c0421100d038101e00c2040e490303003031901c0c01902000e80c0d400114054003c02d0b60404407003030148607890f80081c0c02001803042e5251122650010003003900b000f81010f800304030042500c3c0c0309001c2c00303000e90125800169070f13625000800000034043d0300a2440340030f10304188403180d62174903241c4a884c006a01d00d0315241c40ea0350000d903024070811200414680024140888118001000d140b0404035140400f052503c042d081000310f8004607080080070342800010b01c5600c1c40380d0090110807070004001460603031903e0000b0084000400401c41a41407003206000309c2c0c040c0ca45c60001070620794000d0244a1065901905601405a401581c080d101c0d002907580f0301 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 45541101 1250 45539851 45539863
    0x30b091b130603060227010c050601060305060a050d0311060106050405090a1a0a0303030504030305060904020d12020102040918060b0301050606041802090409050a02100801060c0201050d020c0303090a031101140c090102 96
    0x3078072580c1150784041c0d0203a010340f00c5a14802c5c0c0000d96006c80c841c441076500550044007010740c4000900036070b81c01d14200368002d0901911160304810990008a600d80790000e0103074095000c0d444451108210212041c60078105130081c40c00c005081c0030030861510b8202141b40c005500010100d411040c010041403500700400d8003a0b031001c407200c400028140c15a0205000314026075061060703070f40f24410f1002d40503060f24029084400b0301001000310b1500800059601d030300b440003601d401c0c0c0d21200070041c1c4005100003049401d80c0c110044c1000f505100d1b81e48240b00c190b00903c014542980015141c4c0100d10a803407031414620603140401c0240e604a5900c5280140204200c90441c1000741d500d0b41d412100b00e00030288030020350b0b096030140c0c504030f0485800e40d81d6070f895643d09600445113600090340e100311040d02840b140b445000103101840c411501007000740310114071401d00401c900256995941141d14000c080e50340e40c40b9a0030215485440954a01e6490340c0e1000101d213411 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 45542351 1250 45541101 45541103
    0x41b0207230a0314100501030c06051b010204080f0606190e0403030207080f03011e030c05041512110114041211010c0b0408031e091c1701060504030b091b130603 71
    0xc1d8040100410070504807000c0920714880458010402c42040082111b00c20702000d130000c92030800400105114100805250b90a082d4002c90801d100b0521070983c0c11507006050913801081c042c0140710001c0104a074410340445e99030811021300390300783d207516655003c4e556101c0b007810000fa0525019404940000e9406000380b82d4030101d440120650303400a0007041d01d4246010301c00454200040200420340b604a0403011600d4500810080142404102d19242015070040002e0354481c001110034024007500da866a41c1d10710000040415002540d0150317082403d10081c03051402c0200740342e241c55400951003244c0041b8100513a00d40070500b90003403d8840400400042040c180b003c0c0d800760791140718200900051034584078640d8000ca865504c5507004000b00a40a5415101505041ca0a0404422129150042c8140c0200c242c100388003194001400f0010018203640c95a03000c034100010b040004814140181d10403a4020f10920520b40481141c01499180e40440011 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 45543601 1250 45542351 45542359
    0x203120d02031005030a0b01050f04060506040b09090609160e0d052e0c14070602090a06030b0a05010e03030702090702010f020a020a0b070c02090f09010617030306041b020723 77
    0xc003410640200a544222860120005007480000e25030a00250014a10398411740184580e800c1030180000462000f908039409625160001410b40320140100f02600303d65061a03900c0c000381c000e2146050740a00982e000d100b0f140e00304461000124028400c14540c0e02e441000003000400140240d240040081e1440c01030819800d080c2c0300d5404107070a00c2490248000c1d4208658196030b045a0403650707003034049001d02201c0000360181800a04005219013030050030442c0c00c001243c0b01000e0360f00284d0100345e56403200070280c9800d5072000d00410702440e000b0440210304000c00e44034003c41c48000e01503ca2800840c0303440707000303400c03807252600000e808540342d10404500941c0c514030044107455030114440850f050034412620158140e03009000c02100f921001c039141000316000305410440e540e201804188400a0511013100800070001161a03040250401040701e8945040400c00003039061000c44168002c1828400c0307804008041440381d02e011110807045a07403032902a80 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 45544851 1250 45543601 45543607
    0xf070c0201210e060703020f1206060409050f0f01050301020403121d030d020a03030609020307050307390506130201080a020901170a090308090d021203040305130311040e0307020a030f020312 84
    0x16440c0c10742e00007012441400100da04e00c1c0c54045c4258103d00c11503031640100042040044007440140c50f0749a0005000f419052501c0c0d40c4400c08021550203461544a8000d44424011170703500140905000d400120000c40c034081c550f03501c0030f0b04100e000c44500240507000c864100e000100c0c22101081003405401e40b1000540709000a441d00ca1150041300400c3c5071500210b017111461003501d100304100c0d03c4583c43c644070320b801500d00110011030b04403a0904100811900080345403400c8007000c0c0c5400d41084900c1c1e500d006070a24800400014400078084002405130780c1c06100b542e08035500c58001079071240f0100040354800d004010107072404045200707001c2015030983c8030b0840e860281e03403207040a484900000e9160244c1b08007190050f40050034076841e102d4180001c641041c42401c0051400c02c80d0142c0040c0d01105610a960058402c450a621405c00340a00180c104001300918034107105940020450741050101414800c8801031610031521704102c800458040d1011541d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 45546101 1250 45544851 45544907
    0xf0e0d020d060b040f05060a030212070f24080717130f0f03020d0f050d0f0605040e07030201020709020901120f140c04080d0c030c15060f0b1905030f070c0201 70
    0x10700383d103d200c0c038000c600d4480b400e102d42240e4800c0c0d900800c070081201410030700c2c503000c02001c41401ea14200840c05102c4001428a410020710340090036881300103500c40c90740445100c90ba030b603406158014011f4290070083d42c268004d15260f10190907560b601029111303132100705941884c2000080c0010710b200d2a1400784110f9000081e10395100780c1c01c035441c410880c041200c1b841c2100e150140881e0b4107012508007030026820480c1240c00514001074002e5451002405488000e00b0020003038021600620944d6410300a21029002c42041585000040000203050502e00003107a001c4690310010b0005c00c003c140c010340c0c2c1303040c0701e509900c0441c146124082119071091050b0b071400e1286110340c070209070080208441482d055214210010025200e43d44103140400c04482c406540f03050128690841c0380c0d40801034841c41c00300130384800c041a5445941d1022101d201e062200c18030401900502900c40d0583c401000d03d88424200b480b88010f031400101900e001105c2141034000d0710b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 45547351 1250 45546101 45546113
    0x1090807140f1507030212010b0304032307020409050703050a14010c0305040b130f0b07030c030b09040f171309050a050a0c0522031704080d0f0f0e0d020d 68
    0x10045008044841d8a041c5030040d035a41d562000030a000c03035070040400903026000032440310350312040c24200503180103183c810b202c90b08a82600b1030349802e40080144018160b11504078005a6225081c4000200000025841c00d000e4440024810741d20f0b150610200030f8240600001594800d084907125040781c54440101e09003d0b850f11007961804400b0400c030b52080c01050300580e040440c41e40395441e002d504060010490700c00f960241d030342d10120000185010b21a07840758803940e400182c00b22680c00024103981d241100180300380c094030140b0020620f80f070041c1d255030794840b440500c014003207810618540145041c050b000d0381c820714005031542d200e4105a2040814103000c10903961410580001c485940b03d40c9030010b4000d201c9039a80c146010231010340d501c00c01c050000f1041e900e80d9403c40e4a409000c0c4034500b03140109003000b503110100440e0a003581182845111b03200650801450408090850b400704201a1003d0384161100c615040c032054020342050444081070800c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 45548601 1250 45547351 45547357
    0xa031d22020301032013090809090c0c0f0a05030d200706023c0c03040305061f0f0e0f07110d030902100e090c0306030c0901030f0203060705030405030a031508010908 73
    0x6a03030580640140d03400f101e109042c032113054200140314007210761140302e00400400c11f000e011210100c080207a14115540c00360607a01c1000c403841a40c0c2e8503000385110605207404844654160780c081c1c10000d0000d24013105903005803c2d4900c00054110355002c101100445855006c40304030000a1444140300b030342e4005200b040d034048007540d000c00b140d07418000319441c280480d1801809507003659041c540500c0091618000707010440741402e4484e00e580d410040f054070002e811420150300c9840300c0000000c00002450000c0340055002c1c40d010122080340001851078072011610340004030614020285080007601c0c0c5d2045808180342104050002c0840e4101a482500c004801c141010321850300110b14000103130000d00c280e1105075504100382c1000e860168180940d6842064a4075041241ca00943c002d144100311544203005040c1401006801c050070044200b0800c008142c00004031740920495180014040b848050141c2c0c50003180e80041d0125404d1540800502ca00100a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 45549851 1250 45548601 45548603
    0x10603020d063b0706091202011103040b0a0302031005040203061008060103180501050702011401060929071a0a02070309030f17041511010b0306010501050d0b032b020a031d2202030103 81
    0x40b01c01054a81c0d20584488819105105541f09181071500065205036085580340e4581d02c2224201611825003281d550800400070001a501204001240c0180f100c410300600003a14214610f050a9010900b61407180a007c0c00b0300c46503030042801c9074030a0380075402c0292500c807810b100e00c0c00b514065010b0401523510f00010360030080e001c80c0007201c00342500e04031390729500c84030b40307481c40e04d078458000d03000d150074200d041c05e4400300f00c102c042030210041802a00c600312041010060740e01180c4440000340088240c10302c18002800007a400c86030031070507030f6000614140c80380d6851a24942d021041c0220420b40c0801080000d0010480004101b510040e500c400d2852600215a54201d4901c4161980c0c16844030004002d1940500d00a25141103030202c0070540c603c224002c00c0c904200382c0c2032040b20174081e41a000c00c282440f01603400c40c850510207450420700744e0b03c0081000c5154142402c002e8441081030486540d2241042880030700803103500c00b80301c5161050b01c000d400904c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 45551101 1250 45549851 45549853
    0x109080d14010605040618170a03140301030c140301020d0e010b0f150a0509190303050a03050718060e06090d0b040b0601020303190b061b060612010603020d063b 71
    0x107541c8140d0440805428183c400d035544003803d2601d0500c08458502c1660781d12403071141201e1f8046a80303800301c1c48422400240000420340c5405070700c2d00600034844480074a00c802740c10710040c0006410400514101c60600032840000894240001c2c0240715035407400c0c0041d440d08811990b0143d040d0401222420100c2e03440254540003c14400c610031030310b4170507110450800030902018012005829041809040741030034101c898841c006102207a041076000c500e02040035004c041e07042c001d0a030711204504c3d04808169803183c0342c00030008180581e01c01e010515a1090503138a62109136203040320003e12000c10340c140350400016640041e10b043e0342aa84600004020b94000400c803800b45140c0b8041d1640444c0340041d07a40184444040b46a02c1a82040840002c201124100050b581c4940c041c040030f08007403042084d10645054400c0c01641000420000b41e42d40d2003240304225002200807034604000c0410340d0400210722031b4580b106180582c08a524089841034205002c01c140c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 45552351 1250 45551101 45551111
    0x2d120b04020f0301021608070c0509040506040b01170c010f03021309060905010b070201080f060d06090303050702101104140406030803010312080c120103030c0f080309010920030606210109080d 85
    0x2010f15080c0c0c40b80703107071000c0e040601d1105240003d41040c020104c1601582c81e600980d034555000950325002600d06440c0b0b50720050501044c41190b90031580105080140c0c40301c42810b00c2d00307080d2503010040025061006c060344a00300c9c0d902940441c0c041810034002c04181b1ba84440c8040d005100a016903203200e45800d002003240341806088846113a01610795020384d035103940061403550303001001e0513084001c01e01c0c4030001070304500602d20114480d4030302041c50310306500c1c02450300c10040400c001c0d407070802d41c10120704440082118151009690714900003110b800210f400740a0b41d07840100320300c500100010521407001d8112021010595551b1529210b40b828002c0c14042c0c00d04140040243e00010000240a881030307900c550b05c00e0106140760b00741500c84400c10f800c200d03040300159440d40310030740c100940c41441e40c01e00b80c0f040000d03400e070b00d0025020a5868a00070801401003500c00c8411104100a28000000001400003404140700c18607051150750844103c1c030303d20609203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 45553601 1250 45552351 45552379
    0x3050106050315011502011b0c0201080609040804091805070806040b07050403021516020a0806010f17060c0a0c05010507050d0b09130615030b090303060a08072d120b0402 75
    0x400d105554520f03118040b00c669013455642100240c401d0300301000c2d9940c40c822004a550071950046000441d5283d0280c0c6010600001d0501c045c0200841d02c20b202c3c2c681000006000c42c019681612810380000a50380203168001d542c0e510481d002401d28425084001140e51001074080c0c4603034840c8024426648489106441902903400000d40c05070094610481045800d0f002e84401c0502046901c444034554000c83c00e0501d49802810080c0c00c40c000510a003d0f50000c03920090030f201000040120340f0807e51a01c410f03014041c2d6942e4000090f405500511440321001c609412500811042c1890364014001d50f102d800440f04403410021040c500e850544001e83c07040c01e011002040c2d401daa9900d400080044080c0101910550107022000c58148103005102d080004002c1d50f99080050400038070743c407264440d242c00d5200f201c05002d03e4800500e040b442c00d04008600181c9405240d014030b03821180c2c2c029134007200c1d000141d0000c1c000302c50820381c00340b402039644522144031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 45554851 1250 45553601 45553603
    0xc020d080405070909060b1306080714010e09060609090903030901050117150615040801063b13060c03240b041202270403020d0806180a140c04030501060503 69
    0x108039009460ba410910301085030a28507004001c4161003404009600c40407000010f180302d01c00e6031400715040c2c0c1c42606105042c0104080006002264a0501540c281100003845199020304850198008034042815038940106890356004010505026880c0140100ea130302e420031070300001c8a41c20311000144852a110f9003040200415019101041440719124820740015241680012200b01039808805e23070840034001401c40040045030701c0d0f20305001032003100c1c031201d0b00e0700c8091040031001011252010036007480743e03440105041ea0b07a48001c054904c540c584580070302490708114441c29415819401301c407182c0d1441140d090102040382d0031009040c001d019002c0c1c030039001c00041c01321081050f08071103111710003000b546990720841258200a40c41000784100da002c61070600003007540500c401c0d8030300c00142c50325100a2900d00e000a400320460581900311201100c017140381ca004a0300481e8000280750902c0c0c0013410002110a03c3d40d205201c1510306500c2c0c00d002164620b0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 45556101 1250 45554851 45554867
    0x3060604060809210a0905040608060610020307050a060506180103080306040e0c040e160b0a05040614091908010e070e0a0e030c0d051c020c0a12030e060a0c020d 71
    0x1405020241014203105090303582682c041c00c14295485503144802c003110082542101542c070008840780c441118000103450240d194004512680c00d040c401c2c09a94000104141c0c001e5045610040c440a184e50903425407043c100301418074018030810009001071604018020482078400900d45078880d950082220302c2800000d000400c104040755035460260070030095100a034040c3d40354041403c00250480384510032401443d00449003a108031410841140700804500444c54980860820010032610503070007100d01780305460f0140b4000c02845000e6030081c400c05402c80c40c2940390f0781d0010300b40e071010b03100d441520342c20718038148a07944005c42c11138125a0204070f40c0849841d88002c0300054220f00b0039908641c030090100120140041009010b140342507101c42d0ba56035400301040080c1007019500c0580107004002800101c003000400c9094103402800c01d04a03018011402c03806055a00b0701c1c181c46114440501800b021035a001104c2582d054007110014105c215080e60822 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 45557351 1250 45556101 45556111
    0x7080f0702061506041205100606230a201506030a0b0103080c03070c060503040c050a0602060f060a090c020c090a0507020601060c03090f060c0308010504021615020412141203 77
    0x1c2c0001e40841c118034031020030341c40200c1c0020100f03802e080d00c4120310103a0b00404c40d410303100c5901c4050480700481441c45030501a10041c5068030340240c10041801840040e03001200007100d0014001c034690b44240b0b20a1561070504040d101000228104240c0c1d60028450700700700c4a4086c008943e5030314000551402d199446010000b4980c07840d220703c800ca4002665071019808100510000200d1111701803011b030140d034035495280d05040c1011024080c05402c04d9000310103a19081c0000350b000116035520406003003030400c00f50b5807080420302c046000d5220348000b901702446d81c41c1d041d8010480c0d0900000548000b07a80c3d90741d0540c0c081c103442040c2e9039100903030040da00500c00a882640e6a01c11103000303003000d0007607656410386003080e0b2106038040000a248181a442050340c014511401082c00b01c034154200f040681c614141c02c051007100505402408100342100c4c0c8268064030700a100ea0702d007080d0081d00c0d9003421a410081c028007425a4060301510031500c0e60742c207003924098 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 45558601 1250 45557351 45557353
    0x512010e06030d080901020f030f04170a0509060a020c04020a090e0a090804062d080402090709080c0409060906020f0c0715080703020901020c0a03061508010e0307032604060507080f0702 82
    0x40f548240d0690741a40098600c500383d5408001d0796141c841d03402d00842c0190811821100c06145c9800e0a07002011410f005d0341815008015565105500400751184030070112800b035558841c42d80240e20708000d400310141c04c14004941e41c1c01203070704030b00d4000884100318041c404030303a505a0101c00f19000707030400510112041c00103000c103510908200f00c050f0142e51001e03111050300400504000042805030b0001001c0000704400c5060150455800c0f6074281003000d00c0ba07003091007061300c81649010850045a4400e9001c0611085420405030342d500704904541e540010702d1109440e51042980781010b10804000042d40c1210425000c40c00c1c00a0382c5008183c3c0300c07810100c002c1d40c0310f03403606411032040000303480c2d003a0b50750044803000303620400000948000390000d0344070300306596110303c1071030345401c99030416008040203c900490341440c280d0740251002c8102000402407101340c0050f8002c50003080200402d50740f12038080e0032183c54110345075440041c0c610301d50344112100d03401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 45559851 1250 45558601 45558613
    0x70308030c0304030c0606230102031e0307030f020301120507080604030f050d0f1803030605040b0604121704151704031718030a050403020a0e0903190201090c060512010e0603 77
    0x1618404000d0b50b0428800c0c40c200510041503143c900130740340907800c030500207400409810103c1004044801e1214028001b950500706c0c1d003800307000103107100106001c4844001002900c064070a40c400312156009000840d01c81d6101c0d04038008101000504031014400d941c00420004000910a4400d69159035001c10200103c4c030202c80d50341040d018854145c0d11580a40d4020b0454000e21030484407080c03862034518000e042c01016510756910450245180100d80065038840d03808440540321400d5112000700c000e40340c002c00086524607125007149010401103404a06c004141a0071000c80c1c0e684034100000a48a0481036019540100415502c0f0401546c0c543e10020f116840b80544800c0c036561413003400796900390340c45180a0000603000140600031450417104c0e00000d0500100c00100da0315116850a42d40d1280c650296135205600020245151003508000078080c0e00c55a0341c040560785030710242094000b107402055002c3c010002041c51405000c00034400d0354002c0003400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 45561101 1250 45559851 45559861
    0xf060405060a0c021c02030909100807050103020c15100f091416090308180306090703030807051b030f030108060a090809010e061608091807050724050406050601030c0207030803 78
    0x2000010628015070054194442000803000d040004141407600512380e102c48407420440309040042901c10f49410241e42480001e9002403440d0907034100f0b0800503a035070011400340d4a002404442c02d455030040f042001010801440d00d41d04480c2e1514030076032250b4840a20b0816030b4a080100c50003d40d085001920008400c0d40340d207800b107c2428200c991135183d440e1408143d07c2075068030150380c038806c8584110706003008034a6018111b83e0181020b1411341d5030040100c00e0150054040100108018418401011a8944d10002c80382103d03654181140d0030384068100344100d10441c090f403800540499541e026000f602684446c51030314105031480156100d040308070b030003a04130b00300340405c0c00d12445d0040b000c90f0850243c07008070b8550484908014009108500c2e00c558850410103100086030400162080740e0303400380c607084045d60010040c61900000051580116040c08203100c1407002170344c8124007034803081c0d038140018400c940d004e0b82c2d50b80480c0720041c03915004100040c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 45562351 1250 45561101 45561121
    0x2071202010e13060b2101050a032603010303030b10020c090117070b040f03050d090b0702061c1b0e010219060b01030908070303050105040506040501180504080c030c0a02030f06040506 81
    0x40d011000300400c1a0074203140c0a2404c44220b50401c4240d0b1500207070f03100c501c0072103078118013000c0ba0039020032145e5070511002c14507610552100401662103030404e8a80c084009414149842e00e07013070301390f8480d0783d40e0800402801c240750b059801000b02c170307020704012403005c5030003210224098403491180c2d180410080e40502854080c003140d000f0000d0205d0b14942601c018801880c940002400160960070000d080503000d558020502c50810b0080021000e81c009540302c03941c0403203000e41c607180307411102007001911161a080c11454030b8403c13090f403071044400b514009c01958070000341e0481840166900d00745610f6500400e01c0341020f5100140c860b401c4020850018900420f09030111f50b14074030550400b0740200c021a48480060103142018410154006002c8600340140d524013890240e500c10503a00040500c0d450f14005018044a102254040e80c103440803650394060b40d0840c1c0c0d46401c0f20003012403007401502c00c2d03440040030024005d070286400c040034200c0d90316200c0d00341c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 45563601 1250 45562351 45562367
    0xc03070c050c030706020c0909010b0a0b0706090804230405151c1202030d050a02030105060d0c030914070518060603061908070b03010602010b010f05090d06020904020a02070302030d0207120201 85
    0x840d0207210302c40c1814140d0710203002c2c0000824254000388a00a03044040101010707004051003410780c5044040c500300e544460072001101c00c0d0129555543c41c2030308048020740396217040507104840003d000203043d05201c42c1c1440158515110a2030006c0110800060f02c00561700001c0310080d41d20400a646014034018407211800240c440c0c658560303594418040c084000c408015030000b00761000c0392199802040d0381f207180c00ca411440c640c1040c00007100d43c0a40169030344c031190307590043c0b240c0e64000c0d445255450340041ea4038408986001c2516039603090760140318040e00485840300203c00065000500070b003801410241555640e205000d120002c50030640707441500075a000680c00390034400300001c0c1030107403801c03952503041ca072000c5d00755051009030a04010040113074054803540b040507603030141c0080b40c80d240c2c1c60680d400c241c0701074019003444581c01440050310006840d00001d0b1300b001c40303100342c09950f070200005101780e03240d01e102d110b804001c181a01300840150321035854 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 45564851 1250 45563601 45563603
    0x5010e15030102040f03080a020f070e070815040501090c17010317072301020a08010501020d09030602030601050408030c0703021903080405220207141207051b1210020901090e0c03070c 81
    0x18107040da179405822134030841d94001d8a91000000703c0780d04055052140e002e1200072030001b84440351500e18507211092006001e50100844040811413041590f038044900e000f00400900c00c41d40c60f05c40c40e00087c8405005200032905002d0701054103400e680e409412244c100340001000300102800103c0341e40082d0303007200c010100d841900105040c0072030950344421700300d0005131500d0303074100040c10304d40703040e046903042d075129100c4c4211082c5c0c00301904c0b090380c2d4032031005a181d403181c80042c0c440d4010b507004400180004105042480c4d0001500001c41c8c0c0211080c04c0404008560701007031b00014000a07080c25402c00040c01a42803800030110708840310000c0030382c0c00001c007144004070b0b00301c0b00c0704070398203121441ea60211900803c20300341d8490081b900e003440c011080e521107a442c89900d5016400405403900d12090360781e084070203a5201501350548440e2929405190f009620002d40d182c08520210360200e5440980c85525210380041d4403001d00e551100d1605848265603004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 45566101 1250 45564851 45564853
    0x712202b0903290a06080105060103060302061602040b0a0b130b031006030203090a0c08010504050c03011505010305040c0b0f0309100605060d02072607140f0c06030414030a0503010602010f05010e1503 88
    0x264200018030680120311132010a513000070041d041c80521820b4032005050141011300380441031000d07950304070450702035100b84044480700301450710114000c0c007274481e01c2581c0310704114000201000b45c08010403890000c9940d108400391600c109600d1400195505d400e1941400018403186010343c4c020341d0410f1420044480d0546290b0700d00a5007a1507401034012030351104e040c4010400104414400d0260480003804a18004080c80d40e401c2c02901c02c403810540c444000c00e043c81040d05940018244401201d07540d0070040c00ca0b0400356209440514aa00c20403c3c81003580001c0d01c40e020a9550090490303203410043c100620194118601c1aa04480c3c600030460506203650220f00402a626501a4552032541080d5000d6074a801104e203482d005142c0d60105418003040f040030956084034415100c0d01d40f410080300204440d003030034a82e440002000e040103034015020714101d64595000f803141403480c010344400e0360750030700ca1079811054200120300c034402030203045522848060 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 45567351 1250 45566101 45566153
    0x60804140d03020a0305091527011a010f0203040b0d020a030219090801060b0906090907050708030f10050d030f03021c05041104050f01030302030712202b0903 70
    0x218a15081621510100700441e80c00200860801d826000f1190301020f02006841e442c1800348420003824401040c03124240084031641c21111000d90440011b6803142000700240c0c0028520301244801d000340c0300e40420b8541c08101e440c03500c0042100c09403601da0702e4071802e0201c04890003001e508110034000a054080c02000341d81046030030048005501030346d4145056251000303d0b821921903400c1504003c0d801c005040107900c510040f0342e00900d0548d0304480b59a10244100e9041c01034000040c0900000014000101d1901d1841800740300c40c2001120190340c1c0324108a82103c01c01401804610300c141240010360080c3e014180c40b00075100421402120341c00d07603404403803048808982c100e0960120380600c1c1814440d180d8002031184c10704000b0750568501030343d01d0240b03030340045ca144009000d402120788140203803d8841308504200190207a212022602c4030361108000701030b40083d03210748003c001419a82c2c0700038001ca8941280c0142181ca40c4110041c001805440d400d40c24 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 45568601 1250 45567351 45567383
    0xc120e03030c070303080a110708090f120c090115022505030a0503120a090317060a1703190509010e01051b061f05030606090c03090f0601060302090f0910060804 71
    0x18401032007030759101e0b40a480602d04620b005869698041c00c619a003a00e0a180c0341e01580b0002d040355100c5401c44050b9483d020380c0000a001204448406a00240c541c0c507000b2031b0080025150140220898804800340e8072502c20f00000b44400300004016400804032040407440610b01038243c040590840e402d40e903c0d1070110340b40c0420394004641c3c03580005a0502c41c2c80707900c09140d4000e20b0780c0d2000e0207401c5464030000d10320213122900064141c88400403e100380c0c0c8044690004000a441d51229514501e50381912174104003510002d0f20490080914070701d1207001241c029a005840d104501003041004444070b1f008090314a40350b07a680701c810f0340034110401040340315100504483c902250f100b03da00c010000d250707004034080da1025003881980da94021104d5844411480b04603180d0f560060f60500e0803144581800640c01002d001007509903241d0000c0c880881c06444007488448540c0512800da00b00300c40564620042d44006e024aa202c1d01241c1d402c103014022a51088444c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 45569851 1250 45568601 45568603
    0xa0803090a06060503030721050706090f02040c0306050a0b09120319021e0304062f07060908030903070e06010507051b040c111c05040b16060612030c120e03 69
    0x109480c010900e40c011121501000860f0103000d02500c1c040c1e000c2d600704038080d9200000c0d181d555544480c689007100da17240c0703414450420794441c0e6030031034424040003400b81816400b0112100c2d09034002d074200551075210a0090240100320b810241c42110000e140005000054108030042907000d00700e507083c8180c5210400150100035003020846006004e00035010b031400300404000b508a00551440041030300c0080b00303850884001d810a500745a600e101a4004044202680010742642d840d85d20444800005d03808252441616031428068481606039540e0203160344117980741e8000c0c042800449142031a841d0000c906041c5981010b5003596145c1c10306000003151450f003104c001d40240d4034940b40c000e5070003201950030000b0040000101d91901c0c2d5508443c8021a0440020903a140500c520704540041000044080e0ac2c0c1c41c0e40c45010082c28602c03003080d40c100e030a10f030380070800100660503a00441e80c50f4844064107030301903450403400306441c00050103201c140001e0380082d0714 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 45571101 1250 45569851 45569857
    0x6010c060603060501090b010f050301090c0912030f030c0314150f09010602030306010f08040f0f080d020a0302030a14071710050a06080a06060306060f080c090a083301170a08 77
    0x320543c00854a58100780d00c8404a61640078035504004581c9001101703030760080201c9055858151020940400d00c810a6503c800242d0003a90b03800050100e070410305600400144880c0041d903010300204041ca03900710242c912491011001625035400314541001050090941c21b5000d8980c41c203441e244000940d054a0076070299005d40c0002042107010760340300c42c100301003a18034104403c841c02c094442c08024030200000134510700c0a080b4220070b100100c8107680941d00b045030150341d184400e4100802030b41042d44c06240d800d0418003111076401140f201a0303c902e481e0303581d03183d03d018180404e1600c41710142100610204241c80071440e40c488c4061603011f0b2025440305e40503410306c100c4920403035036a544a031080519081050104503071100666004c12003070301c0d01c8422074036061484d801c54401e140a2030740c040700b800c1e00000c200c840402c207640e0b07001c2124071721b403074001c140b4041e042160610320240401040040052050300c00301c00d51a510141030b00121442c01020b9521414194 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 45572351 1250 45571101 45571103
    0x9030203070611120406091506080c03370f020402040905060f040e03160c09050403080f0a05060d0201031a0d0303150b040302060a03050619030318050d021806010c060603 75
    0x3800c0000c618090102c940240c0c410301804400441c80c000c035403512507a035800301a00061120743c45105075014046401c800000c0314480d01b00c00c1000e00d5480f0f103002c0c3d4815000303074114024010710f07807006640c0c914030030030008151101d03407034095840c1c4502c203c1e080c0003400e050403100f40d0500c52414015858500c0680081c2030f2409c07000078141400c008000364120703089021445181401e030804040c03100803040d40c00310b101000d5000552582490141da0f4825240c2010050b0b514100820080c1603008520902814030001802010b84a00300002c1c01e60340c0c110341042c0c00100e903d69400044d4441d610544800c5480d0b4030340751681c410303c03001031107009102d08107400080c0c0345e0204441c10b2400500081c010003011803241e14240c51603012551318040d6501d114103150f500c0d8001640c1e6210f140300c00100110040001c5040794581c42c01070107400003c5070305601126240d5004c106802e1041701850400e400230507900240d02c0300e014140007a8001010341c0e041000d10744c10000040c0f454050a0061 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 45573601 1250 45572351 45572353
    0x5150702010318150f290609130f090303050606030f070e2e09060e0a03020d050a020d060212060405010509040f03050c0a0f0203060610050414030c0603180105060a050303040b130801090302 83
    0xc00d09003e40b0400d031900030b1400c21186010055080786d80d5030809115054501545030b080d140b002400f01142c0c08120b44030581441001c8400b07018030351094401c0c45c400c3e102049640c440f181032000500085076620070701e00c10358000c152014041c00041c8038666004040184c1c2c041e4901c10a00b400d810103003000804038543e011885c0c02900801360a01800c250310345800d1070b0282c4400640f00d241d4620029006072400380200090050910090840d9900070300a60110392240ca4000000c0d0301043c5001105182100401d006103004d0085a0480b00001c2218034980c90310f0302ca00b00c40f561a54011020303c4030800c403941c06042c040c0101600742d80a03030348003070314015140149428148010800c0740304e0a00890700854081e0440e042e18181c40010200c900710365841e50101e40340500c84001c49501860210030001c02c01c0040c5c007402c3c9102221002440140c0f9400203006010085010b0580e25400922062001c10b071154050100030324407041c85413559580d640e0560071515000f2041d001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 45574851 1250 45573601 45573611
    0x9011104091b031a01030506030c03070806041b0e150109050a0b0405030f0f0303130606080307060b130902031f060f030605041a01081c020c0a0b0a090515070201031815 74
    0x540b01268980040241103410203000007140e0b000c82d41c62011034510f5080c14940c0d180041240c1e9142044600780241000d4125180161110031142c5c3e00c0b0001c031001c0f11905d107113240315202981c003a9030207001c440101503c1c000d2900e91100c120311000841e03101504001c140c6000158039030320890a0310080081080c0655114101400c0c141010884088140190300915011100490010031640c1c414001d12501041002c030b0314040000c0d1084d6030040344070f84030226240e4148059940045a0000101c2eaa0200003089907940002c1d6031364040013030342c90340000c0718001120802d00b0b05a0800d6600e6000051016247d583d83c024138021a08113031400c076601e408100810204948060200d451038058208961410540d517a9803014940c08200e800c000c1d8410124180c0200071244010350000c1c01841110703112440d08600b50000d03501c0c0d20000d4600c0703070000381a0901c1c1ca560f03241c0880f038000c91894600b164006402902100128506040e518540707140071448407d00310b1944c140302680421 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 45576101 1250 45574851 45574871
    0x414190c05070c05060f0c1204050f010e01120b030114010905040507051f0c03050d090f0b060103060303080c0310030203060a0f050f01060c06110f130e01060c02030604030302030901110409 83
    0x421240c0415004081c0041004140003040c403100241d01114021a5141e40e0b503e000100da98642c0150700c01c00312039100b50001c80f030003881000041c03c2138440075218521403013003400044942c1446007076503d01150902c00c08210119081c0c1210f000d000d4081c0010403844090890003000c010241c1c0540c14143d60f40082c0300420000b80032500060004480c00004203007000d200712008031039291050248229840f40b00c04060054060741d03000325101d03e0412180010342041108202c4a0078122000c259640c00980158024403c03c02501e4066a620040c5e66502908000590004d0500c408240410703900100580e010031856105200e0083d0229070401c448c504042551000307031200c00803985410050006540c406041400150001c0b0041003040d00e0020703080561281c0540100540760000c2c50313041c0c0300101c02c1160200d80403006801e5450380c3e61001101e494098034002541508403901160210384650040c0d500300130f28000000303440000c803084106550007030740500316141c3c41c0e6607150 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 45577351 1250 45576101 45576151
    0xf15040c0b040312030506011205040803071101060602070b0d060305010c05120a05011d060a051309030e0301020906040e0405030405040f0b0102010e0d0206070c0c0e0103111c03021009020414 84
    0x1014038201d91030415081d65143d030121a00880303039504040e038a000040440e8820540301e81095070300340d8100103d04190902e41c080e5401112900f004c6403840c038032042c105105209410443e401c0b58040c4c06854140115031001d503010501d008003040d03d81a01201281c401e210380c184500c4c1c40c2c1c07a201e0362030350b1880503d820440b000b00004d100e2403504004000071030220101c081201d039600e101c5000d07556600d0000b924070207150440c940200c0725602c00c1220401d02c1c2e220f030020a01a03140c5a0201c0e150360105401e038030074007811642004041c0030070840e803082c1400d4160030078450310a40e8100b50b01c48011500b140c41040ca82150903840c1ca101c81c64950302071180480d01d084040203010404c4c2e034040040d6549901a1000302004481c514030401d020b007045c1d00700003814950a801b0460f5079a418180c010808014103140b18100c0c9102516540e960ba44601c4041a8150042c0295000d042d82c1d449c02407550501c2a60001e4644e582c03189030b4140c10f040140310b0011900c0c040c060410101d402 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 45578601 1250 45577351 45577373
    0x3150c03060102280204021606090302011d011a0105030415090606051003020a1d01020102070602070b01061403011d0a0908070f03180506030105100309120c030f051206040c020f1504 80
    0x200c0100510141116900e81c41544c819060b50340503500580d80b41418010840c00b11907440016003280e00d4800d030309040640c1904018825400b1b01e036548d50300800d4101e420f007240c403001c0c5174100d41c80d0786922081d034650046003e564000d010710a0010903101c0f0001410548240c00301c2220400c0d075400050080380343c002e00100b1041c00502d003c50030801c502101034100405003883c51441d190450b803100132a8400d4045912155206d0000c0d07440d503883c0e1601c1c03482020300b0f0003810081200c0f5041440c0d180f40305030a07241224688a90000c41801c520030803c0b803600c01400c240070450701c9941200204010030020059148610038620001e015428010b202c0c041001d0f00008400c0c2c0d080c41040b4a54802c1d007a40d043d1a01102c1c000c080d01c03001d038000c1c0c0c010600030b40d0040400c6000401011070940024540000c24020b4880e004480720001c4200d03810300c40d5800304501a00160301181ca141015405403801c00c4250040740d40c54030324080e9240c585181c171504210303071480701c00800041005a0740b02d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 45579851 1250 45578601 45578623
    0x902120f0d050f161b09050603060601050703170405010b090108030c0c010207050a050108270a0b0a0c05030a0c12110a030605030d020703031404050904030903140c0a0b0903150c03060102 82
    0x906001d0110000d80d118410b14540b095050003503400801400070210300c04007174040c420018440c4c640d907a0304031b00180000300c400d0fa20030b029250000348294060001c8800d1158569224040c080b000801001603140242003a105590386d880c01d04c1d2070782c036443c1e405400b0305400390081d900c03120100e0905107016006500a811900103100410281c0c55910780002652000d0070120a40da4650000348001c0740060500200748881100301c0c2000308004c076400ca0b0042c083d40d000ca210740d40b807401d9601079500d95201140003800410003d42011234550010558400528000c001510003006031000d0713a030903007207074403401e4030004040103030720740500c00c0d0b40c0244001ea0241c2040f0340b000d98065158505480701400b0f101c10800c0d50400d6190040464000c1d1500621801050420f0b0800400d00705441c04102c41c141e88584100150b01800241106818001008001202d040a003110516007003901031b01e405200e6420440e401c408200f600600c5066000901a01da140c0788000a05d080c0510342 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 45581101 1250 45579851 45579857
    0xe030a110c040b220b04020f040503060c0307210b03060408180f060d0c0908030d02070303051f050f0f040207050c0108060d0c050103020310080a0302010603030801090b130506040902120f0d 83
    0x3c0c45030f2407a00c1e842070400c0c1400840142c3d003c111041d4040e0409445111442a48644002506003c852150000e8020303100c042d01152031301d50329010b0000d6030b84425290f08003c84c1c1003500020b01013001d00c0101144c1d4a0000001c160042210042842c0a10540d0308031403811022500b0281c004004901142415048441055078410400410528807488081101064176180080c2c0c030180a070140c5e0004000b040f0880c0e5036a45202240002504070f4041100041c0c1000d000c01d01c0120038444810000b040d0900580003180742c60b0801102d030144c940303055000031192009020741d40d61440680745c028000c8000d840c4580c00320000510a00f070041145119028a103840b2001c180c0e464005030a40d40c2c00e0800603076a0710368040102e00041260700a043e140f040c0c00750b2408042c0d06411010440340700f500d130102d140c0d0321840c03000c09881d2403150340c030340215800c842070309605000d8110f0b58100c580038000107000f81c6d0503008079402414803c03c980c0e4541c03101c490411104400c000f8074200f00c0c030398a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 45582351 1250 45581101 45581111
    0x506010215040b040c030803040503030f010b0a050d0c180801050105030607020a0302060711150910110c150c04080f1f02040f0b03060406171b0402040b03190e030a110c04 75
    0x1030380c0003400701c4020340301820341c0f00c40100150400c0860420703007014540100d500d070344900c2d00c0e2030306d5907903644210b880303a10465100000050711201c48081e20346116581e120702d410b1282c031060304402800b0f400a52010403580031045100d139803181c0c000d00c019000c82c0c0004501503040c80d003414545400a440c800440d48100b8010020a074003060303c5402464a241c01f2403a65140040540b80100c1c03070700002066a5440e09008405800003035607000054500410711441031001d182c500c150081d000300818030b40045003840b40710f01c1123039455503000010350308840c242911a1801482e000720001c1000d040e90000c407044d0351081e040e071500c43c030030000c1c40815450706040501004080310184a01804030b100800420000c0da5950000c00c050200b803a0034450003008142c43c40e40c0c2d002c01c20721030b45400c407481d0000a442d00b818004c49040c0c80c41031888620b10f4485410080c05c80c04540e502000c01ca986030640384104101340020482180140e99444400b039901e06405d080120705581c2c648176078580 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 45583601 1250 45582351 45582373
    0xa0f0c0c02190608011701110d050702061b030106110f0703030c030810030c030b041a0403020106050f011d010503070c0503030a05010302011209020d0206030703020403050106080313080f0a0813031208010905060102 94
    0x84e869040d9a041242c284401c0c81c2c0c00010381c0589000509400812004141209190416400a441108250b080b0b604945854030000310610070041814205c1c02c04200502503036008180c80b4484131400b90480d4070f4001105a00ca04010040d00100e00141e242c607070701c0042c103600001c41504a003002100d008128030310f54401d4002c100a07c40103296032000c00009003032081c04003000000c040c00840080c408e2402e460028004c0c001802a14420b801014421096500c21458049404860140c8500c3c0e000d10784019074a581004060200308140d100301d40c0b00060081c00514012002c1d104080345c554103610016091030a01642c03800080e1400c0340440160f6a001c100707100c4590140c1f2201c0e40c1b83c0303d05804030080d100e1a00060705944c02d10200080310030001005042007822214132103011521030300d540340c036601c4030341c031051690b4850b410050104410b80b0003000004202d140c808640365803030f506c3d80400d0300700300d48003400300c1c00d200010480507655008140d403241017403020741036041071 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 45584851 1250 45583601 45583607
    0xa0e030303071e03060506030a0605030106080d021e0a0212032502010507020d02010504091404021309050a03050901090e0106051903050603070306230f04060c0c110103050a0f0c0c021906 82
    0x5841c04001c008543e4401d1210740368001c1e404103019010203030002e642ea28100d01c00401405142c82804c4c0a50310700030300041d036501c0c0441e490400310050740c0903014100154007000302a05129007410420b0284c0c0e415400183c1d26102400451084540a1900d40d24002040a15681c03200644001c03a00e20011403c010b03070340b000855a840b40d0461310800000103500040b0b440c1d00840c2c00c022400362500030b0160f644040074440714480c0c0c3c0b0880381c008814220340c031100107861540e50018510f030f10000c18540000c6c0030b030015000c000818505440e80380e0381c0d41c1022950301000c1c0d1000c00400d4001034007201d10521076411120608950905200505000d40441c0d40c400d07440c03102900d12540c0d8014035890951000302210000e10707809c806841c9090010782034035800420f45085070b00502d8141658015800703014103003103c3d500a502c403540b016031080190701400c2c00400703082c0f10310307aa500904e01d049124420310407406141d6031100301c04505441446284115014503200191035104200140c2e98 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 45586101 1250 45584851 45584867
    0x103030f0516021309020f0f06030103080d0f0c200a05060705090103140a0605011e020307080313020d05100f02030112060c020f01060608060405010e0402010e24070501020a0e03030307 81
    0x416140035599502800000080b000c10036200a60100b150034100802060540000c0702550089480302009005c10003040b0845071441c0d045500202c013407004002284940000d08442c1c07565180116004202408030802c03103c442c01e400011401e1015008130440703000c054003520000311002806520010380303409a561800400030010408006031503003c0d40d10a4018182900e080c1506541904000c004040601014054039001800d113040341c405112014040e603005070060f0700170b14036201c12619450b4890344001c3c1900c03102d031a644011030060703d503142c07110241c038055806020003450302107824003901c3e6071000d5000c4180c0180014481900c1002150483c25404200000c4030380102d40241c1c102900c00100d15007075480e0070700015185412030b24152180c0c004603001c00007603032a0030140b00301e0b40080e14007900255003512109510b003024032004943c04560003410682c1040c2090074607040d4004202103829940100719642d101c2e030008240f44100c4e004038091030440c40c0c0f180000300018 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 45587351 1250 45586101 45586127
    0x6051201031e08070c05030c010504060507031202070f0f0303050c090306010e0a060e070804030e0a0b1e09060d0e0607170c0a03021207180905150f060c011e0605030303010303 77
    0x5000d81401902444400b10211802544542001c3d103e1503036051201c3c0c01c110b00d100700c50003405441010415036201e1000c0350245c1c1c0081d00c81d00c0c20900d0680382244c06c0d84800c45200c2000383d0810480c80406c4034804c0080d16144182800115200980303030050584001a100040b426000c0c008041c40b641c000c92a9819551a150618404e90700c00b4001005440c1c1640160389462040c8203108845902c101c1c228412802601c458090500900038030050b890581310300d03072103540c06002c1c0e0308000c1e10251409407071070703094404941007042060000d00c940d48000711801d1000d990700304840000340103120179903102c40c075801d040311010300b2a501d4550862006104180b0020001001c05070715000380e06503604140f480380c2080b1907290810f001381c044400100b0542c03100841c0b50001480000d9400b907680700d980000da60025038070b00340c0140007500380c401c014654050b4090210b000c0c1d4000074440d41c0003009190201c0401c600c515803184003118001d8000341d0003908100010b10100c1e4000d2075040d095 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 45588601 1250 45587351 45587363
    0x50a030b04020d0c08060f0105030a0b0109020904061a0a1b03020303060d0c030c0b0301051206060102031e0d020310030b0106030902030c060a020a050f10110913090c030f12090605120103 82
    0x40d540c1e032000400b002d2003a54001c015000f090400328912070300080b0903100d6030003104810980e90301e540c01c242d80c62080100c01442603d45800600504a207a0094214400040d0011035066190078169100000a04c9008803250000c034403040402d80c00ba40c0444005102940201c0b10318054500a45a120042040d8028400e012840040050005a40c4000d54002030f10490281d22600586000da10030b22510b0b214410011011808500110304070f402900c05070015494002c041d8a1b40f03c1852101070101c003400c909002020400202d03000461041814010100b0910b0440c03414046000060b040300e020103103441460001a1030005010101070811688103848864840c012460100038041c0201176019040d1b41d07028100000039450040707900500140140000c03182800c00e0341c040c29090741c2d07100b1171500303800046003821350103281017131b006013600100640c03a0303101d21100c5a05003908139003490803540c0c0c041e0f04680c0031a001001c3c4c4a2450700a142c034143c0c0e0300076016804180009022 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 45589851 1250 45588601 45588623
    0xc05010804020d05070603021b032110032423010302010507020d060c030507021009030207050603100b0f09090615090f04020409090302060108010b12100b010201111801090609050a03 80
    0xa41d0f07940500071540990200849001540300e1000030060b4001000080501c404080707540d8a101c40403003920f00a2006801a6492080d0000080c01c080702c0500301403101c030108240480499100706400e45070074611b150807100804081d0208040380c566014002502c65842c218403581c0303440145a0381141e809207001d41d103d0b0a03a00000c3c1c03201181690042c0300380c0c944007100403a550550482c0d842041642c00396458001588007043c1a1001c6880c0100141c224cc40244594600b201c040c54004521003c1d40d442c054a5190018803540800701094100f400400c2c42445c6141079601ea40d4030500a8139040c030000802c0d000c00c1c0d9a0301408044520030300340c450700205540c4469040c2c4000b40702000701485160241d0030003949540080c040e003402542404000740082c1011444079014041c1e1000030719000c00300c494100000c003080c09415046540b01c081124201403424050011003880d0164100380c4c0c0c1e01341c1c0000d031060350203601003424042600410081030307580414400442c1d070442002c42d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 45591101 1250 45589851 45589853
    0x90201031409010504020901050f0a09050a15030309082407030b0102010b100903050c03010c020604080a02120a0906020c011404060509060412050102072d141e100b0402070c05010804 80
    0x80a40059030046401070001800c0200301901500194003450095400442030398a85040c4040134030070300f0600d50032500c56942001200e40590006600c140080000602a010702d05400c0c05049258010341c00915241401d204083c014400f81407100310f000814240c00040700050808030030010100b0003032565410498090b64003c0d0055082001c006100002002c0c10400c003030580b05640c041900d40d40b043e00d0b15508a814140f05c0c0c0032030034003250001c080039507484c1d40d1489160b0103540040114002c40440000c18040c0300c000d07001032201f80d00c5001c095414a000280350044450541f03040100701b1092041140080040f90f003507881a14060382d80b00018008140c96104a0303018242c41603a0700d030034034240034040d400351000610901041e01207451018420360303076500d144003600304d1405041c1680300141072a44c220389000c405500351403d0481101c40030310305025103841080e568006040352101480744d40308494000c00210303070450900c001c548074807070340d044103019560600452a001c10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 45592351 1250 45591101 45591107
    0x15060a0b07050f0d0f090b0f040e06150a0e010813021305070905030712050f0a080409050411180703060602070608040b06010c0206070c050f09040203100906020c010e01060312030203010b0d090201 86
    0x2843e25004070101c420300070250a009003030540c090511000600000303000714480c11003900b2201e0b0944000f55041c00c060500001c17a852020141c07420368424507442c0384681001d03101020344500c0ba01510303400c2400f01842c1c009031208000401710886e00a0340c914050040e0348034024144003980e020030008690361248416200340c581900a00c1e4036100e1446c0c00544501400340000003a8410310603142c105006030120717076850900c55001070041c5410300040c04600305d26400142e12a004d804c080300e00c0ca0407200818019001c81d1981e031080304401b801c11000365007500400009081510080c40b440d0325001c001000b407400600010580040a004180180e104000b41400550000c00c096642c0006103443ca51841d4144940360190410039404481d6152004050f4402c68016020300400766500010800511900c0c2040390b40e40d03070a101c103c403606400d125001c500c0d010b030000024024110308000c45540305210100c03080500409c014003403507000074145d9080018284001c00c0c1b28a03148016 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 45593601 1250 45592351 45592363
    0xb0715050603210d0e0c2206050d060203060307060906020c0609030a05120403060c030203010302010912051f020c07120c0509091002070b061915050a1e0503010815060a0b0705 77
    0x340f072000a442d0303081e10681c50f48006058241d40008104076660104a5194031401d0078480c0d20341c481c1c0d00c041c5600c3d01000e201c81c0349082d030b00315440004009440d0710000f40380c030303403204000c1e5005a1302004122807410200407080150202e030512114040c0ba01030001e558400608a1501800c0d000c01c980c4c625460801a401519030300406803200210340700303149180c0d0b81041c8030039180c1906080034400c00071301034804c5070b050742c2c0c0681d140c105c0c1606241700d941c8011800441116244260074407180300c0a4800c0c440e42085220b1500941c7d602100440d42d0b10b00030540d00410348911030743c04d2040014030250302080071034a0949055030b2590310f001300c03c3c2c14035035600d050382080350000410100b00104810a54458101194200d1080ba070280800e800c20a050240c0121580c10003405010790b40500701500707241640f45440c40b400616070500181c4d08800e20920408100c002c0014421460b080c0800036800901001103035081c945800000d0b030b07012403882000c090b560001070700001e0080c01c1c410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 45594851 1250 45593601 45593623
    0x503030a030203190b0d0b040302030903060c04050406060e0d02151b0a0b010e090d12060503070306060503010c140d0b01030209030a030e01080604020403051c180b0a090b0715050603 80
    0x549454a9500c90060080c1d0b0007103d03800040c11030420000c0c110302c0603100f01c008081021740381d00241c405581d40d24502d2030024106030150302c0203110081d41039a0403c40107110b44485820203484070700c1c01040c0700c169078594100209000c1c980304110a942c44082e079403a1b2454045a6149080c41400311124281c0718140b41210900d00481d11980174400000301c1e0f80100c1e20a50350407000760390320003840d41c030760100361181905a0005070101400c81d2041801c4108107610500000d4030640d60030000b8a0140c9035402140c01c3c7d07440743c2d002c00040c44c1c280b241102e001e000d402d1400c4002507166030b490003407044080c413003880c0782e85107001c0c0c80c580d110342d041d00ea0341c60000d001c66580b0b40080c00d029000340540d00c0c8031400100103c00042150815000707540c00c81e98807072700601c0031029000d2034101c886000c0741704c58100609104401107244004101c003005012150383e903540c681101c0b10040068406810030548000100007860000320720501c40c100f00741010b10000798540350240007a0421814002c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 45596101 1250 45594851 45594853
    0x30402060f0702090a0212070f08040f020301150e0a050703020403240609090b04050706020102090a050f0d051c0f0306030201090909060906051005030c04051e1b030f0103120206010510180503 84
    0x42001103500d1309a00500341249500304007036155845035812642701420720420342c006403c06011a000902612103d00400c1c401000410f03154007541e540c0400380416803116108800881c2800b16003005841419080000c502d020341ca4070b82035454901d40380305420000008000410159030001aa60344030101038504100c06200040c503904207411901004d40d000e031000e0007000c00000343c1c01c3c014401c540c43d4000103440c2c180028600010003079008000703001560401280014040010070511090b050815039000d0a40410381070000180760648078800c84003030500c0c00c0028400340c3c2e0000c030300d071048030060500032501d05140d191400c0900040680103000a0806c0c2c140400181c58030a030409072082a8100c400400c3e108040000790352040c5c0c1c4406070b4103504142c641d0b00c2d0401910070355101140c4004010001d4040c000400240d00860701c04502d03060140c0148100700013801d01c5242150980b00914465040100141d80c2841441502007407015191000000b080ba41001d507005010041c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 45597351 1250 45596101 45596119
    0x9070314071505190e01080a021b01110304031407080706271202010f05271903030605120102190305100504020301030510060515071716050c030d020c06030402060f0702 74
    0x40b0080c01980140710841600e80f860444a442c07144070b42040814204141c0d1030305015182d8040307a40c000d600c044991031581748007555001c144082401350304014040c40072800d0f07880c681030030020440b648004805006000420266011819070810f80b07000c141c00c4200062854405a100804005007011026020044203400c1e028030480400321310003075415800920a0340d1419080404881c0304861100683c1c6040d000e4400081c00f411000e0b80c10782c032403401c552001c2906070200440100e011411000240c580c0c0003440030341480d030034104100d03280100035402d05106501c52304c4280101201001050f41e6400000c2d00180c2c12180c1500414014008560301e51b1242800e544511130604a400c81c1400c00030009007900b016402c041c080d803050031100d401c04602d0344d10240411400c14034904044024030400c2c19074007074984001c5030107108100400001920b8420305081401d840403503007d6400c22624400540c6429084139030180d0704448240e0b0343e1840008081c1c1602400d4400394012a0315 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 45598601 1250 45597351 45597389
    0x30a0f170f01030b0709030f060905010b1801080c0d030e0f030c0d08092e030209040603061e11041d09010908040608010311030c0a09050415020307030b040605090907031407 76
    0x34801d00c0e4180c9000b40c200a05580c3c1d13004040d1010705240c8001088956100d03480c0c804141240d020340030f014401d400103c4c0d42c20700000003840810311000b84601100311030004001c000f4040120802070182510400c03117201c10303038401404080e03294014600a0103081c1d003807242980c0a00609014201c0207249804220035030401e83c03000e0704481c44060007404800c6050784180001d0009880b40c0c4914110901d000312026400c9020b500051101c075007182e21203001100246042c02038020783d06052a1611003a00c1804000d81529150072682c40c80e400300300428807041b24060110400c840020001001d10b0f21a40c101500501c00720740302600262011501180035079201084504890084000c1d10768090380d0010036445001341d1290070303404207060808003c1103105400480d846400b0b800700301e4440303501074039030f40581e401200c1c80c2000a40e2101c41c54030514081c81032902a0005842034503031450029402aa50324640c0005846c02844404262028208112100251103008410028182e103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 45599851 1250 45598601 45598621
    0xf0405031b09011a0702030d08041b03020a050f060c071d0109050c03070c1a0114040e07082107050106031b0603020a0f030f06030f080c06010611030a0f17 68
    0x4140601842409000303a000d100d000003800007448844020580005039282111082d04150303400c102c488154801e00c404805a50140034001c200c440d25252014149060320f00300141170341542410205131124403051000da02c6994440c2c042d1042940ca100c625a0000d0000c1d0090085901c80c000031b114005022500c1c01c10b100d03804082d82d1a14a011340b460740c81d00d0341c00060741c80072240c0d80a0b00b0000e02c00030380070620072224184c0185c050790381444041d0b9064251400d500b4240c00141110707002116200c01820980300b4100c0b0a00760384041d0161500344003900307480c0d00c0503200e1061100700e40494501880d0307680303003251240c503403010081000503501c1c680340c90f25070381c4400e03014480b00e0803074400038540d0f0080c02100d078900c40aa848185048402c5003d50041c40f60801c2c0c81c0f08155204400b200003440241c03030341030350b0b030280382050340303401902c1c0340246800e0050b0060300802000c403424000c0c040300002030f6800305a80381480040240301040850b01c25a0050603503900c48105824440500300d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 45601101 1250 45599851 45599857
    0x2403010609090f030807021902090c1c0e070f0303090504091707060b09060a030f0f05030c100e0c030703080a0309050c150307030c03051306020d0212010f0609080a020906100c0501020f 81
    0x48a51611078941d9103070081a606c502c00380140019101a00030380e08010f107060ac08454ac041c090700d840354188501c20f10389040c91041b000c0761403110760360340c1c0821494010400c1850002c0c0301e4201d02c0381601d825a038000708121414440d841c091502c4500303500410484108002680307440e0031174203494240500f00800a49414012a801110200046500c81c00c00c40d80103400e907034004c2c0d040ca89920480e43c4038a6040c51010b015a00b0340020b0103c1d4150350030902c01804140c6003440c01142d102120f0f102c060902c1502d00d41e40b4820741c054642000040e24280a6504008a07030800003201003007424103a003040040c1e04229170044450f06039100e420300c4000614054865981c081008800c01e2105404541c1c080d1000c511034a40301c0103140003d08130b074005010040c1c1081c809403e10145201940d0161030a03088001c400e813408500380030050b03200c014003008144001c02401c41c07040b036402190807100c016001c1d03402194603907440581c03a801020540341ea01e03401002155110007580e03035440c1c0c6030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 45602351 1250 45601101 45601103
    0xa1815020a030e04051e130b100e100f06051804020301060f11010c120c02010902041b080702060c070206070503070203060109020910020c031507020703080d14010e2403010609090f 79
    0x300f43c04400740d814149032240c42c0c41940440345041c1d101c5800300d8500c1c0c44050040c441c40220005038252070010300c4804416018801d00203192603214103010301001c074000002e0a25014103c00d000c20043c40255000207001c44256044c0550765a440302d0007407000070701a0740e030250813500000001804543c072600045c40304c2c0c081d07903d81440941410050b0300760b960742892100003c3c11355192140c090055030000e003100020b0b0000180d142016070218040d02e20109450344400b0081d10300c0000c507078124610b1540b01d9030710301c040d20309882c240f0b198010074000c0240c06806401d000c030b80c00081040c200102c0d1141c5400900301d030019a500d03005100a503000518043c020455a1040f013140f5000041002802c400140a41400c01a054005010300001098081144214070000000c1121302000b80b00d0548d1501006c90015250b40310750860940686c01001c02005150401c04004041000c000c010084d8002141c100401c100029014110030f400c0320000b540307048603403820441d00c1c19043c0d54403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 45603601 1250 45602351 45602357
    0x30902031006031b0b0a0f050f0c0f010506010e010f0207180609020d1a0604030510090515040503090907140a0f030605220f050103020a0b16080a0c03030e0d050a1815020a03 76
    0x3580322008003c0e14020003032680f0108880207e404034580c000c80181c8000c080c4d0300102030070003641c4034030035207404204002c0c031005964038401c0c040d5550340f14250403000c100030b0030085440107416000035540e400714450011080c20300182080c1e054003540014000300080f220554648590448071002800d4448150240ba1400c1780081281d042a03000c3d41c0403290083d01414500358101c00c040040e103104141101c890061565040036800040405405103010b1070003540c0340e0421005001400760f0142c04202402400401042d81a03e80422640c2608203403034000040e824511083e0007030825908a1a444180c4242c16604d10058882d4014000c04040d800d0166071101c5001c203080340d40a00000c2e4000c7c7c082030090240f41244002030000e0183c050190b04240341603210b0a42c0340d00480ca2420014002d10082d4041c9503050081d4004656210054241014a000094103a11450300100c052104d070a40094028105164082c0144800645071072400c19014000f03407103840b030390022404 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 45604851 1250 45603601 45603653
    0xf030c0a031805011d1605010809030c07120303140421090503010e030904060b0306010e100e0d0f0203060618070c030c0c0608040b090102040803090d02030c040e0303070e1e0103090203100603 84
    0x200c05c00064254002c9040c1400600070505050044441450041034408240700400c401010b642040000d81c000b480040c0504528030300e0f80c40d0040646e01c0314010351056601200034003010440520782e8051215010b40b080d0991004110203072010152580215815460002c4180c070160000c0001c01d42d0707460480d1b0410119460308455001400f0aa41846c0000d0b0114070880490401521071144240c2c282069a041c51501001500301115403408036065a4048451001c5041c20040203801c040101c50106034014180113082e00c00704014940002c010406642405045c0141c00c103801060300310280101c0310b6142c00e000307418600c05940446c1e023003511038005041a18103100b40c1c6c0c00e485283d0081c0d4503103400101004036540000301c0507641030144070b44031402d40c1d40b140315071821911010065a102d16140e400030b05140c441c03a40c0a40514450300300b0001c6902004240e074550b00c02401c00003249039081c00840d1400400e2006054190714107140407040c4074000d422414110150022180 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 45606101 1250 45604851 45604901
    0x306080d02160501110304080d1e050910080606090d081201060903030c02041a03010507020a15020406080604091a04080903070b040806040b060102100c0c1203020f030c0a03180501 79
    0x1079640c0894207010181d4201d000b0034401c66110740c1c4001c0000700c0107400c803402c080d12109014100202440b2020204410b840080740740540b40d51941c2c06042c1c1070603c281000b000e840494040b030184943c0340d0801c015040003501944d2480241d8144040c09030484040c42c5107880c03e0200d0303500c03440f62184400d10f0f22000050440c461740040050301c1e81617882c0e240c0c400d055428040500a040d98150780c0e00b40c0040800b089450900c1124410303001ea500504500d5018204000d59511140d800f19a041c0100300c1030103225000300e0720f150414401d5034006999802414060314040d0b04501c2103440065a1051206111152000d058661000c40a03250225920352402c3c0192083d84030300d03055600500005008100040d03804d50780700700180152416000084810b204403910f1844140201d2500485c41d0140000e0122010400d115810110f16214800711000744034040101444425503000036410842803007600680010140300442281d0320001e80f41140c060300d1500590b0180002e0401044 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 45607351 1250 45606101 45606103
    0x312091a1005030307030c0213090f170c0304051c05010504030503011401090e0c0703030617010f0b0d020a030206030405010b150306040e0606091f05060a0305060108130b150409120306080d02 84
    0x8411102c00400071441c010490394299001c800c91001070743c7c041c600040309a5144c2203401030ba955940720307418982ca00045840e14904c182c0d01c200c4100711180041c083e201030b24078004125001d07220304440491055544076070441d00c041540c00020102d500f440c050004041c0c01c00080c42c10f940c1d904411401ea403801c1001142e0481c001c0c403800303010711158404a42c1d0f1421000050050500902d80401d01c2030300d405250703c200944441d180d046a41d9100c0381d0a840d001d910030002c498604a4452511142d0383d000126000c42e54000a4451500000850108602580018200c3c0c00c0941101d145002549426005820888842c0c1c02241445c6481c50240d0b404200e05120300d400600300f0342c45869170000c40401c02e02c0c070044001c0b451601903000c05c156803440042c100350100c0340d5000c42d03207280c840d000510484002c0d00000c101c5e00000b4440c0b001400348030099900c0916081e2540c115160a4000740c090a0f6010024003c0c41c0c0c02000c0082441d41074018034140c81540003143e0790b0720f131698412 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 45608601 1250 45607351 45607381
    0x2802030a0503010b160b07020c0111010504020901091d01050406020d060503030a120c030b0402030406020a090b04030b04030e0402070204090605041b030206040510020a210e01080705160312091a 85
    0x8203000a004200502403059100081e10014121035449941e5003403d80e140884044282e4003000940d1200d2400c0a0030341e0310107208100812010000c0c0598240380c0d000c9a0456018040d18213020344070600742410f0800d00030081102c90300d40c002444241403d00b071200c003c1d40300313040c00311182d41031403404507032401c0000454206c3c03000d566480140c5c65400000000803c1d0b0b001211082646802c1c00343c0d45a030b0b40d400030f580514056940142c0d101d613440300103082c0b0030b0301f0f13172042042070700a100402c04507803012111540aa010700f4220f60181c040e5000030020b10075400b009620524084a800038001d8a500503480395200b4843c0301c40b50115001c4003444184a03100081d80010708000034480f5003440040e1080d28421070046401c05101540c4407006a946580303082c8540d410b545102c54031542c04185003018000a087c5690b41c1d060440004040cad1068403424040319000e005803100b010701c03c2002c01981640034004000700480c9260201c81c0c0181c10001e00808004000810360302030310b03403000c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 45609851 1250 45608601 45608617
    0xb0913120e010203070609060b0a09021305031c0302072306041205040528050603040f03090e040206030a0c0c05010606020d090801020a0504051012020703031b0e101103040b280203 79
    0x6608245e07096559002500f08110222145503ca5140c0c0b0201c1e00d40b166410041c101c0300320056260700b48490000c0780c15085070b1042e8420b502940060700051442c0644174280b41152901581d42c98243c10800c0c500c010304040c040403105d5601361300c130101c10082803ca000314858410620703044c645940c2100c490065020342a8840303150562054010074083c4520500052004045640ca07641e00009040390821174080d030f24072008180e428105603102c0c42020140000118002d014142500860681d0100500d2600318542d01d00c10030f815903026450300c143e01c0e0390000c024030185440d900000c1d214900510664041000c0000200b0960380600a0740d07440c0309181c0ea11420035140808126031041c140021605025411050700c40700310240c0000c0201d180651404918600c50765070922010030011480010404183c0b010681942d030100007016450030f6117003401c51441c12040303243c2903201e1980038013240d00c40010a00c1e100c0c0403050741030100c400280c440d8014551840f00503a1a171003070300300c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 45611101 1250 45609851 45609853
    0x10605040909050c040515190315050a1e0b010216050907050307050f0406050702010e041a060c12070f05120301031703040c051e040501081b130b0913120e0102 70
    0x306119041d4903a0081e000c035030082040340c0c0103038113100204040721401c3d40d000d082c1104820b004660390401c071a159081c0c40d00e003800c00c0c0b141031442e151186010101d80c1581512070700d41011403043e14080d0082c01c10503000498003544c0c07103c2e180d142001003076000855409405101100050f00c03070504241800c940c0f0140c60321000d03580300c0d00b0031030751544020140424407030b050049143d0481e0540c0a0406071020740c840325035071502400003500c3d50303440c0d5170304038815410441c40340315031010b86080d02115034080d5101303602c0f804074949003410844801494040160046200790511a0314007070041c1d001d010b039055900c9904d8047c060355880c0f00c240009030001c643d000b8079454501c0c1d4000115803090003401a542c1480d110000216040549070f8001c0b821802c01c1200800c510b80751094600402640b030061456040104c0c0204542b44c2643d460f40c070400341c0150720f4803e00340b103420048601c8001000e4000c54540301214464854407408203460101c1c10700c045500a601684012209001c160 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 45612351 1250 45611101 45611107
    0xb0c0c030315120a080d1b1b032a060f0207050303070e06040302090103060c090801020c0c010509120d080f070206010521010e060903041404090305070b09030c03041401110105010605 80
    0x1400c080c00c150001d2a1580c02400c401c940c192841002d21804c08014424190319941d4070014010400707444122070580854485d48030100d40e0260440c0f4800141c0300303644420040f60360a0304099550040022043d05018000051600320a2003c6046c50f4081e10074042080b841c8001c0e8601c00c00c80c01b8201c3e000b00315500400c003095030540034641145001c0002007041d49000c0e100c2d0b004c9068190207074411958192039030012000c103500302004401a080301c1008608000220b088aa0b9800c40c01340140d040c00400581c81030b103034503007007204e901103a2400200c880e000c19059008004d40300440d460207402e200c0304049880130388085100e904840c1b004000d0a0707514510290b400b4510308002442501d507507980307003d8801d03110030302c40240710390780d00c00145071203600d04401c2103d030034408010b50344298900031503180003d4200301642c180e19048261b06a090356220200e41c175600c01e000700064944000704d030008200030752041002503400300ba0b9403180c0400c059456030b42610001e00443e40402c0d400c2c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 45613601 1250 45612351 45612361
    0xd1401030b0402091003080a0809010b01080928080c07060212040305030901030f090b0f060f0103090b0f040305041205010507120b01080402040f141006180602030412020f0315040b0c0c0303 83
    0xc03d904030101c0319201c14543d071ba0fa5920441e6078001c5400c2c0003c07071040410003026401c2031280c51030440e42030038403454a261868655441d070214000034204030703010f0500141c000390307103104030f10010b0f62100d4400d030741d8041d80c0c0386550398900502c60f4a00601c650703081000d10a02c1070b81910110f13940480290306040c01032006501034411072091440b981e81e03907141840841c8028071024081d00c00541e4a80c0b880c1004000d1000c5005002c1c41941854105028080025402c044103070340000440340340c0e681a207071460203c03442e10582e4814400c050004070384c00240141980b1503800307203180703807100d4203d000542000001d6070103804040d8082620b1400113400340c1802d4100300e22480702c80c5000281507000006640c1504401d44841d200ea280c2d9800a0084079040b44010142100c0c41c00c1c0c1c9410107243c040c0003552403142d2300606007081d0500410004648501c02c0302c0c8200b240c020240d4507046018560303001001e008840a9580c000303008049603207043c4080490b43d1164408000d10318560f12 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 45614851 1250 45613601 45613609
    0x8070f050108040602090d14010b030a080403020d020105130b030601030c030902030303040611091801030204180b010317040b0c0102030621070e060f220c08060609040921050d1401030b0402 83
    0x600075600c3e103800304649400c030ba8a040a0f42d001910407923005507030f040040c2c1c01600b1a0700041c5201d000f13034005107000d004a0316500c2644d04580d4102c4451042c0e03019440100d0f41d9024901d03074078201c0c06038038801080354110035001c1e5205480aa074100070a08451000301d00303564039000040d406410400215001c14155044009212801041d0b03034034001c800c0001c0340c00510400301014400f08690014000c40c0303802d020385100c01000d040c0100e83d40070706854087c410981880020000c10b5105401a01d840303403002901c0081050164058403600010562400303075008841051080c800c458415180302d890104d5510350300544401070400500f8241e0510820030040c10041d882030043c1400c1c1c88070781d03903203040910b40c412880d8440c8145d00610300d0342c026505c8842c0c1c02024000c00808200050300c0d80400e942c0684801c0790042180309090800c42e20344202c041c4039039440c850a0200c00c07a100d8106000340314000c00b07403200700070100c5002c04250544800303004c000d15090f8500085405468 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 45616101 1250 45614851 45614867
    0x203030708070e0409080a0207060201060e010b040e130203010203040c06080702012d0603050604050a020109090507170403030f0501060503180105090a14100501031a010b03090606040c030b1c060608070f0501 91
    0x9005880045c24654507203940c44507800050034a00140e1200c14144a42e560a000c3c0d00014100e6500030100da50510743c030001c0c18001d6024441c00c0384141c4002491800440242e645140e40182c000c545d02d0501e41071030101266a0300507107020810041c041071455105100d90074145284800c49a515080403041c050410100d424a500280c0c03540c201101103041403000c0b60245100710020841a8080d01c00988020080c0d4170100a1600d80800c209d82580c00c0070b6a00044403022900b40501c0d6100e1030190010012a0200c100003882c001c00490303043d401c0300041d0301a4107071009120800042c44845402d83d00300f241d40710032076000001c522001030030207061440d003000140142c42501041005120885509920507980281c03080b0390001c031342d07007942c185902504001c80d0092452910703c0540b0f075030388009002176004503901c240e0001c40a00c41d030b100c80803d100c014118841401c500e922000300d06040c90007603d0803031903c480017922501c00914841241d400c0b20340340c41c03010714040c015147c0038 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 45617351 1250 45616101 45616127
    0x1031a150108090708011b0f1d090703060806040b06130608070b07020a170106060f050301080d18080a0308040510050108100e21070c050303041214030405060309031801020303070807 80
    0xc881d10101041102080c00b611414821f074410805001d0307503d090081c01080c030901c020742844001c10041400f0b44689400c41d14414050700d17045840d0b19017070021802403a19511a138a9400707984107010811010750000383c001c040c101c0b841e40b0803d4a0001243c01c4401c54440c0340890361100307004000e074071400000703044501e000500f07041e0b551f4bd5400004010304070100321a041c0740d55804c803c0c45803503001601a0849580c51030103030300f1903041c0900c2591340c20340c942040c4180400c03402d8030041c59400c2c480302d4015000388801c1e1081c104ca2481c003e02201c01c1620704484d180191003032078040310058400c1a040300c0003078006081c1140100440070050401c03140c251042e00410358014000111200002a40c2c1701d04908640da59419051415218102e0b4010b03501c290800c100811490104590300203c0030b400c041c0700b40e01d8010071254030b8a14811503000c250132032800320810800c0b900100c003400d400040d606d40c1203d5000740c0300049031139120032940540818241000b1035449803207810388980003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 45618601 1250 45617351 45617353
    0x60f081b03010b03010c0c0b010e0408030a020904060510020a11030307030e060c03071205030103020301050a050c0a0311120a0905060c0715272001020f03070204050916030501020301031a15010809 86
    0x403c0c00f640c0803909464403004071070003243c0c41c210900100000c8402c02130040c42107024400b45810507980b804220310001d0428408150081004941c03035a80f0f40c48280101070051a407035010102e0b842c06911440110f0080e2030201c1c5040904609003004400c80e910b0b01e60654a5030341070b070031501c1080103680203c002001181b1040c085000018030041801920344299182d250b269807552041600b5a00000e044034605810182404441c049030070546400c0b0489003008501c0046121520205010300d01026280b012504180400481564049a100c1e401403051383d510340e03152004a600c80c401c4800003420300312450b0702a84404016400b10052400c80380c05001c0c092030045041038003a401c0d2100365030103100d80d0b008403002400c024030120036990a0025110490511a8031500d0307000780c88000e0b01840c0ca410004141c620280002010312200b50202c6000030745904006000390404d00044404103020700c0e125200c0e0350314008030b9102d44101c0130803221b84603410b0011540044080c00340e40403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 45619851 1250 45618601 45618611
    0x7030303020f0f0d1d0d020606120f10020c0c01051305060306060403140c01020c100c080f040f0f0302130b09061003180605040b010b03010f03140c0a150201060f081b0301 75
    0xb0003a100008000700a41ca200105d56444980901d440803855007a04030360b640d102107484813507141c000c184c15502c41c008072488403104040d000c0250420b400b400c0801264010030100c7c0c0c0c215945a4040e085800c203440c21120032052010040d07860348a1020f00c0c07003011031030500070407107880c1c004000d40d44958041d000c907007000c0e40c0c0e6440b00c00a2204078071300803194024086584055078100214030581000311103040c4100b0705444094079223994070340003812200740080c0003003030464102d08480081c5401c0c100b20340741c280e0301c440050303a0a10f1800124450528000354600c0302a00703002d032965242000b414a5030948502041045540040c15a003080c1f40d2a90880c4840301c2103044030501d004e01803480030800d46010b141503401e0850580299512000c01c0c80140451000300c0c00500c1a01d80c0120308041403482c40e030510380380641c205c1c0d4450b40105880342c0840d43d540c100f60385030000d80e042c1d002802a5622040302d010954400e0260344125404054030201c80340d06c0d90042ca24010000c0c0002070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 45621101 1250 45619851 45619867
    0x1030c1a07080304050c0f0411090402030c04050d0b090f0102131206110f0717030108030708070c0308040f0314010b03120f0d02160b0703110a030506010e031506010f0c0507030303020f 81
    0x846400403202622103411131b03444a00340741070440903448030600c115400c0040f00340f020016000e5004011503180620b0380440080e41c04147c100885000d004000e0201090048614001c80610030842c4d00e43c510340280b00c10013101079014000c3d643c040d1030f680340e034480c0070b400c04001e41c01c59101005c06031a12626085000a402480002820ba030a43e500d2600c0c4d49201c54100180c0c804409000044480030400c010048d426011083c2c07451942e004c0902030b654542820701804490302600040e00720000000d00140c0c00218241810131244a0031148250407080c03084c26003224240c0c0b4240e50990002c00e040301107280742000800002c441808400d0800440c4407202d412604071038032000c25659561a0034050100c1e42500702d0740103441745030510120441143e00f040602406143c01c0500d40c0b1900490b20f540c1c0171755014030071028040d044031038451b80c0c50307031260a1a1094800ca804110381048422103144190440d00740301d504240142a032a2950768120001c0d48034001071213200d481481411 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 45622351 1250 45621101 45621113
    0x1509060c0b040303230114030723180106020102071406040c0933210f02040b010504030501050a090b070e01270b0703050c070b04180f1107060e060f01030c1a07 70
    0x48604001003400c1c550f10b42c10090107c5020040406940c0310b9444a40c0812400d803802c0000c03a07403d00c9902c1c400507960700b0600804e1a041c120402c000e0f4410f0820004211180d0560107410500c1c001d841300660058407041d16511340106807406001118000002d014101c030130b0b042540074442c0c40d41c000d03900c59121100543c181801d82a4520f180b00307000c0e0704000800e0041080007511100a0780c980b85002d076035603140a040302020b0000d000d240c0f00c0700d002d07400360701400c103450055030040001d1007149440d0928034002d00d11036038201c410201c01c0000c9510148500c2d101442001c060311114003071984030704001c0a0810b1220507400141d40340d48081001034004c2c0c040c00d2103e2280c0c90340c075101d607542d01c106030070450075030030403288180140406c000300702040c05400601d890710000007503010441910783c0701518402581c21000d40000540e1000c01a840d884070401c03000d01c078242d0b001500c490186e40000c400a20010345100441c0d0780c1407003801003000041d1030818020480d1843d001050b580c0c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 45623601 1250 45622351 45622391
    0x103050a0b180c041d040204050108061003030c08040315051e01060507030c0c080f030403030206070201090c03060e010b04180b01050312030714040f03060b0418050303071206031a011509060c0b040303 88
    0x80031000c1720b54024401141081e000d0b407405050340d5006007150b89000d0000c1032846e40725210280802c100603404100340100d800454020b0340d00a007055911911070b0604601800f0244c0344650020980c00118054000585c0303024141c62640d900c1c0382c6400c1c0240c4049585080c4220305480d100c08c030b40800204000d04121000d2401002c2010b0340d02ca51842c18040d0415000034050320540e418802a40300140d0004007000070782c0e5001c600040d001c4d85000c6003500406850200700d81042c0341c02144041050507103130140e2418072070341c0040c0082c2e8a55040c1900e900417005000041403041c400305a1043c05035075802c40300050200c001d81825a95214040fa00701c140d0300c140d41c0e082d0383c0d00500f002410113005c0c46070703900e00c10040350000c401107039101941d07072100501a100b0481c07001e040303101c032019541210b0001c580010704a070024081d20300000e01d680081c40b030440d6244240145070b10030740c047e503820301c1160703c503841e0503a02d1900c6890703001c1c18030300003807049041642d10440c007545020342e1545 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 45624851 1250 45623601 45623639
    0xc010608010c1808160506070501020c060106050d0f09020a0b0a0203070609031709150103110a0504110c060112150504030c06020307020a03020706050f2a03070f020103050a0b180c04 80
    0xd80b141c43d040030240d11040c82800e03013040e80c0c144c002a44c00301143e1078006405049420a036459039481c029824140d00902071014800032502580b000014156400000303480c841d0907010f400c2081e40c0380103030703103030121144444002c0d081505a02d0404c8000c40d850003418158a80d030042e2441c1460703d9503505d04880440f501180887c0b440000250a81d00c8030000641c400103c2c4000c1c1188801004d403d0f011640510000300444101c2c03010580c2a1503100d49000180b801600a05c41140140e980742c405401114440800f40b003003800001c0c60107460700a218040d40c020651000c0c50040d80390203005800300030300580a010046114000041c1d1503c0158400c0c80945c3c044c110f100218a0001e0800c6540e40c03040d4200442446050300da40d00c040200c03a440050402c3c0c2225602e00c12101c00040854400c00c0012800301140340414030400b0f01d0003c01d202d100340c4c0c0811003139490480040440d143c003036550b900002d0f00111100c3d0005d400883c140c0114000122034200b580d517103051001d100f035000c8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 45626101 1250 45624851 45624857
    0x605090a05150402180424030b041403040f0e06010201021b01020c060c090a09050421020d0e060f0a0c03090302040507030204030501140f06280e15040618020c010608010c 75
    0x810444540c4001200342d180c190200e5041d480d01c600102021190410941e0b80781c425966001d1004584601401c2c20041c407180031216140d896480c1895603554a085038180d03040020312f01c10032442038021080b0341c19218000a840d462608001d110300d5140d10091100303040d5076003005002e55000d00d550202e400c802c080c070009640d900b1b90310085418114047e081d000411410700a03078140c0d07035418009105503500200005413956036418591040403240c0b031041c3c0811400001440419400f0030a181c1440e541d4680042c3c11040c00300b4801c0c81d1240040085042c8024001d8100440c4241c0364469118001d14100c00103680700d4000404541064940b880802d030f0000d81041004020f000d24103c0794610800c03000303d440c01044030400100014030140c41885625898601c12030b40302d00b4489081c0440642c0d013480ba444da000f00036104029226a017031009091005142446d040c080c210581c0c001044011100003070003030a801941010f10416100e5403600d0340414241c00910801001122640e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 45627351 1250 45626101 45626111
    0x3130501120603031b0204090b130210050301050a090b030a1505011e080304150c0f03020601031a040c05040e01092108010f080303190212130b0109021206060c010605090a 75
    0x5490071903040c00c00d075005400c0400420104c1d03001070041070102411070900f200d00115100190090603c0e80e00240941c0001091190380c080c0c440c0b07111319061098038146d078020703207d5100391101e0101f4416a40d00000f004403d1042000c0b0307811910000030f01904a032068007503942d400826031618202e00343c40555810040004221b004100049003e40718115400d42d42010b140b0381d01c3c0d10441c0910010280100c0303036000302030300c10348082005642100c01240b045615140007500d8010030300c801c1d103542c0e240d4410700d0800030120349002d01507540304c40700900187c40d0400b80806040034281e09041950f072034005030301245e603203500d410070403480c0007800c22801c0c1c101c54040c01a0f90706810030545800e034280144003607d0300008498100400e8a07444584001c1c0e07041800c0a4411104d000950341540f4040c4415401c107001445040c81c8543c11000d41e50380c0701e041040403030148140e407554840b5040c000c181c19082140060014000c40000401e84580700d102203104848141c45015140d507540d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 45628601 1250 45627351 45627359
    0x7030e0c0607050a14030708030901090c09050f040201031508030408071a120a0209061603050c060a0c020c0d050a0c0b0310052d040f0f0218150a110f0313 68
    0xc0c400485980c1040301c1182c2031060b65240d281d55200c1031000141008542814040541001c20a44001d168403c050542d2407070091301301406402c1001084842034154040461400340341d004945c4600018041c50089503615001103010781400000c4803103c40b040c0101140c2c3d2030080c00144092300c540e00040051504d4104140e26299810700040a841803d004c01d100224002c0e803d130350070800440c2d0250302c4400d46000100e540c03064540705100c02415080401c1016000005002100000030595800d0750710740803000151903a640e403180c0160405107521140345071280506010038011012100c2c60903195840d150441641d0b0012a03902c000401000302d0424420ba001c0050310084d6154484a81402c1020b03e907080c1002c102c2944080c20710b4000d0031070711140c1c480c804498400d01d041c050004031025500080d8402420345240b10055484034003681061076041c205a01e010f0034403403030801e08501c01c498074000041580103d009034014295805410405840009111011081e400e403070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 45629851 1250 45628601 45628603
    0xf1908060c0307081801060503030a0f020d0c080901030903020c0d1b080d0801050603060f0409060605040f020301120809130e0607090603140c180d0c05040e07031518080307030e 78
    0x4040141d040700400412a20b194000c031a60707000940024055000a4140442400b40480b40c010035014800440e1060113558001c2c2e800003c0c500759004d9600e910005041110801030080000c2c140d04000c001d6482c807948a64001200c0e14002c3c81598201d07540a00060b6500318840000d0707034161030405520501d42519200e0700c1c000c226180c0180351110b0080400b6040c81e60522502d0b104250100c0080d40645414184026602e8010410001044145480c2000380014011b0a0085191900d0315045103000d1086030b058400840302d043c5000714560346c2c40d03503d40c0005149030b08110413440340030f0590494050740e418080940080e01052805000003011080c855008800309814100042012011003220b11782001510103000c1eaaa01e040c43c130240c04038440408950090340c00c040c0d60041c480580321090958130100c41c00d1200d4079011181715603416940c04040c1903540c070508580c4445c40c8940c0420300e48280758400714440f450340c2e214400903410484038000440d440d06403000504030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 45631101 1250 45629851 45629863
    0x2060301090b0a060f02060f130204020a08070305060103020715020f07140a030305071d010e0604080d0302030a0b0409050607081504020a0804020901050406080c22020703051c06060c0b060f1908 85
    0x104c0703071818054a4401c41c60083d0707550009007061102400c0d20700442d01907010003110b0415907401800540d942da5690788002d048500448010001a1405005c20241c1d072081c021140e0072030f0051444050303107422450580c000d40c890f880c20000100300b0044100040c1c404480044009800c9002c1c00c0164903505015003a154000c06043c20004810307420501c0040764030f0650400d070000e181800da141d145c01c1c04280c0b603210725088031106200e003407544410320741d141d002180316410a9905200704000c0d0414002138a84980e0001e01d10742000000400b028401c0d044981c0c031a40c00500e10308202d0f1604040703001c81c0c1c0f25404100c00103080c101004150306115011500500f01628100040d6192543c4692130f089035441981c400c5c005500744800300b4480c524000d5603010640c50456031160b06140190040d030080b0501181d07541e40c0115000440c15502c62136040f00d41c19100d80d48684850780d00c041301c540c802040f10f83c1c05041c48082c0e4209840d010348032022101c2c54080342d40040d041c0000107191003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 45632351 1250 45631101 45631109
    0x60b03071a072006040b09040f0608010605012309150409020304030807170108030906070206120c090306010b040e0601030b010302120a0509120414060c070305030304050a150e07030b0a020702060301090b0a 90
    0x20540e0b403010620b40e121343e411281201e40c0103030110340b1244001d00085c05003000e81c11484080f41000804030310f0301e030198452802c03030b04262a03441c41035042d000500d02003040489200c05281003800050040c1c1421000c580c090050149510300e0140c81d00610710882c0c1040c0c800b0b6000651300c1e002c1012003600807010606001100042000710342c135001c1080d58070710400503034601981c0c0c042440c90454544c2415030302e90710100c0500c08402e00d003030603081d00c054200690092107441030000025190521408840c1951240b881c01e110715510040107602034100040d03800e04069003000001408600c52007814001c2e4101080411b19040c0042c24524bc944480c00d000c0000008000070443c030301904a00c2401d034602030725042e86841c0202c0c6403504002c0c0907407024200b03000020801003080808030f071a02666203d101c4000d002111446400126240c80310081101d0703200c0f04c014008244142050386c0d00c100001000361030840958080303840c5400a0f4061410980c03100504a030341c1c0380a8803104090 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 45633601 1250 45632351 45632393
    0x9060305010b09090c0d0603050703060e12031302060319140103060c0905010e041d060702060a050117210904091a01050f090a02030406060b0711030705010813060b03071a07 76
    0x64031080004904c4880075040400741c41000540706031070401034100d54002c50b000003e4072002642c1e820000007401e9814980d4070300707002e0712000142181100d030940b402000401c1c100501d0344840e45c01c0c42010387c400b03021020112000c0e81a451801198014032141c0e011200c00d400c0654950300c1c0c07005c2580c18001014062080c400b50a00860f40d0040d1840f060b51421180491a003414048509903602540c144660500500d0700304038220350005001400349006031010400c0d41c0e40c17408145484200c4c00c5e000f003483e8004901c0303100305d51005c1095030390b1a0440203010345041c140e00300190886452940403030b8108400e440407004500c984881e02c0c0145802e0300c241350f502002400081c03600354010301c2d503892254040301007414400154460809000c01c103110b01e40d21051814942e4001141c12030b094072034850408003007259481144002d0180f501001d216440c00c240e80d607414050f00309561442e41500c0b5031800002c8a0642c040300d0b40c0354a00614459030344811501b000c030007043c1d00a19101e45 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 45634851 1250 45633601 45633607
    0xc06020d14070c0e0423060c09040207230a150c0206040f03020109020a090203060907090602120a030b10111b030307060c0c140d11010908030609060d05010c09060305010b 75
    0x1a00e0340040415400c0c5580c20081566520240751401e86044a40c1146020021802c1000304010643c0700505488809940040d010003200c1b1302c00799558000c40e0300d1851814284044040380c1007907000340c6801445809025881015a00c0c403010310b82c2040380f9161160f004c400741209100b00504921900302c0c0c076210901040c00890400b80d03440700c01800c01800c01c05000543700c1418401e51040041c5540102003503800c940d1104040c01030741060b109144920341d8000440c041c9405494034404640f02e07500074166250304d007010a5150b03000f441d0003505241d00ea400e00da0007a81d42c14031038448800c6580302d03c8000700440712070601d00740d920f0356815441001c45d240c0892603a03000041ea44070036031103640441c0600e55908106c4d0160110307103004155640c07001030f00408450211301c1000440e100e40d40c07100c0d40c2c4440f0040c623080c0c40442e40042d2442c607081011030340c1414502400c0340d02404c0a030400040c2c600a5507400d00315941c1c0200d4030300003001c031351042c042640d140c00b4441c0141080006181 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 45636101 1250 45634851 45634873
    0x9270f02030a233402010209040c03020702010c030e0303040b030112050c010908060109110408011d190209010312050c0a050703020907050306060a0305090124050306010e1014041d0a0c0602 83
    0x2443c1c04040d15110500c2d10090000741c4d02140100201100c20a10101c80c0e00320a0802001c0e000c0c2d0484047d50380305034109a0050145d034030074401d56410b9030301651102d91406190300c058500e09940b20070150580401c0001240301d4a041c402140207180424980401c04820308060f400c01900c0c1c14a14104010340a0070007000c1ca0009080e410360303a450b0000219443d016421300028031a1340c3c005006942418000b410110705060b40790303540c0d8519020303a200c62158407480180c628030f5440096000d05040300600110724038461040303040b50039003801441c000782084807038a03006652030120344981c8904018400c50400c01030307040e0444c0c014100303540ac40c01c0c40f000162041c040c2d50440410035550303000080c0c2140094005415580c20003040c1000008103078000b08000d05507000b150b009108500000039031071681c0d00200d200e9601ca000e00441c00c1d050802c180341540c0a1004aa0711135101c0c8801c9a23800074148480304400e903003000400884007585001844032415620503415500030f010070700 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 45637351 1250 45636101 45636161
    0x92c070506030c032211090f1003030309020a0806010f091a0f04200a2c0109030807050304210506090a020306070309020d0b01030b0718050109270f02030a 68
    0x9403c4211001c0f07040d10382d039071200e8110110403002c00607041c00c480840780c0020300000014062910500b55903424250380c80d40d07905a511130307050b00c0000000ca50a402000840d2103a804500d25900c001c06940140e60b903120028601f004c2a04001c40c03075400000100485500d511802103982400701302201108240c10002d02501c41f041c0001303003c0ca4842c00c51610f51003601c4c8002d40450503164bc52921816489001000c003606440200301e035244a01c903690003000741441e040c81241d4142c1d540c3d00b0560455544401a0304032000881d52031005000114224003580c501a40b04410b1500700010311840e41041490144040c14002c0c003034014420340c0026031004035109920011606022580244510100b07030148403200c005420050f01000101c20000c21088030303406000d841d51020309442001490000c101d14034400e850205007141010040300306104e160381003031101c90f035242d0380c580b41c200034800640b56002c1a1204c002e600004001d070301541440396140c0b0b0282d11140201c1980c400c1404 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 45638601 1250 45637351 45637357
    0x100609080c0904051005010602030c01150b030412051c090309060528090504110301090c02030a021506010c05010f05040201030c14030103060b0301091a04030e0d12030e010204092c070506 82
    0x840e00407102c203000581030080c200184584400100c10130041903035981c0c4000d4507a040034a00300101d50034113050500d002d4000011000351020644c01c0c520b15122580c89810302d210303d071004c105100d014814405c00c441d03c00c0c000561400c13130240114995050b407500a03c1002c054109805110341405402d80078004440086015962880c181444417036160003510403501642c401648542005102100e4113202800b40d4101e42e80c500c2c041c00b00240303141d001d903264000c1d0203e80d401607018035202403101d03c0f110f03689600620181412100c0e4110f40d120a1700752080150b003110500e40700d005000440d6410b11070296044241e1510f154025045001e19100c0d01c8188000b03400c2c113807206404401c941e400e52041162550041c00d4a9a41e07207210242c80580341c08039400d4021864400c1050010b00340100c0720074a1070341c410341200e819560b5400640042c0591401250291360a10001c14680340501c200c0c120050300c40701c20f144000aa28920000c94840142158281c12008042040da1294016 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 45639851 1250 45638601 45638623
    0x11030a0b04020903032b11030708060d020d03020f0f0303010f0902030a110304050a03020d02120406111203010f0806090109020307030b07030f140a050604270804030b09010510060908 80
    0x45210028840058083e0050005107130b03050000164604000d2400c07000c0400b40011851600754403980b4810342c204580c5401030901c0030200400000f100d1034854028642d1054000300071b0500c00104e45c010800052803403604401603400144441c180220270803840c840165001e00131441d41d03040c1008000c1d0092980304145c90660044080790b002e807a190040382e404144080b94503128a42400e0035603440350440401d4000d8054000750075141803002c61001c2120400e080c144c3d03c3d140c903000040780c004030310f10034900c410f0080030b641c15440d00e05074000358000c0c24461075000f111030a0540707603030a100002d042c02c10304d40c2c501800d1f100183c8011542c101183d812103104038890b40c820b10306802401d03a80504540c0b03945030040c0750403045040c586071400344007400da04020640d109400d000403500d055100e4444001c500a001c00680c0c1017099100343c0e0341c41001070314107080da20381d90900300c1c200a0b14611010307511001008640414426590014565031a05075081072a02210549540718602 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 45641101 1250 45639851 45639871
    0xb1912060e0f070609060207050609100c050a06290d0303050c07050d170129031e010f1d04030e04020702040b090403090905130b0105090a09050703050a03121103 71
    0x405000140d80501d01103803035001030360100100d414216807201c4450003410003041c19a0800b00c0c2031440042c412083d00c4020b007907180360940601c20882245064100c06040202d5031b0180000900c090040045451003000045440340910311100114034040c00040003010781c0141c0401c0990310003031140c800e681c2508000565403141c4491882a209d40c1d20301070258072a01d014868010750140310a0120300030b140115540c0e9803118609030b0351200701d02c080035212400245000e0420405402103400c604450310601c5035a01089065000391800d90006500310a61a41004100d09242d056144215495400503e81c50141c5c0c014141e00d800c80e09507409294041006411512141e0100d034001c10010180e50481c41c081c6401811580c1074041c0b00100f9040c50003040180750800d01446416038030920340800b581c00c00050107010800141548c0c081031b240c00140010a00a00c034440203580980c1c003400803171a10f800c0c003070400d004011302c481c480c500e484020380c010007000042e20740200043c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 45642351 1250 45641101 45641129
    0x507020607030e0d080307090e090a1103010f0e1b01050702031b0604030b0a0b01110705030c0405040804151713170904090c08010204061404120212010e01110705010b19 74
    0x2003403c903020032103142e80e1600b01c043e620056041c803404902035441000b05070b85540c0ca1b55166503480144c4602500e000b8141d40c85084201c001860550714a50400f4002d80005038816a51074100700b541d80f545000c2140b50001e65500940d0783e0001160300035030f682800e001e03103000540e40c040703a901c403002118100064a4080300c5245642c4500417a0f0003190004560604ca050010505000f0030301441c0c15030201d1400800d0091044003c02c0740d40403200010080c00424441c10b00740320141100900440350600200004202c000807001c50740a103004540d1104090440000d00b2850b1810182400c0c2c4c01441c3e0143c0c910002d41d07040c00d44200d0345807405040d07032034586080c00702e40607001c20718000700440f038450303800300f103070f000560141003140e0071503807102001070045082c01818443c40c000d9480400b03040010f40b015080840c80c0c3d9807207807a014000200861a130020328211903000c007040c110807800007000002d0110034010000440c0e8203ea02800c556032400304010120301500c5940000c144103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 45643601 1250 45642351 45642353
    0x3020f0c0a260a060506010e0916030b0109050303070302030a171501030e150103111c05070905060d0c0609030b0603010b130c0318050604020a060206011818020402221202010507020607 81
    0x10b140581032100c200d0044a004807043d240c03120142c00101d03910303130000742080100c41052074a22207a0b070248190008190a19641107401c07030181019030a41c9050080607240011180c4080008080345806039003c1d646450030041d000b0308802d8008520301200c0d81035000c0c40000c590f4440021000c00d03003400c000560000034840300d41000444103441c00007040d0035000000b40408210b10502c0300c0703001c4890420065121030704621a4030103840c09006680703d46d90601901189911454100200403e036014103105603503411008103240e08210002085240c1c2001001000007500b44c001e40210003d004c2808080003050b8409103210500b507100c0e441d040344aa1040c000d9011034100340c0d4403400b1038000304040c2407281d80d61000360b5003240644001103001808034070204945040c0c804403000c003c0001c82015581d00a4401d4200e400030b04440740b0a8680142c3d15840100840000c0c811107141c0c04000b040c0514403d4065400700c50340e810703d04c10601c0140ea0200888400a6040720034540310902 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 45644851 1250 45643601 45643649
    0x304050d0303090602131403032106010c050d03020c0c06040803071101050c0102070f020f0301050603070b0c030f0d0b030c0906010215100b0a0c05100c05090d0510021603020f0c0a 79
    0x700c3d070b0050b20781440025900100c0395904080710596204202d160250380c0640c0500d1794a1154070580d4141e1400410350208811041c4840c582040c41450706100f0320b2042c2d150f103402c007104211840c3c0401d500103441c51200401f03012410189204039440740c1803d14210341d150b10f034807030144018101e001083e440c030166030041d0162050000c0300030003103458104a107010080d100742039a080e440764800240c840518a414000c462103004068043c00b101e6180503013410305904001c0707050701180001d0090071818070042016107008001d07100301055526440b4141428551282c010f02d008201000401c40a1f980018000c41ca208a1201400d40340d0307203098565014001d2034110b401011800244c10200d587d008240c820a01d0089081e11070f04900c02c8420b00881e40e0000c02580460320500c0382c00e4a0749003a00d0004a06030041042c1d4010070039011400f01241c0c8507039004010101440980c1040c1941000603400c91418500100030964081002800d5120702e88568140c03010800d001010100d1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 45646101 1250 45644851 45644861
    0x80106051612020102120609010302030309010503150d24061a070606120506100b0705070504020304020f04090302030a03061e090903260109050f0609061003230a050702030c0304050d0303 82
    0x140102c0002c49503440100000d000c0d620544a90098990070030206489103404440f0604a0342c2c028000d5181c5070390400103554a80008000d503400000340c910b03481407902c0d056000a4918072460401c0040c0d2001a41c1c0100030b01c2c0c840508c0d441a141c00030500414400d04c1003007201d40040303002c26841c1c03811413031706d000501000d8011100324a480d541200421100045003405010544048189140c5404003032480e4000c01d00c0152090384801010000c0c0d04080e4021030300140050301e0303080344014034004902a65018801140142e0000840e142001c3d4580328440c050056400d0310242c0c1030600340c07075596018441c0540c049880d91914040d04250040c500e0044e070162a21a162a60012400c10b0348444001d20400c521217017090000b52902d002c420b20309104040c000d11240f401e0319080144446041000e040c03805041c0c1c0c070710740e03d15a4a000c14559104891620505525103444501041a103001601103029940107004502e1445008420346050311020313141d070000c06d1060300701240900 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 45647351 1250 45646101 45646103
    0x3020f030c030f0102180d0c0603051b0c07080c0a05010c1202011506020607031d03030f18070311040b01170708100b0301090b01020c0f0f0f060d02190e0109060801060516 75
    0x40f0900019510140041d00540400081909250705014625041c4211004450f100501c0c3c0846000207204243c0a503109a810111410446c00c540161814584450748098078151135075102000030071119404000a010b50703903040d106055110b1420001801c2c400159034010410010001c4060195100358085c0a0410750820b5520400d0b5a0720400f1b074441744240c0380c48000904081c002c415201048090859010b0803100031482c0d41e07541d5504092481e0054610b041c000c12524040c48070480422080340518001d00c1d0307600c0340d10002401c0004076609100c005060012200405440b6031054820903842901414049840c5d603c10103a21010840f0341c0040303020410100010610040941c00304441c0c2d002038003264204000e40c0c08009104083c048030580c8400c0c10100700c0d0250401d0104c3c80c40184001d0100c1e0708200100c040403040e0381100d20a1100d24403107c4114003241e50126039945101c100382800443c06040030300090504505019420131711a0014681e10340031904c0141400309 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 45648601 1250 45647351 45647353
    0x9163002030102040f0317030c0301290406120605042a05040503060c04151110020f0f160203060a0506030604060903020f060901050907240305060105040306110a030f1503020f030c03 80
    0x2441d1180200142c00e48540402e86030143c40100642042d414032080384e020309c4032070036900c1c01c44e8a07000d45040c1514048010413041505040c00d402c0c41001b84010300064102615851321080917141700e04221000f96100c0c500c100c0c140300305010401540003181c0700d5041e1241c900b4604011300f582c1514113114035801a90513106510400c175001c00198050310641d0410080181510b80d5082d0485a5661805600503260451082070140c8105035005241004c0c0e03c006040c24624680d9841d19903030004031000c074621061889074011440c05004466010460b031100708140c0c145403001c240d4440005100403c0d0640c0c9000d52800d15000f04040c10340300304070000301c5210f03240100605000e401c054901e16450b00c100310002c200002548288462104019550300308001c5001e0100c0207440701038252818004104804404291240180703004565070b41141c1d40d5500210700020b040b40c40044804a40c10701c0c0c849040e00c0c3c02440c1d400c820480b40c040b904c804694404400181c00c04c1c60026072a541 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 45649851 1250 45648601 45648607
    0x810030c08010c0f030b0102070612150f1e031104050406060302100e1e060f1305030a05010b09060a0320040608030c0703020307060203030c0d02130b1209163002030102 74
    0x3640da015041020f10380328a545000343c124204800350251500304086a025800804007880384078030510a4180c402c00828012500003082c10a080b096055038116461082c2001001d001d00d0351403140c83c84130482030f2a850b400715451a2122801d1140d502c00c41e0388260703190702c0440c090000380e40010b4040c40d0010612070040250010162100b005451424050106501065540914000720001322680500881d182040581030700304130390301c100f044641400004d240400c9948081000040d050310490000a100c0c1071481005202c40c0f0042070107100c0d00c5200400d000190440d2901c6100c0c0c0d0101d00401c05500c401000140500026000600d00d4480401c1402e41d0140010301203003200d0007503003500c2d00162a10b100301d8403840704a80a54040c2401c0000e42041c025035401031000134000401120926100c91440c00b0170782c0004415800400040240040c0d8401800302c60241d0400e0728120f14198a01201c400c190041c7c05034003868030030382148508850350001500308a296004008540d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 45651101 1250 45649851 45649859
    0x4060302280906140d06020c0601030f0b010b090d02060c1515090a0603020d030503090a080f3606070201090306050408030405100903082212021b01030218010810030c 73
    0x41c018500401c1065035103100030700050200a074443c0300c0c1541c00d540800c90303e55884005124202028600c101c42d40d81d8200107001c65032000f442018040c6221f00c1e00c06a00c50b01c1b60400d20400c80041c0c000101e0380c1020002c00b104e690703030200c906540c0c5078191400e5480382040300b03d030b6007003190302074078050808980c0301040130303084403889520f070b82c001c04841106d455100c001d081d4045903010701009410420040502000c0b038000ea0203035a0040081080302d01d454a195160b0394650008501e0803160403010842d007000c145104200030035881e0041058400a4070740c1d140d03846524411031194040d1800045407010740e4844c1905401030f6422940920003800d1901e08060558412101907506001c0d940307100c5895030450081c0907007a5010368400c0c03207644032204404240e0b811035208444000004180e4800100035107407003684107905801810101c17983d5072205041c00400801181090320400800101503c4130038500d414210070f2802d0315040d43ca50f40032103124178068002615411040000007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 45652351 1250 45651101 45651139
    0x120302033109050f06060c030c0a05010b0a06080603060615090406080706020111130e06060702040f060806070903080d050a06030510151d070c05010b0d03030608070501021212040204060302 83
    0x2800402990044141c0c0e6a881e10741e0100c07a42900c02041102c445030101d40140b5010000d40302c4400881c0c1a03c1c603001021900318504a18401d080b0340340d945960700b92842c0d00d4203040d101d00509903410070100d640342281c00243c9401300180814845c00d0401c0410a10303081c60416510700c0d450180040200701c1c1c6a84a03107a03101c035036100700c10056080219201d1601c50100550304003030498110404514105842d000300d1520040c04903800060500c82c02c4003690740c601032524a04400003001801e581000201c0342442401002c3d030084c00300702c19080000a03070800498980044c1e5a1b00020310303440306103850340034040030340c00a8424850b480c4558041440c6912100c6042e844030000b50101b0303900c0c4090070030860800c05201c2c8095200300041d4840d401003607140d4001d407051000141c2c12988000080302c00d80d0070701c02a00042e699080601c2245820884403016040c05d0006164071040c204d61000d07144901e072400c46018220002243c1103448642040001c1c0d03500404403060424541801 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 45653601 1250 45652351 45652417
    0x52401030506150a03060b010302120c0c0d0905010203070b0604061d0f010f05010905040b2107050306180604020d030903061103220b06060a0905030102030c040501120501080712030203 81
    0x351107074007424021603441042c601030a0601c00018004401561650b140c0400505014810506141d020402c102d0b42c024520b00e0180b06104214601d522180400d100c24a06692480a00b080c04100e40c07080c04207a8001040c1c03111254008011030050fa00e04c80441c01801a0f039001d000495248800d447d6850001d445451203017a40c0851640260303031b078001001c80a0f155101c0c1c60301190001d101403000b8102900012141c007000750a480010700c9908500c40444e940030501e80d4160450300b0240114503051040c0c03504140300b6032041411842d00c0c0601500c800010388001c0c45813180901080c2058000c0d0103240041d6080402004600789075440e042e402e5104440d12034941491005a91b0007201040d40650050b41203444003035140e84a000380411a8404042d11090042d64030000515031b409000851050030f480e0300003a1101d00d080000340c0308103186100c010755a801c110045c03100000c00221001250107483c1d880103454140e003030682c114031901300400000c9003401c002c001e14000007404 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 45654851 1250 45653601 45653603
    0xa060201050609090109030c030f0221090a0603050402060417070e090102030a05070c20061e1201051804030f03090203010e0610060c05070e060a0e130b0c0304030e090405240103 78
    0x903d8503580e150410340c00c840401e503004000c12144207620021910820740c055050a1a004807682c0301d02e24100070030a044040c454002c2c281c03002946404ca4100f9814102c000c022070f080521041c00c065000500d00e004034041c0d072103001c0003401c16006101081107124001e0003280c00304010350422011a90203984100c8080d1207041c180001318030858498488041038a070030101441c0010880510b4039046000a1002a40b00300140440710355000e9200508009102100016607101005036000032503c8051340704034440c1c02c02c01031188030303002542200c50b44540d051a01100700018900c058004002c0040c1c080d40643ca002c0d40d1003a00c0200050180c0078811522407100c806586580454040b410b0800081c5940c1080804020300a455140a500301c44001d0158503510340794801021500002c440003001113482da107842d814048015400c680002c1c9009038149140340c01e89018200010740b401940c041c803c0d6000080600c001440752920410300105144600500741414084015003800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 45656101 1250 45654851 45654859
    0x303022506060b12070c0c0b0c030c0f0105010317090114030109050a0614100e060405120313091523060a03020c0f0307050d0804080c070609060f030506061b0307020a0602010506 78
    0x300228003000014213883c3d101c01424215a959656504102c074a00580d180464910070300900c007181080c50f1001500190f40e43d07a006544842c0c00820240c0ba2269514031016983d00d003c0040c004140110f0b080000b1213007035148680d07030b110000012a02480c42d04081004418003100120343c103d007640166000d034480c0324091001e20f07225200b401100c00c5800183e680825041c1e040310b00c00380100d02c4071010380d8000700030b5800c107aaa180800c0b82544140c1482c130710380c0c0000400c0c045084005036506c024000d1118100641c950443c1a103034010000e009020b02e46210f10f403507001c18805035190380c50740440078008035201c0c0f9860b20058080d410010004c40d507401001034410250100105880d549a0058000c1200f11003a410560318004040d0041d210300d002005050240e450400c00040208641d948070000c441c5418002858822100c140c5420913080ca01440390b10396950b015034815080c100030595800c40e6543c55079107075101e5200001e4000401e101c00240c0d00740c0641c00903214141c155 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 45657351 1250 45656101 45656111
    0x4050904030e121203060d0f0209070504051011100e010f06060206010602100b0a03020402030c0c0109050606130c02060a050612010906150f0b0a05090a03020409140106080102090307120303022506 86
    0x1d070040791900b40d102e001380302020042c00010f040b03260041e5940b2107940142241d072150101500807480000003181c94501040c400102080789041010b41491000150302c1c00410500c4896501c2d9100d051440148824a40354500444580400c2d031041d400c0045441e010425940c1d00e040194071901c09206060150080049201071120a030003904103101006180300e29003801c40e800c02000f908080c20803804040240035210700c0c4030091003a1240940030702e004000e94680f0300100700c1c200c044401c110820f80e0815111140164001503070320381004904102003000d0ba240b0010500c9000e264010440e29270801c08004c0034030040d03030302c405010448068503108540e290040c892006500c0d11852058003400c00c200d03104079100d9809442e200c0401469400e5095480d00024169071140000b40c91566481e0021860361509100d1500101501c0c4004d40c240810b100c0043c0e02d4560130311440c800480f018800408040c426412140d00c40c5070004d440d404401503050b809103c203001d40c01118120702d86 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 45658601 1250 45657351 45657379
    0x80f0106030501060902131206110c100b010c03050a030b010e0d060501080105010911040b0d020f0403080c06150a0b0c01020d0501150e0d0b04080705010617030a020106150203030c0f04050904030e 86
    0x29000b01e450007035803a20b10741c40d031234a40b102d00d146030080450140c0da025602c40f9005050301c40700b40240b03000e4040c80020030004a60760490070803241c4112429051019140c040d00000350000300b551002416400d001070300200740801611000360b41800250302c81c41e880007107000c00060380d00040c16180144001c00407a83c0302c5003614200ea1003980100b03078a110901c420840030300300c14002d08009000035000741c1408402c10510116030401e170803ca480d003001043c418a18842080140d522030740d5444150348854510001c101c600019000742c22060324001110012050700b501150308228105008100e03641e9244020052410b8040c44030340000d00d41b41c105140f074905504414003090300040340d40d046441310740c0e6400d0075503c410b0b8115410354071540c002a2569280030760034070350150360340596a00c10b0402402402c650491f00b0607000344101400c10100381e640001078943c800c8103942d03800d075102d04143c0103d10314003541c1e01065101c008041000109640151350041c00b1109403903102884840b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 45659851 1250 45658601 45658619
    0x30a0212130309290f0409150e06010c06021201140a0e040b0601030209010e13060521031602130608210a0206190e0a1a07020303040f03050a0306080f010603050106 72
    0xa040c4042c000034024007040c045408a2000712000d0045510f400d500881403400d4814160003610b800b00d0304040101d000c010702801800b400131899190810040c1d803d0800c04209001c2c40e001c2c3c03000381084484424201003107901e0741100e420303446080318040c196030f40e40750507001498484051402901640d600099105244524078081c690004545440d0359030440110006c1d0003021a41e810009805603008440e00e03891031307942c4034500c2c072580800c4c124201418010003c0b0444205c0141488101c191942c108000c400e80354141d49420800700310304400d000042c0b1040340c0888102c0000c0c90500c0c0060134400005452440e4040b186c0c000005603845100400f0074000c0c50340300405030b00041c002038243d41c2c010b111140c0d80480941c0000703560f240300c07184503d000c0400b4402c559603800c14624048682004035526405016407000b1480d43c58540d5415a620781c2c000340c01001e002012890b001d641d400382c1c10840142c4118021198410b21809229020f42120310051b10079506e841d1740400c2c107940c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 45661101 1250 45659851 45659881
    0x7020f01050a02030405010c0c1211030d0903020108011802041517130201020a1101050d020406110f06040c0e10211109090c010c0503091f0801090203040317060103090206030a0212 79
    0x196401840c05c1c00e00c5d200c015030741481e880e9403c4540504c07851700490002d4801502d908064054051304142035a4101450703e01007040c0f58180a0080842c000c02c0180e078007186031419100e580c0003040c910152802031802030700480c0c00a400100f00160103142c45030740300f059008501d12656106071652154080d607551802d50382006030068002c1c95004010542140301e01a03003060605d0118030744428407201c1da00b01e030001d8014400150303000c0c107090355821007040081ea01b20a001c010f81000e003000d40e1081420b5105e8440c030903e04904030005810361038200482d200030b00541011500c20300c441900c40d00b246201207030803200320040d040d02800a0400e8013903148907044400060500b9210080151071018417940129018801000400d8264a520740340840c0400b0036155092020007a160245c20302e00e0580160220610600030070000c40d5002c602007070511341651000840792900c10040300540035900e00690000000010310060000aa00800240482d05041000780c0c07240300320310364085 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 45662351 1250 45661101 45661117
    0x4061407080f0705071a0d020c0a15090201090b0a0801061d1003140f060102030f0d0f1401050102101e23040813050901080a080328023c0a031e0207020f0105 69
    0x700600042207c2c1000b0f900804d05a0000421a2050201c640c0c40c58400d40010f0130034400961501313603d03c00c40d40c000a0900c0500500c425007030510b81c096000802c640d00522900c1c0c104025401c1d8590100682400f41080000103020038101c00e143c01c03400340251491101d0080501183c500140c01d890540000900510059000d14030306000c103144641c25400848102ca061135495440c0303c05a02248100c0d4004030f005410008150316080000e4280240c2c003c4450049042c00e41407005000042160003222803084ad001580d2081c20780294910007064004101c0000c48100707010078020030345c0141442100307038803030500c03001c1e02c840500c040080288240120b0354401180d42c0e0000d880c0d4405907510802065243c02c0080d001842c084002c5c03a0200920000e0b42d00283c0c04c2d160312544111443c8071a2044859610384030540742500400d032100c1d084885407070021032440c41c150700c031b0b402c0101ca04441c40d411202128512009400a501000089114003003401505d041d95006005507a406 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 45663601 1250 45662351 45662399
    0x1170c0306010e060a090509060618010608010e1003140105010f0f0e06040e01020c0604080a0f1d01030504031101060b28050304080a020a080d090c050f030304061407080f070507 78
    0x3a481c0c100318283c0c80501800056003c0034910f000300d600b000c41c0c070410348112a8080106100c0c1014818409130389180030707496022815200045c0081600116000c0c1107401d44690030509954400a0820038a40d503000100006101035060311a4030054100c0c0b03050f6414441d0040c249560b49a91000d110b2a031f01c00da05e0b10a04940018003a450240d0000d400240c01030005450f11341c12940c541d0418404031803c0303564210215000900c194000d8034070420100c941845035031005900e0098802010f40d104507810582c80c0c0c2e000030101845400c212880d5143c4800030701c150750b02c5418200700f41d0088401042c80c1003041a00a03055403c1240498004d20036480b803920b9902c46803100807140e44039031100015481000da10900069854006003052404c000001401390b009103401004040c50b503000e94441e641c1d4020a0007c0d41d80031040f02c003220080d041c40035080c50401e20400032030058910181004101003240b44181c009503000b020b4161084040d130b01241d4131036200561081450000c1c01c16 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 45664851 1250 45663601 45663613
    0xf0f070609050607050a021009061b15020306030c04060b0a1107260c0a06110c0a180b0a0f0909030801081c080403030207020d05010b130207020306040308040212010e0601170c03 78
    0x41400c004004000b0710b401041031b03030284411600401c1841d4452481000024004081040216804840c10002c20803d0000341c4420200d40c40c0c100e00d003401624800c1e00d069000004c20040c0d07508000c80b165011000d4000c1c0441c554414409609400003080700c400b04003c0c00900803401000f26400c0243e94801c103d0b55041400d4401342e481c502481c08181d4614807800a0f05141580c48903109170082646a69402035030610520046c02e142070405084c0c0903018a1a0a22000507603072aa20f1240d40c42e03800000741208400005001f681341640030400310200220003291889180d0040344110380a510f508665981c0c5585940c0d585800001c5445448070001d140701c4014071452489230410701a01d8094242a52900050300c15a1f01d2102118144c0d035403800304140e810801c01160743c24840340d404604091b2141c020a444000042009040064110010f011503494160540784042d00c8002040302003c50300703043eaa903000038021201258814007005911200024154282c3d030004ac002e001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 45666101 1250 45664851 45664859
    0x30f02030103050d0e060706050901051b07020a06030b0303040302060711010f1412040303060509190605100c060203040f05030d020a090b0307121a03030c060f07050c060705030c070606080f0f070609 87
    0x40c070145d038078540ca82d0040d0100500d0000c00c817039000300b6018460406c0005202d00301400100b00c80c041d0001100c00421051100d1b20240c0c1d111011141250b40310b080110721860040002401d520071500b00175840032001c25220140141500c0341e8140c0f41d03083e01e81041088000b50191042300c11180d07091600e8004004041e44003040803521600a840707420049612a00c2c0c00016104440c1240c0a1030480707480e0b454031044043d540508070080005442da40c07031419285800904070148984090038260300040460100450403003092115038101045e42d80f555440320b40c4002a50008038800c001440d8000041042c61a1b002203c0c0100502c1d11100f4000301282e8005020301402c0b41c12000c08212890b80d100c0c41d8030f042c401405909a148040c0405242122078800c01d044041c1040003004414000401e4500c40011880d400a0007810503984036501c0710140c1d0403921030714000820050074240e0024608000241040050781c04005942c8031844031006140d884a03d031281d40e00081000030100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 45667351 1250 45666101 45666107
    0xf04060e062a0d14070305160609030c061112060f0d020303041503060e040809010804110d0b0403080603060f070e060d0203010e16030605030a020f010c1202010507030f02030103050d 80
    0x280c41203901070502424001c0c5140458109121a0302ca00b0752071110128507500550b0500011003c04560308103440d007a00c05010040160164400040900c80005840c9a210401d80c400017150303540283c0a000d4800b45140060075900060300840740d460802550344951007441080e0f0300c6140d66240d240c80320b591140100200358080001c80b6030401c0f50b00c840e00026071800d10080018002d52400300080c0e0441c00ca000303007122501c0d403103000200b801c281800700203031201040310083c074424a03006a140c0c580d810145070080c1e03200100d036801204007600303c080141e540c04182c4110b000f40c54180c5d1650781c1c041410384406003101c500c54100a124002003043c1d00401d00740f171050002808040c180310005c40c050049900a80010011040400c00c001c6008411541094805d20904c0c1c10321440f4900404241d0707a484000b002442650100c00fa445242d10483d140c04045800c01c081080002c0011000390003072200340c03100000241840700c0003040ca01607000b1241260380c030070010b12130742e14140021 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 45668601 1250 45667351 45667367
    0x7030804030302090607020405040b0702190803010312090803071214031306020f0d0e0109061d0318040b041503060c03090807060209010201150312080106030903020c04050c0415080609010b0f0406 86
    0x20740d02c56170510441c00907860700e01c1007510035441103066000d542440e210103486e10044220b83c4c40c1002540c000c03040080c040b10b00b038030f044a6010050303804007041440d040e14031112035001406103110100c5d0349030902c46a0420948400803d4807808405c5030003040641640c40115925681903041c003405d080000c11a81c0203017001c0b248070480c40e0a02114044080aa402180c2445810ba446140303100500c8031510580c06186260031804015007201d1021170348a00500120610030b154130080201143c8a07504901e2985000500c00c000c800700c1c1e000801c00340c079110701003921503500d00b1107200011806032044040c0650040f0425080c0021555043c002c1e52004174250f045540390860b04048680c0038004401440c49450304901e1403941143c014418101648a68205800d1242c2400440d40200304a240d07107500340c802107041c0d6100b00200c2c10a108561021410350040007070080b40c2c95020700e0380c6006013002c403200323442a60b076813501610314041e081507001800410001046464010211 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 45669851 1250 45668601 45668617
    0x1009060b0315190b1204061401030201020a030c060b100c0c05010801050303090f0612091b01051303060c02070e0907140d030f0c0c09021204030806121f0f060f170307030804030302 79
    0x14241c00c2031388607a40c1d140f80b03402030008410f09940560502c001c0041c0d034001c92417030f000c00d1814003900303624540000b582c0d5100303c08081d003840800c100e000b060002540002c190360802810420b188882000001d05c0c5040c2e044007039854408141c0e0200c0c096208102c2c1c3c07412100028019420b20b40000108010303568118803180d0710031402c0140d01c5103c0e1804222a00c250404009002075011000d2401010040d030200a17042010130040d0400311350700c0c07010760000d0342c0d04035100240c814181441030380740c00413030f400c000380f040c4442040220509000801d5070545400000480c2e03041c444070140043c4080e4514001e000c1506119070040c00351290614020f0180683c00a984031340d50f07000d0603405c90b407060300601c1000800c1820007080c141c00994260700310200340d0700d6240310460342e0726590b02e410790b8501c0480103000c6038440b0101040543c1100e00d00c0c0c5140700e400c0115070340d2242041d072403c80c07030302c95403409400c9414003451a541c08011384103400e40640324110a41e58580e0300702c00a60000d14 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 45671101 1250 45669851 45669889
    0x1050a050d140702030c060106090f0312030e060a02031b07050307080c190602070c051804021e090a05100503120906070305191211070819020304030b1009060b0315 72
    0x350380103842c100d8446541c0180110f070040d540ea5a0040d10160070090b0580040d000c1c0510001d003046034080700001001101d41101d4100101c40031408114083d03c100003050905200ea48144010502a6401107011705503111030b9501019a0b641c03103980c20301804d20701800a030010f101c3c0c00b0100e140080240f080140d1641694a040349003400406440d600340820740d02d150f804102d420402621540d841c0c003034041102c40c0030050b10034043c003600400008200a010380b4102181d05014458043d00d100c1e155001011410369161840182c1300500702215080220304400300005840c0c1404100c040e0709100e10380aa9281c24180070510880d0340c4003000c12800c01200300100402544001e100c45400c1407503944442c40280010403040907034a00717030340081c00140c0070003440c1300144440044480d151f040410f1602050300c00c030001d031f0850145a00203040c01d181038040040c9019001680026030710000740401901b40c8030108148280421100b5101da12104e007408281c5143c4400341c20300b5062241 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 45672351 1250 45671101 45671111
    0x5040f0605032d030d020406030506060405030d0e030c040603110a0e060604030f110d080306090702120403020d1a01080d0305090307030e010809070f06030b03010e010207081c09050d0f0215040201050a050d 90
    0x42007072540e41710088121040f98049414000507138180100750700807008542c420b01f46410800069103074150f1a00f110240303c84038410b28040e03101400f01d400c0f11440100300308121036032410090b407255280b00107540700f040089004a04546a40840c90040d0000342400303040070f0456552030004c58a20300180d45581041c0480704040c1e80300c011844645100b02c90b01e68507420400c082c8840004050004030542d0001144210072076000002d6804132601111010600748036800d00000f400007000c0f20020752061075001066003400080c9081c010b00e8035680800045c2e95041c88152a4014a040140041c400212000301c0f0343c4210003040e04145a1010b4459640da9007640c0c080141c0c45510000100e520b9001c6451149001e110740d40c80c080c000350083d4904a44c0b982e032441a0b214004046841440071490b001c050764043d88a010780e203a010048484001074004040c0114144551400040c854100ca01c1c070184080c5d59801d00641e81a1501e6003044a66a82612190085c04480c0c41d80d070399903 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 45673601 1250 45672351 45672433
    0x1b03080327061006030516020d030c0306150c031205060a1202030c09180c010c051c0207170c090a1401030809010507020a0e010e1e04020103020901030e01140105040f060503 76
    0x520009009403ea050b1041e6418034058004d01660310061400001d44030b10000d0b545500d4001c01d031045050740500d000554000a00f030158010321960300f0004440422480480d26180c000040b0084107000381c8501044040020f00013054403011502c46400000d00082000744072a400c294008091008040e81d45401d80c40740810609503045030100309049500240d404494018081d4103580b0000786000388003103001c1c0d11407580d9001145101114030f5006066803041310710a02c10701001d0682000100c102410a111090750362942d038240e140b280503601d01103400e9000500c2001c2c84522240d1a2101a070b10310707200d021058010344140c60510208001c2d40e80140d698400e460b01801e01080054400c3d410507003000d000c4100100819040700d120303140401190201920998400c3d424a4003581c1d9401da01d00403005482c000039072080325801e041250403107050140c54941a90401d40b41040350301c0e0091501ea054070b5452007001c0d01a080490400e0114110124801003541020980b60725a401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 45674851 1250 45673601 45673603
    0x2100b061204060504020a060c031710030b0403050c06010f0e1302060d0c02010501090c020106120f051203090a0203010c0201020a0c0206070804030f030804060605040606050906030901060b13031b03080327 90
    0x822a8203c442c681d03030304100021443e10b0910a00500304500d00010b08103c03079580034080021800754841b10035003070750001c1c0c01c140e188900c500107154088400368072401e0500e030180043c0c1202048208500540001092425080308400115260b20450880310f4842a004e110139010000080e0380000c0100074070301c0400c00c035000c4c101da052001d500024866140807841821941c45002200442e41443c004001e81d00040b40340c0c6042541064001c40d010600d482c02c54585003100400c40240a804000c2000a02d070100e011040e050003580280001c0c800d410040303080740b1420070921701044138500d2520144c20305070301030022030703109031132544c03809031240c841d1b01c1400081c2c1c00480000750746108103c2006194005c08004103400d45060020504040e400341c6140902213069000e1480440003070148002500498010842048002e50300c007044000855006000d000c103036240550612900a541c244500074011641c200340728509580700c1c4d0ba091307910700c6602845510301031314906045c410030300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 45676101 1250 45674851 45674887
    0x2100204060906030612081207030b040c0f0f0206010e0c0702040905010e061909080a0807120c020606030d021f0903020a060606091d130213060e0412020111070302100b06 75
    0x21615a45201842c243c00102540c0340d54002c20886054039449000081c020400d480c0750911401c8503140c40c3e56280f42c01c80040c841005d0140c2e0250034800300c00b01c070940004201604280507a0340d41d009104e444001d80e41c8039002e1040300e03a104154000540d40050043c040c0c090070b880184046025401500d03118250740284641400d150400c909001821580c0803658009a01c5964203100b007240d80d40f03400c01e840c05400c00c1401030001d00390008072007a210304c00510150602002c2042251b03101740b4003c0d5207000c21180c0500a124290390030503d40d000107204d00300c88444040c4000245101141d5102a105009084042d0300c61030414000250150107210b0103808103545002c00c2524048030401e4154039107184020007440442070183c2040c40c4074201c4082501903e003074042404100d01800104070300e900481c0c15816100c184010010280400030000d6030b990f000303104072000f07800d40210b0f5101d20100207015a00c400c9036500c181e9016000303030b030300490002d002c0390520400300c4422402d05 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 45677351 1250 45676101 45676109
    0x303030c091224100e040506061c050712081209060a060f030f020906031c0e1e0d12020309040501030305070b0a0506060f090607080a080103050606030c09010605090102100204 77
    0x2040105004603907060100d1040402a00b84005040114182594805030840031021004404120000608910444101034001c042c5504140060720b07143c101540c4030101521018480c01128414880c1080380303460100c0f41503000000380c00711300c2c980ae2121030f001400c90700032211030100380444115101450502c6101c0c641400143c0341a2602c01807203001c031000c0390441000f0248003541030022541803d20420345980c142c4041500351501c80000380342c10140f6020f1014031802d603051090444c0e00030448005c1a000b681e8070001c0c041e11696410f003a010054500c2d4021900c4010140070403048107420618076000d0040c1d91801180308041010741b1003d80065010139000101d05040140d18a51141c0c00741c0400410402070401c032b00010030901c20302010744c1c0c0300300d80401c00c80300e03981d00c210845a603c0c0d40699241e075100b4042002410b42c0030b091000342d60034000c040001d400c40c00e01082011254100909010682c6e0070304a06903942d404c59269281144102280540c0b05134642c8010b01c0a4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 45678601 1250 45677351 45677371
    0x5010302160807051b1e04020a021018020a050d030519050927100f0b09010908010906060f0803070302151e01080105090d0203040302030c10050f130306060b070209070f020c030303 79
    0x5031703144007501c0003e040800b182d0044c0e00b5155240c02c44540b5641241d070740801103901603516034079064128500800c010300a10315520b084000e5102c44021500d6901c00391098683c1000d0f0307507032a401c00c81c003000d0346d1784040d01185080098458201703500004207404d2880d400c20f6410315103110041105d100343d942020b040b91005020600c4200740c0c0b1791110b40d000c03040010b0b1a15030b1341040340503144d030000b03441508910303200800c40c4203690b8003030340c0c3e85009481880020030006020341028005408584502e085548189a01007400c00c1701000f201c8100b83c0640003804283d442d214100c0f82ca080003000b8000240e40c440c451038514458000e964000c0000c0b9001041e00c2c10000c000c04e06164107980c0301c500795801000100010303140403549184600e0200c0c0c00304080e008424083e00c0e00c4c0315203003840300a010000b03141d50f541d84051100c801528054070040141644641841071907110b68180654010044c030002040107110301511140c441107031050321000c41004020900d03540094424800f5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 45679851 1250 45678601 45678613
    0x2060f0a030b01110d020c01120917040302010f0203040f0b0f3127110c0d050403170319050a0b03010e07150c08040608070c0c0801051515040501030216080705 70
    0x2c1d075a407001d410075010010b000034126400510f800a907444000036151418044090064265840540d001c402d00d20381142071291460110341103030545900900040380031030320b1250741090181c030000558042c1d500d0000d040030002c3c1480307035606040e00488019180c0b0301c0e0801031107010308441291842e01440b1100c128600e2400f802001505503041c0e04549400d034449007400302829900e402c40c0181071f010150000e64002c901c01407003c28403401400d200a0b105182c9603a800583c00380080040b01e01409046000c003c410890f00240d210544403003403452100807103002180e040303a1201740c2003c2a094001184540d030804a400c1d18184500c01c072071500051010071440c1ca038a00c08800c00750075450b00c015501d0b03a9031f696106038002c0d405004100240c62f40041e07206800b8070b131400c4115400c002a090026910f40c8620b01900c41183d0b4044104884031400d04607041040c00100041030301d210240c10141400c0c01180207400442d450f500e0515200700000104903001d0041003124025405004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 45681101 1250 45679851 45679871
    0x30402010e12030405120f0a0503030108010e010b010c080901110106090b0a080604050616230c010b03010605031b0102190605010518040206040909150c020309010207090e061302060f0a03 82
    0xc0c030a121500340b4003a2070110441401000c000c01220282d80003241d5003084080400e0310240ba0681c2010000700c5481004c11520500c180040030750b040720320400017405441940e0400c0b900340c0d42c00c1c0750000c0c0810001040d003c0010074020180c02c0e814418903062406410100e6401c0c00d41d6803a5000380c00d0b895454640c2c0304107042058400002e011000e00038045410140d860700e64551004001c01c0100040391020304200e80b003450783c401c000c0c801d80848101241c140e1034038000e95002410001e9250320f000804480c6040c18050300b8204c40c5d008000d000d010260945004190306103014003411402002002c01152100c071410b035505074015000000c081d810002403001070b040002d0003407200c01c0c10381e007000010707034450040b030707082d030748039181c04500c00101d03141c0410341c4c054055034020440c0c141043d2146c201c1d4000050700b81c44100f6800c80c1e005958800c0e0300c074111000700301d061f407035500710b0000a840e05402c040c1484030b03107101034011460003050b0b040300901c0c0c2c3c00803c42800066101d01f1601c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 45682351 1250 45681101 45681107
    0x1050102010b0a0e040305090d0b090d0e030a0302070e09010f090606080d230d060503030a121a0109300303050703050f01051c15020705010509070608011d19020f03040201 75
    0x142e2050103a4060707003c2800c0c012100c4203258002d00003410808001812250794440445c540c1035150b100210082c1c03400c0404000752500206c0e5580400901a800c1c06141880d000680c10903080d0180c028100c0c00c0c0c2030150070260b092000f0320740c02c8290b4031078071440f8000c032840c0b240c025802d005200010b01c60b400c054446007080c00302d00e02d410030003454050440170307a403149000a4211812500d4683e9800e2200301140150034980d120a0f4035000210b450b040103030b000000c0340d83c41c49018400308980c803064202038101c43c4665a401c0d0008406c1d07070041c40840b903400e800c0300003140d1180c41715803590208101d42c0c42c581c0c20701400b2400a921902070000541c0c240c024650084e090302e600300d44544c14200810201d00d8154003083c1c0061400e03800d441841401d826070f42074090031030000d40d9150300314107100303020300402da42442ca02e10500341e0024005205546c1d441c165408000080086200e00e200890780200c0503107004002d031201224155038903007038401003c0c0d030195200415141c1c6401d00002d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 45683457 1106 45682351 45682361
    0x51309050c09040308041208070c060b0409020303040f14030109200411040909020f0d02010c020d080d050415152103050c0a060504050d030212130212150105010201 72
    0x2003c10b040e40842c0381803259018004e021340380e0800c081d080310303603400032a030f00341c00038464505600010b8015000201c505800410101e108070f81a000682554840e42c000c0d4001c81e02c100b030400801d85a02500c1c02c1080e0214002c00c500602501c594080c02c1c83d800b10480c20408120b0010b049549a91200900803c140c201ca40c40302d80750481c650090410460591250114100c1c0015600d40100c9860f41158103035608034a810055083c032001c2c841e140000c582202007401840507010356449400d01c154000da8888074103055004d0b40b08100d401045039200c01c0000c0301810710003000b002d210f030100f080850210609149090030100c0e0180142c450b104864000c1d6030b0300c20300b88151a003005014500400545004046c40701c0154100d2142c1c0b040e040e0b1016401c0005005510103820302500c0f64005000b06003200751010500e400d0000301d040500c41c1c6890f80005122a503424403032 = true := by decide +kernel

theorem cover : BRFrame.Cov 45503601 45683457 := by
  have h0 := BRFrame.cov_init 45503601
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45503601 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 45503601 ≤ n) (h2 : n < 45683457) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
