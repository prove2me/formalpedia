-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5286
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:22:06.744772+00:00
-- url     : https://prove2.me/submissions/4911ebe4-3ea9-4c41-ab42-68db06877b70

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 950539568 ≤ n < 950719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 950540818 1250 950539568 950539631
    0xf08031909060e0112150b0702090609040b0f190207110109051516082b0c08040b07231818061005070510140423032505010e01 56
    0x41c0302940d04500044031011085c6061190300f01603801301001440c0c0c21550f81c0c48900c1c4100005610820f0b80001c0c0b8440340300b51010308040e2181800e000c800c0e001550010000d00c40d0300001810540c404081652000308882111908821204041c0490f4042c1d4416102c0030000000c01c0c4441d600036000800512003601d42607074120075844640881d0250140403803411420300000b20511202406813011032a882881400003481c012951180480e0400780042150506007541d1226000d0105540f1454100c0c104c240c1c60f40d1021021030f040303a070311665110800b01c81311940c1c05102c0940d01070212001040c15000003e604c9600300500c0704420624001450b10000812001b911201001a0403131b4490400d2034440c1914500a402d041e03080001c610001d1601c04035010b1869813080250055010310b08030340003442c0d00c84040300044142c003000c1000e40d00821518000000318924107440703101c4444040c9501c4240c0c0d840b203080d0f4400303405a40c0207a440790014001078000700b2104000c2c20b41d1080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 950542068 1250 950540818 950540837
    0x4230705010f0e030f030d0603050d1103030a1d07081b1207050d0c090212041712010323010203100609050109030f06050a020d1805010b0402071e0c0f080319 69
    0x2045024150800b1080001515060216840401200761114640c02c1542c1e103446904c100e010041c841b610003581c0354400c04420a8600303001e00711005800c221117000c0c500e9a901c080b2503001804103030b072804a408101c1113500340000018414480a051400c0c0600124490b03011030070034228183d00e20f0ba00c52076594250045640e00015210700f102c8084d0341c00c0d00000e281e410100c540c5100e5902c41b01800b400001c040a030380d41c1020255114a10850200110a142454202c0c4c2d0313000d01d408a50307d4490640060000c01c540241d05030503400250a51f82002000007422401d86e04240c0b050b90051281d60317802e20080c4c0d04800294060f180a2030500c0e0101d207582c03140540400c020700090f1259580708081400c45407207804481103155209000d1252040e2141e00c030001c1c2850003420364042d441c00040196a240900031201001d811a00b001d2901c800b8100c1e9000300558140101c0b00140d01100004400c00f0b0104100014400e0f03002854880009886220300f528840b50305c0c80030044101c1c1c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 950543318 1250 950542068 950542079
    0xa11060a0e1005090102040b13060305151815100914010806060d05090c062b0209030d031d0610060806270a1d01090303140403020a0b0a0b09042307 65
    0x15108040d000e03081001c1044e03240e6141da10b00a103c0c03904205202000050a145424096001d100840d50992303000c00255440c40407100312101a41c3c0496030080e6032216006587d0241d07500d043d00174502201d00034440b101c80001403040f40c080c00140012440f020320800c110b45a0b50005194050282002c1c00b0354604000001d08920641580c4151035503502d01103154240100712003903621754040c2019556401d030b141018542000012044100407000580b000c010760036000fa5110f0381340c00f8005010818031150150080c01c803038245900307184400104000d1031001005868010707011000750040c07035400c103400100442c0000348401d0151a034030304041c1c441250034481800d01c4644140703204050303c030711048a010b0114003042c00340851800c0341400b0250819444000014400c0d03c0070000340500c0b4940391180c010032500500580c001024850100702c040c60b03c19405001c045000501d02100400120b080c94251800c1d10010343d68604a0403404c214000711078619441402022242c2c60701 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 950544568 1250 950543318 950543323
    0x9130203030a11070e01030c081603030519140412170f0405041e0504030f09091e05070c0506090307140f0c01050f1c0f1b0f0e1201020a11060a0e 64
    0x482c500401400b4103680109040078006800940200c01402880756507a091010070342c404d80c00791040c14000d961341154405c010300a003400700c03a8540c9078181010492001c2c1c12424100c080d50b4010b008032010482802c04540000b44090001554041c081d901d1038144444104959540340a4041d0100201200008c00030141c03000c0322412a00407a80e4410a14a0200c8400b4040c1c1030048a00b00002e00c400c05811003240e22124003160364281a15070381e400700000340c802e100006a98102c00114255070b2079840c1c1c1141c1e40c04040c601700f030b80c030300030403603440c10f1030050111007054090b00007140c440d080041495804212400400052004180c140d81032919035030724104181c1480380009541011000c40d4040d00e1880c000d0501300c00b0400c8551703107548060041042e0710740b9890310344002e07080403044910000600045561b1020036807410040152012070910000c66442020241c11126952090009000310308040c1d8500b0707805003005885c0d614144014000c1815542044864550031100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 950545818 1250 950544568 950544577
    0xf0603120c0c260604050604061a0d3e0a06030204080607080612160510030c120213090204060509090a020a051e07050d090f0f1203050903011407030b0913020303 71
    0x718210740032120305031601004400148030f651201c5001c0e0034200024000080341c064800d90007500f0512070a0b2604982e00c844021040445034020030004190022031040041d00700301480c01212001502d81000d1000f17410034044031308011807403030601071154a0522908200c014452810150f007880d003000d000b01d0301c508000f881941001524400580301d9501c860110201518007400c0d0307420f0700001c070280f0b00c90702d281e405171a000310042d9003018080c41c402c1c810134040300d0159039881035802c03800c400e4201039807010034005803003000300d1404a201a230b0342c402080140580e490381590742d1400e005000103010000c1556042e18414000c0c40109500001181c2c0d4140d40c1c0c800400c01d800203110060124014510003508610609041610b6150000040c2d8252020b40d10f500c1406c1380c0d103040c0c407800e250381c071702401c0c2504140b01003100010740110007608000038003c5c00400c0740c00da510b10f5815060800c540b0000000d490b0b0340c0b008820f04240340415008200400026034002c06500825500d00c036 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 950547068 1250 950545818 950545829
    0x60b040302130b01020114010b040f12111908120d0506120303010b09060c03040803040617070f050307170a060501121a09090a0602030403210911060310090f0603120c0c 74
    0x40f10740800c5035a038801c1d0722441140759200c00307800d960b507140d0841079403d8005d4055051924003201021070f400004044042c841d650080b6482c0c41c0100003028008000b0420320f8600a94190f0080414044014080f4100040d00d1451890310360100038500400d40d6070140c8854000d60a00e2000e605103078012089a054408806129540302415800f04d8224414001801c913a800301190100d822500172000b80102c940303c0e900c0b20503d0003250301408080c54181c9083c404901c9218040341400e0184010350ba01000301c0c181080d00100a0b044040384c0390741250540080f03a46c5000034003096030010045620b6455024040010700070013840684646038094145124603016000918103040820410115542c024030954607802d2500e0050128002d070422201c04151810489030b80303842e24485c0300c8a1035000f040c0ca81d00241d0440501110307600c0036140c05220561203038080b8440b0303900e0007100100c3d0900c5400040d02480c0d82481c1c43ca108141e41c0303483c1008010740c114000304030070700100c03000d90f003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 950548318 1250 950547068 950547071
    0xf1002071e120e011b0506061018060e040207050a0605092a0d0f0203030403060b0a1715042102030306030d210e0703020a17120c0d03090620040306060b04030213 71
    0xf00004010f851049600d43c035070500d4213040d401c1c0f0003007100210300e0354054403081d107000000c420004415501c2034061581c4045604082d41c0420402c2d01c90381c0b84642440c07001d00b006182010701d80754942080880303031050320b20036299028051406420080c0007400110ba801c0e00d07c8094006130100900c0c0c80b0410014452214000b01c14241700000c11050fa1850740241101d0791541c1c0c138038011024060250103140300b0f2a0340c00d000294244c1940d41ca80b05900d00c000641110300e40340601d000c080f0000307030080d18400500d038400001c49525000d074552001148e002903850746401c4003014545101030b80d541003004221440c1e410b4120003920b042028600b50b507804184c14520a000c50b1030000e050740042d41c80b2151150001e41c4110350f105614683d1035090680b5211040d40806420318402c0e0030003111076912009a200c00144268481d00d03180d071081002003044e05141a51010480ca8510310a15480300080d0030400c004c4948078040052005903056802c1c41d10b5030300015003111030b0070621070704503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 950549568 1250 950548318 950548337
    0x2071a09060a1112120621010e031e04030c0509090109061d0c0301270f050109060203090f010b09041515060f0e0f130e0f1002071e12 59
    0x9041000580300010000340841e80c9409040720300070b1010481060300049030203641c42005924503040121580d1424200503101245c54444c1440b240c512400c1d401883d030403441c4007005000b2001c0c02a55403800d0001c0055480d00c50f4011581540d01503102c2410460008101c01c0000540b040000320449030110740290a0703940c1c54000c603025040031030000f400d42d441d09803001450be0710841d918281c0745001040b954a24520400d26089990100b000100004034000d1a24801003040c5000d80c0c40b840340000310015400c2c1d80c0d60900f52000c0301d2049910711b801000700048420100102d01c40101c1c400001e0000343d1240300400c110380c0000c0c1000d40303168060b40b084801c0c0191500038119901c1c0c2d41412a40340340e42c55500801050850140d00000b80d80211440340d04c2c5070003100c20710400f00c01400740031107100a1030b1800003400300000c000c0142c015a801c82080c181d060013840c022611021004d680d511041c40d0480c52900680800c031034403c20040011301003140314103004804c03c000c1c142241007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 950550818 1250 950549568 950549609
    0x40c0813120215040b182a0a080f0318180a0b04020909100f06090b16050a050703080c0705090705191e020f0607050903031804060902030103080a110c010207 69
    0x14241c08075501010f011164090004000e04060034900ca40121070a5207080c410030326885456001c2c94000b03455104111905c1c040e50008030881c0218140e0081c46604c0955803440414200b2840c4075011a05410100c3c8640c4114141076416446080485000c56070807941f041c250200c00001d040303c0c1095560b00d4071400180c0b5140c1c12210b4040004040030510315100d0311a0b401b044082c0141803250049401c005091030240340c1410599406018446c2098100c904a1601e40041441540ca521070380c051440031807001c2c0240300145014121483d035440901c2846403810000303511444c0107640d80350800051a51040c191045911a182d01019510017040e046800804180c0302c0c1e104014842d455914454000500300400a60385050b00c8465070781c40c5060300e8a0140b10050742d0180c00c00c210300480c801c100e00440381c0c4608024000140c054980740020120b0301b00342c1045840301c8000941c040d030590040019401440c000006205c0c0030710010000351200320038800c0b10084010080b680d280c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 950552068 1250 950550818 950550823
    0xc2e031407260f062107271d070519050103090203070f090c02100603020f010f170a020702030f0105060609040911060a030c090e0c030f2a09040c08131202 68
    0x41a09002c80100081c280101c0048903000190f81452050007140f01c0c0b07840c0e82400c100e44c0d100048503403014101280c604940e991040351000d464000701e000100040303030034182a02c0362600403d408101201806940151540f0708042600014400d1040c5040580d10034075007003245003518800e103404103110b0b000d403020038078000b501d0300a004480708007100492a07a0035640040a203030469401c85a03002102c3e2901002c0318814040079400c000c00c4060404503501031054105022000d140c580c2c084049841c0342d19601d00f040c1d0300d000308540c0004622040d07240c20407400c6403120042008001c2405c040000407402e03c600304090340515143d51507070b8144420407149460a0b07a020300a5030707444210440043c02031110002c14000700304880000306200300f002004c244109540716100386540c0303600e02400302644004004a050311401e0440103072583d150b80701c0301e401040b46808151100e00030700c1000155201c40c2140c0e010044084104a54003102d80c044406413500000800c2ca40307014950100e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 950553318 1250 950552068 950552117
    0x14151309030302090f09131202030c0d020c10080603060610050c070906050405012903062701061b08040b071a0f010501020c04020a0203030402040e0c2e031407 70
    0x4a4600d0400180107064140c0c000341104c0d14103c8001511420900802005001c240c1d80c080321000d120a119001a00f020a290881c001c10700442e410486201c036503628000c04184400016000441c0213141410101d83d26150390300c01e400d0951a9140c4000801d54904000b488148142d8041407004075450241c2c00f11040c0020a0b4280e9481c00d40710a20107000d0a203d1090741d000d0703030cd8100009114042e10990b00c10b072240402c0080250b066070140d0300a1034001a14060348644041c0c0c0c4101c40d8940d024410140800c2001b11076134039858a200500503c2340e4464225010600da1008000241c00718211015507282100305c580358036460030921340c04101a00b0300c107205498007040c03220162800d1102c60480340309a0071104c119018200307120581c040c108032400507a0041c4046001440c19400018195003074034203c620352008480008e454210810803036402250707003403540d070004045080da040101c0302c1d070805004200e03108504a110540040040040100d00700c40e501108214501d00c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 950554568 1250 950553318 950553349
    0x141303050c032208150703050a02040b070605250509010c05010608010e031e040f05130905011a0906060310060f14040605041e0e1b120a0516031415 65
    0xba500ea28155644800c0b5140044112503128500f440000320f00f0000203c0c030034004c0a805019025440e03c540540280001401ca511590740038480072641200020150138028002ea134045500e0400060a00030350344101803083e900c400d200780c04504250000c0490342401c80038070344045440d1a13420007a00416454001d24625400c2c0200800c041000001401030307804070642d562840106120b5a000a104510420650200008007081039244c14031000011245c2c004001c14280700c16501e0908403905002510403803207403450b0060300381c1004011503500807070640c3c2c501d02c0c60600c4040d4420303140e180d1260004001080010050891003451211900403c688105440c1c03911500060016080b41c0200004150710f0442a01514150021101125009941e41c0800e450342e41c664038220441c0c8100b00340491080000ec0205c04800c0c0b90b452064070590400241418000c0c00014418110502c500405041403e244606410b030002c413a000340783c140d08142807440b54004500e08841d44070b1003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 950555818 1250 950554568 950554573
    0x801061b020d050a020306150108150102010e3711040509071205011a0618041112010b0a20060708070e091e070908150403050f030109060612141303050c 67
    0x540c208000003a02c215185d1084042e5400c580c0c2d200f0008c1110003081400310b001940d250041540c61858180c20456283c0602c00800d00b55409032085140282d903c01c82c2007101d146200301e03940c040003600850525107600c80c0c01015194251106045002d884603603a204990303c0001c10b1040d5410045140100342d00c00c144280c1d4003003030130a24005c1205401420300420a1084421140b8240040300d0503c04940301c08140b81048a05100040c44601d400001402c002c111900e0558040b0090740c2c024424130b0707086a5034140d5070744020034040d01c0003038210a1203030b00410003a0311400400d006910114501c0d102090b40d58210044525810f58844150070560380c1c02440346000740319200c982680d02400016a05444d184400c440104003441010420b800c81100d0064a404142605400600a18083c2e082100860010420394020303032103102c1f0f5903550041000741036041071580c0083c030322a030404c100070031004041c03403104031005140c0e10500790180480c000305401242680c41c0750a8200c00c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 950557068 1250 950555818 950555839
    0x3140c030606071e0303050114060d050702010b0402042303061902070305090d030f020f160603050c0903030a050717041412160f05010e06070302030906070f02040510060314070801061b02 82
    0x10007552400d148245c0c00242804000710340c0d01403410a100e2140c9004c0d2045240400360b420400c001c00b400740902c030455403910785c2600103642d1400540060404030107138104034014030f40240c0180c0c0b0300f200071170b01a8029404000c0e5030088101d598a400e500c0c7c00e00940e0341d004901d8119914414507418552144203010404141076200c0e0520302420a03e408407080c0c500900c0d00d5070364491080030a0a560b03100b003038050152521980007160800036400d099420079071420006400c40e004640440c4c00900f01165600c14031801102040d0701c0d18412403031174507150400701c844041d40c4074191030b20b000e1610302a80800703150040107046041e02624020000b50b0fa00c1e9a0f4648402155100b075600080b0340d440d02c1400c515007101100c0e10b90764503800462512510300c0038890751781c1200c5815181340e41c1d00161640507031100d001c0c2620443e00030103007030074607801d144014007111440b03481c1040c03205d03e40c01005021034001800381e041d602e0900f4011403000441d00c005144801101d4029000b01c400d45 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 950558318 1250 950557068 950557103
    0x131502030403120f062105150405030324101110060e011502030c07090b120106061707020312070e1302120402040b03061003030813080a0905040b0103140c03060607 72
    0x60b60074441e9410703210f080c04100707180d0b0344103401d407541802000081c9010110440025401c6546981c40354818002da40751103141c0701403003032a01c0088506551642001040106c4140c03d40346020340010001111810401c0070303000b183c900100660000305000110b544404092810400e4460f40210010103111068443c0380700d5820300e00130301c03c80000c1b05070b4007507110301140088140d500b0455040c005080e43c070b25080304030015084502d07440f500a070740c842442d0701e0300b182801504040c00507078941e0300d502d85c0d500e4500605007030024040d0301190030600000c51108606d8500c5508800310b031030002c050701090400a9000c1000c2e02c80b5096141c400430300d4220340090101c1e042e12590003110100a40c88d049424141c850b00c0840f0b0389001d00c2d0f0f4500301840024068803c907500449010341466041d201179039040043d80c844808a00070907103401007001a4602800b5222602500380307010f10840603158000b100c4405e01900312640c042c0c0210000e6081d40711902544d0065070030140b08400c04a452 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 950559568 1250 950558318 950558327
    0x51225020c01020d050a0e1c0b090d02120a021f0f0c0c020f04050631090302010b150f0f0c0a0804060f03050114100c060b031c03150e131502030403 65
    0x3041c86030140c050305420305a6640242c0a40d11014000e84810301100c01c00000c00c03010b01c1c00100d02541d601041210a0301140314026154407803241c400c0105814850154003a242c42800304d41d12140d00d00402c8120340c00b9502180030001030084551030b0714940380e52032280000d0070f54002900b0000b0314000b4100700d80e59001200d006514000d4500f00703440180103083c403083c0d9800f1164680c0000c3d541840d0344030fa501041c01c0c0040c181c00f401c0f001c040410005076080c2034500900e02030b00103030b4594242d4074a030b00e08001c174003614482880240f881c040f05403501c0d0768180651508146c4800000c1240d80100d14180074441d0207560200c0c040e07945540742c00014088210300d0310314100082c50100082a240c420341461403202100600405030024802d40464640c400c5500481e4015150840d052250700d0400900307800161500d400303440801340c1a4028100c400020117101ea4010a41040040002c070880481d00040307000c20214211055041c22110710445403484107031684004100010315034030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 950560818 1250 950559568 950559583
    0x904050a0b03030d14010e071b050c1e0102010c0206090607030e0f03040608090f031602060d0e010c0503090d2309010c080409020304030306080c0a091503080c0309040501120305122502 81
    0x1200041c0d43d81f01e42d185c11450000311508008141c1900c1b003118013880a00b44080791601c140c0071504100c5600012a83c81d204044101c406c007544007110100545c0c081c0038107000b0351803610062510707150940080d40d5503040546440103050b0b4891007040d81d40390900c0300301c024060032401c4079591541c41070010301d0305808540040c1030f4042e08500015100010040f030703880c103488408039013000003140c00f0003c0c02d9201a200c1a030f45a603404840c440b2076028019860802d10503203c0341d0b22850b01c0d108003800d0803e40c425400400440710030090070502840311800d40d4000c0c0100b80707a00c039010f00006881a8280c414080c100c804040f4000854001540003107100381c2c440d540c00d220955440c2451981d0303283d4414056800720190000f448107000d65404204040700a4a0ba40d450a80d29190035070103034803c900300f40c22500001444450740c1024058103004140c9034442c00c0c3c2405080d00d00038414081d0006850a402e07185000c1360409110340100c0c3c0d4002034040350400005000f041c0603507070303912 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 950562068 1250 950560818 950560841
    0x3100801051f08030a0c120504120f0303180b22051c02070e0405150619080102070c14010203071203060302040c18170c04090507090c090806011a0904050a0b03030d 72
    0x1842c080400e141c0c0c0040150782e44a600d68507240c05080341c3c0e82d6902811500c1000035404c001c0d06020000b8800c82c0502113a10050040f20461200203550800909236280218815100b0b102400c4900005604403c129802400410002c8541b140310050600c441c5055401620340c2c0306000d4080c018800701200b00c00c1c0010107400316052180c2d200c1e40301f040c3e10307021030340a0100d4000144c4003480007050520180e001500612442c6800b26041d196000f81003160050360190703502041c40d108200b0041c070500050b06188100000020310200000d40d64440d03464020145004811188076142c0a508100c01541e8024024046110090380080404401c1e02407014504e038a80400602070001070170742022400034001a110794400e003010b210250503550403c81d451311660400040c061010301c154608103c05550f507041013031800391354070300c0c000044e04506501c91910010680d51490141160402c013025200440e0f56550491440c0080c500e4081d455050300000640d0020b5401c0ca1b88161052503 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 950563318 1250 950562068 950562121
    0x71e0807050907090504091a01090606080a060b0301052205070c021c11100504230a060801050303092107090b1c0b1f1211041103100b0310080105 64
    0x665910070400c02000a90f50000441c10b07010040c05542041d4014880d024004c15000e000742081c186142c0c102d41c1e0980c01143c40c0b5a440c08140209544000855040701151000303102080c200602a8403a202c1031041c0e500c2541e0005c49098584207002c60704a0840100c0d40420040c60202800b4045155400049114192013138044204940784078031082065004001d040031840c0030018021800900000602840700c2071000203014000c0c83c86401225a02c00b2003841000a140280140d10416403c16002d201950f00103004a40b000401d0324840d1904554545147d1864003020500c0c0c1183c1303180306194054001c2c0890052016040555001c0c03068454501c40f481e01c4a100e507400b484104000c1001200101107640440c1269444014201e00344001d0f15243d0b0b00c840c02c01e0b48036065102141c4030001015032076510320300381c4500c041c1c01c0d16010031549140b0303000080d03076110324607400b81d15020701c00400410a0544126007000283c640200204800d0030640b80c0180c00c450031100150588 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 950564568 1250 950563318 950563333
    0x1090303020304112e0c02040203090f1c1418091e0a0b0d0b1e151e0d1202010608030f0304020306060105070b3108071403090a030204090203071e08 65
    0xa0429a01c101003000b01c80900000b000250000c0440c030175490408030040103403290300000542e42d6440191300841c0f082008000200d403c0c1442ca0034030401c080c1800c10b500404030380b80600d542001c081036800d00c5440031150b803a148191681f4011100000e02504140450100607000c1c0c0100c0003c038100600012203892a9600000441a07801c424401a008a1070803800c0d0000342050380d0b941d410049041c00074030700750701d4043d840b08001e00441c0e550000b010034030350b2510b6078241900c840c005a00758050306c4405c3c41050000c1001e0f0340a50030000d01a41c424003621040500c00c1d8000c030042c000310030903640e44803a41c107404501d54000740c0c0c0c180d219029140101c0c11940c000e6081f103003455481b9030800e100341e0351141b944c510501e442c0008103035240380209401c940ca403044882e000c114410142c003510380103181008c03042c2d0f40440c090010658000c1110f008036070383e1210301a0880380c0c1218085550401840402d0502640e81e00c84400841000401159204008440c4080d6100c6500b21000c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 950565818 1250 950564568 950564603
    0xb061f020307020120060f1509040209040b06040f020a020d090b0c0c09040f020d0f1104060e0a0f022229030a1d1006080d18170a0501090303020304 65
    0x1004412041015900400c1a900103500035013040300d40404100406282c911240c0004d828101e00b10b071221105604181000f40d014a0300080780351150f4246d0320b0b00c403207151a1303001c5100c501c0090805040704034441c0019a80c0d0743d8540100c070500c3c008080954485441d4038003e9a41d0f5100408007000c01e180c0c00c400f2502084c40c0040d19a0308608000911300e10b0404018002d02c0c9001400981d1000d000105810258940d01401d5009034400c1c1549100360b901410000c1c0310241003489144268242082000b103500364801c004c0e00102c1c500000a181d00308962a0380083c420041c4030b8500c20aa00e62580c90118120b04403411964a002c407003550300c02c1c4040501900d200001c01346440741060001c5015104690b11039070390020424098082c0500311117946280c000c00a054840c00d54031074405020910381404409884102c50030922825032500d0080c0c51560750600031030603214000300300000c002104020b400b44042c0c016008220071b496504004010b0351040794140d800310b2418844d54903 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 950567068 1250 950565818 950565859
    0x1061406072d0f0f020114120117030c070b0304031107080a0609061e0e010b01030b15162a0f14010e040f150312142b02070b06 56
    0x10503070204102c2062461904442c402c90000e002601107807054460110000342203003540702d9414001e80c2800411803040c40014220010113070245007a10b010701540e03a24001d00204141074031003941c80c904000c2c8204200340e1130360003690720740001403048900c00249070703079102e0065020324000ea81d46a003100340e0448840e50394407a84100c0080e81c1c030400c0140c001c40d8659110050b150300c22480031518158040c105900603030f000c03604120180c1e4444a1081c0000700f4800c6441002c4282414072a4609040003d008495443d004010300c2e040041d800640006000d000c3c1c50080e408400c10303200d403000c0404511003a040c441d81000000d101000881d645035007038542011510f41310008072410055600440d0351001c0441a550856100d900c0420300948a0046212002c0751300703902c00c20300f4a1410b003401c0310540348400405002c442d803140c0ba2440e40b00411200710f0003405042c000304c041b07000d1807480355402800c010410540f000c81c0300010441c51107500340c00741e40100c5118040d02d4168201e002d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 950568318 1250 950567068 950567077
    0x1103030310060f032d0b030c0a06180305031b101b030207060e07120501110909160509040c050d05060a360906020c0d0503010302090c030405010b1201061406 69
    0x140462601820400306210f160f4518420005140104000034002c00c02c0084800c13100026005030603802d080c0c62240301d5813040d8041100e0807030007008070614040100d00804158000c50082040c0359118070101c6030f0f864040b02c000e50340300c01242d540b4410309500c4800400d01d118603214602a614400708034054501031040054108084a400c810084506034001e520110040b900580c80c0c0306211084041445908010012981032a040300d02a10740b1a003181c80310700074404520418445c80c4159156408095400245602801d00c292030000040c2d46a0080d1a80294818240079182101d180d2220280c0810311200340c0c24402e98490804100080c0d099008008489817605ca50100315904072220000368010214450b25030203107100d40d601503a0380700303009844803500051034026541c0100403140a01e091843c10340e0855041d0b0340090020100640136003820f071004000704090003002c1d880f48025543c01400f882c9540110302c1030a01074025031085005100040e210141207040800448 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 950569568 1250 950568318 950568331
    0xd02031f060f030b0d0b10090606020114011502070e041a010608151009080a05060103050c0102030703090e100504150504051e0f1003050a0614070c2f0301020d02040311030303 77
    0x900340c02070110b40440c000c090000150380c0c400a00614100403c002c1e5690324010b04840c0c40d0041c1490801c0f07074550a5401c143c0c0f00d03504582c9403076410442404500c0101e81581d60341490201000d1400504074600742c89a040b8160b40c2004200b80420420340c0a00c1000390990600c818426a0740c0b03020946020800b21076101d4085081c01164150740b40c95049840d080100341000c00d1050f07204c41d251898119000000c86555110340e0051081c400204601103405800348021441d000e100c1e036000b42102c5051040c0b0690345000408240410300f02107001c2e001e0180900100018903c1c003841d11a111202e10130b2501131803070100417500181c2250703078503000e0000d0f25062901079150b8000e1888240c2008103504900b80403424084001803040c005580c10324047c110104141000c0d024680c1285000b8159006002005502400060035983c02e607906000c0c2c070051309034503a4602c0b9420140440942c02580c1355100084d02078880c01070f54094030969000708500142c20903040c007410391b03074401510710 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 950570818 1250 950569568 950569577
    0x14190614030c011419020a0203071a0a03020c0c2707080112020609031005130605060105071a1302101106012c1306020424020115060c020301020f0d02031f06 69
    0x40b20450350103070740012071560594498a00d801d810040034034602e80520300160042c0c0101c549882035140400c02100941800d100c2e0782041d420650103484940b05a11403141450b80128000c0710004060003007000240010300054030240406180d485644140008940804140c1003c110301c0d503c1030391114180c1b20180e54003104008543c080000a80229414a601d0310a24050f00c049003150b0081500920000b000d0100780ca0a46c41d1003002e88800a244604100382405508041340880b0481c05140c10a45080070081e114031180b010002c00c5c4407406500070502102103d41aa03000201c00301240c409000c1d540c181e40ca40c0c040c041215031000c2e040700c0180300c80125442442c00e07080b03d03540150004ca030345042000b4070307511801640c2040e8806041c02805240e40e480c01010440c201224149034402040500d00d84c10000598080314050300c010003804c10549000c64409504071603020710b20000072602c4074030401020010358801c5a0044000b5000040d4010f84a20300a040c0d040d40d949450f03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 950572068 1250 950570818 950570833
    0x32001020304061409040f05040506070c08030411040b090f07090b192604050a061a0109060305100513050601020c101209110910050f0d1a0405011419061403 69
    0x28101c0713400d42ca80b000442107070401c01420320941da5a10032048503a181c5a40881c2ca45441d00300b032424135000800e01c0c002e01c074005200c000058a4001169441580000c1d2641e40019800c0400c004040700041641c201045400307005a030303491b20741260f01c64806642c8094503142c5440c2d04179414028840e00301511600fa0355170008540c0600c00020005094401c018114120802c0d440588003059400303492603080904c105c4184103213409980061000a0031403002943d40c0b80000b401c40000d40b144804140d51540810b10300c0780090411402480d0061000d805541400d06c5072006180c11386420740540f090780405901e83c1031031445858843c01680340c682c0448420902c200207846207107400c4550181e185080440b56403100c104600440d018014107004130705040910920360303c8038411034411410294440c0005080307002c200341078150303060104815180c0b85000381c007400303203075400d160700406c000204555180b0300070701c8507040d0402000071301c601691002182d80356103610b0a0990950404503 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 950573318 1250 950572068 950572079
    0x102011802040f140a060306051b0d0b01110a050606190b270a0803090301060f1211060d05040f0c0b040b0d0507140406020c151602010f0e03070f032001020304 70
    0x1070103100340304a004808500700391113182d10b0b03948581c210f40112085503160300501c2840380500c10300d0b50200c59454410306070b40500300040f015014100020300c6076500d40710b200b20164481d41c8078103044041641103031001e81403403400c0d50310382d40102c9a590154160b800f480c0007107402c0901100840c2e90454180e403501d202d2105019500e01c04c0e032031a00c0803150803201550315444141c8603400900c500006141c0342ca080d54100b5095500c6a4464902e4180424051145400104400b0002c03544440464902000c01e000300d9190300400c14002c0300a4640000c200910003003d0748001094401d40308803403002e07100c11081d075081c041c5001c1d4404030101800041d500440c00c0d0300440d0014828184412405091108113101d81d10981005d80160010301c059030a609108041f5882c191800c4406410030f0000740e182401d000350082c0190400c14440c10750414103004482e4000000d401400342c9000c1611041200c0c0850510b120407100c2e035081d120064040131500348030441140059010314507152500e03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 950574568 1250 950573318 950573321
    0x2101050d020d06150e01060e030a02030d030c0c08070501050628051507050f0f070506210c0c06040f03081f050f04062103030b06070302060a0203180613020f010201180204 75
    0x20900b00e903035a0744c2d43c4803003141100d500c90f13100003400c034610010328641c10598000c1411001200c070342e020764025030f20f400059030045840c0c0b0000250f4600000d6035585010111602040c0440c041d001007000580f21080c080190009032007507800351815860b200b24014032542104100065404a1030014070030f22161500703141c8085900b10110f107250500c50603407107160500310800c43c2a10309610810240f20820340601030758006003811038405007060310b2404d0b00650318080d07800e50b1054060000001d00d480552205860785001282d00301d4540d07107441d19040e0207198001130154080303004e80c0001200c2d1900c040403d2840ac0c3c0c072060341c030030786840c1c4424040d49101c000040399100d51204004180d03c448520040c1076090701c5040c13440004c00c0307420007400f12800586118011302c02040303d000070070703000680030380c01c80036110005a4980c0c8680d5809100d600300b0003514501d001c1d803028441d1105d070100980c000b081c002c40f03500c80c0c106000b00c01a0300301e0b417800c5031241c0c50100c840091405031929 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 950575818 1250 950574568 950574589
    0xa0f0c11040506060d02030a0b0a0b09130c0521090c0a030f0204110c030c0109020909070b0406230c03090f0609030d120e0613030f1706191503022101050d02 69
    0x64041e85c200311a9000d0079050381c0046440003907041d60307481c008000340303400303d508002442500c514a1070300030701c00d011542c907800381511280030540320101080c1035849402265140c00310445120302c2072142000d861620001135035500341c14490080048140d1410b00c0c901c0301266480000c400140e1a15400d0001610461003c0301800030148040b00b05e4002c2807009006100480c0c00018840030148100807003070a028040a80310741c003400b4140700340c1d0305040864095401d541040301c880c0d0101c00d05007550441d50508a02d180e00042070340100310500002074403056004882a600c00d400002c00c3c01924010000c41c10b5159000d03800c5240b5035405015503202d800d421150101c2c00714441c0c080340d441c00200b520301c069000004240c807003d256011044c00c009031568502010400706aa5902d04c0186014014a02c40d500d450200080ba12001d507504004040c1e18907540d04103580140041e009422415000388161108010b400711000744000e4103050f5800141810b0a031040c1e07809208203001c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 950577068 1250 950575818 950575831
    0xf0b0d030f14040f210f021c0807140c01170a1a0405162706110a06050108060a060807030507030609140102070f02100e01020601150e150a0f0c110405 66
    0x541d540c0014484809001400600440f2a0280d0b19925009150030401c40880c001c030600c8035a485d89100251605000010441e0110741603409406400d03140008030280c18002031420400182e043c0403c1520100610410420016520f9040d4004015100004104a614a51001d5000081c9130601a9000726481d0358000705100c550141440441d085500645140804030350301140010100e0f400301a0412071111364000445800c04026510400e1846000c2d40b02840391072090107065007010043d1402d91a0080428803055030b495403200e85802e402e0360a10100c134200000424480740000c0c1c004220381e0300c000204101c40c0785490300801000c0c003e4080383e202c883c918a203074842c1000d00103401c40038010180810150743e10300c10018118801c554400c10700c4000d8042c100140c0e0081201070441d149081c01d0b40080505401c100d6000c441010b01c9544505600d040150500035a0701400507074149407a90310802102d11300684402d80214402403840f440010071014508007904030540000c2d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 950578318 1250 950577068 950577077
    0xa03110d171b071a0619142215290d110406091d010e06090c0c0a0302030d1409030331060905012927090a060f0b0d030f 53
    0x80950001d001d682e8050300c003c1d2481c1240346844840e0000215801c5d4000c04210b0301105e83c00b1071099512000001d9204880400c403121a110700d0a4a81c0a440c140c3c100600281c0701d03083d801440501e0003802090500c808039540040040740b4042410329048c1540c0040d821a0b169100e10032080900d0750100e401e00c42050b40320803103031000700400006003001e815075848450a0504040c0341142150110381100480d1101d0401040880041035040e078001c0070941350850a503880da18854000e10524a03480c1607403140c10942014941d011025100503007035003c041c04500312400d114403103540c003629500b48030381040000c909a20010b41c0055160180402d660441103030803040c01c0c80c101052101a15190340302e44107031040250a100c0e98948056000d1194810780c3d00796603545c0c0703e820b4484110300490089001d009808d0003a40b0001c1a012181102181d0340352806100b40c403103010700000c0b544039003403012218640c500f5004c0c100c40d00c00040c25042902d1100e031021648410308005000510 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 950579568 1250 950578318 950578351
    0xe0610152f01110a0e040c0f030207020a05031c11010603030f1b0605010b0711040908031524090a140904020120060405030405030709020306090f0c1b0a03110d17 71
    0x2100f80120030002d1100121151038252009015002c0d0b00d450003010710131458510f5000580380c1020510062001c00e2800580300e221510215134004010f402a0b80d051140080f00c0d0036081c0030740002d00c81150350341c0d1035a0b60b90034241c081c1c03800e894403400000d002c1003490312500d2525104440910502d0200300c0c1712000d00c0b070039485e000100d90003a08403041e4a140005d4000602407600e812000206045c5c1d020440302c00943c44007442804044d085013050041d00d003c250890750340c0d505030720440c9480e400358009007011600c60340c3c580e8010040c041c00f80340c0440e80051190220021000f01c80d401600703584441d507403a801141c84c0c80018001c0244500b000e0320100d2411408c010041c0f0580c800c0000b96611400c0604161800000742d1040040d00e0040003007080382d848540c005500148010b0a2f401c8944038032690a0081c003901c0000e00ba06130450050f0042e001e00003039121030803802030722914901c40b5030344109920b40c40341c070ba07aa002084005501c006500c0f42411080c1d842004448008070a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 950580818 1250 950579568 950579657
    0x1508030405041113150f02160b0c10050a090308100b0d0c260901110901050409020702030118060209040c03050601020d0c060b0a1d0a09020a090b010504090e061015 72
    0xc2480642140c4540070705d4144070f5100e43c1d04070400b80d10101040c00102001070500341c4000b801e48440c01104a40c880209240c40248020031803115180c2c04803006004a2510204810082c00a6041907000880440105040b0360039449080c0076944e03401507103440d106070340a40f0000f600c9804114400c22201d46040c0540300a807444009001c104185d0014580c00c021142500755032001482c2403010204100b05a096a04601100c1c01c55109110143c2c03500200d0000900412506084e0881484c9150a80f01000a180e00400c40e01c03c048030104000c048030401141100c40132240a070159100d00800c000a9000b80354084d0140d116a0b0301007548500000480d4038501c0c04d921400525002c0c0d2000c81a26140c0640207600c440c3c200400c2141c000d40350000ba0141d544c41c450715403826540e4080380c20603441082241c0140050b2807041c030004c2c400760200c81e612002141c8200e500f03c00180d003c030f42e003100174800120040843e0f6030a10441003201e40c00006209032000690390009043c1004030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 950582068 1250 950580818 950580847
    0x151b030403230a17160c1e05071214011512020f061b06010503060f0c030a200711030c150d0b132004080715051b06070315080304050411 60
    0x1010101503540b4138519460600e2048280000f8040310840c4108203019440d2550004811a0183c0c00075140401200c3d800552504001942401f400740e025030308010425801170400301007101e2080182d424040c049000c813900300c92024541c1c080100d10f4180c10803040700b0020202510038001010501078000c8240080e01c01e910544510084c3c90942c80401e1f038200c0c05108003401408107070702a10b240e15000e48040b0746004010040243c0010200104000300c4055110400d00400c0d4008212107407130f50707020940d858001d500100c03414100d0030280000340c00c02240d46520110064030342e6010346224072807005181c005c0c1003035042ca5541c0d100180f0b0300d0b0f0781d0100c007030b001580f41180c00030b5600014508404000142a4030b040c42d504200002c0041d0000014803404451907550700c252000c2040da000c0f60180b08129602e07003a00c0305d808101001c03503000314500c0c1c09001c036034904008a003102012021607820034400c90300c468005100070840350a00e50054000030b090041898a804116a400304 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 950583318 1250 950582068 950582077
    0x7080613021309150803040506030c0304210203040504050114010c1101020c060706020910020708030d090f1202071403010e07140604030b16121404021e06040602151b03040323 77
    0x10303c1c16841e8560340e215001c0301c0c007a0201800c03041024510301410440814aa88005068150182c0c0000001000c0c030140540c1e0b0f50031040059020303810100f001100079034942290140034496031825000141da402001c0b014140000103842d104c42d210040d848203003010584480160547c0145144201980d48020003801c006209510058907545c90406000f621300c0281c00e080c1c2990700c44102884400000415110040c0030b0f0580410018028a0301c50500161194000d0080d01e00c111250a010740200f15041651161744100e00d41e0a0b98070101403d80e1000485034003281c10080317083c000b8115244040542c03030f5014080614180c1d42e80e03155008140c0c2102c1a4180c59005061000c1c8158080000c2c00300141c498001e0014070b40010614004a40141c0000c3c0701c1c441c00224414a40100800310a15440090902d07480e035030345102c040d44031390100701040f014407400c0000070480d401d54901e907400041c8050000d42199115a0240e072038010142d1805a458114100d551007441c2490052 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 950584568 1250 950583318 950583329
    0x1060510050406411b0a20130204030602030a05240112060e0403020a0b060d0b0105130b0301020c1513032c030703080c010c17160e0907030903020d08070806130213 72
    0x555120305c920213917140c0b108a1020015590400c174111400301d54107a0300e14208200c041c03124043c0540507400a0f40a41161805030300356400400c0c008240a41640514402e034030a4500b4041961040c80f14095141790303410165540030f82030110001944105e8001680e071902c807800040d00ca881d4901e1040e5120f0859040780140d005501d80b400308100704410642001003031341c1c83d00b01c1480c999a4030f481d02105014890085444055110820000740c018002d4404064001c642d00c180001c000c680f600c8000c1c17070141c20504418085150000d84003507c20542c1c1d0035580b254041d0052100c6035000040c4400042c0521b80c60f0300d0011303250380d024848100154400e81560707595030321407040542034540350741d014000e01500c11114044424070b1552150300c49091080f5030306001c2013503400c3d280c1583c203544080d005000c4408126140340c00da4082da02c558082e40803296400c40c030100072101d092040356a0b800090f18003010802a0404444d00903040c8900c0e00c000d030804449032803c1c5800515a07000c03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 950585818 1250 950584568 950584697
    0xa05180306160f080c0703050f07022805061603030510030c0e01090f0c0c0201030b21030a080f10050405042901051203090f0d06060f03030201060510050406 69
    0xe00710141e400070480c040b0140c01d401c0904c09494064080086802084030150034444000b8416055840b003404071401258028101c4581e55030b5848168107c420303844c01d0010003098180040341610780b00701940c8120040503840c1500a80c90b503006c41c00391502800b1684400350700000400000c84040c80c4002a005048840d0080d61502c106441560b581b20995011a49002060818a81e000201e050126020b0278046020600c10020503408240b4480b801103119840207815a040004401820041460b80e100705140d20343c4c150035111098150381a01761141907260070096401d0079085150b119002e0320002090040c0404a0704446200f0345c0d1581001b00c0882c014080c520b010004501b0441c0078a0065050414803004601410440c0719880e03c00e01001c0088420886036800040191845580b028040782e500c0c94040d0190500d4019944a44202400b040e0003502c182c0507034049a42d55600d006202d840d1004581c41da5820100b034418594100a00407e041841c0c5031007419403259514 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 950587068 1250 950585818 950585851
    0x30f0a02061008031218070b1809010e01120602040314150106141b0109170307170f061002102405030319080c041a07061406060a05180306 61
    0xd09010004001242e2006410018449090f000003036030003480000480d9249034450480f000d43c0c4990041c05a0554860124049400281d400103401e04030303c810302000c2208442c00c100541e001090290404504190004201d2481100c1c0c81c404507900501d0300600d0305032a86ca4034a00101168081ca846034409059011078500c0d104100d4010702d078514200c6904055080c80c000544a0243c0b9200c0240c81c3c01690589104c082d44400012580032042d000b01c2c400000241d01c058200307e41c00400710b120103480800c0007030035541c1c41d80301d040003011140c8603907034501c100505074034021484c00851094810500b10001d46109a042c00040d50344001200d1150400c604407014454010038002e401c00c2c050046641715100920300c07410f0303c50a00b00031590340d441501300c10340035580c00b44400b5508410f0b001402107441000b0080c1501a00c010320007491760b2541c110a1040035550207030081c500700b01043d0b04034401c4001e0000d002400d402d6881440701800040d140c44819502c281c1c0e031075007245 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 950588318 1250 950587068 950587087
    0x503040209060901030b15030705030706082e0306020706021605070810020711010f022103150f090c090a03050703150b1e1c1b083903010608030f 64
    0x304072648400c0c00c0380d60f9405913041d0360f520804540c4c0649086010750701501c803040300e0764046c00180050203010781160b03400f694603140200340a200b40c0e002d00c41110b4480070348134001c020403c12514100900f040700d04407403842da20ba90003540507c0090380c205600b48001521141500d00225007107015000500ca580e003805102c90034182c500c81e802600c1d80c0f042204800140440d60b4000c510700003420035401c03141c1c041c0342c1641031032030b10003111080300c0c1c5081100342d68030030132800b642c05201c10b075a090010745900c0003400110804000c2c0ca603480300300b000c00250f05040b03250003009511405004803a940d5a20b94810745000d005400440e0841601c0ca503451060025101d45020a042100d500c002d1054103100e50080a50340c813145030040b0032143c503410036000e02c000384121003503000840304e071154075500704003199040324002c09180307009424080813418000d01d00c0b103002c1800050410218202480303414612042c00010729019503d6060005d1801801c1c00a0511008441e801c0d0b5036030000b00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 950589568 1250 950588318 950588329
    0x11503030e0303090f04090804030b0702010e010b0a05060d0b03190302010f11070b0403140f03270105070207090902031603150608060417030403020a020a170601091428090305030402 80
    0x108401c0d00a600a201c5654165a00c0c102e0030940c400640d40000e030710482e0f0521046a201d40c1c0c00103006c442c108824031901c90707415800100c03a54071920003049130b05848800c21251140707503c51140d00c0070091042c520380211662014850310b074010200c0318000b031841187c114070300b00c0c4541500541d54880c041c940903500c0d0300610700d0040c44c00f8042403410410355110a840c00c1301a00c050100b03c603e25242d0b0603130304003004640c1119a00c4012a80720318004200d004941c030310041001150740c4209171016600014001c03903000e200282c001d40951802d01c0c140c803000300790244003a42c4c180b00d804064044440c8803501d55014601484d4502003050540d503101d815604150700821403030b44a2420040451416000c0103008054100c1050f50b81c1c8640c00d0403407800c24024406580505900000202c000c0020800e5002d50140020380d031050381e903515180101e4056824458110540c0e0b400241d20143c01442c56070300340d80c5034440001a490880f07280c000c40f459580d0442c00301d03200100303000552605 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 950590818 1250 950589568 950589587
    0x60c02130b3303281107060218011403061c200319030203090105070f06050907090c020f0604120903080f03010f051207090b03032b1d0712060204050301150303 70
    0x3040c82d10b491428031554140020443d89104c41da100c02e00740030303540001255001040c07460f4007546019119121030400000a521400300031141914148214546500926207941410240c1e54954116601c0c10280003e400f07060386984c00d000d0004140100180780f0391031900850006103410000c0100320401d01d460a640d05a0b8405900150144200004d50000840718007010a00e01952030350f0b80c0740781020485500c900f0007004503003031000f0461031001c006101e1040300c0f00c81c41709018100342000d060341c40d09030a06c0b003406540c024800280218000c0242c0e60f030810303120725000c0001035a1f5150004560480c00b0364002c649070000042040221418204005c0c0500b00d03001c0c9014442c0400c03480d5206d4251180c600c8046d02e8201d014669581403042d10900501c0c100405940b080446030ae08400c15410100a006460412909500a95050040c003031559207002400d0701c40c1403101a144a20803080222280c503000c10011625844c00e0003100090081c0c2400c0c22545800c514002d45020003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 950592068 1250 950590818 950590909
    0xf1201060311120c0a0302070501090f030801062303070203091c0312020a080609060303161a01080d09171c020c030d020c0a061d0303031008010f06060c02130b 70
    0x1031042000300007000c03000f150882213214402c4e40d01d0140341c509030003030302070484098019480c00c031249085c03080c1c075031800f1a070034403a99840941c1c1c0e032282815a03003055070040c4d029409520000c44005d0072190b03c01235800002d02d0044a0420800350000703054204103003184031800e000c40c08030204140d0000141000c607081c014081d8180562981c005207000740003080d241c07096044a000c070f0703e540c8042c82180d0b00c0e0700b5a0407059090b41283d0030110071080b40b84c6019241c0c03504190000400080c0860718140c0000160340c0c804c00580b4119001280343d86076562048070703004000e180302c1d00f0030000328140200480303500a80a02040e0700300705420040036598100c195081680f0040d0749540c0c0c0d41c0b8000541b05d40e81040800001e00070385442c41022843d5400e50107220010070311070091041c0404000320b03040300703009000c003200b50083d480c2600d403140320b0040814269074480c0014907044015000c10310410320001101c04002e4006024460040000200c24103400c0c24558a081202984440d620 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 950593318 1250 950592068 950592101
    0xc14040306020c0109021f0f1e1d10180906150c17031303170601021e0313080105061e01140c0313090507020106060c170a0203040b03010f060306051806040e030f12010603 75
    0x344152141d112490310003021074100418400507044000000341c110b2b0a5000240161661850040010f400090b80c0710340f12103c60311243c000100c460140c024441aa500c4422000f499170295078107450841810700c00712590060324010748800005440503612680d030141a0100700030311810082c140082c41542c0001d05d040650410009980025009992106030b411548890b41503035200c3e41180a00c9800600500c99031500080040c015000603000d100b0803903a50101151090080c01d02d80c082d104443c0c041940780301041500104000074280b8090f0480030ba030318100c416886602220303900e411810607940d40e01c052010541d42445600c01034410f60901100f180401d444069404282c4120319041c840000b4044aa20f0b10a00a650041c0011420151a56100c0601c00310100c128001c10000030305e032003400106454000100c0349851022181072016072116401c4c08040c0941d41c04845251108100ca0b018801a5100800d000806800d410141394100301000b81a140710403000010705 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 950594568 1250 950593318 950593337
    0x40b0c06060a0b0c1e03070b1005090108072301090e070c030e18130201090f0608190614011107120c0312080105010512041b090903030c14040306020c0109021f0f 71
    0x1240002d42882941021030b0528170b0005998000c0d1951040300d8000b00391200c51400d025104464103c040141c950464840016a0300c808040da5501024407808070002291010080748a48116852202c04030600d00313a11722544407103041150010035200c510010b20110005410300d0b90280d09030150b2001140c0c040310418005180c0d0404202c0681000d00c80710500104004680c0038001941c0101130003903145040e59a640000380074080206d41000b502d2481504441c440f0741c0c3c51041d10150b407015074030045087d40040c0115140d01c411240141944220440410b0308010b03008840d00580c41800c614003010305502e02281140054500380c005c0c4404200140a640c0e00315040d1050000c1d45052510540c0d42e50901c035902180e00c0e250781040c51803604010500c007503150001d20740c0d00c0c002c1e01e0030301c03001280640c200c0d1f90140030700f03003002160010b220a0002849030340003400d0041020002080c00320a5400250420801c84441e40795580350031440d41c101900031450070b004000708d0400e0b80c0c64 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 950595818 1250 950594568 950594587
    0x1209100c050406120518070e04030212070c0b090d0606090903021501030c21061125020307090906110307110706090302091503030d0c0f17130b0c040b0c06060a0b 71
    0x2181d400301d02d8134010a0b265000260401d104030f80321b00e03210316944202c8882541e600001001140f09072415801401036140e103918105104003280d00c1e01d0f6000c000158078a00d040c2006405030404410503038400303d00218040402d4042c00707050b020f0b184d00800019040020b10300a4078041000c901c2001c00580e0703100400206842c5070151044480c020300e00b80a442240c00a40e07100300610f040148a285001d01c090765000c00100548030700c0313052001c040103d9924a8000d00084c5107078200a41c55400b0b000c4c01d00c041c1000c0d40000404078071034a404600000c2c203900d07081c01604103d54480009594068111034080100500001132107241000c081e400d00f942c0102d1304885000741000d2907041654042410780c1c0302001160701e001580d044c104030101701d95100070b10721740ca1002c0c40c0c00080c0140000502c24a81c00000d41d0052055414101420b416545d07448078a0400801c1106040c8090100180180580000307000398500300340503041c14030b4100c081185401e40e5401010317005c48244019041c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 950597068 1250 950595818 950595827
    0x301050111070e01120b060301020702030604110f0301110c0106061107030602130e130203060c0f160c0f03050105010f090c020a064a03070201020307171209100c050406 74
    0x1510400e00e00155001c088110441ca4042143e01001c02c0b10050000090410321100c84e0078540c0344110780d81241078032220101070907401613001c00703136158200c40c0c046400142400102a0341a00203044506407400200c00a4211060b151030070b0020383c00000c0b00c14034000284621b1020303201e0b13070404985c4004841105592142c031800020840c650015401c05e0032000c19480c48002c0482d0524a8074034500005507441061011108034020701c5404089031213540e10303000b80e40f01004800b400c60b080410907442c0001c0040d0b140c000b0b50707940d41d2aa030702044010310448039201039402240049199450320300b0604843c07150703a224a43c0e01e85402049500039a01041101500c2c0c0c0085000c91070030007450540c50b0204100001b0003d000f00c4130506002d51200c3e007e01000300c10b800c402c022890456001d0242c45c0c1c03080840081c01a0801c101c020001070085100f8031012201d4113200741031000e20442682c402070107403800c1c0c411742c2c000e5a80340e011003542c3c001c40e41c44a0740c62074940c1c103143c0340000241c03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 950598318 1250 950597068 950597071
    0x30f090d0c14010204030602182407030c08040b03072601050d0822060c1406010303140a03060801020a030f0b01020d02031902160f03030221030a0b130911010f031103 73
    0x10b040e5004248091034050094064401858100344110b5848100400360510303d0905100d190044c80c180e0801c101245500b01c9038012000c00a106524004082c3c0d030454038495050705c100c1c0d01000600000c1084241440558030170b055a440380c1e01501f4507980000f800340d02003a8241d80085043c0d0050040d0f4079400c2502c3d40c0e0a60003074075a500e800c51600e000b407151040e0440082c042c60340f0140000d690b80d007c0b50708028540260800070b0404a881500c83c1c80d14400d0001502081c0c041c0c80c0300e241002c00e00e00801103030707403140340004000da1120281d0742681d1100c2034040009480320030340c4400700c0035441080c010038000d000410ba044155a4040d450707020340314400940a20000c0d00252142c0207022404403400281420403a064442c03c543d4650315090200758010320503055010b08196001e105600074107801085517046544c0c00641c00080c0174000d00e4207400100101088844c07229902030031140c144a40007081b40500f0040004000f940f017405000201801c01b94241ca500070a0700c1103a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 950599568 1250 950598318 950598323
    0x1020421060b0d0b071106060d030e18070503011d0403080705090307080a150c142712010f0e0d1211040b030106020607091d0a0b190902030f090d0c 65
    0x49412414120000c1c0b80c800a901c1c0c20103181d4480f541041030045003c0e20404003900c5100c2c40b40c0152003059518842298a213411840100983d00800c2c0510304e185000781c0010304116014004188407800c4407015030b00c01c1c020880210042c01601e440340c04070000d030201849824001d19003078500420061024000b14117103c1c000030080c030a5101070151070b000c0e01410701110808403092901300ca04149007080d45405510b8550014038561040e0807040101c1d00d10080603007045c1340f410892a08404003030020380c03c0d00400c98131516035154240c0d101da262446000000704d000422400e070f42a80d100d4801c22510350490400401d18540069228000d8164080c000801700c0411310f505180344103d4001e42a400000700001843c654001201031080b880c41d554070018a0380d40548050340c0500d0026081890000000038942c07800070342c00000e0241d002843d50540920003803c40900e0443c0d034100d810529000800c0100552403044180e822501c81c0c0000d201c01c03000313208010920068041d00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 950600818 1250 950599568 950599619
    0xf0a03030b18040f081e271011010b10031d0d05040e13050609061b070c0b0d0f241a0726030114100f0e04020703110105040f0b09010204 60
    0x10001030012110644540c030642104a1070320310300b00c841c0700280c0c0d0015042c1d4100703c0700500341c10b80e810203121010b8041d003d0152018200d0480500c1c181c034840c1440c0e021500941d600c0070280900e5849007002500340001c2c0d03d0008ec0b0001d20354010b43c3e401c0001c0d01c0c0c150203900090a0b054035a40c4841194211035486224055517299482410300503400144081c2c940c0c17280a080c4149041c000c2022400340c103554044001e41101e035031360010380c0d0140300c201518500180c04100031044028009089006102d04006907641c900c513071100c101d03901000754a059100d00070000902c0313036105259102504049520054041c6d10381c4545009120301c2ca00280070700343c83c1d2070b4601284150f6080c04c0e501201c0b40780c004e4480d80c4070340400d40122000221940329104000c00d0058050280022000f000320710ba50f0201681126000e010107544015012020414000c1200300d5080082c41000d006030b10421204080c03110368281a56540d0340540801c2d05648100002c01140c1c58003110f000009002120 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 950602068 1250 950600818 950600843
    0x140f01030207171308010e030d0203090a12021c05040807060f050f040e0a050f160e030f030414040b060c060613090803310506180304080f0a03030b1804 67
    0x100c02074002d041000b000300c014032607202058240c10016010081d000b21100c45029500c518035403d8400301e040950068104009080603004180c008542c48135109007181c041810030703590180c140c44500610380040e000150b4420034010311422a01c0d40b54024038001d03050608201e102921040107206941c00e004100408c000b2607405042079401c400c038140906501d0781d07501c41443e400c0d41800c03200c11441e60b140400141000e40e9200c0200e0080554945951001d02246015036488004c02c54441c0d06100380420000c50110400050002d002a152265480c1150300f041c4070503290013007070040c41100180b00e070041124000814560001080b68200f041da4080c0f51948000c10401c03c010f810400000104120448154082c415425544c07103600c4330715400d60308000780422040001001e5403c118042540d0300d0414026001c0e01c1c20740700540e07180640c1d6030146803a040106031030020582000440344103042e090b101d040d8040c9425203d9021205c00e071080b24912030b60003000100900700191 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 950603318 1250 950602068 950602099
    0x1401090c0909091416060f2c032a0307060203040302030607030b012303041119050103321509010f05011b02030601180506030706051b2104080d0914 65
    0x41d8048049070210042d1502079420901501000350703e401250085810b01c103050314124422a060310107940c202801e80c0c454923141088100c0780c8101b040c00e43c0d0600c90304c40c040c10681c070f0b10072001c10540400070320041a1190802407500b84003640e440b072025500140301c10005078801240716580700b00ca600e400512070400c080160399600840c1520500c480c00940c840c25603540038401540101e02505520b546024148104038054402810b10031540e014042c003040154080c0e004020070010b12204030400e00500086d030481101c022640c50300301c40307244c010320007179040e1581c01485c0c2a8040e03551428540c18905c2d001c1c420a01c1c1d02c41e00341003050041c0c044403080a80005010404da0040030b43d807443d45d50b182c28907a17903c0310401c600d06407868000403c40503e00052101d04654864841504200040d00c085040503240c0c1e01d005030b507006410242071650460b000108028000d4402d06490301d052800d2980751144481c590400d100042c0c40501041943c13491780006a0f10071a441215041141d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 950604568 1250 950603318 950603333
    0xb01081317070b24010225030b090304030201091d06010e011116080705030f100b0105040b0c03070b0703022a0f070b040302011e0f0e04021902011401090c090909 71
    0x3604140606a00030800c54100103c10700800d026413a05075440c10b484008502c44c0302407406a010701c50244e440600501540002d0200c0c4480c404c00420450b81119940c0d1548240c4c00e4049802c000182c00c0050107204540c3c11114281c05403010010385001c0618115101700b080380c1c050402810310000c600c910343c181e84205c00350349084071603000f5981540074080d80d0201c880c1441c001c558842c000c0d8400410941030014000441c1001c03040201008110ba4006a00038009540d41504200302000702055081444c001801280c142900444c2e40c4d280d682002d001e40f0601410034010940100510400950300d6040b072080d007408901206011071a05484603c2d00e030001c402240d07180910540050360a88c000c0182007240e000b0380300c1c0c01f1054402e801c610002d1010050302404100442d140305501440740320036068007940600018581003001c1440f03410701c0d81407070440303006030745450401d0a41801c44640d58010b28102c0300500c003186082401815090481c01840c0c2903a40d07407080e40c428082007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 950605818 1250 950604568 950604593
    0x604290c0d050a11180108160207030b090106030c0605041409040819110703050c030c01080f01060513030807150f0509030919030b09031b07270b28090b010813 70
    0x440c591140c0d243e041d105c81803420510003460754081208400010b0038524149850082d4410950151041d107080d03903558000c821028204d039403250b50b508800700001d80f0b040003090181c0420344805840ba0310b0402110004100500840d0003440351006000c00030b1a848166005022424070b492a1a035000001f26440c245103036060030244a90b01001043c000c0c08a0b2140c0304090a609071440a2001c0c401034503455130540d1032a644100090040120710b204e00068845a01c100000320f60b0340360740b0b4a0710101904400d0b02629224920358a181c03440c181e83c440da10810401020030303c080e10300000c04907164021400c0c1c0c18012460541d08d5030b1080c41d605c00940246601000c61122401c0c4805565500d400c28068403840c1007c65000c0c4c107030a8000100441103d02c241a4000080350032000413985044a0714841882074556001c800c459135a003072a25403002400301e0b0380034103c414000031592545a80d001143c00c0c2e140003c001c0460341d02c070352000da00282108011407403140034503100107400300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 950607068 1250 950605818 950605841
    0x15180f03091503130c1202030106050f18041a04030503070e01110709020a0e13050906180c01050c01140106082208090603091c08062803020915030604290c0d050a 71
    0x80c1400003080400e9094606c0c5007a50082c0d000b08011503c9000740a44c091000318196030000140c4103841100e40d60201c0a0791040c402c01d800e140c4007403503c00d056502141584c040f80414008810445226031011120003d000240380c01c1100f039940341c1080e62112014011900c00760340020703800b80351a0156103102a611000380607a1400c00c040e03540000102000c0d1007c2c6042e00500c004541c00407500f02220381040c0004c00a01424008040199441c1e4094150101503540390a495400300030507001890080410fa250440e0714a00307448400701c604940025041e15011103118030011070010000c0c2c1e120b40001b915955925201c0341903103403400303200e440307803599143c02c88050b030310302030741c0b000b02e25000b00026280c01400e20003143c000c2d02d4420b4407040b4046c820601600410152410188a42c0c100c407642506904000d54440031034140041104c00303031504c03c072410742d6500f804c01c00c1e60000310010312182d6403000790500c813401c100184580504101d0494071344000c1801c0c5103159010350b00140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 950608318 1250 950607068 950607083
    0x1707140c0102030411061810030b03060411010e182e080a060f090b0a0f021e0301081e030a030f0b04050a0e070503030913050915180f0309150313 64
    0x18400e21000740030754001c0f01c0c111840600c4152015850074620280c50011000380b109400080e500000e000b0b0400000081c00c0400d51514422403031510240301d224010350040d41c154100041a00015002c030501040f074a0240e08030000c3c1e58410800240c0040c3c0110a11941100c10403490300d136010b20300604080310003903400b02880020556000079045092602c288420b01c035a03000c5e03920050071101050000b4040500c984c00103201501c843c0e01c1500e803103c58079001801c0103c00200500006056031044400c900000014852032800300064007541c13000c5d4228101414003080066140e003d002c811000703060726541c4500140d13140340c0088404a6024200b00321626051003440081e005601c0b94a00500405c0030100744c40c00d010040f103030201c0c070161009203407440344403440000f45030081a83c5903a0280c9441c48865040d03010f4000e01440b0104a0502102c2d02c078500d2608091010000342c0c51940100318030b07040c40c0c699200422000c0500c542894890380c92080002252103104001070291 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 950609568 1250 950608318 950608327
    0x20a050a060801080f030913020702040f020c0c0312130e070339030c05040614070501060308130e04210e030d0201020423150901090b0f090405090a03170714 69
    0x76680010040c0c100d40040b01160851540c083e8072a8491207181c201d56009410000c1d6101010450b40003010154405400000c0d12520002d00e0400c0360040070032a05c030780d000303030740407000900c0e04100c25640c010210300b0317662070070f0303074103405094024900e20800c46400312040001c0c136031b18041c0c1e020b402043c24820130000c4000c601080d00d014402d20550401101840289507800c1d00d20901c1000111038154603424581303400d001007a50501404c18049911705410004a0001002030190000840c418a1544d45504588042494185994211a140c0314440040001090440c5400c107101c2d00142030f800f081240ca400211500710400e4110343d054407400c7d59510690380e0550041c400c4a0440494488400400e4140303100003a41d41d8090b54003070191081082d030450307103c0c010498a481410400b4005555051800c002d800501c103c3c400c0610208110303450b03040500030258003502c0b42014201900c05540c014081c1103114421700b800000010024400e03d0040302c961031300710328940845498 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 950610818 1250 950609568 950609579
    0xb0607141617030316021c020c01090b130911072a05060705060705310f0906081f0b09070305090c0a08062a071506050d021503221406090607020705010309020a050a 72
    0x2a071058480b02400580d8400c4002103008401041d2a041480853783e080d03900e19045002001d003d4a2041b01c0803004100001d000141d4034080442c0c45145174100c00b0714502c03401f100b00c1c2400d840c5a0045024203c2080140001100441c11581c802d40600b041501d07014200110248000b024124106c2a281c00818490000c030fa14090340449080240f030140070b030b86030750341141035401502c01d41220f540107109003562220b05044100c0d000804640014000020200048000c1000d50b590740120b580d6509102c020036007800b104403d102c007034039134400d0700c1c1c41c01c0d54003640c1b0a0020030801e12103c0f515840800c1c81c1220310955020100d0f600f2190301c50604c1c1c10720f0617030892001202c40e14145412000030b5182080046020555001000400340307040811103c8025840284502540c2001c0d00e0203a20360741108003103c00d1940250f1801141030a00242ca914002e001740840e5055030062080005840d0300142010a4803020f03c0d010845002c2e600c0030548190043d04110341c411521035000c541c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 950612068 1250 950610818 950610823
    0xa030f050f01020a0c080717043209010608092e0e010b03030909040302070e0103120e090609150f10020109170301050109090b0607141617030316021c02 67
    0x20400c0c024001d88858001c0d103900c080c200d10030b885000700842e02c0ea200c01004a12400082d09109000d03808107065000a1030602459034082d4025403501a24034100001d50001d00303420004203c4680785600790590440001901590148114030400c141c1d00c000900d52070080c4900c0d4465401e039109040080040140c4850b000b08400d00310340020302e400041040c070001401050f00e2030002a000d1403400506406000308240c1c000c00940941c03150100004002411113a80c0b8002c40c015240303101c1c240700d20403000313010301c046c1c0d00b170340b40701302105d80501c02c1d01e6035503031003c9030001240140d1400e50110800031030b002900d81044140d01c00071603124925001e8064101e403001511905002c450108201440074145c042800369a000a901c084144031091a607445402804401003245052070f51903a9414540e4081c0c61000c00300ea0459440001c02c0001c1441144c0070f010000001d010400c4c0300c95409030741c0d0000410300c2185122a84071404864000e00030503004c0249440400c2d4108191003002c5d6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 950613318 1250 950612068 950612093
    0x10140f040912020706030e2a011106130b0a02030f06010e1815090606120619032901060905010e1302130905042303070b0601090503030a030b040608010608060c07110a03 74
    0x2808a420140011082c11000ca081200d40c450003c8c0070b0740c211140015800c080724450350b068107026444420f1998403a003000480d01c10840c200c55800150418640a0040030000d04549141401402402483e5000841190f4488401c3c648000440c8840f0005100e00c844241c800b002c03580810280034940071075100103000320b03000790f91961003a01c078081400000e00c2a401d410342e9408492010074602e10340b21503e407045100c950540050305890303403500ca110049903030b0840442c1c20007400304030022200d0f0312268014215400c2005c4401d03d014006003096100707003040b0b031154040e0680718000d00410307030541d4011004a10036079000f6403502080c1000380801d85041d1352034051404c0c51300b407032030700c600d8170141c081000005181000810b40e50b030b8043d8240605071906004200201080b9620f040001e040000321a075004605082d00c24180700c02c545968100c601e4a034100001401000e800242454022180b120265a0759009041c845080c49545c040d00b070b4070400003c0008184509081c061 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 950614568 1250 950613318 950613329
    0x1d0103060e06040f080f1b010209090702010e0307030311160309080c0306070504170a0203120d05010b03040819210b0f0f090a0902010302090904050105090610140f0409120207 77
    0x20008491105070040d9116000c0301c0051113045a4546480000d84480c09498000f0544480d141082d042c3c501d12814078000018480d01a980810f200107989002421242c010000e400200301021700b8180d100d45a115460018050585400600300a01140811100c0883e03da1100c12054090f52400618958040c4103c41e820310038103a4440c01440c01152080c02910903072622881c00b489c04c00601c0051400218002c0907000b4102c4000160310b09005a4503540e18000203203540b0800310305141d048a070181c20000000d0018030400c000560340e00d044907400340a81019220381410b00c80226022039252882e42a0314444c00e0055280000c15004480e0011044031030002c000c0881c020301120300d03140811190b0121503040814500f205075440030b80f5040c0180350140c07421110402103001880241c5d03088521369901e00820a50400600007140c00c1b44500c403408610501c0c1c458210403111444c5c0c8100c0c1300b01600c1c08a503189907940e50003001c0d0554000541c049200d284040030f5260b885510a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 950615818 1250 950614568 950614571
    0x106080f06100e13020d17130909110f0a1701051e07120203090312040803010509070c050a061a1e0907050c100b0f031501030615030b0403080a061d010306 68
    0x8502c0e440040361400702680c0d41d035040e0258030740d80c1080040610700c4c2c080050360031000c1c0150300e00c040b46200c240c50103007800d4030f0720f55551041c0d580b0b206206004680c0c051080d081c509102d20002941d918030104c00703100200d88500c40e4102c82c00c00500390145503401140ca0704a442420080801c046d0081d07403027a80d07504040c02a8907580c1f01200d022090807507003440043c03c04040c00d1505e5100d68041c50b049141c05040340d05044292070491000c01c01034806446551001c4010403603841d04031080e40c1d0010301403804440400c49940d03010303540c1c803030008014442e0385c0f50014913402c0c410b110021b04c00b000c4000d2440c40500020002d03e80940a1803005500501c1c0400000301214002c3c42181c00f002d00c05c1000302a247c2034000340100519810b042244d202070302d003003503014540d004c0022140e03c642800c09081c480d491450500304541c920a20240f031a842860100f0126400303a51480d4850f4040c10101215030f00c164241d40281519001520f03d0b80002d100460441c8414001505a174400c090 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 950617068 1250 950615818 950615821
    0x6320f12030a0f2c0120030a0905040605060f0301030f02061606020d050601050c070e19060b03100f0506030403030209130c0306170a0809220513020f0d02011b080c0106080f06 77
    0x3203c4410001020b2031100003a49410308130300700d501c900d48251900d0400d910003142e082061054500b142d0143c1180310001e081d0751401d211f40d00d0244520801814200d03415850025045000481ca010501c0003505c60009000c42c40117540700c02c0c046805c0700e41d0a5814151080461404100075080100b0702003000d490000000c555502030400c590080201400504043c0d2030038100300304025009210100c0b40c42040c4e91130f5074003c140c2c054180036021148003583c8915094041011581644d800a5411040404100304070785450081300d800c55018a80540e60313041d290302240c800656a445920000d00c4d0404021801c0d6050303001e2426144c0035148070002020340800d03e5600c100150300070304540d0303041006e00c44e94600903040a0743c0f5981c01d801c9034881c210382c880e0081150740894403003100f0390168000c001107103004481114401c2c0200d44246248600c1d400086c81c01c1c2e0b0b18010202c00b110070b104401c09010581095030041c02940c002800310946441031207032218a503800742c1000d4400d950 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 950618318 1250 950617068 950617097
    0xc09270d08011707180b010212070f03020f010207111018081e0309060406081b0301180e0f0a0312060b030a0204031a04030e01080403091806320f12030a0f 68
    0x4c0e405048600f40213604100a0300614044010700394106404d055102d154614013015440c1c1002d0002d2601602401c1c088001d2418045c0c2019921484040c2d0342e4130410506c2c0000d00c3e110107038991b05d80c040d15075040007003000105480f06082101101c5001ca4a9100050b0300d00700001e032a41d044950a107007621420b410a80c840c0d0b6402000e010f0355100505000c140503044c4036800042c1e0000903d800840341c8440075030300e01201e50080c0c100849400e40701c2c2c0d455651015601a80c051a00b50000520b44220b4105009866920062008040042e0004034404c009000d030403a4001c2e0108044040d0780342030011501c8000d40c0140300407180c0c0380d40083c44e242550321451b4503038422500b40d00d684107114000742c011100507100820842c207010349900c02241c61643c1103d02e0f00c840c05842000900c9a050204c0b00d41e031800c0440211400403903002c00031044c00b1010303480c4000800e06940c118141582000003035100e0500b074810001c248008150510455484400c01ca6070118a8a54154540015 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 950619568 1250 950618318 950618323
    0x150504091b0f0e01091107120302091507022d12160902040b032a040801091104060f0504050a020c0d0c1e080f160b130c080c09270d080117 61
    0x1d1042143c030080d007000400061015400290341002402e1a030b03441d195255950700b42d00c0d401c1e108407000083e030101c0d40310b12a09141e4502c07850540044079072810941241c0c0000d82c0700000d40a02e004000d11140c503140c5403074030a5110014410003c0c640080c0134450405550380b10a18040707501c0b42040480005400e00e01403007180c007554100c184040c5140d90b500c1220203001030302030740001d4014254510390064100b540142000d007000da000803d20710700d581015890240c800744050311885c90708404001d00c202d04204c060458200b90303001300c1e09236103100c60710000f4050142c901c0072a000d443d540101d4103620424043c1921310424071030410780711022081c0c0c40c4d069016001441c2b0b00040000c9004603038804086e00c4542c0e40c40701491103007a49603036491349070082907030200004598510200104851a242d40c2c000e04080c9004020f01c87c200030000f546444041d1020902003101200c000211074450b07144400d6007054400c4564155034500001c100d01000d21613500daa4146064400d91081c02 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 950620818 1250 950619568 950619599
    0x152703021e0c120313091a040c12110405190501020d0513030305070f1704090f0b031e031e030601110102070b01031506080106080c01110d0f03150504091b 68
    0x3800018500c108000050009050600c1c990010f40c0c481804581400910b0b002c04001030656004080381c2c000c3e0fa5400050748010107401140f0660a003a010307806254009101400381125480109608508081003e100d200d590001d83c0c00c060134000744c000d420710600072a801c4a00a07422903d500c8150302044400b03018100d4030489003800c000040002c648201c3c0074000c1540500b1401c529442c466035110701c01c12850340000c0300319202150401c80e0118074400c220303003011022801d0140b034441d200003071340312114101c4001c64030b01c07400282d00c2d00c404204243c2d00c408156240d00142041080c14584454000f1244180083d02a00c003a009100040c002c2d100102c0e17102501e010140d0031640d5841c0d010b01c00d02c1c40c8600c055560030000400040c240280001801e51001504590320041d0005100619410a42c8010b03071010750940400e5031300070403010014116143c0050300c0303080041210412482c40d4480b81e40241032441135001d0085020550031500c01158a80b02060b036a90700e8452a0b0300c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 950622068 1250 950620818 950620873
    0x8030307021f0b131506030902030307060c021f14070302120f0612250e090703060f1d0d0f02010b030712020307030503071a0a0203060d15270302 64
    0x200b03400c2c0b1818071442000c041c07034216607980089071001c01e42022032507804410428009503078440c0f50784150310300c4d041280e0010b8080c1d03103018445010250040b80e6203100342600106010398807840d4040191080c0028000380143d80640880982da5006003005040e06416203800706440300302040d51180070b4403c507102006124041c0210b540c0c2c6403011220010001c0a040e0050400110740c01071940c280f0a13003a40c50080000c0c071100c0e403078040b6200300004403a01321107210003c11080c000c02c400e00081d1203080b2a03000304003240042c20500304601400c0300500c4090035105035104daa118440200c4e0606894040ea80c8440710485926001c80c242d40c0c10110280e0140c00600080c85880603110900e280d190020b0101d4007050f960340d4a0500c2c2d0381c0003000645040c4031940204201100000c04540c10003040d18040d400c605140b0001a220442c0250080c58580151094040c1040035040703000c040c00c000340d220403141d10350f02481c14000d02c200400c4005009480c40545460b03d141c41141800c2d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 950623318 1250 950622068 950622073
    0x10909030e0d020a080106081605060a02061308040503060412081e0610140307020127030210020304110d05030c150405060a09030915020304090b090f1b0d0509070501090803030702 79
    0x20075100501403641c1d06058140c0c4c00a002c0440407480d80c9090040800405440c0b00501c039610a02c04014500346160b0480d030720a040c100401c21080b40c1c00a86250080001c041c00c00a149240c03034502003074412544a6074041c010482008280548035684d02600300755501c03440856610b0041030301808900b101d41d40e042c0c001210229106061048290a45154a0500c081100034000006401e42c00468880b00180e46480c401212000140a2804003814007110502028a0b540d03002e9103440c01020091030700f40e4044000ba0900c6a00b0140d540d42c508013030850282854a810803a4803a44040c2041c0c0c074900c108036442c02c650820749045413040390464041e1201d5240c48220300e000d400d002c8419010000b841c0c1c400b01d080c1a0b0320181c001652500c0e00110780e40d80c9000c44040948030b40a02951040d03885100300402d004074101c00700c3e801810050080d0079899507003168130890058640501500b441c2c8402c021001e0790026038101907800980760711101c2585c4149185d5a44000c4510a0058 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 950624568 1250 950623318 950623337
    0xe010c0f0303020901030b0303181002031207030b0112050f01031415010b070c1502070302090f2e0810020304152717070506040606060905010e090c040e010e0f01090903 74
    0x1038440e40c013429a21005240100d03240008000091a40d04a840003212280000140c445580b5007286c117003118161a001450400100d8a40c00c00414001005001070549840f15030419a1241c0413008081444250422150602609a00c603e01003400112135141101010042403040000c10074000a1946c0d0048850307030a00700031003460b80040000b12400d141e0007202040302140d060b50700220300c0c407560040015510f5401081200344019110040702002803040c481102c032414944d14484d549100510000c01c0c44600d0209000b25541c418020350064588150b11b82649030000c5018501450b0703420508501001d42c0821180e5400d4000829112030070b010852150284205c2c0005024104100441c014040381000c3caa00c00c01080b00c9a0308860100020401188540c80240516261900e41a030030200040e00c4d65901c0c900b500c0c8680d140c503000603001c0c0c0e213850403907001e02070302070840190b540d442c03000103826030054800036001c007500400400c810002d1302c02c40008940581e01d60741d65 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 950625818 1250 950624568 950624573
    0x80912030415083c0f090c1f0e0406080616080708042013050a020c0f06010e0609090321160206061c2105070c0603150b03040302030c0a03080603070806091018170a0e010c0f 76
    0x90300d040789d0039900075456107000110349506000341751041001c100c10080031151510020301c0c0507402007014042c080daa0040c00301040700340c9650103017204031045803060401c244000030001c01c140c1c0c051040950403d000c0100703030034040c2c025002d00d9030100304407400300740e1540704c035900c1d03110900031680302e4442c04001501070b240420780c60380c0040401d41520b143c000700ca64a80300c4c07403044081310700a503903501c424009021484104400e81d5001807000d0107450405c000080c00011410131030a800c9002c8180c40d105011755110561040404184814001180d02c44090150780003824103417075070030780107100240140c02130090f40120030b285171070180018105a000981500050f2043d0110310082c41002c0aa000c1000781002c19030180d107450301c83d4034202c2e04151038184035422a14164204c08240120710f5400555a404104104008a081600c1c1e540328240054030b424007608003a01d800c5012064131411000b88242000b643e1072003001460900103403003041215100508410740126850003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 950627068 1250 950625818 950625827
    0x2010c0f02011b180f090605120d0c02280e010302040c110d1b0b0f091009020d080307170a09030e0a03050316080912030415083c0f090c1f 61
    0x9201303c032040c040c0783c6610b89a1071081c2403220f801403031a841d5204002d120f2032510035403002c0242c20120042420107111840240344031003900f4000d00030050352040b4803040007040342034a80380b180b001580102c5590b41e2050031081c80300f88416400780e890040d184420074402d00310488c040d80d200b00105084e0107000022230382500b250303480902000700c91303030314600140020781c0e800d0161007441c00c440c00c9800c201c806141004880b40b40484514507140c1c072000141c0f164842120006d07082900e55449540390b4906a52400314004070042d076401603800c1010303100f100c2e80180a203031300960b52401c25281315018007d0356402c174000644075510074000310002d410403056602200d8454054641000d98003400719030842c01c1035241c21582d410105007400354250402d110101d444c690f1600c5100b504003d102c2504884c0f407500e8215a0048081648684184038011800c42281041c5421090320303102044001c1d1a5091719918058000d212104500d0315040300340808a4103601d5441d500b01054000964 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 950628318 1250 950627068 950627087
    0x10c1101050706020a050705011b0c0206180405090307060c08043915110303010506160804210b07020d080703020c100c02030a17010b0d0e011b02010c0f02011b 70
    0x341004400c12001002840c40c0c00500f614465039110140c60f078000b03107081829910304000c0c0715150340b0542d140c0c8108551240109580c26010750b00c07141c0d505018040030411044c440d4416801070304190502c03207140780010042117200d0140004020459405c00100c503140800d9502520320059101c4441404501c1001044094a521050700c402c0d8040d81c810ba091941c5584444961700040c4c0d007030108181c00184440640600314082c0d0314560500c800583c3d24081d82128028820035040d01204000b04141120050110301083c260321326600d206000d02a10303480000c070755800403540440c59603800010072915180e510380715003030141d0311404110001d400503801c800c801c6c801d451103500140b42038421810541c0c8554091992207100c0c07800074040c1521001c83e54410410b4000421850301810b090320300d504070008001c1241030703004c0100ca01405a03000120100311050304000011601580280d00881040c0c0b5080ca207080600c40580c2201c1d5406041e429044d000c05c080c003942445000b214 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 950629568 1250 950628318 950628353
    0x303022802150c0a0b07020601090608280f060f09020a05030309100e0a03140312070c0c0303030b3105010803090904060507090312020f10020a1d01050910080a0e0309010c 75
    0x1319141001c50300c0702c4642c0d910a6070840701581020006014082e4070b03025134809860844008c100c51203d488910710b000039404011116140301e403041d10200320034a00724543d2180c1124050101d0650761050000412070f10300700b00d00c40d800c080c02c0080e1908000c4155111450014108445a080480700344d69490040162a9000c110390902000103a00071110b5103520441500840d140e0350076081d4020035180180a21050001e02c40500e400507000c04403400540c3d0b407500d40415118601030206600803408001201c00001000200c8007208011040070300510591005000303c4c2d980791007150705ca01c15140100d0700300c9842c40006012480356003100350080628540fa1204079aa920380e030700c4000b4400d400300010380214070202e41e200e104010842406583d0308085180c1800000c0103032441c0c9203003410410104503403200750000c0e8062030540c0d940e94805032145800084210004101d013008442070304440c0c0c645000601e0440340001600c844080c103031116242901d00303840d241c0c40040411020b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 950630818 1250 950629568 950629573
    0x5100906170613091a18122b090b01050a0f09090c0308130305010c0e060d0e0a140c01020709020309030306011116170609061009020d02070803010303022802150c 71
    0x1000c8000d6652290203140c500030981d100c10040405032a4517075250103000ca03952075506490317082000d0008240d60f8400c22424000c503644000c2600c00d40140c40600e050103170b0ba500d800c0c041c04180ea9240e00300701c403c203100d0b424103015a0780350020005800c40502891840d502101000d01123071a180e8403558406001c1c0380c0c45c0c0f840300d56030356500e20698400300c1c1e69801e0160410040003005001d0080314080840c1d8188911034100d03030700200d881d038010001900240340c4c54989010781c0400c1446200c6c0ca843c0c008184a03c17503441903020f655250004640f05005204507200090316100321300c00d0b0703809100300030007941c515103401d001118010b00621000c1c0c1726000302c4a410550040302c40d10080240b4030007510b070400e0b051026085040440042c00320581d60004010030000703e400140520039510440c400580b50300c1e180a0682c028000d01720001c043d5500080003000b0705800040c1c0511001d0300c2c0d0360201c030105014602c03d000000618000350030500030b115012890807904080d01500129004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 950632068 1250 950630818 950630839
    0x23a03050415180803030405030d0203070315241110020705031b0105180307020108010608150406080610150c0f060219030501060e0d05060c070c0e10051009061706 72
    0x1d0300c00c41e10b42c03a0780d0308008103051140c1d60650141c1200240000c120500c0503504614054403411780301d11800845d8074190341d0001c00108028001e81c03005502848044c0d441807401c0c0c56036210030200c07440c88020005a9018441a0090351003900c2c00200304a00401602d190a104034858029401c81007046455000c02e1246a0f00080c0055000e403071141d148002043d1410020b60040c00c2c03142448116050760400c1201b178000d40d030000c112904490061502d06144e03901c0e4084400b11801c0c00c0030095109040080020301c00e4400941103001d00c030b070039111045583d80e801d50f947c001c50380b215034280402e002c96031840c0441d10390384000740c807036009040141c40d04002000810040482c41d04040c0480c0d0b0b542d0060040c0c030ba00651100c00c502e000d403150303054a48151030b900c1d51004000c1401a01030000101d03e410031036104642e00007007684094266003420b20555015008032140142d5014100c140b40d014880c0b44111841012034509403240c0000303140d10041020680ca00130b1206400034110300c0d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 950633318 1250 950632068 950632079
    0x60d1a060720010806090f1902180a0f06120f0906060e19051b07081306080f060118050405150312180f100c0c1a07023a030504 56
    0xd0003020034034450145420581c0b050500c0c100100703028140030f410420000e00301300b10b42d00e50841894021300c5000301d0b01a90b5680c0d01103022640c3c40e00000310f54544c0041860b0b0002c04000c4014500700e40c08640700e4101d14ac0360442007080c9003443c4205800201500d2415030740c0744081d4030650036000d0340800410000300548450042d500b02d0750115107200c080301300304803400e42001810400d01007868018049400e040074a0003150586c071003100d0501c18002441800c0080c0701c01160032000c402641e004011b9581c527006005000d0443d0304014900000e80082c80355072084404507440d6a280c001d40300000e0a14040c000201001041080c0c0d2511300c02c074646407564108030f2100340a13040319210b070342c0d900600c6401d0a000e210301d0300c65009510b5000c09107840d40d903c1741b14019000072071404c0b0b842c0c02100e05000084000d0f640c06400154000194640542d46210080c00c02a000303442400303641043e094502407140300031000002030102080c046441000d007246401045020f443d10a0401e600d99 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 950634568 1250 950633318 950633329
    0x180308061c0f030801061808031c090204110405090108012903150a0c1b08041a0f120f0f0403090e13050f0d140a05070f150f0c020615060d1a 62
    0x8900030f80200c0c1107032004022080d84440c184104803420700c0c01d500550720700a0300baa0f8078042c80340680501441d6501810402500b07a10429a0302d400400502c24504001070f44400303030b1300034000c2d24001d1007004004280d85105000d03c0244815400d030705a4001d41c0c10481164600311842402c0d498000d0b96a8100c00318180690180141580803000490003c0f50350040e100c14480f84403903591210044030b12010890100a507000c5400110762036070507880070701001e44e4501c52142c5d00c1c0003a04d80412a4040d901c004840d451141a05118400c1a1385541803000c80244089500a0004031180424020400220001340d0000c002c154980320181e5130b1340e5244d0405086400d12840c50380001c1d1550640e41d808920703d0100303c1c2e0b04010742e1400b409050024090301c2050340140050b42c0c0c150800302040151006d005007520080401c0210b8088254000040d0650500080052054901050740040c0d0a1500000b0360001011189880324440400001d080500004c9004880c80210300c503141d241ea = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 950635818 1250 950634568 950634593
    0x270602070204060e04150c0e0114030601020111040e0a0f090b180115030f0b0c040b040b09060405120321070e1302090d0c03030306090203100501031e0c05040306180308061c 76
    0xd0560b506c0e0340b0304600c001c404440c40707120b0030380400864481000660740c001e568650740104041003196a5550031006034058010301c5a02280c00c840010001860040000c07041e02485060800703020303518181c500c1c201510f840305806801202148003040607404a140d0a1300e50402030000482c41320b09440003003842824a600541c0c543c0e1211078510200311240c00001ea201d03d80368149401e0034100805e19010b1b002f14001ca0f024060000390801082d0b640754107403801418011702c8001d5100719408429101d0700300700c8105000790025900030421802901401303100340c6440c0c0ea00c03181644e0709400c000800540b140d5a0f4030803a4204050317802a2034440c60101164000c0d41c00303255240c03442c03900400722100ca41c4034210705441401808004900110750b2401c51b8003d00e0003090034800d01c40d011809507070030760310620b00c00c0c03501c0310b5000d0341904100a00f0449004078070070048826281208020301c020401d00800142400c40050344528200400c4000c0d032440b060343d905604455039134117640e00304 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 950637068 1250 950635818 950635823
    0x509030703020c06250c0e04030e041506140a1b05060108060f011a0c160e060406120c090216050f0105040b060415051210090c0603270602070204060e04 67
    0x40061031409041d010010ba00c20400252425840e081511840d40f000180c050a588440c802c800810b00c03c2c001c03035284d054098100c1d000003c00341e040030b141c062b102000c203100f028050f60400303808420108000b5160310844400741c42c1e044013504a01c807000c41662100701001c040c4a00c452200c04040b80081002c401035214000801055040400c0d0707034031f001b6005000c008100755030310051041c0c103a003800c80101e04481c140142c1d1140c420b003030760b1804e00c5000c280560b0814094040002d003c1030f4000000d00841e019a42048a15241d0b9419080121002c0025140c036084080800c4003604a0b0700805000003903400b03104081585698807820205400054201a0344800a10040c408a400f0040c1c02c01c00448041103100385030306460341c1408142c82014802c581c1c0360200b4540e1078091080d0014100c140c0001c01000c0c440d841c0408d629001800303032400003460185041c6500c44c4000b2010481e0b04100c1110841c003c1640c0d07180065400344100300e820503141d00000030120b0417000c00320300552 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 950638318 1250 950637068 950637073
    0x30b0a0f0807031e120f17240402070c0e060607021005040f12020102100e190b1f0e0a020d02070206030403031410051e03011508060108010609020405060412150509 72
    0x1450f5003040079031080321304450760720402c94403050400101aa52011100c8005081209840d03c5440054071411256154801001301c0802000002c070ba8041d24003000f06a001c000881800e1818140003c1f401381c010000c0100720110818071401010241866000e40700030051440d10415038081402c078154861000085180400d0a222411030002c500f40507082140810524140d80e0b00001e42e03c40c0030305a04904d0300c2c0e480049114902c010300280d000f4030b40d0402c540c0c20404880c80c0c095030038142142d8036404180042d00c0200700705400428001101c181a101000b66110004190300030f5101030743c0d80714001d40c200034080060b00d130704001c1c51141d40070361800100108005213101078400300504a01ca842c1d11188140080d07a141054403c0c02030303119014454107000f40010074010814418110884009030200084440d00082c845040c2e170050b400920401c1d43c1c484200b4203a000e5402110f610807001d000610080303480d40c020142c807074010340b1015013042408c4c91003001c8440c1a90449141d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 950639568 1250 950638318 950638333
    0x60c0804120b0708011202090f0a0912111b010f110106030506070f020d2307051f0e0d09060f030f2a0e03061302060f07080a020102070b090a0b07030b0a0f08 69
    0x2550402c081500401d40901c1031450402a54001405c401001327110540c501c0020020401a81790350340541c4c22954400d9054128000d140c402400794586240803d48610440c06050040c607030113564500f681c801a141d481c10803540c004141c40405108a103400c1d25035a1b5000000840d900f041920b004e8a81515141c080c2c40303540700024103010780091a10180900d040c0360380200e85102418480303007d000f02c1074540b00c422501c1c21a04005101682c05448070034004040e8000d0b1503584102035600e200030442c0c81d6903202d0782040d01e4442082c820017012441e01414800f5950003038202e6104011442e00c00942490f800c82c0c0500080440d00c8407251601003003020031002c40e00030301c4503400d40740c049004040300e241202181041307408501f00240101000b1603a1151082841c0070782d10025806200d641c0c03221014803009000b074010741d01c165520070244000c507211400100b140580f0942121a0fa08540e4640307101b85c0c007a010b0000c90540110ba003400018581c1d0300f0104c0712000d01440350140851 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 950640818 1250 950639568 950639581
    0x110d1a060117150603070c020315071803050604060b060405030a230705060f130b0f0309010b0906010c0f0534060201050c0a12140c0a0801090213060c0804120b 70
    0x74642c500c0407241c1098403050081d0302c034000200004048089078000d68035a0303810401c88100b180090029058410300c0d062610700038400812502c01da0b040e41d54014040740f4a4000c1d10780901900c4060f04580010001c030380481e003580c028104030b0304040d007040d02d41552030b00400e14001d420007050700c0740c4410104440300d038191501c600000c400c1d000000e0104e60300782000203469104203040c0d01d03080d1200088003180080c0d40c00031a0010b01c0402c202603102e00010701c84918551003101c09442c1c0b54a4031840c1403d03441c11011650040d041a940c1c40d050501c3d640d0b40826186420390262100c0c070841c1c11910840c250b9211514154400301c84e0b41d981208600c501f514071580c10f40183c015a41031404000600d00034005407600c00529140c04004150f43d0740d4402e0090001c003d02c41a0a1041e1041150b1b40441c3c10081c1404189a48e9070900c0d43c0e80c60a62004034010041c1920119401800401c8140d100390340384070589d4000c03000b00d0720b06651040e0706040540c1c420380032103203030742c1e80c8003080360 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 950642068 1250 950640818 950640827
    0x20c0c1c0b04020d0803041a06034306050315010903030903020418200906150a080c040509011d090d1d040f020a030e0f1603060c0309050a03050910030204030b0103110d1a0601 77
    0x40214064006220fa0b2f415840c182640c80d140f0070119202d1041000b5007441c901c2e41c2e00006054811500d62500170f20385420000301503a1045400c6000c0c4448645403004ca5407064426600306ca4260b0b407070940d400e05560802c000340c0060300600140502041000000c1880310aa08100700004048481824004001d00c4140e0f180204854072400b600d081c0c40c81d03500c0c80303c0101c030a1411117161600d01503071030442000d0303540200c3d0403c42e0800e580c240046141829800d866000070707505207141e4410398441e443e1503510210307078840000040302169603210075401c1155064902400820200740301051441080c200d03001980b5640010381c80d81e0004151600c10b105101681b42460094002510404000c2ca04010a40300052032299902004509240b00354041443359a01070251681c1010500b00244107400100c0c40a10a640c0032296118280c0a0305c00c03201265800b80b000c41003070b880c50311000b042c40c1500d03080e10f8104507480340d2640050601010240094009150710400c0c3c10820001003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 950643318 1250 950642068 950642071
    0x1031b03050709270c0c05010507091d10030206090f030102370c110d050d09090b0f03070b1e030f040c0e0402240c070603020c0c1c0b04020d0803041a 66
    0x2084004c0e100c40c500c09a40182c8054a19000060010503844010441190385d511450f6018004e03510340b106200c100781c0d00c00026821100a6030b1080a140308100c1c07a40052007050b90030801850315100200014181400600041c100040c00440e0315803000d40070a003a40e010401c2d8081e060030460004000030441002c00c06841c03d600400e02c00301c10400006485030010040c00340100001c00a264140d03551100da0000300d0744d000003030740c060101d076800152502d00c19000f10701659003092003a5107181400c0b81c3c0c40701400d8005000b42406850070222003515403000090147d81c02042d8100700794085040001c6d0301502000306040000d00e040d0070600000b241c19002a18803591003014403000da980c0146c1c05142108000d00d03002e803240c07031900c81c40c424480c07452003141c20f0040ca040007840c0c54041d4040e16444485e082a100d00c0300c1c228040001e110300c0c2c00000b1240c4a810404500860280701090354070030f10141c0304e48030718400361300d80d10b1107604101d4046506a100c074201c140120689112907 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 950644568 1250 950643318 950643329
    0x130302160f051804020918070504091202010e01051e180304030f050f060f0406020d0f0e010b0301110906040b0a0c020402070f020112050105061b0c04020711011107081b01031b03050709 81
    0x40c03c880c1083e50000e0300352003000d4050300c2c5031000c02c802980150700a0003034400405c00104208001d5456181c10040ca4a5185210002d0f501e090700405908906004031391040000100b49500740d11914031041c075029002d8404240351500980748031315500100300800c041c50041034004030741d000da40352080c0340002c7d81c0003807022500f09406000340409100045504103034000d1000d84c0701c4002103408801400c29107640c1001d10b04005403e480c03441e0650011106c01810f0307009101804159848144910500000b03d400c0801000200072068610010704000c01141c03418a07405940354002a0603604060300698040e0030b500741c02e90440da00115200c0040903000000d000661404000038014081d00c04002005580311146060507001400288144280180219142c502c40e041c80000c1d030003150642404102d440c062940c5024ac001004022590420010b2408a45c4100c0708004010400441814161107035054681d43c9050301e403403111030180e980d001641d450644d100601c48545507004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 950645818 1250 950644568 950644609
    0x1d0d050703021f12111c050117010203060f040b011419092103030c120906020301081515041503060e011b03060602030301030b07050c2a0f0306130302160f05 69
    0x200103041e130018503103455842d00e54000540704c100ca091000d01485184811343c25244e44010b1030003082200d42c8040d040e0345580f05144c002c00c0c8000c001900303d1000382c41d584d0303000341c5000d04140e1070b242982160803007240601d00203402c5030000360080b20301d800400e80c54195a005000c0340c081650300080c000c0050294400c403c040d9000c44951110b640d001d242c002d410951508944404913018000b038a40d80c00106e10200805030b0396007010802504203000b40c2a20713001c0c040c43c05102418540340301d800b500181d0b0040300c03007001d0101044020681046020743d40402071400001081c598412100074003d420008100ca0401e40da0042c02810300c80342200606103002001e00640ea4000140c0b4113595010207841d20781d4680103000d652901404000c08482d11030201021001c5810248011500d80704032264090b690140c1c04202c001d0883e100816050f501000c0000c640031460b0000499184c000d0058688450605180c5940c00c6025040200060f101701c6040026041c09003c001d16044880301 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 950647068 1250 950645818 950645869
    0x80c01050f160e2812060c05090603010909020d150203070e0102071503020313050703080a03200703030504110a0914090615011d0a0e0103140106151d0d05070302 71
    0x80160800c24440f0790b4034019240d2841c8507250851503d0181c05480a01914841413640d902c20210740d0800c5080c00c40e02c040c03c006415401902440a945180d0401414035003141e0a00d00324000501c0d031810700341d078001e003184030b480c1c08110700c0d004198010100c9503000d65686403442d400340c001d04200e6241811035100120802c490300c04070b0300c050b03110140c0303160141e5030b505c62107100ca10444912001900c140900e0300f00100304002c01008080012250320148044091401c05c1d181d10421140d081c030049a0800070b50001a20940c0200c1c0c0c170602c034a2311f05080780c0d42d20000c981e8014035500819401a0340c2c0361300505041d44c1c0f02e40c0e90b602084c264000d04040c0342c00200c9503800300500001c2c030b05100600010a40c43c1d009458420503203c006810001010f0b030303d003a03a4004500078841511078512260034021412010301a8405071027400c1d20700c04009580101c12600c001034040c01400750303403100080031403a5641505401c00d0902800003007800605500401440c900403400e51a800c048650 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 950648318 1250 950647068 950647111
    0x705030105100e090a0b0d021801031703010501120908120c0409060905150906011709010b10020f15060a0504020d02040602010c0906090e0a0621060b030d081f03080c01050f 76
    0x104013a9101c1c0c256036022508480c1000840c016450b0900020750101c1e4a241003103141035507001040c103c0e4020120707008114190852183d6034031080c0110b90005910004040040d041c60f009448850301ca126000e20742414020b20b4840b402d000c0c1e9403400301003800034082003040c407180518000740c0f0140300e04210900f820000e80e40c8891050319901d024011071400580d03140e0143c040c0c101c0016000141c8940b900d013a005c864024440c20700300f1442010b5211103140590700c00251004101001001001800140540011940d42c000d2074182d115429880205c1c06494078005020202003005000d604d0b0790a185000c0d09503000981480c0401c08100320410203590f00000c06001c07900800f88014840e1030f000d4408000d4405604150b00c0881c03000c100c5030407120107086502c401805031408010300412001015220204178103807900041d649004907140040400b4003408001360281050242c5070380341da52480a42054070343c07210b142d5440701001414040c0082181d4404a40d441c1ea0905c1500b61 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 950649568 1250 950648318 950648329
    0x5060301060f0e0606250501050c04030b180f0d0207090605062511120a15020c0c06090a1205070311040c0c060207052a030f0309220f050705030105100e 67
    0x240304a00f248442000816881d888000881e18810b0700107040000600c07010040128031594082e089449602e004001042042d01405513020b80e0b80c4025542100e8861403040c0079840c2c0c2001d01250b450050710140c1c1d43d012020001200624041e4026002c11898400d11408594603640b1080c0900802c002c0050b205030042414203136294801080700741e64800d0b0902519242101c00c0d1940c200d00041d86402503400e00189500e01144201c4117010703091605040d070b0060b405210002234040c1d10000d0100411b24164028204030100035001e01c00d081d6132501c14022804031210b09403110f41200b2400c3c0b007480100c0800500c0400152024840103c0904008020110700c040c0500301c0c1d40c3c007050300020010140070100700301d0714007560b446040d034001c80091342c203608a00080344a0310a80448030308499001c019222034000c0100711007044580320040c400403e04101f9a102c5041e91010b00461030300705849000d01458184d6586622581010144452008074105200c184041410141ea0990301d4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 950650818 1250 950649568 950649599
    0x4060c0507090b0d030c030201090f1110020c01080a0c05190305100906050901050409021216090e0a0f030e010c080c1e1914070503030304060b0321040b1e0316030506030106 76
    0x141b4140300000e030141401c0b030040454100080600d0070040300700090001d0b81258800d011000c44a1085850030813006980d40d003401c00307000e40459004000030b41201080c6c3c1c800b0301c600007181012850809140e072020540c9800c2442c1d440803907a540300b8040004200d0408030060071504804001d103506201c0001c200c09030521030349106503142c00c0100c0441d1140b1400c0003061010f28200c500d50140086585141105401641060782c640782021164441c000b608803011a080b0002c402c00c8801614211380c1200c00004441c11300148a00140002d201500101010036400c4080d083c02150810030000c08080651458503070762091880c1d54083e103605509013510f0380d00c249070070595a4800c034524141030207030340a56071600010003088144101e50f000398010316011408d0ba4903540d02c522030100070788034411003c1d0100c20284011b03c60b000300d2600410320181040707410100001c03498030700e40359a0300881d43da41b840c245d44881c211410b0381502810780c001c58110002d22001d410700e841500160304 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 950652068 1250 950650818 950650823
    0x506120403080603071206150815011514030f06061215210c1002010b0402040902130b0c03040b0309161404051513020d020c070b03190903050f1e04060c0507090b0d 72
    0x155410108d00c4510005054002460143c0580302451840c1a03071256070f10307013481404c0d0340e000103d1058901d18400c0c0000c000d40a035158941d070031074076042403a01c0030b071070000c020079000401041031031940703280b400d0014450903040a1044108890318184990380c121102c9082e50004032403038201d00f400000c5011003110340c00750741c940311402d5400400c901400000c41c030300e50410b1000401151040d8542c0050040c6542e500c07030380c080303240e031051001950300c20341e201580e0a820a10050050000c0c3c0380007103800039000b00450711001c40300c4c440900e2000565100110031640c440c0043e8180c10180186640091406503003e1034a000790042410941441504e071585035000070907a14507001030303054450504052013241c008030744600742078445030300a44407840201c01b074400400c00c141d4507000745404d5943c9940c0381420f0040c000f512407502c2d00000b20390000d104601b40001c9c000040000648000d007040d544c1c050140740c0608101c1c1c1080419000314400034140078180c015911503036900c409407503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 950653318 1250 950652068 950652071
    0xf0c020d030903020405011811180108101d0412080f06010f0c0804060906090803070201090314030706091209091407140d090303021c090201081b040506120403080603071206 76
    0x12401e160072030700c030003290308020340c0031746800004104450300304031103080c540d0824801c0001000d5441c0f400070900600c1064500c510241118a146500c200e24054101d10f00369034007540300740c030343e502450a45200140200c6030048c0380100014000e10031149031420030305d030601280031700708004811100640141100e040c00608252054541e228020800c03680350040c04013611603456a20091941603540704000002d8501100400c07004008801c0b5414158141c5800003120710303550310f844d807034044585da141c25400300b0b11000001c194540100b4240520406036403040035201d0101030400c01e066088080039520f0104000320f0a2007882d540741d0003065600713000304401308450f5641124426449840360035810211003200700354164000c2e00d80000c40c080480b00d40080c0c1003d080c222402c0000103400200d4030804503080182c03004200360055044032007640340503103900100b100e6510080030301108124420420061691101c40e9603003204044000d803031b92510b406992421407000b40800740019 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 950654568 1250 950653318 950653339
    0x150c150718030c0e01240e0d05190b160c060f15080303160305090c15040b13030b130206070b060301090209070c1104110d0e0703080c06090d0f0c02 65
    0x4038040c207030a901c0441031840000126441c2c1c604148021600d20803d00e40c1014400040790800c01100c204400342c07120516000d483d44d034000c04640c00031444c1d410540164600022001280e024451414844502d100102c0002024605185107a100404213410341c68078039540c210f0300e54010300111a403034000401081c149046040e440082c14541260444950900b00c0020340660120185100324500c0c8032401034030a11440640580d076084074051840d41003680044600c1c640b050198440b40301526880707007420380300e05110803d40c0c0140800c01d10441c000c00c0c10800c0020b266200c3e90b01c00702804101c001c400301d40d03011942e0340c0180d95004020164403c00101e07107403002d5100c101d10720340007461241582000c001c080c1880e44d203083c0c03c2c0c42a0300f45803d0703a2540d0a103801000c61000211040e00d18002c007040c4554020072002c8400d10740d5000e0000008041a100300240581d58814000340030070f0701304400d10600d0900b10140346803d01800c0c961034101103410006076000c0f55010b480c2103054 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 950655818 1250 950654568 950654581
    0xd0806040b0415230135010909110409050601051201090501050712053103050405060408010b030f070b09090604090f230304030507031106130e06150c15 67
    0x2400007600c0e4160450310340010160218442c407018011500380703490000c0101460701c9014451071000b281103010074129032408642603851301c0007140203041030100640f11138540c40e0021794a071080c0d00c150410390322407044200f44203074680c01c1e00f0094422074007000002080e0f0b4a6507100d02c8144a400e21070065800d8056a8400079003144401552100003000385147c0f840001e80700103425415901c1051a1a0004051b10501a00b021110b034440c0c0102a4003004c4d40c1c40601c0742c00c1c0204040301001400d202c0068691190009000506111000800c0c99050f40080c940703040a07556411840368480c134020410b03d00c0b04404c4030148242030743d07c03d1003503984402180203040641e100800d200c448030100e01c1801542034190b000c03d101c000c00003095140b041503a950360b01448c0005011508881c3c000c0000800305040d00400d07180c080c1480741000b040c45221031740a542503000351280c105c1a0104145460280040c2e00c1070f6801010480c140310740c104102d0703640c540d010038800c8410044c4010602 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 950657068 1250 950655818 950655821
    0x1506230a140c0d0806062b020d060b09030f030412020d020418031d01052712070b0d0612031d0109050d14060603030703020a030c021f020c01020d110d080604 69
    0x80c24601588600d540e440100c24030b9640e041404440c50000e4021004503c0301d1070850100c1e04440001c005408081c01c2541c0000440d00720600080c1d0a01d84c00c10030070107003440a0151500528081c410540c5a554440c241401d01019203868101c1d90801c0000348150003100b407041910540640300801500c0c1c00303102040060680c0b4807400c1c0705105140a4a040550203494500f10450042203032075032803040401990316000346900c04042030300030200b000030800700c9900d00c100010020075091307003401c404041c02d0510718160440391480c5400560b24825458900408d401045402d00350034070700c626524003e106210001d116000344d140c40c80003030b0309030303100f58010b00203031000610082140c5813a02d0901c5064403c08141c0703107a4000c00b80007551034640071040e500c005030107401800e41159196003c445507071707403486d04036807190341c400f82020141004040e1030048047d035001404000803001c0003a14200c5800c1c0e200781005402e02004084110101c1c20200010a50a007092113481d828000780 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 950658318 1250 950657068 950657087
    0xb07050714010209030705010f12050910020c0a0302010606080f190b0901080a0b0109062601111207030b1906030c0e06130608070c08070b090115091506230a 69
    0x1071800c0744008004401d075070103600418031150304400321131340680d81c0c00041d220388241d02d00c80004514109071b071a0b509035868104c640d101844000b603550504003004094126085000007603104e07030044e1501410160244a110098145410602c000345803419140819205c001c2c43d409000200140f402c115407070030f400c070308440f2600405440866850340340c01c80e0f90b11000c010035142c005489000003444119403280030182c0720b03400e407950a4840d19041d204000c0844140c62101c07503503101d03943e4450b0030140c4041c0610401141d82c9640d5418241d6004003941c2c0503240c003500c00da1402004444000303000c00c1040460385141030200b042140004145e902e068001c107084d81241d0006050a202e05030100340d20203680e059105c42c0d0443e10303050b804035140885450700600c6860700708048408101c00c400d2040e8895501d81c004075015010312107200c41d213006a84140387c00c640311a0a81a0300200b882014050700311403604c00750707080b200101d18842d8002c0c032142c02150348000850b4500d0522640204 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 950659568 1250 950658318 950658323
    0x150f0901050a11150601030c050c0304060311070c03030309020406060f0c060b0d0f0c06090f030302030d09241a060c070e060d02030a080d0501090b180a0b031b040c0801030f0b070507 80
    0x640d428281525001c444c61300c2180c003140041d00e000701d1000143e000b03205642c12442c41200860400d0304001054004203801e5288481750074090140400259001c01c219028510a640228600c00b10344107020a0b5a80f0b43c01141c10b10000f500310100095108500051050300001c01181c80c00d030920206140b005c1f85c48028264030b00004905040c00a840408030807511aa030790582c2050341c440c1c10942c6900140401001604204040e4210b80d0707003031f0092103d20f4084c000c0c517031041c1309104040c1c100709032844001c0317115601d8142400000c1c21280440199400c20b40c0c00915180c0c81c0c032225515004c4902034100c400028101180458031618085045154041d0898482c60094142a0b07515048844012050781c2400300100700c03003417940100c05200b100580822034005819008201703600000309401036455965051a5032541d0402404550303020415002d180c800340e100c1800140c0e1004a00d19013408505401000001d42031100710710394507005801440310361900c4000b21040c0c40f484002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 950660818 1250 950659568 950659573
    0x804080c1e07050406050105030118110406120608030901090b070f02040212040b060a0b07031d0402360a0b0d11180111010519090f08040305010b150f0901050a11 71
    0x1105041c44198215a1500448508807010240e803501000295061070180c60300180080c00100306c0c410b0074141703d40000030424404207c940080e1040f5441e60451b90090700017070301d841d10940d0b503070b4400c4c4107440183c640d280203549000c805100203407903184e440c401c600f42e202e0000361407003c2c08961107580b407403603a00900956a60000c584d41500030750054406940b41010f44010680307910780f50760481c003140c500308425402c00d00c1544040e0f0b60341041c401c450460102003000800f02e580d551008042c50219402d400300400140f0801125000e00350f01030f144492012001c9070820b503180440c440c01c40ba10395200d90350b10010310400c1c402614125168090150020960810b041c00744043c81c10441005e903210300c0314110705c4101500385c490585014540a8003c100407485481c0d540007060f40d40e02a1a012840c91615610480c0302d51143d4030640c1d05ea50f40780300f0b844892810810095003081188101401c20308440704140b01071040005c3c45041c40f800090900e03000f4000c010340400c14a06006 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 950662068 1250 950660818 950660833
    0x90207051510031a2d2437080a0f02010c1b080c0618090c0f0403050a03080a02092404080a1a130512090103060503010c020d0224040212120d060501020c0a030f030804080c 75
    0x5a505141c41d0002203001c80c204842040305c1f030890020074050442e014100245103444894503841c40e201c1c0204401d90402010385040070209502d0301d12801410050411a042140f40641c428100200c01002e184642c80c01c0044990207030503500f02c1d11310010100d601017080e49810300d18181782d1280556601c00e001f800303c3d000061000200e400c1805600039160800d8a07960401c0e000100c3c4281c80c3d90a40c84900300c03585401250986000311009008204d94070b00d860340794070310f00e4981601c1d45401c598269504441100543d4094805a0001040d814a41030314605980d82c944455001c0e02541030000e02245078907183c2e2107604842d0003040b01900800c10710104820007512059001c0d00310313025200398000d42200c40840c986141c011141041218071030740b80c07a401c1041100009491014521a1400c0511250f003c8030040441c15900c4000140803445c18002a040840c00000944a0a05400d08001294002160f087c074268903241084941d920ba00e4100a91b018207038081106214942 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 950663318 1250 950662068 950662099
    0x10512031303080d050f01320429150a0302032701020705010b120d1b0b10030c0501020111040b0a110609030702040501090207051510031a2d24 63
    0x20050141e40d000c0c901c240301c20751b24444001003012080c41080940840c07044455a03182d076080501d6413803207403108000b2800a1040000e415640b030655102411010541c0b503a40350904000c4110b00b071407041c0c0745076151400d074640005050003181c03500e0341459000400200d03800d051b6a03910ba0802842c0e03506a41100da01c600c800d0007900140d0085425610740f100d103401038901030300300c403050300020303401003111050800702100ca03019040219004046112613650006009404042c800d004000802d800b1500c1c509240394030142a92001e4156490020350341c41c0003550204480545c0c0003042030236a90440d409040758800300740300038814030b40686014021040c03c04001404414003c40e4240205d9032076a444904904c01d0240c0100150302c201a04094040b4585030540c3c819000c2c1e060160465603900e5805102e4840003078285840800c038108004010602c00030110705800744804c440d004c03080c3e25402c1d500000a801c0302403e140c0c0440c61840c903550f2841940c12480e01a01d02c0f04c6481c60304 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 950664568 1250 950663318 950663333
    0x150301063506060f09071e110f011e0b0105070b01092a17270601060201060b09090105010365090c0c1c140313020f040b030a0b090f15010512031303 65
    0x4103240c42300c03802281030100c0c0064050049080c0301707120400c42e003824089034401400a1035a030794954140101804a00045004c0403010390080c200702c5800f2500607000d080711441e0307003c07041c81e00d0f45070640890441503095001096030741444c00c1c1143c4d40f4054841100c480840d16403440d4062111040203685101440080344260490380650000e024442d01c42e04100114010b0070485338012040600420466110b50030100700711081082800d0b10b4540c20100140701c01c80c0c0e90b40d0840c018070f141c012540f030b010072080341910540c800c4071428518020f1240000c090803881c202c28440c00410021486498040c42150429401c0004031004003204903100d034929402440f40c02c002c684422001030b128403d01085a02c14284a00d049201039000d90070030020031029010a500503aa170049202d00351820405800014040d108140c2c080c41e01c0d034144d40c502403003800342001079040100340611300c40c0c04403215810b540c0102c511584170299002102e203035000d400201c0d03888229581001041c4110f0307 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 950665818 1250 950664568 950664587
    0x1503070216320d200310090f020f01050903030d051006081e0903070212032205060d0b0f0405132009150301063506060f09071e 56
    0x440407a0340c0030b40c0e401d90900c014600307014184400d180c000c0b01154146204600e524082c00007400c60102d10389603207880e00d035081800b900e1941e020002d245054146810070022010180b148010b00c0701050035030380e02c10140c103500d000a000b0079018440402c26030096040e903000e0407028084a0701d940300303540784c440a0321041e1100c00900760044e00118a0038415503450780b045403550040145051560000d6150b20070040c10b0110501003405602d005030b6075103940b6490118040020750b10707400c0c000e2484008440b80c4074041081c1c010030301c00b040b040e00e0786401c1e209110303404880001c040e800070001c100381c10500d00740f80b40c0c05440d0504010301961413064482106000f8000007403454003001030924800740c0141c6595006c201d00c0005600c8940e000e9181c1d82402014001040059031201000701d940d040344140c1500401030250003401950005480c109030f0310035401401a4103100d8041000030103c066014001c80713002000641a134014900c1041c6051280f101c001c6414620300024000f000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 950667068 1250 950665818 950665843
    0x50604140c070308090a08030f040809060403080d0506100e0f1906030606120e0c2e0305070210090809060c120c1e010b03120c01150902070b0606041208030615030702 73
    0x1444008121714000000c0d2090344554001b00c0c0c0c91964a400c10304040c22140240b08603942201005001d80c07a0716000701403c001c5214040498903030b075190b10f540065820040031140201c1808078280c51156020190088004082d941156541503e0f00800d04681007103e4204804800e00070005940d58580e124100701c0c3c8407a0745900302410998002810368a403407080d031390345500c0340c400c130002c0380703814802c15801004280518211520703101400364002021102000800d541d1420003800ca901408085000b0211a208111043c0c2071f0b40c07104060b00030303030341e8144c022139003c1120200c6510411014844c1070302d1240e6607840fa2001c8204941e5400100200400c102150640304c182041c14054880d4404000f0050112100540380d18500c80c5c2100410380c240390340340c8018049002c3d0424036072000d011611005039030b450301424101450000503117803d0003071204101c20030054010a140d02206c3d50710031003041e0749840e200b001a42860320100d44140241c0008280644642c001540c1d010018 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 950668318 1250 950667068 950667077
    0xe010608160e012124050708041707081c110412060f02120417090a03050601050306010b19030c030204031a0f011502100506180103030206040605101503050604140c0703 74
    0xa03200c410f0480265400c3c4040b0b20380d0213542c03100400107900310040009050301c2035a01c400d00c3d6005622142900d10030340d03280c00401d801d0700500041c0800782404840d5920060f0314a49170001e0307640c4600a40c450100a409451010010028045403d0700021041c4142240c42615261505107141c000d40b90701a0403101d440c40c0c400f48070030000e40c600070303180303046050844a0402d65658131210b2800b91040882d0b19400700801810986985d00c90100c00618050030080074a5810007060510380803040c0c1042d040da500c02c2c0000d454610440445510440350b070314010030345025540b0268040c3c012031700001c1051756811912100c0f60703030111090f841007003455140d40143e41e1302d07403025004c16000808080141c014070106c091415094010903000750000e00340d0481100c0b01410f5541c1800c080e041140160040070a00c028807056000d940d412052400850640358501450015030780515880c0c1014143c82c0c90002c5d039656030b1035008440e01f41c0801103a05491501c010a4420f0781c0c03100e6821400b08 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 950669568 1250 950668318 950668321
    0x50c070b10321e0d02120709060e0c030f06131b0f0e010e01080112111c0c0e0106020c1318050304090606031808030415090c050a05030604150e010608160e 68
    0x528181000f40602c0c552404401d4021200406000c0c29500c881c07800d90b0000c6454903c1c62500314104580c02c020180724170005001800c0c1030200c030282c4800703400134460400500600c81c08d0015903031103540100007110007000e210407004003034000c4c00d50808400b1006049070180c91340703181c00c169038036400041c41e6142501c0c60194001500c6906264035040d00245080006200c003404d480d41c41e803003440c0140600b411003110f850004d00a10a001c46465140c2d520b034181d03108006031209a00c0241c030305440021515230400100075521380301401514407030013008041040a807241d50028603031001c0d5240c040e00b00d81c40b070f0070a11341e030b40d0041c441c01035000d14003880014200d00c244134080c4107401000d2000031f590179079250750030340b41c1020f071043d41d05410301d81000c40180e0880c402c0c000414861110003009034500802c01420a4447e03001c94025001302c0308020000b4a484074940381a000190001501030040c110035006111507000522641306444071603404011400c131020803600d4039100304a0780e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 950670818 1250 950669568 950669669
    0x3090609120d090608130b07030c1202040f061103030705120705040815040510061a07020121091a0f0619050a0303020303100801110f0913140415050c070b10 69
    0x54006d51000340c40c050410000c2000e1783d00c40d8202102700171b500d1030101c42e04038080581d10102c1c0d00c15840040680300c22401040540d40003205070040b080a40f018608518184001409078403c0c111310138140782001c000034007403078022010303600541507890403100c21824104462002c0081641c09682d503104946009210510702c0c010542900c1e0025581c5080320f400309040041900304c60022414826070003040f02210241c910b0982c1d060303403120384c00302d00f6540905000c00203004408165050014280800c08501010004503030485e00c10341d1040480940c0815011400610b5000b1035400400d1581c00014517a002026501921021126a5820b90b81f10105800c86007902c00b0480d0010042c041d0040c00b04600d0090002210090701c4c0341c14418030b041036041114414401c610703038880d0650612090004d10038410314440030188040005003814443d200351070080d0f410040c1900c40781b10009401d980c41c2d4800740000c000c4c201090075800180d0345411110405018a10080b241c40c80780601c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 950672068 1250 950670818 950670841
    0x603300f1e2205030d0c021807020a061811090613112116050c070f090204080609070e01140409050a0b0702210403060b19090218010504050303090609120d090608 71
    0x120f500c010f008010440d803003501a294022000c41c207a0344411040b04c840c401c681500e020354843c00c51907000d40704040f07152a0200407555070b40102c204400d10b4681000001c0c2c02c0d80c0c440031080804441d103000a640340000a140750303040c030b5a002041403c2540400c002c0f80d030f81010b48000607070301e8500c550302c440d030342800c801594040b100b580708280240030345442c49004078010042d400100c02940e54060300c88000d09012038096111100141e400641041004002c0c40b500b6000041c500c064420145801007800200c0c006008842458200c440e41c1800c42d0f6480c1d2040b0207140d4031009840c0102410304040003404400c483c5000940281c0391805041c0c1d4680020f46104015920003505060440c0c0f030b00801000708020305a0012403440c0040a0207441060240013480d4940003d80d03101111980a4040c41c9600681d038107015080c0018400f982e03000c01a9141c1c01c2c03055030515203e82c8103400140c00048041b10010303450252000305000c15901414407002ea5906440d018526143c07082d2208 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 950673318 1250 950672068 950672137
    0x9150225110f0307080106030c090f1e0c090306110301090c05030108190204110c1b0609010509041a0a080304090c05070521040506120603300f1e 64
    0x1011159401c07614045031401c80b01801c10244064200c400c0075854400003404c40703e07190401d0340c0394104002c00b04403540300c84c00382c1401d9a10341902400920300e001712203068031442c5e52440200a44a800c101d00b006d2080f04c0e40310056030041028405a00c031a42c191100d68028040d0380c04007800c045542410300e0040044904a610700d00040c1840c0f00c000210005034540c950080340c0c400d460304400071000301e1030700c003a03c1d007150040003618440c0e0f452000c5c00703450304803170110b103010b030a0510002d0416a0043c00ba40e40243c1c0684012401c1505040340302d4866011032543e07540221341003000300d000540040613200341c80c0c00c000d0030806540000d100b6101e9004588005099620407402030070041603003c0c00041100c80d2050f001d06060320344000a24a811203415210f840d608182000b680b441c0400c650b04450318804801480c0340c8404810b4006d4009a0564265140001540111040c01901100c0000c10002d0b051500310248a0340c0c1c403034651040d10031885d84d080c900010010f4001c88050034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 950674568 1250 950673318 950673323
    0xb0301090305120a18051c020613060218060a020a060f06030209040f0c05120c010305160f050307180f14010306260c090a0c110a0314030a09150225 65
    0x100d0409040724108255203d00914184030a902c500e8440801000700d4212404948220050301c141403c007030305000f2002c2149601c07400c55000d942808840c01404039006a16904560007685c0c501100e01301c3c980056274040d500c2d401600025102e1102c0b039001c103030000715900ca0981403040e8221100b1802c00e440c0c0c50f000203988000804007240c0090408400c420070035109c0c03440c0b0020240e4403800220b460500828055a40e0081d6411164039030f41845903951040505101c0d407000001c0c05002408250103003e01818040c0000104900c10f001e0500358924506500d901ca020741d4881101c64180325141c8241380c001c40921400d07001d1903009001d070a003030b2079084e005198052400f02c03c0214a8040c8029807509000d03600c0080e040780c03110301d1042c0c440c02010300e011074942c014420051132035203028038105003900a00005c80003c3c8d0b020070032800e0070340060500ba4076034603500d220b0001081e070f603540109807140b01c80f500103008605070060200960000240407240c003210112500040e40080300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 950675818 1250 950674568 950674577
    0x8150f070f0c0204090204110316210c091701020d1b0f030b0f130203060f06031012170703031505010201020901140706060806090109020f1f081f0e04060b03010903 72
    0x14881c400c0c1c400d41d0840d00c01d900082c40401d100c0c405401217000c6400000451100c8400002040071400350005109401001d620305402e480055100c0f258184051040140c003c40d210980c21201034802c0d10034070090480d605249240300c0711202500d000b076008100383c1d40c986080241c151295006604200052125a100e60f03101500c4c001c0b04800401301000b40d00c5e0701459000c418001d903154042c01201f008007540b40140d4900300002001209a0f00b0b816241c4038402c00c00030001340003054200007080342c1040000a1110490b45040070481c0d41d0740401400e41c980204202090607030542000300c14210500c04c00c0c1d00d45441c5c1e4012401e0384980c40005d0701107a006514a099400060024010b581c0140c0c40021420307200c0100600301141500c0101182c0e440e04140000c2d40362245014256039011a800910403104c1d0306900c07a100c580020356401c1c040120001405280d0704200300300c401d40d0304540d000610780c0703641040341f901d20280e806640007468010b42d850a824140310f140082e40d0913444 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 950677068 1250 950675818 950675837
    0x20703082206050706061433130e0f040818130c080a06060806210111121006030203130803040f06050109090510061a07150501230406030c0519080708150f07 69
    0x43c8c3c1031080d640ca83c030005c201c641024003507c0f03000001d02649c1e5480b04614001d81d00d00031042410100107021070820860079014400099411012260850300e03100c00900340386280b400040c403404007000404241c9060422146c00a40d100c0070342c0748034807407205c810442552a200b048a16034802c641e16900a210718240f10000c00c580c654800000e4a5400045903602c80c461031002d864006880c1400380325011030a01c111200d110306500d0240140d49021411131410b10007020500000c0000580424400000728040c84001d001074040c940d08108240010b503036915064004001402c400e032143e001d13140912034044218001c2c00c0071181868a408074040702e410344030207241e0054100302c8060700c1d2b194020030011850301442d03000705560345000726070350541180c4100c0d4060780e20356544100d2425100740300003004940781030b040d2041503c00345a00b080000d0a61000600b9070003510041c40380750f10028145500059000c4e946519000c0f400e05a1610800e104004209890702004580c0307100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 950678318 1250 950677068 950677099
    0x60603070e120304060306060f260a14010b0c0c010804110f01050c0601030c0f080307171305061801110601060903030503040327060e0d030207030822060507060614 72
    0x100552407400300100324482070203824803642d2441c1d00c40d51218001c0380d12081c1c01c00c45030790050000c070f00f52252424000b4600302d4910402038012004490b42c0b24081601020510003c0141d001c141811072101e402a81940c55240d0943d081d082403219280340d1007a1070120149500c1500c650b0b00a41d4449810ba140518500c00c000f500c501c00ca52142c1001010300c03450100d420104040307030082d4000d0250004143c00c01c001404040e03016040142070f50300401410300051010405520742d45005c110031078888090402404130b1041c264460fa600010101d28650061104011100707580f40907201d0301160448141c440b0384481e000d200e404042840c0c4a03040021030b01aa0003181c0c42442031070948880c85c1742c26611440516140d4580c10220b803410300034001990800d6681200c076508640c4030300114100c1d54002d54900c45400300074807448001c228201c0048080000900320540c024010510a032214030041c02c5030400001130b101181003031000115500005d040e10580940506404494844907 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 950679568 1250 950678318 950678327
    0x30106141327080901020d0908100b03030936010b03070302180402030112031727070305030a020d090b13030308060f0a06050a11030c19050c060d0e011406060307 71
    0x11400c00356101a2225640458242d550350842c080d01c41d91683c0d4451110400080c908180c20024109109412000703009004000460000c859440d84010a01e03840e244046030440c014000c0198014202482e00c0c0949050b202d000b0008040002951851000003c40c0540c0200284102140001d0400200d0b00c450721130340003031140f04d0072900510040c54801020034101c3e4402d0b409000c020541821340001c265000422809041d00c030070070045142441c0080341c281000f2080b03540e01d24224209008c1440c0002e220f03240003180c101040d80d849034681311001e51504044000c50000506400c80410001140802e6503590f0750984c8110124034110b503015106034a0150042d13038000348603c9046a9641c802490380064040ca80c0c42c0b60f01e48103450300250820100c00c061401c160002d2200f064181000a00d4400e000e0002204400441c814103000d404c2c490f0700c0746a00c2d040500041d040d1303050302c065081003410b820a103008002c003108250741401580000c2e03402c2944944100b01150801d44107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 950680818 1250 950679568 950679581
    0xc030b0c0f030f0106020f0114180f030c0601050102060a2a11010c1d0402070f24050a1e0212191512020405010e0f01050904060212090c0301061413 65
    0x1000c802850480c00c1860444280c00440745404100600c40050041c551b05005402c1810782036170080c45070608440c0d90014844000788006041e4042c1e003030103148054100200001c403408042070340e5841c440780c00c1054a42c00309001c0c441c058895140482d403081094400c0d420000c000d00e8104942200740c400c0e034000c69604d10740500c200a550380d43c00305503003000c0c851142400e40d00d88410908412100c00740307030300e08602030b101441a0f105020440c0442c0d00000b0318020554404448a12280c817415039441d0700baa091030084074280b0303100422042c1e01c600c2d03000c14040c4010034279011080e4422007121081e40301d5941c0001c81200d40b80c010500c1550010350101c40784440080100310b0340c481c030002c20600103040c1d001d2924800e186c20042e055040501c1880e0140011a0020070b10b4a0000c09034400c0c80d2042c41403a0043d2480c0001a00b032040e15410307969082d401907610700141c201002c110b5511708110b595503120b946400800902c42420740700050103c2000360900340a244c405901d080103221 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 950682068 1250 950680818 950680831
    0xa0b0d0203070324081e06040b0402121603020306061f080901021b010f1103010f03080c033022061e0c09030507050303041d060d1e060f090c030b 64
    0x320b402c2e13000011400710390782d0325042c0322602600d03440c2407500070201d00d00740d0342140394809410310b044003249030f80780810b40940c07107500410503881b10b859a00c0401c03005191036802e10254002c42c6103c1100603c00885402103a0088044403070b25107642e0100425003200c2113031a1180d034201842007034201c1c008d80d40140e00c00700ea040010306005c5412594107403020030340310002e413603591000341c00440360591240018800c6407007911411507062040d0800c840d501c40c00080d00020020a071440088420002c485000900d80c40401d10002c905030090351071000d0403143c02d010910b5a0003da502d94040300c110030351049603103049551240030f84039040185100c007040d01c40440151002403002c0b0b01030040040220903541d60305000751542c2402c6003090100e402451007900300b0030040106000550b04035403404008107240c2c2c034a0301da142c00607842c082010402000703400840c41213541d00c0105400f200e00c05005140a002610b1500d481e030080710788103c1e0050070f012a03003c081c4041340122051a51000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 950683318 1250 950682068 950682071
    0x30c1403012d090c090812090112020d1112150102120d330906080c040f0b04060627030f0605100e040507060306080309130e03040e1305010b0a0b0d02030703 69
    0x36040002c00304092415000321022980300c01c00751001e030380d00c13508800040c1039038006040340407843e1150030b1176031050661050400040d507800c0607070901c2950480c6e0750201400400c100e03040f100c0f0311026113a0004001c3d699002e00e510009541c40a84403000e18030040d0580c06400031400410f510182e98101c441d01e00c0380c7d0b41d61280100000b400c0d010026583d10170448000801a19010342400503115540090200d6400c007003040110707440024445034000340c11680400c0907601018040f00034612032144580c01802c240000034416001104451849005044070310401161003082802a00c01c0c48000e02c1ca10105800c50007191050340100d806c61070b20070360a02c285a40b0450001240d9041ea82521560081c0ca02003160a030144186e900a01c80d620146080c6100b5000082484003014044103070340d500c6101d00c50003c1c10501c100d801030800750810b110941400c554210155100000072240e40d8604100700c82945082801581180c21940749645480c01c01940070020b90405444581810b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 950684568 1250 950683318 950683379
    0x103120516121115011502070305060105040b042301050a05060f070602030c040312020f15011401031e020a050405031b0303030406020d0b120f06010b040f03080903150c030403030c140301 82
    0x2543c043c0031849400e4502d0241896950500440300c890f44a281c030700303800307650103035500b000022404910103044800403500003444c41e07240310224014241c2c0d08482c680e41c1550382c1c92040300d2805003000c18141ca41c162852047d103915002803007a00e1058403100300c0070f00030900417600010025001164400820030070035044c1607407640c070f120014000740006009600000c01c5400b12403003c0110004041c8001c03240b0945516050a2440720901d1000e0349040640381c80c096005150100e8002940400c3c80344d003150345142c6114000c0203604a4010541f103400350f8407540e44860101a036055086070010301452554460380d656000a51009200311649600c0e00c44054055450308459102e000810003d0043c00c80d810520a0034044141c20007440940c2c10700c402e01080700c6111000d0300782ca9001c40ba050b03443c01c501d40000c0c501074480c15110f08950f99502008211041c22001c1c40c065803180d20180140c24040b502a00d00c02510003004140d0003050004015118a1075010090100745810b400101d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 950685818 1250 950684568 950684597
    0x1d06031b0703210203011508130c080c010e0607020603061c0c0e040b0906190e1603081b031c02030a0e0109030305070e06030c0d2c06010312051612 65
    0x125001141e0640108460160010940035107070b680b080115101d55046181d90b04104c80d55407018420300031103003004210b000041c8131140a4101d0606d660b0030a0102500343c0da00e001d21030b5034500910020740001c4465080f21040d00344042960305c5558000d041310f045960b070505010b040a0061808130f46500307000700d1b4002041404034401c0c003600c04a20300c40068505424103015118025009503460780c800c008010030317424540091805d60b030840c10041480103100500529240240c0c01c4046510205580041041008402807100010780c4800c3e112204005619a460b402030301c80c10a00b030500c03041580465501a401968464105c1d400001c5080901c2581c0d03084410035041180400c1d6540240540c03d500030440b044040c0c0f044405a00e1403803e00000640d034000e0101d072075425600c1d0654201d400c881c50011180c8007515071407604010078100c80d1140d0b100001e102c141d40c5208035144160030244180102ca10104c05001c186e03402c00700d2a582d0b003003402240c07940c410800c500324182941 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 950687068 1250 950685818 950685871
    0x318070e07081b030603070306051e0c580903170a061a030925140a1412011e0603060f09021c0f080706050702010c1d0603 54
    0x14207010340e079003989460010395500c4100d03001c52190007030706024002c04c006941d00080c41030589502c1100810390307490f955085920320220203144040c980c810410058248003400181c01d060038030100411510400d2200d0b003904600482110984c0c221401194080c0c4210b03d0718180d06a450b600c080300c43c514000c020004603400c01108900007070000e2000003840c030428607004d410080786d03031003000024680114803120307842031441d140300c011012000412040c0140a1481d40501e00a0903942080a203504000080701034069640007c0540d20003500d0390400390003690542e42031040e00d04c410100b2074208030a86a5540384070b00c49640b01d40b103024400d141000c0c145110040d12034040b44160031440c202040e11440c0540400181c6092429000f617502c0c0c81c021041c0c000a0746802c1c3c14907a943c10841d21580d08840050001c45001440030200210342e40054030445099008010300b40864034119021380400384d0141181c00f901d4851640c0e441e14000843c3c1042c03100c0002d00c809201a54030300d9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 950688318 1250 950687068 950687071
    0xc0807210f0b01020706030c0507110a03141f06030b07210f020706061415030a0e0102131d0106021b06070c0b070c0609050307060c0311010603050f19080318070e 71
    0x1c5040d5201d50004066503010015030340582040d0405002c90488018001d145000d45d440c003400d200c0e10140c10300a16100c0880050103990024000c09908005c13248481c1c0c1c50b03140c0d00403215011540852549142440c4c0301354001c2e260320800c10880768036542c03404c8455000d00008403101e60b07000d004140740c803d260310428086d608054005078554020341002c01c210350300c0d0f5000c10854055130f45144400c6d9a006000780200c801e902070640c6903102d51032004001c0480e05034144003503100091405a0241c0c0990503c111881d0406840c5c207801c030b149018680710400e105003005a8030030f152030300d034182c051030001c07246810240c80341e07052120719100d06000e04480e81c00314100a000054002c14051103444001c0a46050700f001d940e80c0c3d14001c0800d40e5100c40d441170000f00800300c900c22042511070664280300c0c00002001b030100c243c690501c5030700ea80308413000902c01e106d54040045c40c05140c1c032038a150180c00540e4141181d43e00c2c0205580b800340030304000681d0080312808030b104007840d00110b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 950689568 1250 950688318 950688341
    0x10509030f0619060806040212191b081c030c1422061d0607020d02090a3305190b030c1818040f0201030b0301020705010b03060a0c080721 61
    0xc120904200660f00c240c1c07000c41000c038900a040200901624400185c000d821075410340d0600d056200345a5113a0415a2000d000300d46603411090308414800448269404145a210301008403540da4441075a42c41b41030003083e00409503003500e114154042c1e80480002003040c00e140211640c5418040741503441900d4044e01c460a241103481e07000001c221440c05040349060102042d00c00300c20309110180010303466440303843c0c0061084c0454858040c40d81096a0240000010b400d02000080c090030314445208c12083c0741c40361011a08014010103000e41311020101b4030290b0909050000c041e860740003110403210890300c005001a1150021841100480400c5407604401c50101d82140c243d400c525102e080c60070039001514603004003d0790829030115104000003010f1006801070030000300a540d055101103064020300006420254000c07004400b900c5003036964001d0b80089410700b452210004d005000051141b60184003094844180e14106030690300b014104102901e440c62039a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 950690818 1250 950689568 950689573
    0x2060406050919061e0e07030f05010f0912030507140723030f0703030608060103080f0c1015030b0a14070f120218120604030e0d1703090303011d090d030506010509030f 74
    0x16178085010f9a55a01c00305603441e00c280400d51440074401d5907040c20740070250524416441990400c030003544980140240c42c001030000d607080b400d01c801451848008180401e007000006101148a908040c40c0003001410a40c02d00310203845504448801340d51b1903141c44010032142500c8502000502020040103a0103503540d1814907000342580e074140d0095440350b02000042c0005010390007594850310740c0d0b9406640314120750000720310380280b420400030040e2420744403645408a203101a015070740250805112600e0b0742c1c0c1c00702c0c229224000c09030307c0210004045003415100b000d140c2e40040072840c0121144194100c1e0308202c1e84840c3c110f082c840d52054103102c883c01e005200411218141c0f0161240c0d140c40e8401400065000e07450300d05c9042000c2000f81000b2a0340f125445071400300901e0703500d0740b4003c07400710340c0c070744c070030f00a070015603401041c141d100c1078a1a0b0220f214090030f0f80a80f00940c0802810340103001c014208505000040c050002c841d00c0800c10002c556012000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 950692068 1250 950690818 950690831
    0x210c03090a030c321002010b12010509010c0203030415020a170a14160c030e031608030c0f0715080709090f090b070e090c030a20071a06010206040605091906 69
    0x20541c1000743e10000d261038030102c02444078030009030080305012072006032424814405d600404038018400040304507070140d0107040c2a00c5407401580443e2040518800070420810400c800343e030749000c205d5000302070b07099100d5880920007550300a4540b060550507c42c140311004401d9a81540c000c0714110000ea58036400c6550f00c00004001039040800000d040d4201c0c624654010100040303120040c05105591748120007a860401c01102c8151072100f0901c286503c81801940701d901c400b000c0104c038480c0389035100b0f4855000c40c400044860221280c0d6080e101d0080c1615104002080d1905128180000084145850141d01418540b0200028540707801d4a0480607107400a01050100540c6103d95882c90b01c0d4401c1e680c0c0c200c0102842d40361aa0380d4651668050303e030f4016060704544001860034a03100e90b10001d44034052051a12140042001d6406a5807541c00c0f110300d401607200750b01082c0400c0f800d03840682c004604809440031000d0488070049055000d0808590440e41d400303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 950693318 1250 950692068 950692079
    0x30807230d021216111f02071505031905060a0308161b1d041b15090506071a0402010c170a0315062007120b070809210c03090a030c 58
    0x20241185078015103a082200c00640c00b48501c0d1284c50003442102241c840191603610803c91011112641700c0c15402c21240f020003d4442515110fa03217801148081c0341010503000c0c030182c903c108411581d2600c01381c00c0e100100c0c00341601424481d04241d030301030080301041c00b5400415401a05903806d101586662030043c0310000103040c203900204c0e501800344610f0304070034424140803000000b0b4044c03c7d180c0c0e040c980564000180d803880d28001964cc00904221a20082c00c0410a25258404466616000d00a2611034010010420308041a0005030644035400c06508036006152a100d40030042c3e0315400301d00d54040003100002c1c4041089840960716004007208410003040100810b4904100a04120101c60508680d80120a8031069840040040d60024002e80307200c00411240c904000700700000a40300030f000280c4503c000752420000281d002c1069003400342c00d0010020070451509940c10242d04070031780d4002041456a2641c85419110255014032443d00701d843c03400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 950694568 1250 950693318 950693323
    0xe060105033c010e0a0c020705040c0302130306060e090a020604030b1906170f010b090604021c02030a020301050f06070c06050d0e01050f16090602030a140d02180f19030807230d02 79
    0x20181c01c4d005c0c0c149941e0390001c1d94041048000c80c0e03803e540c081400710102009a0190007080e0450b1050b00c128000003080c0301c0d003600644101c0d00300d01076088454652188160301c8100c9200040c0d086101000200005410f19440315409100701c8111880311403d420400140c032607030b610049001c8904026001400002e1101d1b082d000d0861008200c180086c102203440d0341c6000344460b20455021034038890481494110300d02800c084181103589140c000b00d40e1009400a00505d80a24080c03180b178103c60402000f1103006c1900107448002d150700d041800c0700c06500c004850380f030083d01c2d1496049a0031007401a2800340703800001d038040e2841d00251081002401440401c100a10541c04000d06500401122554089403511162410403001302d03030340620131040481481c9100250381480320030000708a10014200b00c0318030b100078115904001c52008682000f01801040680420010740040010040c81f4410311600301c440208801d00e656190000512400c10741010400c5207005605 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 950695818 1250 950694568 950694571
    0x302060c0a02070b0a030b100203030f151c060b060403050f0c0303191107031e0213020414040506040b04110403030909150504180503180306010e060105033c010e 71
    0x44501814140d071220025501c8200d4401c10b20086400140465164420f420072085100085d00000340c01c01c035500001c1d0350b0350044800c000c580c1100004615a180c4003846240c494000501280b01600035503c0404c0b180350111003220400d546170444112600c5100c0039100450041d00980002e00c1c0702c3c26094140b152100041d4030070342040080d034030542c00001240390f02851911340042c94804481c0c01c40c4c43c1800320b800c007802d21380392041140e000540c01d02d040e8611500c2542e44c00340030514141ea80007640901d001c1c6022036a2030074100c802c1404c00e0390069070302c210020802b0a60341403590201d0b08568032455007100718800010140107154011039404020860700c40100301002c0041c1224441000e6030080c10b104070b88607008034000300070024034000c000703421405070b81d52001032520280f0400b100103542406800750030300009103101c11103501d910410068680500c0c61f0740c2c42985603000c1599540c40104c1196440ca0341112170f016500418403003000b558001843d504102c56a00031000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 950697068 1250 950695818 950695831
    0x606050301052215110a02010c0e062b05040804030209090604022b05101a030c030709020705030f030f06010905040c20030c010f0f0e032502011106070c030206 70
    0x10103091216501c100945405101c40e0072009a402c10302e6403410b603484c407040c03440c260070507030500000c204501124402040a40442d07002048a20205c140964003140b2102000354460804d01c55540f42840454100c00541428941403004190301102d540444800350380503a9580c001040920840c01d0005580d508502d8030310081c401d6103040e030700280c000140c4e003540c003a012070039048015150031481041e83c1c80d03c1e03028080d64450302d0840b407000b00500c1c1c80c540d180b042c0c240d8801420740909010420200d807407000b802600d1410b0801101c100658003088007111144410880500003081d400003440c09054068803540d010704007c00010001d401c95000345200324584042c03154030f960000119404014142c1d03485d031000c84003180b95401c501840300042119403c104c9807402c500c00c180e2054058920042c8200301500ea0515010b40d00d02851684094042c4c15100d1405000745003030889603030500c14075291645454480145052100c01d888072070124849108010805806100096201c1e4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 950698318 1250 950697068 950697071
    0xc0d1514010e180105010c0303110d152304270305280203090d020316080303180118061808161208070e01030207050f1c08070207030f1407170a0606050301 68
    0x40c0700180e400583c2006100b468140b1040101d0817003098000d4110b0202c00e0142c00c01141c5660300e99848101800342a4401d076138440c1180d601081d4030510f6522140000020011056003c030f00d04103000c000d0540340c0c0407000303030a9070483c005013110744130b8400f207007847c826521282c035145100a0903010ba10b002601d807018a80c0d02034290402a400001d40d00900002c584260b0381079094000b00741021444044850500030304a8003040c55000040114010300ca00400700f503600e0440b100303450132104007054010440304070320354203001300791180c1140b0070038054110100c1c504003440d5110196a80088849550021041a09030501c0080d16031010200f10506040c5002e1a0805c0010565035142e03000906041d80807c052080c00b20030800401c005000004580020700c08000000c2d0b51001010030800161a800002d51a5803001c501041100c0c4d20103100700d03154a032a80d607082204c03501e403001c48141c800c0381000109800045524418124854043c0c0584000c50500d02c09581d641d0300b105009a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 950699568 1250 950698318 950698339
    0x15030b0705121b09100e04020310050f0607020a0e0c0c0106060f1b0b0112060207080c0c1c0506040303240603020406111204030f050a0605151002150c0d1514010e 71
    0xf583d51004607032100c0811101d091200200d082c040e201e0391900110250440d00c0841040700b00e0295000d4801591411035030142c02c00f003c0010000c007441a0303c0e000303410014001d010007020600e80c00d01c0d90440000c000b9641041100301c64107084881c83d42c0320000040c5211401d40c950b40d0003008414144d0641c80c01c1c880102e03200d4540021451041c42000d81c0a04140e03494014014a641962a425804000380d0359600e034080d062a070707034400c070b03600e03107110320b2108840e0041311601e9401aa80b01b64004045c08290f81d0b41c3c1c400350004d2002d00d040b0074204030303a03140b0301c0305802c044881d20b0042d041d0364400685a509105004001104c903544640a5907c25200081390a41d21000e450841ea8424900100300317015203400c3d402c040c00a50014502800c00c424003095151401207944040400d950240d204082042c00b06e2f41c0d801d84803a0311030b80800101c0880c0082400030001c00000641c3c4901150120341c1b0f01111a200340c40b54007006d40d0f090001800c1d41e0940e4406400c90100c0030450300b102c0c1d40f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 950700818 1250 950699568 950699611
    0x9050103021911030d09050c12030406021b121e010f0b0108041502040b070c05090609010506030f06121e0105060906011e1418090105030d020307020415030b070512 72
    0x41052401030418491004020f1912090030800c07980c000031584014080500c0c503203000c5986134961030b12648548122100c0c540101000000d80d0204d44440d030050100c1014640101c0c940040300d40410307002070810f2801c4589107010000700e450741c520184641d54004900e903680782182c55029105220906100c08520720741e91082c52281c000e42c003d100d06500d5502c040d6004020f110b55448084c50f0900441d8000510840010600440e50203a0b00351425650310340801903071040901405034481070601c0899140d400302c0e01101d03800700028000410584910140c58544407407005d217509010004941040040402c0c01095002441510300045508203903001a01c802c8000c2c40052001c40e0144c1c84030551840303910f8612141d5044290350b592080e46d21148280216074048490040c680e08000040074200001c0141c405540c0380d010b1030418017540e0821000d003c0c00d41001104041d94103000c8040b0748000001e0307020b1280d58695503030b1808400070720018000300525003040710501c2e00060b9038 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 950702068 1250 950700818 950700847
    0xc01030e0c010e0316060f020c033408011109030c040506011709070506030a060603050702210c0c04050c0a02060f1e0c130303050301260304050405131e030905010302 73
    0x84003424240300c00c03d00e260801091504000303405030140c0300d042e00e00000b0b00603046a41440981c11075400d485801148601b81948e0744461300035240c65003940c912101800b983c100355510f5030a125090090841d40e00d145903425100241c0007a8254003000400c84043e01d402c2080021341d81d0192000e00c890701d401d80000c1c00c5603020740304000c2d010b0040c900056105c141401900c001c0c2c1002000240c9a0521100060090205008031408070f80b4240120307010314000282c64065030341402d074520007007401d012079038103540000c0712102e0783c0d2080310401086650365001e000c1c03003a429912005c0d00c40046090003813400c2c0340927002c0090a4071810900041c00055030243d143c40c19245034a66030340d11106003112040c4603100d009408444c90200120805a12800850484403d403c4105001c080c89120000c00c1e0103800002c0703030310342c4100b10411840c10540c202583c40640d03402407031404d402d240c94081c03500d0f10801c41032180c41c1ca0a02e00004250300300b98000e02520013882e045040852681d04d101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 950703318 1250 950702068 950702083
    0x5072d08060705072f120111181c030512010905100911040b0d2304030c1e1407090b0a12020f03120706090b01060521041b060305220506070c060b06040b0a020c01030e 73
    0x700f08076270314103545009480d88010540f130303020340150101280b0490f04000703040d0b80002c134420085100010001a01200501615024507801d62501a016240040c101c2c01002c0000b800b82c0310f1036040c00009200d1205c0300c06030820b00c0200d4408aa40500c403042000308450040850304560200014000400d611081c0d5040d02c0ba0300c05c4046002400151000ca0000c90341303540207181c00c0c02501c0c018080100840c02004030740000c0002e1002c1c0310500100f00d031012581c028a120104842075410240c43d018031140c0c0000d00207810382d00b03141c1180e0301001490f031115106440843d25020500c0800c1070000302d0600401b0300d0f14120b400c010217600c805a442c501c00c5101c180742c1c10854045000d010008600034442c00c2600000c0340110b035a884068041d040455518410b003d0220005540d158400390202c0c1c1c041d0700402a10b01a03590081c20742d110340c404c10081d21001c0d9220544500794603107000500140c030016929945031068000028078202c1075603440c50400d402d00100c80e0340c0b9100003d081 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 950704568 1250 950703318 950703337
    0x11401090e03190f0201050601030507020d052d070b0709120807030e13060603140c0301030311030903120c012405010f0c05072d08060705072f120111 66
    0x2041c000350851001c0c1c40c60107050030600d0800500c0d2001e01600ea000380d800b00070101960003d100d1503407581c0040d81250001c503200b0340036030421a450250103205000601400c205400c000b00400990780c0048080c040003a8001d8800c0c00000b1582d0900501e07100d230582c04002851301c40e44440c101029519a4441220000c14200c0003080c580f04060203040500c0581c0000ba000009004015207504081c080c82c0c4500008207107011114aa20750043c108107200301c1581c9e242c1d501c0e591840c3d4044a10a21b5220000a907000600c4004010340c1c081c040f1107400000200c44071f81b144070755000e50742100c50b802c1d5545071501c0c030140080b200704940010941100c400f4241740105284480081c1c94288202d080103080c1e010340280441c1e032248400400d4000c03486040103000700d0040701c8818dc18a0f950380118001ca520050016036042d21580c010624603120720200780706502c2c40a0f4005405280c1080c08441c50748031500000c2c18202102e8448610603048002d00040144000c2c0e21220700c01c4d91a00e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 950705818 1250 950704568 950704571
    0x70f060e03030918011502010e0c0f1f031a0108040c030b10050a0b030f070507050a060908040b0c0105180c01140904090b04060f0b040e1903090b0f03150301140109 72
    0x403224a9900303205944842401801c56049101141903d21030303540e09003c0d00c41445810342200b94868414819800402119801071030280d4801c0f040042c0d16120b020740c9a4403138901500c081c0150102000c0440e02c0c511a1804a001124881000b02d113490041c0c1107030402c41c441c1d04200118003442c0380300d42146d030000742100b19900d0307441d51f003210701880d0340120741c1141c0d1001c000542340c6560002184039580d4403055020700d4031004001c403040d10902d00050825030200035203602083c0c1a606c102003444c4a00466031034240e9400050074141c100d10300a50031750350368100b0000c0551680341c00140440040300602403000f40000041d0140c3c1a403841000d604e4404184c030322098682e684014080398101807240d189141c04d282c03100c080c250b05407030322411504052000301c0b181058041c030601a20701d60050109500444000d882940f00c41c1e0040d010803502c0c081c0010144408002000b030056031001d0301e0b0b520b00e0020803017100e0311102410640280c0c5800000b5044440d91000c940c1500c011440 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 950707068 1250 950705818 950705837
    0x4050105012d0908031b0d0302070201120f090f08070303111306080604180b04030306050604050d030c17192706051605030d0507170705030a090302160e0414070f06 72
    0x111041181c0303030001d003024440000d0b040d510841d0046e00307a0000e4080c40c1150324801124008070164007600d5402404680445503a005003440d40d0000b516403003405400080b0b4500c0e0b901c80d18403003040c0382c00c1510300d02d5000520105155140c010344290b100c525402c2803030440041e050101c1c44100c1c5c0329003400c2081250200d40300f80d840342c2010460042030005d42e0b51030101810712134100e0030181e800b01d0200e80b610b200041d40d81814420f55044440080038002d001015460548514903045001c03134104000c001610b1400d10307003030081d1081580d08203401030300003402e400142000c2400681030741e0010402c40014002101100c51200381c2d401481d00689034600c0c220b0b920f04c00f11043c0001002d5000c0400d401d10b2105465001c03601c544096550207907643c2c10240c00450107002a1060000143c04000042075000a034105020043c482d00c11101c41b6401001454101c03070b030340d4100040107812841808180524004140c05800000010300700300c900d81480f01c807200c40d26200b400c2c02d1082c4800b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 950708318 1250 950707068 950707157
    0x801030314070c15090617100603110912031305041406010e0a08010203160e04200a0e030f0607021c082a2803230405071a090405010501 60
    0x3e00c0318010071307800e1410b06070362002e07080c050f04c650f100d8050600051901800b0324546106840d80d18019641a0445180c0c2410200210f026000d40c1b00c000116200c01c01449046480d034102c14440c0f40100d602a507110b6110824540409042d81d005520490400070b8107032940d481d00b810f007134002d002403c10503e04088031011030301855007a13010152952020003003045940c951041c2030301034181030752100d1442c01c0b41020002200d040c0181805107001041c1c4e01071140a040c001000001e0083c100000800f2050303000900d80412060408035a1b0440e00601048540422601544509064110100302707440346005003008401004602000d10b944120720080d000c200110b81c46030518000242c0c2e4207008021402031001b000380c03100d0740302020308150340da26100c0d01c01c030440410710603550b2080c90301c0c1e002d800c4042d5001500a903a60302074000b0005501907100d680c9400c08070185002900c07082c01004000850341d050744420b050200b44a01404504044054030540d941700e08000311a905610 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 950709568 1250 950708318 950708333
    0x4201308060709030218041a0c0f0412111212340210031104090203040c08060906010311100f05160b090705090c0c0304051c0203010f1b080103031407 66
    0xd91003100d840c0a01c40c1405692540710380402c05480c000d460b82c04148294000c091110b0000710340c09804a0502d120412003c00c11820054001004842890038040da503070365180ca41c0d0059114100036001480e40c417040002403072482003900d4003100c03020740450012031215200c06a68000050780301c0c0028039400e0360404111405803041d01051901107003110703043c02c05801081500242e110302c03020300b400154203129001d08060b2924010885084c8ad24100d40d0340c0203508058012544d46845640203c6c190070b007000900d12940030400245815450340c2000ca00d80d80c000500140a0a001d040b01c0d2415030700203546001003030151402e40c0c3d0303803c148480e03a913584c1d2080e030300100314031048401d1104a031400a254002d40384100c4809419444064036001c141c03284801c9044150000d00c010880d030328002208d0700300c801e0050f69541c60381000c2d9000900b150049071000c0d00103590740c250240c04400340c03c00358980e00d10f6814484011f50440e100505881080904420756078000600c500801841 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 950710818 1250 950709568 950709607
    0xb0309010f020d0606030e01050c1602030307050d03141b0a0c0602071205190e1804080d0606030203070906110c2718190c0b07030509060d1a0420 64
    0x9030704007103403140340000700000501041e00c10f20000904040c1b6805040d0b8042c85018080e54070407001500d05100c880d69807000a10407041640e041c04140400800304005208107409042d6940d000600e14191380200c1c0c1c24400d01400800080e5007034000910b42d00c8170b1100300c030261301123400c1014003448140740c47d5010707104411300204007140402c2c1d080d10b5941c01901400002e411208200d48110031144129442c7c51040441544101c3c0c200c8482c002c1400c0143c2c150304035026002c82464044c0c1062440140e271616489100080c1d400403c12420550101200000e00894900b011280d545198100da40d0741200b80f0052155481c002034008502059104903840580262400c109180081c460201c1c01904640d40b4418040c80010189500f0f018541003000c5900c100b081c2861400c0000302030054102c1e400440c140030b000c005125246d540c1902501100c6040207011642d10034032080c0b040e24a000b62001070141e400d00850f04454592044007000ca000e00e03071265911800110f00c400d00201e031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 950712068 1250 950710818 950710841
    0x3130e0141030d1706181902090604060806032a01140d0e070315060302030d0503040203010b1e120d02190f0b01060507062313020d05030f1e040305070b030901 70
    0x108030340b03088042e40044000ca00c181801c4e1215101e82d40e620244086170104070b0309081080b0031000010000e0100c50035058505c135405000504000707004001c21455032254005c80c0c0031400000801495203020404007809c490010141305202c00b10340200a541c0c0b0f207402d009070611451024410985d82d55074295094000c100c9000d000701d2012000513603c50103140001d030b9203404190f07000101043c0b10301414081f00c1e030180003000211840c180495031070b0400b41081703915540318403c48405d0f83d180b06c0c00400070413440a074018522108010828000ca041d81801c03645d030840401e0480c19500407403402150000515280c44a96031440c050300400c1c42c1802c0105980c000c2d100203d1040e0344003002d4510103215500c1040585815440307080c0602c08044000b0000010301c5c0010410f641e07003103000600c1c43c80038141c01e018101c40d903a00c1d82990040c0d082c81800c0800850320180b005220340384900c14104000c407242c5014111346800d620b5030402c0c010201305100010110300001e0096200c42d14021 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 950713318 1250 950712068 950712073
    0x6101b14010606120b1c0b040c08060c1909051509030111030a051009060b0405010e46030519080c0102041d06010f090302040b03010b0303130e014103 66
    0xf034603084050a1402c1c0000c8000300c26180040d100002d05144520040c2c1182103217003509032a40340d0b03581c0f5900b417070024400c442d01003602c400000c2040082000c1405640050541500c4001101400a410f400304a0440c05c00c002094108225140c030791440e0b1881103008640740c1d41d041c1140102c5c2c05000a030440c1044100008104125540300b9407100c0d0140d00e004115105079640e46011809489860040700b0300300c201000300704180c0d030103040c50a00040014002101c071107040f035041108200010011154044000d040c10180da03058042441800035402d0a0300d619400d48d02c2d266680d0440140e0102071403050b00f000801d010601c4d05682da0512028001d554840c4c0361f41c0303c0000d0070740010b6510902c1c00190301040045d8062070444011607200d56401a0540c07640c1c080002034440b217251a40c0655803142261a11744050004090100741c1c03103070580c145450320121a50341d8030b0590000b07228140c02000c50348005580040345100118807110204800c1c0c800031466801c40b00401c0c010b9061 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 950714568 1250 950713318 950713331
    0x103020906032506080c04030b070305101815170303040f03030902030607020c0a0e06130c18060c212c0901060809010e0f0a030503090a1407090506101b1401 69
    0x8035083e241d0102034407456910f01015807521000c2600c2030040e0f000040c207040c1070344006620240b280d80001e40c081540c2801445040c3e803100d0310b140f40c03100c10030711085031500c495804034500d0005400a00400c169a02c0d001505e0708101c0c0244c0324040684001d0504204003091014544250440300c1084d800500381ca14a04003102c029645181100420f40644d2090740d00080045042e4002c0780720700030140581c2d580a401e84240002403044141000910021002d001440d015101081010301610b440d000100071280c14461100444892020348149000c1e800030030380da52101c0c2510150b50040c00c00c02a80c61418900412540d40910781b42d00600034000020f01071342c0c050300c0c541c00307031008030002c220200d40046070540720303100744402210542c060b002e8038000030f01c550011940300144101ba103201c0c0d40c080d80d4070fa0910360540b12189450340408018000080d241c410303250010002c8a81c0240d4080030440503203210207480c990007200c007050b000c840501c01040560140307524418000c0106 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 950715818 1250 950714568 950714623
    0x120305210702060106110c0f091b18030f01110f0f160b0601110f0304061809060b070201181802160b0a02041d04020934090617040b010302090603 64
    0x20f0700c80901c0303407500007102540b07a410500000f04042039800009009588140e07095070a001c90310f02c001d000000a903600f8401714111600c8507000d0401c0500d410340880d9540c42e000200752a001008008a10b5645403640301404001c82d2800c0b6400e100c40084942d407914890f000035076450064a0b815002039610004140421081d86411445981e090326410a200c010600300d6030340b00415036080134958410002404901e020303640407440080051101c4078020340340c0c01c0000984803180d100381d8801a0118050341150380160358a00c504081500b4080a180741984401c4041544d014650607554005100516500310b1100303664042c2e002403402807182004240d0400035440b501c02d00c0b22680e002118030307804140214845000310740050100c01d164441e860641c409000d0400ca021103640c503602c1000444c1003568810150354644d44810b9a02450114060000302c03c080c480c101440041040000050b410440c84c1d056a4044d2401c03c00c590b0381b240400d1030f112142c3c071074140c900380354841000b8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 950717068 1250 950715818 950715823
    0x1009240e102c0901091a04032703030f1b0f1b03030503060f0f1201050f070306080a030f1206030c140103090c03030c1a09030c0c0a120305210702 64
    0x165014021400d600baa60060030076000321000103900740780060041c1c038000403900ca20301c1d07402071402e0000190150081e42d440d02140b68401191040c0320001c1d04004c14540c208412950b00d09000304000184a0441c580c503107514040e01004061168150540401521a10040302c92001185858818000905004c4c0103054448821150010008511031110708200c1007202180d5042d02c0d01411030300d408041202d01031080d03904035001000f5440c0c90100c2d982c6c1c030044440d003045020000495040895099885007401003015040c1820500b00300b00c0110300050b43c1c03001542601e4642c42c4240e841c1021207804030b03030222040d03171181000408424070141742010405c68014441c400c5405500e400103405840d10003602030000c507150340b01040817038021108202c0d0203114103402c92103821500c03d03a86c1c4084060300e08060561011601a4400b40200070301c1c070400c0c0045800742281c0740780004415100665450003000c0003408542540e0b100c46142c042900c409c0302603020222480c0c00c020007503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 950718318 1250 950717068 950717071
    0x5040b1006020a1520370813020303160b07021203040201030905074a01120f0503030a0b120c03100209060c072c060a060302180301060e01060212031009240e 69
    0x50712402d01004030550040440d1411b0301031225030020b41d0740c01c54556001d0f00c10340c6000f404c5070860728808460a006075000d10080c1841058150303480e4004489050048603402d0003000300c41554004500303001485205015203502950910b00450f0501451409500705641d941c40400d40660b01402409541c9410300d460140c0700e0103800d52003088169006400c00480c0003018402c03042c021400510041003100c480c2402d043c041d89240c3c209081c0ca9031400d280d035200301e60707401c072141d0703145e0f5544101c1c5070500d180c5203544040303401000640c14180009403190b2842001764149a40003c1d07204141d1900b07001e5625031000b07402500d81d02c80c1d540460844a03107400661828030030110001d545060303912215a4050780c0d000c0c060408460400d0b105900035404440c1c04820101d043c0c1108001d55400d005207005042410550401540b40480103072504100e41c8a2101c00c0350148204481c18104524000c100d0780a5800401c40c620803080d40d0903c0d10812001d24440c0c2d082100202e9503006610340a1b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 950719424 1106 950718318 950718337
    0xa0c052514060a1e0207030f0e270403020d1407060f0207020913170702131d0d09141203161707050105040b1006020a1520 54
    0x152a02c40d0032299268002c0c0c40d091a1009401c90f13600c005241807100d10290300346071040c0d40c081c2450060b44005c0040103891201506203954020704180903440250103183e00001c1188a00c03100f1340103d40c02c4d80036102c6d5480b102045440b40303a002c8040d025042605040c19015510640030701840c250312075046409005c6880943d440b805030343d00640a03c807400d4100740c001c1c984101c80c104410b4060046180c11f0000c500580c90760040c020300d81b103500e0720009034030140361810f10448000c014185c04c01e1080030040320f007030b03904106510181e0f904901c29203a03410889041200009031444c00c007a10b500140507602100e40c0b02c21a0300f480c00d00c00c0c014216585041c07407103011143c10407101654269103580600090203882070245410000c0020400d100301d0620300c02a5984076100e50041c07644462901080784002542d006065000f1107024841d02400300d0580100d03160001800c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 950539568 950719424 := by
  have h0 := BRFrame.cov_init 950539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 950539568 ≤ n) (h2 : n < 950719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
