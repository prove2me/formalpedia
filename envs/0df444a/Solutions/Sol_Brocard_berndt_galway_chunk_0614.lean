-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0614
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:44:26.493262+00:00
-- url     : https://prove2.me/submissions/3d69e47c-743a-447f-8549-c2e174f5f2da

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 110251798 ≤ n < 110431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 110253048 1250 110251798 110251807
    0x6090b07150b0325051f02060a2004030804050f03150412121404030f08070e0f03030f04061809090b01140a0305030307030f0609090f0206030a0b040c0c0308060102071a 74
    0xf80c0b81080388001e140d9250f120070741002580008040304081600903503004021420036030803510702d4030740c08400209260380185036680d03079101c80c90f0080003603541803124a41c0e80640924014500400307000694096900e00c0c0c0c0d541e24040400840c403401e00c034000d00a41182c07504517001e1040c0904503a00c260456500d80c1721000a9400302c0d00c00f0101400646050714155402c4e10010145500320700c00c5110381c5640d082028800029244407600b220800b00003101c0c0c1d0724402e110b0034029054041440040c040700d081003859074424507070f13410a1700a60700103a8852403082001884133406070007459001c104011104a0382c0b6402ea82e49414060940b44c2c1034900704c003140301d89440d152000150b8100007030780d48a0820b0307500100136051f603844c2d504145040240115050070540705803460554000d202c3d560701e404580c280269034100620326025181d4400c4000030380d446501856840c3d0b4102c1d43c0c0c1c074101d80c04514011b40001400f034041411036010203420320002c07003100c0c00400b184203a910025100c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 110254298 1250 110253048 110253071
    0x181801030f230d05040504140f0a0903030209030706030c080109020703020c0d02060904060e0615040807050904080c01060806061203090907050c030d180b09120304111c050706090b0715 81
    0x1c0d00c2c464404084030344505a034600d080c580c48400741050302d00465044c440826100b070300c160703117080680300700e00e599140d8000b040000c03c040e440012080c0c40f9040160030007407080d0010307003000f459a00c607601080e02d685d00c640c015075102629601508180d1000c50a0441c0307510005d50f42d42c03c222046004031207a669000941d5218011b880c28207600820502440e51100c2144000b50000d030703440d5009a0384034084c0c03048403100344103840940740200002c00d83c140c0b038002000a42c0c10080c0058803610410130480105850a002d4500545004402484a401c00100707010b19180c0c1d441c95461141c2050003c09415582c1407030058016010b864410f484416084810703081d0b210380c102c0c2e0018a0700d4020401807020181041d040720754014503440c074895490914540d22a48800010009202c0c10000940043c404090141d8283c502800f00800b00c4031680008010014230b241c140d441c1e600405080200075804160b034000b422503005224104044c999079600680713000074812580c6a20313541030440 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 110255548 1250 110254298 110254343
    0x20a0803060d0c0801020309010b030106060f0509061614030324031509030d0c120b0a0e0c0f0403021503190b0a0603090813120311060402011d010903020303181801030f 74
    0x20701110701c0210344d603023000b83c0c00600811800005c5806942000030016116024003041c5045810548440e8600074901c000c02c049948031481c00320040e8280d003604400b181031512090340c0340504600944d90790520a511a2070160a03294040003000680304407881503c000c903000d00c4034004003012028944600341d82500f1806221070064041313140541c0000e240e030744190300122050241408102c10a001001d0018503403d40c0900d451418200c000708816082443c0280302080e10207818a040940704d80c00a40da5194040341c440e0103003000310501c80e03000b001c81c0404801c41c0315000c0c10800303d2001c00c0032070b00030a0f0600ca08001d00d5900c0311034005002e0080b0480c0c005e40602c010490301141c44002c9a11104104202a00081d002c40300a00e010310340018003d01407a016115121b0754060711400541c003a040c48100350400665850000040c5c0301040035191049007151004170710ba0b205010311400c0300442031403036000d580c0480104082804905a20101070f0402c000c0c2c40c00301101d020900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 110256798 1250 110255548 110255573
    0x210604231503030a0f09080604210903060501090c080f220203070504050115082a09120a060b100c08070b061f0306090b040203061305060103090807050102030a0c020a0803060d 77
    0xc1d090f000002d40b40c078495038884000301c0d8048194171aa508241c441c100e20342d5580003203900400007000c100c2410481c07141042d410810040702c1c40c01c8080d45450380c1e10741007502c03003e0340207800311a221001240c0320758000c0181d03540000001500302661402d165283c01561400284c2d800740d03001d07492581d041d91005e00000002d040b02410500c2196900c1121101808420454000049949010804c5100e0382d80a8400c0308a081152001940c0021100d810507405490301d640e2000d01019800d55961052000241c0d59009840000d000384802060010b50f125411003042040301245004000916900c01d0324552500302c503144a2036503412010450303200b0300c8460b425101035811440317403d00d641904240141d8801d05428010543c8103800d00081e80019503280b51300640708401c0d1450f50000c0d0707100036032200c0145000b2580d40d005803501083c41e0302c110001c0d50aa500041041445410b80c019a0112131484c8000d2505003ca0380b03c1108a00000e8802d501c5094001e145500b030200c0c120040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 110258048 1250 110256798 110256841
    0xa03080a11040b0c030c0111070507061202220503121201090207050a0209041101260a05091603080c06010f05011202030c0f030a021803070518190221060423 69
    0x9a642c4d0b40126819170f01d8120403a9a010b960812074046002d4861750180c5020760b0340306004001c0300e4245103040e1059004032008140140c5e0074019130b2126480f4101c40441a000c1700098002ca60400d4240b60801c2c1c04002050001c0781c08100c100034014a116441c2d04484d200d520045c1c8807aa1881c1150a00d02d20f52000f940c0426039100b40414005001140e030032001c003d0729030484c19021803003401c0c588690280c241503041042e00000d842114140c02103076000d440141910114030200c25004c102544503001030340c0d180d00202d5626021801082044c1c09845030075980005149010002005002c5400c2032440f1260040045a4803050400c192901540100d52842c2c4a2074046042402504110b5105002410354198041142004551102500e0b006407030004801c941d188005036001000d0860000100080101d200b559410710240445842c81d6489074103175811045250f5510002a00c8144994508240003e9200078100003080d9407400c030f041800c0d541d50341c0d107645181c95101e0010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 110259298 1250 110258048 110258069
    0x1c09140a080a151404020a050f01090e01060507050609010605060f07080c01020403060b181605130b03070507030f030507171e010807050a080a0807032709050106030501080a03080a1104 81
    0x1e4008000b0035035403d0000f80c45096042080788035003080520360b0b20050710080d4001e01d00800c01c2c00281080241d20310040d5040c140128401d5035020521441002640408001030000c203104003000401c1c003409802c100b03400d00074055a4103040c0040c200c2e00c034110308cc0c2e1020b00001184010001f4001c1981c410b80f15040c021500c071542c0e07040c080080c2c1311100340644100d400c0c1c590b081c20703030481c0703544980909032030541121018402002914150302440d010100c001c1e4482000580b2007500008500c100a2961166124010303803801902c00ca4680d05004241400c2ca810450346940c0552442000650680d4144458070351448a4058141420f03800c052405182d001103441c071800a80c844c202d91003512001d181568800d82a51a130b1910500140111000c2005130b004c6407080c2c121a00e00b80c01c800c00e60000c801b81d5030380c140c4c0c4221658064154980c4030001000401c0e0140703c2d8900400e00c0c0e00c0609864522550024036400008010320311359a0788020141c0d1039038607841942d010700200d080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 110260548 1250 110259298 110259313
    0x10e0712050114012d05030a1e020c010b01110c011409030a0f0203060705070f14070b0703030606080606070209070f031b080906060a1a091804030309051c09140a08 72
    0x5511102009903c60302d0b001c50884200d03600300c0040701e0108816443c0d01c3c42c1d6000701d0290400210380e1a403003d04101d16464661991070f00f4859800d441c906480c00211005946032a109190f41c04d40b01c1d2100e0850502200d9030885180120120304032003450001d00c1e0409c1c6480407a2002c15440c00b4064000d6007504c155004481002220784004150500860407100542c2d2015021103103803160103801015807440741070000014050280b0102811036110503100500c0e218980a086900300c0c80c13042e40001c1d2030b076104114894204071030541002e4161002c0d8501003440d00810004500036002a08010341031000d00307040c510907442880c007086500c028240e0404d4816000380380c04001c0e52030103503501914010441c0303854410220000ca6424038020740002814480d100c00c160082c3d5805038104980b140c440c80c050050500b803034403176403003610002a5401241040d61400310701503880700190b86580b044109558000c007415045444c50090600a119104081150031201d580102d82c0741c494000b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 110261798 1250 110260548 110260559
    0x30b0108060702011a0303090d0203030c1f0c0228060b03060a0903020c040e071802090604270c050313030c0c03060501050907050406050409020a030e060709061103070b010e07120501 80
    0x14089010b20440d60080c0080c1c1c1c0002d00d54200300350220881039243c1e00412015119060400f082c0c0681d500050030350b800d004079065024201880300c1e0b050460041d032203a0b003408600d0503228034210a5094030040030720001c5c1f031f8040c10707080b030780074020391044424940b02c0802c010294110300c108000140c15904c0d542094208040a004004004c03000341c000c0408034402030a02d131140d4001540040300030482d240c80c00c2048a8040b00d4000b40146464081100d0645521084010001403841d10b00e08103100d4008514142c40100411014a240d403c0c80410b0300351503840000d0f00d4100ad960030302c6500d1280300c1c1c82c041e15032030701006005050108450001060100342c1d030120341200c0c01681d410440e6516010100d84920850003a070000c144148000e000104031a0302808119200303080000b155500c440069140030b42c100d510034005521880d081c04810350240e0f000c002d4200110046080641d6542c554803400014050500e901411a0005a44070310942404081c034540302400c100558551 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 110263048 1250 110261798 110261803
    0x14090105040e0a0f080c010b010e0303030f18010c020c0a0909020f09100306050a0e0606010f081612020d0b031006180c030b09010602060f131220070b03040204050a050601020615010207030b0108 85
    0x1841020130787c2d4a03140300002c036540240c4020201d130300c1c0100914a5503856a240d55407135440900300e0700d03a81d103d43c9585010b08100f441010022000798000303041e070200002c1000b00006550300204100c030304128076200180c4843d16007c16004046a403036145580f210001603c031941d591002d0400c03401c4c002840b24550740d643c000d40c094203c21b003e640075070392510f0054880051420f99540000c20880000d1800000401c6d0401050f9040c40c18191002001c7d4044050303810143c41e02d440306030f49240c10f030312a14040054101d5004c04800500165140c14202c181002c0300400115049842d01001c2c2800c40c403941c41540c202e54002c01c42e040c90750b10781400942d03039942124411130784c2d0f1b4101e0100300da540c8400016844150701c0081b0098000307212408039070100c038000002d4442c0b5691510781c0406001845041c0141542103009a16460203004000540d00701074464004145030000340701450340c0c086180c5621080040440702850303107210040349005c00f964800340c0b01c09502000070a110001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 110264298 1250 110263048 110263057
    0x1107030f14040b0301050a081908071a190b15120901061d09010b09041e02030a050f2109030a02010c0c030204060303050306130b1f02010f020307020d0914090105040e0a0f08 76
    0x25a00d0500c1f80e0344400296581e0281f0703081d02c220394000c45054078005a8024010111140700e50205800c0051a085021a156090b122803051441c2c050070908544018420b07074503219811a41001102c4041890082610a8010340511f42c2441c1c80041c0c00030600b500040010040c445010b00d42a4003884130101641080e200640607509150450859142c00d142c0035008a81101045003410070020120001020680c0c0803070309801000301c4480400c0081c0300b0201d0a42900014140c0070b1503010711a000410345501851023035109000d12100754400048082240764213080650071a909401d01141c1240640d100075401400c00801008065002001d0740c002c000c2903507200d42d1900040185010355011b500981e40004000070498401442c01c01c20400d0403966000004903080c6007074003001a40e000b207806001603405440d441130000d912801c205c0081144d00901004250020005469240d040c826140304584414500b030702140c05000c042ca4943e401640c2110a84280c079212045401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 110265548 1250 110264298 110264309
    0x30618090308011a04050607050a05010f020a0908031201030b061f030c0f030203091c12060f030209010b0408061308040e0a050105120a170a020a05070e191107030f14040b0301 77
    0x702e0000014104410076110003079100c030031150381c1030a00340824070400c1e80140c03006803001e104004045000c41e40038403078000040c880301400750380c84d00d90a00240c000701050744146242c1c0d00403c00036605102c40c0c045241560b40c040c040d01c54940742c00001600a42d00c1e0100031000001c904001400e650b0142e110f203412a28070b031104071000c01f00d854141c040b40400c03a210882c60704003010480c4c55465011003844441c3e498141070414031041249101100c80c20b03013002080704078499051042d4a04428141e005041c0c1c020050318041c1800ca44946502c0050f1090030072103400070a03130b0100074180007581d018100c9200702c88001d180060880025007802c0c82510f00031031a80581110f01040440ca0300f92080e003110103017640609607003039071106610400000e000c5008403004040050002d01a020061100d00d00d95202c40c101804030a000420b84160411254940403006c401c001210060311003d039054100070780d4020313080000352109203c114080245c4d41001a01207403002250000d14107851 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 110266798 1250 110265548 110265557
    0x1c110f0c060a06060c031818020d05180d08040201020703020909012c0a0818030106080a03080601020a031b0c0b030a020c010e03090303040b030408072102010c02010b010f030c0306180903 82
    0x856806001045070303ca40504400910022941c4002c00c0c050700007a581d40c05118074910740503540b01c01c4401400c0802d05106143d82d00010f4222030458240034054010131010205000789501d408001d50b15000c4c0900d44080c410020001815603000b4420b902c021a0050700c407000618118503214004c3c004200c111801e620080105400b885000707200703d101e502c20070020300211802c0c1d01c5041d1280c012070401c080c81f040011204c3e01584080c0901401032610b6001000c2e0300149150141040798000c0026045506c1708a4841c0829806005030014461852002070315800c03906003240400380642010b42c1543c40081803081d100103036030080c41820022002003141d105018801b5031644641c2445ca40c0c075601c1030005000d20090b60b401181c0080c4100103a5260007110f0b55941c0341c01c1140501428542204c02404406035028007804002c014544000c00000100000203441030391040010800c1690703501240d8029030103035112401801e800480d25034071030744060078038000e040c10b10402c070001f4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 110268048 1250 110266798 110266801
    0x20907020c01050a030b13060306060515070506010e0402030a0605090609070509040809120a05190309171e0c040509030910050a050414180f0109110f1c110f0c06 71
    0xe00c08140c00d00710180582d01d90b442c1c0209003500710013800040c0e12aa50001c00c10304241c821240e68440c4070011761152038082141403510003000000d0b01c40b403002850046041102c04001036000c0f4090b41911099100314445441314008245440d200c81c500407c014500385c01d010601d040041e000340300e01411004c0b1241243c89000b40b00b1030100c2a02c0c014001d413424404001545001c0c28080307030b540f040c4e1003180c44038403035500e0b0036140c526190f41031080e105510344d990090581c07100c050f80c00b0303041045084002c01d07810034846669040c42c400403801c90090141c41c00000d201440005403040b40100700f80854145001419102e074400405903224082d02c076000c1c0c8040340608207a6403074030000d88600741090b180100d00c08a81d528411040d5003c00094443e21440d00600c00d01d03401145107001400e4250304069203042100d2092050f200e00324400e114040300410800b0454000c2d410192003401d440440400d410060040e00104c07a801c0c0c440030a43d00318071840030000d4181644030404035800c6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 110269298 1250 110268048 110268061
    0x20a0504050414190c0503060405060f22050a0c020606010c14160e07020a05061b07080d0b0307050405010b0409110d0e03071b0e0f0702120313030e031b0d03031b0c0209 74
    0x119810304117400003082003800003d245141130391181c0d5014501910100e6044840b100103010003000c80319040d164a902c4c1c80d40310072200302e44900380e0701c136802c940100405020408080e5490030002d11050401910703690384070400c11540d0780342e0440010501100d51b80180d41c107003800500d40a0085094000c1302c4030001c0c152510020346c1c85a0140c101c0007409568523603110090f0040e4040e188040d0301304003000303000006007148005203005500200001143d2100d4420141000c2d50341d40204d100c0ca05240040c01180100001c480480702200e50000c0c404110001358500c0d0300421035030201444c502080350241580110040240d548503120501c90301c141c000d40005400c0c1c082c0071f00d05500c01c40f040010b0000c1c40303411842d90030103000e004590303584020a54200c030316442210030501f41c081c414012410181c101403d00402d074030803409080d440d07240c620004040701d400680e05100da03100c20b14000034540240d0001c02d0070080d55201e05030750096030401406800c49100308034041c48005001590 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 110270548 1250 110269298 110269301
    0xb04060506030103080f12040b010303110d080105010302280e0916020c090c0c0601140301110c030a05070c030b010902030412020109111e090115140418020a050405041419 75
    0x603254014040741c2540d096480e941a40c1d0041590159500f80402641c12258410510244103900c2030f42c40018640c11458000c0071484c49023601e441c198400000c1d07050054000c540141036890038640161244039130b85400e10702c4503050380030a48a030014912019410344c0828141d490210585110f4099240c80241c1c01d128101e001e0618010f130041c0c83d5000c05441c01000d0150840350000085040072000c0305914249007080c0d00a0384182884403080381682000c3c041c20002c3e03100144010f0400b82048080c176140d1207a1049007042050014041d800c00108014a401854010207400f1156071100d51030b0b0000d503c242c0b415210012455612601180b050040221140d800343e0707902e12012078501844041441d8155500c01c4903035255203245240c503882074040c020003240388651020510110b002d170030060410140307141c1440402c014003800d10202d03d80f81204c1d81c5403c005903a14241c09080300e56019030713000154400e04201c24410000955602c4078003548440955009071041c401c2000d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 110271798 1250 110270548 110270561
    0x20a150c14130e0a141312020703021c031e1d060a17060f0636010504031203110c030903010c0206011a0c031b0609010b01020601030320010b04020417010b04 69
    0x811a02e568481809814940c181c41030308841005070124a000d10001054180c00045485001c003c807045c841e007090001224154141c01100e0014014403400c50300070030744048212007540402050341a031841098810380305076280c0060b00079906a00c854031440205040c00c1404c68120a18039900615110314055045a128010b0358440c0c0300b00b030f1054143d01c80b8001c0024400307988540e0341e14503d078894540100a00c001c9926020311000100794984514010070101883c42e42c41503014103461603a40c10004170b40070b40307400c618640d103d900c080c1e038100d014001e02040d120741c280d004164034242c40310000262980302000c5009200000c00c0c0d903001c0742d8038034003440344011200036440070459002146c001030074142d40341c1041d00d241c094003184502c00303081a008110030551001040182214080c41441e501034400d1004d400d03d5451605e0041098034080449071f01da000a8001e0410020258015420800c0152003507445503543c2e880b81c1c800d2601802e400c1c440c0c4d420540301d802c017403a00d4414007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 110273048 1250 110271798 110271817
    0x618060f0801050418021009050103050c0c0327031b18060303041401120203071e0305010602030a030b04180b0910052208070803090a060b010315030b07020a150c14 72
    0x18032650f841c11040102070005040444005d40c004034403400961166012030340c410b42e060b190004d0321842d1500060440e400101074116440c414001183c006c5008000c031440804442641c0b0004a1b06880c0d602e09040145050313a130603c9032180441e008440c138031400f051000f080380c41d000d4111180c8495540e12804070b800d030345d16420800091107030203002140c92081c40e0040c9814a07071000d0707001580f000c0768002e81c1c0000206040c00004015075540d000706101410b0306260501a9524128010f0755a01072030458409140c0c407070003060103e072500d92001002c42031301c5080021b000f41c1d9040480c41e00d803041d40c091056008000c040310030583e0a000b2103020f20070600d0340207100c0303603807501d04201e2000d80313401219541070800c0060042144140514052021500504002d80e90351418500300c52400d6600341c1490f09112440003141030000045040380d810010030f40446d510554100d0a0452441000b0301000301001110315040d0b842e0711003100e8600e13645507502154202c007a013100a00460005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 110274298 1250 110273048 110273057
    0x30e030f0607050c010f060b0c0705010c03080403051b061501020d0e011e05040e0c0d0609091e03030b03100f06060c0804170109020406090b0a09060506070b041a010618060f 76
    0x410b0106108030014011030b4040000092000503810740513007580c04550200519907808148801440c906008000062400f42400d103400d450503074003d081d0200c014800390621001040d038605014400513800c0c00401414180d0304145828030071082c5c5503009080309401480745030610200c1034000c4d00340c10310001d81612400c55144406501000d001040400c660412006100000340068a403040500404030170318031503240d000103e41c1c0021207840d80d0024081c941044150700100d03941c0c40c1c5400415a107030343c211700a0802424103401414080300005e426102c1c0d0402c00c1710a052561218121148881d814040c865032004121800056203e0161024108200c1007082c0846401c11030405081c0d1000851920100e40005045425a500c101c500988842b841c500c00c6ca0281ea008016101d03101e02004a18100404200390b4021601d008043c410a072022805011038405654048507800070606450b685a06009040101c820040404c0310203820011502e94001e001d13020b0300d006e080c0d45 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 110275548 1250 110274298 110274301
    0x10f05030a110d1b08010e011803030e1203070e180105010f0f090b0307080a05100f12020d060e0705131a040b1c0b0603160b030c090a0e040b04030e030f06 68
    0x454000301081e40d8406070f800001c1103520000640042c0c0003048040058460131181840c00c403980b4295040c44010003403d9140c0f1015021604004421501090301751800043c0c820b20003180781d00c1d040041c00780840064000c81040001644820000a540020703212030b48690102c602c0d003501c0803001e00515021515034240307080001d10a0320344000d510a64541a002c3d1503640014183c01d61043e120100080d0b030f0482006003114580c014240c120700307840341c0c3c045158a050781d0000700324580c0c007840381280c41001c030500941d9142210701c0c1c0d0403900038200f04401c46c00540e81d00e80c2c500c0e01d031003454010a5102d8202d500c03a111703445441e5004c1c1070040c13030000d01e1002108103c000c000b100130040c1e000c101024141070f5440c107486801902da00c1f07041c9104e10340c1001e070109407408140c0040302a5005200c0c0062040320313002d0081c4c07a00f200440070007940310003c00d00054150031881d0484002884408104018003a1504010740164040e0f264165524812400c0c9901c0b015000d04e05502c0f0b86c072a00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 110276798 1250 110275548 110275553
    0x20601031106070c03081210060e0a06080702150907050a0e070e0904020a09051f0f03080f09060408030d0213050915010e03030d0c17060405160e0301090b010617010f05030a 76
    0xe1203450300c11241c002c1d601c0d4176903442c00742c65001461050300202e02081000498401480f161014040d1801c18040d0083c002001078000c1000380103080401c4020700101d14460300801200c040e07030023512803501e003501c3c0501d0107594600c0d0600c900c92080c00c84650024146186d003131124014441655a03e074000840d10038014042000741080380c018003a608001a00c9807644170382c50042080722440c3e00c80c0742000c0702d00149000185c12001d00d10390b5111003040058503c1c4116501120044069500d960305000042d004e4003403540001004e0100040c0103210142c0303980184880c45150900c464250f8544040c025443c0c070484020b49100c2c0e1055142f0240d42c040ca503511a410801401c0b03d1130f200c204c400d29000d803001c5d80300000114038200000c01d591190030551503031183e003c0e50200210b1030414401c0010300d502100c900107111700103201300c009840a4001d00c14050300005031f0304083d655503100520901049000c5a02e8404400020940f449a0355003801110b42c020001d00c4000000d8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 110278048 1250 110276798 110276809
    0x150f010306091b0b0d0f0203070e0108040204060509040f050f0c0114030603011e0207031710170a0203061015141e13031406090106050d0b0604230a0b010206010311 72
    0x503409071400d000d04000510502003c007007200240902c0760320103880351148050401a1103003c03032200106401802000595036100e03031564200407091904507465226800428000c14550704800e40000a000c1084188481801900d1625200f80c0480714104213a0300520b032110340c0016418002580303042c0721220b40e200780004d142c21041c01400050390140610b41e0b00b1082c1d41da80c0300b00b100950040f51040606402c040d1003041c00382092600314040c90b0940f00440c00500c1e40c0a81e4207210090800b100400c0400c1081800031035028040715024205296041400c21440c81102c40c8140461001c444803480303028a0001d481e08005101d06040030002008010403030760360088400c820a1149029030703030800b041640110f001e0b4113111201d03540b07080600c3c10a81d0040c002c822680c14840100515101c5207a0007038820f4001520f1086512660000360140003000c4c0600144103500b5888001103d640103070328041c6100702c504101c1e0880031401a030300c429091101400041540850100d5420003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 110279298 1250 110278048 110278061
    0x6030a02030403030b031c090501080f040602030705040e07080a06150207090507030216120807051809040602090402130807080a170a050f030906060103290f010912080c150f010306 79
    0xa1304011808400f0751001c2407a18142d00d40d9880482416403040707a140350000340043c05042d0030310340740c000e0b031510b610002c0b400c00000d41b0003010143c0c00800200058840d0f4203450141103c24a070303a2082c18a480000d12a03681030759203003126860124000b0706000580500e4504482036005019041d142501040040800070321080601d9003c02070660103914091126940c0391003403403281910145400c000f45059001003003481441807c0211840c180229070b02400202021500d0105555a9207001c4019016841055030040c1c000700f0002d560340030014801040d6901c100459000c981c0d00e001d8195911a14680502214102c051032602c0d400c0060050102c807203a424814942101d840705000507500440f10b000ca075410000c1070041640c0d05000e021103044d1407a20301c500c50f20a05a181c070249040c005201e00c2298043c407007030096402502040004e20514101841c40b99071420140c606a22200180c0040e001340c950001100810300045401110410a5141280e08550300d0400410310f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 110280548 1250 110279298 110279303
    0xf04020102011d010e0f010b060712030b040f0b011211091e0307060504081615030203060f03010501080a020f040e0c01050d02130906330c0f0203030a030b031b06030a020304 76
    0x480710403001c10040c50030f032120300105a0800010300c17480d880200d641804025011020540d041110343c003081e564001c2078a4110f40c200408411407a140c11050f0001d01000c0740594100d420008030050b0201c480d84086100e40e02a205c0c4444e080700491030030102e0300c3c20342441c1b1441d41c00384040603890600c62a2500740030201c0490036410f80217840001c0c0703001525440b13900000d00016081c040d2407000d000840405400e1151542c0b8581040c4401402e203c240701008205a804000201540d9880d02c03501e05070540030340200100d58440c208079840c0d00c8480000d900441003103003403104034109171107181144034403840036100045903130300111400d500001e14045107940a1100c50100060100010001c2c00f40070000211a4980200381903001c9501ea2112a60403851500b00c0307000b080309086c00d040d0a607a14040040b03254a00d0a0100c889050b41c0203501484040740c40c0c10003540550201c100c01d0302c11011110000603011442034940140340042d9005041071000c18100e0032141c000d10340061 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 110281798 1250 110280548 110280551
    0x1403030d020c03030105032103011403210a0e0109050906060f0706021204150e060a1503060204090606080105030d0207060c030c0515010e011505040506070c030b0408031e010e0f0402010201 83
    0xd600d4100103081e41c2000c40c140e24540c00c0000100010318007082603480c0c040311141001d800b1100b80c85242e6281c0814800d619001b1098040717500c80b0754040c8500d281c01d900000303481840d040083c4100780301e03410219003200414030101038504a03601440f8942c00300ca500406c4414940d0714a001d1000d5071700710600e0001242d40c140309071400111207001030812041c0d0007003034120a282c04d003000020b100c490341c500703211140b4050f44a910010082480c4c1c4e840701781d8040125040a04a5502030304a4080e0b00140c0f526202140105510182d50401422280070fa80d41d400360b070740c071a020980c6400c06080d2120250344801c904020050041c15400b00550081c2072610504442c3c0c3c0700d441c248031140b19090b6890400b6030041c40700e000800741042c05042240e100c441208000e60001d0024841d07401280d00c600d9001c5208400c100042501801960f40000381c0d03601d070706080c03522400941085d03899030340704180452015001c2c502201c14604861280d25000c809486082d51907150b040e000c0c000780e0465 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 110283048 1250 110281798 110281807
    0x16110102150408070605070c15090c080f0106080601142202040b0a030c03050f06030d1107080114070e19060c060b090106020a02010305061e10120c0c0618030801140303 74
    0x1ca00320076000780300e03c0c05543c43d556610941c1c64103200721ba40090181c424000b00c11551000314818104118103403419990000789081d0b182091500d442d8240d20400440c450b02c051030308506010340000c4110b8a8140850f102c9988501c03003911320b8150041055042071908004120403981441c010800b404905001458191903130340f40000d6038014002003003c661201c410161040d4107108403039003d4040041d2013001d007820720000fa00c0e0030165148908020441813890f100c12002d001840050850000800c10401907007030040d0341c0ca80c04c9507414003180d80d04419024604103907076100301216403185d0f408001414481c06603441010410250b601540e2800c0c07078111a2244104c5074085c3c10203170010005400c42d840014140c65004007401d0094014603550802070090740510211143d08440240d1501c8038001d08031101c20b5131038081c00b089810250090100ba030404074082c0c101e801040140820449604100110030f002800107001691140041050310030450500880c1c2e040141502e162 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 110284298 1250 110283048 110283073
    0xf0302070f030e18010305060115021c022103100905150909061b040b030601030c0c061404170307020a1101050c030f041409090c06130b030a09120516110102 69
    0x490300c1c012000c038007182540280000342d141c04016401924141d0754001c0c050360440d620349440760b034180300d6401c5800a20405110f80342c001c0c0001e80340b842d4a44003111202010200003940da8182d222680c02c4699103094025101c402c000480744580c07032048074a00200d140010100c000e21004118103ca1070344c8001114007030b0f64140f41c4500800302c510083c00281400041003000c000401d07650a00258100401c218025440c000da95101e98242400a098502c03404c060b114019203841c000d06551524401c80040ca00f032890231801a8010b00b002180860104110318440c03000707540040250380840f1640b40003e6a1040304200d0365410714115040c035a010001c039255800090300c80b0305030000440d007400002107682c10503200d80c204440c0e03481d55040030348945071204003c00c0b10303070b000c1c05001a81054090205e0346400042102c403000680c0d91614000510091404071401c640e20389120070351048291040007900d803484034520000303c00e52003d9503015001260402a14154002c2ca01e81c100c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 110285548 1250 110284298 110284313
    0x6030307260c0109110a0801020a09030f03090807030305040e0c04030f2a0603060302120604020607060f110301080c0405010503010b0a0506031b0a05130f0e0f0604060509090a1a01030f030f030207 86
    0x4219101c0c1840011402144042000e411b48603040710070790f40e2043c41140d00c06503000d81d50354202c90f0001c0701e10703004040034102110019100d0304100040d03c1510707800410164440c004008598502c0c0d510909038a0b40801491588214800034004c0c569020010000c82c542540c10390b800c501e59007240f42034480c074840711390344030a40d03078000c001080d510642001903003414168101e00664802c0a42490701d460382c00150740740650300b0050407841d6201c1001a0032a026071141c200f0a25409049840b03695a6010603034501c014103200340a21700307040000850b0b0505009403c00d9030001424046054140000d00206400040c0a0300e001841c0c1d1030b002d4800314424008180074a100d94074541d03225100c6400c10324030016540803c1d80c80328640d81c10420301c04104045a04030700303912600c0e513154a6100024002c4c0c500c68020320781c403a50030010f200d0968000600b8006c0780f486031840d07018074189801081c0065000344006446da010464a03400020310a004180307d10f9107900b00182407001c580c40303907003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 110286798 1250 110285548 110285561
    0xb01020a050f07060207120507230306040807020414090706140d06030809090f0c072003061504060602030c0604260a1206091503060c0212030c030103030806030307260c01 75
    0x320541c100c020144941c5034180324013001f03403480c2c0c2e5100050302c0a0384d039540d90390000c80c4111841211141c0164941c071034001804180250000d0840e4254101810310b05401c0c1d0008008900c11031500e8001e03041564140d00c0c1500c5052024060114545003030710030340780445070700d032003500541007040b200303c21000c50700c104000f46014840080d11412401d0601c02c01c101d0250101c1d05042413241000742c1164031000b110507080d409402d101201c1c06040348070941124810100e40c0c1400303402e04101009010341001c03080210101c40074406940e407400140e0302ca209026004500381c1040000402003010000b001d45203690015045611440e10701c000112900139400e1000061140141c405000b000c0b4050340c0080c0548240c01c01c400c0900c42c540340700303114851100501d142d40700c5d424240300d14028011641d40000d541c4000d030b584d24002482c05c046a0003400110007081480b4046101d1381000015502020350001c214201c0e0b18800c0e860711380711504a8401d01c0403c000308022414010300f80140b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 110288048 1250 110286798 110286823
    0x1803050924070b0f0412050a030912020f01150308090607020a0f0b070309060f0c02040507050408030403050a06150501170a0f0e3a1206080106080d0806150304060b01020a05 76
    0xa910b6069a1034a04500712003c0d00b18880300440d0018000482d110100048800000381031203542c1e082e020a00383c0150140c0c4a02a0001c1140c401c88400b56802181c03200c0c4000303003080200856003070b240c08030b0240c40c81400050800f0300140145101c6041541c01400310074001040c040d0b15035a81d0348208441b11698000e1801c502c00441c0d90310070190048007000182201c3d04000000080600d4024490b441e9000c000c0c8c440d580754400300d08000c0c001c20031070307029080442c151790b5981c0e100d084c404d903034030250102200c8242c0740403d0204190380b00c0000800b52003059403080c00062070700500a600c0000a040319506590b204003000d401d030103034411180d01c0c140c00005084031450491040c41880242c40e15654105680b00c0014082100c42c802044114020704042041550301859180140345903002581650305c0e200b4045186a00003907201d0190070190f580401d2651340805000100d02c2c0c0c100d040d007012106101141c0080d2442d00010300c2d00c1410f10440302c09241c2c1d0b440e0245002c2c10360150 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 110289298 1250 110288048 110288119
    0x40303091409160c210c020111070f060f020102090319060e01050702030a0c111003091205070c03020405060409020411090109050114030f060604091a0901080118030509 74
    0xc0241c1c100548801c120300d201110402803918100080c0c14a029070100460108414401c04100700206a12481048180030100b2805800300000140c414107402c00c0590200c3c504004000300641e00280440072345d200345240c071054a18003481900c200c0b4807140c40e0b40541d5000d000100c25501d0400c400500381c3d4840401c0e0303101d49113034201282150030884504a60b641000100404544c0000407110081c2c0d0b145010240034a1508208082c03821960141c0d03404964000f035022100c0c2e01d40c00004c0194001e0241068915010ba0165400d10489100070620700d03540f0010005403805921003917000c04043c2c4085941621503000078200e5a410420440c03006000c80c07290000c0d680560f9400140c035081c01c24401700c403501c4032800103d00004140d12131003a10741d00002c2443e1600404e03503006150410041c0000c00881d60203101c95115241281e01501c3e23400e000082d0500140540c0000b0314801420380d1070301140e920125030342d50054408941000e00114013100d1011403184000f45940c03840340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 110290548 1250 110289298 110289317
    0xf260601030b030102070b01030321050a0c0801050a080712030302040e040c14010201021806030604090b090102073008090f0307050c04050c090a170c0409030e0102060903130b03040501060b040303 86
    0x240c21282c200035501d01981c418090240040c1e015401c460540e030705400c1c6840312601d00c2414040250507400e98904003410501402104000c91304155204c48907915454456a01d4009000c0c04000382e214032070b6a580b03c16001c00c5000e21442c0c40803903041c000d14000d072a154588240b44003e41341034404580d0f944d88203004203c0689124614015618248025841e003100f00f05020304d42144d80351041c0c805c46000011804a540301d40c4903030074042d48040b10002c1460180c950500039000f80c0c2054642c50500045108001401c40079002100201c4e8683c1c4c10902400c0000c035a8010300400c89902442a4098075505c0c640810103455034501c2107008049801303000060105844018140801000c41484140e6065450024080030394950002d4108400c1c0f80d2800c061903c001c082e50581c2080c41e294042050540c0454034081e85072081c1c089078616107814554994038411081c1e5141c003250600350910141004c5001107030091301030400403410781d841e0400c0a5140d03025078811000300d0b04814 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 110291798 1250 110290548 110290561
    0x603140f0d030c0234030318060c030c030305150307090608070e0705070213090816060513051c0c080c031315050913020c160501020f0705030d0f26 65
    0x8600428801c91505112101c1005406561602d0050348100f8000000140c1040102190041c503010541083c0602c041592030501034092842e201d0041d2400200e203501150041c00f5801d82c2851030f6041e940c06c040c40025481c00c8000b444060401030b492300c50408103c1c1c440e07908000c0d400203041d4611000500300d152a071804e150070599480940201410820400010340060a8540403234045d24943d03800030101e403241000381038140d402000c80703402143d0005841c54141c00d4040580c0f00788410081c035152420540341945642e0340041c0385500101185400d0856107841624121407402c2408800a840e62081e109400031400403c8507407010a00b03171124164a031591008080d078000251080f10819001080d51240d44d8445d405000402d00e120240049507040341d0a02950710f080d034042104928980c5002c0000b841694018450040e9082603c5004a11070081701c03c01001801507846205003500c000c907010701d42a05000d2801c0200c0d041428040c03031a419003100381180c0c0c0492400c0c1c0c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 110293048 1250 110291798 110291803
    0x6031a01030504081b0f07080304090c08040f080a02011808220308070303020912030a0e041d060a1a100207030b07051228060801050402090105100210020d0603140f 72
    0x1809580c109400c0000b844040340203807044903160410400116108400ba000c820315001521595810f00e1240c1100003400316004000303042500c1e02c2820611841ea40743c3c0e07046035864401d0760064410b040841c610340000c0c1c280d40003406205030b01d0001040d0f10450364813150703298800c1c4200781d0701c02c0c5001030010504a50780030a0b0381d004c0c00f807152800f40300d4110f031102d00c0b00b8041e589005040c035a00198030641e941d01c0e418a070001e50222421290340700d110301c000910720b0400da045075010310f00380110300120000410061400d042880c1c0289001e5030786a41c01406404c05658035216081c0f4070103511101d440e045814204030600b1b400400b2581d00d14949030200d014000e0000c41005810f001c0c2640a031a50081144c00a41090117005207201c000400c8000c1e01483d80d16180d400c4c68044005070580c010741255110745d00803101820507a82e40c60a020080710a14080801a04003854201e6a1800e03903001e408503400031500024074548a9460800804550080d004280c1c413101d4081c4a2407002c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 110294298 1250 110293048 110293091
    0x30804030c09050403020a030309030201060f120309050102010c140904021308160b030c030106030510051215090a08030105010f120609020c0f2d1f0902100e010f110f070603 76
    0x38050208501e113410344000f5182c15805000604243d1180c2a03102814800d421803c0034046510300c0b40b48003036981405210180d0440340071808185042d00000e05580103101c0d4103104051601d41038814020314205407210f5111150743d9501560901007210350b41503150704140901042c400400c54881d44180e00c0a0b6460103078800300100104008005050090ba82602d04485d0341e0705001c5132588400002e81040c1e1895000700b07030403040c01031a841d00102d0024080005050f94544040b40362144542e403a25079882d13400280c14610208010001075205544410382d2218500e00f0a14480300a44a103080d40d038581e100036407054000c2003a0617448000d00c1710010420f44800240700c0c914944d14680800c2c1c0c8000110440505004c10044114806004441d00c086070700c01504140d10300c101041004001008040c1c3c01107240c50040c05010340141c10386018460141c550b0b040030005000102c0c3d01c00c1030702d548201140502e0050400e50b000801900019103001d0700d0204180802c0b88808101425 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 110295548 1250 110294298 110294309
    0xb19090803130b0d021605010501060908070f0608070908010e21090a03020411070c170f070308030c09010318050d0806060913050c07020901060504030204060f05031c0e0406030804030c 81
    0x401525030019800400b110844414005890302e4801810681000f4040c1c03405030740d1107140040c6264100309040d070142d03050362780c141c40349841d9548403480d0607543d0342a0b015800504515010522a541c0110440340c0d00c40c00c1071524228245d241d00c003c2d4251008400c010a140d44049101100b02211107511450140d030030114500300b000003000140c4001c05440b010740074a42d55160301202403c008111042d0a40040d11000d41650743c4041c000320700300390304041c80e20b4052007051240003107001c94207400706c2e900000c100303007107403074808a140c0c480e40603030001d42c10315541d542c0181e646482c040c058000715001d03602070300031803613a11009414800000c0c0f42a03c90b420800c54914180e031030206040100c030300301c840041d16039100102003525114103107010b9407280001c03000103151644400100700f0740c2e00c00d58040c003075140d6884203507480750081e0042991540200c1a030007400f8850886001c08215940350066001400c140410110340750b81d08259860307000000d0602c02d0013a04d80880c3c0c002c0c20f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 110296798 1250 110295548 110295553
    0x1902040b0d05012a12110f12040b060102030c03040e0c040e0c0a03050106112808030906070e0415050d060609020412110303040305030f0f0d05070804061a030c04020c070b190908 78
    0x2400004000c0c017480d20840c4151007159640394200460034941c080da04070000c0c8441c15640c9841d1503089181a4104440803a101801c2c0b90000d00c0551002c070a036010310700c040c4011030a1604040803400400001849800c0c144014000000c3c018100ea901c0c5004a441141c80c541d10440254001d00303860301600040240304000c0c0a8000c5441c00150344241c1d03171011043c0c507a8501c0c1e04480003103078248060000c0e00d0340ca00801030044040c408220345001d0211900d560022202890a110688400004000707003944880c800304801d0521344d0300f41d0120b5200e02000642d00e030b140c40000b02260480d401602c00d10500b000d813101080b450115240b52303502c0032401507081c00e1031982c81e641e6030310030107010a60729034004ca00700c01d008094a040d00d8208034130180a101525004200400c3e200045034181da0890401d00d100604040c2800000107020024000e80f07540c00c4801c0601c8040c1d030001c4d040c03e21603c2151000590301001001a14048151140e441c3e858403d40400800001c5207810050098 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 110298048 1250 110296798 110296871
    0xf06110d2a0210020a12020c033606030a0e0a050c0109091e0c0507050105130c0e04030806010e010e090f040b1e070e0a051905090702030901021902040b0d0501 70
    0x316000039140443d07060203100966540012030040328401040100101c1007800400c4c010070160021010304502d50f000c00111840410403d588510229200401da4008008202e044039a0600e10f00465000e040003102041ea410716a0300c141ca00008401e003514103800c107070b824003a55a4860407184c0200b660050078009054222040b6001149442d10001c4490741d50740c903014054041c2042c2c0f80d40640002c000c104034a8200e00c0a80602d884a5049580e030082000c041210402c03c582240650f070960380e4030035030b503884000554441e8008107000341800041c503580c500b01c0e6283c0d03509520481001c01c010403141090b2604903070214025101e1900307012204446006071303150001c92540100545000a00c0881190101c0d91490032604200c0e0041030403a100e0940340d0031203011404070b03103054034500f07002d9450450807038484c0103000107507005030001c41d03001c1c5140e000d41c4c8000000c1800200002020721b00d541c00100004050602217030700345d454040305c144607003100340403103484404c42586c210302 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 110299298 1250 110298048 110298131
    0x1a0601030b063103080d0c020d030911090a02160c1805041a0402040f020408010203150604150302030c0d140f070305160c030e03030a0e03060c0a0c0f06110d 69
    0x702d000a445043c25008200580c000304802e41c1e910065401c80042c035640c51200d42083e000e021050581d0015228410300204024401d100f000c0e005908020b00c041182c2a030000c1103201100034001c9201c103902031021202c4155203a5581c1c000b83d00c01ca0015a2852400800109031130008401902562038981008040750044810428501c910545a005e9070b640d8400940200461510200d41c40e2002c6004540580705500460140c0130a120700461002034100700700d418031440c0190180740510030290001180680c0295411507498400c003030902801010901c1200e07900480300307810981d01400e0000c0c903000100703000c0d0402024a018003962070501c0844001c1c3d144c4040c41020000303241094014540304000c01c1080440040c2640da03140f8a01c40002c02c0c910400040b148240100c101090041707a2020454900c0e0580d521031640c030080c25203805480d00c2d1040400c0d0380c801e8a44d1b1030b843d9134031518401000303460340c46040043e500c1e2010355440d0b9030611041c45400030301c00e140c80c034000d03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 110300548 1250 110299298 110299327
    0x406050a06080d050d1d031c1b090e0a052a0403082b0501061407021215011505030610030c020307050109030804060e010b09060f0103060f0b040e06011d06070f1a0601030b06 76
    0x25071100c1c0104230103020b000c904800c4020301100d10300c8021301c0507034484c00712060341c000c1c820f204484566041d80c00d00d4075035000701c0046a00698440d0907495151a000820006501041c0050042c80f10207500300360782c988840720154000c03003542020340c000e8400034044041c1e0880b20a48655400c41c108071540c10141c0250031034031000c0700010f145038013054490865132075210706509030000344240c83c81c400482c15043c035000020b0080220355001d8003800c8448034441d5041d01d1103504003d20840e55807100400039402000c0c0f206004085000030400c00b00031503000d010300f141e200d1081d90b031019107261504191040b0ba80b1080380a409074102882c0240c00d55030f25481c02c2d0004821900341c4a8101c5100041e0003c0c18203070711469914003000d9001441d940060003a20454161401105032a9100c00045405c07203220501103c0c6040e15070080b88260412102a005143c40303007060710b46002250705d41098200041400c000c5504440b420000e295a150281c0200083c0680d01c243c2842c40072101850b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 110301798 1250 110300548 110300557
    0x111070b030406050c1c0504060f020909011a250203160b07060f020d0608010902100903080409150b0f0a020d0201050709121e03090614120406050a06080d050d1d03 72
    0x1d0015888002061181c0d00362000c0f14030351b01c0d805241e49440301c8600f0120010b46803c403010b0316010b00d0260440c1c402211802100d84503440200600d150b0ba080c007000c00c40380802200d0031011602c05020407401c03c1000001c3c5c0414001500400054641d01d2040600e484c06e865000714840c00c1c0b9000030010010701c80c0a844029500c407402046900b10020958005c0c00380043c80b008180c1004400958520103512500e0b8550007036499800f00811100150b0f0480280d00c00100711060401c07040002e00312540c441801d00405051141601c4d9440e04040f400b5000314880016844000580150080c0c04029249031441c40703000a20480c501400003800c0c0b0b09a0303118140321464803880310360130000e203090240d4a04c0b11703148102590701b41d241001400c201c0b5900454002c9000700103200d009250a00540d80c4031134001d40752070490303038032940c07404040d05c1c02401e0610b8880c2c0b038820100d0000d10510081c8280c00d602c0da2081d45403054410b00d44140c800f00c0350f100480408102c043c001403100441141c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 110303048 1250 110301798 110301803
    0x503010501050a1707090302040b03010614130603120905010305090f0601060e03190c03150516270803030910050903180114030f060109060512010e13020a090b0111070b0304 76
    0x70b0b11a0f03103541060380c040b1425403444144988420411004580040b400c0c0152030082c3e90401a4512800515013299058019068400c5604004458500e00401c0d61540c082402c840400c4a9589a80d0351160407020020540030030100d00b010703c03995905105442d03110200300000c3c0858422204103d4841310103004d01400c000c5040e14524054604000c09050703001709003c055132948240c288802c00643d28082180c080d9610f409048044800d4002d8500400514080030f500091294040d40d40b00c215501c9405001900e0101070600e106411002004004d540701441c0c1d24170303200808904260101c0c900181a51400e814040100b40010035280c0d166408480e052201d0b50f41c00c0140e8240c00340c072020040641c030000030400d9018444103030301e0042c4003e0f281e0041c0191200010740c2c0c9806001c02004400c1d000d100100704042c0000e204c250805000740b0510180c1100e9004103038410b981303401119446031142d14031040395034040344021085203507001805a0b80e0070010309041c44c0c800500003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 110304298 1250 110303048 110303057
    0x303180f0209090a300503010602060f04060b091f050301180602030a02120a060501080703021c270605090c0603090604080306011b03030509010f021c050a0b03240c07030503010501 79
    0x70710940307800c00c0a588a0b94000d29401020058010001e1003006481112072001d0411748071001c100b4002c4c820349041e105039401405255035a1150002d20380030003002900e03801d480342401c4100e600ca140c0c2840c003d03000d54000c010b1002745070b009a580607690381d0280c0d00076850014120300e01c0c02c80e103001d90b0500303034400000b6030749407039003980313100a0b014044210000e509042c0900514900301e0344407500f20358080c1c0325080e02d80d880171429002c9014180382d03002d000015200307500c03203034440b0340c4a1104092244084840d040f01420b00140403202ca0b20100c1e42d040e500c0e400e00213402c4040015040086040705c2052441c85e010a00a440321400381004040c8800800400c8042e03006010781000c0c0c1804141d0300ca43d502503818003c000d04800d07030301120b45510b07200c0b020310001186d0007250b541a0403d00c4004048103035226040007040000d001d502c01179a01c1030101c200d41e9090204014010000b0030440e040c805c000c0d4104046280901412944181000120700107904002036904561013401c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 110305548 1250 110304298 110304301
    0xc02040b030d0c050601060305150d020d05011107110609010e0112060e2e210201050f040e060a0b090a0512030c10051906050f2110090303180f0209 65
    0x810003501199003640e61500415060035085036020f540c007181680a202140c010303981c0c82509904a41083c1c840420160604070074682c10300f003204011034454130140807c0b030034101c162903450844074500e43d4810101c5000803400309001c003074840c10039039907000ca41c0e2500c0d10303801d40006404020038171205410f00820003895003010a0a5104d10001d20741c039200d40000d442e154420007003881441c4a00700b05108510b0004d8000d81400b070f85941a6200000f10401054912864010300300d084803040303042140401c8003481c4012104050801030658401075419418075404108803010356800400b0010780602c407041c140e80d44c124442e422604281e940c0c28142c0d000d0201035046d40b00b0055040f49900c1450030070001000c1a90005100d00d64505a02985035801078400c01035940900c0389562000113104084200d24103086012849222681000c0394640c20b0f00c221820840c01c00e094161032652070680506150b014003074082101b0218020310303642d0740266184003540b040d198010740107002560 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 110306798 1250 110305548 110305553
    0x1c0807030b060327030d060303030212091b0603100810060303080601051c110f1812070303020616050c0a08090a0512030a0e060c030d0510090c050a180302060c06061509010f0c 77
    0x11a1035004040317200b1f1107900d41381c0c00d001e400381d8080000070031801900d80000f0200080402d0007400c100d24800410b40b42d0740030000304061904040c00d1200182e200000016121900f0021351400072840307800811264030314103015100c83c9006004a050000c2040022021409020294140030081c0000500c10201c07050b01c4605000b442c080010715440081c145400100324a00c2e01c0461204842140c411005511020380300d460317500c03004000da4400e1000c51181c480480c18a09401407078603000e42800e4004a565107405a4800700740c46203900040e6044003801c10080c2080a0801541d6000c915291100b0f407542d00e224408441d030800c1420920030b00540d840318125041c002c0c10740d0131241c840c000101403000401d030030380b981d80e90090b90144c0040c484809008192800307400f034403142e0074080b2030a0140c03114261b0740035015100343c03e40c5003c0016601c1202810030340c911100140034910b81042402090710110007290381d5940c040c800c28000b6070784030b0114480c04140d0300d082d4a03001c4192 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 110308048 1250 110306798 110306803
    0x120f060f0c05030a0f1e0506030f0601031406090304061b0c030819030b03120a08070207051905010f0e0303180a08030309030a020607090609060503091c0807030b060327 74
    0x504031903240c0e0741001989451103034484043c6014882c051070410401880094450440303e40011055884646a5141200b43d1480d40300380d92200018040e10f81006801d41501d00b800800d030000c5900c0340241100c40443d2408010701c5500802d0340004519142c00c0100180140b0398800260030980da5412800c81000580300b4868011345e4802d034400d46688041c006480a1a019803206000a1810303419107001c0c40c00103a803035090700816900c01e152024500302108c40c40001440c1d90150320441d03a0004107a04c5d0009920801c2c009400c0c040c6000b4149400101a0303008900c0b02e0041184082c2540e84698010040f05d245208150300c180100b203c000120305900610303400400c2a000101c10000d8919020000f001c1d1052540c1c207851840d60358041c1030715088014000c1c20b001820092050220070701880c01190043c0c5101c0c200d40041d900c0704d12554840c02a4000070001942c1d10051012040d0036014a4440c060115003003400d500e405100c0450082c003c00d1011000c8040c41c807061a056005d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 110309298 1250 110308048 110308061
    0x304080c0f010b010f0509090c0c190302010902010906020c010207090c0c14010606030606260705070803040309260c0904063314010807030f020415170a06120f06 71
    0x3503419034a0960038081c0042c02400303400f44641c042005e000901441512640c00c4804680d8014141480e64660000200c1580c1120360314503284d1240700b065884030b44124441d0056148680e0002c130300500b4510004011004642c4110b0965003c10241a604d0380c011803214140c5852910001e4482c242d40301c01c036a845c02c411800f9007082c00c80161580c0c00302042d00f240058585540741031010302e61350001240c003602002e00400000020054046510000301c0d641c07500134101d4a412070410703005407210350041d03100b44c030210701280c1c0c40c400400c0411032036280050f4079004a109000546448500c040d2224503068119104e6000d031070000e02000015401324410710800d488403a468922540050521540354040b00b46888190740001509a40200980c0a80006955603140703038642040c1900903052203010350200540074400452000303580710a03442d0705421951000f202d415001c2e241001540c010303107403002050400b50305100d000c0c010191164019442100034089101030308008008103203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 110310548 1250 110309298 110309317
    0x30b0d030302070605010f050a0909080f0c0604150e030a0e0622061409010c110d021e0118032103140c0405030f0106060e040f09020a0e0405070f1a030408 68
    0x2a56020061681c10342c05800042c0c41684108001e90700c81c0b004450500d1280301e0760303a00555880d41030003804042e8109040051056058500740201c60308058040e41000c101c0c1062030703101b01c00300010322103210001e0034070000d50001046800504404103441303104000c02001801881c00c1e04042c9600c44108075500508003402208900354882e120303010061692194200041c41c11801e240b42c0d40000040701d00819058603821440e4080c1c0d61188650072140c618240c4c003c0552003004017517121100b4030810707007a081e0030504c00005070400152038032500807240d64818210308005c0c00003442c54450070101c501003400440c9001520202140607140d00006011072804141c10310240180c0503003d08107860085040c0c0301408003942c000c41c00c8071101e1041c1c500040c0140c00922203070405502c050324a008400c000f180740c0d4402d401140501140394040d10003042840104424002c00303000700c0018007035050780000da19243c15980c6a0442d178103035206201180010101d01045040703400c668207600d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 110311798 1250 110310548 110310559
    0x9030803070314090606031c1b0b16050405030c15071e030e18070f09030807050a03080f090d050928030501061e1403010608070e061503011d0403030b 66
    0x1030308240050203005400f04030030005040301e01180304031001281842c850710014005040070aa1051511228035100c280101404101260070542007102031034070a450b80280c5800e00c0604004203200055181c25141808200051009016558005c2840103903c0b008582c40c0c8103500c0b5013182c3c50303120b2042c400010000204510420b0104200d113034802e1a80c0d001c1e84030b005184440c80140603540c0b47c100c00c0c80065030350950003c1c048900400c2c071075680c8071044c40c08058544d100e503200b00c901c0e80219070607540766000076450003c2590005800d40d100345141d0800150b810540440d80e52240c440c040c200078442301140403040c44c0c4864140302d800b03800381c40c1d203400202d0341d8110600015901d80000e847c80c0d42801800f00348107204440b907a18010b02803500202e082d150140c03001040d80010400e0340d00d95200c3c00c0c00192100c040102e800545000d004841090070402e0030040ca00c4000e80100741c40030424801000840c4903080981a00d50003010038841595641c6011401414041581036101 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 110313048 1250 110311798 110311801
    0x50c06071a04050a0c06050705060703091104020705070e070509060307050d0b060301060c051e123007030c230706060e0c0a020106090501080c1216030614070c03120c09030803 77
    0xf0800155240d107032130244008407502030701c0e01b03021035103440742d040d014040d640100701281900d4426808800414004c0c1220b00d45c07014190009420303607108040580702984010402d0000d245800000c0da000780c2c0303600b4820302c1d103154540454000d000017010481403000100390a5081106a000070000307100042900d5540d68458001501c90340c1d004100b07a0301c6105105c0a2800c8a4480140c0c145d01c0c841e0a00500000007014061030407588030050f46001020304a4804203403085040e106850600c0e001400c08140c07811100c002d0459a40c030080c3c504000c040403009405985400140c40010201145a41d8684c210305110000c0c0c12198000c010b04015501000f198118250240c00348030b14a90003400310507903079591982510000c0c05424a00d8002c070034041110324045d0814070b0307001e0703604055402001141004001d94866a8015543e041c2c49074614151003100003945a03110082d030800d44040c09050314010420b4500107002c1c1c1c00f480c0c1e14454180301364001c8040c600119803005207150340f03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 110314298 1250 110313048 110313053
    0x40f0308100b04150813020a050d02130f060503060a110406030b0d0213050106090b0c1509070306060e060112020a0909020c01021303083606031e07020106030c090603050c06071a04 79
    0x8640301600c0c020005e4492030210f0200d0902c04640c8110580080807826164104070401607000040e4604030b901c12a001e00190755031496001c3c611000300d40090009016151406143c14894014250803400d490034204003609043c1000750340070f072216460300180c0380c0c24140100789400c1881c500030b58080300280c04c034211503100e43c10141c16107403150342d0f007914569078807098500c0d4059491803d0360f513000041d01400002da801c5900340c0c00002c41c011980410790b03076155072040b180b450700250091000442044810358024001107110410080214a0907a110b60018911111030050005042e000500340c0700c110b6003501a42c1382d410312000a404540d035285800c003100e034085140001610602c4840e0b6541c840c0b40c58601400300610400f1041902d812000c000c660b82c4020860000c8807142d40d4138000d4180c020803d87d2084000d900002084c0317045040c45e24081085a00c40c2c1c520905000f02400040c2021a041d500840255801a220509803030f01011034212601184078850102c401c2105 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 110315548 1250 110314298 110314319
    0x20c010f0e07050616080f030a0e2a010c050708011d0c06040e01030605061306080a050606030706090b0f16030f0306050f0a05221109040605030303040f0308100b04 72
    0x5900100c500d04001851180007070940390b41d010300c00d440d03001394244962100150315800b40c0e4110b40c800c0c81c03403a250060b10456484150030950354001440e507038040b00102d03031904019640c0e68201e00c40c06203071000c40c0c45c0320781d140540c8807005003410480c1e00c90f03050080000401009010741201d02c0248083c120000e6051881241907140305401d2251001d00803845c1000303011079003a20b5042207c0300080c1c0c2544c5420002e4407000e0010754100c0c17002d100c2d0800340100c5104420152810502500688030075040461030030002034000d5100741c00c2803004100c071503005812401110314001c4540e85400c034100c52480c55005181e00141d104002201c07400030154056101c0700c90364440c4d2410014203880300140003882d09824406034109100b000c00744004d10340141507556620140d07071320f03816004222a41c841602c41c0c040f00c2c000101000709000003245024007801018200c158019420740c80d050b101c0b00d4580481c40300181c00d01041c9804102c1c214096400746000e8840041003079500c550781e55a429 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 110316798 1250 110315548 110315561
    0x110a06020a0201140a091e0c050607030c200604090c03150807170601080a02010c110a0b03060a080102161e080f18030a03210204030204090b0601030c02150f1504020c01 74
    0x44d41e682c444000440c0c540081c4264410076820010640710107520700c9880d4105d10748a8816121204034180002705036852030000c0c05403511035602c02c0d02504a61038501403c0c2c50108a580440c12480900180f03501c03041c017540c045901054002c1141100c0100a8004040517586280b01403481600402c058a000840030300f11603401d4038211035010550710302034413170b0000c0c0100340c1d141d0804a00703030026611a04050110074042c03911504142c200d00c0c005000c2e4009a4880e41d035000002c0100030760740c0740950100307004080300300013907190801c0f103000b20180760700350780f4020000d1b4049021240d6200b950080c0012103940030042c6c55450503070009509030364000928083d0007540c94ae1a5002a0402240e00c070038075a8907880d00d0341503941b41c071181c0c0c0c0148004004a04c42650030701001000d640c90f070141411142c00b445240102e42031141c0014166124038000d801598820038407616003840b6003602c0e03944003c0e1074040c1003081d200e04102081288274448240e50050010580740079280701980403d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 110318048 1250 110316798 110316821
    0x606190f0308070b07110a0312020d1406030d020307050c13090203060c03040203071421100f02120106030603030903060c0507060e030a0f08061302030c0f04180605060415110a06020a0201 82
    0xc60340b0b030b40e90400407111010764034039401d01604503004c0240081e0084402526071038492901504000c89900c030bc0045070b6200140b00c03032000c582030520849045c180801c01c1e208000744042e5280900a4031003da43d0212414240e0042c4c038610300c2c0da05020a02d61195030800d500809a80700c5040802c3c15000540080e40c080e032090064540006c0c07195483c01e040a0350000151079240920a00144c1043d003085a403854140750059003c1c4805010640c80340c0c105800000c8001610341d00b10390050329407158160810010b147c6403200c00c1c0003098003c2884400c49a100d8404a02c103000c0e8181241d95002d05200100406d08214102166000101c060010f03804142d40e10400014042d00481c0c0701038050703800a40150003001e003180b40b422160003d41e40291321070f075004d01d003104034118811154010f9200021f40300f143c44200e01c0b14003080c003402c4010310b001c449150601d403c0560403030030710851102690038040b641d507040007a01c80c2400480c09041e0080c40c215101d50940c02d019000c1d04105005 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 110319298 1250 110318048 110318063
    0x3c0412060e120301141e04020309071a0406030f051b0d02071a010810140613110a020607080106020115060e0f0406030c05040b03151506070b09070e06120606190f030807 74
    0x2c10381c01c2c078680b0803540c140c9801021500600b030031b040c84002c0d0b101502c00213080c010700303801150100010158103560031700c0340f403556955440d1550050880790b0350803190b54068104424072014040d5107803014030112030944126901d820003c0c0a8000b44251b4000400d804503918040301200580c50702c1c40d0407205800181c50400d500707048260200c4640703039030100b0b01441202c0800c415060003444406034004124000801d0540852190802d420613041400140d10000030070800d50b030704c020701c1ea0041903980002d0080b2100501e425001441c0d0b03000f01001c0040010b0500c1c1555904464003010a1300035004103c5a0344a0411180101e000e000c0ca501550400c20030800600340090b2002d010722007013104842d540c0b504500d4011342d0150042c4d0f0b580c005010312601020a1300d0880b40b0f0b024a0300c5800401845151510440f12084001c00d828803c00401170140707141c0c4400300f40c05500140459400c03441900c0c610401080d5400c40d0840b1940500c403002c04010030801e04020f02c2c0c1140550388 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 110320548 1250 110319298 110319329
    0xe10050a05040912050c0109171305010f0206040807030509040f06031106040b03010308132c010b072a091404050c0604180b0103113c0412060e120301 66
    0x41c0b1050b00d408140081c07003210701d1180b419640d4451800380c82d04048140c0003041c5c1d4215a11006640c40b4946d100106001c00040c00070180302c03840c00032400401003070a020045600707040001e5201d80c00100301034255240000c140003014403650480700445802002013046500e042110340003030129000071203070a081e000c0d030004c0360701c0d111040d941110031180309103245a0955a40904a400c0b50300e01c82d80c0032070710003030124080a003200491500c0d403c60700c00b0b0b90280003c1d48441703669003040e400994010b00c20082803010510031040e102c5180103840c2442c0c91445200c10710070290060b680068a0146040c50344440340750602d1385580a14007480455074202442c03030801240e4408d03885249482807441c5400205a891900014100581418001000b1190503006800f640c00001c0f11384070207070a42e010055042195440003408220840c0e80c10111345000c0c0d0794811342c070880c091030742c2d914150590700701004003680000040190711002c2c3c0c0c1c868407c01c2c4180c8040e0f0400e0142d200310002c00c45 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 110321798 1250 110320548 110320559
    0x7080906070201020f040504090812010b070507050609180411130c080c0a09031709090f071e0f031503150e100e21090405040302030307030b0603060f0111070e10050a 73
    0x1da17000c40c0d00c00791aa61420345804104401004030b00d100301d0300c800003440003000025440c1c074100d0081900c9411107a0303800061031700a06201890300320303612801c42840300d1641038551010706804901c03148291503c0b61160f007004018000360113001540301c80d08200e0b0003010880d540001d6031100068440c84a107849001640d0f015005490441d00054901c0301d081001c02c48c40d16002c40d030610b1001c05a80b40c140c1d400d02040c1952400c440c000c0b0420600b609100529070f1081040c901184c4070034038130f11442001d400c01010f050b000b40c1c4e11401c05407101101485e90740c401c8040030040d070f80100410180358914085c00050031074581e4400c414050b07a07075480700048550092000d190940c00c06407548086401240d1503000482010410540d000d00504106071240d2080e1406640660029510303442e06a00c000c00b510052041d8501612081c410320626865610340305488203000d003821003240c5040d02d40d161402c3c0c49903024010003003024091080d00d0700560720741c0040c0c1d0320035618450a00e0b100d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 110323048 1250 110321798 110321801
    0x130e2a01030e1009080c0f1b04020717030a0618060e1e0a0c050405030312090c1c0b15100905010206100806190f09052b0807030f1407080906070201 65
    0x21601c0b5036001111121180c0c903581d072201078024030070329090341421000d114003881c1c83d00e05c82c150070155100c100b0003001c01c0c000121071029000e04a50651904050750380b02c498200f0041c003a03022043e000b001182428200c1c1d08200050f22011017003410800c200208400a403840d440307800003028035903000c0303045800c1801404140d04207400411050b6114103100070f004249004a9900f0464184804119076405000520210071010006049403c0031085141800070a4002170701c00c40c1a050140440a80801c1c10818581c102103945180da44900314050505201e44501c0c0d804640d910941d900b803500482d0f50300940f9000e80c00c07101103036299801800c03158168011103000307500c0240081e0000d07610800003005030071031240108060100018640c00e4035000b041c1110340d50004082e880725240e041c0744080f60007618814907016149401e6004e810309001811030010152180c162100e410182c0c0c010281c5020340d540d0032085450f086c10300519000054500d101d2500800300403070b1016205 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 110324298 1250 110323048 110323061
    0x121209040b010f02030a2604120e030318220203090703050c0306060612060f1e0301150302300601030303020316020a020109060e010207080102120907080105010e06130e2a0103 77
    0x7030b60001c500e072480c107140c2a10882c08102c241002082980001000b61f0000181c45005501c0350700700078002c84c81d00340090600e51342e0750640c43c002d520501c00c1c07003111008014840140a026516141441403190301e01500d1400740c0c00f500348560001042c009401d40000750881200e0103030707003a180003e1030881050f49034a81510305542c480000e11048201c4c960f25413206030402c4005084070048640d0301d000c268090800074200e2013180c1c0255040039541000c0c041c152807910441d4010310000d055900164919520040c200381c04408141d0514400c50b00e0242103a081d05018220352142da545c0c48d000780a0f600441d00d2400312034010b0380c042c1415000042480005905844e5210217600784003044600807004080c41341140702c1d0304d10001ea034030401e00c003c0c0181ca04010307004a40345001078001d4545040c661002d01241c0c9040d0040001d80d03406084250019401c03141641c1c02050010010041c0c9008412540180104507100f0500010050a0a070004800c0e04440a44d8500350064045800c0c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 110325548 1250 110324298 110324327
    0x909090f121c0e010b090403180e040804031b0308070b060109090506030d05091516120206090705010804230705010305090102090d12020a0c030b04060621060b121209040b01 76
    0x44110000702c0042c2e641142c0000100e0000014070480a4000103044000540b0250007149003400345040c1e1004c00007581d009014000b41000150820b170f41c88516500c9036100c050310321503800f44150000c45110300d090004541000c0019124510303030410010103402a191240441ca44283c0003550303c00901900e403203204005d016142c80300c406441950681c0c80b15103529030100038501140040306400c40035050241c1e0003a101907404070107280059002d503604072440250342c004810080184800941c481c2a9002803070300500686840c50442000380200f2122100001c1c80218404181c0c1c002030000c013104c8003664284201c0d112261080e0807845410300c0309401012240c1104045a0607003a1107400444510443e0f10805003500c545000e08080e03002113b0012001050109200690207003401070041c0700b03090140215a000c0030040a0700741c000c0101221b0b100c1111501035036174080c0e00c5001544100c26180000d220240031001c03a408000020b20803880e00103410842d5202d482c14403007951 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 110326798 1250 110325548 110325577
    0x70f03050606090d06020d0207050601051503060a06030c02120a0f0e0f030a061e05090a11040203060a03030e01110d050d0f0b0901031b030f030302072010050a050909090f12 76
    0x10f80c994180184003480c1d10043c0c415603002c0001c29103071420b1344010541940101e0240003154100806c00c0608007200c2082d034804032040c81401160b070b643c032240b5021140d5506001a0a0074016410303810404000d8589100000c0410000600c68015800f40064540c95541c00b12000d034610030000f0400d584100b5a406034403560003040000c4044e4450b005407480c003950a40080ca100c005201035850407a07103c01c1e05c0d0004141001040500500c5d1400b40c80112015030451404601280441140c1c3c071016080002a209203412a405600a100800300c0442034030300c1d101e00d003030018100e680488494103400d8030301456080e548116126050000348002c0c55021a82d2a64584070002c43c0d0544812262036030f400760000000e0080c4014050031071007a1405611403240d400d100f80490801c040d04410096218101d100c50b80d9160140c20900e9070509180b82c50700c1c4240b208803814010140e41c540c01008500903c0600d400002d0f40b941348108203011140c503204021101c0c0b10900844400740401c8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 110328048 1250 110326798 110326807
    0xf0f0807030e0d050601061b0203100608060c0c0d050d0207020a09330b13080d020d09050306040203060403050a091d400f0501020711030601150806060a0201090c030506070f03050606 80
    0x60b032148c030f1402100d00320030040381203400710781d000682410903a156a6000071740c0c400041040f0b4109112aa44c070464114103d4100341d104605152908504560309080110004241c080b9a00581c160341c85c481d0060100d01e00c807600d03104c03180010a03410a02c00d540803001311a0034107540344003010030190700711550703148840703854080190f0b8140c00101d24906105100407010595003c10016844002c1e00381c0d008100c03070b940f0808060030302c0d41c0b15005240030390081020840540c8001a0190304140c3c9031600550303070014140708649040071500000e074004d800110000362482c0c0001940d0150880c100940c09414400130303d05040c204507500c2014400000440d07482044540c0030305860a4002e0582101010131956010308a0740401030072900d800d000300040180e0b080420030980500749a4a2450442c0c511100c09400b000008288601ca0100094400d00d154800c1d0806e120459010312880e42d5107481c0e01d882e580300c80c030447d45e50b0f0028a20042c803402d4507109029090107040060a05c5141 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 110329298 1250 110328048 110328059
    0x30207140f010f091a0403200c0a050406060804031d1002010b030c040207030801032907031b05041202040504080c030a05030f130b060907020f0f01062912040f0f0807030e0d050601 79
    0x5800e00901c147c046c4604805144680032007044200403c905181c082d01e60344508a01700004607800f60000e5001c0c0c0d203004030a00404e5042218a50400e805051502027511600080b4020707141c1d60801503002840c206c188a1816015000312000117030480a80346400002c0003808200c0c051404050009094880100081141c0003240c00d42549602038050300080340c000980307a0528262a0040065070395080302004480d0702203102d10071a01c51034441d00c1d143c0f4182c2c1c00610f02c03845004c003a1140e680c0d10041400c002c00c1c3c0b01100c624205074026a500c0e220304080241040e041203840d0350001c00c00a0021f42c21143c6500d20480e502d81c02608240c55840f170805012460200030922400c3d84168801c3ca10640410031804040e508240000700310f040c100f4101054801d01c10391400411002904910480c1c5643c00c20f540c48160011450380c0280e0362414241441000c1d0712001d0300031811a582102401441401072101600907266405051110070521a8500000402400170b42294005111 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 110330548 1250 110329298 110329343
    0x70c0e04050a0204021204051e07151e0c0c0806040c1814190c05030603030304021903060203013530040e0103050607020d050d050601030207140f010f09 67
    0x80140c01403040701c0401d8110f40c04a4102da000540702082002840308100c100801004035072041c0b2001084e0095480000101950b24009401007480b151042a6250035041c40340b02101c8454844110f81003071014280c10140031420912001e0b03940018071040131424090014105d40281c0e0f02a900d1000ca52a006820b001701620180901c4015101d1081c401140c0c07132001203600a505403a0f420708841d207000d0a80b401c40300881819401d000d400c0c41007050564010007501d90207601524011460507038403104415040061304014900707840440003044400070700d074160f0b0488540c0c1c8001c244d424031000d1403803410491116034014a501c1100d100f03091244035003141c1e0f4240e40b025181010100ca402c0c80c01145d81261300141d121038031680040007030000801c4115007207402070000d00b45601c1c000304018518071070701c40c0d54009162914080344660b48681c0c100e035451b5821030308404060150340e42d459240c0c5808110041c041d030800022034407400751449018039850740403a1450028200e12580135 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 110331798 1250 110330548 110330551
    0x504030b0711160608070315050910030c0605040311010e030a020409170408060a1b020607030510090e03130608010b09091b030903030109051e04060b030a120302090102060c070c0e 79
    0x4220050740b442c5050750b0100251008503001480480322079042440003010307480c0003001c00c4105400d10707900300780c0ea894032030702d29041c2d80094500c03100d16540c0000800c0c0040c0d0760741c03000303004071188540010030307a03405006002568495401c4404100c440d50044403110303259503041d949600300c1010000149403aa0013400e0492069803907800b504845a002241a0400c0e40300c011603810000810000b01114807503210808000c032008211060b80350380003580e4210060040051595590200e6044074403070549000400849000317010124154280c0d58498015202c007012070072000c0c20200c2c0046c01480c0b518140c4014030803c0c0e0078510010100812982e0207488100c80d02085030040500c0076910300114410000f0317000842e502d525000b501c00441d00e0050241d64201017541326050209050400184c0090300810007180e01c103130000c002800c2404c1400d0003000c44151a0341880401e4140e001b03821522026001d8851650b41d0450300801d07445824070082000c0b01185042c00701da070000310200e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 110333048 1250 110331798 110331811
    0xf0207060e0904060617150a060b19020c150406080709150c030c12030b03060c090607030c111908011401030210030c02030f04090515032a060c150901050c0a0504030b 73
    0x4c0b641607501e0020001c98a606c214001c03841d045410b6609004c11041c0000c1c1d00514041000c015843c58014012030700d001c1e049c0c0700600d0a50f090400103801d4420058101c23071520007005d05564509540c10040c140d8042e129440100301c0c03820006010f58094480b0004030361300c41402c50201da20102048448144000d421014402400d035880c000c203e2450460b11030300c40780e0b180025100300100070540b5000300102404c1040a040100418a8545206880320700e81d0500303041210207114540740e900501c0d4844a95000401d41800e0016140d203031410808596018000300804016003500c20702c00e078070900010390401d003500300140010f4441d600c030b0316040b852032040d00e080200d21140d14401d50701503803211803919119403e01003000f445030301d50020700308110020000003c82c4010203031001d4090710301182c2c501e241c1c04c0940e9039868141c101c40403211a1000c3d0f98205401d00070300460100d080d100d80d9015882c210000b100840170408039981a8215100c1c54240351555607400b501c408005d085 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 110334298 1250 110333048 110333051
    0x1030803090a050609030c070b040609050d020a051f09090b09012c0a0609061202090a0509030405030f03030109060f030b1504090f050607030c0302030c07150b10020a030f0207060e090406 82
    0x2950702083c424040b142c014800036014684c0c40d00c40d207070303690f01c0d14009800c40300e49284200720401c4119002401d24046030003c0e034100d00ba1089500000302c0c0080103900441e0015984480982d1074800340d015000022841e45491020790b0701c8100b00d0041355000c0804070b411400e408010f01c400000564410300c0031251449015042c0c1000e480d406000d401507981048880d2125402e208014890141c070001d80602c04c03c042c03a040e51a000070301c0501014015030102c0e940d031341c0800c20051082c411a070140c000a82115201d00c0d4048842d984c0f0750003440f4800c1502c1c5480408601006602d40c0c0da0203c03504074101d24086e440b0940340070641e03484130800981c4240d48189050008030f045000005250050300544414a098070024050b200c02a01c0e6004051042003040403a0314040c0c01e440c1f41076081300c0c1e619100304036040164000d005a4809651001c1c22411040760380e41e00243d0049000e00c240d80c2c040440f00e8500f801d0f40d031134006000c2c48012a01606159286050903184264000e008880 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 110335548 1250 110334298 110334313
    0x1e0117060a0303050f1605030c37051006061d060406170709080a03030203011509061d0301110408030307021b0d020405070516031e090e070e1f0905130507080103080309 74
    0x260346c9520801d66508403100e07040881c003c0001034042c0003000403480400107140c6501812401d82d0213144079103c0300021140d07501d0030101844400c20031000030400f5100208880b41d1207020182c402e400c140e0a03c2c84800c02c00c80745c007502d4100368003038804031200c40d160111640325400503400c02c000002d21000c2008001d0a001420110810900c24028029240141c1d00d5041c2034080307041c0182220f420701817012800c010060703a2350108101d0a1a100034425410302e40c2000b000030701408000350340390f918010205010400e440040000c41c01222907400b110340500050070342500400303003816170f41c0d4804000040c0e8009801d050b009168031001501d04249040c04040d8504040e4020120a400103000201c02d0070881c01c0d4001540c03140c000034201802101d24020340010000c4009240c2c204012810240701025181c9140c80e510842c28030b154850a8401160001c189508a109051040e40b03c42c0d82654001250b100d42c40c0074a54554480120740e0071074445070710310750018006894602c00d8a1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 110336798 1250 110335548 110335567
    0x105150705060c030f1f0302040e010b120c0405010e0103080d090201110d0f03050106020f212b0c0305091903020f240f0907090f0b1e0117060a0303050f 67
    0x40858030074070744075a491343c5030b00b0032040700d00c1c2c1050003c0c01c8240c5461715605403081c10240c02e40c40c00417680e0482d001f00d4990f01d01d444040c00340124a0340160410011320300c03540f40440101e0340e80398900c425a001c10003680d0700c0351f510a64040a110243c8034200800217030501c10002c1d00152545801810302903000310144542c0c52a0000d000e00c808006408400c1180c022549801454014440c510042c050814030521242e203d4010004010115100d01c4014040b04600717010780d00110181584e50040b040728000c0c1d10341d410761a161007142c00f840c1c40d0500944a010f4458140146c031000000d080032403002c0c041c1d074040c01465000b03a0641c1315003460a400c500b420022020034064064401c000b441e042c54001607014ac0c060310389050404100700700a840c103000a28401124568040892003010491181d4000c154249690713411001014412003440c00041c134040b5190004c1c3d030b5035101d00321510680000420265545c980c080c60300d07507040006c20301c91b00140400b544000c03412490401e451 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 110338048 1250 110336798 110336803
    0x18010b0301090b150a030207020306010608090d030f0605030d0504180501030c0303051303081b0105180606091305060f160207050603060409060b040207050604050d030501140112021c0f060603140105150705 90
    0x172010800641c000804000714201481483d00514460500500c14104980c556840d4001c034440e40c010181d07541000007103210b4a400910081001a0544004040e082c00050a0760320a006030803c0182002e110100d842e00d9119282c1260303041414000c0d01c5040d682c1c12549a03001c11182034680e48203000c04400310702c03110000d054581189030f0402c6182142d0000c1800e507030307001b8038000d4808401c1958400c1030300b002c2401940801c1c2158544600d42d20b1115188041c0d00c00003029100c1c1c410b480410101c0d01c162042c81c0d00030310100388140c2d84a42ca10070120783d11040303401503603000354041c0040354031410160440c0ca03110b80710f0400840d040d0400c00114040b17030080f40781035036136511110038441072140500203d16032426900e014401c9604010ad42203040c50510310f150304001015510040c000c0c208e605480e1201c480300c80205810207822505d0000d04090001031428503d0300c000020307800d0181c41a210003003039120010305079a1030001080380320355035104481d0745a8004c201800c0040d405 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 110339298 1250 110338048 110338057
    0xc04050106090f0602070509161407060f0b0d0c09020a050d021201050a0f0803030f180f010c080603010c171e0a06030c14010203071704091a18010b0301090b15 70
    0x242d0394000805180c0040552011031990006080d50804241071005071900849250b0000c0f10190200680c010144c084030034035002d45140410402c0458000200403c541003001e0840300d24005006d81d8400c0c504028a4650b00f80000b041d1085220007004940c145802070014101c01d81405414101c0c2001c0c43d034181d83c0708000700c41e203071010140140854940045088090308144100d80102428440460b5680c88040c0017607007940710840008091207132800c030781c01c090303080342c000e0b140105482c0107024060481940c985d40458035410020f501401c0c140304928110b046540c91052003100c41060014100e0007400c1c120f00450424513980c1808105000e0394000d4115a00004ea1a465810b001480c2d030450340001d210201c41c84242c0c0b072260707400010b40f580160000d400002540c101c0352040790f980324a51100c5945800c114a2402d180c01600307500342071a40540d049840c020680d0020381240740240122078610500380010300c9815256801a90008070250100540b5030a800c0d072640030b41c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 110340548 1250 110339298 110339309
    0x12040312020604021003020715020408010903080109050705090103181425150f03140108071403030c0a15020f0d05160e01020c150904020f0a090e0108070e090c040501 73
    0x50100104090103500c0c6100c034036140302801d19802c043e400102c07800c15540740f40d010150041035080520001c02c00d4010742540c003020866445542d2801c26019201081e015004240218000075207044103000e99842009241d8946261100100c01900180785403028000504521011400061200e000003220062020001c00040f0074119500602c4030800c090007408004083d02000007240c0f0254449003849181000211591581012070082c02c00c04101010703c10041c00008000e0804512001955450040320b04081d00300420705550744034000300d05440703901c90410180407a0000034001c1441c04861030162402000814040d040e410410309450800d540d0000e0140303094148003410184541c6082c1030f0b0402d2407800003c0d44034030704402141d003e81032a100006182d01d280d02100c98984000700110b48407000c0e081f180314143c120783c0d120808600e90f00070100300401c004078441e0484442c00c006019540c10f0a021820a0201501c030714030341d105180d84410255501e0041c68084c24 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 110341798 1250 110340548 110340583
    0x50c032e1118091501080408090310092103090c06030c11010e1501091b050306040b040911010e0307030f060f0f05180106060908060115020f03040308031e0c030a0c090503 75
    0x1240b000704448440c0107402c1303110a12251400b02d240d80d8106a503a0380c420b401a86581e220450b13480441d0400300203a5081040714900a080030170405002a1001802107403e2050700c1101d01c0340064040398240f41014112048209c001c20120b48281c000c000c01080d030345043d08500e090000500e0075240d4038580003103a40c0184a24141c0c3c0054004524018090540c0520040c4400303069030440d00800790b032420820200100066030740e242e54100c000300844c054000c00c110000760401214076000c02401d1030000b0118100000240340001c2c0860949800404c1c0b130407a05200e94900380200307250800c0d264029220000c102c0d1a5550740f045510404104040e4551800e000b40203d00310f54081d0003100901c2000801400710384800140360b41960b4944022040c60303000c00740140e1414510603c20001e038400010040104411a0003030750060b07001c0111090303440311520308003509420485008009000c00d00014003620f186070030000505c0380c90308046680c03a8407030020a06000c6807511381003095 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 110343048 1250 110341798 110341837
    0x3006060302150406120c050a20070608090106050d0218040219080309012a0f0807061d0f030301032a08071418070203160501150303030603050c032e11 66
    0x550304100d405178074075540c0a08100d400c42d080d0000c0e00c2c0d806141912010488252a6185801f81e16150000c81350752540840b552070b0343d550b6008102c4181201c40c01c4e0309500b0450000343c076041c101946075950398000c1903103c081182c58148182d80d00001e009076482203410407011f00e442c0440381e4210140081d03078003075607440c00c0c0080054484800f2144010980f5640080c41d1320702000407c1240c0ca1503444026502d050b00103003824900390080500c0500290f107402c3c980c08880103149807041e48003a480050761010010001401c0d12030000f440b019191102d00f00725000d0340c9104400024070b0007110a904274130f01d6101c0b5a02440d20900790880d4000c030784103059121030351501141340d0303481202088a03440c080c41d000790001c0d124025500d4100c0840710355140f100c200002904a2580700443d00d107240b003926680e0600401500c15440141e405025644945540b4203001c10f44e041c4c22088915404d500c109040c4160a541c0320700b6180040c119551000c2c00c0107144200000d102c119107045001181 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 110344298 1250 110343048 110343059
    0x405040b090103170a020a0602030109091203020c2d0708100b061c0c05071a04030f030513120309020303070c0317040e070516020d05070f30060603021504 68
    0x3161014038a052160101100400008449519254510a08043c0140c48401c0c07240264506440e510000702620700200011034002680d60150340b0240c014140c0c0d00b0043c1d0001c0007a0103d208040010300c00d40c00041c495801c412600d802c07001070b40d40c0e0186400e410219000600d09083d03240d0441d120719084440c861282105a007d40181540f08884080c50451440058012900d0790220441d8036510f0340030900d010760042e003e9448040d005080c060302d0281d009072500355410129402c03408100c81010110400c1e01c83d118440c880d80d2204141c03840446162031300301010403c0110074040580301c4440d0001070720301744040c12190381700380c924a84440c250300d008030020342d981e1003049a200c0d05000030010a90b040d64000d4000310b190809568035445407003034859a525071038010350090a003506d04803c0110000315041140e1440000140c2e00343c64610b40045208440b594044025100000100030713001b030090b841030309101c0c080000c5c000b980d0350f0114040f0b840780c2e07050010380040441c0c01c104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 110345548 1250 110344298 110344301
    0x70501060801060501030e0303061530070c030c02090415020d0504020a0605030f0f0912040b09130b030a150e070b0a0f0f08011e0b030a0603030225060809070911040504 74
    0x1d01400d01b41440010241c6810790f5603400001c003001d00c1080c8071004c1203004001003084400c40c02140c019405078002602741441216800540e140000b240b0800160001d03220b8074904291a07450b9803644072282d625000c11252281c00341042c0c03504020481000002e030380c2840140b010288450000c1503614090040001161881d4056410702004104004011107900303000c3d0b42c030040185003903456455564207a843c1c0281000e150030100c8000401007014503007040074210312030084940c0c81c0415151118801074410524580d60142d02801f04640001c0360304544e604840b02403100002da402a20200500d08001030340311034050000010250205039010101c10141c04c12420107400d0600354079801015014140f082c60000242c8080422440741d600b401c02c0014078400640c2c1e512418000305c140b000b06400d100031400340c4110b852000c984800c040100030f428100f00b92400d1114036007041550000c03801021020b0500901d003020542411a01c50360b01800704a440003034655042005200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 110346798 1250 110345548 110345561
    0x7081807120507151e11031c18021c081213030207080303060d080a0c06090804050301060e0105130b010912030507030305090613061a04050103111503090c010309020a0308070501060801 81
    0x14410b156000203034010b032085e8400769100d8503003d003010407943c040303605400c00b4a013820706000000780072142c203010600c4081039160b100400c001caa44002d81c42e4106010041000790054521100d4aa44010240c1d220086c00d000e113102514200040704c5035072000f01c048841507030b080541c03440c00703042c1941044400058403214000b180b85040103030020381400b0b100e4100410102d030006684a039548196000c254040c2c1c040401e1242081070303d8442010342090240303078040e6203030000c00074041404a0b0f0079030407560042c1200e0300300c543c602c80a01c090b04010340c000d810b0003d000000619800b58444080f81d140c080d0707580c41e48071040d03032034001e040d0390019081040503480390090062440300e2840b0110f40607400240000c41c0e58443c0300219000f00e049441e554400c2c5004000410320000340e0103880c00c08001c0702c0400025031402004881e0f0702056a0b01080c9a0201d099801d065009502c0030080600080400c7e0a65a0380d55030720200f5031144030701315004e0751075120400c4980001d01414 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 110348048 1250 110346798 110346809
    0x90130022d070501150e01152615030c0f090a02040503100f180b0a0903030b04060602010213060801030f0b04020102101a100516030302030613150303020c061207081807120507 77
    0x640a500c3e005005541380018040c02c0c02d048c0b600640e8040301c5000700f805400ca8060008000840c62030a4550000082d0407035040042d0400000401c0c141d1401140001100030010003155018038601c0512200c0d040003801c41c00d02949c00c01010039699420001184280010b40010a401c01000e68035810340300911030050a151960418030b000401c1e5198080d4010342c085e41c0020407501e82d041c11009448089040c80c8c02078503102d0007041d85681034008000d55040c12405031030896035003008407500002440050105640b1031a494001f86600500703641041c0144104e64120044603500c1e0220303100041140d200c5200981c840780f4900340b0003a02d52501e6030900b001c6042c45a0b0840400e50f090074250010101136001001548559600b0005180201041c80400646040d101940c001090300d01003a8090301c600c0c194600a850190100c0d8403101e01d428500c091a205e40b0303000d03103281d0b002030701d261080300c0d0812420307160100410550000f46414075a40c440070710381d800c2103810700f03000741c102 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 110349298 1250 110348048 110348081
    0x240303030105090105011b02100c0b090c010e0112020c03280c02010818011d0304030c0b040f0302010c08120f0a06060309051506120f03090130022d070501 68
    0x1040b00e0781d038008803641168828205401000004100c500c00c000f0791803c001e5224a00100d01210160f20601104d60b8903c9020042c0f00c3d5107648501d0f13640d5261303c840050002e607011a0b030b51000c1d440b62181e00c0780d02d00014005400d08442c4a4070398110f801850300d10345c40031030100384294200d4038000c8540c00414142041c07440f41c06660002000c004008000c1460021507962912668100354003650700e0b071a1a000c600143c0d0746000455440b41c2c420700c02074030180160f64010400c41c850904075003c6030302340140b00780e5452541c0d00640b604804400306540b5928280f04280c1810140d0003010303c11780040c071192400c2d2400c403600300102c82c000d0300164100751500b500080003400002c0c1d035a4200c44c035203400009580d2a035001620b4030000b02c0428006000b480c2e50401b9a400000c0640f039190301c2621080034140c140404000b880da80c0714284c18413500400101e000310300b41070b4010084515000081c07469078080c00300d048030303900c0c00200d2103600f5440010a00f041c0300c028800c1d4210071104038103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 110350548 1250 110349298 110349301
    0xd030b0a060e0108010b130302031c08060909071a0d150302131503080d0e0f06090c10020a060c030b04060b030609101d090102070c030506040308010801020408070b0304140624030303 80
    0x20510b003014040c40e4182203000450400484890501f00b002356801000c44002c1c0000c66014400e12071204481d20104030213201180c09443e0850352036104d900e020008010443c030b030007140d512445c203507503c0b8111590100021541c0807540d00070324515245860101d0410780c614818407180c070a0215600300ca40c0d2a0001d40b207080c0c944440010b0480f07410205441d16040420030140c000c0c01d4840e14201ea51043c04c0c04080d03054400700c0c0d00c62080d040481500e40c2c240b03440060003900b40d890301803031005805c062a807000181240d4031030707241e6190070724002510307289170004a030440d1000d8208481d180c5001c0f040003c1c5141c5910110f50000100c02d40e851110f2034062480d202031003070903009440402110000b1001c1c03100b5410f5820140e04204c0b160310f0141c0d80c3c24141c2d02e0b003e050b0360580018000f0000400c0c1208140201c6044502110040900c10315209071040c0c180c00c06403081311382007071070b0800c09020082000364500a5203283e52487c2800c0c100c3c81c442a4580c40e92007034034001d410610 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 110351798 1250 110350548 110350577
    0xc17091603021311030424020403030e0904140f0a1709030c090a140f04060b0306160f12110a20070501120f0504030807030f0e07030f050f0d030b0a06 66
    0x40c0410100c0703074103032034144601e26000019006020003c90380595898040104014402040860304000142e00e100d0341e081103480182005901c100d01024000c160441c0d02c403078413414900d1140783d006008048140e00c10104040740f40c00c0a444d0007841d5004c0c1c1c004454078090152107401d600203080f10080e00781c0340c4a0302901003600c6650000002d44628a1030340021a4000550010070003050900700078035040c508501c1a0245000c02d580566200d80341040000349410005451800740c0c2000c0300d00541b066480e2012540d2802102400c410081050001298200640101068228403140399911440c00a800411203908142c08a40320500c0c01c2c44800900000329000c001d8840a103407415030a034509a55001408036100d00050581c908820001455400031000c1d009803050383c0c0a102141300300c0d42140a8030300c9503d071302000360807aa03010400540034200c2c40c00400d2240e0300ba035807400810305400e170520b510815900046511010444468507204070b084010301210b0510016242605 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 110353048 1250 110351798 110351833
    0xa0308100f21050304090c0504090b01030203070e0405133f0f0f1407030306030308060f0604050603061801080106050f0411090f0415060201060f08010903080c0a09090c1709 76
    0x2401920700c40030046a10410f002040c003c80c0c01610340503109104444400364028013540c006e218142d26145006081002c5621038000c42c0e0060b98656110014081d40714100401024054801c0112040c8100080002141101880c17031048000745188a0010100e00980ca0742014071182e0011002149039640300340e030081000d5840c10300515180324030701e070010f800b034401e0301d2034a03500d00c101a000325214003010303415080342051b0391082d62010f210391540414000600845402240d1101c81404244100c1c14207001441e44280000c112040c480c3c0030850700c0c040c401d42a0440c241c56511244103210609049494002070308080d902080b044a041164940c1c2c2e02840140300e2240d4000c124203c10b0787c0e640d40210300035607421850301d01019a40c0c0000b034000c0c802403040003140d4204190020300d100040c0301d071030f441d150941c580110035599007007443c80701e074000e00c401000d00c65620b001240b074041074480e500d02e5040c10b48400e5600c03040c2d03a80f881d1200000030035661560780042d4829420103142c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 110354298 1250 110353048 110353079
    0xa05010305120a0215010b0703030e0f1b040b0a120311061e04031101061d010b071a0a0204180515030a200d051009032a02010c0f050a0308100f 63
    0xb4110070303240c1454400490429080c24080e0140c50540000440c40101e4000140006886524200016011004455290b003d103032020030240c0c0080e900899805840c5040c413170420001000082c0c2990801c000827804491038220f02c1c000d02c4000e00300010190062001012840385100800346885d10b40822510710300c5414070b42e18181d90b00c070003080406029068070102051700c40020b02820382c4400d602c0d26403d107034a00c50742c41c18000703c00004070003030b0b41f03411030f4807007500700c0706015101c603292501106040014250070000b55080100041c18a0741340100d460b032040d40940030800742070140c41043c5407000700c03001038407a400c01c3d01d501c0c2c009924802211500980b458082d0502e5245038009502c4c000d2040002e020390040c00c60b001c198900561002e07208522135201c002024288501501c050f2940e010503081d1440070b021184050f6008942d00c44826100e01c1d08007511621a40e1420b0411440341c20890210b056901841109000464100068071107441c2c0c002000340b80145080f040c551 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 110355548 1250 110354298 110354323
    0x70302040f120f0501090506100506030402090f100f0e01090f02030f071b02120a120908280f050c0405061002070b0702060903120c0105010f05090a0f020c0d12050a05010305 76
    0x11280101001c122406110f40030f1250803a0007045541d0540c103066071103040c111503219900502c00c6000c41e0314580842030320702894015000240b2a9100410440c2100010b440700003031101c40100003880c140c1c1c008e4084042c0c403400104c0451540b428000105640d40d484032601140d00600c100300001190018131580807203e4a0701107001d08008034943c484142052010b900401c805c030a04600c8140015403460003031203020324103591401052b0072103200700d0034003c004940c2c000902280703c040c1c1703003621070340e031440d03010803483c42140c09944000560403600000c41c0d683c1c20a071440d4110b803070148281a40901e05540c2052415600b140c000d440712101c1c00703200c0003188081041d409545078081918000480a001c40d440c011080c0c3d0060080e412480c001d44466090a001003403440da000f036024111180503100440715151658440042d004100d072000c0301a60030700a16265039010800081c004100d5110342c0800351190707101200b542c40060814000034200001000010030000301902000b6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 110356798 1250 110355548 110355569
    0x406050d09062301170a050a0f050c090f07110c132406080103060c1b080d11030106030c0e0301050408040302011107030c0e1909170a020c0303040f0608070302040f 72
    0xc0c1c40d4540400204082459440d40302003040d1210030007540700c40070b40d0580303c200005c4034809000c000900d9407103a17000c3c00140f031078214020080000e4951030365550303024440c1095a40782c480720f00208540840c00c40c0c4408941c0c0703000e02030018482d0088981d401c6102d110010b1300e1300c20b0103240800c0303989406803410801555182c00f1440c00c150303803e00c3d103c02281402d1940120a070344080040c2110340c00c0c0020f0720040d1038200380701001c1b40282a81017441840f450b51407130b1540c03540c9801e0000e42181a009003616150b2601e80e00d107890240056001c0c00682d100080c581e161000010051601c114a680c000d80c940024000400c881c0c10980d400c9a9092038140c11880071040290708142481c0c0c4000e0070703034101000110b12007030031420852003001c0c1c40c0f1903620100c031003240c81001d441e5011009020b207076000c001e182e4418500c0d0003c18a4580b140121101107040318003003132455100360301002d4020300d034950620030154804030403a04460140b5041d800c15003401d603d04903c901030b2180000e404e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 110358048 1250 110356798 110356811
    0x1112060928061502060615070b0610050913060810051e040512030a1d031305061809011503050c040f09090c15030501030b010815060402030417030106051e0406050d 72
    0x1591a007050000d02000f10191089100002c0d01035950b80003075501c41d00c22910030b248114000710780d0040c1c07a0482c0c2c1201c0464000d450308410300064605020800c800c11104020034201500c800c00c0c6445a00c0000000080c503038a4840181e007403229102246001da42044244110302400c100c04409103805015032140030b031603910b041841c141c4c00411080b0f081d0408400c11140300e05a60020120507111805070860008070700603e80c40c0e103e01c03400401340c07602508017840203040c0b91015201c0007080c0e01d80000c03001c82c5500040c1890009030710020036034545103c0c613044a07030715005d2a0382100e0310b50109400c00e8100b087c0c5821452160140f02541d90351150b0920600080440c801d0061003054038034100c080750304034010003805003400181c50340032140000281c8108001041048036191200c541c005480f0541004060360000e00240c8110194140704100d01402600660003032001d502e955644002e00d4005110311010080780d03110034001840108000f503041411200c25484402000402 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 110359298 1250 110358048 110358121
    0x3032205030a0602091504060f0c110d0f020f0d031e030207080309030910210e010905010e0319030b01270923010e04020109030f0c050411120609 64
    0x8404154052585803140100d160300b404256070042068030320655410650f400517205600442c811f502c07502000410310a0901d481074801c12402e40814842c55064000c1c002c907200092488036041c00690310a040300c02480c045190068001007682c0041e900000c03000ba043d200038010041c2c1c01d0181110f51038070084150164031903412990380543c0a4030a9807a828102041d0b80d5980050030b40c50300442030b0b59101c070b420900642a10601c041203c81504066a100f1070900c040c048500c9602ca6540d00c03080c9407800100c4c03c0c040c60b40c80000d800300035602d428026001614141040201006061521640c13001e2039902208400020f0400701c201c012100108000c0b4082c091168440b1480f40c1c640f400c8906400c064581130f4640400d8604102d580d070b40c9032900814030b00b07000e5500a011941d00e020400024041911200c000e0b40508499004581d0f140041001d84800c0302c02c05503075400001d11300301c580900e988101e17002042031390f6060300c0703180c44040810b0100740400a090800e2217050344006 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 110360548 1250 110359298 110359357
    0x10e01050913120f0809011a01120213060206040b25030507050d0606021f3e03010f0906061b030e03190501050103030215090c01050f04090216060b06090303 69
    0x8a09070b10480601c0f074500d00d0b441c010502880c1040702000101500085904400c0c14091201e04807407400c0004004946500191944609101c0c0c4801d0700d9000c1c050451146207030840d0b080280724903000381c403007440d05140852541d2801011006c400c11840340340003000e25a07070544110320b039050800151580300e00c04141e9943c003c000240c40b4281c249540400d00c038bc0d0200d001e906030f051781b40030a44800a0410803500380c42450700b10500070000c07807107484c40c12841c09510203990586200071741200d81c04a0740c2c8400c60f6009801260711002d4541c0c0402000000e440b4403002007869103007560300041d4601b01c49040741480400a410000c404245100742c3c2e030184403016070710b108071100314504051440c002d406400240302c10350141c003d0101007042c9080c81560140306484c9c001c0a055400d00d410015195078000c0403002003982024080030880142900c001c00c08141801c000e502d0241c0070b40360880c10344d981a42458007505050190049a842c000166050090048140143c0c01180080e005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 110361798 1250 110360548 110360581
    0x20309040f0603300f0e09100b0d0204081218040b0303090307060c02030c010e0105040320090901090507060e0f041805010504030c1e0819030f021917010e010509 71
    0x50413820386055602c02c18080b0051030b05804410301e42c0401100c21003800b507614408042c05d01d008110102a205814a4150351499109184c100b0381804240c5a081d0b1800316080001c01c90401c1e640060b0034041c4d10030400c102003650300044c8100e4540031102d8203151070840524489400340340c070750059180729501070040e50080769000e0111944d40c0d42d03401000300010740d16802039010780100d9202c00141c1d4030410104001c2c0308103071601840d0914640c0e40081c0704107011041050b030710388000b0042850743c44010305e500503050b0307a0021070280b42600f801420406107a0101e01403254540725100b150701c27200d40e0780745080000c54000981207407072107041b00da0000500c00100b2552070002008201a0006002108036001c0d50080c5458031110b0303031000300165422000303000440c040c0140740441182c0d080b580d144011038034011039001055500f22050760000309a829486914101c0101d5441d4040740c5825076601d110305a8203035514190b64031800d50418040c441c059a14840001c3d41c0400c03103070120 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 110363048 1250 110361798 110361803
    0x909020d02040509031c02040b300c040510030e060606070507032a0902070b04020d1a160e04020301210c03080708040302091303120b03070902030a020901030c0c03020309040f0603 79
    0x1440f0a28141103400c2d20ba6002c04034400302c0707103e00b08080b2091286403003a241074a1400c0d0f501803400243d84003420710b02c258920001e09103c40010201e905c0300c0792901c003601500f50170104540f04ca0429040050f18101c1102d13110400d4038150f21410491000121580c0180f01550002da82d10003d051941c10070350b4a400280c801d020541030035481d0760b2442c0304950801c0f44420341001651700ca0030100140d00c20580302800ba980580d01290141c500b4607210500944580b071000402d911003400038084610071201d813444090020151528a41c124140c04c101c940100e804500d198180b60354403614520b030b1a1840311500d240340c24082007005511911001d10781001c0036036103450700780c602070322298404e01007280500a14808181c140300100205414203506884907940c445407508070030020280c0c10959a8588100c04001625203540e10055000d544100009690f40b200d10f00094191008101c0701002c00103419a0240880d60100c20b80d48070100403140401d42c814100c2100010b8403480c2c001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 110364298 1250 110363048 110363051
    0xa030e06010803040815130314090904030f090504090309150905031209030106090603030c060b03031c0504050c060f040b092e080711031e13030c06090503070f0909020d0204 76
    0x402c5003140000a00100ca00d21412650045148103000507092420f8818a02d4003e08001250000b4051a0f03122079008a103008641061380007030008076030520660f416004101c000704030102296000000e4005132600342e40600c000e1040d640e00500c40c2d2043e00c1100d11100250f222008000e1042d9407610007000001d045030990035a11101d59125448041424403940c60b0080004100010740a0401100d0b01070700e4480c2c011149840da0300c0070780081680c8540c5800300704800c030720140d0031810610301050540000190703072400d0300c0c02e90300d041b0864018078451101404130003038aa54000c1210207031000d4413942074541c650540851040b101b031420320b07094501e86203150501624440d86c560381c068020b40e104401601d1303185080d034407290400c1c0c0300c00aa4000300048035640e907200005100070051104164503040014116007198006900210394440309000d042042e181c1c4807040c40050a000c4000e48542d600e8407803985840d020511072050615120f000070802d640d04c2001840d40035030050700 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 110365548 1250 110364298 110364301
    0x50702060c07030503040608010815010902130302090a0e070e04021c2103050405061018020702030304090e0106030201110d02060a090201020f06040c171f111c09060b0f030705060a030e06 82
    0x10405d131a07170800d0007808002000c1c0300c00001c2c000301c00180704104400c401d0f140a030340d908204126003e580300c191544000c03240c031400000144c891090880c42510100000a40c0018001d810350a090542e0310002e6030100d94018040541d5400c8020358a004100381c184603000c07114030340442c42052100c0c40102d411040841c0900c0150560440da2050744104241c403440c0d6118000000d254101d030080502c2c0f100c10050340c02c05581c1c00e40c002d0003103500041c1100d091035640c460b4842070b00d842c468200d9103651902801c204658011883c030a002c2c1035500075140d541081880296510710040416100036100c07044042503900903c20b6414122240d0305031091403900b401c0030503c00f4030390b00c18075105003400f410a000c40800856458141903d648401e000b00c0250746807030f005000f01c0900301248409c10008101e0381a03540c2c1c00c1156280306004041003016007400c00a04a501000c60395004080c2198650504d9030086414010703110122103071034683ca8402801c0307000304900b40690040d4440d440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 110366798 1250 110365548 110365553
    0x22090503030709080d080412110708010212060105071a04060f02030406060e13030903140f03070302010c17040206072613080f0a03022116030503041704050f01050702060c0703 77
    0x1075100c0e0740c1e40d40703c210355a036440110a503501415001c0318001041d41001c1800175280d801c00344002e1007580360030480388600400c544c0c20901158007080b0b40341e5001414042c0c4044440307516600c4802400c00034140107890300c803e000786292413407011710350f1045000203080100603402482101410001152249401e1038203800a000381d024240e41608244c00154800d25031803960a00e41c3c0d0315640d4120250f03c1c507941d825519866042c0c280960040030595005030070104050024039001b03900100340b600044201034800009400302d00214901a010840540c884004841c4000e80c00f00c203c0400882c0300517211000700000712500c4c0701843c006020030b0b4424442d443c440a69420f0402c3e0b955901544020569401c010300d40100940c00c07070380060441c210801c18045d40000450340d01441d000400c0000f440e103400303061084000c0b5030b01105001c02e2181e0392803070202ca00400c1e02c06604d818101000100e80104a1101c2c0b4108403001400d03c0464075400191016a070006045400d50f58030391 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 110368048 1250 110366798 110366803
    0x110a030e010f1a0108060301110a02030706060807050a050108060d290a0c0915021207030f02010506030a0b060409030504180209181e060420040918050705220905 71
    0x40320400495800c005158010820a1242c0e804a40d40c0c039026001c0c03800e684005589801c8028901c55040d582c0c3c0d00c80140811400e0000c1c090710450398082c55890b12180750041c100c88440e040f0002940c031808040c0556110002948103458003400c1001e929505d0700d00194450961000040c000300c00e040c2e252540e0082409940c5110100d04910b8400d40d5840e10b50508540034a030305040001c0c0b20180401620941e8680140b03021150320646003040124204d460155100c02402ca0001e8a02155842c41c10350a1145541080303044001d4080751400d80c40c0c901e10207001801c020320456179090300d801014002d1040310024200090440303218543c1e40c964200079040002c0a90150781c2d1807110040c0c148060300302c940b0480307041c0b0f41c0702a0840381a0300315101240090049410650380c4801d0118507104650b40b206441ca0401c01607943d5041103020403d681225200c04000c6d0900c02e10000021008228607007621401d58a102500c09242001c007064103001c958911003904c0c122040042c420b01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 110369298 1250 110368048 110368061
    0x102090406060e15030c030a090201121103070f0e030709020c0109051603030f0c0507030b070c020616030e190513021303081314060307201509060708090a08070303110a03 75
    0x484020080b48034445030407903144006ca0300c503035122408000003601003502e0350280a480307006141460040d030744100544c0c101d50283c68005a004404230810200543c090950b1000502500c0c0013404c00271520080703a941d071290b004155030b031900030455014001d02540911401c640000032900c8888900d001d0300b0407103050740425030010303680c241140c0409004141c02c0200e203610000801100d440c0d5141d5100300c074800792010080095081401c000341e50b4000181080160080d0302005141f0a46005800c0d19820885075018250030850f800340841d001006004070349040c0d131140e02c240803112101b8024071821108060320300a080d400700500521001a003150780e5000e4080c100c458440164821201c0e40c0515294003002c01c00010714105d100340c004120150079041d924074508015808142001401c1100001800340d51041090020f02003100caa00516542040b4000c0d0034507000240e20b070705904001034159040080c0071000c052207688001642101c6400d01619000403c1c0010041c101 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 110370548 1250 110369298 110369327
    0x90303180f0a1712070213050c040e18150c041a04080303041b09060302060d090201030e0f0309130203060108010509070c080d09021002060606090f040f0501080105040201180302061b010209040606 86
    0xc2c13211541c0024059008031040a90028611402014241c1054021380802801c03a402800103110000303e10712446815030082c10300f1b80150252040f1070f100d192a04003141d507108040420a410b00c011656410200c5065407201a92610b54280826084005100301c0c0d010300003500c000010001404500404030084904541900c6100c84e03898a802d02030342c1c0240006540b01e541009411040c500540c000f2500038418140460040b0080d41e0590410b034103074a414004d600002101030b424901244415a42c0700a1a021421400c180b4002800301005000d900d020308031070804100214003c402000744aa40210019503510419003074001030140004124024800008500c40385800130444a208030f1000c8c12003420111071070100700740507841040303194201f0740d42c050784440460309001d107a011702030400020605040c14800100b80018041c000103000803403400500060780c81504807008032121480403d07150702944031042c0280304102c84150700a20741f1000284181d00070031000710041 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 110371798 1250 110370548 110370553
    0xf0d0e1203131a041a0108060c040608071206060e030d030207050a02012d09030b0106020d1d01031401030b0103020a0b0f0901030515040e0d0201050a020c030f160f0c090c0302090303180f0a17 84
    0x2640d613a807603940c0d0780c0c8c00d0740d0300f0070403200612050040c54420030310140d12814900d8003100d02112510494119030482c0c21520000b10140b00000f06800c00f04114250401c2c0d0b0301d8110303e062955114142c58182001c0024104495401c14100140c5508c000c040042c0500d08913070b40743c40e42c4020203440c200c0c0d240b00444403034078a130000007102800031502e5090a0100e45540d000c00b001e171444e80e91031281d0500c0d900e0500d07545403100c4c004030006282c250702941c81aa420610340d410350042043d1544103074010090140200f0200b04c1070a50003041c1d6091900a00700030400780c803485520080040344040e03141e005031404040810010001603081410b05064000b0482c03500d814880c04280d2290400b40c0300160301c00c10183c80e081c06580f0081502c0b03c240e10115807500391503a5050380402000d2025610304400b11400e01c00c0d00d4040c4a080090902400c01b18908440b04020a880303000e1801d9030380020005074bc00307181545460f14045400d120003484004040e0321200c0300207401044c2c410b03082903403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 110373048 1250 110371798 110371801
    0x311240f0a0f080f070309050f03042303010209060706050c0708070f11091614040e0702030403061104140f12010c0f1713140c060f0d0e1203131a041a 66
    0x9402020030f68010303489003685105030780c3d4000081e40584901541200c2a224806919002000500191014040c44000d0021030355022503030b401c0324604070b00d48910070391040090310202c2c1c0d11307501181c0707400368440070101d405e0740c4001c0c00290b64069101c010304005000a614020003050031040c0c03a103035202e5006c1c1c000300c00324042842604241240e00b10755034a0f42c0382032684640e02a0803c144000c00c440c801901d059240d2000c801300f003c05075020405644003040034400c12455003d01c28480c0310844040b82403901e0a0701c0f00d800502e41c2208a4024074a031400303807140e5101c40003006400420341c0002c0c060300d40880c0c0300038160010074249100107540d0585160900c0c0c001300409010307582100b44a8510360300ca40b2041468112194a5211482170446050190711080c010f030107002c81040700c0035142c0009203542025640c903413201d00c80d20303040400030210b81c89403c025a41c024400140c690420141850b001129011030794442045c200d1120800040200c09284006815050400741c102ca = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 110374298 1250 110373048 110373077
    0x804150306080d030921020a030801080f0c2b03050a12050903040e0c0d05010e1611060c0a0c060f0e011107050309010c02040617060a150311240f0a 65
    0x80301e80600600706990000c88441c0f050b54401c0e0002c411590058a07094a101302064904540107240c080c03001c05a042260302c0001d041e007110000340104401c1c4090503103406140c10554550080d260340078440c0030f000081401055003820710f40919004d108030b910311a0950304000d4100e4203d4000040004c40918880030700909038060a4002c00320b2400031420141043d8506160410003000e510803103100340600c5000d0b5881c3c0c0101402419003014003000d500340704500203204011039100009100b4204485040107800203140d40c1c0c404a80400151100c408050031245101c0000016081500700b842e4540c0ea41a15030140484441180007001741008441c45a5598000d142019081e604207000b406141d5004804003080305100030f100003007050b252443c1340a4180006000b200591000040000740d042c0d0740b1500b541d09180388601c004c118a565a450300c1500091485400389045802e912072141a510040951005000f082525000c40c03d042d01c01c50f03001100200c0c0003400240d41d9050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 110375548 1250 110374298 110374301
    0x206070507171906021809040308011a0304050606010e03030d020d0506040b010e01020a060e0c0d081201051f0c080c03070f0c05040501030206090f01020708030d0c090f121403070f08041503 83
    0x40f62079002c003580ca18031001d61038560003034110405050150072850880100390380d56403106c41c440c40c440e489812095061481b034010111000d505502000401c00a00012400c0060401ea0026013480c201c680b0030186404203080d07001c0c038481d03003c1503400820200d2008038281c000c3c52094200b60f80070030080c00c05c04c0044501c02c40c0c48010b40d0250f08500c240001242150f003210404c02460b40843c4c200c0d00040707021564007080680280c688080114401102580f081c00301c50040c8422a88000c11010f42e9190500c8401c2c10005181804240302c081e8040150610544003280058030903651100c91a00b0002c81000d10804102c3d1394800b524400f2501d46400d11555051f690081c20070b0381020300c44410311204019165801c0d041d8130840f40001811107040001303001c09800c3d04000709a186102c20007801180381c0d40c10480f1504034000040c0038018030b003681080400c7c3c1181d290010700e200b582c111825441100c0020f021040003000c10000c2c0300107100248201c036201c03510000e582401d00c0d0304a0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 110376798 1250 110375548 110375563
    0x201020f032b1404030905040b0301050405030901120b090c0307090905090604030f03020705060c09040609060302100507170d020319051512031b06090d08131b03020607050717 77
    0x1000101108001100b880700780c0d264240410300708000604400d5100454101c1142220b04500081c031480c024002400d1a001c0c0004250096000b801030f070a243e919680c0301d010f8407911904100a00c200544001401d402a102a0781d01816405641c00d0000d0050301c0c0340e0040b141d4402082c02440005403040d4035101d4584901c0b07a99014000d291a00c5d0340440d03a00912100346001c00d5028000c0c84041340050085e14080c500b03410005656482640500c401e90758103922821001d40350080800150302c820130620940301847c40c046503a904a49404100e500e40d189182400c4800030a00704074080c195030095003d18083c4505041c48031210008809803034048070108682000f8507075030007440c100154452085a2844180c0e07091040300c04941144402000004030140d11207800d00401d580e0904c01001e00556074a4954124644444105066140b00c039008103142c094480b1101c8554910b602c040195034000c01c100ea1705e200301d0a0850362814a40510302c1048070080251443c10000900b90 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 110378048 1250 110376798 110376817
    0x206160b0c030f0c0f1b06060102010b060f03040f080412141c051c06090f0212010f0605031302030106031e0b060603010f0e0a11040f060801120b010b1803060a090201020f03 76
    0x1001aa907401d0b0505400e0300200810701007040c5c00d21000900c8020500305040c20100d0700010482c0340b800e20002030a41311640e40490184408000c202110540c0c1c1e0200e950044d0000143da81142b903c0c0b42c184041c1c80f640c0d1001c2d04c155901101d100800989198005184a4150482c0c03007141482081c2080c18158921140c0860000c0082480a0003000c07001ca0100b40501d02c0050760541d20565641651380c0b060903c181c0c00c0d80060803150020404002c3d03405041001c1d5090704550074440041c0681c4400b801104884245542c00c0d411944d0940003c000365511103d0718070080d07140d2011810707079a005001201d0a80091707000412600b040002d80c2c3c103c482d0103c12205051400d811140b441c4800b400750410141c4074124007201c113400c80000d00c001d201151a02c14150f107813840052144c0c10680000e02c04100005004010620702d00d41170f4192018030042a95690035821102070341d40c0c1d1400520f0f09400340004002000d02581d120001c1c040c000c0c1c096600091340300094549038407408460 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 110379298 1250 110378048 110378071
    0x603230a1503050d020c0414060a360501230609040b010201060305070e09070801060506070602030903090d0605180303060a0306050721060f1409070513030206160b0c03 74
    0x1551440c03481e0854801e1150440803410301c00d890740c070b4181c00d141240c01e0040140e03221081500d003d0400388254004803920503c80340c0181084000101c08403664403850b850303541c520350803d0340d0345034003151040c00560010b45110740c0c04494a01d079000d002c00344203507071803404080404854070320510a0800d000800504161405200390100802002e201d51000d046668410001c00014820403c50014015082100a0303030324140d131289141c50065003104c2d0190341400303010805030710307050b05032020903070701a90142c0c50742c2c1d51000052450041041456118140d8030280042c032860340d00a80c010401c46880a0101c003030092000d035a0302c4190b03151a08600d101034200085081d50788916004400c628107400202c80004010701120004505454002d80c0d4040401c1541203003070480005052550004072160a80e10000340741020041c01d1a0500c00d000880c1c94030080350840c0d0101030340e4000c11442d1503885090302d0300c120352002c000032100c01600c0000700f0350302c5802805581c0310300101d042 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 110380548 1250 110379298 110379301
    0xc030c02010506031510031707061503080d1a1903060b0d0305091c0210020706030b0108011d090f1203060a060509030706050d1b0c0302060703050c0a0e12120301060323 74
    0x2005c40681400402805035510070110200000f1076004110160104c1c008040e40c0b15216414143c045400c60b000c0354101110f240c0081001404410030703104001090400042d0001c101d0040382400a01c0214040c0d0111011000f62042540c441c80c0000f0340340a12020000c1120400a1000802d0701d800c0150200c1d409001071075251820801248030012040305040c058142c0da8040360415800d2030207603000da04400303801d0152030740c58800e500ca644800d00c2c00c84219450101440c0003a03608200f2030124680f8407000807000b000070800d05544805003000c40340842e00000810645400682d04948a0000c01c40c0000d60786201c5e101340c5441e9007006001d414020b00d011340c191580d0384004c5034080540d4682420543e40c048131040340d50a890107889203400d2003030310301c0c00a007020030042c00030061619040078041222641010b840314030b002030501603908580d4600241103600c4102003511148603072409009802050400340d41250350340d0328180048c045440d400d07905040c5090100501807910740 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 110381798 1250 110380548 110380573
    0x121109010c02060d061e08010507030204031a15030f2107020a0b13090609020c061b0901031805030a030606110118020409020d061118060c211308010c030c0201050603 73
    0x100514101d03070240c000140403a40c42c40c00d03100801c000486e03031107503140a03074003004211020300840d54003487c1c2c0e14085103401e0444e070369001c5100c0c0c000b410f1000303001c424000446000344902c41c8182e0300c800034100c489102d1085682a9201150081d85104007a00103c02918403220001ea03009164004c1c48030421505041ca8140d0780e400c00401c540d03006035020000a01743c1c180e48980d20240080d8031015a8812403280300340e03d00200031f45031243c000c002400c403050501d0070400340c07094007000740790102e0482d8400101c040d01040040d0302901d01d010010f4003044c80d0b0340641c0507008554050721a0607065508680d03c80c202c5a440e08000f1078803500903c4d010051800b44d20a201715480202030f00080002c0c0e454440858285824603449031900042c0c0b85034040081c0c510500340081140d900b03260a081c040343c1d5480c1c038038409a80e01c2d45003201d143d0340400011300c801c1c0c1d82001e2456681800040c0d8803201b0742d010741980d000b1100071034507001e52241c8041c41270060701d2203014090001c100300e14000303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 110383048 1250 110381798 110381809
    0x1006090803040326180a060806090402090a020c0111040501180803040b0313050307050f06010b0705120309010207020d03030c18061b08160b1806060102071206020d060303121109010c02 81
    0x500001c0348100e00100e880b64107491310081d11411006103207900b101a940d80038840d541c10590021000c1c800d5143c00c01c0b0071551141800303a88964152030035401038465940c0b000190088050408455007000c5490750030108010160003124001da0360300708000011440d146042006005000b501e0301708010074455240341600039504128a01c1c1010070310030507500c0d09821600614003c95158100b903c0f4642440342c1000b8a90261860941c41442d040841d40c840c1e6a80006084490041e440800050851705080d41a5418244c01409a52051019140060007014200b408c080803405080100032140700c6410080186c40040d00d910384010b081400d44102d112000c201180d2440d8100301040000c94208508400b591040820311058107251f8a40c60a800903000411240d520100400207140c0e80061020704442c556510b16002c0c01311402e1880280c41500c512080440c14074400108040d80070a4408000104520030481103446400c0304400e4452010b20300e0014070740c0c0060101500c0c0c903 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 110384298 1250 110383048 110383073
    0x1e0304080708090f130f0617151f030f030801090504080909060a08070609090b030d0215180615030d0815101107240c0807060b040f05010e10060908030403 68
    0x404105507091307050001480d001c075500c029000c1e83c1d1500038410305074400b07009000160101914028154820b00c02e0386540700350034024a10380c1e05450b0701040403596108440b42640c030820004506840d12400c1a403440c0b036042c00e04800003001603000180e03250081c402c103401141d2105420b850014440e00300804000050001c070f40c82100e4a100058169082104d0402051583c0f207100305a03151407004411070f640342107086d00035080198000d48041d404605ea8035145900820007055444010308115070003920200040c80f80700f41c0050000e2001d0b0400c00703205980c001c5040f544003c09249084030030400c2650203840e0051901050748151900301a1583d5070112880c00e90302c00300b4020001307450540030f81e1080708142c1356580821080c441c6102644400d071640e08181c00040e0b000d03a64200e4910849101070032103a6120100c60040d501c0d030300513a5111424138424051940c44121714801b5031404d42d501c0c003a05021050001c7d805000c1d100410894503054083c605061460300c0b4095103001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 110385548 1250 110384298 110384317
    0x20619020c03090310050a0b18071808120d05010b1201140118030c031103030703090b0f0d0c020d0e0d050a111206040c03022706010c0819051e0304080708 68
    0x2c00c0c0072141290302c04001c441030500304482c0c045104d0800c4d110840880b03c05c00740c10380c005c5200480343d01420300903003001da4101c4014500040090480104005031550a81100500d4050010320031200702050014000400c0648400c100da82d9881002c0391f110301c0f070701d9030069070542901c0c0108440e03048514021035401045c100350101c02e2884a000c41c0b44003003134004071248000380005100780844403031031801c5108140e00135490103640c0d840140c41441c0920554040c0d1600148a000840c0d8401c2aa5161105818103006d0000710703800c0031703480f500e00c144540d00041070340e10024054540036814004803a00000500007144643d250301c0a2440000c5104c2d070041ca03510810300d0211020485507100340c0c000c04c2c1400d0480e0640c410000070209844d016045d900380102c00f200f24940440e075098100500b401c10b060450341c14507182c0d02a001c1e40207520f945044135121001090340100c01001907481d00c2d000010f1050b51101660f4180c04140c0c3d01808500007400306c240002e0b0194000c009250 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 110386798 1250 110385548 110385553
    0x2a020301150b031b03090a0f030c020d060509010b01020c1302090f090412020c0306010e070e0d140a060b040c0c03050c070e010308090909010c0e01140f07030c030906020619020c 78
    0x1190241491038075559844101c550b4000010008418000c400c20004103052441c0c01d441c60900a060965a0405680282100c65400705620070103009481d2485010303405084003000c0009420418010030044560352011350910407a00d14640c030104100c904d440b001000700848400703401c04080250011407140c1d400241030840d41c0c610740e8520100512a40c0b0404540c0b403a40701a103002402c0c00030f0001024000d80c00000107100c4031480c5507625a00c40c220340f914074002900302c00002e0860301140b4029102030949031850800c1c8101141c8000103500540c001e2040003524800e210440e00384820300350005240c40421400244140d008180309036024040311754458030341210b004458001e9208640300140020300400d18100034034542e80c4039040038020443c046038940c0c081c2c100c2070154071a0b4108900c00072a100c5414002080c2c0d64a400580f014176104c41007803a01418074401c811095011604500000602501c0014802c4c070402010b003808186072180d40d40d00d0301035088030054190070b0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 110388048 1250 110386798 110386811
    0x8070f0c020d0c0f0b04030b04141f0501080f060108070e070c080301090c03110306031002090105040e0f04051c0e130207020316140105090105090f0a051302040e06012a020301 77
    0x503a154a04101e2503400f03025050350041ca0156001c52102c00d07030b441522100410b21003000490904c21805034000d4003c50302d0242041d80800090500b03400980b074506081100e08458101800c903480141a01c0507542203c02d0040c109441540d601000d00c0388000550040c80c09002400101e40090303000043c6040c41c0b0010841a03a56440f075410980044c42e140d81d072241d414071011740c075002d901150214442c0142ca1070415002003078807200800c04004005400280c1c0310182d92281c0104d03001441142e4268403241400785240000c00c1f41510250b070b0600c101034203210441002c00031007002c02035170b40b6100116130454051000c09006ca40384104015802d00418015850500422001600001600c0c0c5143c0c1070005d03000c0b81145c5a00c541c5e0400c4800d003c03555003645c100080341d01100c81120040640c0a6440003d41080420703040903402007100e19102040d0000794018100395041d43d9502080c0ea607440d001102d02c4000380c1c1c4e482e50250030110303082c9004079050540d510640c0c005000403900 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 110389298 1250 110388048 110388053
    0x150415020708060702010b01020c010507020d03030506130603050307020f27090703170a180605040e041412030403080a0c050301090e011407021006080c09040206030709150302030103020118030308070f0c 89
    0x1440f80480d4403d025035102c03c004000b82d070f418400d00007007820034200b070b501340581500482c0c081140700d00028180b545d01c1b0b020880c242c1e00d203290b42c00404400c42d028021a5100e140c01500d80e044038030124000e074000c8000c5803540ca00000e500c2c0e609503140d624136070310306410b0000110494019100d10003238001d04030003102040d181551034500210089040303680d2280c03554010408101504c013248001403a98003031101ca948801150200c8001c4210b4640a0f05e941c101250340e03988005454241d440349890303440d00c940d500005184154000d44400150780d80c1e200c0101d06440768015144005002000148041c07111607119408681c072003000003454001d01c051840d1080c9040d0340408c0540d020840c80b00700301c64207010300c601400702c200103401c201c0c1440c40841c01411014000a100740c030040002500f052141115100408a00182c9030150741042c0c0d000d00294000c1c00140d0025040945c101d07941040241640201c0364199603040940e078800320102e07440d20004406200b000f0540801d03034003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 110390548 1250 110389298 110389303
    0x11d1b070b150901030308011a0405090a140a050f0412050c0109030923031009050f0a11040c020d17070c0b04060e0f0a0f0201030203152706150415020708 68
    0xc4901c1464081d1860500100c051020542404510701c1090080018000281d010a41d030341115a0003180340b10b81c5e030000307003602800d00071071b006180c00c0694007080100c00501ca80200422004004040364541c6601c0e1100040e10170807181c02c6100e00442c404200044d00c0c1c68124202c00d40185071035400c2607032002e6803d096070000e1005800081344401f091002ca0000b408640e03d200e8140b280440075004d50f40880d4943d40660b60342c6280c0d40d540d0340481706000c000d100d105040ac40800941c3d2076040d407032820400c03456000c10842c2c0910300e0441c00140c607500000750b503003103258142c45400709201d8540b0001c0380d1311001060034080042e91221b400005000e080a41d008601c5444042411410060301920b4140d00300c00c1c00f4043d60248004402003010b0320000b00c16150280b1380541e90384c2d21802c4600344206001d901c01e401c40501c00e080c4040d10414003403003c0b030900141c4400a0350300d07090200304d103040329680404d0324240d0400040100c139580c0389000d0104e81d514016903514079540d001781c90 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 110391798 1250 110390548 110390557
    0x60305030307080f0901200c03040b030f01080118020102061305010f0e0f06100501140703031103040501020c0706090f05041505060a0216060f0f110115080f06010509011d1b 76
    0x802240000f4240701c8104080d0250503445804600200f01030030740082e100881c030100310240c0103c00c1001901244a60092003280c01401070048101c0d620700b0891030402603501c09100f00c240030b5203040a120080000d04141801b81030701613004207569150900001043c10b1030901c04c0f145c035903076105008500401030180225843d0340350003410100380350042d50b07030601c1801030500040c04400301c81880560b80218000300c216624a070003a80f15444c40c5130a82c000c2401030740400e80c0d028080304000c10040c054004103882103d50054803800c507030b0303424240c0712a901401195100c1c1c41c803030b0080c0440e040c40d5000214541c0e1880300e8998207a95070000c20a1030b80100c2103200107801141d0246000743c1810f03000d10081843e440d101d00320751811003000344141600c00840d420040d02810440c50140c0035000150107540c4029184d508550b5103550558404550b08100924020100002024a041010b9a040710140d013640d6200300488040002800c0b402000700c00e00a41600000c00310503100000303071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 110393048 1250 110391798 110391811
    0xe0f0105010806190b041403010903050f03040606081e15070f030906020f12310305031810020309010b0103051003060c05070b01090605040b030f0a0201110a061407090b04031a0601030603050303 85
    0x446d03031035043c080d4540340d0030710200509000e86e06100c1c4280c0042d52100444841603800c041050b1a522035140a00140c1043d0380062160b100b8820b00b000440040140c0c842c101040301e04541c01000303d030503001c0b04004115410808220b14401840300c00d0b019801104c3c640e8410f600042c03030200c0c102c0542589400111003c0101030382d0500b00040e0401e82140080103208039041505250030b0700d6907081552042600080400c107002c0046205000c404202000881d40d600c2a03542d201c05880700e6200030342040300c2045196081070304080041d4068440c45008000c0302410046240c25621580042c0180c0e01148081080400085020800d0001180e01824504501088031172030300c0c08000c04d4404c0342c400380d0f11a4002c90041112003100089401348140e0a00b000d40011200c120154104105050098043e03401c002240d116041c0302c1d41014401c100c607031103d43c0341e5034403802d141a00c2d010b54000100104062401002140300b0345280f660f02200c1403402007507442d12a91090b0440d0804c0e5041e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 110394298 1250 110393048 110393069
    0x70501050c030a151206110909040f11040b0d0f050312090703050606010e061e041a04050a0602070b03071d13020d05060402090a180b0d0f0c0e0f010501080619 70
    0x14041c1c3c0780c02c50f0061685003080c0724150b40c100d0742804008024080b0883c0c1c001c11450f03540c0680703d800d00c081d100b55100041d00400f914503070714250500c11401c001e0f180d801c50300d070080c079041c1d00706e60f2500b4401d400b68a200544481050b101540e513020301103240101c1030324603120030310041407841c503640e6505210342401409440842e107540b614a12b05940a00640e042c0008010002d226840b0f40c0c041c1d802c10021107840c40124505d440182c259441030b0380101c2c109901004103460585180310040c02150020340d40d5041c1c0b07a40d5840700301d841c1c02d06405400c1540c1c07010804140b15034450003400d103003441101100d04264a01d0380000d00016600c503403068180b41c01194103843c20350a40318080c3d12179020341d0250718000c4211700048412440740213000000c002400702c2d8000150660141c154810050882c894500c1a824144102e0101d01030840d1003248131080820803002c031070096809041011049070899080400540f610040104620b40005107040310308400b9004003c000002e202c0750301d2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 110395548 1250 110394298 110394301
    0x121c0906050112060e030a0e060912010203010603022101060804020904110a0f15080106120c0c020405041406130302070302210a080306240d09080c01060b03070f030509070506030705070501050c03 86
    0x1c00300184d412901080b50140c00138087d0a04440e0404620501c071581190b4481d640c0840b0400680c41d00d0295689190540c030100000c03a610350981d0050bc000c00581c1078409481842290140390403600f4003902c00050302100200d001814103c000b1500302d0310900d911402c40841c60013203000d050855000d600c6080f0301c0002084251b001c0a4412411015840e080c1c03c658144080a8004c03565003508044181e44c6950004103103102705294212240e000780188118246800c21070a601c0313074501c2c030018a005490100d909a1040143c2003285a41030f000f4002d140d1468082240052140c0310b0002910307003014481c515054184520401703240f0650300c00d91a41805814880000340c200e8104050800c10b003c07800502300e000040e204400d6140340701040d1448180380002c0c65004003107040710f0542c2001c2c00032a0201003a40690701c91882c0e55242050149040b600b10207494003550311003983c0c1c00c0404148811b041c143c00550b4442c25a04109181a042e5503c4070f0031200115030040c0e03c20b10100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 110396798 1250 110395548 110395553
    0x1b0b15040b01080405060f07030e011b08130314030a0e06090a140c03060118110406020a05011514090703020f160b0603011b0e03070905010e0a0e121c0906050112 71
    0x1255035030000003864010f803a072504d95952503030303040040d09800c4690700c0180050f42041c403035046107000c2e1f481200280110308500c1e444c02a101c604e140b403c4003068001000511400499010501080c2c040d40c5812512100281e040d1441e400500000d0100d40c981100310880e41d0f042003414001c015200040601c4000c40c1071a20011442780c803135a035203800807050100640d0b40000ca070740c151540c0780c80c01c0c10b021000d408a88010904a4018404280040360004031181c0124441e56480e00030781c028000c1405030320200f0b240d40b05501036a5541d1048507809500c60800e0078041707600c10b449040051170031044541190154201301d0107020709102a210a40400c8501821140c00c480305a00912100d4024512551040c0c40040e10f4400c003c0300700385c1150146e80401c03211008000021041189585902800c0b0201d00201c2d40d003a001d500308400880501070000742034054200b008a05814105054000c017040d101a5040d0755207680c582419070046101407041a00814802c00865407141552 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 110398048 1250 110396798 110396801
    0x10050d0b030606010e060d0b0d120809030702010f121116020a0803030402010e01140d110c010b10051611040e0d022a060903160609061706060a1b0b1504 67
    0x48421500a0b048401880703c50f0f60821a48010500308131012602c4400d004210350003001028482c6a10052118820091000c07000d41c614488115542d051701c0c03075442c3ca050555070b20076880c00900182221079001e8615125985a40340a81001000b180d00c4901980908098020300c105444489003040320400314545a00e181d001007084401441c1140b8107034001800c501d9a44658a040c000408007203411000d0a0084034000e0080c0c450030080c0b40d82c0600310003000d0700444882c0d6100d618020300000c035440c00309521410742180c2d0b076600e403801c842c0d40d050410a13400707a0390454481e00c4106c030b00f124660300c1d805090402c1c16008002c0500c440001802890714118604000d000d40140300c140030b0600d642c011304280900e068130880c0d91001e1800110340ba0928201030481d0300034100d030b8041160782c1c0c0030414900700c2c2c0e0166035450405111680d5101d0310301007a10709945c020010403c55450780e000302c030351204843c0082d00c000d500841c40c0e2109151b0b030070200c0e080010130100c07080c0c070302e41440e25 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 110399298 1250 110398048 110398061
    0x1e0f1c020c0a1202150d1107030311090a03140a05010e06040302060106091d04080c010203040309080c040c21090c090b01030f06141e100507060f05060603220210050d 73
    0x1210b107503949a00c1c1c0014100000503c18019000b00060440358803581c20134001c17980c00300c426100420040a207401107640d030350480d150407000a130070950b280e035540080303c044d01d4411000a1184412a165590b00030781d00106018601c000d02a4008110104500388101e1104c680c0c1e14010308000d1401c0d14000382403a005030091000d2100e9208180445404c05c404042100c00664211240345c45070f0a102c1d0f803038051a440204070f036000004100416074059403240450b080b40c011500410000d03010081075038008090200010380241c0e0110f9a003c0420500f500140c00d050002a00c01882e2a40007c0c04e04c05d40002840c0d98444e09810035a50b49813048a181d40c0d2804010040b00e81031500f600060328401e408a44106003003003a04404c3c004902603240b15030801018481101d201000240041d003240106907500341c50801e5070298030031140901886020000c10451850780c0c1c1014000481c2c0e8251010214481c014550b40c0068441c0d00d40056411125145d454450000c4c4c89482d064882 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 110400548 1250 110399298 110399323
    0x70905070516080d020417010c0f0203091804111008100603110a05030a0b0901090e010b030304030b010302010c0302010f140108011b0f0509040207021c03120e1e0f1c02 74
    0x1001c0150094081c2c03108814842180d21242850f03072060075000706406030165801c48118403c800e0b02c0b006a0310015440b0526080164441d428a0103400405070780f40c0c040d1940168000004032000071101d0403580b0b09550041c81660031240d44060140400c1030320308068900801702e605841804454043d85030140010912494180700141c01d901464803140a4034004200380301020020035030071596a006003e0020029028000315a981c01500020b01100e40f040c044039460040361401604002c01100c0a80386c0000c0302030241d918540c0116800040340c03400350115561220b40c0018040d2501a003000c0c0e0030380c17034040880b5504180d003141c21900031407400c03501004ca034070703032007001603048000a0300e04815030400503214074968000c200a445005c100030360109581603d000103486051095140900035990480030402c0c0c241028115010608503403119400a049800c594001010140503045c0c0c40068905440c52050a00d00e0198a40c400b40d83d00740ea10044192040e40c104201c810041 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 110401798 1250 110400548 110400557
    0x10e0601080604050a1203021e04150c050c0108090f06010e0f0901020712080c13081e0304030b01030602092808061005061e04081006050a140303030a0b19060207090507 74
    0x1031564034580e0740c00d0307085001807540d0f00c6c2d00b845441c0c66000340d059400d075003040038451581880550b45000e0f1036202c0d0103044d2485004c15680101d41c1d10802a00100c40d0380400202182d050002c01580c4224005025118510070005079230072150003408802d000307001d8803801000c64109020303600002c1000510305046688148612804281110f004401040040c1001042602c2d440c1c0407444c80c0c494410214450003111000103011400000c0062080c040c0014002d5200721030140691240718610015060500300b0300144082078180d4002c0803c150001c05851800040385203c429401958008604151a00904014007034040c01031035485240b5115000929040600080e954047c1200c24030454050078403084000702c1d040c00b05d4010b030170414111035094180e141c0100140550b40110f0340211001c810004410040d0f61000300c0d100d0005015500303603a41c404460380209803c0d401540c0c8050050b01901c54501301f0340c007050151445601408005090840c02429900c0c068981ca0810 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 110403048 1250 110401798 110401801
    0x319030203090c0f130e0304080607030b030304140d0b040b060f0a230a0b12010f0f0608070c02040b0a060e09010509040f03050c0c1003020d1802090c0903010f0e010e06010806 77
    0x100d0b00401c040301031490454081c03002c040b40001003520403a921103401545443c0100c04114071000201500c122078014048a685035118a401c4040e0707a120000c0d15010351003031000b8450030f00d107180c03415008500542100303116956529081504075050b10150348044146081c002c2d142022004005020b5058a041c940a403401c902c10039800c0b83c0082c03140c1d100d0b201d0380b0181619034500454900421b00950b80c0d03a210040a180c0c00c5440c0c01c20321541c82d003031840030000200070782d99a903400212131094441e054a9078135050180c40c00684520105d074403e07070b00d14010b001d507170702e04026401512250740c98100980c103040c180000d140060300300c584030f892040f04101c00110700040501403640d2501d4203a44402e0440492403500e01009156588032010b0b00c05c3c80c00c100d07030503800307450368000c4c0b10801d0082c21154030f03901d002c40d810f246001c2d41040314500080c003200d151400425420802800000f11030300a09105412110003504052045c1d44511a101c1c4095003007113500d0140c4104005030509 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 110404298 1250 110403048 110403061
    0xa050402060d0f0e0706020f0f0105010819020418061e020c070b09011b1b09021303080f0d02040e160801060804020d0303090b07030e0111040b040b0d09140319030203 73
    0x140642d01c0d9110b059515501e0144103440340350000541d11056400b110100c03611000042d496290400024010b4031070303806503a00c00241402040d048a01100281c05040908102008400c0348401c082c3c0e00182c685580c40c14480100e45d0004240d4024680002d0701c582111100f080b010842c05801d0341c1c54018040540013410204545040b83d081e061000d696440c1e050050301c84030741440c0766548509004100c0d130180043c0c0369201851010b17000782c2c945842c0e01d6440c178104901880301c0c0320310307480c6c900d40b010f0000807900e2004114603040c0342d05683c209804024030320305a0344190031441280a824040c032042069040440a403c500c03402d09030069810030740028040440184080c2c0700b0b90310b031070f91501814000c0c0e1107041415007150003041306182c000c102402401c1040100340e12586032004040001159005880940d1000161b15190528145c0000040d4000302000e5505503035032008100016900c0030f0712012042c07120050364440781c240d080c2c0400d81c0d801040d80c40c1411700403c00c0011 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 110405548 1250 110404298 110404309
    0x9010503010b070303090f050607030c051216050c0d1e0206040816170a050901020f010b030a0206030c040e040c1a030c070f0302010b041829010e0c07150b01080a050402 74
    0x544030300b088003036119001030400f24054610050041c003c000c0140b001d000748100480c0c2c1078030030b00c45a1002e2014154820044cd05449043d11440d110b282100129001e20a0405420004125031034a07a08141c6080002420081c542d403031240401c0b4000c21a144882c406191020703460040d0000d0011440e1507111201c4912407600300c0d001002c0c1c2d0032080c02c01c0080025a20183c0c0040090844d1203242092010b03140fa441032990750b015110700d890000c2da505050164500d0b511018001c0c1000c02c480783d00348001c61b0005849200910410300c03002c2003104600b03821704e1080780603030300041d030007880c029000140490016007100e00140410400100310303400012a104245e1140d1561a400141e050803030040c8203641c2420703402800c0100241d40701c6020404c4000f954000c081e4140104492101a842100c0761004290440200b0004120000740320f4072a6a00070ba078116040c0c0f401d0f000f0b55817481205081450004455680e141035000d950b80883c82c40e501c420065002c00150906800044 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 110406798 1250 110405548 110405551
    0xe010c0806040c17100906150e030f030d0216060c02030415110c0111011509050105040606020a0b15031504030206011d040f02040f0605090103050f0606011403010303030b01090503030c060601080c09010503 90
    0x441c01354204001c1600c0301001c21640e0003c0500c031070200031260b15112941a0b451540f11804005030744494280b203946408100c01141c03d005400a62905e50001c031070301d002e504000c030300d4070041e98141540700100302240205042c1034200e60203141e40b542000b803126080030180c0329010070003210101080c440e000000314028840806d00b002002481c0710b000c0c3c280944140c031a90362601e001110005007141b901d402c000d05070b44080700c00f4086030752921402c0b07a8a26050034060640c2c2d500f800414000700c05400308610400c000b45c00d43e1411000d0b20901c0110260030342d0100c0050b03020034010080409400714800c820541d400c009002424107442d038580e118036240d0084e20a60380c804490a499000d07034042c40c010300700038122492031340c0c0d6410416112000c40200c48224011000012420f61140c00081d0010100300713101c0d800e690840c0c070210000c0c10b521402d541070100c03203800429255401c00180408540800c0103041c01e152541c00100705010141c5101a2582d0600c40090070781c4c0c109080ea03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 110408048 1250 110406798 110406827
    0xc0a061404051f0932030c1902030f1b040f2f0c0f150703050606040306020705010b09180c0f01050406180f060807020111130303050711040e010c0806040c 68
    0x5100b0780d003200e200c0b030004c100c2d03184014440c10703c50204030b001c0c446400700410010044040040300e048018030042d1a03102d54140c801c0b543e00018481c4000b1001c00c1d030300e07084080c0081c04a03400014200c41c05c9140c01c1c42810174143c2c4000d640c14908140c07415009000e480303501a4070a012007401d401d00031882d0306c21a0070070340001101c482103801c03519881090b50140b804450440343c0c4031090507580c60303d8000102e100784003d8148000036070564040d005450241e800980110314140ca10b841d040000d40280c10101ca6a540701c0c180100c17950780c0c004e0701034000c840e020419900d03168066801031030104150361241c02146189458503241ea0080103403402c6134001e04244240c20300094180703d44405582010380a00c09854010481760381c030440c4284501069002003082101c14881003515005108a004210490040501c0000d12540151000d00d1080e00e40c1c00200000400160907030b40b1a0f80280e001d0382d52200203860203a030060f01160041c009507001c0141b4910000c0050802550800d207 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 110409298 1250 110408048 110408083
    0x9060f0612050702010912110708010c0c030c060b061b0d020c0105160c08070906150507111017040b0601090605030c070b090f070305030901080c12040204110f0c0a06140405 76
    0xc1843d8000e41040040355800001d40010184212000d040c0e020320690070105032240d810045101401489180300d200150b440f02c45008095540032a0300c17462008045070a1604c40403101e299440d1000900407074110309001000c25803800f585240340c50328103c2c01da42154021262491266085004c60f01142440c0040c2e280300b8001d820f00e00300181d025400940e0a1090200006a03440b07590b016105541c40707030303140c191698042c9008403030500036410042c0c0302c2c14800c0d581d4010b518140f888d0303c52410040c20860641c2850000c9941d14040880d4156aa00c0f0680c0800c40b180d0727806601207001d0096414554107604052444044034010394000514610134140481d501540c02c01c8a103544140740c3e01116085070b2645003060704c1e0b070044d84030503001c14942c8010489088402e400d030307601000b8034504038995a0320341d001c010281c54020a5444841010414a08000522001400c400031150010b10484540346407d400b1250b0b8022200e80c44220b20051000058002c03a000500200d04801c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 110410548 1250 110409298 110409301
    0x120712022b02150903030c01020306040b1f0c0c09020a0e01030615050d05090a1704051f0203070312020906040f08190c030303230106020a02010801152001020d060b030109060f061205 80
    0x883c501c65118101c01107a05103c085000320040c001500210b2041806071014446801c00c0070a00c502180c440c00d8181c03400940c0f00300046598031511161944a0050030380b045c000d47d40c0d00031030f01240c0c0300441e88000141d00e03c0000026580500400000300b03031096012110b41c1c4c0c207140080c12806070724110150180c43c1d1011803840103080140c0e201503038000a2816003007018040c0003d0603403161007041d01030b4a01c4060911000815811000d12640607005186003161036903040722101011306980c28125801d00100180c1c1d107070000684050a40441400603440c18100114507007110051050004400b0071201000a08110201c00840b985410301044400e443d01c00d410000704414900c00d000300c0000e000117111940081ca038100c080c004e03200d282c906d03601c8003031188109074800074090203d1003032401e100d4482441c2c03200c181c0d854501c0c0b00040c180114240490240d0b80d040c3c0c0041010500440103010300d0109101e044014075402014000440c1740c8807001d0a41101501001c007060341e200b0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 110411798 1250 110410548 110410579
    0xf0905060c1501120b010602011b03050901061e091a0609060705150406060303031406030303130807120e1302090307030b0618040605090d0c051b120712022b02 70
    0x401519032036442c1903030704807a684590f0800f03081c6501c0740e01a02c0e541990000051a28010320032030b000040020091408030912860a81c0582409804080c3c55965a080000c00b16200001c202d56a0181c1e124868024a06501ca00940720416155140d15158095090b100d64803042151410350301550500d8403000d5604006003410000f030324540c00000710804100421031154440004e480c440d403810406148101d50004074090220394007905a8000c20104003036040003140d0283c03040c40340302e07010301d099a241c3d103100721407828000308008242412048400b0345000061b80e04a880c41034030441c1088000b00c0000e6a071101e074031024042c003160b05d001c6455a02c0c0c055040500910032440c620322402e00349000001014200e039109080d00901d81c11540762440758140308080c54101008001183e1000c0042000340002681564050401c04d80c9400c885400d01c0000010309039848280b0041e041401840b09412004c0324280c04110280e00280d1000c650020080a0300d8043c1e8003281480c00aa = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 110413048 1250 110411798 110411803
    0x8070b040e0414060108030717120103200d11040507080903040303200d180603020414040c031805010b0f06030405060f070207050a08060415140406020d0212040b06010f0f0905060c 79
    0x440003c4143c4c002c40c000451105000001041c0d10303807080101641c0c000d0340d17200400b01406029032460404d010400100f0200b10f00e0150049083c01e040380000c3c40510030b9000611641c0800780032100820040218042494141300c2d0703903441001800d00110703924060305825142c0c403d500000781440170401c600c0c0001c04200301030310104a1900100c1d9401d413004400034110310789481318280d00700141c0c0804960b5074801d00035141110302d1001c2c825100c501031801c10025105081d15036003010303914000e81040744021000e011002e4091000041e0700c204007001d010203403241401c3c443c015082002480001440081c2d41544401c25040b0b0554545410300c00324100704907540300740d40c4114103500c0802c0801000c40d5a6000798412860243c881c10076040d00c0081c6c40c0081007010140c2c0348100001c01054064008084908000800502e0301244075080c25441505840c244e80071005103081102558102228001d010b5150804a840e0300080e080141542440e001c2d1500070007011809007501c0c4003c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 110414298 1250 110413048 110413073
    0xd11010b060d020714210304020d020d08030a181509050c030304090605030f0111090105070c0e1303030c02060f0105011b08030a021e040501140c03130306050601020708070b040e04 79
    0x1030049640c1c602162000029420850b015a43c1e4510417444407035483c00085c0850b500c2e0412120041c030f1024604010040f900004c005a0708a14040d03092401a5a41d42d40b03d031420b4401e1120070340340c4c01d00f11285000c845050304a501508005c517038440114896005000e8050815400800c0200072440c02906000724441302d01c0e0544400305002c1030800c072035000141510340903400c4401e07086c0080e00e030038203941d51400b0070740819104110b015942d5100310300400207980902e41c40c001c10350b41c41c04d100f00005411120344115442e07104c1381e2003c040e454081c54500c9002440208038a06210b10808a100418407807503041c0f0044035201f10000840c034a44041842d0006001c64891034401d40c003034040c0d07015500340c4900070f80184003504d500d011708040d201a100182d40d814962241c50102052541c042c3e03001c0c140071b00c41880140d003116850700c038000285209550202d000d040c24000a4a044400d802c001c0981e00101800d2000c0240a010342c1d0445084030b10300210707515141891071b9240030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 110415548 1250 110414298 110414321
    0x122006090603071710061409280f0e0a0b010e0f04050603010b0301020c010603030e010801150305060a09052a0a1407080c060f04030906030507080a0f02092d010c03020d1101 76
    0x14a002003182c8220031783c2e00d40007241c501e038482501c89900a04c00030042d10844822681c0300d00d00c0f43e4044d81d01e0036603005000c0001d007007020324002581c80f0042c00014a101341e0219001c4419042000030420640c019400c4800082c01c0c100d80d4010b0b901c00003015001e2140449008a548000055903075509421840440c040940210350b61b02010040501a200e9404160045821080c81201c5944501c4a041c101c42a030158111004010304088018000107062182c1c810b641550110b4142194480c0f02e000e01000c0b03040840d91007a00101080c1e0794100312481c42d0f407880501103950080d80040b6141703000f00001c07000c980c2d20030715850902028003e01d0000d803201e02c00c1000f00b01d0342100544c0c4d840c0c0650700a80341d4000c6036640705021419280c0841d5594001204000454000061a00095182d10700d840c000350600d00201c011600411324000c02211003031070701140e5207026821040d00c40041b1000e180c4007803142c3d641d0701c0c0696102881c07800302d006c00071611108000a202035120815146 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 110416798 1250 110415548 110415587
    0x80a0318170a0209010e0f0114061201060e0906011b020d080c120301230a050913060e0a060b0d020d080d060b0f0702030d0207080d050a140412200609060307 69
    0x81219540301d070350341da51600807802130712a0000031940e080f0700700301d1a03c15401d041555440d42e0900200e085e25031030320907000d40c01c09418016003400035400e2807a03501070205603545040440500c804c010040e40090002ca040c08040c010307048440024a00e0390f1002c6405484c1204082c4561170305407a10721030303413840e08040d024618241d03096503540d000640c12114190612031920280001503900e40d0301150b4015808500700c8410007450801d490b049034001c09140c01100c03901035a850340d0040ea45402480100d0b074002c1e80d035503010454184079401004400796031400c0d00c2c02c91640130502040f50120054401e580105049280b00219040007028002c05290713070f51140f91412031003086400c901c508a101e40101e03561105007910004c0e2440c00c450302100104025050364001343d99552114420900b00940702d004440c540f2495002070004100d810016013840c180390800084c81c052040c035800d2107090340e0000d44401d5503044181c070110b150484101d03580780c5038070100b5902c030103801d9070070a400c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 110418048 1250 110416798 110416829
    0x307050a0602040f21030c05030d0905010c020708030c1506060705010c030b010305010b090901030b070c1b03020306010602030f0405100c0506130b1501080a180b040803150a080a0318 80
    0x555a0081c000319030302080700c00c4d1040d403201aa0791146950f20400c031a40c3c803407000603001080c0714a424500f041d0145050703078540030300e654124095071030880007a6030396074694040703551141d4100241402031071260082c50802c1203251201e074807041d00100b48101049d40c117010441c196550702c00c895006a001000b003052103000000603016024001040c2d010078074004c00000c6418280c411260380e4031700141008016801e60381e4a0382d00140242c01c250400c00118007900024542d81209203c214030242d00d000010303c3d5104051408105800860447d042844801c000058013402e030b07403d440080b43c7e100d00103030041c2c40c116010510f4100c00f0b03204d031040406200c6a4036103643c44440f0700d8000c0b50301300c6056950382203068041c2c00c81a046400034414a00003110300a81c2c2d1300180441081508080440e0f00b203840390000d030340c000c0d10107441c0e00b0740000501c045000042101003c0d400c0558100340c03554648541d407038440d0f000b400045c0a01c04618024986810410b04c650041c1248a0105420 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 110419298 1250 110418048 110418053
    0x3050405101d0109080c0108070306170a11030c1c02010210020a08070f030506031005040501020409050c030907140a090507030609021305040b0a0e0408161e051b090c0c0307050a 78
    0x40e08030101e80500042241040b05032544500318a00594866030001c059448880004554a100090110b0100356548802241c1220b418800ba480040b0b4034009040312015070a04090080c8003025407031081d84207034a484400e4440c28090b80c06030840780c0009101d0041400180d040c48802c4070b8014206200040501d030301038000348030b5401b80c1c409981c1c01180c0e009449098082300c5041d20b4035541a400303800c0c4000301e401a81c0000c2e83c0b1501c1600050b04140e40c6510381000d643e42550480c4103000f01000f0056884820401c5600a0440340c000e03504c022640f0300440d4074106d05d030041101c41038032000003070516130203504081d00a2509200440d43c940c2c50001440c3c9951860148d02d01c9141044504141803808048003030a03a100b4005400464640d6581e04070650700c10f00c50096a075868000c4130008c2507010604440e00742a10106100c074038107515096040900d24085602085401c1090400d80d0300d0f41079819130b11103079011283e0780c0d0786c0ca2001058994006e603040200144983e41d007d808 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 110420548 1250 110419298 110419307
    0x40f06110423011d1009080a06290904060c020109021e03011a030c01030905071805010905010b0c060403120e03031306050702060702120f070206030412020d050c06130305040510 78
    0x954003101142c0c0002d4540710044801c400c0c02c1415000b58103100c01c8008481c075051107030000a902a082c40e59a0a40c0e844906082405121040c1c60340b03a90b5512003001c1c48102c52001d540302c0340c40388610440310005000164180406400078200d55501d510284c001c5000354007040240c1e400410300d22240c2160f154101c0d04410884426000b542010440032420703c166501c005c0c0020014054030990b0b8a4034011801402851029101ca214441700002d0300d800e41084a10805e4144e10041074035814410144140d40c0d0692040d01e605800700001c00a001001c40c4d05500240d151824081024204243e200903114920083d002c0303010000a1040140000965006c060310440c4240301c15615031038141d8543d1403c4a50341c000d60000800206000341c0f510007011101c01d081503140c02e006454021410740e0704200c5d02214502c10b030142031517286030108402c4404207000e180c4075140481900a59840758409031107002c140ca4041d040900700360007076003034030080d00020307018841e070b603002000060 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 110421798 1250 110420548 110420579
    0x501080f100b04020c0a050718150e0c0f0a03020304030f0f020a061a0319020a08150c0a0516030c0303110f04120c0302030102070b040b01080712031d0316030515040b040f061104 78
    0x11050342541c1550648a030359400380124a003070b03482b14214118036040699040e91001007101441220801450214004801c0a0b1640c0f041e80d80d0010b031203151a00e8064507000800442c04d00b800300c13a130040308205131300140c0c08030820750003140890900d040c615041ca6000d00c15460729070500922100c40c1039515420b41c10f4066500031680100031aa584120300e03120140e4440805034034201d440002c4815408000600c5410114034246190540d000300213140d69078804003c6001500540382c1c00141a414016040c0c841020303036800b072034212800c11015031481907215100102503011800410f105402c9204802942c000c2c0c000d55803016030f454650800c2d07804460844a0f24240360010480e000c0000e2035005541601d041084403002c40e072010b48442d640c078901d0b0b8140341c035070b5851207140b52414400d1402201c00e000c84500b1f500d0452502c1410180c51485803400000b40208010114070f0859040e504160010b884500c10382c014200f01000c0e04030b5000001c02c071000050009055040c002124 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 110423048 1250 110421798 110421809
    0x608010903031a0a120302070518010302011205090d0e04090f08040e0703020306010e0f0d0c06090602010b01050310120c091a0901060c0f17070b010f0501030501080f100b04020c0a0507 81
    0x3003001d4003050b020780358038464184040d6040300303503144180003600891242c5e02e07105000e4012160348030b0399880010f0320041040078103c0340340d040310010000c42d40c000c3c0740c4c050b80400c18a0248101d2030000d811035900d0b1080802442005007100c2000c88586540c0d0040c8402074101d11015884041810007070b00581c00351080c0d420b5114510005100d030361191003030300d004000503942c0028518100041080310302c0860300c010744c4510325030f200c18002015907100300010591615201c404500d00003020f4215605088924180711003002040200c0c1c444110107002c0d90300d0301a484645d03181c0c50400c2003c0440b40d070008040c1901e495820510703c20300c3e400c08080c5950854024466a88071041103803041c0308031000a003000b5400d5942c0b400120b02c0e01290007580c46545030355043c101e06880f0003002000aa21454680b4540c40c4140019640350088a015103010001840d01c03100071007001d55076440880c268042c603903442c110080b041d503450b0111034941c4070500c210b41c4e03d40c510381400c1da22040b052040c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 110424298 1250 110423048 110423051
    0x7020a0314040e0f04050d08011202010302030406060905090c0a05040c0c060e150a0b1c030e100e03010207030e0306070f090b091c0b0601020618070e04050f0105070c1b0b030105040902040f060801090303 89
    0x1e1f210541c420200a41030303900340103c0000304100c9034010f4001e5080500225a403540760070b00894211a1442183c0c452540a40101035800281e400e000040c245500800d00581c1440c0110341d2050300b00c240d0704200b5610010015212400c0442e480c01c240c141418880c100d83d5880900c0445d00c0a90851080038004a5403a010346518102e078840d441c18002000f008035808200c0e4541503d0034070320b00e281071542402e01200c141c0000002070708903803003030300201c1c0800e46005c2d90030a10708007003040e690300480301c1c28001c80341c0f0180f040280c1042428420400120300000380c0c3d039583d80701c6407641708411414207031a83d1000c0e2280790408401004540240c01071145400281e0f402690a01c17190b010061040034103000c60401c003c44250600007041a0745d030348180304000000c801c09114146c42010641d550b0101c0755483e01d840c1000007105040b1b0100d400c1c048609000743c80b400e078120781c1118030843d40096242880c1c80803402819003e8070b408003443c030f00b400c0012352010641040b42c02c241720750350 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 110425548 1250 110424298 110424313
    0xc0308040806011509090f06380c03160f05070603090b0906070504140a0b0c03130803090108150f04051602070546080a030e01030507020a0314040e0f0405 68
    0xb1000c480d901300f280120b00007804100304200382c0800750300401c50b2007100f90021610544842000903201079440d030f403420300020428054042e02030380c585140c400f2055500e5a1074203901200c026624010040c00c040049a020b49600170000780583c0542000d5110f030940c0c440315581c680c05401090007140c240c505684a0f0001929108040b8a8500c2030a0703545070b080c203143c244800c200201140d0405183c01000c41c020108520072800081d02e0301c107191200441e500c01c0700240f04000d003115079014001590047c8154801607820080b05130307220414414501c0b00d00f180340005008603040f4003031030350054a01001c2c8004180d01001424640c101c6808070744140390780e5020f010803164680d40c00300c0000315920a52518040b0280141c00c1c11050100502d022050b03443e0785840310b41c481e4401d0f00b880e0310903042142056003041c2403c1962200b400c1c104654684680f010b0740765044001c0007010806050010000d04031090161805040c4e0501000074601c0c00e41c0c1e414081540644060300e8500c110103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 110426798 1250 110425548 110425559
    0x100c030504022404080304260307030801180209060a09060201110412060506030a150603031b0803151201140103170304050709090312050a0f0b0910030b0c070c030804080601 76
    0x35441c05254064a5080420544202c0611600754072100c9000d010040000091006081001e0805004607040241d0b030240040080d40181d140d40aa0854139001800324101281d0442d00c1103045440c0c00450036150720160003103500a10554128580c01078000c5804141c4c1a4400f01480540c4c606400030048038500c020000c0c0640120321070352040036040f03516440000e0907904010742040d0003404480002110359102210100c020703408004059456104006051f032050150641c0380149007503400311303030035a00d60802d0b6100c002c0110300c1c1080313001280e84894907403000000180600700020804414040080c1e291290b0031b00c02070b10f420030804d00780d250b1044c1c110100c0b4040c0741e004c1c0c002d280881c500b031041809404640c800750188445141868001140f1b13004891040c121340e0720028031181c01480110031600040d4055025000744020400c8803140a50580162030300311540c0686680c404211084601c80caa90007800c0088400c40042000300c07202c06032042e2032104040e0b40c0c5c03d80e01e44 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 110428048 1250 110426798 110426801
    0x604120c050102010e1b030a0c0617070302040b041e05061303150b0609011103070501020307030b01020d031e09140a060608060f090c090a02070b07050417010203010b09010513030f05100c03 83
    0x603001c3c09800030303108580741d546c0003070700741840398805000c1c1e03091024951189101c0d140b0b140d000c130020400b099005070340c80211010150340066542011401d040c104501c804540c00385004100031208140c1e01e4031500c04500045034000c01c4000c01d26650b07204140d40304070315a00c80d880708480f2980001c02940025221f07015502a60350013411190800520000440740c0701c041c1d0300c2240481c00301308600c0c00410b80c04e0000b03511945068030b0128200c2440400249800c824146810406141013a1081184010031a0340c940280c46a408694049241080c0d814034112980c4070049200d40701d521410014660048412501a902683c1080d600d500c20303400590021110041c0301d42141840d480c42d0715140000e9504040c480038010308003c00c50340c41008601d0b050b00e50f80c0108401003001c0055450f103454040f12006150025825035242006443d50b134000d025100b0305021020032520000c0e8450303c001c0c0001d60708443c80b500e0500603410060307207448444005c040781ca818810601c010901a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 110429298 1250 110428048 110428061
    0x30d09060c03060501030b0f060906040e0403170c0901140a030605030a05060708010509090604030507060e0a0c05130603030509041d0303010312030b0a08100903021606080108010e01110415020a020604120c05010201 94
    0x1c3d01800071210041c8c104405039102e042d2155028105100208080a040c8441846203102e5201c1d03150f1400b50062010001200400d0002d030450708206a80d1240d82c0880c100908841400e18161298030b00c40c0d058000d00f45982102d81c1501c60417030210284440000d00034014002500e840c24241d80b14814041440c0c400c60328405140d00c03400108002910800c014159103002d03000015400c0b079004049410124102029200d030040010309009514103188011600300280303800300300c0a40703503940103800c0f030060b410300c18419540d0307182440e000004050001002100030055a94a40c1c4a1030f2030103800003c501c1c00d100081c0b400422000340e0908440c524255400d0200a01d2100102091800036100307040c4110114015400c14829840c51554284054151500c440e0815814011a6400c44e00714500030001a130520001140c4040c6c104111403e89104001d042a8500300800a928100d82080002c1d040040014005880001d01155040d1035201d00040c810300703680c5800480c2a14103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 110430548 1250 110429298 110429321
    0x1502100501090603021e0a090207081206030c1804211e05120a0c090b03070c02040e01062105070806160e0405040305030a0b0a05031207030f0305040302061602030d09060c0306050103 80
    0x20325020002c0700d1007116810380d8820300000c0111f0107190700d1b018aa81a6000940c0489180401040300c500c100d2240ca0f0203a480031040d401800308468400000c3c020200c100b20b04840d195080340442d05028078041039829480d40c40410f51250300c00071030000d00c500031070180051102240101c0d030741c5161080d0102d5541d203941c10850f484988403500c4d6000204100540c02090054011300041c1904103100903520409868031904010011401407000b40e6881c10744113011a45806030501200521380d10403101c07507001491b00d00c0b0030f4040d8940070349401302d1a00008101d104074400c200391001d510008175420b030b440c1d94a603429507001c00d0510046c0ca8058900401049040c000640214050360150000901c014100304200d9528404603003000340502d10300c200d04400091400038160401582c0d410035030240340400c80c40c5450f0318000c0d1543e40c058041a0414000d045035806907100b0801e071240c0e492000c60411003109540f03070040c01040301c0307200000841d00300000007543c0e60282c81112020308 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 110431654 1106 110430548 110430559
    0x21207050406050a080d0302030702030d05131101020a0b01060305060f091003060e1c03020a03020403050f0c120c09270a03050310090209030c010315150210050109060302 75
    0xc02d81e4000d5805040c03681001c202c105030000307010000c1401031400580700d031591207049095100d4280041507283c14507050014000100516a010303911880e0754410407a4240016a102e2881e8070b4003400050004004004042c001e41000d544004001d1012078a01c5506000401c3e400703068449e1065072015803001e0041104500ca0980c0481001001700064000100c0105d14046810544c40c1016008220b07074103c140281c0503607010b5540081903404040d40359071220358a240400d1414814040e620020a00801c00b24506400d010080c0014600e0ba841c1500b22507012400300006080c0c141854450313003400030900c6421540e80c0300c0d540b8207940b402d2042140c03260707240f181c0280b0746142c030411460407541e030001565049500d0a080c04102c00d40403a251084000e5030707a00141c50380460000818095a010483d02454401958200496600c82100208076440350200030b4208 = true := by decide +kernel

theorem cover : BRFrame.Cov 110251798 110431654 := by
  have h0 := BRFrame.cov_init 110251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 110251798 ≤ n) (h2 : n < 110431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
