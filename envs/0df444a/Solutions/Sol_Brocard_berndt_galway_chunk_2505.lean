-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2505
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:54:46.242134+00:00
-- url     : https://prove2.me/submissions/20cb1af9-7617-474a-9b93-a6813d69c45c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 450359712 ≤ n < 450539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 450360962 1250 450359712 450359731
    0xf04140a1707120809090412020f01150311060c060f010905070f050403060c0e0319020a0b0327010e0105010e010e0906040308061905061615050c1603050d05010608 72
    0x390384071803211800501e00c2a41000c03a62003480c040141114548121410b00e0040c02d519140c075500b800843d80201c2c0c191411940c1c2a0b04a43d810841da03418401881e00e10038000082c03007464102e400800c01c40d070032400041e200c030380c01d00b40c1030901d42c0e1124200e031403490801058a0301460210101d2a00500034400d94008608110005100d184180000d4000c0b0007a5113846040c81d096448610041460b004950207200c83e01c0c480345140e89e82003000c091400c8000c0d40000900440c2e10500a84021943c00072200400520034024a000d10300c111403200c6030302268510950440400450145c0200ca001d00e80d994640400070031aa4200c82006051700c031030062010042d20b0b40b0303030b640795142c0d821100600040c0948011400c00d1803c080080d001590181443d441a61134000107541c55006c0c0d0b0540c08070319065104242000441c2e001a0900b00300c0490800076803400c1604448030f4401c15000d14040409070b0a413a04260180058030f00c44803071010104a59030312004007401e10b24041d2401400d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 450362212 1250 450360962 450360979
    0xb0c0109050d21020702150a1704060e0708060402100f1709031308030a08061504080601092a0c031808060a0509010f0204291e0a0905010503010302091305030f0414 72
    0x940c91114000c17203402e41e0307000e8001003c0ca1198500c440e5142c200812100402c8450516a51030001000d58903000c0e80c01a00001600d0502508440c5841e030198070111468000808000142c0ea50203042230840300c050600803010072003000304807000300014010380080c0205d081800400000040031348461201c03404420501c9440301c410907564010101c04d94001030f4000c0014840d4140242241d0003950444c6020341000d484014040c14910240c05c540c0c111951084884902640100b400d0f98810740701c038409010b03c0416400402d40041c9502c05010b00444140000000140002c40d030010f04501040da6840e00f00f6146080c00b0703090a0303c401c0c51560030000b00144544c6540300716130459034a000600740090306504c00144070940b540864190010030301c070f00100c90407100000040c5080c0c00d0335903540c039030001e2000b403d14503c40c0c100e141088411b00043c00140c031000c25081d0020507030344080d8050f110300d28280346148a4004010068000030030001400c145001c1c0303181d4400303030455801c10f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 450363462 1250 450362212 450362267
    0x50a061e031a13140c0d08120f0c0708090303090a0b0a0216080a063209190b07030b0a03050f100b0f0102150703020d1103012c010b0c0109050d 63
    0x6002c08040c0c0c0c0c07550b002c3c281c2c1c40380715000a994a0103d9544204003040c0c0d100026441e001607205001c00d0000d48503080f0000e0031003205480b02c1103a0b81d112031a030500d01c1e85e9042507290428940280c05004200d4a00081c800e0510b5600f007066544000c40141601d6506490b400c1004042d0003c100242c05071040700045000c0d070300c5440ba444161401c00000304010f90300764803080041e11784072000409000640b525004050030380d88110886040d0717031016100f1030400164503803a00000d9904280d59803003a684c61400501d40c0880213400284a280129500e4500b00001e0226129580010428070aa40000c207181c2c0021a01800700b4a2110f41000b00da00300344d0a004507842c45000d0240103130000310548100302420194650012850f1800604241c10b240400d411141c0c1007214501e1044007100400c070031002c1ca000744000c015151640e00304403092414845004406001c4c107088003602190240c0c00003002d502103030780d0315003200032505030240480c00540184440072003420340701c2459070142c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 450364712 1250 450363462 450363503
    0x30b04062301051e0402090904121d030303070c1b060206060a090b100804030507050115180c0c080a0215100305070f0608010303050f0706050414010b0a1206050a061e03 74
    0x7504807403001d480760011004503c510707100c0d400025401d030f500541c20701c10381c001500c4000f40340f80714500c01d034110102141034660180c00485480f400d200b00020350103d040042e1800700599810800c13134206001019114130f40744c503005204811004116400f0b58000a200341e00040c0b441c01140f06a07041c0340415261240a000e40d500d07844030541040083d141040001e100e08102948a40203180160400c07400b540d4203801e44502510004456059500c140094000a810b41c0c603400c0742c070745082007800403002d40074282000400c2d02620024020402c689024004d100f1017908003101003102040e490320501900b03081459000542e1a44110030b030108075075600c012070400f80c0c2c4540c1c4039444980e00e1950100c40650000300802c42e01002031144400080780c0c1d000b011b0040307202d41403c0030414242074050f0300b100c4031420990310940070802c0400c1024038518030754402c00c0d002000480c582e0f40f01103800005d8080c550040c030004a4410a01f0366140c0403403c0c1c0e03800d0320b00c20703488011040510701a4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 450365962 1250 450364712 450364781
    0x5150406080f03031f0f0305010e010b0111100c0e03010c2102040b0f07050703060509030706111c02161e031805060a03020d06090c030603050c0604060507020d0c030b0406 75
    0x14142e45070b100b0004115041c0110849040800750000d0b40c1d040651950b007900ca65440baa40116040d0b0344030594848820028000c03101d0400c001e01e416068800212036456481e420070210703002440d618801500801e01c6841d01182484024009001c00401c1a800820042e4030b034a0000c83d01c0486050280f81c103505008950460301213801060900098040e0458140d00502c0304039802c1c80340900000c00200d40d40174044c80307601050091600c668160a2140c15100100c0d91204140320800010110b080043c0128400303807070180d001a00e9560981000f410040741150107414040348007144100421000209004680301c0e640d0702c03800c00d4648083c00d0700d200c01d900601da404401800594041c901c030768007030150b40000b000c000c9601c0e40d6803901c1c0b004413650403403200002501c0d08014410710000300941c4003412000e42d0000d02e13080c50304500800c103007d403c000074800d10041910300705211403a2800c0018540009040c481d40c1443c4ca400b900500903001d801c0c041100041c2c422040410aa06 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 450367212 1250 450365962 450365983
    0x806040c03020909030403060606080601030f0c08011509090504080301051e030a080906120124180504020c120d020a08090c010c080d060e011707050a181104090515040608 75
    0x20100d086825035080056143c2d0040c6004001d100521001022502d14081d0300000c0070700d03031181d09075424418001803d0b07900c46d0408036101d6007462410700c20320f03621510740c5045070000c031980381030050a07110840315403003940d100c0810782c1c4c2400709200c18004150010340c1210802c66a410345a042c007036520007020340341011079a050704034010840120f1391400080040e4800242182c1c5407403a41c03000da48203d5400e0300255140740403000f0321409030707aa58142900840355410883d4000b00c803209a0500e000460040500491b00404d903100d440008005070000544030103076181d00c5210b1142d180c8000d40020040c01c00280c503280100b90b59030004144a04441011380d5044010242901e8a03a204e0f80544130740580c0e6035031032500080c940420040c4901810480100c82c0c01c2c1d18600c03c005281ca15660842d601c1f40460302d070b0402100c40c411003405030810100c480884c4003000121381d200079004550144005608110403c580c00039007041e040c0b0000811a070070480c09449925060b0785440750714 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 450368462 1250 450367212 450367223
    0x20d0c090e1e0406110307030e06070302070809100e091f05091905040305130303080f011a040614070605070e03010c11030912160303090e150a03060b0f090c070b01080604 75
    0x10002150360b0310300c1240d00c40d0142501080701000d00c440695168801c846180001b9901c1210340c1d01020103111f2140c001c0c00d41c3c6429810304070a511840d03500c0c071a00c540700e0307c144500b80c103a60030a40110720403c400d5400404186051500048081168500103a080da005a041e1000b0030b4510b4026802400b641c0b08540085810b00240c3c4800020940508107506000c002c0c819007807608072942c030f40006940b20380c1e0760502508104105440380c0745c042e00042080e505900d181c000304110f007003e480440c0c1551600820f003900520008005114520001e03091500700300812030701d150030042c07005c0c07071985c2030b0b000304050700341c590b01140c001102802110640c0c000b000002d02c03601d8031b407520303407504041c0c1800c0d500c0c50b17206010784c107819441c0c9030300c102c01103080d511007000104807140050b90301c0114405229000d035141000a444000c0d40c1c04024083c5981d80b074044096160a5050341c80720f039015005042e00d0800c441c4c002c00030b4114034002c682c084442d4001042a10b00402c802d07014981c0300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 450369712 1250 450368462 450368491
    0x1e0a09030e04090609060606030221040f030818070b0c0c010306030b010506071a070c020a0905010e01060507060b03010c0509030708150f130501051005100e0102071710020d0c090e 79
    0x11001c100240c03900f0001524070b02d8031401d501c8003150039403007000014a2036407001651240411040034051441100310419540071500b00000b041056404603912645490140b00301d581d0403041010407881d5903d0500749100700e0001090354446240100943d410400441e80c4852120300110180c07000790000401150300e0320010400e50500c40094401688a110b802c4d515513196000080855001c035171105c0043c183d500400e0950402080074006402890703000c3c0010b60411450600855061044504108000501009210310703507005021582d0010000e1010119408008155401c0b81c43d0043c407078001c40c10001000480026088003a03403141d01e080009980380d8900307484c0d0103030040ca424400c040c0012040700043c000e00c14940304d81514502c0c42c142e1410f010520051038100046d10090112112100000e6a00007480c00201c8068402203104020100515401c24000040e0707146114000314030008010680d07007003903003030144682d62800d00d02d54407141e001c0d81000503034820380b5140a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 450370962 1250 450369712 450369737
    0x31903050f04090551090a02070b06091315180b18010612140705030a0305030a0506010c020904060905120f0414030d1d03070e2403060c0405040b0f0303031e0a0903 72
    0x2200c210f03c103902d000145071a000308045c0081195404100d410f04250340e80040d40300200b00c24402d5040c8c0214064408107220700d00030740305640d803810005c2c0242001c025490b02c0480350040e030301f142d46030302c0c0650a001d11402d4070745003820720b8442c1500da00152003200c1c040c0701500d010520455044806020200c2d00300b0b01942c40b0030000e03444a0f082e2b88a42d0151000105170358804001c1256243c0c46592003a03941c0c500022000110340c07024203039504200f508409100075a03a042052500305401041c0007540c01c440307107049880c00ca40310f540c1145182e00800c07101d44030080c510189c811114012003600122507031104142d04d0701400807803200400d00e40c00352074401030306070b0240b40050348010b01107840403521411006000b80c03049138020b50800e07107095180e04d40e1025550b00728100340143d00400040c10025480842c0380241e004113406aa55008002c049035900308500350b291030040c0030759949080c030681c4036010094580c07081941284a41c081810240c3d40e02c500d8940d99090358030711040142 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 450372212 1250 450370962 450371071
    0x7050315010e0a0305070e01060f020a03050304061a15132903070e0603010b04090f11180301061d0702060711070306051306060608010603110702031903050f040905 72
    0x5400c4040d5003080068030f0210010f001000341381d014040d40c01d5407101c80d62400d031006004060340c0c0106401c54100304c8045c00040e40003000c0c0d07500700341c0c03110001c660040c2c00c41042c00007070ac2c2e08090300d0780310081084c144191014800140029407130496007030001d0340c076200d40c5401491103029030032440c1020101c00c02101003041c045c540000c40d614192200545035000128203400a030440c45441c900028204000600c6220348850840c0c101300a001e03440c11418121094000e246901c0c800100c118521000341d13038290303c80c1c401750000442c44580d1042070003680c07805081c11200c1e000035126010118060500031043d180402c03a040005004190961b922030015000c094015044c0c0340348bc10382d110000300180518405011036640307901c02c40d0b14008000303003900d04d81d60300780003074210410294016840108542140d40792051615440c0807107860125140e100d0036801c44d001301404140491040d8003600158020001c09108180c4c02c80040341200c00b2201e0782544409080009040040c80348 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 450373462 1250 450372212 450372227
    0x1404080306010909060b1207030c0801050f0303120109140702070e0c300f100303050904110912030d1b0206070c03020c0a0e01091104061202030a021b0309090705031501 74
    0x70040c981440741c1950b52210324251090350701311031040180851104a880c1d0071194242d40103000d0326091120348440c2c1009002c2c10010f0207800d000d40071010086400b514100100d600b2a4544100c00c5051b69482c2180e0340244206e0788810b44130320078800480d02e000d10000e400e0341541c0b41c40600e42c056440f40041c800d499449100e00d02d0001000b00c0203a803203941d54240d40c0883c1d03203003094000c80030710340804401070b4060010900c1100c4008880c040c00400c3d0301c9070589414050680c0c0014002d5a040c25904890184040840e03000221100b10000d020020001c4c282c0404156424440c4003400b9100d80114240c1e11440c1d00103074051000140c802d4400c51510321100d000c1e0060b2425501e00e003001c603402c408180c01181881d03c0190041205c1b010510520309502d41c000c0340681410b08246c0001c0c042d603c1d000c0c421020036004800310f42000a140d04892114541c064514215141c0c0e2344020340b82e80155010521403002400040c000078001c4040301d105090347c807501c440c410003e000540791503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 450374712 1250 450373462 450373471
    0x106181a042309100e061f18050a0e070f0f0f03020f1009150509010905030601080307140c19030203060a1b0518060301031109010b0c0601141201050a0b0a080114040803 74
    0x184501c50310104c0803692403068516017544a00602100c0c90208200e00410f801c1151300385038031800345020040398502e003000081404425002007980d4590300f4644003c0c0c000411003409a0080031130001340c285103800b0703840c122007914480519807171b034030b9a42051043d01440701a40141503e21420400d00d09840149030150786424040c3c040c035101c0c041c2044002d1950002c41c0410f100041440956802440d0b550003400300300c00821007981040101902d030302520400905560803400d024510382e81c14481442c400c9000ba01508282c071002e001c2080f880d0403840140e0190040da004038060109030b000c0c0c0b080140348038460f40100f00c42310000f19119070000002c0854084503c1d6446025a1a0401035008500881641e20f004034003208100c148031060344100550842080600c000c090003207000303811500c014203100e43c403030400d030b0201d007040840b0303002110254a440100014000e5681c00f601243c00c00f42e4500103040d81300c4d400a4221081e0600070041c1c0310100300054001200b103001035601 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 450375962 1250 450374712 450374731
    0xd020903011415040b0307030809010e010c0b0a051006030e07060f0201271e0c06030908040806240105092407080403060905010f020313140106181a0423 67
    0x4060481240e80541441621200c00103c81041c00d040c10f4500fa00450300207101c114041c004103840d540d078403007043c807481c54082c1c1802504142054142e00603852214440c0e00803400b201c081c6403820f0f0389001000300703c40120034683c16050114070f1622a114554220100314001c0501c2d90034450291011922020401c007150348400c040c0e4801c10010350003d1054114030707803192030711815150032803942030360003810701407007031002030000200d109185040210303003d604000031440384508200c4428419604403c010340303d0345040c01421030f02ca00c969011201e09500007000003070400011902c501c55041d441c0d40c01119280070604090700d000361180044110048540b4145465903a9103843e04554010365140b0360356440c5009000003805503144c40072441c5811071851801e0507541d241d044a03c400500f01c1401c00b55501c0701c0b000c003540146c0280c00881c144854002140c41c9502c0a40885c0061400c04450080d4500f0542058003030050501340020054a1403c1043e541010b070450080038000c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 450377212 1250 450375962 450375971
    0x80d050a0c0906120e0709060b340b060d0f03020f060105010e0a0b030901021308240408121e2d0c041802040b160311060108070506070c090c020607020f0d050d02090301 74
    0x3ca0000d80e00c900303002414240304003920f034407003000c0200301d280c0754204514071840103a040c10280c2459107210482b10b0792008101c030b416100c200101f804182d9284008000820013a101028150001182403080c0c20810403101036a0700d130030044a03002c20382014590080000d02040c40643c0c0c240740a1a8407146000c00141030001980322046c2d810b0310f540c04a04e15400091001d42c800e01c0c2c8403502c03620300200b0132460300c013820540d41e80c90407881904000210180c0c110302143d0101c0b80c1c4045004003440441262040341004078500f01c111200f0781c81603520030407241c00742400303410011400d84034044c04074151b41068640281d00c2901800c0b444240f440d07d038200008180c600307500015003802c180801c100c03130b406038003031402070111003002c102000503610440c010001440700041500540f001170f80c0454440354a441d1100d030710115130700b2080d03540b41401c9811412035800110a44148115821260881c02e44170442c5d88071510505003a00040040180b0701e042d01c41c540013020b450b01c01500001e03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 450378462 1250 450377212 450377219
    0x10203092103070b1009020921100504080a0f0806030703060905150a02040e1e01151101092006130506070f120c030f020705010905040509030403080d050a0c0906120e07 74
    0x90855000380d03022101d600103441407117440006542c2c000080d12041038214a8000c21000090040300240780c5140ba001c841c40902c4203605080c004c80c40c8041d9514070912460a003840e08074800e800c91075500000804008034010040d1141e6005030140d00040e001c0c00c42c1c141940c45406c05410685000e43c0c036849034039001c0e010301c00e2030590203204110031440140c40e2400c0c1005541036200241120b840d40031100c06018404a14038040c0d8111444002c024600f00100601a034035503c1454498219519008680041c4030901800e00c1c420007250300c16804024042d07040003814003c800c070604905508110600103406e001c001003000e5409452040c03a141c400e0390b03a40103113040e62440303400011504581c550815420004082c41101140017503c02c080c24000000c044040301c3c458944500d232100003142140d1414002c0f10040c50704034490507541c00d80c10010102400301039a10013201c03490071141c85c0c0f13802d1052038900285c50003130342d038020980071103118070014040303001c24121180203001000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 450379712 1250 450378462 450378529
    0x609040809061303020a0f030203032205030a0b0a1404150b0607081902151905190905240c090405090c091602060f0f04030f1106010609090b030c01020309 68
    0x20034441d8a104024a50f941c21441440f40d80350a0303621000e80c0300118081480184c1d804802d5a609003c1c0349600084186c4c1c00340d640408020550120f6054003e01d18642c0601480c402024802c4411400a0198018404c0e00d012401011075001c0c04400d2402020602450720303070460304000ca0000d016031f042001540350304616034003000b00d070282c07894120700c500c3c94541c050028070728403002c0c2d1b12141000d1410302e420a00710030032002c0d00d100300c0d6510340005010001c0e11201c0700e005c40e0740d50000c0021108a207882650360b48440030f100300301424100f002262507000720641e48501443d4104a040c41c50b59003d00c0041e2101521000c06401003076886091922440d001034030492121503400703140c1e00c85180180c04c240b0b001c0c250550b5100500100211001d210a0490700250305140100d0400c2801104a0312101081d80c14032813070059000014500e80e12840d800199559a1410031115815208040e13a4880318600f40d80507130001e020405192401007214850b1000e0007400d03048000310f00105 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 450380962 1250 450379712 450379717
    0x6040b0f1309020910030c02030d1e110a020f0109050706081905040b062b0803040302031201090b0103060b03090a0b09010902060c010c02010507020a05120a200a0210020102070b060904080906 84
    0x10350180383d001c1000130300c2d0f2505031310100c03800c02281010004480c0e0040025100e04c9140c600002094680207160100c1c2403680450354950782d12001000710903204641070074198840c107800c40051140d4001101602810320590a1169101c030042440b2844c0c100d05540071040140102c2d04c1e03106020f01c0a98042683c01918403c501c26641c1c1d0f211842c00f02d00b0012480725080c02c001c0500028074540c0e0030300c100c032520500160342080400b51030765190b1504a1031445004410081c1c88183c600000307030395055800122005000740c8092052644805550090780801c54014602c1d5201d460004045401d007401aa0055180300020850011a4000c11461b510003060b9030030680d921082c20951035420b00c111074111600344050030781d065941c8c03181079594110140e0030707601c41d400003003c5a1542c01620791020002202c038508215146031107885032205031000c0300b640030760a03a44c2c1202481d4410302c01c03581559401070f44014961280c0c02808150000140200c0e900b2004001640303003552498003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 450382212 1250 450380962 450380969
    0x120624040b1903020a1a0301090207051207060b0f040c0203090f0f121b0d030207060516020d050d0206010b090604120c05030a080d0c0c0305030a051015020a110a0506040b0f13 77
    0x91410b0940c590701c140080340c002540180c03440005110b03007a480d40c015108490440341c02510150701c5012034100b05040828044844020080c00540c0d0303020080250400c0000b08c4040310500020703404030301800241c5823000c1090b401608100100205864900c0308a60082c6002e00b0000314031405601040c41c1140a0440300401d9112840c01c120400358145038207400381c0180c0e90403a407943e41d55006950f0740c0c40d0b40107040911401003042c20900303e04007001c041c0136400030f005101c020b529041c00c586a1012003210710050003440c00110703450701c842c000c60b022401c010704024071705460b044400d5058100c069080340d07492124080083e1076501080a0031000780200645907545008400210484561481c14411711420140b54404290420252fa0340008589004140d5036640c0351a00152800c0c0c0e000741c06100454043c0c0c10f500c80e400252200f40798800c140b407032a45c010030b004005844000348941507204c1400c101c14400c0c0320f818000b40508108072100c0038207200020034541c40c1d80c8040d40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 450383462 1250 450382212 450382249
    0xf040c140d1d01090203030a0f110102040605030103050d0923010302040b28020d0801030206160203060a24080606010f120c020307020906061e0c100905010b120624040b 74
    0x80090b02440e0003040c1054540c0300441c02000002040d9000c41c6c0c4074010a028071061140c5400c150107020b000c2e83c501d941e203600e800000c55960351103000c007810582080c0429200f61040860b41001280075940213826901d0546031880c0f101d04113000280014000c403452810503809000c002507140100f000b8001c41c03400e101d51100d40102d1250580341c150380040407001154488280e40c507020390030004490650b501910059a180001e2078100c1911100c10307002501482140100948d8022643c450341c280d41c00e0700d056800026181c108107031024483e0150144c0c940000012640d20741c012102c60503580c44500300380101a414401200407100322460150142c2c100050300e00451034018480d692000b802c440c0c076400e003044440d009404007580040e1400d01440000d003c2c5205c2c10130060521403070300d401c0d02440702d522a454207a000e0010310001d0b40c01980e0700e41034030540c0d50010441610800e8401c0407840410720012441421048028210b90450b907076034841805500c461006030a00000035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 450384712 1250 450383462 450383471
    0xa0e0a0b04060c0e0303040f0e040809130506040501050d0302030d02030901060e0103120906080903030403031e0f021c0509060f0604140115080f0c0a1d0d2004020304020f040c140d 79
    0xd50004c1c003070712414041680300341c01c01c1000303000d80c0503480415010b403018100702c0400790340d5500e00388245128140c24158000c070901c00544803c206034103c1481800240e606005a90f82c40d404d002c0403446020307009016800901241060540aa01443d40000d1003030021038120759811a4000605083e00260b038030400e034128110710702e50020341c0040203000310314100300310386800d451150703c9000c007400040416444044041810003800080a00341f410a80d04008855114400c90001d43c80040942e00d000031049480520740c52901c2160710030f10222018164030359400d10115138580c0010101c651060790703a03a103002150681d019940c0a0000c031171080700f10405000014200c1b03003000348030a645028120411400071000410740f410601c0300c1c01c1030350321281103514a40c1484400300d031094000c88811b519000f8442d5060107090305410000a1803040302103242404203030311044134060340200b908130000750030b03007032036800003804540c640b4100032081011041140240d1000007070740d0340b49445 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 450385962 1250 450384712 450384731
    0x2060d0c0e1903080306240d0b0a2102030f060907090e01020903060402010804080d0207080c0609010501051c06140412080903040e0c0903030c0f010b040b0a032604120308070f170a0e0a0b0406 84
    0x147c0b044905550301100ca40c03030090320300031030707882f200402d422191011001419030004640301081034a0764010014142c40d03641c034080000030307a5520b25105880125040c002100090fa4040c42200ea80140140142082d540d9907001581e2a5002500442d0003c80c208201529025503201a04441d84180501c0d40e0398800c3c2580c007450301001829000c0d540c0d252a004120340d42d03400c4030360362200740034100c001d10010090502c2001070130100410149d04034100200f10410a0005154800348844c1d1038640490301e03070780d094507507074007840c010011030580803404200251202409080f810400804403481d080002030110b08004600c90300d25402d03911200155040d16040c01000708659055403109149450f60315140314011380a0140c01d00d070210b0142d4403950440080c11103018040814070301c40001012729008040b8142200d108000030320100046001c14031414940035841c0340036840c8411522410301003002001400b183d10704901c11180311400103941c0951480c480c5008800000e2407441 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 450387212 1250 450385962 450385987
    0x206040308010806060a090b011209080406020d0f09050616050a030923010203030f060a0e01080703060609181106091201051909021c050a02060d0c0e190308030624 72
    0x201a003009205030040010401c045d06c80c501140d00321800390101080000402005031400b91f0b4a1401c4152b45050a168000b4007aa00e0028001c44445a00310340e00381174821422030325500300203115000141410805c00c41864808040c0c0b51422032002a4981820591749441c90642d00100450120b411400100a103011343e04c10210000c2c109070f810b02003040c01c240000d480348001040c030b401d101070b13002c0411a15150000c1039409402c2040740f40a9550712158016501d038400d20088030141e00780140454428458001c00d5280c1c03034080b042842d8100039540d0300a50f11844901785400240c1400000b03607a50303643c101d5401d500b40400002402c0c0c1003010503a00103252511440b201d481c2040303401001a1030f1802001200c51f80d4400c0f201c0c2c900101e140c00350408900321400396000001007a0070040440ca5400711340d14880d0350700c456038106035140034001c0f1841c101c110714010103605070301000894035880c02107901c04401080c0d10b241014942c8510300320304c500c00d5015294000800c08410340d88 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 450388462 1250 450387212 450387227
    0x320c01090806011d180d05030f10050a0e25090302090924070c170a020f0a170a14070f0c0b04140f010201020c0a1110090b0306210a0302060403 63
    0x8605409090b0540c182408a25454854442c111041082d4800942188803d0091013a0070000000340d0740c040d024404001c0c01c9400a40d0103007030492200300420100d89880c2c85807411240d014140c0c2c90000e2400c604510f4a01c0c0041004000c01c1d0a8a8070040c0c0c05000542540c910140b07481b101f030740c82c1c1140140050340800501d50071007079004101c4540c9568080514041d64076002003001d0069580980c211820001d404004002102d03030b0309602440380382003002d000d203c50705900f110101018400383d59910960b00801a183d020340440d41c40c0e0881c0d0150007006e154840f824000310b000100b09180f010b90344100303c107986650348040c41408200c21304c908000180342e81c015050806d41450101c03103804525102480c803405c0d40060000303099000303406503144000c001003583c200511500300440d8104003041803a10a0480c0c0c0e400142040c0141d641c1e00995030045110340c15a82c0e46010700403400520b000159400d15891480004088100b1020310000d120364081c040604051402401d8030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 450389712 1250 450388462 450388469
    0xc02060108071a18060f0d02040306111606020310030f060c0201180c0608040303060306091a0105040207031205041a04050102130b2d22140306040b0103320c0109 71
    0x41e100f816021102d21080c1c10785214405180302400b02c01d0658001520704d10400100407a6020046036042c540380199028004aa00440b001c2c03007000e07078100540c000c500c40c08882c40724031005429000f0200d00c1503806554445420303000e0744c2d1803075205e4a40c0c1485903046e9408903056500c030400c0c1d000443e0b0a0250310900b00a4958031442075442e0740c2c0c2d15120b1031440c000c030001c000b50807000805152082d04003070011a000f031010030044032141080307507054402e036080201000004d0000100d80c20581301704e51007150950f95484180210603001e802405019100303451284071900c00d0a03032204682c0c20b6034061031084000603507400d0b1880304404100f00a42c058150503905000011414900d20000203030111620300d400440034240381c041220740a01000c0c228074030070f2036034030050200d040e044042c161201d01201d001b10b09450410107030381d00402c03100100f644624200400004da494510718100a02000e10410180441408000f1250191031020303c10340c0310301100c20030365800c0300100001c2c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 450390962 1250 450389712 450389729
    0x50c12032706040311180c43021e0f061e1b011815020d1104080c09060607021f0210090b04030825050a05041703070b010f030f0f03020f010c0206010807 67
    0x1851300a11000c1e440c080e07608c220300c050b0383c61002c084042070f008d0144000f50a42070785040384d801c40d01401c03003509840700f2400c9024407080503c006c2c611741c000800c410b421500034001d040046c884810f05c0758542003d040501c03070f025020f0b010a080e0060742c01600d00c0044241b0000c0b00319824480b00c03070948008491980e0b911540611200105003c4c5075403103201c1501c9500540e83d007041ca0100d000420f800d5626404c0c0000104020902440100d10600b06d944111008801601c0300c0003040b40c03a21403401c0095006a080c044074061440908040045543c140151584000c5010744001034464a41c000c440c10303680c50081204054012440540200307881c884807040f1240d8400140a84d11051546c009100b400305c0d414001034828021034015008120a141c0401b0920941903a00e80051508a8495142c01d0003c074800e429684414200da80060500300c881c0d18984500305c6104030300c3c00650460040c2c80c1e04201c860402d000f041541c82c034541c001d007110b40c034201f0390714107021494009501 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 450392212 1250 450390962 450391009
    0x121908090a0b0f070308070e0a09020307032012060105160804170303040c061407020d0b0108010c141c020c0604030806030c01030c02070e0703060e0106030207050c12032706040311 79
    0x1045184032051300c00b42685401d100c0040c0c0c80b90001a41c42d002c401d00a10f5000c40d00c5140030489000c40d030041c5004000c0e0741c4092140f040152180c0c000360305c10a40d88140d01c0028407000960100c1d83d40b8440e08271806041c6246820218a030f1001c0112070300400b03544108000800304050303220403030704400c001149800707181141825a9840c4081001e03214403003c01100804221140810740c040303410159009100762410111441c2104110000348980c0200d94680300f000d86200d40213204184014a0054025241c80c01100c103240140c08498440325109500b40b08112020808003c0b280c040e50094941c003059103080b0b01054601490405101c4c10103007000c10340c41c111038002400005489200d2850203042c0e07500d030782c100c0c010b100e00c1e401380441000342000006c016815070300424001e40180140d5081c51100e50600c5440c41448064003040d80c010440c810f200c500c5640c444814014100740344150040352000500150270540040d034001840440700c072402e10f0715101141010024442181307 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 450393462 1250 450392212 450392227
    0x705040e13020d060b12010e06090c0609220204050a09021c06050a090b060c03161202030a170406091203150e07020a030c0302010f090b07030e07080606121908090a0b 73
    0x18040d0041c2c030f0005144580390801c884603959244010074403506080020402c01e05826540c65481e5007c0d101003d460084903000200c42c103085040750076800c1c014290720039003181c040c0786441250700e01c0c40e02400242e092001013160750fa0109800c0c02803845450150b00c030b40d100c84422000111001c1d0160000e4a064000c1007151a020070070421203130404030011b5082c40240124105206618044845010024108030504076034004c0c210414043c000c2124582c0c0700310745c260303038a00c10f183c00200800c3c081036002e20800c070b0a941d529401072049401141e0140e40f030b0350307500c0c980d9114650f16020a0312540704210801c1038074a08801003042d0b0200d9100c50a1400c1c0203911545c102ea405001c10003c90032000030704d4001d401000ba40c041c60642040000c05070700301100142429603486002a00b1700c001e0641c0814000750074000e0700c42001c060202520b810f0204039100712117013507100d01da010f4041e04d103403060030710600c000c030842c0174103445580c0b6075003c020000c9400454102ca00ba0400910880 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 450394712 1250 450393462 450393469
    0x20307060e03030f1b0d02060402010903140a02030d0f031109090103170f042304090c06051b0f0601030606080607050703140c010e0d0306090b031f0e060705040e1302 73
    0x1000c9035641e0400104803208500030030b0a51141001c3c00620002c0000c030500201c045070407a0b403045011109032480010f10840c2203850f24000e440c0030b030010300d1500c41400840d44008070401c02c00380b0213044540422250740030034241001140c020300480d07a030342200c00f42690140290502044691a0380c8c1c075103161000041c2240c5010b0002400d840b00000344e608099a0020440e44600d103155000c40d103590b582d1000c0c0b0565540a800b403405207244810b6920a42007038080c0b02070f0254856400c1c0c42503410110704513269009080c0c1036980128219269000110901c910858080c1040181515605608046082da41c1c00e034000a0300d580100304102801d94410103490403507500d031500e03000341c443c0c0c010102c0140c051705e50100c159520703200b0080c90940740001d8205140e0b4298806000d403d0b5900e06503001c45128819543e00b54211a07642001c0d1035490a000c070000d030740384d000024028602003410b481c080c8210b07080d4020075400030701800318502e00380d40980c0c0700382c1781e101d031004105455020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 450395962 1250 450394712 450394723
    0xe0f0d060e1e0604050111120f0910020a0c0b010803040305100b0a052d0303090f300336040c0909050a0207260a05031e04030324030203 60
    0x80c0c40281d5424444180c03140510600d290745200c1c50711041c054520460254840750244c908466540c81e01c0300045500401c41e040d13521040380b41c00da00703070240e6030500c440c1ca41103c01030035031917140101c0d244ca200d9421703140f01400141010307550380c01580b85586018031010300103820500b600c3d80148810070008000140c20490055a0b04002c24884407003c00319525040c640c000d140e100c600b5040460355686004c04040d2500803042c5060781c680d0400003450380341e208400c0400e8001c49000000308980c2000c044d02d051984841d0079001c00c0450240031072691900c065200c2040d50400582041480103501c2d801074410324111800b40b250401c814074500c081802920030780140d40350840c0e10703041c50049020780000c20008000707215a150000307100000b58480b590445d0042c00301038280395070381c00780751840300040003004000c0c0c50000307404000d0300e0380d0304003d0035410503680c40f44d07450340d121007460359243c01580f103514003155024420150b4908081d9000c29200c507100c05020410150354000790 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 450397212 1250 450395962 450395989
    0x30f09050706110c04050c0a0806011805040b120d021c0809062d0106051905190c050a0c06020a020405070201050601020709244a0601120515010e0f 65
    0x818840f5601c10010301c905000c00031415581c400c0c40c140030020fa46802c280100982c08a940e501080c5a83c3d000040d100d07100903041031360070b06062407000d012505080c4e00c50011640010421100c0600800c078240c58200c0b981100740c0182c0203c180d024000d113450401e42402e01141c20710b04801c0c5007e103e071607544d1400801440300c001a00040844403891a203d4890f580000b228048566031100d101510076484003680e00c604c0320210310f01c0010b0901c2201039582051880031b0105030319001b420200c40f0540f0401066486008000b0041d002507100160303400203100d217401900f0205024010803085903001440601964104000c21103181e90105041d019258141d00000300f0101c540141d42e0910a191813941c40d6401c80007012883c1d20f68001d441c50344004d1140800c6030010509000b0700c00c01c890302c0c020000038031401d0038011102070340020554803180c10700d03240100441300340400043c0e8800b504d154641c12000b03038030300c0c0c160f590150300e298011405031201110071410304086a902001d070364 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 450398462 1250 450397212 450397217
    0x71407060203040f0210030e0601050105041409060103181a0c040e0f2203110105090d080a110f2805181318140d08070c0f2406030201030f09050706 65
    0xa004c111150f192030b615280c01501600205003124400350040c100042d40180780d1046200010701c944c8214200c8003503c49070802c1c4c0c80e4005c000d60034003a040b04083e011906043c0c960320000702e2543c8180b20720741224020a00210440c14003800d800606030044d1480040c100d08000500120490320701447d00100c40756011441580c50b480107100c10991501039946413424000703001c040c10ba1011030540b03030020320030003048a51101d0341c15a03030714002100280d012403520000035441148560000301180d04810805151486c0d114203501d6a40c070500d10a4260210035003000921001d041305003084046908109140800c1c0402d03200d001c4023802c00c101d00c5100a44d00075840c040390340d0481000b15064403070080c82d0040a1400814103903401c8a1800d03d0b22600b00440240f42c41503010b03074040c0d40541c8a844441020740c403003901e0b20413905816110401ea880c07000b420402c00000c034092440214000280c000e003140b0004082d02c880d41c442507981800d05482c44042000801c1c41b01c06c895660 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 450399712 1250 450398462 450398467
    0x80a030b0d0f030e0f130e060c03152416060b0306010509130618050d0809160501140910020106140405011d0402030703080d1406010519270f05090714070602 69
    0x240c10300780d41c203401794002041c80c030302d8454541c0703a4001c840740d81042c2c001d40c2d400b959010128002800110f0b2200241241c0b41d40d685c400e400c1c542c0d500c1410109040b018015050403c06551480d484110f106410021600350082489440c1c13042400243c2c00b140900440d5150100092140b030f00070b40100e100502c0c0c45101c404020b0300b80d0000b1410a0400a0506a00c0250401c180c84e1143d2800400c00700d045a00003401809020a1030b521070f4290f0030f0410b031000c3c2020011140e820728040407083c0c2110801c1214500d82c1c84844803a03c002c4030fa8000b003001428401035668072602c2c0354100c0c0c011428500140410035684498001d0788843d4500000c0580e91400080d1510b9040d0380090101140000e0996100c9603a400c07000002d9180380c41d03001c60340c85c1d08004585030300c00d00c02c1a01030902099454481e4510030041d076a1590814001036003420303401d201401403400168442c0261440c003010412007801d003900055449041401c1002d100044001902140d10409074010a4681d00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 450400962 1250 450399712 450399737
    0x11203081501030e01060b12090604030507151d0a14150a0902030a08070803010e010e060d020108100f1d010807081c0302040f0e070e09070e0411090d080a030b0d0f03 73
    0x6640600c1c2081160002030281c0d0b9519561f03d8410380c442e9503484a50422800081c3c3c040c42d0020340240500e41c1b5a6034140f0305030305070701c0312032450000c45039040b005c0d0781718a143e045181c0580c0c000004038066030064a84401c4500c2c20381504089806000c405030003408033009501e1007500c50591140c0c10ba034001c00d007041035200081c00d142100d0401002c5441c041115001e04c0301d45400f45050b5040407085a40300c1c0d88800078880910301c200c030145da001119411020043d4800d42001d501310381006812100207031203900c0c43d101d4007001e80042ca03100d15038512407124030004803043c85c0108814009071a0703075810004013a8840c5010040020100f15030314000742454800d038115401000d50302c080c1c5a1090311000115201c070f50030380e0543d001682c0e00e040070311249411601c15000324a5925038807a0401c4c3c40c01403001074451014200820f5070b0a2103000800e0f200d011000140314440c40c1d00a58402100d0406400c84102c80501c90040c00e62002c6600050207000700007031515017604019034648034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 450402212 1250 450400962 450400967
    0x3010c0e060f22030c0e04020a090902030f0607030f0506090103020312130801051503060a11180120010209100c0b1909050f0303090d050f0406050304050a1a0609011203081501 77
    0x145400b005140854851002d680d43c030201c01c070302e080d203124000868110740d940c2e004c00420402650069807080b00320768200301911641d440030b8441880541612b00c5a000132180a00b000011a00e14002c00d4030780101d1458031855110341540f24408417a140c080e54110f80110f0b540742c2d2861600b0700200c50004030710321007496004000d00100f51903402802549030100280421100207030966002c0d01c103060200315090440c1c003500020180c0e841e645428010908003812400c510090714905200d02d48503070818000c030081c0d003543d075609180c00150360f03890003605103e0400d400354040001c0040840e15540051030803192140c01080000c560380c945627801011200810a1480042c007034803a6045251103d400440690310400c0d1a800b502e61791982c030302d01918584240100c048007580c08201c2030008038014809550454001d0003100c5000309a82c0d00c0f0820f46c0e8018501c002240e108004000e468500301d4019405803401d0f5004824190240d9000750024401a240300003d13504452980510303403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 450403462 1250 450402212 450402217
    0x304030c050d021b090c0901210501180e0d020a080a03112107020a03080403200d09030309050a0b0409270602030912190c150606050c06061c110a05060703020102031503010c0e060f 79
    0x101c815410003495335034100680c50f80012210301c0c003071903050240e00b011209020900c20f14482c06034000e00240c58803a41d91101d258440d40b0858181aa60802c88210300c3d40c0c0c4000d446c0e950840031889100380300742e58481c1c12100c8000c10b81c1d130031075000307a1070780c00080da20050590300b05502d81003503004080c410141c0e018030304110240c1c0b01d00d41301d140d81002030350ba4090030030310807203000ba11085981030303d030005d01c007007041a80203a1b0b0044904000400402c0d10079800080c60600094401400e00d4902c01030740806880c010003601e5143d000320500603000300600c10071b0402813414950f5481c01c00e40d501d00d080485e030400303c0c45042c00b0010b0501030a104003544a0304250705200320802441c2d44030600a02660040c440f094078500c5804c00250003400d00440360003c00a1610114040394000e0707641c00480300002c2c0d0015082440c00b01c00103016100d440203403c142e44681c0000d85c8914021041300e45441c00e408006100b0381c1401c0c1d10026254101c0c0301c01ca04003400b80c1d24240c2d91010b01d1001102031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 450404712 1250 450403462 450403517
    0xc0b0c010f021c050601031a0d06110f071505072001060e07050a0e120a0b0702030405100e041a1e28030c080102040803030c0304030c050d021b090c0901 67
    0x107400018509001e01010000c0f00c00070301c000000304070548449004400b1070b00c4908400341c80c0c051640d4001201c1c07801c00820302d4006e10408010641c02204101400c0d180c01c2001908030000e008610101003100448420188400644040109183c0564000d00b0020700c0b280060700c1590340c00c05024103880079041440980406c07564251316040c03181d40249a42c0c403000d0702200041124243c0c544c1c81c54a01c44480d558102c2800170b008904803525021901803014014100b988020080000c07151550b03458910181c4003511140035203403500d410f1105403504150a0808401c0c41329605000b5580c0c180201c1010045074000030030400d0b1100452440c009800000340f00c40d00c409440100c405840c0358071020307244a5800424240c2d035441d100381c281d014038011916190002d1000400c000022000746901030700a20307012040e03581c0c0d620703028101446003c0c200c0040c1c00c0002c2c1000316400507a80e100900c14150740c440154613041d0305841c038a00451007414100b000005044810030a020300e0101030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 450405962 1250 450404712 450404741
    0x3081809041b050607050a02010324030318171b0604030c0f0305190b0106080415092303090a05060d09150b03280219080304080109020a0504090c0b0c01 67
    0x50a050600801207480058500022025004080360f81e0514074180d450b4964008000c140340841030f401540a0072081d10707420341c443c8001ca50700185c3d2001210450055020740c54691070703114480c041500000d22504402030441c80c0e5024007a01c0708000410015080401e040a60003581a0703000079840d06c10355101601102c6140d90218194100c06c0d9450210b03441007040302c006011091504480d1a04244d019003e1052200108140c6003d2012203900038841c1d0121036007110803d040708120f40340041d0988582103159982c6840340c0071410590a00207021000b9800c01d40d40c640000c0400c42d980c001c440c0036031000700304581030071a03580001e290303540d10161a8207075290b880518001041c07084480340c880e2040503040300501030b0005e02141001a050f0801c03800300800d070203000c03441d95240c8800381081221031000850308406d2028002405404c4008240403010780104002c040380c0e50442032107103191207ca5400a11a04949001c44c0e007600b00c50b54448407425940c9004001c01c0180b88203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 450407212 1250 450405962 450405979
    0x1060c20060307081008160f06020604020105070b280912020303061518120f071e21060e0714061312080705030a0503222a080d0905090c030f01030818 66
    0x85055105519020b45941d08d4015003102e6549508070baa492703042d00c010340440d00c100500008a00c2d0740600329031101c0e81900c02482c14240400c07120001149a402e07100f1241d490403406c00700080c1423800c40449178944011815400d0000024031041e030b07075082c1c0495075180003c1e485241210380418071480d05000f013904481201140340903443c3d001d4889001d40c0d41c00383c2000452050781d1103d1011508103000702000d83d080c02c02d03c0304814000111403c8649069024510380012042d014147c2e64034000c602034070456251125129040b100360328401d100384805d00c0380c1c03114243c0e181c505008481911072100322180c50345c1803040082c4a5024044c19a01000400c030107071507003040003140144030b002c224011076040580e140866400c40d45000308000350070865943e02c00500380b40100ea105021340310189256580c1040d234607100c14214000007040c403540040050b482d000300581d5005080590303d0f882c629083d08000300e90141400f001302006c00114598203184000c0340c442c15070f044050001c0300e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 450408462 1250 450407212 450407233
    0x415080703150e0c0111031b070501020c010c0809040507090905281404170d0204090606080709030b1303091e0f09181103010902030601060c20060307081008 69
    0x585a0000d400282d4440700c00742c69640c400190707441603200da0a641c0c400b601c041143d0000440d080191012101d0301d80c8414030000010907190b90100110b995003000414000d031412002a09003003600e00e0850620503095010004504980211000040110340016081e0b07610082030300c043c02c0d160808540c052400c0100b01d0405c0c481d03151500030f500c015102d0140152902ca800703042c2c0300071400360f40c068152a008980040c3c558421a605150762000c090b052000e00e0801d0000c80e00940d0040f041107450754000c12000ba040341c1807030741140142c9043c1d00d010341907403a0401e100602611903480d0703c0f81e44070706005041c1304e1a00980642211040080484800020349807c441140a42500d0380341c2c6c0c040c006a82e8032141f041e82100454640d0390707081c5410a40300c100303d8899080c80280c15549500c44413006a03014400e887c040d20041e102c411184040341030821501c2c004103031103501c401c0c080a200700d4581e203000940c0d60207041464072810701da44155000b0003514240c0e00c2181c8a200710307c0b99a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 450409712 1250 450408462 450408479
    0xf0828030b09060906012c0d0501052202060403030503060103020f190207060306210606150210060e100b1b01050907050114040e01050d0c1802070203060a11090d020415 74
    0x1c5082400480381e000480d19031074200304100348203460044c00300d60200d043c00004046154015407a0140304241103602072008045007908034030035001c4030580d65880c200020392000d03134600b045452441d105403141c00f03d26070114125118500016051004c0440010214ae20a0b01100c03801e10619030410f4543c00542106150180d18144440142c0202500854518403a10500d011228005003902010f420202030080c40078403048141e807603503194207010030600c0519035154002d650560007808440c594075035180440312207401001030034a4201c14006003282c1c0d111180d00b901d8400440e0399a840540303200d07101c0340c00d0110711804a9401c240c00c0001c0e8060100301d41040359400c0c0c0b6400007090240000c0c90440c881d03402444016900c3d0380041c006414080c01e8001c3c048c0c40b07801c41022158650b0000c00001000c2240e1169003600042d0744011400c06000301600070702d050b0310521060003498404a0a40155404a03000e407480070304043c25036540382c000d07451082d00c0d60b000c80e0241e900d40c03415 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 450410962 1250 450409712 450409721
    0x606030201030b03010b0616021807020609190203030706020a030e0a14011d070b2b0209040b030c011d040908030a0c09050a031a0c1903060e060303070f082803 70
    0x3640840d00d03090241c000740c10180034510320440001d04042c40c01285007a0030204602900c0180d800c44800050314040d4011007448074007a0751140c00810311443e0551500f4a06141600e801e10854107400022005840000c25280c000f07074000405a02c407540b0a00480091000651242003403281e410290305101c242102d401404070750100a1201c000441244600c0518100801c0c0071135000410400c0700350102e0016202c43e45a10910300681d01400c0700c80c42241242d201c07940604c03580001c0c3c801c4145001c3c42030342e01d8104103601800c420050301c00046c0501403881c040d410721a1038030503070014590325a032012406a5011404a80341d05240e1034030ba006081c62500000454010b01002c5180e103072420360501103079071000c2d040642c40d07013851601210300302c0600b04156510060051000c016100d0300002e020041c5ca9800040891038194003c06110b03020308041d010750010445c110211307400c828500286608401840d0f43d271745400c0b0b82002d1031603248009414a100005240f0821070341070f0030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 450412212 1250 450410962 450410969
    0x90203100b09070306030b04410c0916030f02300109050405030a0c1a010b07060f0b0307030314093102270a0305121e070804030813050d0606 62
    0x6009050307650b203543c240c2c112152800060038103a2140006000510700112100314142040c0003100156003800d01603400891842c2e608001800695150000b02002c0118010140f01104c0c00d10301428011010114803240814000c01c164403102c41c14241d40f4550125031f844071307840c95080d2902d01c95450111403258002c17030100e06000c4000000605503668001d40c0d0041e038100003d50700c1d00d101240c042c0c501c150099021a08100d030060340b5400b40112110450081001800c11961410b4a18040088850380c0100c00d0035103241141e404800d460002d400ca00b520750604120220f200d00c2340c4d10300518001e009910707178040121b076040c40c44401407448101502481c1c0288030000720a04c00040c041e40541c40d9507000c1c0034403844840d0114940d060980002e148080c0032a500b5a84a032606401c4c4a00411b0100304400c0014201640051003000d44151104502005051401d55036501545104522002e42120710200380b02c852180312160450042800901e00b84441160b843c110024280512 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 450413462 1250 450412212 450412219
    0x304080f030a0f05071b030f021215011202180c0702010908030a050703052a010e1605030a02041d0304030f02090f040201080123030114010e0702030406020619090203100b 75
    0x2266804000e00000355580502d643e200c0301042041c07240b0480c0c1d26003140030305480c020f4000390304120740a140c01450b40514000c00d80004801054018040d4008000b86010016031205038a1140f800d454007005040d5182400001180c07402030000800c903200300542c4d0000300c4944410700200f028244000c0084078800e0b201c084003165244c10043e160300a0000c010041441000b204001900c503400615010400c88003c0e040c216101002a02c00845800c006690780e40d00c1d20000d640f007600304000c090311001241300446050034800400c1c0c4a4841c083d00074003e580318010208402c41e20900b00b50303080502003c50781c459589040040814a90f01d000340e00801034800407410380308a40110300d10864060f120003806918284108050002000b41540d211034100e1045915a40038003c0f4540d81c1400a0300243d00c2d414140001c10846028040b4015988200020040b03da008a000c581c420340108074581c0281030700e16004040c00049030000d5060103010000b03804086540e21070ba40800c4250f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 450414712 1250 450413462 450413473
    0x807050105120703110d09120306051c0b060307080a05060a0f0209010f0c110607081201060c020102100e070b0c010c08010e07140706021e0408061518071e02030408 72
    0x214019100c0e48541c8820b0b00b080034050000482c454000e4114512007040118500e2500155036540e07411160310a8084900d440c3d007201501019034140900805400110356049408403e114806844910310324014890b01c00c403030006a90fa41d041c40a60004d00100040e00c0d5a00054a8016210030707080f989840102d180c01001400c1c2070b464825951600030684444407001e42c8190144c440c10044101141c46483c410500750903a02e82002903c0c00501c180440707511104400d2150b00380b02e405800500c100492400c84d600540c5e40010b034160325000040d0001540d188015900d401d00d020790b0030580301c1c4800004c05181ca00015488105055070f80c1c1c1d545250782c2d032101e4040d804010f05070b0b001c8002503118803500011041e400000c04206110f50801481d10b0585580248200402c0a40240f00c003808141003040b282d0074407000f03030f0108440e9004101c6181003400100820303041c0d0b5501c00c2402100e000104a68040e05180c082014041c4001030b1411200320001d60700d5000e8003500d030050180 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 450415962 1250 450414712 450414719
    0x4060c170a080f0708010e061315090902120d020a0f1b0e1503060108031b030d0c091d1311010507020d0c0f0602060f0c0924071101080907091d1005010807 68
    0x10b0b55120705842d103003c108145230b2100070030000389d40e08454802170030b0396990f209240f103038001900000040070380c0c80c808141520b01e401000550175100160f203645800200c071141c2d1881d40810b1141009600c41d030f0035440000541000d01c1e07241980004000e464085100104070108811416489552030500b81041070755080d00340b60f181c0c0e03400c0c8180309a66005004480c2031054241c0d41c851a030301e010303007200c0c141948070501200b81c4da00c10300700d01c001c200c0214087c801c22030035440c031760100909403015056904100711911003040d4171500141c1103440030345140080c0d0f84540704942845400500303140c07080c2c0c45400d00070711700b441e14801c4010118001c400000c0e001e0001c01c074075100b02c2c2203005614407640c955030510315076440700c207440783d1203446046122070182d0401500040c81b5000c00c00c00e526581c0740d2410f800b051111403115414046400100300800742e00254600550700c6100000c00c0c296645001800d41c0d0400c80481c4c40d03503003d22201000340d860b0301d500c010304948540044903403e81d078 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 450417212 1250 450415962 450415967
    0x50705030c0a3f050904090b0a110a051e0405041d1009020d020904050106050a06050d0b010509030a02010f03110d0516030b030303040609080412140d090b04060c170a080f07 76
    0x140c014208032845890741085046580712040300d01c5082c03e8140180360441080000b000c07500c081100715681e8011400f40081040e50384640007080d610090940e03d014400000039106000d00642c5c05d00364514866400400004030050740c1c000d001c090b000317000c00c443c0086c041c542d40d903202051001d240f0a244070081010554010b07559496009400040e202e507554091092241c0024030a4510b5034030781000099545a030703880c4074000c2429580e80e5850381c001300410425113400001642c1041014082400260350100d4001d00e4641d09080c202c2c02c00100385000d80107030068070f1000700e602e4400308008a940700c81d41c0115202d0b08404003100001c495210054044030b801da40c4040e05540103000040c0041c0e415440540c2c414003428049042c15a28903007004480c81c1c400088850140c06000e904201404201d954201446400c103a03000d98142081092240114400c1200300120318812006000e00112166000b00e02d920440e0380e107001d24400644101420307100032001d400f0000000c1c41d21072 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 450418462 1250 450417212 450417263
    0x207053313051606020f1027050705030d080702070608041104020c010b06030a02040501020106050a0b0f160210090321120209010e040606030603021302090d03050702010302091e0a0f031104020a050705030c0a 91
    0x100c40d03201c500304a0155141403460031100c4404c40f0310344103c44001c40d00d33940c100001282406560f58201091506400007401c184040d44404180441c03541801300140010b510742c45404000e540041e11403101580044c09444a6401c268006d0000002d001104905030001c10070f8510a07002401201d540b1824041900c1840c0701d40400420280058101195190020507420284051480e8003a20030b03000202c0e020360069054010a01e201410800c01064402016800b6204203891014800c201000b44c070706844480c1090143d94001500c1025a020b030402400280000d00b0400401e40c440002800500050005911031020090390606998050003220881c40001c0d0844201e001d00303a600b6902500446012030506800b4010484281c8800303140c0814010070a550410000ca22020b014040b2100d803c54052400e03070301c40c1800403540c1c1c04481001c0b01c8044e240141d8403c4204002c4940b802440002005030000081020701c4204c0003803449002030242038050500c82140d140b0300c03140c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 450419712 1250 450418462 450418481
    0xf131403150114120a080d020405090a0515090901090816260405040c1215090e0f032a030a08010906050a05010804060f0608010207053313051606020f10 67
    0x54440103a5a00181003081401300300c40c081d84101d0f1810043c0d503651403000c0d0410304242400681c042010415440d01a50040d003010309550200000d0800c48105c1a01c1100f4907021801a0b039040702180300500251b201c019035076040000b9a8443e850f00d50710001c411500441030351440715107540c6540c0c04182c4c03c040b55060260340e804a18080c540030a10001e4445801c4203000d00160080c5140340d01241c1c0100c9110150300007510200d6801e00852070200c03605102048040c0c0e005810980e2021300000440d188581e4820351308000550100d80004044400103c407407950001082ca045942e40203192141a01c0c0380d000c00b1300150344c891081c450f02150621906002843d100f000c5130110355240d012204216000e0f002148213910740e0789803405c0ea84000300032109a4004c4800c1c007642c170303e54004e10082c9000184001c46010303043c0d00d01040e024024104001d160640403001e400c20074200b1413142100000c9041d400d02581d103440c0030b510780d40a030802c28918002d0030002000c03840188180340340c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 450420962 1250 450419712 450419729
    0x717100b01080f0f0432060f27030f0f070308090a0b01061d0a080a2009061309020d140c04060b030c0903010905010e250302150f1314031501 62
    0x2140e90304c00b8144c2491001500030744000c0d07201062903c00b0404411510500d200f60340c1510f10b01480002d003075103803010061800c100c00c1d002d80d09004029011815000701c1c080c09a04056100051221079415445031000c2c00504500015140101100c440d010300f81883c001d840300d020656039003a12540320050300b90014005401d00005000c000e000342500041021116101c0905003c100d01041640e21141c00441455000704400b100704822030107020b200c403d000d200300c09010002e10100d000708101801c241e207d031403001c040449010f42507004090042e00145514a04180c0703080448a14117a50010802d6001320744043c0386508050241c0011141c100308038515503a120188405590045100c2d140d05540b00c3c141100407032000d01a2081b4203509070301510f12480310410291100340140911001504864410000750b584c22030103107842c40b49403014503592041500c03e480140308050325030b4815052035002007078070000c101084640003410380172a20802c4040300c05403590703502441081c40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 450422212 1250 450420962 450420991
    0x50a0e010f0e0a1e06031107060e0a0812070e06160201140f04093606020306010c05060405010e190c1503020c100c0e060c0d0806030717100b0108 64
    0x4194403a070300068214901d407511050040c42600014584030b419402048401c04140c401c00400031a034021000424a030300741008601c51000414445014000c0060801942d60380820a258400c2c001c44808a600107040741c4d07505070203540030400d01e0b0142c5110000441c040071080c0d540c02c1120407a503d03401020044c0c446d0403d19401141d4090021061500303244050061010712a00317240903001401c4680d00c00b00703000404074a0845030781c142500482c40001d1207880d2110500d01080c00c4514030f900050090386c2e9654100050701c0720290300c2d60040c03e5201d40b01c00c000c14000d0661050030038880b0842980d08885405249203041001003401400700020000200072075400001e1400c096001d80c00c002d4144454100c28a04213194504103480c4962110780e00c0d41826030180034070040200c00c4a015040c0003048401a13903c0c0240226074013401001f9003c124250f0701040480c0041140c0b4070040d0189003441126900e42d03940983d900c010604101402c00558050403039603108104611040c817 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 450423462 1250 450422212 450422237
    0x60c02040c0201020c19021005070f110a0b04031a010611070612090c1514040b030c0d0915060f0b0f0313081207051b0c030c0f01090b1810050a 63
    0xc11446000d6070556600304215003000c00f090000400c01980b541c10440c20041d00d0040c0050301d80440c0e07110701000800c200880002da844800701940c25004409040a0380545d00883c0303201055030043c44030320101203400010064103402c5103204030001d862920050340d0340c000907140810610700001e15030300040b8081c840d46102d40882400900141c0002c20700347c8598a81c130044081d150000940e04200c4100d900c2d03a240c0010242c100784031102000c61800b440c0087d41c10700d500010380748840c24407001441030101c002a03004007108031782258080d2100a18090504010100380c410140554240302c000248003e00350295522000c085522a02d595641c08200c100c01e0740c0000100c0d820081480070000c403504074108184070ba80603403156640c96940e05a0104050341c2c000b88201c0d6540001c01c0305000347c9010900011924058130890b030036002c0f010042c0c0780a00950000d070402d40001c104082e04640141070030089080035180030303081e414541001c5840f80f1403503100a020404d94032044 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 450424712 1250 450423462 450423469
    0x100302032d0a23010f020309070806010806041109070c0c0e060a14090402090718030f0201030b0d050a0b07110f010218010c0816060906051e0a141b190512070801060c02 74
    0x1150f50860b20400080c0003003141c110001203070420780b290543e5600c000d00920a100702001581d000d0a00c0c00000c1c52145401c1d82c3d04040c00080840b0640203003050400b140003d4002c0b003240e5111503005a07455822500c40b400c0300404802100e02d0380c810780030308200245664091416480444000c3c1c40d00c1625640c0d9000e101e040c10018212004000c00c0c001d4407541025074010400155201300741c449040450b5000060603030700002c0901d840f404a110b80c21000130400100c2d03556160b80031071440c070280c0d60407506842d121021102c0441d1f50052a107028858401940248400c00c0c2c042c4010110424520044488200c2c19500030156807042103a80704101c810406965241d101c2d020108a0851998459094890a90388100703019403940c44900e00781508091030380d10100c280020401e200c42e1000c018100d14000e0824040348502c0441c101042070040e04603a0a0b621816110ba041440340300c0042050f8413110743c3c85200310401c2c000c1420144030303587c264121002542c401045000325001c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 450425962 1250 450424712 450424763
    0x1051e06120615040617180f07050a05040501120303110d0f05010312020d170c040b1c0e12040302090604021b07090f06051f020f1e010b0d1703100302032d0a 69
    0x540b007284400d0500c03407c2101080b011140300720600140910f24500001e00403005101d812443c071890402c4010b0041d84629009480395a82626004c1015101090034422a12078410302403002c40c00c00d50400c2208286410a41c102d0f403003420511141c1c1c03c6000c4c100e0311030480d481c9080018041c80b00003143c1205c61b07000b1681040040023413500c0c0581d240d902480f254412060004010074002d201ca0f0310790703160b20489044500b004090856041e51000380301d00e620950000034481e0490401080aa8490354152450908821101125114030010f102c0d9250301078402c0314411400c140d40b250290249014510440300043d103d480d81ea00824501c40d80b0a00c0f0032030041c2140706544140d42110402c109442d00909030150b010700d01011000d819007940c07841952180100301890038400040c1117510310400409503591069103a86a651505c116407407075a10103545031103030001c025015040c071100500e81b00101040c2a42074580e240d89591180b000c4400500f034207204581144e40654078030b51 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 450427212 1250 450425962 450425971
    0x1715130308042303270a0308030105010507060f0501120210031503080901030f110307021002090f2205070503060f0d02011403100f0b0d06120b01051e06120615040617 73
    0x60070f1424052048010f0328503004130301c100c55820105030310b440b42070301d00201490455606640c120301d0f050454549042500c01072069604010b00041c0b48002d010031130344080d01800d8400803d0006584d00c190038120848402c90a030703c50304806c88a141c8142c002d200755660441484a4280454035645400c0e4454201105641c103168450300003c240b01c00c184038802c02c158004007400d899090800d0001e20380510700340e0300480305104101e408000d07030700c22019075001d01003111024411141c40d203004460030300c40000200c009042109100e00c0e03a4000003c0c5204040c00d0311420b250087c0d8904002281d1804d00c0c0190100301840410004500f41c3c2009503880f40380b400c01e2105150740c40194400014042d8481c4142c60400b00b403010300c1400c070323001d0b40c0002c2c44205034110002c2081d46500201c0364040c0b1940c5e2081c4050034680440d45d1115a86003490040140520340ba518003001a44e45000115000b0744208500340519034030421420a49054400340e40d21030303800000304800e40c145010040c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 450428462 1250 450427212 450427253
    0x16050d180303200a0f0b0109062402030f0a0503041106030f0f041412030f0f010501050a030906060306090809090702030f07020d210c0b0f01030f110406171513030804 73
    0x200c030805494804c1020f980994410302003403100b20a90f00b040c444401d010f8018844080c00c100040020048240350010a9544100342a209903401c000c00d078914864030444844e481c1c00410140081a00617024500c134038054402d2034031400240040107040d10084808121098200c004210710302c040d618410360040c0300c0c8880c0f11014048012407450a4540424102c1c22040002000041d0071004420f50300b0128100c805040d5505080002c0c141d401490200b40c10140d607152140e0600c0803035045034004603001001008100114102400035900c0b140d40240940b083c1e901244001388004126025500800d640504065207a4200486100c0c03005041e0b852042c40710001e03284000d40ca00c1449d02c4d5455851381d0200b40c01e20b04c1d089801c2130004091030205605500100b01080351000703400d400640c4034003411071010031400000d004080e40c0c0c202c1185210b401c02031440e081da000945110207a07400e803140d0341c7d540c0ca2801c12401c2c410902c83c002c00141710000440c0002d01c00c102002008040e10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 450429712 1250 450428462 450428507
    0xf0204030b0718270e030c0d230d092a060e03070f081f14010e0421050a020f010501030c050402070c0803030a090c0b120f06041116050d180303 63
    0x8080050804d48141c2c04a11001090307955a4400c000d10321689150140c2c00c0301560420001c40c1e1a15103036032000b10143c0030700c100744400251000602035525408501c071140c01c3e4903012140c001100400c100e0b0821501d00d003950010558a10600410101d481c407441e03a10101c0c6400c10808541d5203d41041c2990988100040420007030224640c2c403010700007240050900954004018180000d080c03086100e4074034040b100c0050740c5040c80e0039419100180580341a98890740f80810215540b4041c044004120190f0540c004d0f9000008000d203041c81c0e821100d48900701c0c2003280c200d074401e04c801080740440c0740003000345040a4001d4003112f0700070380e2030321141a03070744000364116801141c401700c0c03040c2c0e282900c0b020810031204c1308029050381d10030310b82400340041d0400040000542900034408a41001680b10741d690f8004070408660040c0c106d80341c062091107115581c0c3c10780c00c1101c50b8080e1041e03003100c06114410b807444070380c0c1c41c06000030100d00d561400d44501e05030103034040c1400303500c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 450430962 1250 450429712 450429719
    0x100b03010b18040204110c0604020603060d050a0c030506010914040f020a0b0f0c0d14092103070303150e1e040213051801060602030f250b0108030c010f0204030b0718 73
    0xb0014003480310b50285454461a00e020310400007119401860304090420a205440004000103181503000b641a584c066503500d8070780008a16400c40c040c01012441a40415030400101d001980e00b20792107503040b95843d0341c84000f0813040c3c1da40700c02c0c1d03007509591110004001c10550300b002804140040c048203001c07078940308c070101a03901034411000c06050000c0c90070f4030058100190701c0c2210ac02e00e801c616400e40c8034800d0100d0301c80e007130500d8460003d50050141107480e5440b00440701d002881100e654070703038610300500606690742d0000c81000014100043c0c3c003850042c20751154608803588685a800c10201010005011b0310980c0c02c1002c0000b0b00d400102607118150084000c10f000b2003c0c200450182030a64507560050000c42d0001e010482d0a02c20000540b034007001303009005c0450b0311881c0e4407910b03940010640540300d1110903000040c02c1502000410403102c014000f4040f032880d00060100703a00c5a40710061100c0b030b4590010346120302c1011048001c0d018003007010b10b07481e035 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 450432212 1250 450430962 450430969
    0x3011d0a02190c051002030c09091902180a0509040503070f11131a011d06070f0510090b1b040b0d0e0714012012161401051602030c100b03010b 63
    0xc0c0c020404600d06200f02000d020080200c58000340e0701c503009602c0c500d03104070825007900a8103219401011440c01013408e61600403803a110000c1440021503c440350080403000e940c40031542280200000c01020076242003415040384240d40180080d4541502a03440c5403500c45414000d89005054004204541e5141e00b4114103080c08090003041c001e44040480903084184000c50341800440400c54040c40410010300c4041181102c2051f124400b50805051042d2200b03001441c5004038981c034030748125a0b511442e4014003802c06650f00b503a91802001014015010644150405203c04c008171040a0010020703e07551010108041010809a900c0c12000380c0040c0c017902a40d0607900c055581c45a0f0303950302603a0300d20140c000444080d0355951510244160211481e000103880e1000c200c1071083e14003560740c0a01c0a200b0101c4c0104514000c080c00d070340d003424050981800c401800c1c8000151818511481c0107004c1c0c60040c0303401c2000030700804d8250394055403102d002c181c540d038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 450433462 1250 450432212 450432247
    0xb0901090305071509090203191107081233270406050a0507020a03050d0c0c02090108071802030609070305090f0f03041e0807030b0720030a110303011d0a02 69
    0x42d10041d02c0c50340d440010381c045d1010b25140c01480300c5c2072050081082c404205d051a00b01201040301c0050101d10b5030701d980b1132a100f4075001500d5030000190615941c0100c03459280719140d41c00fa00c020007805410103c1c0400c540c084c0b569190920340c052620113181c40c0701d010701f9201d01e82100d40c198000308103030350001d0704d01103074141c030015501d1003080080b1207240100c65100d103051024141100442e94042d080740105020164140d07942c0d84000e00240c011012560341d150010140c09040d032b0341c0c11065955691901540a204140820000c188615802624007540700200702840551740c03660b040f401803034010950844d5100305056048488001c1c000f04102400900c080c1d9601e0b8240104101240f00c0e00c09642003c0d2524402001090000304000c03040c1c9034480710364401d607100c1c024200c42e861411100c2e8090412100e44080342024000b00a2100002d84d840b80942a2088043c080d140c0c0424401c203504500c00d15018090014002ea40d903620030150034005091044a00303600007050b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 450434712 1250 450433462 450433469
    0x30103030e0f0907020609060709050303070305070614040c03110f150c120a09061b02090c030c04231003060e310b0702100507091205010e0f1b190b090109030507 71
    0x5802c403109010b4078113028482c10758032209c1400d12940c05c5140c040400d9885c807950b900602040b202103030704400c001c1c05070048245e02d402e60002c0442e5003400e041c00310250110740700444486c009403413100c1c52414400041d24914100400214171007170340003040b6030a580111400305140c05800001062030b41c00382c2c0544540b18080d5224078825007060005411a40c0e00c50500b07200c4044480043c005a41d0f00c0c1c8915804030700303103240a840c1d441c0d0035001e26080c01150403c80310503c5101c41c003c156484040b00f05120001164214441c1719802c100350200e03502c6000f000e80c010f14800000e10480451180c2e40d1080e008182d5410a00301010f0440c122202c0018003154003217800824054044d6040004000b415a1820100074038148480050560242485030003c00c690195415040c0300081d400000083c0c0e81c030f425111840018040991520081044101e81800a0400340305506104070175059004203200106d036000c1c105401c0d0b0300c0c6038005c410003038100900c101021000840500011008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 450435962 1250 450434712 450434717
    0x1e0703030f05072003010f0b06030c130e07170a05041703070c0611041d090d2a05330402062a010501090b0f09040b07140f0913060803030103030e0f0907 67
    0x2c5030084005c06003954007000310320210609104549100e6944c95080380c3d04004e400013895901d10750300a82100031200d40c3d0080714000c3c080410401c1c05a0807641d504410340840342d00c1030541c0e0364040318904890701a10013420605a82e11645080e085d0b07a0000c5403c1112030502881c50050b0b41e40d50b0003682c41d610102e20b0b41d4a40070500700408400586031003441d1020030554400d034a8410b031225a162282c80d00c5404000c461209a1003142d20100451848110001000c0780d0144034108540d880c484d1801000d070301000d20404000d41181e0b03126201c0040b44041000c40c3e41c2d01d88e602001a9034002c81d03201c1c3c1402c403122803002011301c08400c141c0390000841002007050b600d401c0c0c45074101c0e61726000460051481c1d800680c13280d035503680307040da0181d444190100d00b5160a039080f500e1b40c01c9001a130240444c0000c0741140c00c11154080c00e0f0101e07044500c071015131001c0303000e28103441b580d1040c198240d00510040c0002400746c41c034441d2841c030180c98909106205000941038040950340c2801 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 450437212 1250 450435962 450436013
    0x10b031e0607020102070305030f07120c08060a050108100b0309070506070b040c0506070b0c181c140a08090d030e04050709170d020c04090804080f0c01021e0703030f0507 75
    0x480e12414810158071642034002142044000c2e1400f429030300c0001c00480f4040d0300000019181030150785008049000d0410412211081d50f00140c11800142c4085109030180d280c001155803203004506c2c4507003440003071509050300c0c00e612052580c0006e85420401c1c052440d000ca0b035078590101a0000b00d00072411009142000d0418480101c0e041d042076008480c200294000f00b040f1110154110220420b52075503145040300c5807554048032480c096111446000000d4411070717a24089410320302440075012040c0030810040e9441c00410381c010300a002c1841540340c503152501101c1d1310b80f4004c1c1886130203510494000340c101e0b141203c0c1d02c008038201000600091440454091040e12540018140400e45d03c0e40607540c1c00810305081d10403a00c401c0340381d007000f00200503174004010b031400f29003106903001190781d1114400f1311424011b118241c01c5007203900d070101e040f42140d002000a49002403c64400b00c65405080040303605000c07040114000003060b24900c0656029007012884 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 450438462 1250 450437212 450437263
    0x5130206221715010608010f0b0f07020a032607020d02090c0706020d0203011404141f03060608010b0108160906050d060e0a050613020c0303150f030304080d090f03120809010b03 78
    0x1843c0c108180c110004000c01c80c0e0040c04402810301100d010340b8103000301c0c3d54950035506601c0e0741c0d81c440c4c968000d40102e507003000002044131145081c3d1044001000e07101c00343c0d0616910703050500404402130740c0028404240c102504041e00030303903081b9407000030151400440f5152041a6130011103000c0074540c0c0000100550300061040175850b8800301e50620030a4824080520310500241102c3c250106504c0640c408449191240000f5130313004c0004e004265640400c2402000c0071000d19000c105040d00061004000c1582c04070039061589480c4405c038207180c000c0750190464018100c203181c0d00c10001c5000504001c00900c1100b40c444080380516002e81807107d41008480101c008600500c0114208600441a42da000d81c4039014400300c10049000518074484201180d40c2501001801040000000c501c0c800441a184c0b1600e0701d80380c0e0b8584000c100c084074403002d401c3c41116030401c00d00c540301d003c040380c010462800202e06159100002400d100c0c0c1c1c101c0c6403080b49400308a0a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 450439712 1250 450438462 450438493
    0x2040906090803041401060f1d1f06030204030204050703020f0a05030a02070b090d12150509040606050405041208090a02010c150b04110403030207081506060c0f0109030c06051302062217 82
    0x1e4014108c03000b640c00b11140761007045038a11050400c0700e101c8030090000941c0303075907400001e1b041c3ca00c0c010040072802540d90401600940c4103000980c080c41c10480010b804602034004c40e12a5100306000500d000003410041b11b654201601c07800401381c00700510408102c0302201e55028448200140c564154248005807410880880074010350b03003010420b4031f41c5000c0da400041200d1040e070381004160340c1c9103403140091000f40c100907170280c6040f00784424000c00340100d940400c0ba507203e42c1d501707445012280d640d95282100080c0003a0140c10302c0f03c00a841041c11114511140c6404a0000130040000d8141e80184002c120035110102e000c00a241e41003004100030b015500c043c09110b00300c144801001c400050202d406003000080030304003114104588000070304171100030440034a2a00d001080041102d0054444904000218004e4046a1805100e840d4014540c6261070101041032400c1341000322040861200c10358009090450748540244285110f0040c3c101c050b040783c10b1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 450440962 1250 450439712 450439721
    0x30322030606032f010e1210110a0f0309170706140702010b03190c060809101103060f0f0315100b0408030d050906010b03010b070c051f030c0e01050702040906090803041401 76
    0xc00c900644d850580889903005910240102c50540d0030424010100e080980b509600000445090b0f1030224050512000c0c100a440c5903016550b0741e07940c0c0440c011045003550b07214403003d005207103e0a6402010040d4a00500c8014441d0030007041e029000180c1da0380d420011540700d00942d450340c0d20140d4600d018800380c68201d4040404541401d4030303882d03c0400c00b841b40500c0d03081c44180800725120350020400c49a642d8403034001441112500e01c2c0b1010329410503038803e4020700c1a40341c2d031401e40c5400d000e060550200a8020017040300100c1d2403080078440034003460400213207210045198040000280007501c46d107801140c2d00c900500d1107804946000344060340c43e8014400501001001104aa044400c40006951581868240724444a10035401280c1c044150b1b1003c00c68011394042c2040c2525413610204900211a6425102c1e1489007000e90b0001d6070822000e0014507003035101440686c02090b00280a404a54903410294400d480c2a50382481401d010301000c4802d008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 450442212 1250 450440962 450441023
    0xb03160905100e060d030e1e09060a03050d200a06020315040501180f0204090e060907080f0a02011b06060f030c230f0333060402070203032203060603 66
    0x44410711403420f29a00c03042d10300601241d204810380d41511080c103100340101141e04400400320420b1141c1c0e00c2e000b180510400d12140d000d90100310020b203542c035000000401712500900600900c50903031101321814044208a00c050004602e81c805440c5d00c01c0058859403032240b00c0040e501c3c1007000518002000b00d0742018400d0f81088010f11a500d02d00e1002d035080118000301007907500c882c04a0348064011a08110307416031901c610b202c2900c0d0000b0314240149031640036202216281d29130140c4408220140d024181e22542c07095005500c40e680182c559101e0480000b65a02d130b81e901c40003911102e0f8003c1c13620650ba40024820320551200c0003005001c00ca55020342d88904160f203020034512101325510031401d54411401945044c0300581e002d40210140d200f03601050f02440e032030114401c0210749001501000200c00381001d00c225520250010019030416000340070503c040e03090003100c0f8101003030034a00000050114000e040c0614072a106480d441c3c1c00070030300020892038004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 450443462 1250 450442212 450442231
    0xf020727060b0c0d080c0702030d030515010c02030607050d09061b020f0c010f0809190302010e01060e1504090c0801321b030702250503010e0706021c030b03160905 72
    0x5003070482600180d80b168650701380c100008a0355034608600340030300805401079098081d400d2840d00e5207030f056000620803540128882c0019940e0801110a2445030f4002500f41c5c1c001c0d0003140d05c40740104080c08080d06005408a40d5501c59691901030320083c0d0182820f00d19070340c0d0003654007a0180410a0b02907203203001040c4507500c41c40000d00c0f00040200032420f2107010400308502800030f100c040321007201807103903e43c030400c1480d000380203110302c0c0c840c18565481c2910204a03502c2507800180141c0d1900d030100380c40e000c501c0c1080002c10303111900720344980b01e1a2000548500a000e0380030328104200310150081d03106203441c107420600826241d1120a19810809000350420300d40c100007422503107641d1243e5800034240d00d803400e1400801c3c414000000440040075441a911081d81d1703055000b4080100ca0b8070195917a8800c034082e082c0135800034000c80d8410159002c420034030341880c1c075001c0740c1031b180c0740007090801078694080c2540003132038a002d00160001d07000d041c0e08200c452 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 450444712 1250 450443462 450443467
    0x9241507140c150c122503170a14041104090b010e0703050a0506130c050f180a0b040305062202120a030e0109050f04050405070504110318010c0f0f020727060b 70
    0x3800103540b140040100440c482a0124075803412440081155001e41b10f0134007414055559401d01600501e15407100a884004d168002070079a01180140c21185140000782910380d102d541d151090b40d000b010945811079555254070010503c021904d41c024910312980310f0341820306e180010143c40c8028105403200d07080c4018803081c0d07120304c90410b2004035202000280380b942c5800482d02441014a2403200ca82d0204080700140d00e0031565032000740b07040703840c60641e6a40320300d45a220b0140c0d100140a039042071002411207280e9440c5450006040044001c01d500e45030300103151001099410140c6512002880c010160000f0ba076096170034090900088462600740080c42c0750009a40307450056845102090801404008500280200a1052205410050811130944c00c101d51440b80d80cbc694840360030900e0418811904d07020201e503520400c14a00e04000e0700c2880c07013001440114841d0101c001125200700c601248504a6800b6024011075080700d07020035140c203038016940d0040304 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 450445962 1250 450444712 450444727
    0x3050d0507120806011101020a090602010605030610120501020c03040b0a110a1205070816060c08070305010609050f1309050c1e09180a0f1109241507140c15 69
    0x2d040031401c00c400c91900340e00c0d81c2c0e18000101c9084682c07400c800c0b06c960010440b0606a0b42010311841903d1455008100f40769442080550750101600c11410f904141c80c1c0078040c0c0c840000329581058040c8002501c2c2c4006506098655881a4400408843c000c5000a03e0652105ea807110344481ca8001b840320103d1a105d004003000c0700707000e0b0b00a10070001413000c01c01c00c10806403591803080f0032004d05590203904000c4054401a41d08900088003100000d101600070b22485040c3c40075545c40700c030403a04001c144444a1014042c1e1070380b1502d0005400f011403030718000c1100062103031015010150036002803000740000000e00326000201600c1c3d800448c0c030340948c02948103004035416411190464051402d10101840180410401e40914824441c0450b000805402d05481010b1240d0700c40ea10100408101902c0c4403100401c1240d1050a14000490000b800c5d00040401d18000181d0795a049000800315101d5240c1c0005011510518004e01c80d03008445440307681502c2c1000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 450447212 1250 450445962 450445973
    0x706050a0b03011a040e01060e100305011410060323040303090510060b0702060a0c050a0f0309060503010b19050f16060605030105040203150405030f1b010b0402190c0212031303050d0507 82
    0x729000b851701484e03498000c1c940c015801d40004005007425600c100050800100c9209070110901082d80c1940c01c184034540085c5c550100d03248140030404a4084060134000c088010701031003000a000400001d28510552040000300c078040e40c426100021800850321b41a820941c1044400d03a80c9844c25508120f1114004100e03000c803681155420b65401d18424107a40c01ca480382801350503403041c0d070544400c1203001e25404559600a8940c481c90f04e641e11030413901d921003401003482e0400144403528440c50500c0f0f0034012941d10b800c200c1d09201c0c10b0401e480007500034400e05405d0b00c11070b8080005105191050101030402070703000344160300c1d003500800c5d5285800501c03081042c6000c80040d0620206105450a1b01c200b101055580c1d10410103e040106c410341e0840995441c00e00ca040307007441d085c400c42c0c4170960001c4642852007840c1c0025100d0315015502a604084032540d81c0403684000d000818245030100c00d02c0b000385086013400c40c54004501c2086041c040c0c1001207071701040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 450448462 1250 450447212 450447251
    0x405010501050d1d151f1a181e01090b030c030f1302150c0f0706141e1207180f18090b07020616020102030c09120307080706050a0b0301 60
    0xf00002c40d00090403000d8040740121006085803d002d4035290000b02c1c01d140e0200d0303010300f1012034203800e21110500c0d41c1d10744446501c58443e185190303581c8100da900355076000d010001d8a003030070105102a0407000c5403000c0c4014034803146900300082c90318603540c0c1014003000039010419425065180ca00d114680b9840040c1c0501030403114180045c41c040c15004a84c443c056001e402044030154140124010350040320125045018031701c07021001010002c2c050080390656540c42015070300000c01d424080d8030005404d44d00c075001044200f480c0410000400010040c400070b280c01d890580401070a03844d22032003140e41c1450003c000c005030240c0382b4081090358144080388030300c8000d0160b244020411900700400741101d440400c1205034020404074801c9444480c0802c03401d05501c4124203e200031114046281f4090103d82d1b41c0d8100b513041204600c994004503481c2c10030648811380300e6007056000f20381854030f60b03040111246840c0038107409440d06034000d00491034040c8174119481c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 450449712 1250 450448462 450448477
    0x31b0b0921030d0207030302070c060c0b150103090203070b0406111204030213180b0708092b05090a081b060f0a0c0c05040c05030f090307020a0e0912040b090f040501050105 76
    0x112008980700c01060a00440f19800c0802c1802c559405440c07401038069041000c0980300b8001903100044e00341d00507405404095806800301049584050480400041d0000c0d031604142d50740700c4034001030700e041203e00040d040854182d5100e43c079080c0020414200a04010703000c0e0011080030801c54440000d0b501174960481710b41d00b80d0749040310840001d24001308a241920038507030000041c028552101801641c20383e40d2400b40b030762070780040303070781c1d00c014600344050440d0340c5034500e00d0454088440501c0c9036036460842e2030b01321110005280091a600a20700c83e070000d1244010903d180290243e1112050310a241000c1031858014120f028642406e82031002d1085a81c0030410542c004c0707000b138030b0000c2c41041695040540107049130001c641090314820144080b0380015400415122240d500070207040d962401d000c00c441c038082010f420444103204103a1029280c00c002c20281000e03045401483d603d500b0300c50300700685110609045c90003503162400501886e6445001c86549 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 450450962 1250 450449712 450449749
    0x25110109081c022a130c050d0f0e030c0f06060f061206010c05030a11061e040f03030e01020711100f0f110703020901030c0612020a2003090901031b0b09 67
    0x200120307200f80c0c104001010a4501c0080711191404100e0b1148a84144418255a180042c2002d90220070448449890340d101240081c030050340440c19030741144012403c000004240ea808600100b4030b143c01c03640040c4807075001000311642074076040290303940c0884120b5070112540b1071480400c0051007400002042c0b240c200000036a164003941003441c2080d40581220768540c40b202d00181300340a000a080440d001d180c0105031800025180b506a0f8400c48010a215844503a20340f0355502e40850304501303042c1c4503a01608456020320182245500490058104411500411028600014920301803040301002210380641c014108a048182400c1414010004c0d50005d8a08070aa6000035801842c2200200c100100803190744101c1d03806486185001d8141401141640220365252000816100003d00d0440c40d0301c0c3c480b58010008015646000751240204401034404d030001e0300c0c140320f0303944901880d0894824050082090084150515102100061029406c554020380 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 450452212 1250 450450962 450451003
    0x31203060b032706012c0618091203090705270a11041e05090106020304030b04080d270b0606070302250807060801060e010807080a0906022511010908 66
    0x2940050b0419104001e0b10f54402c8401e0703580d6803400e000780a090302220944a4140d034842c02120110009041c0c01104001d1107554881c0c01900606000304004190128520454050300c001070710f41001913018030700d600c000c2c101c0a41020144444030080b2204052000100c4c2004c00103100e08c0700d44150000c08000000c189031000413030f4060a0f008940040301d800d00301c201410b0031f400c1d40441c040c0440d281989c0b00030b03151780e8516090303845c0c0c092880040e01c603141c0307040020b000030601c10007494481002900041e812004a8020f5418000b8840c1441c022401c0c140800030300400e21944c90340003030300f00c074881d25000c0e613550001e490700f60000c201c0c0324051a4000b10308191800135107510151814104945e941c41ea50b201c0200851000e00c10315020a07501010840d09500c01c85035036129600d00e885e0840c650719100c01c1100100001242520031076400d000b111200c0c0c0300c4408942000f034940142d8884a120b6060080d407030b401e504007075814000740c2d050800c200c500210710507801c031004080030f00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 450453462 1250 450452212 450452251
    0x510051602040b060a0306030c0f080d0f050d060306090303050117070e0603010e06092820040e0316020f09010303020a021c050601061106070306183201031203060b03 73
    0x10b0180043d0502c0a5210030085500c00c0312980c1a88843c04490050724030302070303403940c80c0045003020506025801ea550408200407034518081c5082c0e0300040c003d4540507180501100080048900c039420440d03203203860750181c80905034103009203805000f11504485825030500f260a0f42c918245c07013156400d20003000007030429602075111610264a5100340c8400e8a081843c2c1c1c1c4e00c0320030ba03244da011103d005141000c2060429521402071a074440030741140f4251032291448408580345030294080d88130400c4006003c024000f4020b0850040640426200e80344100038509070f40f0250940078903000801000801e900040c09029a5015640300c241400d400d003989001d81801c41d00a413192040b0700000403a15400500000d00c80e0310780b415644280c46108080301511024491101d10b59955802e60600051715445100c149c1c3c1c614001c0010095074110280c0480c0180c0000c25011810000400511500d021209500040c031303d401c200c55401c000b24020a800007030454107104030f8018200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 450454712 1250 450453462 450453469
    0x30309040c020a060515010f050f0a0809030c01061503061a040b070305210f0a0b1f0909050c1b06100b180418061a010903120207050904060b03070510051602 69
    0x241072054114130103012514000290b04424144a44000d0000b02d6074029680f4030b620860940354440c60101c030b0381c3c7c6421040042210550300240908605000800c02c1d400c60b2402441650000e0a81e800204070300344a00700701600300c0b03006900100008074100303600390300c04907803104070340569001c11b40c42030319061789050840b654024080505001c144581c00c1480f442c68883c0301d140f08050700700d020380a40c1c0d25010b0b0403040c3d9440611554100e800002c814881c1c18401084040030303c2645494144d00c0ea64014079020340e0b10a07034102960341400161840e244190303901d150082d024640c010411804e00e441c9410030151540304102581002060032182a0540705001c11440c400030702c207018903503e400480d4681e800d2080100c899519000c5000380d0100364442c10f00c076112058584003240c07072940e1a00b81e001d000c42410203085021f1880040741c295070f008940c44c0a5030003030100064a20a0202b4146449890b80119104800c44804116000c0e0b01c201241e0745a62140410400a075036403020 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 450455962 1250 450454712 450454723
    0xf1806030c080730020f061306030915050915060a0b04060225050a090203101d09251e0302030303070c0c0f0602060606072d05010b0f030309040c02 65
    0x700341c140c1c208400500c0b59000180f001c103a4040c40001610f42142d06410360000e10b02c1e0f11318410111091a52401502c0c101818601c61400500203c0c40c00200c2100c140e0000c02a42101c0b0209070780b4085441800400c103460504407009103410455810035051203030b44d07441f044c2e5041c15212019000a03546896410058004084c0800706948075a2100030294a5814001e09841c02c0d0b03000d026440000c00c407030480d0030119040a0154015241080303003600180d480101140c020105810b80000c2510030040ca00c444000081e200c24902e0900403462400d00b0741d00303030316803c40c0d81c8459444420030b04032100b0351080f02d03020002a8080c081e0040c07900415034055102070343c1400040701b08030071190030290f1440101c0c481c070364110700652500101141c04903240283c4005910050008019042c07480c01410000d01030580851f05100300d07100c1a1600d0008660307078100d140041c2020040013404d01030510100d4080710032818039110303040801e1792801622942c42c070031525854201900c0307000307100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 450457212 1250 450455962 450455969
    0xc060313050c0a03060501090516090501051b0601030803041e02010e060306041d06010602070803041d06130f0209010909050f0a201908090303150d0c231203040f1806 73
    0x40400c2c0c3c03030343c90800e0b00003003401348651120030341001c00050703540c010b45400303500f10032003a11000c003a6402d0000448a0f5004101e0080320030f0200030205224032400c1085034025403041e50750a54030300c6c0c1485c04010383c0a84100342d44080034079644010050380c010039001c2d10a0340c283d80c1541c40755030300b42c006005000c42040c64040d00c08051010b032000b08010520605940c26a001c9450095482486558900c100d10030140c120010f1680c40e200a5003083e542d40d00700900821130a00314105131250b0044496040410543d240d00050150301941c20482c03030401009041e60070403191501040b04e20100300c0042400c203020b55030360110f00981400b603152402495080707100d180c862600e441e051300e034180e400038100040f40c041000100c00b44000012284174250060340982c2c000c400304140071640810f0341049440121000e40810180d4000291000341d450340c8404c0a0301c4038000c401d11480d400d00d491088243e80040009210156020320740504680098400c200d600c0c0c0c10440000091030f40c1d42 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 450458462 1250 450457212 450457219
    0x901120903020703051221070302040b0408030913060602100b13061815080a060207050a1515080105071b2a1a0910050a0e0402040b13080c060313050c 66
    0x458080c590b00042d282d040c1c0f449041181e00015103184441c0c8103020704680c000101d103280c4550b0343e007001701d085801e42140380b03418050f041c151107481121840c2c0040d084003400c0d51011400032038500d018000c420402c0d502c28400c10030f42c1d00303010000791200d966420f00740e03510b51600c0515980ea01c503e2150304205220490421015172105c0c52907440c030034403607254290300e170406d4000130400140950540460b40083d0080c03000341c1e09a0b5a800180d0011201a14640201d4090202041c1c00400d0446c648581240010329100d480455030b00d501050b03000171031180c0c98181040000c1d070300101c19800c0e03001c030400c00050440070b502d0071410b410741030a0b165280c0c141c03a150070389294070303020102c005489540c90500c032025841d80b1034100c1ca01075100c00300d6100c00820916034403a40940b00030240451140b40071600c0d1107461f0007150981e0701c15030208801c031100081b120108803021881c04050140c1c0f0000c4d0052450140020720107010241a640010f0720041c035046c00c01c0000c00c482c01e404207014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 450459712 1250 450458462 450458471
    0x405070903060f0606210f050c0c010e0a0507090f0207060e0109031704080409090618050f1204050603041b0e0403080105121504030f0e0d080306031608030906090112 73
    0x50500900440040c8411100c2d02d042c0000c10610030a41e0141c1410703500c0a581c0d444e80140d03030507102d29a00180103c401006a03a41c0080a182045801068815a2a4440165180f1004180c03900b1910106612101c0d900480b843d4070002e500451001e0071035008000101d4400c000030b060340000d1240309401040c0760b24124080d0802003043d00b054210600948840704481c02d081c48029481104490080154004000c01c0c04100c055502220803140503140000e01014030034112101840c0c00705042c0c4140e0b0110b49041c0002608006005481e64400001410245400c020070380e58000940010110b40d036100c01d0f000005c500e40c0c2d41c1e5000b017103140c06032081c0b070520b818003600d00a001c3c0145030161407000b1b448105038a0000d21340341c4882d004d5080700d0b4207544131340381207904050401100c1c042001040b511550b42d40e0748004190854052010f4a6407401d080041510f8120148442c00704070466a0042040030300120549000010540b00682c0d1128142c0c012107180c00800068121903150 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 450460962 1250 450459712 450459721
    0x1e06090a021b010c260103030323070215070f020c0f030a0507030303060f050a03050a02010c170f180a051c05030f0d2f09041107080c10060603060e0609060f0405 71
    0x540150b00316940301d03241c2d88215045d0380302840c856510303040a1104402140010000244283e104e00725a010003c4030f42c006404803244151918001d03203d000040e40080103015500007102c1c1361030780108035030418827a082040140a9111141060341074400d11181d44040170070748080c0184112658003c0660780e001c0d03200d181c09401044a03014850000c04090000b01d0113083c9101003a0030350b600203004160b403284a0b40111070f00551507104030f507c56110b0307100d4140e4000c0c0d480a440c074950491646601c81002514615103900310400c0203120f2400139108006544500d103070001c0808203001d110403882c0741d90400074514410004148000040010919100314281c2d1000c801c101c41c0d04070034404107054501e40c068030907011a84591469042026514030310f01a40f08000b800d211503402c6003000e480d52a0604550091051001690400380d052207141b85144254409800c10781000c101d402d0070000d51100201005000c0e070700070000c0c0c2c0302240c071607550204110341d002c1d8000e00502c032501c1c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 450462212 1250 450460962 450461017
    0x20c1c060e031306090513020318061303030e06040b010611150c0405120703020609100909090f0b09060f190f06090f060b04030206030601030504081c050f1e06090a02 73
    0x805048490004000e03800495180d04c641c17031000403501c0061008400d4483c10303001754002d41c80076012030070075004510b010190010a12401e803086080e058001c4003913019042c080c3c07d032080e4142086e826080340701000005201505442c0c103594503450039035503290a480b011443e02c0326020108220640110400ca0031490b40030060042c0c40d42501d540164181412100e0b6503040c070341c040254003050a114516080c180816441c6a403101f614140d01e00580d9003491404403050b814040d00c05000d10401c034010b10500f454180c1c2c108074010f0040140345030800c02404112030141c01452040b00c50044034401d207242d60440840c95882c1801001415542e1010a0007000220321007000182482d10015800c4030f0402914222500609150b00c0c560310039004500408004004840300030b000d020303403071a016003902c02440140c040000014035080106044507501001040c82d6003890030b0720059240c151450408135042001594000600d841c3e5150320300181c003500040220b10050341d42000c0041e02c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 450463462 1250 450462212 450462217
    0x60504271b0b090a0801051014010e0d0f050105060a080a080711100f02060601050c070e06010201110309010501030510051501210903050306090105010c020603040318030b25030507020c1c060e03 85
    0x100100d804041c0a0b51302d85c291801c4e05c2d000c0b83d03580342c0c8001c08041046500305c000080018260140340044040c40180700056803104c100e00181c07030f0b000340040e42204005007441565009181215904d544d1468090790310b540e051440e40081400b007021800d141040080d00540d007080a004254808064420b5001002c030070808000070010700c1104007160055001e08101c0351080d643c032024124560414202d00d100c00c8000d000c5a04540d03844205030880c500c050041c50040c0c00c04400410f00d0751660038060300c0c240c03200250011036803524003482220140c40a40781e05012003801c00d800c5d100d21103291694445c1c030581e2413851180c2011007400c10144c0c05802584500e40444401100740d0725480111080515001c000790860703410008900400d005000c2802d40801900341e10311590b40b2070340c0d502c400c1441a00d685000c03807900c0412450b844410004000c009081d4501000b9501e00031a0095440f01b04982540c010001043e02c1d80311230320f038a034585503000d420400910135a9001e0403a0359899 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 450464712 1250 450463462 450463477
    0x306050c090306010e0c0403060203090f01060609090b040501051c170a0c022806050f0c030406090e24060d23071b1203020c0309040608060703060504271b0b 69
    0x2d004400c00172408008960f12140900c9086c0900da0070b0904580c0c58400079030020b0140d440a2144054a0318004024020240a00100d0b42ca04491624014050003907031420050207200d1410000140216118100c0141d000e501e41d01161301c3d0109903003040086450829145401d03100c0029030342c803000790441d020300c441d540302382c80e40d900581803413104c020000002c005044c0c202b50500d0003001a0351081c1e01404d640c00980c1d103e5403070101810403241c5545d1080e80200701141748450308204481d84d10000e541e22880d600380080f014082d40303549641510080c41f85610031040411071213540ca10a5000110399000040c40070703112500105042d90103401104d80c680000c2c0c19490800002100304106400aa0304c90f08600749400881800c1d00650002c1011160301d100a100c4402c00f5681d5014400003082810050700e098200842c00406440c41c5410441c0603504040c1d040c86e0303030012500c2d0360440200b0b00324a1412110741e0f15000d40403944e014010b0480d0200d001c40418103502440080101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 450465962 1250 450464712 450464719
    0xd09050a03050c0d0527031608011401051c0215040b03010b040311030a08030105010309080f1201090501170a020d020607051b19270f0f09060c030506060d0e070306050c09 75
    0x40d00d02c080d80032541c5108583c6c40a000035208101540d48503400c40c10b0155214005050b2007000c0940130142142d200070b640840844d0b0345580134280d410101d4000c01d80580000c1e2003000c3d28041060703a8141171080301c03000900442c403608070800c40d00141c10944002c0d258500b130340380c0c2d20f5969a45017141600140802e4800548070005901180f43c0020020b075029880092641140c0c686401900240842082910b1248040100c906450304900c014800c001c1c4881403143ca65040c001c01e002101ca0503080452246d1008440da0b002070340001e0450401a4125045000c54010b440407441c0790241c1c000041240c8140f01e00306030b41c0d20079620200703062442601e000303160740101d0141c658400d002d40b044407103d0b80801c0c6100c0755003074002e03401c9540c28256040070552064414800702290048000c00b4078881c0e80744034040c10020140243c40030610305140c14803950a007400010900e2140d0742000282a0f621307010001482d03800c1c46650010b50704a10300b0000c520304400002d070b07aa405400c1e110310 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 450467212 1250 450465962 450465973
    0x3121116031a0603010519021305060f070302010e3d09050d030b0402030c07142a0306060a0803030609131205070201080604060303230c0f030c070e16050d09050a03050c 74
    0x6035404d05200e060b20034880e051040650030365204150009511412032201b02c110100d00100c0c1603200c0000602c1c0d00070700188540d5a880d99030a00030b0840340070300700c07858454101b0304550018450041d000d40240c001c80759030792110141038044858035a82440d4509000d8103240c61b0100740800495010003000141d1020b2103418440c81c1008205e102c1103500d040300e03040038802000851954400040b01840300000c03611005040c03d0340c034500c004442c6408a03112503840c2403c18509050100d035400540c2504c0c180324450400c8001c644a0100600c4076010700356040000d4400c0d80130343c50a60440e6081414a62018041d1400400c0c5601c5103e0030307404501c002c00401c9981c24a841034100b100d0b05659880c01500318036203401e04006100500010454080c0802e044091091082c061184108801140c2c0d40b160810681e00300384045d80948842c851700740400c000c107612020450006115440c00d01e80d07510b4034600e001c4c014116000050b2041c400c00028404054000004010410340354040b00c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 450468462 1250 450467212 450467221
    0xd1d0d0908030703020a0b061c1101230301050118030b1509070e0d11040209032b1716030618050601180812070c05090a090b010f03121116031a 63
    0x790ba03481030910040044e03210108841c00f1440301c8031f2003504008003c00d0918810319400b610b000c0150b15907020b5610707040314064103039691703008911656000758401480c405100c0648600030a40814424141070143c828501000005100c2021002d194403007210411403d02e6510316148460200841c1c1c040c400c86404502811b000c0c250b9410340c0366000b440c08052205564a80103c1100c224a680d0400c0d02404a400c5035981408140740c40c0c8001030030b12580c105400c0d0301620010002602d03406001c0c1109008019080319600e81c1e5009070003c40c2c801d960b0807903400c200e00921040d8001c0d841c90105880b1101d0003185a042580560b200b640c94094500c80519442c069409902c83d400c0d8a60258004007c06034111025001090280b01000c051603590350210392034080c00c0341c00210b620f68801041003003003843c580d5640500b100c09080c000740c1e41959241c0c03000101c040c08170b00500020400c5071070b524a0801c1ba5002c0b0344280d0b00c0c1064003d03524074003415440e03a034100040c000d80480c00042c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 450469712 1250 450468462 450468479
    0xf13051204050901140603162c04060b0c030a050702010c0206071a18100b040603050105010b130b09090a020c010b0a1502100b010503070f090306050f270d050d1d0d09 73
    0x2c0105c00c0103012a02c0c5440e82d08003e10028107118800d014400c400e02210031030340d07c1822613404464071a03170b1440b04d6042c483c2000111041c0d504000c0f20f44000b841741c1d02c09aa0000144d407805496428640d030744150600040c0c070005c61519009501240004000d400c2004145180e03000d1400c20700a82541d49075011801100d004c2100c8c1d4251517881584040c1c60511544c104003150140600006800c54407a280d241c00d44500b40c02820b4541c00c0091944001481c0d4000381001f00700c08032140d400e2200100c001070303900a000d000400303d10340200c2c12141d1442c0c2940201011200249629801d543d16014100c42c2c0f0780707001c0d0000140c050020081c00601c0a40100c10440030165174840c5940e40c0d504060700c802071045400c204100c14010003000050161150b2130245015285152041c0340c52646002c0c0001d001c03081d01d048445104490241000004640700f612105081594035128a80c0e5503500400100034400e0390028110344002c400500444d4001004505035202000f150300d40d042d4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 450470962 1250 450469712 450469739
    0x30b042d0b0f070806040b06070206030103141606050f25060608010b06030907050607050708060c030105041b0c06020c0a17090a0f0303090504050703020408030d2405090f13051204050901 82
    0xc903c08a03030000005852860581d00507829582c00520035802c01d65980c0100e000d40d04260400c0b81c3e649002e00020b0f5042008000c101d000c0300743e41c041c206040d030414000412a00642e80c0d031260303901001c00c103207451210240c524034100e5404400c2c8050340351282040c102400a5105041c0c09520f00648a41c0504003001220f1083e07500ea00100300c200e24140c240b000d030341d1201100380c4140c06204030200302c03082c00348882805100d00302e00c21074983d4102400c0004407404559840c22054600d0003041e4050f0b0481820220184c01690040c3c948030303194a12400d041c580840180440408070000038480e020001401241d0f0059460f080d40584071649454448614000a004149101d500f0040d51516800441c3d10800c0c030300d009403d081d074881c1004e1842d04400e543c100d0180c0c031585041081001c4060900c00c1c052000781c0b903840325160601048900c0740c050800f00503142c00100241c01e01e00030703003181030900b40d0100880c2e104060300d10003002c154101d409264411014070740009014444181d8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 450472212 1250 450470962 450470971
    0x3050a290a05040207170a02120a0309050706171501030f14010905130f1514072006010b0a1202070507030308040b06010c020f01030b0d0b010603090312090804030b042d0b0f 76
    0x1626091039038491082c86c869008072401074110b02c20502c0300f120300441e40d03002e04440c0403140c030040b07218a250700e80182400c00940100d410004104002030f060740030181075503081488181c1c1a0720301c14441c001280505290000780f401c160608080c41060b0300240551030407207100c0c0300104400d40b49c050502084017000300018207000300e00004a00419610350070051a12016007000031040b05050b00c0442142007100c0c010045081590045c241c18400210f940303545007844068003803981090380c03403a480d000e40822481040510407c02440c500182e04031901d481d040b030112000e40341c4e2440d00808102c011681210354125505c0422565400f0b5124104010b40c0182004400090400110020b100707001d441c41d4850a181914000b107002e00d0142c6010700301c0c0c0d54011645e1105424050450b4010070300c1114a203103010740722000b1500a02c252000d40f40c0c0440313800d0058440c3d090403c06083ca041881c00050107115007001d400415142c41c0502910a107021015565220703501a01f0106c200d6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 450473462 1250 450472212 450472223
    0x102030415050c1b09180715050c01060b031605071e051009110301200f030720031903090201141605030c070503070e1603050a290a05040207 62
    0x4414000e001001441d11502403561070014100f0800500b441c0c0703000e01d000214402500c8502095200c1e0500361030003a44401401d00340000d0600c10540aa40c0e4021480384120040d101499240d07101d200e1811642107400e280002d200306619030301040780aa0090b07a4180138018101b800c600817a000d841903881c6c0c05d81104440104001ba00c0b8090000d0100f400d040340e81c2d00450300344600c80d0780070744a5001c00c10b018060742803c0e24030540c18107003129501500c188004d01090100004450034408440d1041d5420001c1910703a03c40030700540341c1603207600011414500080c0e52020780b44001025181c640341c0030140c1e20386200d00610036811106440300190000702e01403c1c0024000680c4010107040b1003904900c880c9204585880382160001199400250423080742000b20b0300d03041190700080c1918240c44211402c000340e401f000211100b0259040c103498800142040241da8841c02580010b40b01e0080c0c280302c0110302c400c0008600e1080d5100d008041c80108880c00c0610070f075405c039036110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 450474712 1250 450473462 450473467
    0xb010f0f051912023402130c0513030b040201170112170f0414030d020d02060a05040507050a03060903201009020a0b131802091f0207090c0914030c010203 68
    0x10a204814842c4101401e01400081202007142e00103030301c02842801400305118964500c0c6a502c034120646840300307640038451044071040540d86408040c119108102400110b074000a20706603014041d24640c0701e00354284120001c20f005000b1221413080b4130076601e80041c01b1159071034900c0c02c1401c2c00741409003400d0010380e40014880311404070351305000100b80c90800b080c00d03904002c164015040f14014031107807907480c1e03901d04013046491400625800038003010b0300400700007507413082d00900065a4036258400b050a110051201c0d030003074000542107801c900d8172820020040c01141d030085000961000c41c140e01e042000c07840d046100042006003005c034900c1c1040e8400f819a03498240c2c2c0c07050740c0c040001046a025001032803a699000702c0c0020680c0345c034500e080303404001c01c075141090303004200441080c0d44850f4111050310303114903071071440e0100c4882249010143c0d04885941031418074403072200c0740c000e640a022104441d0113403001400a10903d900d90520407000c42c050b9005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 450475962 1250 450474712 450474727
    0x3030f02150705030a090b0c04090b0405041214040e0c070b06030a05190c0825090603110402030903070b0403120c090b040b09010c2103060b03091011090d060b010f0f05 74
    0x3c50007150000f004c3d19012810007440d4441c501500c00c203503000c180700100081d04000020312409009010b4400322010402c07498540c48041140505a075003104200302080e204002008580982d4080c01000601140a180180b01210300358040401a80c0360700541000421070b180004203816543e074010081e211288203140ca014400012000464110050030000300c0c00031402c01c0172905007406008180810340d129188114445420b41200140a040680900210f200d03401d000d80115000d03a00142d03603135140e071852400c6000341d2b04010040b4280d08140b0050645c842c1d10161580c210000400c070710b0104c400140d0b200d801c00d1090f80c039140c00c103020410078811042d000e071a5070081030400c501030034000d07601c0c138203401124010b807407041e03100304000d02040d907042c40350744050240b500419185080c5120899640d040904d40100c0c2e180c0c45400784046811018180c80b40300401905c1c9403050b00940c078018000e0802c4111003400070b40d2032452102060b115082001c0c002c4400d4a450345044038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 450477212 1250 450475962 450475967
    0xb040608031c0209040f091218080601060c1e200a06080a021e12010815150d020406180207020f0f2b0b04061e0605010f0302130b0a02060103030f021507 67
    0x2010302d08507445503a514081c206d82039680500e4035203510594070055032588103207002d010380407103410041048a20700000d02c002c1000141c101d065407a2800e12124035905840d21249901c00c1081d42070042c4c44641d0400c1c20801e180f87c5210a0a00545081e00d807110b001091041c507454034415800081c1c0305c03001003101c042d0b550340100005079824140300814000714015402135407002801c0004603088000400044805205d41e600342e442c1c41d118100c103800c003a030402100b1040101982c0c17003180e0b040050011542e44da401900100b080d04980c1c0d10704a40c0c005150300940003100242d000d542e500809a40a20300903403034100a210042010303402c900c05000d81110b031540ba03601c81114549911f03181011035405095184124860300000c0384040800040061120b1403059111000341404800d1086a800c9000e01e038003c002440d005031501800c01031101107125960040d1050000003ca0942c560303804900241a81d0180c2c941e038410b002c0984040769616600d111500120a47c4c4000ca4580ca2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 450478462 1250 450477212 450477217
    0x507060504080c010908130501080403051902010f0f06050a0506090d20041d2b0f020c190303090b040e0c0c150f0106121103060603040c0b03010602010b040608031c02 73
    0x6018200c26401c0c00da42904040c03c4a01c02503003031b80c0740c10340482c0442161000b81c9990380503150a203008101410320359000f42c920700807403143d5a1420ba0851403050114400d502c0050303054246803040c40504400c03c90f4000801071401041c0c051706103038070003107291300b8664101e9104040144c244a031800c826140c0507454000482504d0a100110302d81c800305603628000d03480c40080380c0202000e0780359020b01c001d2818400e8107c03d114048440c4d5204180d2181d0b040c010000380c41401c240d0803142049400300e060182c0852420b62044e08030510746058032482000c601580c0c400c0d250102c40e1616025100d6841c0074a1040041c2c0c00b403480005014009080050311040d00b54104581117140c1907070302469108822075250400e4110310340100940d035403000e0300f2020504009401c00c1500383d0030341111605e100c000c2080780540e0001010900300400380b48194014041c204c4459207030b585500c4000e0203042c554030643c4c440c60030079102040f03084021048450f000512416004400c911450680294 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 450479712 1250 450478462 450478471
    0x7051b13060b0d0915090305040f0527060409080708191103070816060f05250905041805060702030a0305060f0d02040c0504120302030d0c1806120908120406060b030705070605 77
    0xc00b100505c51005242030700414146900c6500c50175103960600300c9104001e40c007a031002d8850040000b20310040d0304031490b040d001c001d00101041d6655078000c0440c01903c00a44002c22840002075400d041c810881c0c05844200c1c8490301070a80326010403012900600007001b0a8080d420401013880020100e00c010003841034460504004102c0f640c0f9980200d4250b2411082101d03112402c0048001504d03d40009000703840600104210030780d10300900c1c410107809214015a50782e016011001c05900514020329400700455119142800c0000c1d100d4204680240201b030800010918518012203071340d1554001801e200e0505150f60204805844c61459220500c40c0c00c00021891000c02c90200c08886c0c001d03001113035110406140b940440e03040c00c0783d00041000021401225080c9103491104840c100e140600b28850409a0603008200f9520014000100042e82e50207064410003414840c0d8091401002101d41e103800554251200b1200c0d0710000e4010489000000c226601c82c9400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 450480962 1250 450479712 450479723
    0x3030d2301060c021504120b270703030e090106051c0f0c170109060b0a0807021212160206040c170106050a09021201140303030103080f07051b13060b0d09 68
    0x412100806112210000b80c22010024125081100a45c201001032a081c202d10500c458035252500c2d0300d000c100008210014440344115011540007c40324460102d001444c0402c8003d0724001001e2981d5200e49201c11400b10300303007018181540c60701240c030904984040d1203250ac0d000303008910552180d0280c00c104002703982c44c0e040ca48016410b21907600310124a0315016940d184110020403c044140d01825090b41800020311035914240152030405c821400c0842e090b03114002c00b40c0c00e002da07508500d0759001c00804c080141c01026140d1718012400c2e0703075074007401000040c8120780303403101110040d0802c001070000304060503441004a1110f0081c40000401548540010f44c00346d48917400024015008103103a00402200383c0c03407500402d841c421040716a1440e40100e034032400705100c0a0044071003c1a00c111442e020302c1150111a408003d0b60000804004201680900002e901d402040d07294000c0305c4c903144a10940c800ea90309040007508005411200703402400803544107c2e807 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 450482212 1250 450480962 450481001
    0x70228030c050a032606030d080c0d09080301030b0a02190e010905030106030602030a05010b1216050d0c021f02160b06150406020a1214030403030e0c0a0905090105100503030d 77
    0x800d20620400d035919119940d1404170004260f050428186503041038a210f42502d001d114459034002100d120031545814a08419036850301c0c403400d140035041d0003000d0b15082421441c02c001000d002113060702d205040e6014181c8840d25414128051903a030054003401098000c0340142c0208214107246605240c0700c42e1040d15180032a081d6007003036000b01c2d161500841031260300d107007502905002d441202c031200d080540092030b00060b42000780c8003a001d01521100350040ca803090b0200c601c2020f544106005060740e06c07030300070350f52030340d81d05034a12003038030784283c800038214a000b242c90154214507500715460303040c0c503540c62101c00680020f90181c0043e03103000e100c013103c8020f00020441d94029180120300e0342041410100c03100860030800039040d454400c0740e090503007500d410a03054640014901c0300c2c82c600c3c42c54049607003d220ba1105944070001403030481a0003180c0700720003090080c8460340b0342a5004e90021268061654180c009000d644a405603d070300400d6240e011700703001d01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 450483462 1250 450482212 450482237
    0x64a1b0903010e0f070b0a02030a05130f0305060a051005060a080c37020a0b010909060e0f030a1d0a0509090a1205030103060c0e061909080610080607022803 69
    0x2401c5591500007100c0344c0d00100d040440944044c00301200401c0100e100524080010302d009407680310b414200b805000000c103100290308554441c0c5805481842000700102d1f44078140140d03039040c201c55a03100c8a05140c0001c001e441088900c0c0101c900140509003444c4e44810141d441500040529002031410301481208100c400030342070a184030110304c2502e0b000d4050306105000b01c4840300d502075520004400c40020b400c64001c1d0304440c4c0340745c00000c0b0320703086281240c0500a0920480d80910400b448181d00000110040c13921a03c030351206c02081c0c0b01c0842e00384071032081443d01581304098080403c180d040103041241c0c004100810360342d025401d50b44551382480040700247c0003841c04001881044a01e01c207520384100103017001c074034106114002803045d00c41c40644174464042044000c0351140562415400760004c0703010b5400c140f40006540b80800c8051044440d1881808007140755a400403600d0424030901e002c0c0441c00710b1030b06011001045080c50118200410407007080e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 450484712 1250 450483462 450483469
    0x60b0a0f050706060905061302090105160206070b0403110c010e300a0501270b04140102071406040606051203120606040b1b0f0106080a0f06064a1b09 66
    0x40c002e0805c076203000035175003000c00c2071244070f207a810f049086051041107513140a80c0c000c801e44412501840c2e28401179922031020031224004d502d4010106041e1009100c2056040f2080c0d0020519071801c407030b68956224011aa070f400b151481703507040464140e0203e82a21100c1c2d604107580c4e0000700041c1074905039194545840c080e8102540d450359101c0b081c0079500c40a11001c00d55204460b0240e40d0034001d074580c0350001d100904010320080d81000079000c0b104083d0160742c0025007003240c1d180c40b990415181511040304903411100d80346044400704031450b14080c8481c58100e400029030400c0d1500340c00040c2408007900d0160301c10030900c40060290850f1000f4643c840b0340241080f04000020021441c0c54012407011400e64100340042c000006c0016510100b66082480c04800000c1410a1802410b003500099200070748501e01c0c0c1c2c081c0e501014013185041e59012280065120018040700c880c1900d987c81403404c0d001d0b000716014844c40908009621800b0f6149890000c181001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 450485962 1250 450484712 450484721
    0x150b0d060303020d08010b03070e030c100e1c0c09020a02070510320a0509180c19081501030b03100f060302190302060f131a031504060b0a0f050706 65
    0x422495511100d06004040d0b040c0a00c1c2d0b08a00542003401003541048004452400000d00e07000410402c02d02041d0282c1c0d080022407401380005e05141940f0f0366454004118030072003440140112204901036104106007141516160b80140e030601500b400e1552400196004001c14011403040715004149070b5902d01c60385007181c4a940724017440004440006008640d100402e000484540740001e134044003610843c2c40014a80c90116600e08504001808184019010036480810383e0b003008591070711040100b0101c02c00661840b4894034040c0e040700e081000302d8294004070186410201c895000390400503d81030000e00391604c128845202e2801ca0b4940d5014000e5140c5686042041d402d203001030400780c100c0d814440f10b0150131034020404500c104640e02c0001080016240c3c0705c04500c3c0300160140441002d00399600760003680c50740407a00180d806226070608fc03000c00940d0725247c41020116596074040070b05014a002c2e003541c0d0300008948001c02c2c410b0800408001600e01c0c401d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 450487212 1250 450485962 450485977
    0xc12130c15020105060a05090c0a1101020d050117060621100507020601180204230d0501021215041503082a0a0b0702031309050411030102070b0108010b010c15150b 72
    0x507540e000c0c641074002070079104003600c03450003019541d400380250789072204900d40c400e26801c0c606a8230107209008855202070205020380035407000c54203041500706a04298102d60420840641c1d1030320241d42c40d9112002603a07502d610821001081c0f03840040d140407050329000d4041074550040403201e442064032000c0f0340c810f0060300311000501c00c40484000c0003036481c0300c0c1a803c40c101400c182102d110000360000300400d004c582c0c0e81400c0580c1d41d120741000103a07885030095488003107490100e01407242c11703600580d0b0055241580c2c0701d54101031103921416003030310310020301843c91521000d0a641c070180f01100050a04030132032185504452107030141c3e102d680300400302d000c424201110b100c0340260000c070443d0401c118001048040700c0b9003000b49c0349141c50029043e200c40c60000804902d4201454155001140e19024802c0605400b41240c0c10f000081c030811031200c00441da00303251904001c0100c1142c8100c50a441400d03440b42d90460710040f41801416118a0f11380d0a0343c00610303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 450488462 1250 450487212 450487229
    0x603012709060e0703150c051605030702030f10051e0a050411120718110d020d0603060f020310090b060a1b0c0b0705070608040f02060903010f0e0309180c12130c 71
    0x501002005001403031b0309289400e02d60200310b0068161f100600310301c94410400d01002d03c00d00c0001c1030000a104031480c0a40c000d00b2201d000000102030354880305074036400e03d40703c0d01d4540041c030b03080c985035403911214055000e240d109a03a0280c4180c000c02c00603105541d0030200014808007502c840c1e0b100707400030058000030b00005107000d02d2541c400092180d449443c60a1810550703403041d043c0141c075015a040100036031038000a0651000401c03596202910181c20200309501c000038a500030340c052030081c46c00000c5103407226005015500841a029041002040884030381c03480b999000c004054203001e040b00c1e0000340c8c2c07524410300c003071a0000450280000340c420704002c41080310303c0091400381811100c5103001d48904000d00e04214002c4d000340700000d02e0041c5694203501030150180c072401d08200c601c451225155903078000100e502e0150b018400489501c0300c969030000e1044803d065000c2c40c140d85140ea8448410b070150601d41d542c4da04002c40b40024040c010614090844203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 450489712 1250 450488462 450488473
    0x60308030f040f02060c070e0a090f12021204060e030f0c0a090b0a0f060305060102210304060c020c0a320a05040209130509030304030914090f130804230603012709060e 74
    0xc08e00394100756001d000110754515010303904c0001049007014450060300005201d0000d14002c01c00d07070800090314801050751900060120310315801441658540d441a021900039943e908a11036036000e10010045d03004408034000c12000b40c4c2038020511a010107002803503510f540d07010b4010388901c0c0d1b8010402083d22407080003455681009800d4884440c9003003095a00303014080c1d16410710010b000541031945074002d01c4040c0d27008120124444c500071b03040c0f41d2456941c2c08038501584c07507041000302c0005014001801c00036040000b0608040041841c525603180c02e0402000794400d0510136040000d802c0c410400c801e091040e14410303140e00018555926061500412940980d041400f0b4482d00000035509911303442005a404000d03043c52480c261a540d0031071656541c132040040082100050126120410106903010b60b4200c0c5031034030070301c60160308200048c0024000c003010250081e404690451203d802e00310300603094100060702001c00d0f12001c00f0340e041407034502d040340d001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 450490962 1250 450489712 450489719
    0x9010f09050c0703050301060f09030f0f02030115080718110f03061003050705030a0c030e1f06050306010602120d0b04020d0506011d0a0314070521060a060308030f040f02060c07 78
    0x14001c2903801402084050700d03120080c0d801400740c1c00107015110400090301d86084c28107000e185004051a00455101c4103114240303000c0c0901d2041c020100d00950a00003c9000c220401c009042560b0708a0050b1000354188a110b040080030428545002615003181c42c01203500707480104411003001a5850f500c0c82e05000b800b94007440c0c041200201032928041001c01540807007680e4001420b202d021560540c0880d04401a0a00d0441030b0341074011451401343e460f0603405400180c1c5029038060040c02d684100300f6480301424441d00f000350300078a4212010007124801450144142c80c0c00052006007540460100e03001107034601003842d542c5060061a41e00090110b5040e01d088001c040481c080c440424482c01e10380c400108040c0303245039071000c0b242c3d05000c500d011f014045c000441c2010500714910701244012140c0605028810124448000780e000b010280c17504000c00501e50703181c4181d100c0070300e980100305880941074118407034016a140c0c0e0041c010300c62404001c02000b420b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 450492212 1250 450490962 450490979
    0xf0408030417060f04022107172a010c1b060903020108090705060f09040609021206091305070335031014030c01030c140703031b0f0e1e09010f 63
    0x50400b414050b408441004090022510195072040d8103036400c210b0318540141200f400004201c403500d49002e401c0713010582d07001070116060703500264003c483c3c1c1070050030308103240d200c1b10040074458090643e0071540d040d4040c0100065162240c0445611a440d2080c0c24071100c070a50403800000c5c0c000e540410656920105003070304651240c01070a80309141c040011194800c080b0b4000102e1030100e504012503407168810001032003410429995550084000c050041d01219072602c91121840425031000d900054005110b9001d0001d00360303170b402c503112403102e400034401030000400c0e600190312509101740b01d4802080b02000c2003a440342050f2804900b200100e0308401c490240c45401a082d590b40007414141c40c03202800d00007405900140e0840e0080c1c0300c03440c0c041c1c0142d000a048010182c1c16808031512508454604004400b8a00102c2e45420040d4401002500c0380c40092042d1400c1040c02d144510814111007070140301c90041100303d0000d0381300b42e18030881c81208000700c04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 450493462 1250 450492212 450492239
    0x30d0e0d120506010f031e050f010f0602030309060a0203220606090c02010b1e03031204050a111509040e071505040e0105040903090b071104020c0f0d1814060f04080304 74
    0x10041070203002620300352000038603c1012a90362410551034007810005411030100c101c40040c0020000e2289140a1180e14403482c0b00303202e170a60100101000060300e40c40801070324020198400901480d468102c0c80d1000794102812108103a0340c2068003191130200222100c00031741c403803040480c0380c61611042d001164880741c4c03a0019a410b0120f4603416546094100400c0726050711030b03884d81c0c024400400e01d58050707079100355062200c0360b040c002800000200c4801441c410400000e0300c00c011401d0099424200440c0c0002c0e0100f880061190720342604014002c410400c100d4081d6603640800510742d4aa00c02c184010030000101400340b4a8284402070141600791400d224107202c556005010340b910313102d0303001c41020200762201044100c10740003011100083c07096449440d5001100d80f9100350750341c414500d2060700c08010810b800392803192001c95500a8008200c0c1c0b6142807202c0070340350144120351200e8104207800c46200c0003006400036015072802151620b080c94859603002c1d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 450494712 1250 450493462 450493487
    0x3080603011b020a0201110705060f1201150c080a1125051005030f100504020706020d180507050607080f030f04170f0d0b060d0f05070e190611030d0e0d 67
    0x450315014400b1090790005645850982e080c81c100c866072409500c82410b00513503400c050344c04100061868002d42916010304001c00d00581601c035941d980300420121003030b2503403010000c92500e100c1b100c00702d0311381c00181a05200d14101030034908032140c0c8041c00c00b0300d04141d9000d4021034081c000241d00221980c840504030540707180c20031401024024001b804028401c00b8900e441c50b0010314450340b96100b400081401030000d6450300d0061804501039000710320034614283c0303420010203494940000000456030043c0242603103a06000030b001311503001c61f6084d11440010009420b902d18174000540c403e080180e02001182040e1818013104d10300c420920490000620010150320340720022070701c1c8601001000a00b084c111008510140102004c01e0700042c80d05104c4521a1810382040b03100341d841e86d841c01c0714400c0680401c40080140c10700f040304003000d9502807100382e01030901c542800030881c080341e045c403a140c112201942c2e8290301150040d004407090300c81075a0001d040c110b20 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 450495962 1250 450494712 450494741
    0x160b100e0108100e0f0d0924170a110705030a08061008060f010c02090702010e010f11251e0219081b040e0d05030412020706050d050a020f03040308060301 68
    0xd552504502d1a80c65010101030103031969a090b503035410307420803c4405410441c10068030507840716400c002e030480c0d44070304c20b078460003820701c2c41e1019005041b0001ea4403228151202505c0c0c1401280e2040d100c4001000b031f5102c1c5580e400702501d002d1141000c1c1020728414401141c0d5240201c0004180d81006400b00d4042c502010540c81040c1d080300f50564040800e9501209407180c0000403191090074190180d04400300c002800205517042d002402c0c000d038120028041101249201d0007224010010081c6071042440b40c164038403881012440b10a00c5040148840d142e03c1c0c072410803045840341001c02c006051041c500443c1481301c26000710104000303c880a80d842e10165039180d401554081c0300e95980052688980c4d03546610686103003c1400232a81504a0300d0400750566205483c04c2d500c42035040003806500b44002542d405440803030340c0d00340c100007494050502078140a86a145c1c3e9680030302500009850000203584030f54080c0c1d4480000b400c05509050031142d5003c42d917800d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 450497212 1250 450495962 450495989
    0x30f2107090b0702060909090d030510052209021008070e0a0f0603021c06260601081e070302091611010b0906100c0209040f020a09060f0b070602160b10 67
    0x9a031904000c040d000c6440c001d0074607a480b100c502c0000c0d12840751110080d40712524030244085124009902c0d500b0030001d40742002903840c1c003070024004034558070485521800110f10078101092494403c01c984a10000204c3c130385040d54001013000030061a403000144040c410080c0c032540c08510040d0100c0286c3d0020001c0c0c0c10300a6407500101d00b4022a428180c00251407003443d241082c030740c0210011080708100181d11400342802d0340c2c0140c4408405014506001d821710080410b20a041350141c1008141da00152a89c0103841003000e0469000c60055000000240e00c179403403907078865404140c1c202c7d0910a031880141c40900f00f00100d5440341e1501c3c030501031a455107070311503820500480310140e05000c422001c451031851300310029040400b0405003c100644910385410441c400c0b28140f145907180c00407402241e480b80714a035140c2d092840d04110240e504401002c500d4013955001d840e003200746010010020481e0f104039900c00ea46401c100242201c2050700014140355041740c1e1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 450498462 1250 450497212 450497221
    0x20c100903050711012705040b01080907030f050703080a0305240a030813081b0108060603040506040f0305071e0507050303041404020c03090a06020c030d080903030403080a0b03030f21 81
    0xe2060080380b400400d1615444248913682c3c0c0121050b100452000c108003200c2400f00740d080141400910521340154140380501070b441d03024002051213518850003c001c06455902c500c42560b08242c0706950502401340c0220200d0002c1c0020310709208161000300e05810028040d00320100d10f44a502d0008030100066909a51404d88190480ba04034100c6920360711410045050f040c0140e100d0301c05e612444034607420801c2c480110390a2410700340c0740c20354240e5848041c0222880101d400a056810040004000075000d0034680e41d001e000346003060811400b035075440e805401075640303020718803442a2800c1c2001010802c8074064007040d005107040c1071403d00921904950020001d10032a0041403c0060304810020b69240780c20003080080103640e260400381d2901e1120703083ca8000c0c060041e12261580c02103a4150090b04d104000714595170341c40c2c500725101c84003e0454100d20b91501c40c607010a94040002e400f02c0804498026a2584c1110200c90b29424692010340300c40038800410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 450499712 1250 450498462 450498467
    0x1306050108180d1101110c15060a0f0b0c011e1406030d120e0c060a08010e060301050f0406021315020709200405190f0303030203090d03110f0a0903080d020c100903 72
    0x4400c3c240d090810080403500341690754094961502c00e01c80c501d5021941044500d80003a454901c0580310103240f10685410041c090303400f0060286201c0300c1d90104040204139400401403000034201400040c0a0180300d10502003042d0842c0050551920344000840350f04190655540100741180141360300701031900042c081c07070b510048032048650350700006411580140007200c00d1110041040307980703c10722900541000002c0c00b86680c4203212030001040c80c10305201d80c0340981d03200309650595580b00d03941c020107580041e14207001c2a5000900007000809180100011800c680162080750b0403c0325400460700c943c100400600908480001441401d034112401d540c401d0301c1018640480d03528525203140154480118000019070001c245541075000c0c1d4001c5088038196502c000c019a412010b07140d100b101505030030410000003120305c003d0401442500410b051119520f80d40740c40752481900030608940442e500002c400c040318030240001c0c507210301e00b0381d41004113229a8500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 450500962 1250 450499712 450499723
    0x30b010f120b06040f0308032406040306020f0c0d030c2c010804020a0e0a020a030606020c0f1c020402181f051c06170c01020f0c0f0d03030209130605010818 69
    0xa64819642d600070381d507856100c0d00c040350042c2801d0844407940607941d142c6042c0039802203400890800544031040040000c420180f440b1030350090003981000c1c10350311110001e5110000e94086841d08210031064000140701e40ca0a088040c0c4000580070b82e0b030319016208032042e2102e28180b40d4100c0240018100e421040e0720b03900c40c00c0c03030072804e250303203600c0807844441258003c215a11865020421800e44540050414000d10340d01407040540d03800c4241d0b0340c0e01c0c1c54009107502000384d1400396103504004440388600080d000038005181c403180c0204040f0380c8901c0c00c4c502d01d401b5002e104002030804580803250101d05800d1b001e520800c80b85c0041c81c1c3d020300006180020014403036155007401e181c1247e409042c0603001e20305085509150903a82e07040d0060303e280035001c0c070b00540401040200e007895455401510340004a1080c20400400803018281141410340c24414021662a04a407403219000c07042c20004210f0304010000d060503030014101c580d008540c0d0540828204042a0b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 450502212 1250 450500962 450500987
    0x50d0b070201090c030c0815010305060a0c051309050a1107050307030c110406060e0411040b0901120e191a04031b1a1618031a1b040e07030b010f 64
    0x144801500c4200d801ca01410a0403000f500e500d00746240803082c4100c824840088580c91003c44400c03800020400e2002139007440090312503001800041c00300845c94004604c404006d2500d50320341000391040c48202e6101e80c01c100365147d075880400074070408912424070b5201070018958181201980c4442c0e9904c00d9810040c100030341c00d8002c000300481e1003509000044018000d01490b03407038400003001c0807080c8070070b54030803801d020848030205500c004643c195113180c443c1d00d15000c043c00055030f44210072016140000da90343c3e010a2001014018404002008080d41c1301075030060a04000f0706a008070a0f101c02d48417003081c08006904801e5003d02040380340c20003112203003d420700b9110b061102503040d040c1c188441c1000a0746001c655818880718040e00d5449099400c03204218070380115000003444034000300c4a80348440ca0003501c03035520296856960b840f10709603100d0700c02c01d0741240d031051200d0510f180c148150311b03030503000c1d200d0f45000c2071800115065130303608010042400d105 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 450503462 1250 450502212 450502223
    0x602070f1a04060f140a03090209070305060f060a09180c1e1b110306010305010e011404080406050f270109050105030f0103060507170f0403030c09080d211b09060504050d 75
    0x21303000ba0b40c16000c2e400c07401c41c03d10030700c42a44d191010380710007030042d04004004a1083d842e04000900481c00380c1b240798010301d4003900c010100440c40e0140404c1743e101062200500500300301c0014940c5c26403002d56100e407001100424012108400075046007071001440c030007900340700c80c08241c10354081140007456010b00340c443c1c1d1520b91401d150460304110710600da051301031040040180101500544c40304132000c0300811a06042481885164009880051442200b00070402c02507100d030002d0700303c10726035140083c035000c418843c40d08000f00f031445030307841c144004801040560b00001800020310003070070428558035152071074000e900340501004107003035130764000704440c68070988804903c00e50a804049143c103210481c0356056208940480000b800d0010944500d03200b0303030f0f0000486904800400441c080c4000070350304034040001c0c95401c1c645200e1018074201d02402070300940d40b10011a05403003181850000c0c0304440c113401000501404000800540e01da41d18040c06142d00007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 450504712 1250 450503462 450503477
    0x18160309080f1206150f070b04020406081b01080a0209130f110a030222051008130b0f090706020304050d15090803190501060206220f0b010602070f1a0406 68
    0x34079001d242401441015001440040703500c9450392a8402c0c45400b0b10f504480030844101522003400d81131041c040d8a00d20440140600070000d44200c14041d00540300603c0403070304c15160745000d4a820300750040021440401c42003e00f00d560403807003298018075064410b51418418002040047c1008848900701d10b40d00d50340322085c0980c0d64415031555680ca03c11680e01c04421000601a4100c40000704250300c030558480000d6940700000301c201c43c1c024011a101c0c08083c034066881c04002091410140112043c03c40054003940d5400d11424880340c4004c000e04000414a20f052002d40012096602c108001d200a44c0c5044240c244d980d4081108040c0301030000114000e03052000c0000d107040404000c0c08a0f000300c4005042014181c0c602c1084640e0780c90b14201d903101800d40b0103840000314200359000301080100412021401080f4144650380c1c255248810114243d20800058010407828010510406d40d603500421406543d8136040301076800035100b0344503031b00ca000c0a00648 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 450505962 1250 450504712 450504731
    0xa060c0501091203020a020106080115060818072309010308030a0f060902070302071503140610030b0d03030b1005070818150f0706111206150702030615181603 70
    0x2d400960314a944441041403041c4050000b80180d00300107461800355003844404590308005100e01e803005100c0015203908a841c081058a4100020740f400c40080351051400d240002c0030480340c030081c042c40040c03d408800c12810801c0606408400a1150400000400110310440103030381d0081d800300700018880c5600c20000c4028211948443d00050020481100303058002c101c0c44100c40c41c4481c80700a0f045026821002c85240800c40181d1842c2c042c08620b80c0c0c2080c1c0082d40444620341400118982e0500009000d8260024103c0c00207844030502c1507a41800300710b642c03648c1d0040c101141000e4003aa0717071030f0080c051300c9441007001c5440102d44503d6070f0b42e034904400c07a918180000356205424040c01c00103510000c01600c100741040045c0865801c40000c458285c081415603801c25182c3e402080f9106051111903032401405000140144c0c3c1c092000c54081d140e101000e00c407001c24042448550b03141988000420007041e0204180701d9401303030012454052910340000c03801d10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 450507212 1250 450505962 450505973
    0xb030c01120b0d0b25020d0210020d0f050f1b041d0702010b0603010308070318180902041e02030f010e040206071b030807050309090916140d021504170a020a060c 71
    0xca000c01428502280040c040741d240076050306020f1400d11031751a03070f07000080341042c0e0755407840b850020010380c05154500401100c6a000d000c0030244401e000c250703941580c1141080d10b009950314100100c580d800e000003071086c054040c0c0004030310f4010900740391900d11445200c0e8400d0060000820303140000400652007035000030400d440051002c2d0701c0e075031a410b191415802040040300480c001c60b0403c0b01000040c1014005c2310100722910115050780550000a4083c0b2041260072a807109564001822b0810b10381c103102000b2000181c5914109250600188040e404060b00340c11040a01000d0b0303c60000300c800d103d40201400d00881004160f40ea0b40002e5a4809048804040380c13000030400007200501010008484482840e10345108082e101c3c909140000c1c00c4040c4070a007006940000700010b010a04002c00042d610321040c0c001c6641b1071004107400c09030a00018050001425581c080641c50001100a0103090529400700d070070b0310304900455060003c40c0b04980100310 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 450508462 1250 450507212 450507229
    0x1e140d09170c0a050d030504080405010c0516120b01050a0b12130b04110118080601060e01020c03071502070f0815040807060e071d04081206030a0b010609090b030c01120b 75
    0x2280700c1807059488490964440d155030100c0740842e501d0040d010f00c1d00383c40e442400703058007440e00824182e1901303141500540d8030068201c401c803414003401044071000541d00542000070842211444c00c030f40698070b00950084c03016081544160b410f10000c0c0700100c011010342d910240c10108031900782d121000c520715032020740307a001804010990104020010201c10300e085c0d040f02030701e078031521664055060052030f195001d031051550041004208007071080740c2a48060314180140c64441000318042800c10155800c02c1c4130445130001d2000c0b14640c1007003428000e1140c035900d446160308040c0e156885409069004400c000400046024400004101e41180ea03001034200624650309800075210751071486a800f048164590807200c070f400107100c0b984030759413200000b850f04001003020401520043c20054051083d402500000b4258040c0c03903010300706030b8958074001072810041744151805107401c94000d030410006100c250b60805d001403004007030391a0120740d4a8080002c116802c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 450509712 1250 450508462 450508493
    0x40303140c1209120a11040b040b06030a14180703080a030f050f0402030f01110301090903111209130b03060a0911030d110d0507020d0305130306020a1e140d09 70
    0x10b014150541142400600041c10742210a03900e062001c040343c1d41040d100c0c40c0207400644003251408681d001c51030140c1c004080c0e42c0c0020400102d0114072000300d841600110b44050780c0d266a04e5000c0081d296540c8001c0c2e10030050700300c00310050043d0b10001e0b10b4ac60503110041c58140d0100d182d0003038501940210240c82e0441382e080085103031011911407106000d90301a4040d00601002c0c44003900103024088d07103181c066503000d1841e480c010301103008040b40740050f4100710909402031110003040c0080d01150f12182020394482c01c83c00104034640720300c900d584185914101e03113450180c40102d40603500c041141130000d0000343c9400c00c0403074042d02801d1154107004026840e01101c0d00100708000002005c1e080b603025014100c401d039a60701c20f9000103540f0402c250105800030380310340000c20807902d25403030800440e0394030f5840c081030307801c41c0968801160625121030100d04401c503280c855103102d8500b401c0b04000c40e860007107513449500d0b102098103444030081d90500c100042940c558 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 450510962 1250 450509712 450509737
    0x705040b0c0a030801052706030309030303090d03060608060d060c271e1d09030d0903090303020613030e0f03120a0201061d0103020a051002010b03010c090f0603050c04030314 77
    0x9441980362019155042c0c0a81140841d80307410004c5024113000d00003034080d0f44083c6440d88842041d00c034062800200520255061104218242c03145d00c1c180003035402160140c0040000c02410031003d815034015401950804c00844108401030f9038a00002a2054000c40e000540800e00301c802c8800040c0001e4103144541400d44c3c0004201ea060f09400490762444c0c112104038901184045101da404d03c03400c24400030a0000303000070f50742018000e8004011408892400c405d10264800b0781c0c2000d007040d008246014810401d01d40c06024090303102c210008407114045040c0c0c4c01420246103c0d00540c0110090a5643d0325609d0410105944000081c40380d030b106c551417907000b80a000b40d4003800e030200c001c094100d003518604a641c5410b030780e03008008800c858144014012207800c545070480c2150340f0740c1070261007604c080c4034401800040d81d417140181400c0c02141c0d20030702d503d42e001c0c200309450102004140c0c880310083d82c003a2070713041c03400400718902110101854025140316580303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 450512212 1250 450510962 450510967
    0x50306090a0b030d0807030b01020a05070504151701060f0504091a0702120f0301080d090b070f030e0d060f0c0c03090312030e06070801261005061507051b0d050709050705040b 77
    0x18600e800c003071058400c91031b07941e003801560292401243c0301c082c101c50040c0160b00031007041c011480c0c00c4d000795240c025521554100c4658508000500900d01014590641d46d20b00c0c090085411494190f0301034002514107005a406594411488010009410b00300c1003620300483d141510911005040d03400d0280003980310311000c6026009070b80f003845500303001d10071001c4886090340140d080e0411115214030890400065488010780e0682d804812000c005030203001a80c242e80b02058401907900502001403881d841c3c14141d011500070b1500e003010311681c0500140000d90040768041031300c0d88010000d0141c03140c070328143c000d820840303071240c541d00510042041c00c640c004090f038100c5094001c64004010483c108201c80c1000704042040e80d00030b004140c1110304103401250300544003034042d0b505000700a40110070743e0445002110b035a045400305403000c030701d81e0b007002c00302080407980c0c3c6000080591365681e86442d644a45882d0310386401c0092a070701c0c010b400741c400400f44c43ca603c56 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 450513462 1250 450512212 450512233
    0x213110c010c11060c03060613060201090b1005060a0c05010902040204170c100914031f021201091119020c0a0b03011509140103020d06080115080d02010507050306090a0b03 76
    0x91454005100100441d86800082d000740c038402c414840411400c840908001c2d01c4101c0041c1da142d00007800b00340c22007000c21000058110704107502d001001254000140c082c040e1404d6080414050314902460764005e03010f001c19510359080b612001010b0038050440f00703451902d07d0150070808006944644040350000e050048964401c0b90f2014a4050f200080b141c10100300001c0700c0800d184000907900704082c0026112401e40c0960098010122070300064001611409102e10315034920525401081d50703802c04482440303190141c864200280310308441c034082e00309039000361854a008080b860600c1c01c00240280300a01c038071a0054815031109071211401541a032081c840c1f40e007281d8400007094a83e903c1429150145e591285c46a104004c40302d00440c00307500005062901107607104000103007460b0912896101c07150010700da00360b040c5800d042c141085a04500c0c1019641480e04010340c1c032354031404403580305e40112884130a03901c0f03285010340180700d0340d0100d507014494031800d070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 450514712 1250 450513462 450513491
    0x1090f06020301031a1e06030f010c0f0f030e0a11061201350604080a1412010f0602060103030c2306040b0a05100303141b03041503060905040b040f0213 67
    0xa43c1601c1c000c1281580340c00307403d003492945100444060700c1908070301c0e907a2012103070700c0300c581c0307800c80402400ca031070b41001d010310380e821140c4003100d040114040200e000810b0760052920060103070030f81000c000c64080c4450003611040c80c82001400b610000b080407106079038160585481c00c41c03682480b000396071175181c4904034007161540c0b89070000c104a07408158005900100c1d0203441401e02401040d00c3d00c0e9507054041d000401c2000a02000c07a03200d42509544c04042c0c81c020400304d1604040e540f4040400124020540040e0210f4002000620200b50881d02160b003842e84846a03260805401c880c4400150555a0760300040c080c610901c02071041c01031607140906940c800421141d1600c3c008485180e0b01d5100080208011804080d0030160b690003420017814510007100c5078052610340d10307007594041d0304200680421a12654541c5a0612590002c0c5c0380c01c1100700024101500c0b80705039510000d00c004c01c03101b0180c41b80011074407103030300008240071340e4102440300590b5000310 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 450515962 1250 450514712 450514717
    0x302040f0e010803070f170d090c08070b0f091f120b0402040f0611010f06081501090605011e030603020a090603140d14130503030f030f070206010b09040e01090f0602 73
    0x802510222581010a940d11041c0c20207040b00c06110041d0b20300b61031941e40340c000c2e041602c0c081d1a0007900404402290501000a04005004c050001034121452521040c6202ca41d00101c040f940426818843d10280300221158445154800340d1290603074000603030304140740038000340c005031580115000c00d80c002e4600c9455003044041440285071810501c0128001c52241d490362824000003005014041c90041d000c01901100200c0c0300e000e01555a820380f0b02c0e541c4160201d511010902d81c1900b061601140508005541070080c0d601e0440001e0191110007030f44036001e030030701c08064041030180c2c0c03000004644c003074241d500c0c0c1039035041034400500291105440ea01085402124105804981000c844606032680c20000c540001c80c0c00389a08013a10014412030400c0c40410981e6041020b80036403003054002e1039aa1400c181c0c000c1060501901e41000e40d88003c005004071141d94060b2102000b055400040080d000074010f400750803807100245c800c0070004520810300425800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 450517212 1250 450515962 450515969
    0x8040201140c0d120e0d0f031814070612060f0509060102100e0102220b0304061e0f0207140a0201020c0103050c160f050705101b170c01090605070903020d150e0d030204 74
    0x44c20401680b0281ca25619003481c4c10700c002c00601d038a07264000e500c1c004c0c0d001d1440c0344103441c218052403002e0340c2e0f0300b0028045d0007201000e039401460f08100c02d41d8015195a1041c102c020144038980c82c241661000603c60b000b940e109800334000203480c0e900c02c11031150034042981d018820341418030707101d034001c0d8040e90160301016280d404408249001d040c0100c21900300f4099140b860340c0d203460ba81d0091642081c0740e030606030b008000c1645c0440b6405401c0c00542c44450050790362a15181582d81442028540d91032600004d0001003d40e1b00400c1c180c440f140e003820089001d41c2c3e4240c10380703400e1241d40040d81905141c01e4602050041303140f11024607e01c150211940c0e0341d2031b002044250003540811400290503400d001d050401001005000c55125400c0080b480c42c0c0316042c5049a040285c8250150b9595a07842041c0030050150a802000c241000140316081d600443c1160300003c601500710b02010010300da84e050f140e40a03400865104040c0c1e80c403604007200040c040d5000c0d10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 450518462 1250 450517212 450517247
    0x403171903090212030324011404050d0309030803040c05180408030417130314010e15040f020d020616060c0503060d14070e0c030901060b040609051009090e0a0204051608040201140c0d 81
    0xc1f01c40959500440d4041c2c005012440050b0400346000100041c125506108804004104c82c001002078016400785000e1446001c510844505190900c645e8802d601c01c038488207801d5a00340004105118202d070707001500000350503004015010600114130035501070348815514081c00106120b101040b20102c6a400c070024009040510170142e074807020910000002002240441d00040600d00107121241c4041c1100514090540025015070042084091109a5401408100102c0340b1660a80789042d080050460905002180c02d080720f4010040115101030600e440d40c200c104032500c020152400f40b0a050f00c0c048110344140e030010386081a240d8200304001c20084100b009035801d55125907074072003000786801c0410417405c6184646e24280010642c020440114500484400c640124020554220544180001c454005046441e000d0504800b01d40c8158007101060b045902440c0445140c0c03045d251a03070080c4120391507141d0074030071000003048680d0010300f010548000709 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 450519712 1250 450518462 450518521
    0x40c0305030c03041e0608070c170415110105073006060323060d02062b1a04060302060904021b061303030e0c0d0b09070807080304031719030902120303 67
    0xea40151005c100e00421010030680c1c00042d00c120720039801100d20130700400208105c2020fa62a4400d15805900704806070380c8407a00d28020a034018404075280c80910b0002c020600d09010001c04006459a001003000403005050f488a00840d12030f103039160000e0320400c200303075a0b09800f034014003030b400c103c9003100340c107074240d04440c114880d100e0711420b0090303c10ba2411480d9030801c4400d9018201d944c0000079091090140c1441514503d6101e00c204640083c018044c1040a4032003c11110118401c0d41440700500058540205403902e50720107880240e250100d40680010200780e03d400c034203547c402d0704200310b240d075011290240c54a0080c0c0781001a400c5c17002d0400d0b2595244e0508a4105502c40f6000c00095a5040090350281d03500c02691225a11041190b0030640c050303014500c04da10205042c01446550102040410704011806103403018030f2090700a6640213840380801d1540d42d041000554441c602d103080503d03981070603241d6a01d0b0602104210380d104480341c540a4855 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 450520962 1250 450519712 450519749
    0xf1005060a0f0f05010c031e0c0201032702100504051305040b010504020a0203070b040c21051912030e1002120f010503011505040e030f0703020d020d030605090a05040c0305030c0304 80
    0x70410410548140803c2c01200b6030600c0c00554110101000840030403d00844170750b0051005c10007001c008249540b000c08003003c0e400018141c80132071443c1d0b69081000352041c0d0012500040546074554162040700024a52071001d40c1c01d401a41e0083d80c102440300c0c01085244441c1d841248141d114403181e02e003690b21001407000303c1c0501d12803100564400c20944010403c003010217079000d44568288800c658444180c45240c0e2100d40226030001003848069080020500401c822048501e020980c0b0400c00c2e00c1c3c200030042e0480075041031517a564032085480a090202045800828100b0340d03860008594242403440101d8403d5031342c00d090f10010481385410f01070402c00d50951440c50780079034142400c0100510142518060038441040000203c4881d0405031000328003c2e00501464104114080d003800c0310320b0000c3c07041500d0108144803e5559820307460f00304c000c0c1d60340002c0e10f54039481c018612038410340004c0d240b840081404aa4503000000034001e4950514119050b10036 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 450522212 1250 450520962 450520979
    0xe33092803050306040902151c14090d0f02030f030c0c0c030c130b030c0306040c03031409061e0912060118020c030406032d06050114070c0b0a020f1005060a 69
    0x50360040100000c00801c08200c0710b103401d070041400325000800c810300001c00312003100c04580c40101103800c40601c540704c04a0700000c40c850703d0410360030311103070000074075003020b041d03803190303182964001889140c000c002c00c070038802c109450b0421144401140d032810504015000d5030001c44034181c00f403081c81140b6840e4103020414449913074000d4501880d021000c0109400780050019882c0c052041c0d5194400d1340d41c080110764000d40c09403d0040025040d810001c0c4031040360a80a0b410510400c000c140c9030703c92004946104243d04001740d004804520700809901c200610301c1d0344211000070540700d008010400904a0310a800401c5507003011006039404d038007a00c00a01d2541c1c2052004002a902940040c91500412202603100c00050508450040076004200801c5541c4403814400c651700700b103254002ca241046500c3c01d00c4450342c0d82028039079040c01005402500440c294029600030000d1020070704045c03054500354507801d200d260041004035601d900c90040ba0000198008 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 450523462 1250 450522212 450522283
    0x3030f0117120d150e0105040c0801141e090a05070f03110403020d020324040c06050903030706110d0905030306041b0503010e13020409110f040e3309 66
    0x4150801401c01aa0084002001030f004403614140c090344810340b440f040784885416101070800c6515642d00707541800d05000c116610340501c0c3c0180f04a280040c007403100e40c10001c403d109000c0707400da082c113210485083d40b8502161000d80d08a030f01c09017880b9030b826954022074420803003980c03981c880210f0740d9411401c1e01c1d8011080003c1c002d0400003440075042101c108040ca500140840da45400d113200386001d000ca00240e010210502c0340188410030149120420080205140040c180288030001035120303c20b41400600c019590380340310010740000700c1956416030380e008003088540031ba400c00e40d4407170340300311191441a450041121400500d0141d030701c015414550701c181c156801c01117084a03600000d03140e6881041c2d10142c01005075a1070003908421403080040710075905449081c406e00c0042602403c0c800d13400e1481c606c281d1100000c019020580c8074000c0d24408052040c051700405440f465401d01801000420440f80000200b2443c3c051030b864007004e01702c0c11600403001d4030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 450524712 1250 450523462 450523499
    0x708090c0f0909031312140a020117041104020a050c0c0613060f02010905030d1406012d0c050a1a0f01030507090e0c100206010609050f0d0602160605070203030f01 72
    0x1c1890020500c1c6814a0210740d0b038408180d40c101d915101079888a908000a107501283c07111040f55907a1082180a8540080c904d9a060040c80c00809a40c00a0102d0303030100030f812401c074403000002d410701085c004030b40c00450000d0030442d5205404000102641d0101c6410729152060080c000c0550509904039230720b00000c00d50302100d403810100c00300d400305410380030300e0119034a45113541c002c942c2c18401480d44990030340000807d101c600410f08890803008286038107000101c04900f03e0314400f240034410a490721000f0340d1910203000d1040d134000303080d020060002c2c81458104010441081452102101105019030b0a60b640c03c1ca0074001c046c0034040148113070043e8070200301d040007039001003051144040558001c41490408030f07040602c0d401d090310050340b00c10700401425400c450340c040031305000d03944c032144048401302040161040100c024517461f8005225021844d029002d2800154040828031007800c103104000d581e5001618140385054000d4000100c203c0c4124072848074 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 450525962 1250 450524712 450524719
    0xb030603010e1f0e15010e151f030b0d0b0f043e0a0902030702100c0201020f03010b07020a1703120705040617040c0b13080106060e030304120606030b070302030708090c 74
    0x5a0070140c91001c3d104048031301089102d03207142013a40b42d10742010140a048145d1002c0d580c2d19007a85a441c2540703108182602a00b14070000f04501c00798810f40703983e02521400e01087c510b0f611004590b500b000c008003e42001c0000301840000090172107001d0249000308a03900e07584603264030800800124500e0000980304443e44c2c81c0101e040d01da40b04655500040c61080051360f90340600090380c0c030460340c90b00160450302784100541c0162190034441200c1c4e1000310b05103c1403d942c2c216a200c10b000e907003510040824548110f580703502d1404054020340e402c2801d80c1d1a8642050703501d4200b80c1c2c00f10701c4141e020300041c8045201c0d0342694111362080e551550b200d149070746144040300c8060b1050724041c0c4144804181c0380c40d0480103004030f83d4600180b800c45403508111500315485504020104003044521140c50350340003040d00d094400b940f2070036003054200d140080003032039964030050030b1501c00810440c4c40358140d4003840c854485500c07095015942c1842c03081c0c54500c5440e21f04c1d031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 450527212 1250 450525962 450526003
    0x20406080304050a090c02070b03072f030706050606071b0312170711100204060e190b0306010f0e04050a02071a0c030a09030c05150709060302042106020d060b030603010e 75
    0x42c2c9009400c80074090b002401607501c82a109c9920409952080b00c0ea04041510118507460700b03d1601c0a024103111001d5204203a2035004240c82c3d103078840c8242c050503a80e1608041442c0383d4401089940302d503807003146e4040006940000071011072903440240e82a00c0001701ca4142c1c1da003d00c008031400317004041090260350b20410180c2c3d038650a5202030800c0d04c2188042a001c45843c130060019100782e4440d40e09030b0b9611010000030540001210b0701c500041076040010600c2c4c00e080d42e4000300c0c03d090a0b0350100003100101c0c0c07809030381088945e0107402c01044c400300e800b00d0350007851182e0080a000002d4100d06842e00c070f161360107030b40510013508100001004100f01f9448202164847d142c00b8214140c1da440d81440c1136000440041c41681000600070b465400c40a204010921307400c0543c1003614180512281c0c0082080c510320100d0820929000c0200701d50450321120b02c011410801180c40c1c1c80e540c0d2403608103c171500d0113586001210a41c0480006151030381005000b080344 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 450528462 1250 450527212 450527219
    0x61b020d0f050c1911041811090c0c0a0605010509010501171603020c0601090c030e1506010509151315020a050307080c0304030b071d18071812050109020406080304050a 74
    0x50ba40c0c0d00000041c80e00e8040c0e0142030390107890f40d04800301000d02a07030005020107424000c000031512659205042c14003001d2400c00040c240403400d8607a01c5c42110000100e0740c80b04610801845007400e10f080780c1c09846c89903010801154031407030603600d0a5550328150303a00c403801510802c20500070001401c603140c00107210801a14490701a45220307240c054107101034205814174100d07003a044603681d1529095072504c0d44d5850311880309003183d110003c024404055001030100340700038154504012001a80303240300c0e168003144000802000001c02d6030740c4c11f603804000000249004441c854108a010000054030001c0c00a00d020380080c00b451608031295540e0100b90b0004107052107a000601c03001000c224850840c600ca08596290b0034961403400d41c85160036066900840d203c0e40a01c2d410058400000f81a961b2041c1c29041c00c0800302101d2a02c542c8100807507201c00920003010801204100041d0003000c0130510030744050201035124000340c1e403240902c3c01f4a03038019600c1e05041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 450529712 1250 450528462 450528467
    0x3100509030405060a0804020418120c051f140f0c0d0f0605030f06011a030c0412030e04150503060a06080c060a0302090307170f060606030a090c050a03061b020d0f 72
    0x140d0422a11812a460103640d100424001c1d0003011001003c01c007018100810b504007402500b14500c950400307030490400c0f40e602c865214503400c80c0441009030321b0403d81c080001c2081021006c6c4501364200700701075002444400500540019200c15000030b00206900484003130305103000e00503480c0e002d41410214460140100400c40b40401c00c00d407680d00016284d10144804025442c1040180c4140d605000800140701440903058048003007c0003001140c5548034241c034191140c900f80c401e80310784030b801c08640d2420b03000c0c19954407a24207503e402c5030280e03000030740342201c006900b601e04036aa19202182114114451100c4039008001d44001034a070038401070545195a04006040802090100740340c205190001308030031920042d1880f4071a0100130700c10b0f03c0030592000302101e03c3c000002c980c090201400e44000c00b500c0d410103008000c465140c0c00041c1030003410034500755030b0302c0c2007a4005d80841c601c00103501007080b40c04d9020510106540b180c4607900e0b15500f03006012007108 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 450530962 1250 450529712 450529721
    0x10c020f12010c08130201020307111305010e0603100e0c0d0c0305010c02030403020f0402340f1101090f080703020d060b03011a0306060d0b160903050d0c1205090310 73
    0x89902800c011180c00040c1d6412041c0c0c0c040a840100028000442e0344002d400003034050185500c4031805103ca80040c0e034008221540d03103a22104094410b04c219002c10320341c50300000e000b00b46a040c0400450300c0b0b05900c0c51140f16031000c070110b509071540c0c58440f030111981c0c20810403054001502e0701c4030300e04020940c40c102c10710410010300c8440d41c0c1d840341d900311000030b03d180d00180c000040030029441d00000712151356004503411490070310307a12407010203c8003404802c40c0c00d40c1003200e00118401c40841c1000455000503240140701c404d80390803510383c0340c030000f018040307566200c01144000c540032120003902c140f00001e10610781543c0822850380c84421040710481d84818a150283d1801e000d116a000a00102c4c0241c00070741c4400c1606100300141150b014041d064030000c042840c04000c682c00c50f0769086011005024271400311210030a60708094410b12541800c40c01c02503000321440d4401e4000c102054910840b440e0488a41c8140c403041541940100500d9141464541c032 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 450532212 1250 450530962 450530987
    0x1030609050c0a0608100b1813021e0301090f1b0c0203160b0d0606081b09060f03040321020307050f1b1207111017191a03010e061501 59
    0x1140c50b4004020002064112250805400a407944044c818105031410551000d00240c07010682407600c81386140b8034600c6010740441c42504010180d00c400350069044504403c0011402a0030000e400c0415001e070b8400e11440380c00d2450903400b80b480030014443c55000e81440148526640c11000f01181c07043d690110a0303904d409210140096014101840c4004211030b209254441c40c450b1495011650240d01400c01d004c0c543d402c001500c00b83c3e000141031418402145601c3c1c040c0d41c0040303034160150100401d208480001031105254101c0f4034015240341000c45800c0f001c0342104204241c0c00103a40e0000841c109010f042144079480002d00230701224100c2e00410a85102d100b2803a0000c81d0001c070014880010b0b8800511095140d550020041038400c1140484203050060511211005a002d02c55004012403078608401c002050541000b84040c442080b1401302500128a2004000e100350b180c010707151036150000c6280da22410750300b85000c0340c80c0c003140300554400c4a10803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 450533462 1250 450532212 450532223
    0x1021c0306050a0611241f03050d0504050a080a020607020402071a0c030a0c0201140c070309270c170115021f14010e191a040c030e0d050405030601030609 68
    0x320100303090720f5241d040f400920b55651220044100c030201281880100c003040800c401041d0466102102e10b2034015401140c1000203036010200d00d050b865240000741c0009000c4e000b01a2051043c951040103841900c0f41151200b420540d501d0050356112048240250001c030300388442c4c80980741c00e901903c07042d40a17a144c050395a031154140010712404592500c01e620340403040c407811250f1481088103003140c5000030801c9d6101480a501e07001ca00504e22402c0c1c40001903864101485440c2c064000c110242c0381200c0009840800701d554007410030005805840d01840d03001c014480d06c00304079910000740140089909041401c144800c8042011042d0b00c680300307000c8003000b00d034802e501049130624400203002c0c419458504a102e01030b030002d200404880d040c411803c0c000000784846061503080010307024208100d2041160f15001015803252420884040b820b1f0540c1204661443c101705564001c55180802e84440c0918042d16826070f00c100e00600c0010000d03442480054001d6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 450534712 1250 450533462 450533471
    0x60708100305011b0e0315010512070518010e070e10032f21010b0f070f0c090e010507030c090e040501110f0a02010c1704120e04050915060f01021c03 66
    0xa88400703080d0344484c50300ea603d0303090380000c00f00ca43e0340c0581c0505141504601070000c0d4225070000b154060410f018842c03040032400c010503e4a14100030100080c40e0280c04100c48487c089005040c1c0f94003403062500903004c1100080c00f40e0301c64960724000c590003c0070041c4070501660210001c2000300f0110154200043c00c00c5c0360150001d4580391440c4000785840d90720105252236401d0865189942d55000440500501401504c001503509603400075404903101c5c8000c3c1845400204080400b0b084100c0c441c101013000b90b1035401c00c580d00c4001000a00080d220780320201e085484407a1010300040000030705000c160304d40d01e0100d07080b50040c000881ea40248400394a003940c04801c2007020003000113004007484e40c0a0007280c65046003030415001c601c12040d9030b10404000200010045d5800300341c201c0c0030502541c0b41e031151000280081003107250a001c440c0e40c460854008841c4242014001203680c607080424180c25a03041e8084c02c0031008884c480d00c1c070440c0d01e0460a047c1900c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 450535962 1250 450534712 450534719
    0x303110f060129030c0a050c01110a0f230d0905010209100e030709090819170a020301170601150807020a0f050d1704170307030f0f0e1e06070810 64
    0x300800d6000c1c040e080c0682c0c0e0b141c00703030207a448107040c907110f01c903600c11405100300250b4021580540c0c0f002009820034503900c21442c0d0407580107004440e85200b13081c20100e034441100343d12007111101c100d401d0310f4000e40d102204060340d10000b100d0f800d040301c96804000c0030340958440d81000510700d03c680c00150070840800b0000d4410660340e4040b0780059801c421040c402e140400485d002400825002c00c1507244d90340720614540720306192071503071100b1040180c00061103001044e000400f0214500c2c01d0742085070909010303610030305c150304085414100004100902140031412600000f90642050350350700c1054425040085c00201503005040000001c82c84482c0f20084c1319200328040e01c64002c050705d02034036510440281c100000b05850801c800a81880c1500b030300b40300c0312000307a0344a41d41c59100300c1c041c00d10002c00c10422400d0180f202c035000342e50740186e01c107002d00006903410168a082711030728150079100d066203180c2c440740c0815050340c0514401600094031090409600d0746 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 450537212 1250 450535962 450535993
    0x4021026180721081303020913021908062d0c120c19140d020c010504020a1202010504031b152001020c0a02092703180d0c030311 57
    0x34110360840c01d40003030003158055140c0611906019080f038000024158200c400d000050310000c40c4003c01c0e040c000928440c40c5100c00d006400190303030060102c140d0b032030510190098000e01c1c4d10200c0c00380c282d040d00342c4000c1c003d144920040e604c0d1400200729a47d601c0c1280f03490100e09000021034941c4070400c80ea680004040003511074142403803042d13500d8889040030ac0142d1401007600035075203402e21042c80840c8411f03004c2907900d180303407804103e049042111850580300301c181d8041c6003440010002c01101064000a100f5402200c0300c0040507900c004d45c18480e1400a402030002d03204000500001d0300302e040c0741441c1d4425400c412422a01ca100308a000c5000d64010804511441042480d0101d40003030504016481c01c000d60410707800394202c0d581d85052100080c4107030300c41c400145c22041c502541c00c64594030040d25850604407090056101c1d40328404c1b02403419003944125403a41014208454000d82c083c4503039134103e00e140c800302e6607a00440690f0703109000d0124079940045 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 450538462 1250 450537212 450537287
    0x1915080d0807081627091e050a02040f05060711040c08010e060109080d050f0c100c120501180b0d230c0405220206040915060305090303040210 63
    0x40340392650380050405810180428a00621074481000c1000b880c25407150311512031107210102c09660b030507000ca8509000794251450304a401540e10b0100441d01341484070540c0326440440010401107926440f00a40c142c0c03086000c1e050f48568090010405401d10400a00e0141d0241c58801c202401a03800102522110030f200030000c1c1c0144014840b041090440355013042003400c0000d800c0e413401d030219440c1d10145980c00700340040400c40007001c12090b02103400c142205000e039000200e5410451004044030451480020001034010450304881d108090580e1600601e0100000e900c0039080042c0c22040e92040d0001c06401880c070009550716048101c081a1000088981441c1500c403482c00e03140d801168413030b9060005204603696401c601d00b04288041112800790341c503d00115242e44600d5002541070303458080d20700d01040c00b001d9040d0079210a9138083c804d0b5282c280180e42d81f80010340b0065400455005018900343c02645412600c94070010704900c12080011802e800c0c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 450539568 1106 450538462 450538483
    0x306010309020d06020703171b0306010504030f050723010e0906030703120909110f0a0309030e0a0603050103050f0a03020a1101030908030c091503191508 68
    0x26440307a080000c4042d00035024006444051030070500940c0301c070005070b000604080410f51008110034840b80107030b0a6a06080009103c484445440e501c0a0440e0341408020040040003950f034800031000c1e2400f074405003035134615109070507a86c0603203900c1c1030b51800044020402c49a80000350310191600503240c4901a65a850109103010090b400191020112810543ca00f036440100780d020743d0078041c0c00740300d50403481b100440540220004031180320402d002c001c058900c644d015403860b030300074035054464085034000310b040c40060381c20100009440b6001401031180402ca94042940e510005081451658070000d450300b2074500d0040403c100d40e440f540d4280e1090308107259854200e402c02d0741d00e0034240e42c0050240d001c5a2118040d078209680c160380c0c42c040c4410780c0d10800720014041c0c0c505118202100040052012111711070001902c00b140181c1c0800801c400ca = true := by decide +kernel

theorem cover : BRFrame.Cov 450359712 450539568 := by
  have h0 := BRFrame.cov_init 450359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 450359712 ≤ n) (h2 : n < 450539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
