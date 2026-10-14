-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1592
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:45:02.903774+00:00
-- url     : https://prove2.me/submissions/607f9495-f697-4e76-9d17-7c66a3d14d49

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 286151079 ≤ n < 286330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 286152329 1250 286151079 286151083
    0x6120903120515040e0a02150304020102070909111f03051012061802030610080c0109120b07020a05031803010e0606060a080a090c06030e15090c1e0603010f03050f0109020a05130e0a05 81
    0xc2c1701f40c0c032901c045412100800400c40c00c4911a07a4141d0141c034402c1c0c2049900b5008003a490001d840f06031800007054655220a0000415981d80c54104003140702041001002c0d900c00070f001e850788d04807200c0100000c10413041218403071a401310700031a0440c0300189061a01c20400c0c00a0741c14896a428030400b440d04e082d421064888a905450955244100550b40900c0340e00c500ba03625011080d2a001180c503a011554001101d4419101003007240c1d2a1149143c00402605152411080708406545000d01c20049043d140d8800f603c028601f020000345030b805901440c0307050140c000c001607078045c0d8590105416580c0184515203ea45450b0001c004026180349d80c00d881c4542d80c0d0358861050f060100c1032007428039200502101488206102140d00707080900c00b8550a01d00e1518401e9890002039030180481d100b00454480c40c504000b464010502c54000e40d691410610784050b0700c03a44200001c1e207000384e42c041490101d11000d80020a900180740031603005260300207042240c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 286153579 1250 286152329 286152343
    0x17030c0a12120e0a0206070203010b0424050108041725150608060f040206090414090c0a0b0a0909090201090522060602070b0d0e0a020307060906120903120515040e 72
    0x441ea942c42803110a0400000c1180d80710b01c0051181d511010300310005250107401080300030300c083c0011482c2c030010b0001c2010343d040d00e21102070178918501000303611201c205080d0000d2909113800c000b40e041c2a15101460304845106c2c0b4140d140006081890400d0141e001c20001d8814901e00050001030400210640444041003c594105070000070240c00004065015400c1030042445a0f151542003240c20b9204c5160141c115840b120f82000350849184003920a444070005080740615000402c0900216500a1420303000180410400e0991040d01d00b402d545150360005800344841c00165000940341d440b41c0e5114603a000c020808070b000303080341d107052501c8080034003026807511800e80c0c0f6010540179940f405201448000d0a038900f6030040d0403110041c406a441090a40c1c02003410821b168001c80c012910700d030f100f0040f09601048961080c422070104200e1003001d9a402002c4100c0485100320380e03616200030465022400c0d040280b00d21005200b00140f590007115541c803000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 286154829 1250 286153579 286153613
    0x20603040c0f0611100f0608010c0201020415050309070612110a0201020702030c090c092b0b041e0317041b090e0606040b09010e10030213090605090d080117030c0a 72
    0x39190b04001200340c021131a000341c598801c1d019289400100702d450009004030807209240a4807170b00006517100081c031559000240c95400566240d04040000c0350f0091aa060030080040400c208051700c0c00114030139042d00c4007864800c00d03d0141d50790240c043c00181c500403010b40310000388422a260154014840c981c0f013039007540e244001801c204407008000706c0710242a06d00c1041076a00b51324010050311016402900204032100003492064280c0041d69000c4420818400501c82030014811a201c002001c0e09035540c02d14180341d800505211444000d805010442d20200e000c0100c651210307503031040c6001e01c1c2154103580e0b03800c01014009060800a40e400350b400860154105801211030074180504642a140d02c0c01d04802e2403280c0c001c3c0b078404000841c03040840160307141030f00340507002c00070800483c0603660b5062090403110040d103059101c0e4072200d1a107608580000d055411103281c00301152100c1a658617950031031107200c0c01c1d580e45009039440e2100300000c1941080703181c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 286156079 1250 286154829 286154849
    0x105071e030608030f0d020c06090303010e01080c0a03030f0203190207150e030c0d0c0b120a0b04090506060108060406031509050606150403151103040501050403030b04090c150c020603040c 83
    0xc0e8003080903000c4503010b024443c03030382d00204252240d905011008241280e4030640c0185000011504541048802d0b660026540c000100401200403012010b902401ea580090080440d41c1e0002444c865040c0c031009080c4005200750783d0109000b441a45e99040390640e55109008202c00300075182c9032a40502078010001c000c8040440d0322800e0302c49103003180a00209160300d040c004111840354082c800712021013038608042030020068019020420200d0920041400c010782e40380290750b401c8030b0183c06145400035800c00300e44d0008485800460030300306080715480701d0000c100503004035000600204696498049806a00e90040c41543e01440c06c3c0c41e000e0b1100e1040110035010400310042c0362800b4031003480424811900c441108010100000f01580800080d40e026081124160380340c0e551001004141601401148440441201c00b08031034a00380d520300d0260205401000105400c0d102c121822a0107a0030141030319400038015912880c003884c10184101140c050803d000e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 286157329 1250 286156079 286156127
    0x1902130c0905040e0f061b070c060201021c14060108091905100f111b011b050d0606080c04030b130b180c060703092d08030c0c060421050f010507 64
    0xb001c4c0402c801c5105201c00c00504000c0d114442c2d002e803c0868480e803c10030020070410b070400500078070004e00062515400140e15403009440081050205000c6c40c511743e23041440841b0195030740c040780b0764014800d00700302e080ca80741c401445107400c08003484011440c0c0000c01200900000044050f001e03080720500f40700054a1031030f0b001c240e600803043d40341c0085050202030440c040c844546086902c014000141010b07070001c000000814840040c5d01280c1d002030981c0507980b07140662400b074040c5050001c080d00385482554164840d900c8050070580d8110085086511304500d00f690498002c401800503007001c40740a500007034101801c280912a01084002500348141607400d82e5406485603060301d490145403118191b0010025445220844010260000310703803004801707012a0742c01940c4451070060000c0c602100245000c2c03040b041804104004030b04034121418248031045a040181c80c81e2409a00e0000002c00d924a0303075003024100031580b82c0c02503003000d02d5007841c084010f031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 286158579 1250 286157329 286157351
    0x10909060f1b050c190f05010c090602120a03060b04030339080d090f2009040213020a02070b0d27030804060c09030507140906121902130c090504 64
    0x440b1000c54048007221520315200d111070780500c01408824100da070540c2c142d051911412049002c03142411140c07002024180c00500400344100b0318000480c0c01d01c805d20750308140002e591004d182d9246c0c100c203600012400d03c03141c800d4000d44001c0c842400000e440d1358907450050700710500c03601401c01d402d00140c0c5403095165400a0540c02113040320b5003020440850721172122560000640000741900d5107100c85c0010054038850f4501401036061443c03480d1081e0400050079800003482c0d10454200081c0400342c0d582c420381031180000d8220042e5203444e081000d0381803868561000303d0022010420b20300c0105160000c1d1855410b0039662819810f045403c1c00e190455203402600080304200050300081c4180d00482d0700540d0760a02600850381c0b07645140c41c04146810690b180d0b08014a140718504202e561a0b401c4013040b81d5003a01d2010004540359114140c1110754980001428084255290440b0108400192035400d010b030080742c4401a00c01010f0303200b1240194a06000080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 286159829 1250 286158579 286158581
    0x6031e090106060320030105131d0c030609010b2d0d050d0f030524010905040e0a0b1308070b13060e011b0302040f030201080603030d020307090e0702070b030109020a17010909060f 79
    0x400005c1081c000c50450b42004103000d03e01091003080d00038540e445018a0041c0c2540c0904030601000200071310005108009050170050082d0440d20310742c1c1008090303901f40d62101c2c0d0103d020381313821100c21000508543c00106540044084da40c100c4160543c0000340700002c01d141c1c103c44000e4480074900078141c0c50440446408a510318565100252408a1046124170342542074005240c040c0710183c03102c001400b2a201e50780d60342c05642c0003041140c00c20015400041e800a038251241c8178150041d03e444200d4480c240700148840485400105000c4c0f84000f030040c0b9940181381001490440130150340204040c901c502c00039141c2000c00a0305502c203000b200e040d01d0340806040b908518680c01510032030006000503905002c280040340304110103101440c0b2900305a40c4040d00d8078900070641440314006094031045411000d0240841c01010085904444107150016514002c0c2c4100b1174864030710110307054a0030b00440002880100a0304880d05990040008014403180400301c20 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 286161079 1250 286159829 286159871
    0x611061306090f06050c070c090c1e03060f06260114190b0f040f0b090108061c050106080d02010e070302030a0b07140721020d0e06031e0901060603 65
    0x200e0420024400030000600c00c1d001901060b1260b0030903602e900c00d40c1d550300c05440007190201080840810392070203100075181c148004041d80389041010308040940140b4410700c52062180c1341030718882082c00c2c00c2c4640c0c010740040c2002e51543c0c49442d00d680000f4542c180c4c40ea0020b4207500a1030300d07140742c92107802c055030403900700c401c101450a80d1842401024070703150380700084280e4110030000d04465624000e0070206510014503a0b141e041a5011000c42069080605480402d103c1d09034666040741d51710b130b00030b0b004448004441001c040d840b208641ea41d18001d12950074884d0000b410704001803603208100454009001e24103403800120b5540c604c0307100c080e62641c00012045e001c21480f4882d03e4024100303142051050050460441c0d04c2e0380a4681113130802d0340e05010341318070341c0301c1660403990003a54030182160044420004001d907140045103441540c0010205603a040c16652452294244801a610714548134080074020f103824810500460b0405444174803400b40351f80d0720 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 286162329 1250 286161079 286161091
    0x109050f040624030f0317071202030606070204020a09080c241b071203090e010e040605060316030b01050f03160605070201120e01150e070219020f19061106 69
    0x103019a0740d55890340b0000c0c01034039030b0244000000c0040d8100c0c241c0c0300c1890390061402416030000e8080395250041c00034000c0310215a40150031414003004d594020354255109881e030001580b66240c11000480d02e12551800075401407002900100c01030304144000100d849030000d60b0035204001061180c2c080d03045544204c1c05034008014094240b03804050180d0140f811021030f40d18042c8040d081c501a5140c0280d404030100107103400415900c10b4081001d4020342c0042c20f8107515002d040c500c05500948000c00c4551210001203032602c04200c4c3c10f02e80c4e18548211072500f80d80e400c100c00204001e015030f81c040c4865002c00c28075410b00140e51500c0121580c4003000880c82c2c00001c40d090f4101c200203c0c1000000361a42040d8141ca0160004040c9448000102280388145491800d04550b00c0702400e0f40900d400c00c1002600482e00d560200c040205240c11841c0c6440020105800025450f50206000044951a0042c48181d0090343c00c2070b1909449040b01102c050303642c110403103403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 286163579 1250 286162329 286162351
    0x9050a1406031f0b09010f031106040f06080703140c04030c083702030a060b04051f05010c0201140408210405030c0d08270f01030e100b031906020909010905 69
    0x500441c0d401070f41c00a0410b900501000501d594510001070b04c0e5402030307000040d0000000c2c418024010014041c070580703030f01204d045203001d207801044c0e0b01c0112144a41c2040c401d4280018600c107009030080651007444004c1c11083c0d00e8690b841281c42d400c2800180c98240803490b000c12021000628000d18510a101c1851038451400d0f0b0701002d480c90010034880a019100f202c00140c904103d00c256051049030041040700010f02032208070b4070b000b07051000c0390742e84500c07030360041d03080e01e06d1442910401e04e0300c09400031690005850804090703034221510080007500082d804008950005a010079804c091480d1048465460450065025099041c1c100303400080803460f00d86410708107544200075081c10003604044a07001c002d080083c140e00804100181c49442c1360104180403401e0007420104400b4500384e0781c140c3c1d42e00c2d080100000300e55a5070300307520440d90308001c1e511702a001d040950a00101c40d240074400b075081414003d0150165400104440210303000e1244100082c1c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 286164829 1250 286163579 286163593
    0x60207140f030a050a0f020f0118090203060a03020a030c080c0105040806010501051b160e1303080f04031403040c0e060604151202091908071a1c0f0609050a140603 72
    0x41046054510403075240d50500c903d40303081001500c180440c21503103029108014007004c030b038018042c9404d141d140e900d0402201740440c9590b41641c00c0d070304066610440e80141c603507940101181c141121600302079845050080300000704401021004280c0340400306891820304407400665460046000700d880302c0d08410014030165218a0141108951505841e84005681d165850500802c1ca201c00c6804800385002d120b0301e1058800c60350480c541440b5014540b034140c40c01488648082c1107090306002c0e040220701410312130081c00000c210000c5034507549080528005144403001c0c4600e02c0c096607070000041903842c084050742c088580c60380a0000241c00d040003107070304c40c0c4011240c9070f40680c2070080f6561900d64030107036000e2524541001c0701c03650424010918000d01944488484d0b004000e4401078802181e00b552023114509903d084640700d0b204e5280d0280106a181121180c90100d0000b0b000d8441d0308850301070703c207054003007215544160079010b1041c82107907c5605503010030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 286166079 1250 286164829 286164869
    0x40213020a1404031101080c13060e0609031501060801080c0d030e010c060606050703030506030f121b0d03020a0f0806090105060f0706061e0e0f060409150608010c020106060207 78
    0x203001003121019034a80300c03040030000104600707190003580058520013071620003e00c141d42c100141d1030300300b030f400c01880d41032401070350303402200704220b024031400c01c90621144580307503c40c00d0944000c0230000b02982c810365004100000e80c0c0c88240320301d1000840c400c0000541f6940440e132000c510b00c010f0003204080d15141c0301031b50101d802281c00784c10040e0500c880e00204855100e802c002e024a40c3e0303000d9441a1500380101030724009401c962082e0000d40d4041042000000c04e0440846102142030300c40030012050703d15180d12800e100c229006401d100610198507a008051030b00e81c98494020912004404880303201c0200c404540050840d00148007501d44074018112201f5100c1070503140c03800da42c0e204802e5440b2a44081209420003010203210b558522103074020308104e4421009030b1800300d000c4140148003404c00c0d03008070f40e2088a0307014003103105400b4512494401042c8000da5071102040d009024403080d600041d443c00f0000318050348040b8584084401c0c0c80c034103a04400d030076 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 286167329 1250 286166079 286166081
    0x102061312050c0f011103060a050901290d0501060f0f0503072001020d18171908060414090c1002010b010507020f0a03170c152401020f03070b16020105040213 70
    0x9a9103d620910441801e2541c203e03090180d02c036000307070008140741c40e42821818407941034026001a0b01c03c01c01d080044c410310030120310281070030024020881107017100200c144414411403001341c0c1543d081c040082980c9403c455520032280342c55507a00301408100004990782e02003917440b4000103000c071008070424101040c4642c4015040380005103440904144d0001725000c68010307103500320150085905001c3c404054120196031800150701c0d01e41280d01000191000d12a2a418005070b01c0208025440c0c0e984420740060400d070340080d0034108605101ea54804005409115044a8030202200b91060050700e00300303601a10ba03079003080b18a500b0070444c6024070402d540c22022910000000c07900b0301801c4401905040b2007503a55080c00c50703015041910042099011886040621100024030284101c80d148412a00a82044036070700403802d02040304041e5050b4803000c1440010b000d15004154020b0404031180224003d0f00002642030b590215070196200385051000f1400b0555 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 286168579 1250 286167329 286167337
    0xf24050f0a1d03070303051b040b07060527010209090903040807030b130b010b030403030f09020612130804140a09090b07051315260613020f07080315010206131205 72
    0xb460a07142003122003018142e29642004c101640046c0d2140300b48000b14101040440b407241c0c0074000035142905001a040c124858150000d00c0700340d503440003d040c0d01c04030001030000e40070303451a0001101c184103a68040e422051045101d00864408104110000410fd41c02c495980018011203891a115040040c034000e03e0b10030301484000450b03001612105070b55000e080c3d61010b864480c2083e040050403075207141e480c60100f03450950031501580c2d4403015183c3c0150401d1f50b0060315503404032080240d100d4104020203190011801013000002035940785c6c81d1041c151589110300d551a40e620064440601018141550200100d40814417a2000b04041c031048450f2425180d034400b01031012181066084002620107241148115004201380c42c8507083d03003a8003003040c100400024035081083c14081915940017511002d001107001c2501d40c1c01d038000c1409900ea1030b2021011074841d12260040d401030040c0000151400e5001e500301d00e0041c1c00c900108044000c0080a4802c1c1d44 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 286169829 1250 286168579 286168601
    0x918091203111c090b0c0c061503100c030c0e0405100308070515070210141006030b04060807090b040e0304120308041a09010c03110a2a0f24050f0a 65
    0x8010401c5099030800c006043c0718440998100040859050034241d85591001e041d0707a078440810031000c00201400161140c01103400300c941104562045d000a1a000c264004548840d0414480902081d051b50000300d60002907240c41002c2001b4004000c11030301c08076810101104028020f101040024010344282c52043c0120386154201864480e11035000b1148000140e0003501508001d8483c2d00075013001003aa03000c100c101d0300b85044907240d01181401f91008156030f0389248101d980e00c0790000c000801441054801080d15074031050701801c1918405030069040a0780014860400000c039805c40380c031020141c440180f02ea80485140e20040c00039117200a54000c20040071010780705141c0101d58000001038081c40c812400340640b0342c0801407000364002070180a0340300b80c0021a450399400070000025842c0c0d80d070860f090722211221805055031004c000c45004101c01c0c1e0a1000385906100002002c200c03c0007041000d0700c01c04c4681e0f1081c00c41d0980458096816904082c0c1005 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 286171079 1250 286169829 286169861
    0x6020a0c080310060315030b070804030201200c010605010c0201050f0f070b0c091f020c06031b0304080a0e0a05011d030703060e03250827100918091203 67
    0x9203545948019801c1a6490f00050349400400c0100035050f1140c043ca84615130684003030784e851900c541d601208000d100605000d046000075003094402e500c5101d04860091000000656421070304200780c001c5009c40c50598a003c0d404180f540c0100620a0020b505960719850102d0350781a0b143c0c141c115456070550000e083c41460001080c1c1841a841451202d040c161250b02d4a000c0042c41445206808919200816503042540d404143e6000703182007030b110326599440b022498a0f040440403100d040d9144040300703200401520360700402c0340910310b94590b020140030340200000129184505801725a40c5040a06021414801241c00c80c00013002d907081156607448000c160340b407031101081e2682000034003000400d6045d40c0c010017040c01010010b408401542d03030700703207601c98003407588403c1d070b1800b48055501c851411a401003081c040d1020301c043c101c8940252044102e40900c1103806100112001c14002c10b214103448140c014400b11856500b08401750020626408415100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 286172329 1250 286171079 286171097
    0x315130b040501123014070204060b070210050f091516060b130905031206030a080a050a080105030f0c01030c03060b03011403060601082401110a060506030c010c03090306020a 77
    0x203030741d42c2c82594000e01070139140c079440400a2a242d40c2c4504442102552410b20a03440c0768003500410b64560743c000503041907605104031002910031400f0307c0c0b00c006d621501302000450718a0181000e031054070310030741d00c041c90b1142085c000d4500e8059080b8103e150b01091241610300e140c11840500b045c10160707178803494482105a002c640003500102514000e49641c2c4400347d40c1003400c2c450001d103841c0401000140d030036990302a1240716110b114061300b00c14030041000d540c1d042c000007448a60000d03a07180c0d1101ca10b50083e0803034005401e031802054408000140c1030030049400c00103116400d014040940101005500400521b0821002c26542d141c0c0854061651001103011384408006090020540d03800c0510705140205480d0400916206000c40c2c018074804030060701c161615501e040003050700c012100d10310b640300d00c01e440348030b40c06410050250b994030440c06200180e042e01c1822200d81c0040d00c9400f1b141100500003090700100f04003241c0700350b01818003020145441070b11 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 286173579 1250 286172329 286172351
    0x106020613080c100c0e10050313140303071718060703090303060504060f0e01060e0901090c03090b16020d230309100914070911120a140907080601050303031513 71
    0x904002440c803100030b185c1da070911901540e00038400d220a0101203800014680c10340fa80206180009006010010101c126000c10480144030401410100c0002c4a840b458481402030001d4000d00802e204548014082034518444c40c40e07400956103e24002c1503e500c031200d00301c0003080c10840c140d00b01951400007245c141d680340240402415505406007196082072124900150181c0c080c005101081d1180b0810740c44903c911811039443c031100003407100300c0c0c2d4002c0c1c001c0c1c0100d0200030406186042049054000111f420b020440264211004540c9640d810b850110501a81450062026007888089004200119404185a4142d8200ca034298503601d05503414080c0031104400ca0341444080d4070300410a040c01041400c2e000d000c1c02035410108480c600c41c0040c042c3d071400d0001d001840c4480c164010034520050109a00f8942ca840503078107480c0d001e00d00a40d00c0c140503002c0006454500041a80d0282401502101030001d08501308504091a40102e5209036141e10728502 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 286174829 1250 286173579 286173583
    0xe0a0f0b0d060e0108070312020f100509011401050306150109050d03260103080d0c1b08030a0b01080907051002190812090102160213140103080405010f080106020613080c 75
    0x20041500500098440c0300c00441c00040c0d86150b0400c00b4006407034001040924070014990040b0707500b0008106011099007801c81c100b0042d6400701000c1e201e0b17000010301c4c00115910851150005000801600521a00640c0d11b10001e01c1281e505030300840206400002455550f90b074040141000308082e5a14404500c5100c2d005030181d020031499040341d801045059100f401c403651885a0342c940c3d60455071611140d004490702902c00325600c00b000c6941e03502408825108140e02c481401180d40d0300e1a08506640c01242c40078100c50a041841d540e0794010395402d406050008094542d142c1884140301d80901e8170302400b01180305410280c0c1000080e11703540d070a0340303000300704040c4d0300d502c20701081c0010f0348080c101801c3c0360f20411248072580141d1040640d0681d049549c4030303400710b424901d0300c0640007580c1d0602e8040c1c000c074000802c10110740020000c9802c2a01c0d00740d400c50b4410b60940d0180070912500016802613000120b0140c0310702c80002d8035900c24080c1506083c1510203042c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 286176079 1250 286174829 286174859
    0x11030717061c08033108210a0b0102070801060b03060f0423010806070c3f0201090210082703070b0906180706090b03090102160b01230603070e0a 64
    0x30b622220300200f84120080c01800c5e03141041c1a90350941c0024003000040000c4416031507010746100e1020030043d0200c4040b8440305d204206d0b96141007103038208044218014200a0100b82c0980f02d00e41c00060540c406019640840e681d8032a101d0843da680c105010103400701c07480b02e9070700945d01c1c001010011400b072020101c9608407040e2120350340c1045c540510b03002000c0d20207001d22052400c0000028091101d9003078800016488102c030350942407107680d150030b41d540401c03006c1400a01100c1060390562090703008900841d2840c6d1100380c4100c0135200600c0c1954142c0c080035120201c0044294010f80c16001e46040d60122440c103400303034403116a40750f82a210b000040e0841403d03c48601031250302c00115a007a0009030081910300980a0038401440c0303e035501281010000031500c10b420350540354015030100742c0250050f00b070328100304019024000c0c0701070049003c0221040d16081d821055400c0c8001c0c3c02035103145c880a0064944860700022280d22290019000c03581318207040c140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 286177329 1250 286176079 286176083
    0xd1b0c0f0503160b011403030f07080901030b0909030c070b04030f0b041e0f0201080a0e0304140102030d0504050d080907050919020c0f1f090b0f090f03040b0d11030717061c 76
    0x140c4ea55040c050036910a45c00e08840341c4c42580207120100110500030704580c10281e01c1010959a810b0250041c4c01800104a5541c1d02440c1841044422000880200201001c003c195180181c81d0040f002c1240914000904011800c9401900081a0014007508140143c50000114800b08200030340e400d003021040350160f801c010503208658202c081560040241c00c0144a6560004d850581ea802035104104020307408810300c541070790090003102c10080f401d16050005140a04046075958607092502c0005480b24001500003080890103100340e680c0103000900d00e803142c5001c0242401a4a50520825400c02c48524040d00c10020480509104000780400c0e8042c980007040b402e4880300c0312000d05043c900c41c0000600f00e1400c143e0303c40d110003901a07030b135141c4a0500349050780c00c0300f580c05607100010f0040707441500e002c060b0100345078589003400751910b50710042e002408180d40d55000300d482c00180c072489080c3c000381e5550258001e842c2c07043d407042c0030b0740d00343c0309032801841 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 286178579 1250 286177329 286177343
    0x3070309032906040b0f03012a05070c180e1506041802061c1d01050619140925051b010603030f05070c03170d1b0c0f050316 55
    0x3002000000c0006800c0600019541c0402e545003195109245000030000362103995101240036a6aa43e42d42e0001329490180c020420703c0c0002005070046008841d40c600c041c1c00414400040602c14821203031059400300c0c0004d480741c5003000070000d00030f030614801c458944070410185480c1040004604e00f001d09001062a814020117120072035410700d21101d1100f40c1c66441a000d03031204801c031001e412441c402c4010a0010003a0400241a001e09202c1049504030b43c4224518054010501803001200c550b04401c3c00300c00040d6050126108540304440307220303210fa206141c01c4030413940c0001458507008031910320003984051103038803c11090114001140c00281c0f841c144030080018035151000300a158115180a060f41070010354050805c07400088080c02c0001c0c1140da007000b50b911207184003080e5500801040780c0c0e007007424403090143c0340903900b0520000650b01c0b0205400d1546840c201e00e600b0740c440c0082c4901d5580203444c00c2c0700410035421040003000d41c40403541d0281c80 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 286179829 1250 286178579 286178597
    0x30209040f0b0105091605090a0504021b0f0a03120b0f0604090204080f0a170319140a050a050103120e0a170d020d03090503180414010b0c0f120a050318030703 70
    0x203000d42d10400180c000780c2c000d0024000f080250950550300e00c480510340d00700b464807001010000340e5141020b81201e1781040c0049000f18100700500040144051444c0c1560011400c0180c4107603141012040a00043d03103104c80e100c07420321964052205001c01030000000182e52002080f81c03907101d640002c200a0380003d003001104400e00c0340050f00304410001e00490149510f804074480354a1103084031079400000480c2c541d42641c400007aa08511032001e11100d8a41800f6000d1928101d4134580002d0512000542c442410321505044e01d41c000a40c0b4117041c03408108852010039020b00700d410001e562004110005030b0b0289941c82c1c81031100030b0400c030301c0c4e4940080c1003030074000250040c1414040880001f9002005a8103250340c0100c4141c41040d00d000007030b001d0f00d42d02403200c0321070300020004500d03012050020400004100d0440300905c060100281da13071040d04d29500e644078414009090a1031245004541000c040030300ba41089580b20206402c40d0300025080b008291001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 286181079 1250 286179829 286179833
    0x70207061b080703050f0d0f0504030906030b03061501020f0105090109050c031612030302120405060f0606040b04170102040e18100501060807030b2b150203041208040606030209040f 80
    0xc41490001107020441d201080881e648101032401103181c002d051081c0444d010035400103400584980700441e41d0300b8840c070304100810200400c02580d080e07000980c520408a4a58000d014041407204007030001e103001d80c0c0d2120072004503451958403504500440c44081e10744030090190038090902500009001c108520303100b4034002800c1c0e40c40f4000d411540f42e0b00c861949a40d041c0c4100c800c050841a0400050f140480003031003a00d8050700c5041c840028032090003000103440d8810b001e40107140815403101000c09c411400b81c3e1242c0400e03e5002c2005220141c0c6035038501ba14000c001c4000b600305a1039080e25400c05001b1a81220301d039800c00d015480b040d0b0100000035001c84000e004006035410a10010152100202610f0034182c40d4000d640c4142c0720070405c0c4100c07a40e00b5a01207a07520702d48102001e01320282c14180c134501c00c1c1d880c05484144c0d00e0301c2168000c0350f110010080a0748000b205842501d001001a1940c503039420000000d44c50b21682203100d10310583c16041245498 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 286182329 1250 286181079 286181087
    0xf0b040e0c040c030b0102030d05060102030415081503070f1e030501060e0f0703050403090302220c03020c011401050d1e050709020702011101050108060c07060213290f09061605010507020706 84
    0x82c83c0350004050034075100ca40566004402c03200d00c8010201d000c901c40d038031800141d03c0e500c40c3c1d40c0030310803140900500b0680907031b1042089010362841120031601001d14000c240c0d4562080c0940c0c4542001e1810401180f0132418404126940c2101b005a80e99034035200c15003100e803294000700180401000f00a24500942c115950140241c2000c00c0b4605080e14000d20400031400000d01900c0821110700081a04504030640d1045020f42441090940c240c002d02075006405691469800c003445102000b20b02130210f81a0f85003c0d1a0340e600801c1c40d160790035485248204220000c200e0015600800d04c10b100705006000c00c11f0b009640c4601520004068022902a88940d40d14000040c850300b2000320b038654004800081681d114100390600d0802440b4604103405d121001000000c2c200f1505034056509140c400c0c1a5109c0050240d1940e09903c84c061441483c5038003004003101d6440e180025011140c0c940c520201d0100255562600b142e100b03842e00d10142c1d1103500c3c01c000792070340 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 286183579 1250 286182329 286182341
    0x2a121504050d170402131e06080d020304080d08041401060e040c080c13051906030f03080c161205041203170606070b0c0a2708010b0609130f0b040e0c04 67
    0x41c5180989000c00486000e942c0000c3c0035000a00c15030032241c181d40c205102d034100948030004407036070301092805505140000c040900c07401e00c69019903140c0c1c008040c00031043e1130441d0780c00c1014000244194108490002009100b142e1000d076010106076080805d00c0745a01074102c0c602c0c10300080c14a81401c503003014050313009494582c02809411640d884401491101500b8440b01041580f00d06060704140640034144020842c50088000280040b620001c0c09a078029111280181c8915008082a00c0b50103900d0982500303a05000c00000e2031240d0462840c4464604035003016150b80d401070f4084a03403207050f000588807800c964080b9480381810340d0400320480c1c1c5075181001543c1c8440342e400c1c0040c204941c1c2c440219005c2c8540b0b01900b44030104468210100c103141e68507405508a5040740d001c1c0409542c0380c0f025007807581c1130000441e282d4071001081d00c0356444401003000e000c0c100c2910382e07841c440d845d4141c850701910345006a1400c0782c4041c018010001c0d06809101c11910 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 286184829 1250 286183579 286183603
    0x12030702010f0c1205040c05101e2a0c0e1f06020304140f03030c010216061401030819140c010b0f0a03170d090519060c022a12150405 59
    0x8644003c10b0b8140d40c01c1001c01039030030b1200c1c801040a942c3c1d41001c0010214550109420111840b0682101c0368001c03010030582e4140c0210240360310201c101290f240701c840e01060010313001d82000720800c0d242001d041051034411003282901ca0f89800c55020922400d0340e0500004400342081404801c0514401c00076001c68030085091038581003440b08507072109130713030b007030080034580301c054400d440c180102c171781c5151100300075552080418500340c00f101c950442a0740c000c1c80c0c4404283d0403000c1000e100e0480703400c0400e0504101454481710704000d46c07083d8640c00d0082082e4440042c0708040003805202103844000104000042d0502608500184036a48a40455001880020b8209403071000c8040c113102d5443d03c070b07c81040100001d0010b84406080341c480c0400745451080e102c042ca200403486134030709001022190030140e070f40b8500c400000403444001056520064020503208018030002403c04c8034070310540e2900c5080c003004c001c030078458008900c20002441020040042c0805c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 286186079 1250 286184829 286184831
    0x103031b050a230109030509040e010605040204080c01120c0207050108180105010f0f06020105060901140d08031315090201080a0c090b0708031b0304030e0603040609021201051b0702030c09070c0512030702010f 92
    0x417601e0b50300030000e201e103240a6204a90b88d4000b00300f861001d51060001c0c0102410171580c0e1900c90030007542d034982c02c54000380041d401070340d40e80c0485014020484a095290010545942040015582104010080401140800850491800709000300c034020608c581c0041e0580b420701041405070714080d0440030030b680c1401c05110458845059035811180496403003d01d03c243c4600142420305070340740181c50700f035000c0103020b24460109440b0040e18428101c24080c54203a401207800d940351980c010b808074074110000346916403e600071450034134461514252113500c881c54518250070600c1e0543c0d12003400300420920f41e00444060100a50300851681149060340d0001c00001050303010710b006007004004201040752a030080c0f10035541c018102144007507000070b642d009002c00c482a1446401030306d014a51520b6a604444e6496006406060b4884110061040c9144c01924000400071010030020110324140310302200744442004003992402c1c180d40080c25221211040c00c281 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 286187329 1250 286186079 286186091
    0xf1a030d0206010b2802010b0f010c05100e030405030a060506030c0301060f170102160302010f0c05160206030c0f0a0c0611031018110c030c0114040b0103031b050a2301 74
    0x2203a00019002d046541c40488965904c40c42d1017000000c80c114428000b6036080c007980e0840f016010b411071803111074103031502105816050011140107203c800050000e411000f15031941c100079401200c1904a613204603442c0580d9840403a1505803c3c800544074142e942c0c0030710105180610049001c61b108500a211040c1008084a01c0c4005c2e485407980b806854a5181407140d400c6d015142081500707040e414005025040c064040c0159103c101001441c01c02410038982c0541c003550028140310b10040b020440c5075007802499400541f280701640c005103c3c08002d00c0c004001000010703440e5940c078450f1040c620301801529124000b030180503c0500c200810114011a4041201c0224a2008006034400c00042c01040314208500504c4030000708603041c400000003c00d4a585104020006210603031540c00a8a0b07082d60300405401c100d600401c0030078858107028402036600301c0703010080e40b2969950303446c04255800c211440c006e02e03640e40305840d207a00c0901810b212044000d00003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 286188579 1250 286187329 286187353
    0x30b010806030c010813140a0809100215012616150207060c02011b020a03060507090501020a050c10170f10050303120117030915030a061211010e130f1a03 68
    0xd80100601806d6801d81d4101c401d070a10140c400301b01110003000040d01c1d001c290b607040c818041c0e40410203c1d4001d80da100038100c003892000652201107014002c6680080e403c2c00c41043c5007100509030403283d01c08545c0c982151348801d009501442c509903a502041d140b07840f5840500300c40108580c1306640142e1401c000d0290421ba003494070950920309014810500b0050300d80080c0b0030503004c1d4000c50315000c0070080102c0c0e0740c0454011440e94076808401c56070b41004a940710300c40c081c000c1594111070500c0a15051030748061802c1d60307403070400c0a41d03040300c03034091242c1100840307103a02400c0c0700d070081c000c0c203900da904a6006400207070301a618201c3c00e103500c40051003041c418180112014a1150344400307041c07050b18800d5000034000b040340140310903000c015030001e0703611f05030030751510b00b0003d40900e040c00d6480d42da661080845450300005030054590110a01c2402c1e041448140d0700c41e0b25440f10301c11100c600400c0480099600e1120101e0808465007240301e9010350312603080107030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 286189829 1250 286188579 286188587
    0xb0a080a0f141f18051e0c06030405010f061d1605040902160c050904020307140d0204060b070c0e0606040e0405030c01050f181b09040c0312030b010806030c01 70
    0x19105030412490320101c1c000e0700d07250141c00d041e0310b903802282c090200d40b0b0346103841e600819203458840440070700c810031100d00e4442900514280003480b990100100440c0e0011207100c11106080660a544000112001244190b841102c00311000e0b5504c000e0801004420b1080c80041c0c00c03d00b66a102ca00948a1440c10700c4801a003106118034403000f403098800d2148040320003908955205546400d950b102e141c44000040d802221b11008080c00440c4a0a14641640c46aa001070040001c9460044804c601e200c5824006403c604586501c50260303e0728003540000380040c904003a903030080760134460215507064019480080c4120241b140039660b0701c0690b02611710700984502c2d542c80701e01c1c00c1442c610500074001d000c0d500342420860106070b1107103464072a400400c19540300a1440c1403203912004480f42c103131403080008000307000070f00b8840b000e664007074031810403003080ea80c0301d86904605003c0710310303800002034685020499959019005c150000e006030010101c03105800d001030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 286191079 1250 286189829 286189843
    0x10506040506090d12120e010b01080c1612080901050601020f0304060f050702090421030203060a0e074805070e1b12220314090103022b0b0a08 63
    0xd11842c0301041c1401c1c0ca99910621094080d0721903140c5503600c070305003800341c902207070700c0c4038021803d180511440b15120180100c0307440751740503910743c511603540202c950010381059000c203464448401200c2c0000d40081050751a00f491034035003a02a00e4042091400c1d5940141303090f04540140745090704201002041c0d03802e49009040c0049840302102d0200c0d01401190001703940030704008148410302c122041400d2107803a0b01a902c1c54508441300080c2c040c4d00c0305880f00f03608a0641c101c01c0211410310801a0780100880c80c2c02d50000d80210b0b0912a6210060309460b0310041003120102e04000304c440c444c1100103031801c012140701740c0391140d9441e10441e00c0f403181c40145030000650409400c0329070410041001d01d55030386540045005c0491200c1c202c80b0f8034000c0081407840031001c1d1203170703200315003265040d6107119450041e801d09500030341000a005060503000e000034040d412410704082e80342d4542d03101c0a0f107100340880d0801c0c141c0b89a4042d0a0261340740240510070042d01189403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 286192329 1250 286191079 286191089
    0x30415020c1f080c3f0702070605030a0506040f02070506010501110703150c05041d07120908090d0501020c072c01030302100b060d021615060b07020906040216150e030301050604 78
    0x20980702c174078092211040021304409540020204000d8400c05078840d8000b1203452505003100c1201e655280050380c0c1c0706091b008103004288244006200e00003a604541c1d40b0480241000c50041510003407a4243d80207160111190740003400140070559003c8640c102024004000340101441c649540003655032000c181c210494881d50306904c82402402107500505900328001e510010744074182d00b00b90303015100c04002400323000c00c0142401c0d842c01641610754015007014a409865410005071060800c4c0071143d41d5028010043c4043c41400b20100501c04060a0320000141540c0c0000c410901c0c260300040940c03101c010300200b580001d08040d1400c0140e40020605901c1000410340e004012132b44140c14000181a110700045104040704544189611100b2a0030111081d065a040b4002c0800407602480325802619241c824103410003800b0f0001482c11006655103401714100c01030aa90007060b501802110b0107052156562080c80d100c061415541803800050b41d5218501c10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 286193579 1250 286192329 286192351
    0x1d060f01050d0e070503120a18210c0e01090e0c04020c0303130f06020406030b0306130206030c0a0306080106080708060a0e06070c0819030b13050c0a11030415020c1f08 74
    0xc280c9148030030132400c80034200003002c07136a1051007591840820b5001c500a540000d02000d54510121000388402c1e0690390311100d280c1d8412031041079401810074900c1d0948a440781d1040c001a80d0301300010f0680a80384605020074503100d140d00062030103c040407142d026620404c055400b2903000f0081c0c0f6001000e84110181030381c3d0504280006030190f801c05030409100080001f0419015808004003c0e002d5040d85c42543e610f8040c00c007419080e40010750444001c2001078400600f460082500582608000400544421074542100c0454018002c1c3c0c0c3d0101405100c07000f410040c2c0c60740441204004e0041c1e0b400110902d0703e07410041c12802c10310a1049102080009503802c0c2d41c020701070084800042044080020042c01c1c01c00a0580121180000ca680c040d0240c045e85110b000054091031414030104002c490351400b15003540000e0006100c0442d00d088054880c50740152640d006040404d00c0d81d08010b140386580042c0603120f01006402171050307420000c042d6101d100440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 286194829 1250 286193579 286193591
    0x909070f030b09040b1b0417060a1805060a0507110709020a0e060309030712030b09070305040c05180114030307050607081009020403030c020f0102250e0709050306041214041d060f01050d 82
    0x1030a00124061f6400c0441107a0032260503041322080015801c1c0318100e565400c0c401303948010303444101000c440c0e1014199402c07942c001480c40e4110b0b0045a00300f41d0526001d41c1401443c0c1d9103030700304200c542000e040c0b5600040c1034024140c0c05144000c0700c1d0b00c00c4030902c2c514180f1401c541c1d5a480350813801005c256401e60710070403c502035800510b403040081c1610755540384c45040100100022901201c6016420701c012500d8140740900c2c280600c031070400752085909107100703122a00042c1602540c075220402000700094402c2c0580ca00424440e00c42c002241000d0f4150015412541c12802009105000c2080481d6202c5007498091760107980c80c02500c1c841d440103c0c00c00980c2d120840d2034088690500340c035011085243c604968004215030060b071541318084400c641740d8401c06505900c10800314001c18444980051804818140b441104211a14007480307500b05a104503136845054601074008181485a42d9000c0c00407911200054151400601a40108084078152035541e0b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 286196079 1250 286194829 286194871
    0x9190c03021b0102030a06060827070302060708031501020a080405040504020f1507140706140f0d050705070201020d030e0303180a02062811100f020909070f030b09040b 74
    0x2034119100402c40e145000140b65490052501035802662581622440e21400080145c0b00d041818081ca1014a0703540c804010400d05003170489020003526150700501da80040140d562100601e6118450a142ca031680781c11015403444410501c10541590480540b40001902e000112015108100c4000910f9112800410b07072050040d0f41541e00042801c42483c0451101406403208510541445021020a5411640300ca00c0d41c0b140d0346c081030f45030740c11140c6e00ca00f460280a8032a0070782c01290900c100b82c41ca10080e00d0b000e54421020400c0000d160701903507030521114168815904043c0125210228016078a12000f007100c81c0c0e46800711015a1518418481c050b140c540040581f600c8041e805520f103440e00d114400300940400d50010126014001d44580b840030940c0c030054904a000040c0b01e9010300403150b040a10300c0c0d803c03c985000303a5100211140640c2c050b507240440c04000d40d0001d412680c13480c0c03032a8031603490002044000f805254165601c0704103250700c1c0d41c100d0703620 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 286197329 1250 286196079 286196081
    0x5271c0b0c0a0e1302030108011107020904021507051005070f0804051002030c0c10020a08091506040f1404050a020108010803040f09110c030301031a0711060f0615040807030b0609190c03 82
    0x4848080c0e807001d079240710b1028404c1182c0103507050704c5c0c3c0d0380c1c000c0218120b881070349501c1f0b00c07607000d0094120484400080140c82c001c1420090107180e00c84880c030300340d02c651b9842c0c2040c0c002055008199691400e2005055202641003400c081c43d050415250074107481f070668803516001110040d603000400100000190760030f480c0521a030004079403a280c4940c1445010350441d80018000506400000e001000002256001811302e24410aa0b03501d8020600021b00400401f021078103880c3d440e40b4441c0e0804054071803241c1d000d100030b490051054800105101c5c41a800310b884c07a40184800e1110010854a00f411580024000a100ca0140c04c1d4281c01c0d01400038030344c1c0c003404003000000a00c00c15540a00c0d01620904054095a49aa0701030f290307800044805102ca034061000914180c042080858000c00001c1400d21507040422a614160b40560003c03c0107422605081040100310000c26400c100d0490710381c0118504014042c8202c1c80c1340f1121304280f529000390043c0075002e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 286198579 1250 286197329 286197347
    0xc02040b0f060408030301140a12031206180b13150e1e1303020f03040608150d140c0405010806061c060b030304030f0201170415090305271c0b0c0a 65
    0x35002d180c645589122954803a002441065009080c00042c0c0d2002c0c0382400b494000c0e11442c1c07000320b65041041d1400c0f100121860528441c0c20b82e1408003282231342da204626492420541000314690600b14180511111030850f0500c4480c00c02440400d0409440c00340c2d000d5490601490a0990700c00c040c8a409a2202c4a0051b00075503800c144480c01c0c0c800e01e9200350150094085401d0685091251030f075a10482c0309840000303aa030300104031045032105110a03001801003901d02c902c803480c0c031024a40343c0080041400e9034801809440d55080a0140300e004194000107044640380c050003090341082c15214143c0c910094100580400c00d03a81d0008800400190450340c5641d202c0c41c1400700c3c0e000c80f10060b030110ba803054003a501160301c0b041c0144101e52280d54041d24012121124000e414281012801e01800b40400388400500d40c01c46c0d442410a150904121401c45040c081481000a100801061500142d07401b090703108101a07005030107841200c0d0b071a0300700d050890758030b44 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 286199829 1250 286198579 286198609
    0x18050405030405100e0a0609030c2304020306030f12030a15080a02091f0b03041401020a020a08090a120f140a1106030a1103040b0106080907050114031b040f03061103070c02040b 78
    0x8090340207e00c5543c000100015070303200764101043e040c1c90f0000741201001101c0030b688950640180b031051410103030051078000c14064215210008100061410038800003425400c1072000700400040b4949070003610851400501500840c40c146110141c44020311a40a4020b5901c90702083d0400c510f9400701c0d00a0440362031204950b51a849d10001c83c2d80207840c10303141c4400744548103a00c0401842120601c0c20b680e0000c10244036555103008150300200b20701544032150050029041c1101c2c1285010070340301c4c0c00c000703d06008601d0580c0005000d44030b002035a600a00e0302c6d50028000410048071704400b2202c0c02e4590356580b40c4034001d0080020855a100070200910041144a1810f94107a0b03a8030346a040f200c0d568005050b0b42c0d01c9107482802d000070200f11a014441031902d004640200681003040700c20f0705240001d05403030380140d114030540849030400b00240525440390035000e1240300c0741d00380340d0f09104500401134140c680c800b903c681c0d618409105640c0c0c601c491700c01404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 286201079 1250 286199829 286199839
    0x4020304210306031712070c060f020c0105040203100b060f0904021b060609060405070903060509070e090304031407060504031e0204051302091503060414120f0418050405030405100e 80
    0x1071a619001806002c00c0d100844d0309034801d001d040398a14110007607813842140b120395184a5540d403007080f5640311031040c09448095503410800c410000e03500040c029078100100104040c1858414540342503c0c0c0505a204039160055150ba2961b0710001c40f01c102141c01c0c1c000c0c1d10f420b03030b20300001c000b40b0070151000640650107000000000c2e001c145070303200e46421101d914460783c4000510080c0c81c000c03100b44000a034800000c0c0005011640141d400c031058404a40c20240c1719001c1046864007680c80394419800880e0030010030101d04401e903140c2810b0780107440460b00e0940050b105024a001c014620307d400558034070100ba80e00c41c0e01190b20340007803041c000c608100900c0c411000002e0810703030180071090300142108040f000710700340740100034004102036543d94403284505464003510301c501d401142d03841c2d10100c1044010b80050041d403400c0c155210726160815000648030035034282070f603052508003c046240407041d203080ba0f80a90700640c20840c01c02003225a800450304160b404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 286202329 1250 286201079 286201133
    0x80c01050c0f060f0403031a09130804080f151609031e0203011409070b03060907051e03010b13080f0d030507020718090506061801060c031101020318190305040504020304 75
    0x12030b606090501607401b81e14100680d844040f00720109070340180b030940d00300941d6030202c0c0341044004c03142807140c6d00a03c0da4034140798540c180755003080b0540c6503d522561015183c4c3c8030102c0f088210580107154000041144203600d680070b440d0050a11014050418128071100400506050038041c50303801802007018040b603030030000c900c030810f5030200350511664001144455466003142c0c06010000c041c80403580d98100200d58583c0403c403504a83e94030200d40188200c2c1c458007550181040c0c02074542c4920030a4500c5150a0700c0d41e01c000c01d240e100503601c42da070040c045171040d2100980d05d00400c15581d03d24050785040e074940c0c006080c0451008614007610749030350020210901c074030281c41494031603000700031861043c04803d401e030408040c010072200f80500301d44e04001d071107414884a88404080004c1c01c90300b04842902c2c0800c180401032000450070b02501d00c00881544042108000f04c2c0c40090090081e40a814010f0f07038001301203800d1000009510a5250608485890f6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 286203579 1250 286202329 286202341
    0x305010507021b010e060306040203040503070b010e040b0703090b060915150405191d0603071701050612030a090306050a091202030c070b04030b0c160615030c0f080c01050c0f06 78
    0x5902c1d429100c450700f14044585400d8198819440c03481803480040c0304506540350001044001d6101800c00c4415200401c4001d0001d44030000e480e00a00d44100b45400502c0d10381000543c001c0b0040070f003010146481c0c0e41a00045001c040716030002001d65089180d5518555402d125410115001d80c1c0070001d501030140c40f1443c0801002540c0301a10b540070485401d8202c1c00c000401070040e41021000e41c0a070b0801ca43c8100206a405207000301100d82030b55807600c100c04d00d00c0456038045410b035140c030200192070404030a14020b000030b075002945005a03200c0010084005404000c04098450300400c103400d0301a000b005a06400250482c000c1920715400f964903401829800b01d10302075040001000308541080e28100c0c0c0d0050103483d0199500348018400380c2c40002941d0007001d81050b400041203184c403c50900c44409200b850002d402d600b080300180c0b08540c403031011046140c8081c00b503080003040002d940700c004e017409512216903081c5241040000340414149200e54020041 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 286204829 1250 286203579 286203583
    0x3060801060b041701060b09100e0406091a0d11040b01020111031303090b031504090501020d0f06090b0613090905030c1c0e01170103080d1805031b0714010513030501050702 76
    0x82100d8910201004ca034207070341030060a17514580320700c411141080c8552101410004000f8603c0619880c2c0b80d4045096580044d08640490300900e800a86e1200b4103030440100b20700780d4a45000495074002000c0140d036034580d1541280740090b0040c2c0d00c880c000c00b60399000350484640c940e0304d803290076181e29282c1245646400400c030242c0004c2e1030041d001540681441c00c41c0e01550402d00701101484410b8240009020041c1c02191150341c2042085103407a032500c05c0040040c00700d0f001188480c40d08001c0c03400d403069031400350f00c2603a040024594450350019044211807024030081070400c80c5003801c90079400745030045810b6000f2400c05100347d80340e1103c10444900140c40e07a400c0c040d102c0c801156201d01ea500071601048450005102003241f4001405403d0606440400d80e03020b1007540da01e040c0c944840803103a5500104a5140401c20003e68030380301800d520007082d40351f19001840d408110718841080c1440b200060111000d0240b4960f80c1c060b5400c04024405401d041a0082d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 286206079 1250 286204829 286204837
    0x309250b0319060e010b030f071b1a010902091c0201020a021017070c02010c03030e0f011805060a0902090103030f1b110a060513181d100e24060103060801060b 70
    0x4a40b140392800c081000803a140d02281078611500d461030550b9100f001c50791407c0409003c03441401501000305070303000000c4401c200704602c1240c006002e12040400308408440680003181e80e1401404401080e03101e080341a1307030741005850b8181c40d0300d1950006074100008840d000c7e421180402c2c1d050b079000d4100311403804404c42c4031002d045039550036508403880c0702c911000900060001c034103040804d1294000d050f40308008019911110b21100045003141c03044528129003540040c00c03c4144031041c0081a481203901400344034140141e070014518002c140001000d000000002d036403600e05c40e166402002d483d030700e54114100100d00b411440c0c84489600c4621500241c2e00204d016481502655452215079258041c0d981c1801020a0601240c801003e08142d640c0600070048803080c9024a5500440c0e000c0e100d02d410300080b00091b500101a00400f580c8540134031081181e400d20501e41404103400c442c1302c99141d06004030b02a0209038808a0300350300300031007c40e00c512102c0c020 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 286207329 1250 286206079 286206121
    0x717040f140103110708090307171e06010501020c100903020901030b01080c0409120f1b03050310170c010e010e130b130b0a0b1b010c08010311060309250b03 69
    0x15000071414800114180d50700f0b68441800b0b65028095400001d2009000e8658084010305961013151a404540e4801013481000740c0c0341c1e8401c00b00d40310003071410760003d0042d000d220b003d05160340c101030001c0c0d42c4044d0b146040d8029280b0030300401c2c3c0e40e4429401c8502559004003800c01959590801841016082c00742c020203002c0e40300010031900e07040c819204e90660014588a402e80d01c030300280e885040c101134800078420f0401d1a010603071943c10340c0108251094503103d40ba03040010920303407030310000d4200c110301c1c00711500100da03118000030b80000e0300c0400740303045100d401070000100d4544810451040e0000d140340e0141140d80c045411549100310f080e242001229100130b040310588412030f10040d00029842d0041c003580449200901c0d0803000c642000c504011080869421501e007403403100b0001e141703800148200070b0000c0d00d00c98501c2003118914218282802c185494100c00c1c0035102482440d00010a43c01c07004081440c02416003a03074070f503101d1400b03070220764400f03108000c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 286208579 1250 286207329 286207349
    0xe011e11150a140a0b130b040621050c0907050418020f0c07050306060105070c0e0402030f161a04150f0908030406030207060608011104060503070e0a0825080c01050717040f 76
    0x40d030b40c1d8095200700448808024901da12100f480d20340d950003000c0140c21f00c1d4101c3d0721502d0100313880c501c4841c60825000a0302c41c0000e42e0380d040c1001800d10b890704413a184100d4007201132001040d4824181e41c159410340344034042c01075605114000a2080354440d04c5614030114106082c22004610803003100c40580596940f0366035000112001d1040140050240b101f040040c003510b6284200280c0c42403016044500205003200c1481c5071041601040a445209610034400600510140b5100f100140c0711241410700b080e003040c0b4082d04103004030080003d0b003499a51031510a071202d0004121820030340c1d5441d80c0fa114014041e500400301601c40701d040400001d51010144102d926001c81414a00e0605003001c1003280d0300d600207045a0208800807000701100c0d80e407015903030001c103c241d0041c500038003003441c181c3e50b002d040d400d80c0d4181c81d4400d20801c0980030101e21912003550074601503581c1c40b002d00d03285c50100c150188030414030901260102c0e1a2082d04c45e0f410541c0c03400e5003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 286209829 1250 286208579 286208581
    0x8030a02071403100f02090622050913030c020307171b18040210030f0213060305162a0602030a051b0304080403030305060301200a0e011e11150a14 65
    0xc070b021000552003509401d0340c0040c014400c0c6030300a902001e60000b40f0700004d490301400a00007000381d0080450080c0d464203403088441d0710052100142c1c01810255244000c40c540101281004903c1120240500a01c107c40324210359090204170090000c1c141003034003071100498101e0f980d615241d03150040c0b42d0484802022450503410020364440041c4600c110380e03031940d090104200058940030305140d201c1040105026850000c0d1003000e19041000503400c0c900b0340000c040e55030183c00c494031034014095000c45075600c21300810202a4150590074034110781000044040e4140501a18071407000c41440007000c480d4011074021280c00280d805a015138034410020383c401600d00402d0031008010400c0064080d801c0300794841d4005000040460030382d1512003180c0b40490905240703000008007002e4581e044100001002c0c020300c0c01d0800001c66030151552200d50026400a111a14000080c0c000c020010309940226040c02c002c00390030301103500e6000d440d0207803405c0400e22941e4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 286211079 1250 286209829 286209839
    0x5220e060a0e060c1b070306020c0a0611270d0501020d090309150e011d030d02010605041b0804060b0a080f0708061e06010c0519080d060501030c080415090c08030a0207 74
    0x61068040d030314100816150171340d02000c1d401d0200207940c610311140610100000403c1c13182c40501100030380d10f809425660200d18080003142c082c941121007210f8180070b2450030324242c186c030290a0302030000c4685000904c20000b0080e003140d8000a207503600004583c1c0d0b400c040d40e041400d80503c20380365030300040d44801c008400f4009105907000000c9500c41000c00d43c0d0f126500240c1e040d265000348408501c1c0c042c4c00700707051002e800080350140c2c0d1144010041420544110103100501e80203030b569104140320000c01c9a84040d201402d03040e00d072408a00740340c0d81d0004c510300030030440d400c840c009584030001300d403600c038144982c42007401243c2c001503504d000103442e1a010780b201e0308040350300d5a03180010350340c861034950280c071540300d0b520040d020145101240707020b4600914242d0345440319100407400783c030b210b038000c039040504048180801c2c50f0040103c5811580c4811281c0700c080707034105090000c10149001070281c1b100c0f0a80069003500c08001400520104d80c203990f402c6071a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 286212329 1250 286211079 286211083
    0xc130b03060f060d030810030b01030317011e091a0904030f03050703020a090608070311031503070f080601050d14031b0f0718090302030d060b0c0d09060905220e060a0e 74
    0x1101c443d600200801520000684a000030541c4000c154050740b9065450752104074070030380240c008901040c40c080c101d1035400404405607004000300b14009008210700d01c1400c0541c0500d105103c02c650700d031440c010301c04815004d6a8000d001c061701101ca10301d41420010071110104030000c1c0480c1c44d09000c00d880c14824003c80e48907180c43d0b01e40d0f4424602d400b10850310940002c0004040642d40c660030795000944000460050345c200f02c1c1c0c490b420848008041c104880d507881080c0200801d04100704000c0003140580c11074400300c540f1900140c8a040c8490b03105440340c9440d14901000400103e40206600074122404500c41242c9511004030131880d0b840d21140202610f800041c58a500e22110315040324032007038841d106032810f0508a484410a40d2040d4001c0f542d02800860403e410580170050018011180e141880600d4a40840035100054074029940074203612100038111105c2e00c3c0d02ca12214107194010001c181d5a005c0070f5480300e03020303a172100c10241407902d491442000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 286213579 1250 286212329 286212331
    0x702011b050a0b0c12011415040e0c210405031209060403021027080304020111120a0302091203130e09011a092503020d06060305150d03020c130b03060f 67
    0x7000d030050840500c507403208001001c0007003460a40040401051040c1c08034400c0140c0240420303e0040465801101004100c5201c60182c801d50001484104443c00c0c910020a80207200c1c59901903840d03e18107001d55103a0350440b40c0c070071010101da050004210303000000346014030707247c1c8202c00309444030b45159444510a860280059011001081045100e0340c810945200c801c604400c100843c1c19410300080310283e02a02c0082e00481000290358001c140c007102c08034190090566121600b008207601d004d00d58a100805a000c0b48001260722200c1d104400c410260040780c5e10354484c00c0500403248041d00600180d00203480110f1282d19050013510380800d00303840c06001654070b210903c4200400208071007901140d5540d2100300c00740005201d12100c0542d3b902503075810300900b6400949243c3d0740072a0406151600b00304042203104203842049000311003003081d8421a0501f2803401c2e0750b0510640d4408042d244c409020301e910750100014101c150191b031002e41da0707085c1c03968540c80 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 286214829 1250 286213579 286213583
    0x90c0403080a030c090f080f0d0804021503100e180705040614010e0a1d0718050907050c1002030709050415060509060a0224010503011b0f11011b050702011b 69
    0x105002c08249140a03400481d0001042c1c40c0050350350b03550340140030446070341e40d1040004e60000000c0b200c00240511000d02c0c041c0d03c2d400e0500c01420540d000c01c2851030f02e0300844214480210209503d1001d000c4024004e00945850301001d040503111508050254070051400b4071421b0300000c2c082c1032030301403001101d00b6450036021f00c6440b0001501c3c03807000c44050701d078030134100f840102d124030441501c0c2d84408e200840c0042d491400705009401e00301103040034001000c11180400a50b90b60010160f8450703440c2c40d109803100c0260903001d182c01c200c45003101e1003a0021082285565008204901301c0750704039803e00000c203030880303001c0801c0c90741d001d4100054401c00420640342040002086c00e18170030300c125024800fa801c00314038000240d410300c50f0f10208902c0100900e01e82401108084c07046000000c00d060500440038140080c1001c0320320501403542c0072146d900c04207512000c5180024440b600c1384041c6e000b0001d1066119000c202d01081120130b80d9080d0a0701215490726980d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 286216079 1250 286214829 286214843
    0xc0e130506060d0f06020d0b12031c091a04030f020d1d01050901050c010c080a0507020c1e0f0a0f0f170c010c0f061a120102070305040302090c1303030e090c0403 71
    0x140b6540244030145003150015a00c0c60340d14400000003442520003001024050480040c00300c407035000b04001054180250907950b8030a01a41810406114603000c11401c0d844001403455541e241001d234444054000700700e00319120040209054112031605a8107204e50700b0b6518503c07003150150350017000e80101c100f904044035218032042d40610000c1c0f40303400301410001e00f07000c080032590342075a00e0203280c2c60000b458030060003195800d0b40985c980201003400640121003548012402c50b103d42c540e440591103450300111031507164400014000c0c04081e00060a150700d405100b80b00c0001da00c1043c03e8154402d03000110383e075070340c440070280810300c8016012030844040110b41c55403100e007054480c07110301c001250005909100b0000c0080300c1c01c00c1035991460440801c200300441d6180184140d0042103450002684102142c0540340c1c1146d41e4041620b0308200741c441c500444184506c440d400171001300902d500503040c0859420700b12450003442e5200002407515009a12001b0070310 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 286217329 1250 286216079 286216081
    0x9010f06080601120c2301120209060d050c0f04030b0402120106030812090c040603050c04050a060b0f030c1b0312010803070201050a03022d0c06060a031109040501020906070c0e130506 81
    0x140e03001c04e01c0c0c42c02c45070080d0044444191550700541e00841172580050309484022454405560000c4419600c1f43c2d800408608201c903040c0401c0c03442c0325400c2e03014001640e8a001910464692040e2400b80c031401d41000d0b01ea90300d17880c01129000f1309072410f034441d00c0901c0740c2031000c4005004e601c0990740d0102c040c0e4140411841070221080d00541521198050226918140d403144d20803080203500130030080641ca071a80091004a4001a044001d001e04003007051201c0707135001d03040391210086920269070326650071624005a0003144800000e080c11400714842c850800409001c84010300b60004034240d076100b100c41e550340714200d00240819030500446400c075019502504006284075440318101d200071009140502011607054203081c00401d405070044020082c0b103903c03c0c001d90b880710445096450700c900c0701c444444064800c110410014082201c00c0d0144c4a4031100034184030b03100c221034035003122000c1e41d6000d000d0000c803402001900807082403116681543c2c0010180100b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 286218579 1250 286217329 286217339
    0x30303200403081620130c0212070c0306050a050f0c04120312140c04170106080a12120e03030f0a0c0c17070206070605090105130309090b0109030209040b09010f06080601 75
    0x2080e08082180e44a0740c00240d00100030510b0208052100d42252400b00c2d081704001c02009890165411550802864005201c0c0890b40018030420105011410543c8403030340c600d40f490642006070002802d043c203000900200d02e0380307600403500030140020140c420782d40301c440080c41030040344146d01c401e89005101202003801203100140361141000c0c0070440c0759120410098403a010340719000b081000007410015800c000920054464840300240a030911b4100c0c00c80c0c0c0e62186400152004d45c140c29040b44060007004d00034684285031006105804909550507261b0304112424021300000500044e00441d6a1089804200b0991504014000c06d070f104c845001c91002c02d2840320000801203207001d0381c0c0e0500941000340c4644000700741440c080225500b924809000048032080c588515000283c020680d0f206503944030303038001013410303240d401281c0c07034078081c1d102a4011800000388000e0144545101e84076013400c600901840190061140403689548a08135854202c9001881 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 286219829 1250 286218579 286218593
    0xb0304080301030f140613030f020c06030c28090e01050f06160507120f060606020303160806060d02120402030606120714150a11060606070b22060203090106030303200403 75
    0x1a52401070302120414405e40d00b0309480c0c541c0c15646404e60248401c8010200b55011140c011250858406403598040b10000300c0c040f400090300040c3d11010216070454151040380031940172108280f10600180f02021004e403e25009000d010809910305002103100d0401080c1d9412142000c1d118038503000030340403024810041042c048032a8010520b0004420600d4100048032134000d15450000480e03602e00300c800c6841552100d02990020300802003042c11101400390307400d2443c2000d0310907a640c040024068480c030f1614192040c40414040c1c006e00c40300040e01d104600c29001c9540366180c0c8001c000176070701c946140d02d10301d90046a0602c1421040321807410000c4000e401241e00088064242d24160854400c00c0002000800502c5c0700b00c000f0004503800140c140c030424038101064032014540c9100030511260410764050354180c020500d002e082100d500845c4c00c40d01c82c00c1001e00303180601050710058001a051004514001919420607600780416041092601d451070755000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 286221079 1250 286219829 286219853
    0x91a0603041101030b06341101081f03060c02160513020a0e150c120f030f072309030c01050c030a0c0c08100204060311120615130e040c0b030408030103 67
    0x2c2e0415444140109043e243d01c40136082c2441060b03000c2005c40c1b03160458981801a1041138030300b0100c010421404034a8500c248210000c0a00c1d010240b0780c0d822060780002c8a421043c07000e140341483c0d000080c80910f92200c80000519030903500350032a0a2148000c0303c0090290344d0740060341001035100307950b441d40189001e40f101d04000340481808030000d402108070080d07a010140f00098501001d500600c0740403104141c2d0702d0302c41c0c2400c1c00d41092070241c4c080100440034008410b408510107502562980c0282500c0c43c2d055180501720340c0d8160040d03081280ca4500a200d80da00128a40d8020015204400764000003141850380070b54086440d1103007080242d0304902803010110f40c40c00c040c05000400950580056626440d240005048540c1d81440c0504458244500902241c60018042e084102240c0405102e00300340d00540c0703188980d1703002004080d2540320028040ca440040203220b80c2c001d08178903001540d5914003185505c000c41d00148264010001400021a80c5100c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 286222329 1250 286221079 286221113
    0x105030a0e010905070914040804050f010912050d090501390f0b06090708090a060e0c0a060c05060603010e031210030602070303050411040e10090822091a060304 71
    0x218071040010401400c42d010002c0588450300508814440d00c03500340260b4116803460b1030705030060318040c0c5581f040f0740101d004217032060304540c1c502010f5a00c5080c001000d4610450800c461100c640b92156440c41243c5011010030038040d00060b1944c0240d1003052000303500d00c100345a0b1422a02ca03200b0403603501168603070216228211002090300c140d03540d0407043c8500c00b4801c8608020040080c803410091002040040d100101701142001061407400c9a81c00700d0041035480c4400ca036142845551004a500030501c1c000c0044c00d1503002c0e104145280c01002640c095807580010b15003a01d941c6c4401c01c0c000d0f03108000c11806080140c0070164883c8820790203041198403542c4490999004490940001c2d0304c47d0706000038041440407020301c00900710303400c008103d0a10b82c10760301c07100c0752145002601d65441c1c1e60424482e44601b19020750b40a004c1c0e1001c00c40d210404140340160030300491029626000c0209402c0003a07280c0001858002003c55080d079036141d4440c0d504001013460 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 286223579 1250 286222329 286222331
    0x203040b0a180f1e08060106120b01030915020715050903160c03060906021903200f07150c02100b090408030a0e0706051b0313032a030501051006020c0108060105030a 73
    0x4001803844405000030007506180c2c02a014482035107004c2c1c100340405402c0800c16412030780041210b15042041420724080303094001c161a8217840041c0c0080401c0380000e8039501019031030742d040c0003280d40141100303803080c0403281c2000d60503800b00c02110030403503a40381568000c00c94912110130707c6a400c00742c148100010b0140315140c3d50341c40f050b0740d410b610468203540c000c10b049618038060300d188074000800d03190804c10b4000d80d80e124110030121101003000441c000a0184100d03d40c6401c46628541150902c14556409650714000700040200304c0014040d00501c04501c003000d000711207200200504132a03080e281c944500541d5803003d04044a6951b60f0801401b034804203000c1c420082109841e1a6100e140000d01c0300d442c203041d5005170480e501300b0050951814411801ca000ba00d0304103090340c101e002c082c5605a41062004003034551224180c20000410905402092050003000e11130401160741c0c500603070399980000d052030301048410740002c800c1d51007580070f980d125000c3e0364 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 286224829 1250 286223579 286223627
    0x1506171b04080f100b10020d031d1506010314040b07080601031e0e070911040b211003060b04020910031a0406030b06040608030f0d0e0a1505040606060203040b0a 71
    0x1101500e444103583e10000c094000d20f00d20303401284184a8540c494205440e07004401d694640000d4035400f41f01100c3d418103644928042c21729051481e01a0b034949014222103114410280d014810f020448005000030f050080d200780d80d090400c625406958091201509911068410340d4100c00040049041503660b01ca8803c0da81d4500070f4010310208181000610364060020850810036107802200d41542030604c0383c2d4521030380c4000c131012070301c040f001c482e00c1d1082d11440c04075110044820030350004002c0d040c01854020352101d44116071161904102d206d4401090200ba4020004070503400001140307a00c1c65140290064600c3d100c401a031980100550400a03007140c1c856081038610003440c80030030070b8030308051241c0000350980708000c50421010480491092284884002e103454135858401180181005000a4640c0c45803d0003010440140c2c924020081207a00f40c070040c1c00c0000c0003450324004005c8509540102c082c0f189040c4000e002030394011040d0400384401c1061079 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 286226079 1250 286224829 286224839
    0xc07050a1403120f1005031b0f03030c03040b1201090911040915020d1e090c030305220905040516050604090207020f040c0c031e080403030c050d0f1506171b04 70
    0xc0c9030340f803040d180701d44400f4250500703605e0100d40600b19088903000ba07020645a0250700a40c60301106014800c50754050f04540301c20110b0300b54014940842600d110104000c10341040d4100600355400b04811010b00b01daa035018000d09844007018080e106204c0c0c0040d000c0c01e401e00380c02041a1600401d8042580200da96080c4100c2c1d01c600c441104207540e4000090310f001803075540e101c291011260078464460301d512030298102e000d210040a004000a09549505000c039841d03030002c4280c5203c81e0915501c00d403440140c0b10403a000c88550080c03020340184440d4102d82031007911400780c00d481c1024244425040290300042c0140d0340104449180b28440d5614010525410342c03940e1100b94048103031402a0403d02c001100308030f00182e80c0040808550b00a050b10390080e010b180c007245141c15003600381d66610480d85440c444c03501b49484400c036030a1507003004141200e040030060b900d50317403240b0884040d00c101d00c00c9200c11407501d001c904a0017000d00541c0c4400009251146815036803 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 286227329 1250 286226079 286226107
    0x15120c18070c140d0306050111030316020a0803010602011512030e040b030106080f1e03031504050a020c0a2a05060f0a091805060a0b0c10090507050d0305120c07050a1403 75
    0x1040b01c3d4190784400052032034241d01d4001d000042100b820031070765000008101c1600c84c0001020501041c424802d042c190502c200b01c0344008a400c19241e41d520758649500038060b20b06045a92408034103d40006012501d00545815150301680e0750150b841c0340a04100c0a0403044c028980d041d900c4510114241000b400145028040d040041558041041c40005030010300d24210203075410a108103c48521141c648400f2034904560000b920341d10601c0c014000e00840b10094200d204003940d80d020000c1010021180880328001121494510414201c0c150518003503943c11140510075020050300101c00f81440da140c07410940200d036151002d000401d405900640181b54884041c05a03900301f5140e1600070300103104540340340c510307480141070f03640080134014070034640d840e0041000e111081c0f03c1d0001812005044c40040c1d81f040c18001c0203600300001008140c5140c0020440b540302e4441101c04460b231110103010443c2070b644411050490398400c480f81d03400108920f400c0d21040e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 286228579 1250 286227329 286227353
    0x3190e0f0f060d0c081501090f12170a050705060609091209031c0f030c0e18091e100f0903020606100e03060a0207030e032b050705030315120c18070c 66
    0x100d990f6005c0b242c81e01d4680c04010b0500440d040e410300c030aa15050000d0307103411350f07088140c1d0294031801100200314603154075085000300040c040c4200104050300380940c020010110700b80030b1822100143c86510800545041c19502c140c1c46601110b6005050900c84c00a82213020005064030042c04440b038144104a598803807400005803640d2803111200c0d0144111280910030746024500c520048001c540f0301c001a00d00000d1114000b4005000c800080200d6101c401003070035540342d227520300c00d0000e541c0c41080921861281c20550003c444005034403484038040d030564001d0003280c41d1502803280130a05ca031036443c208400da410300e182d9501c04209843c0510040e01703005a40c2e80060a0040010b126116507610980040781000f40c10204c0303000300c0029000c0410f10030101c03101c5500540300c510407804001c040e80008401c1203080448402c40141ea101c0603111401108952025140c881381420b076004c0d4043c41500301c0307000300a07102d50328070781c065514149010313001407584420f856044 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 286229829 1250 286228579 286228601
    0xf06032406040e0105010f0507031407081c0c110303100306020a0c060513170a0804030e01030209030a0c05121f0c0c05060907030302010c02010b0a05040f06030206070503190e0f0f060d 81
    0x600c00f004104a590043c80900a0760052400906041792550010082c8440d8104a00560004569130081c0038407503041300e03010030b2090186004a4910105000580b000590b040c01180325000044c0c1c0039140481140c5c4a001600c3c2d0070300c6518110354803900290000c8403090100015400c0b844002007082c41941d01852401d0b4010800c08210718220182300095149d003241844207101d514042a00600907540060781424419490101280100d00900414160079418800d02120401b4880002c082c0b1041d1041a100c40115080340250955105200c09824a02940028071200701360241d6100a084140f5482c0c41c01822103d502c40324940403094030744100301c1c0c0004c2002c0041503024030901c51004c08a0000380204041100090180c0c0c034140300711801a0380700c40d02a0084502a802000a0750b4000e009035200c10f040c0c24401e5494118142228500ea0883c82d10b84800d070060b51403041d00100207082e40c2c0001081c2040c8654030041004164000c2000d0080750312810881c040d13104920 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 286231079 1250 286229829 286229849
    0x6030503070c05031b210f010216060c05030103080f09040b0406080d17010503030427090f0309140609120c030102030c070c0f05010906110f1902040b0f0603240604 72
    0x39040c43c0c03c2500340b4a20a0380b0301100603030b00914400644807980c0307080000807101025410a44842010350420322a815010f509500c00100d180b642ca50010002528a000d45420001c050b02e054080d07402c0d1000380030160030100c00340311440075a503064008214a9201400125841c107140340400c00352a01c0b500301d40b0040d00300c060542d5000b5400b102109a06001c40c400c01220b5242034082500c0f48078500039010f181c000d600400c507045102041507030380411088002c01005070941002d845102d0611822000540b205000284201c00d5605c0c061220724000c001c0d515040c01d09040001d2400d41f0b0b42504214024801040402c1c2c0c2c084c8055881092064201a9254081e00e400403a4448540001c0501c8194110030701c8241d80c8001e19605071141400d0041c0414014022203203030004641180a8511810808601030300b140503440a0ba0f034400c0c1c80502c00000440100b1020f00701301e6100c0c44d0041c4092000401c0101030070020100f030324141c618810402065000b180d8a07910070b4200110803 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 286232329 1250 286231079 286231103
    0x6120b011e03080d0e010e060c0c0d14030114041b121401080a0303020313050a03170109020304110913020901080105060901120b0604110d020a09090b0402040b0415030603050307 78
    0x1440c000351007500c075001e21205101c9400e507070b070303001c4140201d001c035032080c0344e4a80900c1030f83c000c02d502030b0030410007210480d0f079070f85810303104155650303c000c0c2c80400c14000c00f003483c100c407801804495031030500d28440358110380c01c0100200705078203d401c2036a4000d031224003020303071105c4138505460b0010035560355144d1800185d226006440c104082211044c202c40010000ca80703005c030f52251b030f1941c949009a0383e520350014006404860000213803032401450208010550009044890f03000314820342902070781d0307860340c540481c001201c1c0070700081001c40d088483e910713019420036070140082d501c09482071050780100e4001d401c03d0b0011100c7d40c0d50f6506000d0240703861050940108001229440003920341c2d03683d094481c0010b40f840c3c1c02140c40326a008011000391054070494a10004210340b2080c0750130000740014860710030010020b25050f2402c00f1030074140220360584091108062600d890842c102d16440c022440700300800d40c1d9202c012002690500040030401d00640300307240c0d8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 286233579 1250 286232329 286232339
    0xb070309050f031e0702030705030601090903030506220e030c0a03051206030d0c080a0320070b010f050d110307050d0b0103110613090c02280302120a08010b0d06120b01 74
    0x80c046210803044a20350052010000c0e02c0c4c40003040c2c050700050200510744511443c404130703203000110340025030f25004007400803a50b010347d94000013880340281d40610607a10343c007040c421000341c40000f014a58081001c3d4000007480758201644107140c0c00201c81c5007a054000c1241402c01001d011000150000358401ca10800c0314021508000100d001d40101c440011028000078030801c801000c81c003001c9510040d80703019500907203d0b804c03408211801c10001c0028845150b00810040380e205003050004500184031118080690350060510003450b4030944840481104c017142c2d490741845683c20218298440901d5410340038490706e50002d03d075044d03190015483c0b400a0031075000791400d01c51410301d81c0440755090201c07080c0160004120340300800490820380c0b0503100d18040c400c402c104680300c9600290380701d80e107070190307080e90018a0000c010035032900c11000318000085101d801488410361407801403140130130440340010324a03a540b0701f1004103007030807400359414146a001005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 286234829 1250 286233579 286233583
    0x12200f09190f06170f070c1514181f20040305031c1a1c0204140a0b06031017030712021b01030207150209060408031b010b0118150c0b07030905 63
    0x649022a001445071501881c0c0a0319100c00901180030800c150714030b10244880081c41340c415023000c0405008a14400b41154003040f0148c6400d010508000c03034060070118042400ca210149950303514090800e5a41240c0c0602000c0111242102c1003001100c0a0400d07100200000c510920113951038009004500e000c1c16840090318045a00700403906458410003d000446044e0450300301c1c0e841140300309840c00c102c0079403400075006894030301008490341403c92118810158564107001c1c0c811020f06110302c030b000584d103d0604821800b01484401e4417100c3d912810f20041d004c82c0d0501c0c600b40c0f68489011800741c01030300543c10000c00b40790f4094a01d482405107440c2824258600000b5039030300c100740100000108081e55003c40c1001055a0314021280204541800c4949403012910041032109113000c19801d030750300e0050241c0c00355000c0d182c4003a0350754022000440c0039150003090100d10005100c40e000b00900030781c102c00010901c400c1c4c240101600da5001940040070b02d001746c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 286236079 1250 286234829 286234847
    0x1a090a140306071b150222050a050a0302060f1b060c040302100903050a15020c0d02070510110d0e01210516030e0309010c050f03070312200f09190f06 66
    0x80402600f160500d0060f24002041c401c0d25511061483d03a007184070204800a014036115004415483e240047d04c400e01303075081c6070680740e0485034456401d40d10300c1048145103503071000035001601807210b00102d00392580075120340200412a01c9084006408150600508986014101d0310104040c02503007450007000045040c2401d20144850551702c0f003a0352640c480300020240140803094000c090b420360180e4413981002411100e880320302400181d22a0203d0182c940a2280d03c030041821034400c2c000890886c080c18050807803c0352101c0704503029031070021000c1c1440405403000e21411603810080c407580000c2c02000400c0e041c0311070b03160126544004403408040c284001d8402c80394010088404d5003009081404d0840b45510748181000280244a00c031808040740080c01c0c5034202c4011032080301040000c002c5407001c980c0d04080e04001640d0402d1481050016284019202e801049000d03c000c00c0da0344241c4082c44e00b00c0400b845038208010340c40b6000010026140c000b0191 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 286237329 1250 286236079 286236091
    0x20603041a01091e09170a030609050603010b06040b1312081c050402280b03090106050109120b220606060f02010f02070f0f0309360c0206011a090a140306 68
    0x901003041240300c000940b0705030050024000395920241806c202010391815040001c800c4115101c800c03a0401500034901341c81151002410800020100d2806109222000000420180c18035080c09040c440580045550340004e0004440c04111040c43c3d5041f4004079200b190050303684c02848400d0088c41044800d0380c0c41243c10002840016a5205180812500c2e003c42c5803224003c0c03410554203028040d030000c50100360000920003807490640000302510001c0c0c0381e0075a1680d449040380d04041a04d540130b000281c001011a0359140715014860416803460780348446104952070781001c031201a131042d40400c10401d0010b846131303028040c8980310705228004504200741c0740c880480780300e9524001010000c8030035100003054081c0750104080c0c0380f01e6100500d0044ac0c0d0210010081000728005143c1c3d44071031060500d280323640a01751303000c0502d6014001591810343c0420750328410741c0310b800c00c000c402e124910350341c2c0364406110010800140c070716100103c108145030400d0b00107810 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 286238579 1250 286237329 286237331
    0x17091e100e1c051e090d020402030405030301050f1002121b030a0207090f2c030c06010e0105090f191e0c031a030705010221070b070e10020601150e0d020603041a0109 73
    0x140700401504d450004000ca01c011001d1552030564100142800a00050096105202109000600c030000000e5816200c00b60f41c1c0c00a450020340800c03644d45901c2e0142c0c401030b488030a060b0749801000000e0211020541c0144202d455501e00050954111528000041e44449420041d10020780103001d100110080100820449140c8480300d010f01c10141d01c40600f142060506e00b82c40801c126040681040700b62012540c698541c0c1644131020f00c504c81c8100002404a08000070200c4d426000d40c00c039030308081c0d202e1640e400c0d40e005880700741c400341800c040b00c4e8800381c9840701c030780103445101d109680c0c0095802d9827240f145826507002464a8081c0d0b1080d0000c1c0076690f00010700303040911a010000003003103c10004141d181c4201c074070040c40300c0f0100303052002c0c131a00328102200d420b0048595103d62000e85600300c0e5540d1091041e400d024098409035903005000f00303070b840c800308000741c4140c88850142e0046940c90f07209507002c540b0a130340810341c4030380c4240b424401c5000d4003a00c20 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 286239829 1250 286238579 286238587
    0x3070b010911090402130f080703060f02030f0402010c0f06020c0d0206160807181203050c060a05100b0901090b1b120310050f0f0301090303050717091e100e1c05 71
    0x50700315503000d00100d01d401545d0001d0403900700f1640c064508000c26200d1084124652034621032503c90f135176484101d0710383d82803c9d0160b060304898000e1341d12440080c50400030784d0303a0780e40044850302c102c00380c15608000204407910104065000900c10043d552004007184841120001d01e00075001f00a0000d032042c180101005543c00003490303811501703d1030038044e004802c2c02e106501040310740c0103400440d004001c9008040c0c1000291008402d1001510b501c3d0392400124000c3d5030049075000107d61030440e00780b1034001c2100c09049100d4046c54094446074481200c40c0880c0d102603003400d810070b5080c2c617030b174000041002040100c029915440b410360030425200d1000c4050f40c050b03984140504407030150607440300a1442070148004001384604d0149080c09402000c0980700c00b000565001e00708240105140c58040c001c8016400034210940b14107454441000721300c0e0040d25078000c203500d0800f0308501c0d0007030462895900019004130070005096a044240c0428103030b05200d0144 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 286241079 1250 286239829 286239851
    0x6020c01020606060304060b0109180b090f0907090218060d14070f050f0708160615051c021017010308040518070e13150308090a090b090a240803070b0109 68
    0x1e0360340095007c030b404a15450305da0016114008035070002e100c00c140032240e03002d49070410781110010040035036003669240c4801000c00c0c0c21000484000c42503902c403540070004c14580c1c0d4024168107450140400ca1b071032a138000170312541c3c082130f0401c0c0320340d440e400c51401294804841c66040341c058204603810040c0c4a401504a002d0036601c034040345408a41c12042c0011881120082c0390b0700200760034051401e01c0c2840080503440c4c200c00c0305080091010a25090003602d4440d440007011103026000c11650070807410850840303c540c10041c02407101a40f2681d0341c1ca80038080d40c412420700b500d40303050400340106a051040c030300c4503802c40d000c02d2124440d00010350924504e41529030b8814009111b04610190565411410142e402c20b80000309001d01c540142000c1c1100311600d2007001d544034501d1080d22102d8506640c490f2120020031842c071442c0d0f000441c1c03145043e0141c1d00c107004001d01c1801814059201f07080e03903000000d54000b000100902c1e02d000d0f0110b5942080b9405100c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 286242329 1250 286241079 286241089
    0x6040f0e1b0d021809011b020a080304150212010614071703130804270b0312030901090b04080a0e01030e120703020f030d0c1814040f0b1906020c01020606 68
    0x41c0c1c0c02081c1c1c120090080030380c141c0750300d12030110098000d0128000419404081d2940000881d03100301c665103048802400305405036050341c42d14000d5402003400f0002515680019400680220350208052400d01164845400a0b124101070b59408400c29803600da005042e02c0322048510344d40860400040c00021403411402108201090102e40c50340d540d401012001800e00e400a06000d9002c500000c88071307500080c180990414000c21030f500c902d000d00040507500072040705685a0441e0500c11940103201e005154000c0046002003550040d54071580c06241003611300b41c0b10040c0000700e454105802510380d0349403440c28030f010000d00c4503c0800300d0b00e50180201e601c02800b4005482070038141308001c054258110b660903255074034806c240e0000100b40c0c0b000144003251b420382c07080d4480b030850b07038041044581d900d1120030601d09000400008010a8144541d01c0b40e54003d40411502c8048548211104480c2e841c0400760902901900e007610701402a8115840941000910303118 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 286243579 1250 286242329 286242343
    0x50f13020a0b0a030902181906031e050313090b04050609160e0a09050f0a0c050a02030702010f03023901112d030703060f06111903021608010506040f0e 67
    0x408954140c0f54003c088085010748150180a588540201204101d8006900402c3d004800b2400401c9445401d4145602590a14803019018001c4d0380302c02d0110740c026001101045110b1402d60745440a20080441e003005142c01c98071b192540c460360400d4a003030910030107400c040c040780c1d000740302e01c0d1003032050b00e10040c22240321041101c0541488001d44940701c102015203485401840315180801e002c0c00014421611004420b003880348843c00c007401801103070404102c0f40d0241d450401c003900151841d003070100c541802c0581c200f0103031515a80300c12500c500030042c24680326040c0d4244240d503071000322041140c0040c1c0d2402e54902440720140c41160a407801010541d15040b141c1004c000104800180701c1c2c06000f00001000f0000c3d9069108201f91104a410200c01a842e15002c958106194910300440d41c003070030382904d0404142c51550f030207038400c0c81142c11181441c88034a85048407a440b4080503074496080c0211840d090144100103941550300300400041c084000d1303134880d5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 286244829 1250 286243579 286243589
    0x60f12080d110903100e0c010309020a0e061305010801020d06051f0e0a080706020f0706021203040206030a0e0106150806040203070512040501020f031003110d21020f0a0501050f13020a 81
    0x40c0d501d0344070b4900c8106900381c820384200241603598113008101e5042c0640380c415003410050060788035511540d030192056015103034001c0e08103403a050400102c8015404040d1100b9402640150003242c01c004500540c0d010381084400540c40c0c01040c1e01c10310656100707400482c49851030244009070a500c0c0701d5040c400c41d0a03450503126614000000c00c07098030f2190031aa00501078044041820381d000246a1003c030384410450340075a640d140c0403602c40b201c441d14071135008402c202040240ca40200959000060620000781c40034000c230f011803c55600c2ea20a0301606860a807844540307030400394180d8000015101076141d0b10707111100500521500700051010355035400480c05020007541541c000d0b5840070b140035505e0414070781c000c68040052100f120103040300c242442c164201400c020681a901c1040030f2103203140e13008035500080001034401d0441c402c061a035003210000300108070545001700c0000071142031400501d9180200240110794141c05550071100586503140b400003114 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 286246079 1250 286244829 286244831
    0x1d0a0b0f070218070206100b0301030b040803090f0a051c090e0c16080f180f0102100e0c330403030e0105180622120201091406090a09060f12080d 64
    0x71880748001442d5400c0300883d0400c4030845410841c5203500019940e006100c40101524800e5403820301d416144800d0100410040440010030300044405006d1504506a0002c0d80c03142300c40c020341585040141c8400341c802d54010b4282020011010001080c5040545015035289041103516101540080c0c12042002c4c0c001510792041680202a00c0c24aa03006802da5907501840380c0110300e9030400c542044c0390203080c046002c51840d05405580351580b068015101201c3e0700d41a207402040b08007000b074407a0091350403844a079640c428620310700004140401804050742003501100d580f1800d00454001c0c0c0c10402403000ca50010070440703a81c0000d01c0c0c040d0b9900d001d0741c0c9403540e134500140c03c1c50f00000d0204029043d0103000242c60034040c0000700c1c80f08000d40e1400386281402442c0c2000c0d0205000355028041003a1384250441c04080141400340b400744148042018025954045000c5a650310300612242c212640e0500c000c0c6180414000254070356203130103440b482b45141201ea02 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 286247329 1250 286246079 286246087
    0x610020d1b050a0c0801090507210b0402040e030703021e070b0d1104170a050d08010605090607020604030210080106031a0108150a030632011d090a050109031d0a0b0f 73
    0x310810040000c070f6488034001e00786071740d03c0c00698040c03c0c580c0c0c4103d91a004084020848040c680c4052605200c1c45150300b0103c9002d4803800003e440241003680c000e610340030f0484c0d06610810013420124401d900400d85200d43e02d00740d0301450a0b00c84c4170045034000f0b08080009207040700036135501640107000082c01c1501c62121015034441ca030b000d10848620041c0c2c0000750440490324440c07c41c00360f42548c2c0300c1c1003940d404503101e0209001d0303c0c001c203906101c0268581011800780c0010743c4050881442c045d2a81c001501c42c00c0b001c28020001004040103001c015407600030345618441403401c1078549076024001800010009001600380c480c1031220341c02c43d41d9412108801142c015800700b0401d1101e01100700d066110402d0ba00c051602c080d0509140c840c0740075803a041713600540c00c0c008a0403a0500c0d031050a100a000400b443c8140c91070f4001080b028854441541c7c4a0b480d03010309000006009101d800d03400120910a1060140030091024500c04594000748006159607032 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 286248579 1250 286247329 286247333
    0x60a020304030203060c1c060e13020402040e0c1e0903030a2d020706140309100507020a08031005090105030f0a0b10120c05010206010519050105070314030f0610020d1b 74
    0x91409250b00c0694188201c00a00c8a02e1002800501d840c2846e00c003001c2180742c4406415055905601c0f600c213500f81300800042e400602510854100d85c4018409407900f80d50f4203040e01401c409503101c90100a0001d8040210104030041d0601641100c90880c24140b2900010b600e0b07000c4c3d03c2c200002c0c494010106407800ca60032450411561062000c03140707a10380250000e54a150500550012a02c0390303244556000078001580d02c6108448000c05e00c00c0a58501c000103030078040e1510013988159025032000650480c059032007100700a07400c000e6545440c08010f044001039208034003a411480e02d81100e050040f50361803400d90803002410307140e155401403030b00c14941c940c40701003140d102c1286502040070300c18030403040742d000740d00301c3d90786036203d000b0081414824034071040e9905481400f0003095021340040d0003040d00909101c0c0f034082d5034180848650f44101c0d4114201c1c0c0410b010042a890802d50020a1080703501c0240040302c0c0040300078040d100143c0041800c949070a000c001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 286249829 1250 286248579 286248583
    0x103020609060d24050f090c1809011508010b0f180310020a020c120d02060a0f060b0a0f1d0310050c0c0102040e0f0c0304120c05010917070b010801020c060105060a02 73
    0x40000410f0608000544159041c0d200703280103000c2c1c602550a8202c0002501d1400100b04415148000c090300d05035201e501002c031241d0f11680d18007031003080c0c2c5140d1241e1940d42d00c1040b4000c0c5100703401646410340494009202d110160080c1071120b8050103030400c450007400640c2c00c4007050012032445240c4901c0002d1400d040c500d400200603000055108040794045414141c80f4002da0702c01a100d400c0119803611140c107400c03070100690003000010b01c803200a4200d448642440d001c00500a80c031100303e800190301c00c804400200d1051f8000c428071a41c0300100520200d1480ca1544100c070f81480043d0f140c8000e040e01045440c1c850010030f40070814402140d2804000c90003c660700e81d0341e40110b8800c7c003011180d4060a154880c00164044110400c50b4031039135100b8521340440c070306000150340640000d9003d84403590713548104000a2119090015210400e4145a03141c1c51a842c00f51902403058001303640607401400304060215001446505490702112040c0e01c400c07205004074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 286251079 1250 286249829 286249837
    0xb130312111209030106050f101b0507030c140f1315050402040f0608070503310209010305010f1d0a02040513060c0e0907030209010f1209060e0c0a060c0803010302060906 75
    0x41c0c4038058569a9229007a8440c01040300480590003480b110755103004000340044120801500026800721041655100e400c0100e840c0140e0111014240303401c0c0c5a90b45001881d420403030f0a608810300a0040c110b040d50031030054082160008a0991a5404500c00001a403032511000303071183d0744001c07c03071b010701c0812019043c042c00c215141c540d40c18010051035001d100741d101080c200004507031494861b0088900c5070300602150102074001c040070004c6c3c240c0c1c0f29046040e01c0083c00203400160740d001030150085009070000301e400703e02d0b084208101c4401d110074408105145d40000000301c804500d2001d501c2e01120f0000b16903441c40e030000e07181e00c081030000349030910381180d85040b1904001855a1540140c48030301041c0e9a400c0c054049101d40c60740ca0b070101e5803131080291a41d1040b8515a5405c02140c0c01083d243c00e0341c0d4030301080d1a9240c0d405240c0d43c2050001c1c2d2660300300303501e501c00200120320342210f50002c9a210350ba542c0c4418000a405000000b490007521f444001c201c2e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 286252329 1250 286251079 286251107
    0x18020a140f011809020c15061c0206093006060609130f0e0f06041b031e050f030703090e0604021908040204021c09030e0906010f05160204090f0303060b130312 70
    0x5d6583d40510711945841e002c0e44a20304810700b0381c00e0081100345c1400031100c0b0384542c2c60180007000707000c5602001401e0300003d1075158400c641101b80c9840100c40302c4c414034981c03a070700b200745c00040ba8043c07d94104030005006038040e0006016000040d920f14100c044804001030000951401d518030000c05016441049001ca1143c018030307080750200040e000380710b94010b881070070300140840d07040c1d40541054880a0040008203112005400d92011076140e0503100d50708171410741c075003030a005081d500241030035004140c1c1d02c0401c100c10401d00702c040354803070811034017145814405040001c1c004a0001144e00700420740c4001021525190b040314035200320f120010546c806042415800342c4030f2944101c0000344810481c03080c505002c245d25000e00d1050f1500742641d501c1c9001150b4540100c040400601d00c4284e2400150300c80b8450740b68554040c0d0b0b00307044100c1c428203014040d85c005a0040708180000c101c1c04080c6a802e0406400307499000c4080c15071401c82c003104441d250703660108 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 286253579 1250 286252329 286252331
    0x30616140d180c03050f0109121d0a080102040e061503070c03020c03030f09010f020109020f0d150204060e010809071d0604020d060905010612020708031305070918020a140f011809 79
    0x4902c00e0080819038079045030f1060040b591402182e10100703013620040000101031291418041e0400c5006406c0b410211540000381c0141d0f40340040014051700c1ca56124400c2654002400d020390900c40f40f10b16403002082c3e848450059051010000c00c1c40300a24820030006a10015002c252080c4125840321000401b2640c81c5c400050034801154080300c1c0450128078172144010b5001e0041c0100034669400400030b000c2480100107205030050081400c0710181800c01180c46030b00f000380b0140014001580d01c0d2a0260fa101002402e031440290412203c0d60094030200310a603c04101044410204542c2074116106d00c00807030040e00a030070703046400750306210300412061200d50003141202ca09035110068485000d4860b400c92003105806443d8082c200006102440610a5031700b506100e002258034159540d0b18a204940d10302d82219615000700015005528000d00000042c0666825011950399410005204d4944040b078041c180030f200c030180c00700c010110107a031004005001c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 286254829 1250 286253579 286253621
    0x140309031e1908040509280f0e0f070902030703020f0d06060e0109290c060a050603160b0d090f0212010c090902030702060f07180b071209120f080720030616140d 71
    0x9050048c6c811030323400d03d04691412107643c07450080040c0041032984035901900c142828108450083d600c0181060240f603020040700d104000903030b00030003400e00680300019a50b402c1410060002c6184c1c020b40b410060500f0050110907141c112a00494404202e1500700881307034800454680030703c02011803180114810401d11b0103da4000324841c80c1c045040c1d42d106a21114012190002030080d005015414090046020195413180719128014040c6030076110556000840010032045c1402c8281d4541804544c3d46411490b03240141c002d0f0b0b5810360440c90006002903450000400d03101c40418000040b641940c0500c0340408007000a04040121603110784c00000aa4060b4104650745c0c0c841178402440c1a2007102c01a042d580d40940d0b843d06200c05484520f801903020500380c174100d40410241000401e0204251000c1c54014900f480f5144080e04043c1000002000740611644040024848035480000a000c00404403506074075003101c1800780c0b008110071a05a402d95503064 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 286256079 1250 286254829 286254901
    0xc0a030e0a080c0a05010b01050c0316050f010615080a06030803040201120e06070f08090604020901030b0c0408100518010b0609060c0a140307050d02070e04140309031e1908040509 79
    0x100c4d0000010340100b00074041c414415004440740d10441a05580603003040c03059000c0508071800301425240510110f450b040743c016809421108503a000c200c400d403600cdc0310203003401e41212007990f020794203160801c462455038031900428031006000030704101d074007007120940d5849a40000c0c00c14212404990a0345441c0502420042c04403413044041081100082c440c680300080716881182e000d81041180e0b481e50303469102d6950060054a00c116062002040e129810490b01d0904c0350519804256410000550000f03032101031102c00d0b03d6410001581074076142d000440d40c0f01017007510140d41d619070881c034550421800010041580c0d410302c051610b2000300001811509010303c0c240d038608410600c0c00e90343d528051203114020320052001501050790781c0b0085e541307610b040c030543e40350140d4075000070b09140b40035141903c4205070a400003504a0100701d10201d4095400c2900e03a44025030701e41042e180118800d0920810811001402509520b01c00b480a04561040402c8801840d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 286257329 1250 286256079 286256083
    0x60e0106090f021c27050a020108070329010306030206070606032a0302040915090b0a060b040b090f040902090403050702030d0309080304060504020f031618050c0a030e0a080c 77
    0x140304000105003085103940c0a14210320880d0704d0086202403c02821000220401c060046180354840c0480ea0a82e100102420340f4007800841313108602400f0b00718003510014001d810080c20101c2018905169541e4210251740c043c3c4444a8100c00c1940070b010000048018120603040250800e02c045070344010040f594100e001079a1003030550f1002807142103946011221230b03280e8a40d80080e08081000075050650005c50100d000b103564244001c44085041c0a1b100d901c102100c10308131003010400c8041081c0300305d1002d8000e42c940c0300d203082e04e080c00c409568000d8000d5a03201c1c00300c511425009603140e0380b2101c210741c0d01401e0441309280c02d0401400c25003042809038024060440030816651003407146803407055106028504584070f64907160000d00000304100c0c0c00c5807540b815080030b13a90800460b58081500b5204910f5582013401502130091115541642c2a08207014444003a2000050700c03d080c01c103290000e1407259232004640741c071046c03c501034100c03140050684160400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 286258579 1250 286257329 286257341
    0x280b0d05010812070203151b04030f0201030b0105040807050f03070905100603140f010303121401080c0118060522051905090f0f0105150c1002030f0c03010501140f07060e01 76
    0x19600580f11015030703840c0160761510450500a6160b00540310826000d4440d144041d0001d00704610303a080c0d8000c2150017421507100750402d881180b440c20042045603450b0107140c1d0301d09420700e4224241440c0c0910990703a602c640c050786100368528160808151803c000c0c220041800c030030144010308045401175003419903401104c0003e401d025074403441034903802c03006000300b400f20318003211a880c540381110011a00850501042d07203a103a00c00c0c07880d02600c0140d01a1482030042e02e615020600050f03c0c0c0c41c0c0c40c0c61150002c50718080b0400c41a40c11809450413091070112140c1a43c80080d040c8520745120f421a640c410400c0242914031895040a50142c0d4801c0d11000700a4072501c1720460410350071104c080c0000100001400380f400c201890402d0200340c032100700d0820b000c0c004010700340302c0350101e58881c081e03010041040400e11040aa80c126800c000b002e46103505000008020340c21140380c1124081c8001981c820041211044031031282c0c0011003085410340c0c01900318081d000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 286259829 1250 286258579 286258589
    0x105040b16030c08060103021b060108031b07150f090e0c030a0f0b1f02150a02030f010e010b030609150d03020a0506010501210b010201090807051c0509280b0d0501 72
    0x1c110341c1d991603503000740f007681c61408140d155a5803685e51000110083e40c00440f80c03180118011003201740b45482044481e000c0d04942014544500c0f41c017550746003a0303004c0c921581095200fa40100000120401c6078510381c59545000410b140a070350058403a8003807039003e4292440c00343d04009101c4144000b0314000e4000c41c034203100b81e01e8200003d4060300c0350014095800320500415810a480300d4406a034456014010b65250722800710440d00c1803602101d07044e200e1a0001308200c5c0c0443c0030313002c4501602404440305100d5050500d0744145000051449005800100200e00d0000b400d00c0407020300600249441d902000b00e02c0d00a40710b00b1225070444540c032600c400410103600a0304070f4084407004208607807410800326000b4003c0e180703000708903065540e141c01001c041640580102a1140150002d0104c1c08201589040080d51030500404000c07091241c481607986001c840c550301541400111010008640042030600b195401100300074800a40130441c210142c0046040391 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 286261079 1250 286259829 286259851
    0x90f030f060f15092e0b03011e0f0b031e04050307020307080708030d050c040e090f06100b0315030708011d06010b090604030b090708010c0302070b0703060b09040b120105040b 77
    0x500e6503010004500071008440380d1024801001468800c5d80820400c0018510360342c3c01103052010081010114203500241940d40d0000014840c070150b101d41c8000c001c00800031055890728081e542d10b0926658010700c001201c0000200f2041040f002484014100c203171124004d504003450100e5aa07480170901700e0103030181e0180014450004590704040740c000001952a188001d03042400510740140200c09080c0103000204058445910051050300c6030002448801003500c6101d203007440c0103100a4112034104814403043c8800b1050b00d81250940c0d95030122040c8800000e0700305a941c0d0089505503190801c07080c40401c104402d14840d141d8041030360b559988800a1031418400e1041050300460100700800c0020401e403800d99000010034145d940c0103850311303804ca0941e0680448800001e0b004524181440b54490089802c0007050908010b5249408000c1d0454059036001d50b200701c0d51512200e030a9180c07140c001c8110761556008009514162074600c040010958000080c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 286262329 1250 286261079 286261081
    0x5030c0106060f11010509061819030e0102120c03040b0a110a110a0503061e18030408031b0c010903080901050706090606080106081218060702040207380a02090f030f060f 75
    0x4184c041c0304003402440490086e207000d0352100444040b0b1581e03040360060742d100c1d4100a006d40070187e80100c040c03a01c0396849481e56102000020314016410b428500080801c00c0280e4001d000001242c5c01c550300306030555105da580405c11f0716802d4a550145e0320034000c150440d001c000225a01e00020311045400c80342182d00c60060603a41c0e60304941415800071281560400e1454415056900408040014030034000402885041d0340041d8030400a5500201c0d03003a600c03030303d42c0a8003489092074500501c030a06080000800c1400036100c0502078041c0003849044a91050302120f070410b07040003091104090340e1070440020201407044c4071695281030300c00300340042c001c6400402d00708152801400c1c005241640720003540100288d590041c0b080255400586817800030f05051405221030004001c0071806034000d8082d0010b0018101240541460b030303501001403001d4012440e02e90050311680302c640441c10301074421001503854030400740200c108000000e1410702c0350707640018132030003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 286263579 1250 286262329 286262357
    0x70c05150714070b0604090c03020a0e07020114090309010f02031b0a0b070201180803060f0d0f061508030d0e0c120703031403040b061c060c030e0c060408030306090405030c0106060f 80
    0x980070f00344008010404801c04a200c5107400d400104103140030384280c00c1015a20380c0090081140d0354070120144d6031004c1084130f469020f20990840740380050340c408543c0340030710380d080e220721800d50030506200006500da50918403c0084e01c1c03131103600b8280c1208688501000d540d40704002101150314400c2000043c0402d48180604e40f031380703d00342c4003601100000c1d503101c891540000340b070355410000c0c4c040155255980e8000d04c004d00c902540e0411a5026036041940580e106080d280b811040c240008005003c00007044032040b80c05c0010003e0506c2500c00514141003094580c40c0e840840d41d4600c0050110109024040328802e4031880070700a690006001903020464016007000b03002400160142803e00625404810004204004070b1996540f08100c490100b0182c0020f03980311414031111008208041903102c0c00ca5440e0b05080c5044045942c0e4440140411b002d1079601c008038040160800a4817091080003000b44075403501c1d003400400181301041e51070300042d158551414 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 286264829 1250 286263579 286263617
    0x20313080115030201050c0c0307030605012c070e1c0b070207150518041d01060f140f010e03030c06040302010f0f090f030e060d05010321050a090e070c051507 70
    0x1002d112404841c1029207035400544103500329041c03150080c091200c0408559505208245c05180328801c000b40130b504001002c0b012407a4070441400ca291204a44070000401d41e008591145184c64480044072200740440c072303a031240004c09a0b0078035241041404101c0c410a09510a9100764220f40650342e42c1e407071001c480301c1040451404038408100902e100c011200442d00030b01805040860100400301c804021400d94094940c4142d564440c2484020034819040c001000001e005000100001c0e002a4400104207003950500a400d40040400c4c1c40c00d1007540e441c42400019178206103400d05020b4040c03c885522500018038188070030404000601c55800230340e402c403003e41201c0e004d941e806c0e00d14482072001c10b507000d00c05001241c0a0000c600409000e90300c94901c3e1000010400317100054020a46e51324018004140040c0e071107282d00140d42c600302e40c40c030b603000758003611804000c1c2c074030f800d43d000040c10380e00624011403810f0003c071940b18010b024981ea900c110b02c0c45686500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 286266079 1250 286264829 286264841
    0x80906012306180118030b0f04060e0d02070e0108010b0604090209010c1b06020c1f0809010209060403140d030504050d0e0f090f06181902091c030801090605270a06150203130801 78
    0x3e04082100d03002ca001c2030080240f0542c8142b0514001401c1140b0458080c6480c003841801e00040c0c1c0b00c01402d020804e07620ba001401880000c000b0b100c649004400038407540211f0084102459020401488aa00c144108805190010702051a480c00c0445004103026140129005403003101c20051050030200c081c104108104010400000740c011007ca803c01170140103240159028002071290b070b62110003c100962185c0140051510441303001402e00d80c15001020516207807034100404900b005c281c400c070700c80c510b00d042106411241c00050b03407200281545078201007140e08010181d034880c0d203e107000e4101201c43d20255288801d020400790f00888150441e080a4032a102c4002d000c1c3d0040d004140c0d0042070300c50302c0250104462070302104000203030002400030004214810322842031300302610068411019001010034007440e034170a00880100c820ba416000119503241603031124014144a08807242da8801c60340c0020754076008120070300d1101041240000b28050b0502c0743e9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 286267329 1250 286266079 286266083
    0xd05250e090402091e070c0611030103050c060a120906050a0e010e071a0c160510090312050901030b0405090331060e060f0d09030f08090601230618011803 68
    0x6845940c4990038000b542c04c001c0c181d0444010b1104d07800003060425520680f04050036522a211801c1c107052140948020798108241240100018404503101240c0300502443c240c40c429a40c0940141c11a900386010342d8844a861910110340200030307180e003029010703240c0d0107014814a43c00000c12402c9030301d99803074020154800398003007104040c031441078040310b0640d001d05814615100b48050401c1d12400722904010f0840c8003c1c84a40f500014080b11500246004803c00e400c40c5d66070b4124000315024031060180c0450340404e0750703120382c004512f060b002401c107201c281009113500c0c1d604d822050356040303a450300c80c042e0545417695202d40300c04e0341001c0c0050071001d8500101900c80c107aa030041c194105a04010241c560003a01f0024403683c175048100080b5540c060030010520000c81442004020400d000c1c0041c142002540320705548042d041100700100c1921340d44d0701481c0b54107601d03401c854046841c0c01018020b03541c0c080c0c540d2082e25084022140d803070755050911024000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 286268579 1250 286267329 286267339
    0x4050105030328020c12010203060102060f04320f07150309020a0918020d0309050a060504030b0f0a0219020105100503071809030302070b0c0d110c030a140d05250e 72
    0x4490649036005100b5107a030b0203d401900c20f24032178036000c2400c41c40c1c0310070404400d030f400000b4803805580c10450680d21009a000e10f4080b070074180d843c0c4c401c08040c2083c00303095400440c0d0500140d681205180c00c21502c3e4412203040d4030800366500d0301c0300300620503004a100d00c200c5c2203a03520701900402500581c01054401c8140c10b084100009201d4a070000258001104299005031201c0c07038444411801fa40702c410000d03107403a0810003c65038a40141e410841c09100800c00110b072070300700682103100221240683c0e629050618001c0c0a40104400a00030a400e4010400d0b010340c444c902031000c0c2000009c003291604103150790307286288141240c5d042d82d041c1002925000c1d83c4000c5000d446460098a00360580c0c8be0084230300c00c15a048112070000283c164091080c0d48550070994107014000c034100603401c0002512809882c04000502604510551040281c003040781c0015540000410290800149400a446040c0441040e0002c03222001203201d000707041010035500d001344 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 286269829 1250 286268579 286268617
    0x9050105031011070807050618010b0904060c0e06030109020d0f020421110306011401110f07060509010216060c0203100e2d0d020303070f0804050712080f18040501050303 75
    0xc0307000101110f140e803451108050000400040c90a4028155180103500600c0d95042c034406085001d2030b001030a100c280e02d01448a52540c40c0e0701031003503010303400190004034802e10b8101034809a90ba1006140c3c040000400495413001a60280c0845142c00c08200141c1c0e4442c5050401c910031402184000c50a00c00c0c503a8000c000c0c1c4a03a098198881c2404000310007000020928118003070b009031440885a00410302103503441002da0780220545402014070206041101e501c84505000e031b0f03001c02c1000a42c040e0a03074002c08c00c00880c03c10000f04001301550750701d4003c003004020314049200c0c0c09442401e40b080c042c62700038041c980d80080003501f940380703107002d402c040c02e040071040ca40006a408100c1c02c0074071003405299003130345031500915904d1808800061100078020f03810000d00c4410414040401c0e40050850155070340d0541d0003031403c12078145041c980c002e264076410680400582105400c80c0420300040c1008107640c02d11860b41c85a08150720380c05004080a5280e038141 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 286271079 1250 286269829 286269853
    0x11040b040e0705040902070b1e1302011d06030a0b030c03060405101e0c09090b0d08040e0702030417030c2118042909010608070804060e0111120708010905010503 71
    0x14420b82c200403282059850191780e000c904080c0c2e00207030000c0c5d54a2240310204a090405280041c0b010440804120321030314100d012a09803c140c00006410401025005c801c0b40b41360001700622050b0081191307807280350503c2c4200140a02c2160240030303000c0c02d40213070721605000500c40e000d25800800381408039840d80c81c0c800105102541c581c0ca5860264007141071088034495002080c182c0da1b104100c550a100800041d10094070302c0d0f0780620b000206030ba020512403010340381a10215000d002d85611183c1c4100c1c13540c000c1c0d4001e5154006012500f0800c10310000081601c40013117415076501d030540b007503142803005201d03501c9200700c0c40400001c0110525400741101460f801440001c1c460303091255680e11040341c802031010102c1800c100205498844041c034010300381c0381b6014490b0303e040100140081c0010f84020600c0d52104401c2449003400c0d04416403441c04444c115482d0780e128407844040c0d603425103c0701c000c9005038001054105080c02f42030f0503103001130001c02d4021400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 286272329 1250 286271079 286271099
    0xa080406050603210a02060907060509040b15042301020102130303110f010507030603061808070f080405090a14060d050309100908070603090b130b0a0e0109021207080111040b04 78
    0xb00300b19414003071108802c5504180000d942400c0a01a9180761a030300304410191500101901d8100c0d00d50203541304200f41da512030200c41e0485019940403d40c1015580030410705040c4071541007003e1000702c0c001c248802e4903c2c42c0c02d13420401d440d00f030f040c01c004400164200d1141c2480c100005408440500200e8001d13003131038404203040703411202c01d000d41c0c200184c216501550500002a2202420024003144e4000c000e0290742410140f41807a80f6651203602c0b80c403407408020300820400c8002018085958140c4000300400f038250907543c07401c85d260800525003900c41c039951782c010740040f400e6403e0a4541d1a00103074010001c510b050800810080c100c10303075204000c2000f104a00c0440c203a4403d21a00000301410703140031440c0c00d09480c10380d221480c01012401c3c0390a0440104000c2000c45400c960030000020000552030440e0f070103240506140b83d03029411030481280d020b142c5200150101c22500508000c00c0000c21602d078660440c4524803131415104414001844480d601c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 286273579 1250 286272329 286272331
    0x1e0302070f0506251106130f06050a0506010917062e030f02010f051201031704051909050702010902010212030618010b0a02011805150a02040f080a02030c01050a08040605 75
    0x10110004007000c241d4603980751a00880c1c148200356059500407076091803001207452100e059003055402000101081c5030340d03e034010440718650b4080c081c600180314280001e8040d071504820180507514100010300d001d0802922400c1c000707111805c0011b80501d11420300b424520010b40a444d40b0303120101d400758003410141c5100304024003032070210b0404040814a800461248220100c50b2050b40000f40034800046801c00900208000f5000e5140590703131094196607100e22424081c074548280803507180115040302d60421160300c0300d0740380c501000403200201c17034490b001800b80740d45401003242602c000030710090241e4400c52004040741c04c01c0024682c0071001824a00e0890551400131000b00300aa002c2c01e0001c500040d203407a5541c0c2030140c8a0500895410003040c040603a454999403194200c01886001002000c11a800201e40440d8002c0501d8401400c9440c2c441c07520326100d9107100c40c03c920078403840030701030503031750141c4140c5403025669202e420035039507183c9500001e820 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 286274829 1250 286273579 286273583
    0x307030f0311130306050f130f0507180203240d031110020403030513060f0923031f0f20030717040807060e0724050c070b030f071e030207 61
    0x1481d005085001078442c1c0c09050300c01e10b8441c07003500507480d600340035080303031070107000c9a040c0044441005119007140302c903505040c1e8814011000103401c4c0c1415400c03d51540c029030220503400c40950004000354001e503026200e0350840006400d40e00840031224104282c041c0d801000c12038200d070100307001c3e12800c01c180200406841c012003090850a007282e120390000c80201d04007150b04030a00c0c40c0c1c400300902626807814038410004c0c28a0f00980002c03014401c6644030413414000380105500e00014150356172014048500c40c00841460010b81d5240c14450039886141008003240e0003038030b000300fa221142001c000c0e8070089581913407410581c802005030007840710140070200c071948100c01d5184242c4c0546101600d41510b4501041614540c28913a02c1941c0a000c1c18440b04042c41c2c03044884444001d5a0901d21081c10300c00e403428000d0b0362594003240901e0300b00080d1081c4500003035129010910354030445680da2001035a403500ad9000b140007032041740401880aa019500900c0300034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 286276079 1250 286274829 286274831
    0xc03020c12011d0d080c03010e040b060d12020c01120203010e01060f02073305071101050306030c36010303050a18050423010801180b100e010e06030d0906020307030f03 74
    0x383c00c218100440405038401d104140c0c3c4070400307406206500c5051a03800803101721040b0301d103515000302d03030b82e16403806480076160f65801004160306c0e58440d8285805c0305e9200068410070030003000045e48462444d00694082034050980089420032407084038140e601620004c4080d90810304101d4140d400742d44802c0c2540703e290740c0480c0081d2a81103000d880b520000c1500d02c02c2d04a41d2603a1107400a038082001407007401d01c10080028081600045210801e02e4086e4030790391044c0002c0d160102002e14690480312041e24a1101701c1c3c1e1103524280804049a021980074801c0d0358801e02403000d10018000982c203009501c2514412020070503c180ca000742002d119031502c00060481e146002c503c0e80d02c40441d014041810391501941e0f00401c0c00318003c00400100c5540700406500740c2c90014030000a44c000140705040c0411030002400340816030310441d41e105d0303880400e500340640d0406d01c64030034900c0e424541441403024009070b90040e400386051451955064a20f541c0001c2810181 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 286277329 1250 286276079 286276091
    0x121b02120705071e140409110f060d1113080a0c060c15050a0212070201180b130516030501050c0f04140d02130c270324050f04030f0c03020c1201 64
    0x4500c1d81c010500591540150b03884000e0325000394812401000c05c0803602907420001500b02140e0b170520003031f54201003941c4007000320400d080003c4041c4030365000c01460520b84403a21802208110203003c4d4811882000003000d03271602070960340e9254012004008600044040c400749102c0c1d040a0141803160300149641d821603941c04060b9a01180d01d880f8081d40031410041c2002e260100781e8228806000800003541d035001c5005400300c840c0da02802030a688404170340c0d200200c400001c0029080402d40342002080341d420326511140d1320081e01c1c60f608000101d03090a141c84116418500c1c0290070a28080c58041d07250070319001000304a6104000c5003d02002d07881d480e07400c1040a0f40900001491004410040c11180416400300d49a611074004003144410f2030b2018820341e5001158500c507851058011000080314029017076942c0d09180c14040784c0301101b03107440e01461003503ea40460b4550500101d84071054044c025005030721203860300b2164100845421111000f103400404c03a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 286278579 1250 286277329 286277339
    0x4030c0314150c07030818071202014d0c0f01230309150105030c060310120b060108090f0c0f06071407050103060524030c19121b0212070507 62
    0x240b07000448002d4460f0b003000410808141c0d1149200394403000e540d803850076000c0300d40b02c515610003150007a091006002c072010400c0d07a014002100c9103603410305500400300c6001d200e00400710510841c0100002845400c2e000103002041c1e000e100d07400441c01031000454040c05c001e08201c0059800341844940903400c1100900d01450480030302c0c860000c01e5403410f220280724070302110f00d010b5030002038507003006010710b581c00700321514040401c0b04c1c00f513260f032a0b50702103140d100c406610505000c90000e940000300500d0034030302840b44000340c07a41c00d440d41d60110705680341e0145801c40743c1c81d50000c951036000da1504042c0960410000707045039090112903694041c40c0b41e404801d41840f43d0100f5804c101c15a4180200c5014140035602405960ac0035581d841c002089003010b440440c00203c00070364500f0005c81501e003a0783c0985000c0c03694490140021300f2036483c0e4100825000e0078a1107100d240101000c1e0705020401c03a5000b0454419001d501d5240c44e08514000c5400d80503e84001034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 286279829 1250 286278579 286278613
    0x7030804060b18160e0409050a06090302010e0303091006050a181a060c01050103020405060a05060a050a0201020f0f090102150108030702060318010608061e1b0309100608012004030c0314 82
    0x100c101c10180407010700c20740030138003d422003001c10b004d14400c6081460a50014401144500c0a10f51003803012500da030380ea2034164054100480400d041344408001c01200712000551500240c41e980c404010b1a0303204c40c1801442000d41c05094038182e034210541c40e03820b90650290100d41590000c0f84080d806010001e84141d100958041850307458000500a44c41c00f4070a03075400c48421034450002602d01004980a4010400018140080403600b078004c0c9000790111807440b070b40c0c45003207507a80d0034400100f582500300307190440c01842083d40070714480c104400c015050f9084c501c020341c2462059030800505601c0104602038014481400c5201480b090045202030400c22019001c20301e040014040c2c01c00025488402c11444817043c040001503007000e6004400040f802903580b0303a50715003042d00c1c10010160014129291038400540ca0006510085510381740c180660403038002c0b001d46c01e107507010f90302014200c3c40c0c06010400000300c210303502c0d0791340066000584640b0306070b1140000e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 286281079 1250 286279829 286279831
    0x10e16020c030115080613020d080a090308040e041b1809060f1503050609160e040f050a12030b010216050402030601270501080703020c060708180304181107030804060b18 75
    0x90201040c401061005c04024080f6951000b612501c01070304030700540003d900100c1d10003024200810014006030346074412855000559001071b101a40d842da15204200044811181950f246078502c108504500001007048222221916010102500c54000d00700804025804441c000da036a01c1000c448515401901d03130280011030078458042c5141801803c0030310081c2030b02500d0b0804114280302001d050340d51029a0000c1c405904281d80e14130749044016040c110140c40d5211750f4020000300720103250501380b034510a0f6014403081c07540d14010f90b40c44401281100c0d080348085014406414990b01840c3e106e50141360074582c46d1302d40c00d58403c100032070303100b801c040d00826207040c45030396002402160030660f1446c046140448803103907a5140c01000d48044208200308000c030380360400400180307502c050044142c99849565000c00724681090340d00c0a4a1941001e600d0f200350385412055854590305521805c0c2c0c655519990003008103a01e50189501c104c3d402e181c0c0d8101c58001d1009 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 286282329 1250 286281079 286281101
    0x10050a020d0c02122b1505100c05030304110301060b070f0203190b0609150307080705100201020c1207060f06120c08030c030711060412051e06010e16020c0301 70
    0x10703510001c00342030405840d4a00072550541d0301200c0214590381c2c2c00030440e1613600382030740342d082d002846446070542c010703400500210545c10020b21084100b080d850280c1185d8044400682488030030406442c044690300d0060031581080c40000d0102e40c454510350340c0c180004000040403511403080c06d000740c0101300c09031031540d54011203c1c01c40c14104880800c0c06060b0802414400b200c0d81d8550064200400c100c1c09a1401303008501018115204803200c00c600905032540e041d241d0745003942e100220702c02c0ca03200b90b002c2c80c05c07103058500602c00c03180c115154401820407500782034103070700455105000c22034070319030742d041d240e00c2c00407141c4130f00b00c040d000c01c121f0600c0c80c04150600905100481c1c000500036007080204107090a000800c43d5240d80d03214103044281c90229000038006e009580c0182500300c003084071f00c01080750224002190b408840e154100120304030500c0780c0ea1305800d00802005c0e10120011403c0345c1d644070a40c004580091048484251500000c2030039100b00480e8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 286283579 1250 286282329 286282331
    0xb13020d120e041104030201210f0b0f0d02060a0c0305090d140d170105010e1c03020c120601060f080a1b02070510110307060b030a06060e0f070807020705060c10050a 73
    0x88554000c2d489036802c0700e84403048500f1301120440314011003c9101c1ca12000b410700104601c02c80902c5940d50402e10003080200d010440025010940c001130884540f4440c4101d4a1541c0c0107071900e0610f80d0a0780746600601464104030740e0401c140c4038038503181011b505200003480307080c00f5039441c50040c0501070322800c031500f404a800c5906510f0711030000f07400f0341400483c824000d564104103005a045520901e4410001c090b01804158413142c500e440e110091031050848050580004034055403140c2600e0035203801c2910b645440c0c42d2038003801400d00240c030305403610052610484145400100e00200050700c1c103c5245c40d000c2c456108041c510260700303c800304010030318082d00e66035503050060410101c0c40302c0c5000c0450b01d9200d000c900800d15076481050385c00c55101001040301f12940260200403154880c0201d6010210441d502101c1200c50300001e01000e105504441c0560110b030010b0a04500f05002c01000750030481200f445442058001c01e55407071107000e00f6010301c0a03018 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 286284829 1250 286283579 286283603
    0x7030c020406081c030c140c2812030b06090d1a07090308030c070c0b03090a111005090904050f0a08071b080a12030902060d1401090c020a0b13020d 65
    0x30500090b200150b00559513904240b0084004a104110300d040c0400e541c500000c00106411080e1159030708100c004089010101e00e011100074001b40c0206a00d00304010510108015202c020104115110007820146600d500548a60080d0002c0f9010070b0010310715418000c102000c1050380e10201c1003601c0c14a09903030551440d51049a5581d08030b401407400000460030740e19001c013544005800c054400e800000c041e030500000007a481c0190002d031000658034104004516525040b0140c1511001c241e10301101e0707079142040d074102030108681ca4403800c29413180b0030000c1c3d2800081083d2418000e21316001c228160174046243c01502c07400c01300d919030105007060502c031025400c14082054440c582070040c4440003912420300342e8802c0c035401c0213054604044010f4882640c1c02904900c020509881c1d0310780d242c1000424000d941090813090303a80b41c80d84002e0b29a14010702d00960406070074000824080c4201c20740c05400e0050002007408103601250303200d81000c5c010b4030407a691032 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 286286079 1250 286284829 286284833
    0x9080304020f090709030308060604030602040617010501090302090c030a0914010606020c0907081b0d050a09050c040c08011a070206040816091b050a0210050103030302091005030c1603110307030c 86
    0x2081c600003002030300c0143e07141c03500344000740040019000140600c03800b0400169145c1d00e032412280a0f590150065490b9595800080c040a000a001e60780d843c0300200041065403081900000712034004102d45007544070340c004440103a1014048040e50798840040304007090b003c034600c07210078540600001e821468090300908009195503180e100c2c4102609100045a01048003a0024103050f100c03020800402880d010034400c8503540e000d490b0820040007030341307802d590050358864003540649041414000421045030403003104c40010400c240010320924004900c1c82d8581d001c050320b03d6180c0480d507000a0a2a0003580c0881429405500c034200081c0740000d1410080c90300315030501c00b6094883e03240c1c0082000d0202c01d020000007040c0244014420860082d10701440e42042009513100c0c20020f000e07601850b4154020304048080640e1184a5000c0305e200303c008142040c14008040315049001c1c0b1035100c240c041228030000d6a170726817014402803e00b5071298441034141d403154 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 286287329 1250 286286079 286286089
    0xa060c0207050103060911030c160f0b011401022d072111030f030f0a2d02010507020d090b0d0908460c061d03210108030403060207020a03060908030402 67
    0x58001d0344401f03090000c3c20320306450090550390411030f01c048068840030b4290904100d443c00d80300140031040841d08407000e1007a80c0394024140c5003070305410954090600010782c2d450225034000340300348a800030324500107004090004181d00c0014259400c071175581c1c0d1611080401c82c64414000300c0d006174650701300503000c011a842490301b500600240f91511110944078040c0c14402c40003a13a00003803610b051807150040c1c0005400e00301745940c11b1485850980e441d82c03988141030000d0361800c408101620b00000e54004060324990314505144d003008a41d466642003400130040e00b42d140c00f011400120100c1c0a80f03c1071065015a46c4c12210084000c160b0186000c07186141601070301141001c0880e280c0c41c02c1c01a550b6040070303491900b8030301e0460001c0260a03034601541828001882c0d000c1d00100003402c580a0b424034450a01d02004c400c003400002c217110384a03c9038004c010070800544a40c0240508500050010079082d940f5145c0e0001d0f0740c0003500071501c1102c00000c00c0110301d02 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 286288579 1250 286287329 286287341
    0x90603051609060b040b0a0c02100206090c06180d0501140c0c0c09130b09070b041d0906060a030215122d01051311091003090b0c090d030f020a060c0207050103 70
    0x8108003e000040c50501207608030b02c84d0f401485908900011030080c0b0901070308840c010310b40e002d0a01c1e1810001480001d480f280141c8048d0010b0140401002c05031401c40d00343d800e240a80030018144149043c10842004a010000c48195490356950408000104212403040d81c0500110381c3c1d481245100d503041501c2029042c0c030910320303003060140b2150080c01c140741c0300e0b0340411000015161104100d2810343c0c1c2d54408611388000003030210310040071141005202d0b411b06c03508101500c0304014161900011641c3c00d801c007800010070005854001c1c1020b00050004011514002101d050410700038400c03540031418200740c401c41502c14403000c2c04944280210070445901754102000103081c0300001c1e0424280b03a4407125244119803c410407103002040050403180800807444000c1e001d050940e20035074a0381510000903580b402810104c0b0352031080249825400742a55400360b440040c1300031710364214840d9609010002d142032142903040c8216400a0240a00c2c00e4001401d40322 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 286289829 1250 286288579 286288589
    0x123060307060c0305040b03070c02030d091d0f070305190504030f08390c0106030c03050f191b0b030a0504120c050c060f160b06010807030e0c0111070906030516 71
    0x5500c580c3c022030345c054143d400f80e952241480d960307901c1e100c0d002c0b58410070501001c0d6243c003d1241075090141c00038003800454403510200c0d40260b5131001450b007070725411283c10b003240c8403510006003150310136480035030f015042c6500301c040c007881e84480703c003200c0302240d003200030070030549514040a8005900382d40c0035402e21101c28114030312284901c0c41c40031140207141454503107403603010312071280016120200c8002000700203141d500d0030081d1007130000344016240340c0505841c2c41420100401c078802c0144003101c011030304000940e1010110944071041e51042d40700300c100800c0030f100080095000e0202498081018100360406c2c00500c0b05a00307581e028003080020b400005070010528004a40c030841e40140c4030980288226003500ca02058a500c00100e0f1000008018030072241a018010070381c0c852030381c0d69407040c09504844c03a42c0104c406590103400c6414181d0321036440d088006030341a09031040b0940d00c0080100359010346d0400c4801d0381002c070310110a030440020942c000c0c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 286291079 1250 286289829 286289837
    0xc0b070e01030f0216020d02060c011806060801020c2107020a08060402030c100e01180906170c010903080912010e0d0302070201031a0108040312091211060a150501030e012306030706 80
    0x81480c04480521100300322009004041f000c1402040d591140291401551540020b000c8081644014850040e20280c125101d038900440461608014820399203440e8083c402031454440b50391807900b40724110b8194001080040000303c2c01601c0b00e0403c0c80040c90454020140d60500f0b10416082c20301d201c4d8040d00407003e5200621105070b0000903080c00308000e090804400c456800300e2082007a46422a5107241c0c01e180b00040c01e11407582840e00c035106d041c81070390403c4100c600111000241031001a041090070f02040e005031501c1d642c0b000071150007000004504042d00ca03010b0504070500441804650301254590a550305401541000382845260440030224080064000e420140c8003404209100c410400c60038840d0f400300310003a8004076502012080c411000f8844243e01035441418011540801c210781024082c1c0b4007407034400350b40742d08181c1c10f1400440c000c0089401d008499926030b00c54810f0b0407182b00313400c0c490039080000301110385030070400c5c180307414100d83c4090108 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 286292329 1250 286291079 286291087
    0x6090f0403050a12090501090b060a09020903030d021c0507050c010b030102040e0f090a0f050d0306121112030f03040609120203070803070f09090e0f0607020703020d0f030c0b070e01030f02 83
    0x6540442180c00881903401c0c005004104c3c03800385002031003000030040c210340c13a00700380006000081b0043c0707108440071107451b410941c841e150901a0302030b40540c3c5805d94424003460034215501c0d005815045a0101c98214808022034140d041c0c0b01c0694034200402c00000d03400c003ca4000703000c1c100800d00154020741c0351070724100260345800d0000f42102100b00d80e500103c4c511810601150900681082c203c00d0528500d04026440d8102e0041c00ca001c60314110300042c0010034560300640c3d9a4105088500b4900b40c1401e110384024900a00c0c1218007040000354114a140d030302440c0945e001c1e4400003200603d03441d140006c1515203c4d180c0940d80184164030000d908001145d601c01500d2400410a1050340b1040d50300e03074071302c6d0420400d276828804101e00c1c0d900c4c000307103006594030600d02f10354072a1550041647c4075072050101035008603072010741c180440c581410200182e4880d03d840f08001d1a15240c0e4240700c43c040c0d03050400540702c00c414020a680c14052144e42c1c44103580300b1450 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 286293579 1250 286292329 286292333
    0xf020a030501091112010e18030a120c1b030c110d0501020705010b0d020901030f0203071206090c05120d0806060c01020a0206160e18041103250f060807051605100506090f04 76
    0x31700d50507c141070f01c01c4407400c00140c1854002a0700d0244251440450380c85000c1244064182110010700c5d40ca52841c0190559402c0d116442144800b41c40c2a600003a803400f58a045a4400c1d82d21801e58150b4240080c2ea001511070407a500190b074081c800042c2c6a05e000e140150958001040c030921a4a9040300000543d03615000a0b04499004042c20310031451840401c1c28000c0b5a4080e10655000c04403030018040aa0444041d0910505507040980d480d00d0402001c14030034190200141e01c0320fa075103001c8a0051101c1c6030031910050180f400d0246800a140c00ea902c008400c1c0010f801c96420b000c42c0310070342c2145041280035424203c0c032a50380b0342c02180c09070341e0207110750100c00ea0201c0860207002a40304510103840018098510008224081e400c080032403003080c0e111424101c400203106900b114150301a25144d0b90f403d54162a4040100c440350031020000c040641c401c2d41000020b0010003043d8801d00c002400480d03186080c10821049032001010556105111010080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 286294829 1250 286293579 286293607
    0xf010602072603030a0e0f060f07050d1104091d0303011d0a0221090709051311031005070905090a02090f091b04141203071a0a0f020a0305010911 64
    0x209840b42504039019004030701d503001801c0c03031604110311a01d000020601508151540100c0141d007034030002c0311a450b00b001c0c1550780d520301c00c80c0c0da903001d2034420b4080b4800c10b21500081c080d01c1180e003408a070120003601034408a50081c0e00034030304143c1d900001c010407100d900000c84a44c06040c042d60941d80351822031518400403000404900b420a0001540d00d20141c3c152103100c40f070b010303406480c094240d00c0150f2081055034546050320901c5400940b400d114054148980c0403c20008100b60403950381c0400008109100c0d076150044804403010b1400700c0c403d4034440c41156403235201c001c0ca844e060103a6040043e04982c00d503170042203d1085074030b4490200a060740242c0d0410410b6642c261080c84181885c941d0960061000030006180c030354150860a10701412500c07490764400e031a025036600d1045010090504a1127240300403106040c003000c0381e010961000201c1d12126641003181207902071000400400d07650001844401054440d079507610007082d10303080c640080e401405c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 286296079 1250 286294829 286294843
    0x2030c011b03140c010c0905010318030e090601020c1f03060e0915101205060103020301140f0a02030403050910020d08090d05090d060b1f0e0303040e0408132c0f010602 74
    0x140500008218070802c0680f4542155020500000200035488030b2060003407040c031341c5208aa0021341058102141c0c0801d516045901c1a0b250302c41d041e000c81114140700f80c02000401c80d50550155000c000d040791a10703141000d6065050000b034100745a980400743c01c1780c2c41c0f41c00020389002104204200c2940c0095501c043c00b540c42c01440c880c0c0c0c0c0700341c1c00d03440c04807140e0041111821005000420000c0001d40326060700d200314024450b004103503800c40d40031801150322124250044020071100e00d402d038000c580190092600c549070007000000700e000c1030208409600182c0c041011009019440b600b000c1d0081da4090280c51800c0039420014114005c0c0d00c5d90340c0c829001e0b20208005c01c26581c0c0300b00396200001d44a031000e0301182d0000741000d214070042001141c04202046450b15000c0212025039403402d11101980d103503078850018940007540040d840380305402000c9284010356040c0c0460030b80c05101e00c40f2910701c2090340e01c2400d40150030b5800842070a001889107540201d144 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 286297329 1250 286296079 286296083
    0x105090a120318020303040909050105010b09060a211b030c0c0507060e01050912030c0613020a06050304241a01050403020901050f0a17060411330702180402030c011b 73
    0x440c0c3c28060003441404201d0b8444001e506110004000035003c4441d00198180da00400080105d6a80c800c0350300400d10440d040180d01c110200642080c0301e0040c5070309d0744000d201c40311442020415031003040840b40c02c41440c403013a8445031384c00c00036281d15003d0860580c20074581075210350762940d01c1aa03542160b0041c0c605004da80c84003c01181d102d001542ea4645008190b250002c03402050541c60307074000e071001015800f030302300011103220b251024180000d03070140c0820107540c03030310a044940e07400260080318002d46030713200034032140c81906114850380c030b56440029803d04204240300082d0400d0201906011090004102581c1c41c4c4d4801811070310142d901c1a0079603400d20002d032082c0702c20f40225504107440c0b1407200302d6540c00180395215920503983d560491031200100506400e000d803e40400d10101c00075a01803004041e0b001c02401c6a8800b02800c00c2120780c00106145d107120f40f4058014400340421082d840d04003e000c08001c2c007801c014a0189403804400d10440500c840 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 286298579 1250 286297329 286297331
    0x10050f0105120c210c0a0807080702030a1419020601081027051c021f0e06070e1219060f0216080f0403020414160e01210f0207140105090a1203 63
    0x201c503980e11401d010700b44e503010048840c110310f480e2108202a041d0803c2c00d00000007048180010350700e40c0103188603402100550011802c040c0a0401280c2c100120080d9103403c510030b01101c0004c00418000d00c00c048a540c010748469070605e03d20901e4103103940f03010541d1a09122100d548001031038280450f8003115600340614030f0b06402d080c1e19144402030690082c006038051001059401f01e442480e81c600c2040d00c840c100e081d61303652000c0d030340d0f1041d41140341d41120001c60009401411804000c1c98042c0012002100003400d01d824001183c682104070454841d030101008454401c07aa03c0c090210400c604041d6540300b41600c25000000c01004090001175040c003544400701a5002158024401d1141c0d95090807070710003c08050360313406159044151841da8181c040c0380c3c000703c8400180c0d02c8140300810005441d103113203110388480c070b191540c504500386441d8482c0000c011060007800300000031980c8032580d908680307009003c0d50460b080a00c5030b10018a6001c80140d400d11030380b41c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 286299829 1250 286298579 286298587
    0x180b16020f120403030c052503060b090c03070f0c02061b0609010e030f0a0306091a010201051321030f020d06031a040c0e040809030d0e03010608010504050a0303200310050f0105120c 80
    0x43c04034071700300d51302d2300c0005204a8200001c00c0e0f00313030400b103107801c3c4c0e441650288507141c0d000084c05100d200a40b45841c4c002024030010308141d100320ba80e0014030704145000481c0340c400750045001640032113003071400401c46500603078441e0b20801407103401035101c00080250610302d440081d101d0041034802521040c00285600140380f180d0401000b60820391420001d880000c1d000211628500388510b02650900000606a8411040d450320542d00710380024804108000c41d0404000161040c00c00d0598a101082c10005c5c81c5c406020034200301031000a4080c1981440f001c407842315003490030300c0c82d0040c04100005404d0040381c0101ca4901c10b4040e440d13255441d00800d540104080c254152080c4a4001d40071341d80318001684810058000700891511740d11198280c030000c450140050740728a2452000078400c4c0e100c40d1031a0ba045080a00c0414480b00034401e55100780c40c1e0034110204010244014609038025201e954801d00341185810801040110181d8008090b2000aa400302e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 286301079 1250 286299829 286299833
    0x90a03080a0207090e0d1d0a061407050f01140c040311011b14060109110703020303060d0309030b04050307030305070905010e0f0301060906030c0e06010905090a180b16020f120403030c 81
    0x22401504e4250340034480c048031120001c0d6600c69003164840003a0540c0c0e500324a040c01c8015503601c1880c080c0c040c00a8a003402e10a56848410301590302c40b02c2002c1020f1f00c0403032000e0010f43d154202c0780c000840c1d510069520810038020280040900b1001000108001004900f036000549028244000c04036015503400714003603007100010306819404401e09051000124405059504c040420404071050301c0d020038060088140c0200584d008001250852034150ba40b00e0b00c07a840382c5400d4602c1600c80d0765550003024151000c484507480869582d0405805009841c1d1000c1c1c40d24010a0041c5030000084c010210410858040c1c03c561505860301d8400303401900260052540501140e0703a20301e00100d110381a4071405000c1694003000c45c10b030758070403030070307107040f540300a1000d00071b81c07200210b440090034101082c00c0d80d100c0781c09400001545103104940f0a4601d5159900540e085680c040c0c01c00303428800703100854200d81c2caa0744500c0100e1003900d055940515219409220f14 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 286302329 1250 286301079 286301083
    0x40e0a0507110a2409050c01111207020616050d08010608070314011502070e07050403030e0306010f270c0e0f2220042403090201141c0f0506030106050303090a03080a02 74
    0x30a0111480505100b031001c2442800034061f0007900003030b6204603010a0802655850311380541d084207038000704014990240c502400549a02c10290703008041030030440e80c80919122520035070703a0218102c00d004016a503081114250f21048904040c0020000e40c1d46c09940d00714140203010b1040880304a08850520810051703000c4c250403d000c101c0c500701018041c2203a04944402c400007104003000160343c0c1400700e840f41c100c50b107041c0007258071070801f49140c02e05406040030b420f08003c001c5a56542e0700035405a500a40203940b0b0b200518185441030180048042c103945005150360140214544414018611201603518000810340342080b81f6072141c01609252403440c010214000c505029980c103118122540c0600c5040000240c0030305900703440184c1800b07804298a4007510082031018030040c8424031103c10038642e21a8805860b00c1220560134407010a40d0ba1041045010301302449080d0290000300c000714182000c0e0b82c00a2141d07001400300825141010407800c04050003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 286303579 1250 286302329 286302383
    0x503130f0302160801090b06120f12040f120302060a02031e01030803090607090806010510030f020304060f0f1a04150f12120e0102150903040b040e0a0507110a 70
    0x10140d0005502481401c1c000d42d14584104040c8025541c1c15001410a90510600c001141c1c0000b260485075036030020003d8104010099501e18050004440390606050100c0038904040090507510b481c1407208022244800741c01a802d0141e004420078003190700022442c0d0710441c40d034005a40d0341e54040444e0351640e03000b4000c5082181210000c0704014042000c0e62044c0c03058012104a0360700d0403000c441c01000c80c445d000040e0800001407010382090341900c0e065031510709000c51007481d080101d0382264022201a1080d5556244480303a0204a0190b40c90b0200d086070107010604102d03881480c0d8401c071080041c03140e40d462050980d8958201140c00040007a04041c800055440c4003410ba1405035a0301201c03140f01040e8038901f800d000b1100640d41b003806a00500e03180300e400d0448040c9550140010504e0b1000380000200d424510b0000c00103041e032903e1004007410520721980540c0c401602e0b031360900080c54a107141640c00029580280707900a41c01845041128400181c0d05030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 286304829 1250 286303579 286303583
    0x50a0f020f04030605150109120602281805011205150406030302030d060503061012140d020d02070f1208030408040e100620031c0209040207030905131b050313 70
    0x400440c0341c10071244250003800403603004600900c03003581c405030011140c80d48174803d0740c08541030040520403d0b10415640014510400300146004500c9103131814003c58480c1c0150583d481c0d048240c440d80d4041c1d100121180e5425007104c466080c10000303842d4001d00c42d1584a0507540e64002420501020009052084050300c1005181d4403820020346a80c04101003101440c00c00d00002540d060004076588241041c060700c6202c542400321000d903e1075841c23000d56048000d203800003d880c0c4280701821b0748811580041c1005210713030310003a080c0b115aa202414500510300e0400c9800d2a401c0300d00d82160b44100f506d0b64030b5407146001080e500464100c40074048007007042042e040300e4201c0701c0050b21074a440f04400812488a16110710b40315002044031074205211440300b842d1400700c500d80c8542d07041c1c4013508140210303000c181241c100f86401e0340040c151540030062410001d041e40c1c005040b4003420300202520007881001c01e002809140c08100000001411510380003900220b019 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 286306079 1250 286304829 286304831
    0x5090d0b06102d030b0915090114180601120608100c0e031903231305042a0e060d051609030c031205090d0c05210604060c02030f04090c0906050f0904050a0f 69
    0x407d145841101d4030010880b900d02400f0300f000041352811901d0408100d00100501c2c2c3c06501c040d03d41c40001110700580568103000546030b00756241e48d51806200040c0001c1740c01880c0780040049040142d8a0000c04e1005100c200c0c003064000d03880104840508100d002810f04824449150484401120612046000184021989042c4200401440d40c4c20071540982c40130754403501004101d829981e0460700f11040403c2e101c2100038400d550760540745032410a40340524015010810070f038807000c1c81c49101f0755181c0401030410303542d4602c440000814900030f26802c0c190307680d24000d04040d02001c0c0c407a11403003441c039540e580700d802200c000a8015007d8440401d807494100714099150142902c00d007a100a0000f4102905040300403d018400c003c0405403920740315180107129906070182180400c0004040c0104144000c01c010440700000143d050203004005202a410790080b100304401040941c8d4840c0c4034800380c414400d0225000202501c4686c0c00800a00740c207d040e650721 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 286307329 1250 286306079 286306081
    0x3010b030405010c09050d02011101151215060b030106111c020a05010f05060a14031c09060320180301062402060f0603071505090d0b06102d030b09 65
    0x1044552019501882c4910002c1c40840c039080001e0740d9080c46401416004080000003c02641c42062000c100d00d00600000403422440f40000209444a42140c452581031a880304204001101280002c020380c0c40700b00f05490804401090b503200602c42e0000b08105038179042c2c0050400c2c4510703280c810994828030361828800b04040d40751a2140e50554195103400c520b02120591390084030b204480c0200880c200342d0030910400e100e50b006a005607014418844101440e40f00841ca11a541d002615032440c054a044002815207840d0380a00e20854003103503c0010190006050303c10120420f5040201e145c01c003008a801015568841c1c00400081740b11004848001408138401100c95030030b4900d240d444190400c0e1140e016502207415600c00c40042020000040c0c3d510303058180c1d46031591030138000c1c0b0b000601180c10300304291280003401003441f40603d088100c128454a20381408404080014407071424440941000001452803060002e400340c0b007540305d248102c000034944001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 286308579 1250 286307329 286307339
    0xb0a090806040c060f020f122203081902010c0e061b0d111b030a1716080d14040b06240d140705120a02070c03020d060504031416020616080301 63
    0xf0200544145800705081003e50350b01c2d06e00c00301d221400d05070380ca4000d1103402055038110b00c00e40d000c8956407420a2804600c1070755455518840402980200d0301181c841c000d8940b01c0000030708000c0346406581c07420100b5100644c01000d10100e508040300c0046d20f51841081e40c3e4010901000303420040c1c000e00398490911904100c000200e00b42010440c0e400358050764a80726644401e0201950690104484070001244810290b41844c1e0074501c0e141408500407400940c90081a01168401804150040415510301c280070032800d8041160605062039298529241d00c081c00705809842c034113101c0c0c0c115a040c0d180090070510381005043d0380ea00c4680d202c1e001001c0416131890007018940106124501c25810758029041b188003d00450b103603050003034000d43c007d140484103019802000405a50750010401c3e03800c2c003508000c240c83c41d0a1178010100c0380c925035107282122090008900a4800708038801c000d942c1503c09942c2d1350300030408030302ca00041010040c2401400000891 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 286309829 1250 286308579 286308593
    0x60e190801390905060304111f080c030402220e0a0f0605060307150302090a05060408030c06012103031d250e0c1213020301150e0a02030609010b0a09080604 69
    0x89620302c2e06454200c07250003000ca0618a10049a48400041010f0010b201038a440f00065170400d00c01c40382d0007241c141040214003030058003809820100182501e40c036501c0d070007078481e983c0040c0c680c903500d01d1454107a00040301c202c55183e442a000341c400e04070081c20046680090200d1036a0000c1311080c03101c6207804000b40d0a108401c0780e056041c1004142a8200010703494142e503245107080200c00048501240203410200c406988600b00c050700054076144d10b0000c00c0601038610103542c3d0b501c00198003515007141a030021120102940410b68911400c10348045220344c98940030070715855101c41200c0c6012101141d000502501d0036400e2100581040ea40c61160002c86c00c9000a94818035005c4804040317500c40200c00d010000b09070311180c8031a606901000030510307807c098149402007421940410750441866807590000c1c0140c014280e9050350000c0709290561443c9410030200b40e00740300c103102c1ca03404101c010840121407402804103201500d004001c075a0b5924103414208 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 286311079 1250 286309829 286309871
    0x20705070f270908070201050d090803040309080c0f01050a03110d050a0618090b01060309081204060203010801200a0302130e04060b01030c030e120901030e06150a0501050301060e190801 82
    0x1c51060503a030842caa008450f40a900440c5070010751050a000f511b07001900c180c0d00240b4000111035403011081c00003003445010314000c6019540345290581031020080c9451600b08182c0c1c800c00d803083c1c1d940c3c010307a405030481d0a02c42c114a404a00301e210b11007099043d01483d95900040c80c103003030810482d442c1592003801107070365000d151401081561784002c100c0c0c440880c080d14502d411401401940c5c0030b9080003825901c207220240c03074401c0d221010a1019001e883c112555078000004114284003401000d2000e1191801c14240e290074002e03c03040c0d882030010300ca00f8180c003c00d0300b400c00d00c840c00c2120001c1c20307170210741c3c000ca00e40307440e010006000031041c40b40440e14120751103080d02d102e4440c00044280c060020004440e15040d20265a04061070740c1d81015166480808198400d010107802040700c0690b10004049440030404662034a40045041000a1004101d65680a40e9400180c5801c4d038480003100100c00309040c6030545170700030701020340c00d221010140e00b81005d241 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 286312329 1250 286311079 286311119
    0x1107081905160609090c050c190524042d060204030b011215050402060d06090b0f010c0b07030222080a031413030201120f1d0f150703020705070f 64
    0x2032030145002640420032082e031030165a0004150700024490310200350300600d00759100b42489401c0035002e0000f00d01e46642903c0d0355201182507103c01080000070010403c0180c1400940a409001c40c00310f08140c1c40010405400e40d485101c0da00f05c3c160714001c014500e00f00c7c01c6503014603a4100d00b04000603520911044a102442c0f100000e0000e01546420003107036449521710b00c54506884104002d004042c100340da102c0010003001400c0705240c407900e8010030f10f030036000c50020f2000b000c0207184058a00c4140c180074616078000e0015001d0400e06078840c01c10300f00161200e500002d0f14480008101d09403801217140840441d8a40000443d064614030030360310f09010502e011001c0320203009100060103d160003c606000560040f45684050610448000b4003411824800303000d8030107051181124900070541d40d9112003091003800e010010120040030044500444482d29043c02040c44040541c00314000d0300708181401904001c04a4804002059459801d1180d00c80b040e1900 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 286313579 1250 286312329 286312333
    0x6030c3f0606040218040f2a020f0102070201092303070b0d051803031b090414040b090604030c230d05040602070801090203030a080606120f070912121107081905 71
    0x2c403140341900031103101e032007104003803072a040d4010140000b0b0900207801100c03050711049661525422902210f000c0c01241d01c20072607000070000060300b0000d0428070404140d004001d001d0150b600410311000311070846480007299901050252030720701c151041d581d0b050040c613800166844007003021b0700480074a05420001900c8400d21440805020003039113105420600c00070344450052000300c140d031500302d8500f51400e100c030740000c0d086640c0c2c0b200b00d91410070300400f40800e0003000e00d00940d1041d004001004541840d48014004020b0100001c020207580384808041801417503446101c900400200d5800b210314001c081c202c0c0d00079000d20001441852000140c0c1c2c4814080c40e805035801401847c40d1140c882822200407800038001500300b5410000a0310b0b112080503080e10a00741c034081d1040609008400400151030b96002c18042e9003c1c1500f84003054007442c1011000c525410455508007240070600d0802400f07a0020320305000700e006031055100010581c0c0c054903c6041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 286314829 1250 286313579 286313581
    0x20607051203390901050d0608070801050c030c033403060e060a0b1903110703050301050a050a05300f0303062e030e07030b01170f01020306030c3f06 66
    0x20f1001d122501214a40280e00c0c030031400094540d1407002400003000c18500203140020071920b0383c065800c20741c4203484c240c2c00740c00c082201d858203104041c0c0004001803281c1c91800c120406002500020745a00305815500050b0040c0344034407514580a402d4040000901210581000d402000c2c54480c40d60180e0300754000a1443c0340c082c1661082c3c503e1761011504244044e440f02014040e22407408051540e82d001001014482074082c0ca48c0a210b544c407a0798a41c1403c061113a060b0310b80e4842c50060388148010b104950710f49030070001046698601c00710a041c0d1814504403a101e0803d038000038000e00c0c035054503003d80480150b110b00e070305031080c1c3d024100060b8074014102c2c43c40c60501c40001c082e0710030304205200380c0210350011980c03000c0b9002d050f1a515152002c1d08c0aa02c1031040380d003010076082d40c071101400600d80f00e904a8000b1400d520b03200f030100c2d4481281e0300d0b0300307482405a03140c098000c0305800d130740425141c8000b8179081c898810010400c04611103190310440d9100c2c85e4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 286316079 1250 286314829 286314871
    0x60203060a0603110d0506130e100c020d05030411151917041208090304031a01050f09010f0b0705160b03040219060c0210020c040509030409060e01120807020607051203 74
    0x4c0100d682150083c000d5038589008411420000d09000c0c10b403030340c0b0010b04400112810b03814012000c03180d150501900208606c9504075046039903c502040541d000300b501c81d0030047d08001569446500700488098004803440045c0c03078601d000c10202407155012a5108130305080c0175440c4408201030715010316083e40d0010165080c601110000d00c9407440340400340007903100b03400442d00040321703204990920347c4aa49085000c0151520200b15281a2004101528200c507581c039100ca019181d407110703541484620040c030220b03802071484140002801c0301c00c0000c2017006a00381540e01c46151446600e49078001c002d90700a032400d912034030b104070b40c85110760320a1a035981201c0040d03c6003441490a03074248101c030310401503008254001c0b1142c00d4040d407214001c0034440e111000195503158100288641140c2d2150003000b85a4442401481400d81c241625800950800011601c40c90395200242e90f9102d4020003c05501400c01c02009000005016500404e0503041c0003071084081 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 286317329 1250 286316079 286316081
    0x2a030b04110705030403081c140f010509070e150d020705030a03060816051903050f1006210f081c0902040612050d0f18081501060302030402061804020d09060203060a0603 75
    0x2c01070641d800410003040012102001482e000411403450150901c00704980c1d130807112980380f11807445d18050104079461141800301405000304403111600b40c10a8000203051090140786180591000780c03c03040d00020700d0040d1103410828503410343d952030007440c0c207980302c2d000300760380d50003003800c290000c00e03094000b1a5501806406505020300c8a14100c10009496601d15804145005428003c00407580a0081210740c1804000910800300640003000480c4ca280e4404c0081c1c818131200411044000c1e0018251603411050f4032400b00c0b1141043d8015100300403c5200500c1085261101c01a03281c0010507080c1c000c40b0704100455444417a00181d00c501a001845070b040090508209809508031454201c507e1502030810491758400e0002c101ba5a004007007994032440e00e1004100407580010b002d402c2600d41581141440d5000c03444c540101010b111065040240d1a41540c540d030f23040d2548050a108140001c44203814032500035481603039014001d80c548030012032801e0007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 286318579 1250 286317329 286317337
    0x131701020406120b060d090b04050c0a1202150c010513030f0801050907050c0c060c16090b03070e1b0a09060206090604020603060f0102010f0e010b0a1707092a030b0411 74
    0x1c1912100402c40c070f4441d0703110007071526004840c0c0c000024400d00d00d80409620612120500c160009510f42c24a1306141385070582d13043c48684078600c001000d10000c5142801c20382001d0381559410100c0c5a1804843c080c0d005140b001d032160344c43c0404000c00000c0c24a240c400c8580681c41da003039034240f1000c00b122580f174240152034124000758085607403241303d04000e05d510102403040d00c0b0042e4200000480562208080391076030303404401c03039201e0180ca590030309000780002c501c100300c00411034001c20740300c0380e161241082100d0381100040580440f0740d806060925186e030b003565a5107081d10007401c501e8842c0142001171083c5000145414000140305000f56001001141195100300401c403201c8000714081d4115501c900445512540398011411148e4000001180c007044000c00d00500c480341c0c0c1c0c00000180006030101c0178403400800c40c3c0e0180c1b15403003c0401d01c1600c00ca03034284000e41e52044040c1c000c46110340d040c3d91980c9540210402e040448052102e032080c1c01007000a80130b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 286319829 1250 286318579 286318589
    0x10914030a0512070203190305010f121101030207050708071811091513030506010e011401081e060f060d0903030e0304240e090f0a0605100c03110c061317010204 71
    0x2c20030070001e19810180301594441c443d481128600400ca0419588102a00142c01c001c2a1240d0040c0b016030600ca5188000c0e2a4038170414035003072416181d43c602205140c1900f13061550010b2100280002130084801400c840d000700c913403c43e038405c540884100240d1109581130324084140744118010f40861740c001a00500084c000310ba242002c2c000c0d9488158030b60040c413a1840004000349092003c14001d0200754002e6280390b150000c005021030546071b20340d04100843c010050210400d00e0a005170901d204a850410764908010580501204924a9000b0780104281c03c02043e5504041c001900c40d513014000143e84031b210703d660380a60300804490040708540b10030b0300c1c0782100e401e1450b01f1031803411a0b408118071000c0b806286041d11400c15a03002c0a0030084081d03068010140184015622103045803030714400240769401c01c075002420004824070b40e001101007003010000c161030040a0940d6070074440340c007100d5071800d4810251000f0841c2c070325510582040c82540d00b01d034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 286321079 1250 286319829 286319837
    0x190603050c10180b0408010e030a08040b040f0605010e070906080709050603100909050f0d051c0213030b130b0105091b0a110304030804050112060f0b0904090212010914030a 76
    0xc040c00d410080d401216038030090801c0501ca81403810030381108401001032599000e021758407400c00305200d00b56401c05420070140e41c020440b40052540c0140c5080d882034000f15007446617101c038601030382d05410109001d00801c5c03e05001103070360600400201d0203042e45031030380254156580c030152440b20003141c1000124070700754020402400c00800440e4000380015160680c1925504800e007150080141521150f002403400b4004540401c500c441400d40c034100141041ca00f8401c0c0e5050340410a003020003a134010540c4115a00141c204202130742c5d03c481190690715051004019501c0c1a0b0000e88440380010000a180c0c10101007240c000d00301c00019440d003280c41c036150f0503d64001030414081085042045940c1401403002c1c001852040c0784180d0b66130300d400b000500d214440087c2a0f403c0b46081010490404075001d1181100c14900c1629103621003003000400501000c03801035000608040d1450b0b1105044d4000034255108016140c02c08100c241346031b940340507103000c030808a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 286322329 1250 286321079 286321093
    0x4020f01030b0103020702120a0218010e0106030c0309050a0b15040608030f030717090616030b0f1203090d06201201030b0c07060212070f030903080f131a19060305 72
    0x40d4420740050910400c10f041c05444c090107a4003180741408a140007001d142c10a803481c0b000c40c07030400b4031b41e40c6102c540c01e1502400c0d41061110320345508188101002e05036603a808281c0907000b0b0300804441a002002d031428442c0381d040540d210442107903030001805105004103c180703414860f40050b5001003000b11300b07060017941c2d040115800900240140625490159246419200e44030302c40c119600107040c2e0744c10f00102641d58488649904010300d410310720f5054454554030b04102208404803143c1d01400410840f00b4150f00c20755101c2e64005002e24014000d201d641c2d00b00c03216085112a05188125080c0c0c0001001d010300e40c500011340b140031004001103030920260070f82000c034041c1520301e4505075956050481c2e0152603000c0e0000d902c0010031800c180c2007d500c00308003034142418000729916643c01014810000c0150400b07156400100c2c40600f140124520010b0703104c1006400c1c19142020a0030646003203401d480028101c15101051039064003030942141d60040090000d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 286323579 1250 286322329 286322359
    0xf03030105190b0313051501080303190609020d1a1c080a020c1002010f050705030106050406050c1903090906060516030e040b030607230a0f0c0507080d05030f09060402 74
    0xa18074503114000804942d0040441e4103184240218012018101c1310340e9041c2051a046081070510f06126514240741001009080e10100850b54032001030301007610080c03898008140200f400e0742101900714808243c2134007151607070b441041c44586042481880001310000c00a801c907210310b240c86901d982c2e0022000040e03040f03016000040060042c1d500940411001c100418424800e14005030744800f46040200c00710701c100d50708000c00f40750488c5158102400640310388140e100707aa040113800a6605200c40e4140314100b40140301d500c00c04610801350900400381e901c80d01130383c01024a40000022a240102d04a4210049100301d411001519880a49103085c14409050300551110f000c0d10440d6003c0c0806071040c100c5132100c2244080d40c20191030045980258014500030410a05030410f80107621010380802900e007516100c496441d081d0309020341c55022440521400a0035840da80c1c00a01441c49101450386052035546c1d50320020341d03101019036001e03410414069540301 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 286324829 1250 286323579 286323589
    0x50f010c022808070303020304061d0c0f0418060e070803090a0501050307021501030b0711010504112e0201021b011a0613270e03071e03210b01110f03030105 69
    0x660b00c0321200c2d40c02c468842e9454040341035000940840009500108020400c03546102d01da900e8460040600c508031401c04020350794940d204181c5104080c4802c1c807540d1079896400c080785410300c4901e03003000710040f440c100011f003d40c0d03400c00e22207014500c4d010a04a10000c252800240000d00c164071013480c20005559680c0041c1c0304074114010034000561441c0d112101c54001c5100b034180c0506461710343c2c402045441c1250a40350705034100018813011415030805402014421100000490000c00c0d00d10300400c01c0451940c42c1e8030302803c411210540640c054100002d02174080c0e042201200a1342c4c0c200c0746092825400c8400c01482604103040c428003400ca0382800c2510b0b4458952a442d4070486103143c80d010f45088854000700300048026801003020142c10040114241541030b034038000d5141d02d20307841441c40d038000d4040d1014036100b00c103c520340c8241420b409003689901210b600140460800c0580891015080c0c0c0440e8400060b1000e81410007801550440c0d0030070040103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 286326079 1250 286324829 286324873
    0x61501030f180f02010905010512011a070f05060109140402061803010e0106170d050c15090c09150f010f0f05030c09061309200d0b0a170a050f010c02 66
    0xc0c0d03907542c0e006142508540d00e94a8140680030708100b40303803086584001000b51496421240c1000020700c00d40460346070f00c02c0385606603040d0074100d04041010703501428240c007480d40094065071030700030140305004000c0340c424140c0c0d400304018001c0e054034215040c2c40c2041601e000350080700400107200c60004c0710010101c0020010300224402c0004603080d825129650000040c26400410503101c4600801c1005501840ca08003241002010801240c50350700c0000240d200d00e0542c4000340d00b915083c004540982001000d2130014100200007a21800c01413140741d000e19100144036000350300803c403140202003545e8540d50750f442045001ca50b40e400c080c0c1440c0150700217200c6404980d40700c1c2c003d80202d51407a0504140b0300d290030b80c0c5100340c48140700c1d90f40c40c210170110a1050011800c0c200ca843c0b1050882c007298241240011456401c0203511040303404c110000c0d40752034040003080100c0c3c8580108101e485150380090250b003202c45540d203500140e03010601e0b803032108040c06484 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 286327329 1250 286326079 286326101
    0x8090607050f0a0507142d070501020a02011b020411030106030c03050c0912120a1e091203080c0c010c02010608013806040806010602100e060402010e01110304031707060c0206150103 80
    0xc12400a0f00b51406854000e680e610300d000c8240031087c1c030060919038542001d5455020000702240b03480c1400107521034001c00ca010b0304005115000c040b07082c10041800070601d501410800c800380c0b240e118a40700350020f000301e40019080c2510a001c5501c00c0c003a45014501503a0b142e442c001c1c0d4001042200d84c0d140c116244030380030f41d082400f0a01d00c0c0001801d1203c1c1d0648034404100d5071540145a561380060805081c8012000c06014061800521141c400d505081c4118903440d481d81e200910f02922000f41c10944c02c00084440c9681d064002004540c4082c1c0244400081d1065101d400000c030240244a560013407092030410b003401c0e036103094140010304550310303258464084c6400e01c5001d03080341c40584d001d02580d0010b00c03258820081864144d00c0505402d042660009004203130100d202c1f810441c441c2a5071031761000600c01c98000b19841100d003072102c6102002114513403c5098251152803804800c292014004107501d84994803803c2c01c81441040c4400640c0245003c07554 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 286328579 1250 286327329 286327343
    0x80a0201091d2d0c040e0105030d0f050901030e1b030c06040b0d0b0609030304300302060f19180606080a0c09050c0d050132030c01050c190308090607050f0a0507 71
    0x4403043c0508601e2014080c22001d5641e5544905041c612540554103070b2182d4003d80c001c902102c0c035164004407a2a4108c0715140c215501d08501d00100c2c040c00d08400102da85003d00d100700f4401400300c4041d100d280600b0f0b025038190341c00750000c124481c0100d2281e400104400c00424180d08119446018200710040210b03050070728030804030385560019040a442d54500c6041070705605200d8017090b1420413106e00741400348a0740d5500940380c100c068036030704907000c0700d102003a2512080810383c007840e514101c003001080c61040e00324585468000b0300381c07000c80c501400801c0d200d00216000c0b540740d4201c0261000740345401c0c01c400c01071400070460707516020140719562038010103000d01790003801d4101d2100300071100c1e01c0c410340c98640c1c003089030740071602080070084543c0c0700815440b000982c2405d055403180c0701c41a901e41001424455402032041580c0b920042641044420b8059200507080b214940e03120581512a44600d461106046d807042c0080c074010f910030002032840c2031043d00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 286329829 1250 286328579 286328641
    0xc0f0c020f0411211b0405091503030a050d050903040e04021309050d050d0b0d330204121a010e0402060f0c010504061e0b060f030c1201080a0201091d 66
    0x159509040d00142070101c00121301040c580c0e440008402e606802480c85000580a4240000008118071551148a010341d04000004030481001c2d0490604403201070f0950359586500100107206a011300f040100c03081c0f80101184021100000380e1b8182c501041c8040681e840d03e03000c000e043c074002134032801e8960315800807400007682808106d07210b00035602e9144e205c56100600200b62202c00003994080c4510050b4000071524000c0301c0c0c16a0601c0342101e400c0c0301011460821a9580041001981c2d4000030700007903141c0c902d040e01907e00e03000f10828002e25000040d440c1c081c2034203119003801c551101000c5009403038414000c8c140951405c008500e02690015081c0c01e44404071419a00c1503503803a008050384640100c65010400141010000321043d40006400e07030050410042a00c1008000581d80d21502001c440c1e4403880d555940b0500c0da9134456040d9240c1101004a00103940060300068060b0011141b44840700c112207002101c2d038540081038043d8005201c00f05021508213 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 286330935 1106 286329829 286329851
    0x20c030d0f051302060a0507020415050901080304140f010e09070201090308100b040e040201020c120a1b08060403030905010204210c08060903030a050601140d0e010c0f0c020f04 78
    0x15010b0b9255200d04100312102e00231100021740051801b00d47d03004000c150320440381207400c01c0702c3c102142d0381c03030308410368490045d0b205500c6580d0402038047c0c01d91404001d510143c01042c500140000110000180003440c1a100240941d668105c810705042d40300340c4065102007030030b071088801860b1400e49005446140303d10815803040f20301040c11a8801e01800e101c90300c0040c401e41540f45c00c911015291544c11070112200416403003004909520105010b0880d45080c2c041c00c0713190740d640c5099024080102d02240c2035542003202092094103480c0d440700d042000003030f00c2d46100480c078290010340c0098100b0f150b40e0b480a0100000404000b044039441084c0c000c0109c0c581d1990001659181152000f0844103040864544485070040d4001c02166050b40002c2c0100d032081d403820364042c0d500506d04c900080700100700030b0150500c000307440d400042c081c10006581041c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 286151079 286330935 := by
  have h0 := BRFrame.cov_init 286151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 286151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 286151079 ≤ n) (h2 : n < 286330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
