-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1360
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:34:06.668791+00:00
-- url     : https://prove2.me/submissions/93ebd29f-d802-4ecd-8aa2-6226781fa3f9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 244424460 ≤ n < 244604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 244425710 1250 244424460 244424483
    0x140103050d05120403050d090f060b0f0103020c03030703090201021f05041505070e040b03010f111b0d0e01030207060b091503010501140109050f031204030c03060f0605101206051002010603 83
    0x302100c035030080002007483d40d450500410000303801980a00104001a01c0000e0044041e8403900f44841c1d90300c005076803180da184601398181c205440c02ca58400c4007800c00b5480c0040c240c480303981e280b100904841c10150386003034000c00c6a20a1290075240036103455070030310b40c01082150400401d001d031000c5030502030500404400341042c1c080d140c072554041c0c4560705030151f86410302003d400c004030340c3d50b49950b8071071400c080300f034040c40760700f60844601594070388134080d854026003a240003a0745c1504c80c0d4410120101c3c030030743c0468034801518080c43c001d600c446951820310090210401a19403000711842008608000c00701e545e0000d00e4110002d00141e680d5490070308500310140e0110b4000341c2011801d0221381403800c0c0544c2141809001c4032189061100c0c507500301c0d080340d0011580301b48007440400c140200c5d0b007c0d166203508403000810000d031500c0c000070b1025580c550301205014005100d0442d81c1819402031000344806042e582c03d41d642c40500038001d150500040380c0800d90b42 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 244426960 1250 244425710 244425733
    0x121207090905091902030f0703080d110702060d0b130c03051905150d14010c0c060f0b0904030804020a0306110a0801171f0204090f32061e0414010305 66
    0x40c0a41070043c001034001d00304103008400078003044441003100360b8046c4158080b1511060f01004160019401406c1098507001d0140c00c620903110b02810700c0e80440300520075000035035525000c60303048191880c0002040b54803032003c107190144100310100414a440010981650540c021501c10342107084038884d140521034100c0c045a0050700d2940c0200780b106080c00c101e04016000350a22402ba880c91101001002241401c2d03a01d907104490002d49441140420000c09004602e5403807402d03241401003550101c0801d0701d04100400240400800030040750542d00c0e100d0b03a09018503003180080c0104a00c40d41502e100d64400302414001a0140c00001550100016001c01c40c801e1200a0020440540c800c58100b0300403103102c81b90319901300000190188940300b1000489866180440c8001644910400e10043d50444a41c40f0a040e00c40f40300c4007088860481d84207200f15088600561032400f112400e2034800b46450300540f07072021220500300c0305010941243e03c180200c40d48a40c24 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 244428210 1250 244426960 244426979
    0x1306051804020a1205060d080904022a010b0a0803030717041109010905011a0f0405040b06130e0103030807020f060a0c0215010306050108210d0518060403360b0c12120709 75
    0x1c00a403c8e50320501500c000c03032821384c000700420140168481c0101d0f60041100d01c010030945d6241116a540c0c6403804100d007003c443d01001466224007650a600e008030028040d0008880700d1690001e0b810000341c100a41c0c9040a04955005411200c41c4e40c0c440c41020001d11082c000d90340310742582000d22013242d62040455036880f400e14202c1e42424a84400d01c0040d00d89850140d0b0b0112051040042070001e0360312b410001d140d42c9110221039450340c24050400c940c06040e001c01c41d0031150110507110030010780b5680200c616040006d111b12000c604070306003c41c1010f07980003020795000001c14401d10303401c100d042e00c41800c2a604100a0796605000b40503812500011090041c010341e94142003e070302503540304c042d00304000c120000d058249410200211411404101c003250081c044000b54201c01400036902084d03039000e0080510714900c501090311524007003400001d4031004601d02404260030320040e0240c129250b000d40d60250820081c2150f810f80050403030140007484904 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 244429460 1250 244428210 244428229
    0xa05012103021b060702090f0a050601170601141b03040311030d021f0204030212011407020105060604030f1b1805060604051f1e02010f050c1306051804020a120506 72
    0x1c1c190010508030302c0d1070140f1500305901c400025440030040c00070602580301c1d041440d128800c28001c002d65031802e41d4650341102c0000e0891410460600c4503240c0340c541d99501c450b0000c5c0d09007400c038010b82c1e080005481c90712401815a4062411000010100ca0008058000e80e0312460080a0106001090540d110607003200140160300c00c0c1d03031110f55010541c050050a860508000d0724194136500803035107400c3c0e89005a00c00c0e070354606a103000c02c040075060b29000500d0748004d20040c100800060014011400003800010f20099101f0030441c86850f82e0b025500b91207108221943d642c0055000ca401c5404074600690501000802c0703442c20743e040310151140213140303081d03801c0001140c51400501c0c807108014031151600f080d101c8a003003520029a000254008500500710344060029260007130021200c0b10700c1131140a9a101c0711343c400f030003590018900240c030341d1240f0b1219400700f08a024042d410130710001c0c095080c941d10142d43c071a9042c00d5002444a500c0c1c0a003070100001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 244430710 1250 244429460 244429463
    0x9020304030806120a0507030b1f0509240d0812010602010606051602012303010f0803040302030c060a1e17070203090d030e040f150504140708060d080d02030a050121 73
    0x41490001450b940703480c008a035880300181040345c20000b25640c4162070280c0300d400903101c40815008121110355441c501c6007d150450403168036062910000c24030841d000303402c2c1c00c070f101100c0409640c88010488009440d20004003023090360701c80740c245400d01d17a2020200009146881c40049540d6005004100454549980d41c3c0d01e091b2080c400e92155517403140c0c1c12810040c3c03050301c0032409101900303000040020300ca0300a80d254585042c022520303a441d40081a1f540003031008101603a00460030500b502000e45030713640e0380c40d036500c001c42d5000000d01103604000c00c4001c2541c2c690ba03008a0042d400f199410480340703503844080c803da0ba24040c401245500c0301c66100700d4000030707100d4080f5004520300030f0b202052140205100340142c80c20000050840c41500e8020401454203001b6643c02003c3d2005d681003034201520000c0007070070028011400303003807042401c0d410420b0313882c200c9513403601300041151a8100300c100c00b4040c007428400d0700811b071611000c1128418540a01c6010f86 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 244431960 1250 244430710 244430717
    0xd0501090506062d0c030a0210060503070b09062203060b011b05060402220608151003031d0d0803180d0504062f0a0c0303120b0904020103020309010f240902030403 72
    0x21261401544100d6201135051014020103000c0340d100003000704045c00d030704850340e001341034290122841003045601650010b0300c65440071800700304099149048034001002902c849907282d035860701ea05148402400d6904402c0001e2a00105020151341300086040099881034000840d4200c000b01d6036100700c9004d841c1e60400750100b0014a88000d10319003081c2c0802454142d031003620112004c403543d603486034480c5e420015a4503004044414007541c04440300d51082540c030f0541c2c030001d05190202032141e14441071284081c0300c0c0e40d40d81400700c055560141e41e0942e40d1034078490700c0c190580200c6030a4a144113104413a4201c501402c280c0e01600c40030380d500d210f0410742c1c42c4c0d03410504610400d42303032881551940d0318601110a00c001840c403030040e2810f01c80e107460751400810906440e0403900c6014a0710001200c41d1b40c03000341c0303650040e40911b40944ca0752a4100000d0040560f9043d95104500c0c000300000180034814803d4141071140300c1111525595400e0031050b48021213004000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 244433210 1250 244431960 244431997
    0x181906230607020d0b010609260c0d14060c041409060306070f0c0b0403030219080709030807031718010f020304050a020108090307060507090f060c050a06050613020d050109050606 79
    0x1941401e038064145140000c1a6102c10303034260300e811015550a1f041880040c8151009202118001c90205183c0512200562143d845000c195445004000740d1a02c1034600f00a20414003040803100c000031640d0300d040e03900f1410b00c151307003003440c2c1e10500c68050600c20010040901e407401004291180380d001d0301400e203645e2411404c48804100070705110a11400146040111b120311010a216912039140165500d00c0d501303030701c4e12056450000c44100141c01d0100f000c81988030a0480403650710107034458407103a06117810360f486440283c0d00c1070380f440088200070944420f0306158220350304101c02003007080b0407400141c3c1640702c2110007901d550302080c0c44030010351041074016400030220007900c1c105555551000180c942c1910101d00140c0e40c1c4c2418001480504001e46c01403002e410704180e465065a101510342c44141006013103180d40702c00244041c0c452220300c1000e842081403c40d940c1100d040160001c250038007801c402c0300d20704400500d076818250308980c41e4500b807a62040b603 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 244434460 1250 244433210 244433279
    0xe10060302090315010308030907050a1518181d030a0e0f0a050306040305090108070813110111030706020304051005011d090a0204020324060406120b181906 69
    0x295114104581c3c0610031103112803078100b103020007a03020f0340c4154a56036407400d0852030186805250f40040f40706000601c02002207224050b05e017510341c64141800030102d82c02d203d103070700500319030351000b99030311b426a4110310802119031100c1400340c0b180c0030314202c42d1081165190380307000322440c04011611403081400341d4940340040c13030381d002001058072005540340c2012a050040555089000c25000b0403040c0c0d103503070011070895005d0302500d08903095181c48048102ca505528402030900b8406100c0d9598692054070380c160390b04040401c6aa44d0350381441e10500940c811103080e0b405020340c50600907001e0717050090030b040301d0701c840701500c0b01a02e40c400310400c0c40000d0803500c29441000180c00c01a00c6900107107120b405100c1e81c2452005c00c02a040203089041d5000d18031800003048140100780d04680c1c43e4070fa4400e002c000003524120040070903c81d03001d07119000d0042d212070b000c01490804104903404880d083c280e00b4001107603649402854110301c100d1000d4010b820411044 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 244435710 1250 244434460 244434467
    0x1006080a170c030a171312030504020f120d09050d020a0509090304180509010c08091902010c200118030b01030b041a04050318190b0c0a050f03130e1006 67
    0x30412420289410310b0195800700481c81c550180038040c001c102401c211740a0b035041c90381801ea01422080c040c1d41e10795004c0c0d40e21906080088170700400e2560302d9000c41c00707648802144203c0d060002e06811800049030305400da50340d00c0c0c01e805d20001031140c1c8001c60340d4100707985e5207030840d540601407402c20390408040018072a4000c4c00e40225102c18800040c94015256a603a001d9850303200029040c14000805401e4a201c44c4104007031000320380a001448000107800e055000c800314040c00d40407500d00c0100e074600d513031000103403284281607407140c440c5a00b5020201c0424098945000100ca4014050108080c80c400500000c0071040100041841c6907092540030740b00c3e40310840007100c10800c60b070f20075000355020b454a070304c0801c100704500c100d80c0e416140c07988201e54003400300120880c103656000c4a409181030001000c200c41c1c828610800050518a40c80030a90304c07500e0a18511560f00c0d00000596241ca100020001494101480045025491010000212608105007503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 244436960 1250 244435710 244435733
    0xf0c0818010b090c071e0804030204061508010311010c05100f14100315020705031803010507090b040b0c030702121c090e0f0c0f0409060f080f03070b0702030d06030b0402031006080a 80
    0x40c6c5800d40006500c034030f00354101e026415898482c004180d12241540140b2040b1b50f401d41065014451a4414100040d0005003090440360300402040c000082c0070300485035003808000007030903845924214a030040550300002044440f05038100004404034203c16040802601c00d1990241d03244010304c003042074442600380d01d05d643e00c005072130081399584851440e8014910440c5510050900081c245020701809401c04101d1802d4000c09040a0580030948128450441c049500244803009010148196000d054000708282c901c90041c00000d521407002d46880141412144089aa03050158084505850b800e01900441d541c803c0070100805101030907028440c407090200c10807803014000280043d1030714072030218016241c100110022400380c0c110f2120b54100007415044403c000040d1001c450b0801c1810040b0b854241c0240d08505c142c0902a034103904150020042c0300140d0061801144240d088a07000502c050021b01180c1890003220943d404c007d802d00b02190003240341c07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 244438210 1250 244436960 244436963
    0xb220b060109170a03090503061005010315050a0806040605060d03050a08130b0a020405010305011d0708070e150c0c01030902090c093007090923010f0c0818010b090c07 74
    0x2c0000d07100c55200342501d0301c580805080d07900c40b603070041c2015031010f008401001c09900400960610840b200201d5204e070284504044d42c900840f410b4031008141c0360010a070182c16664400e44403003440751605421a016110303c0e04003c081002c4c0d0801c1c074040444140c040ea80c5904210b040d40007150840d801408080409a070540311901080c0348a24143c0101c1403803000580d507900d000e001409443c0142e01c601060301c4040d420503034650400c0d41e071540c4000103180281e03041d642e8200544022150a903140c0d000f8800310380a15200d10a0001007040d03d10000480f200c604150004405489200000a400020b000c01081000d6240005050b1101000b03101c5015a501d1207072950305030064103416204507486034041211070b003003404201c0107801415010300480340d0303a444006810803418000388000c0c1d03080342c03070803034034034080d403125260908003001032000500c10b0f10003c040c10f101303039806680400c9003a40400c101905115414118001400a03a001d50f130794003140c80e654100020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 244439460 1250 244438210 244438217
    0xc030f05100f020a0e0904050a080322030206010f0b190305090a0b0901091a010b12060607060c02070314010c140901110d050c10020406080a0b0301061e030b220b0601 73
    0xc25281c4021580200803008091010060711000614401001403851402181c0106140004d1002140300864664000d40e004070000f0f58a440b0103c624001a00d1401c01c818502d8400301039400301540841e00034120b401a41c81001c929031120401d8082d4441c072400104443d0001003d2001280241c101c1644200407006031340b107102058541c0d11480c402200c0415050759160b03540e104001100f402140c3d140e01010740c001c10f07981042040209445a6281c82c0c0125600c4000204a0303078510f011510003550002d000d1000400041019540308245e01045804c2030040c0d502c0b0021000c1403045040b017980a0b654506060000440c41c055076010089080c10400000f06e540070310300e820042c10352842929912295540c590303000050130b10070014800c07205240100020454113a01159007030b04813100600c001500110500002d004000c9940100501c005080b554440d95070050300d100301b100c0c01078100148683d540900c0c044400e20015020740e68480c0c1c4801c500c0803075400b01c149a4000b47c10304 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 244440710 1250 244439460 244439473
    0x315230424030f0204051308070327030b0708091b1509030303010b0705010e060f060118030b0c070606090501030515090a0605190b010801062304050d050a031b0c030f05 74
    0x103041c020301141074000366044107003a1202401c41c02c1c94443c6585c41a2400b0030301107a03e0030b540e100c00c4944a00e000180070415074021050741092540045601d855010b03070241029a507900d00b10b10301807401c88200d000320b00242c00044410320003203586000054848041c100414400f810401090a15940d84090185c00d00203a001910104029030180c4184404152a803e640c5070040c2500e0b403180340300e80c840c0c000209000207031a000032000e801400c01d00b030001034070208803000140c8000c1a80040c210007141d09c04d004414042000030400e80e40501000d11215840c0e210820a590003840002c0056200c2449001c44041d0821800d400c142d4960a072007462480d921490103444040c1c0b84000e400204000c040c00000561240161240082c24481c0b0706614280001c0c1103c11000008d849069408036500303038030b4030f0f00c07801c98000e0305d4014440c101080721070410541e2180c415400302c0c0414414085d141c08100c000c040700d01c000e540613590481c89411a0384103e04040c100360116103520655 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 244441960 1250 244440710 244440761
    0x32306061b07090e060108100218010f0315030c0807080a051908040b07080904051302030705060d0b04050c0d150f0b07020d080a0e03160605250c0603152304 69
    0x14004c4403580d04490008106650402040604200310034078491440340c8104101c0b056444c0c074050940b911002424000c004520342c24041c1d02400160021414040c0000e202000700039415844a00f03640c1500d0880d81030326100c601d4a81e4614442c803002d003c9601c001820304400714550052225140b2611255007410f0303488003030020f03641100c08200d031259004100300041d418284038041e4806141d40c00c001c8907d055401094076402d0a001c0c86004240003c3e009045011640021001c0ba8010303104000515184031a56030359007166180080310350600c9120b072a00341c048078010041e40c801c00040b881c5c1510382120b00c41c0a0303020500032a045000f0a414001047d0048080c0c01d6500660301d0303080050302e40d0410581042600100e48941512600050190030361050968a03484201d4109680306580420740d4a010b044d07a00c40180f03080c0c000c200c04280310f0342c0340c0c00c01036038070044624421415445140320b050031880304182349071170b0032141031078519440d00f17800c40b104d034010b039102c0c1c640c2c501c103013 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 244443210 1250 244441960 244441979
    0x20309100815150d05070e03150a0b0d0203120c070e090303160819020c010905012309010603030e01050307030b030d09140312070f031e032306061b07 66
    0x1501000081003000082140c040c07082144034440002c102d800305400c4a450301e100f0800d0107513440d010b00d039640d81c800240f0303103070b0060075100402d0000604640d00b4259070b409904034180d04441d148251424007000d00d142c1d080c10b14005454603401005040c14000c0b1441c00700b201d030062035010030503120f0f203c400184048036054460140300c0101c080c5a8a2800c5020300904182440c004400c201000003048030885003a404e4980d03a9680c40005a076a03402600840e01602411102030702a504c2c1495407c079000030b8500c54100c00e142c1018000e155540d00300c06034221600c0d448060003042032904403d4032503114070011603005681e400c0000d20b0075601c40210b0310304030a9240100206054030b034284002040c983c4607901c9020110000d14043c0348003914205540210403004081180e0b41c10304008140c064200120381c0c0580700c08908040e241c854000740940b003580b15900c00320f8420001f80d05401540428a80300ea003016040c42d00d001c4d84440f91500040f004845a006406840707400b0503400c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 244444460 1250 244443210 244443229
    0xb04110603070c11150313030210060e0708090c01050a0f02030d0509030d0f0e0d0c0212030a03051006030b010e0f120f0105090c1e04020a03060e100801110a0903060903020309 77
    0xc580c2c0d21050043c803840e04407070402c140c46800b0f01c164068061041c034541c1e444212070340844071500a4644040526007070b882e02141001079610141450700218100740780007503142c0f099200390740720341050f11410203035030310346043c50718060029008000705035543d406100803100040451044034607040040390310104888040d1820300c0c9641000032161141c0e6110b005003440c031150444204800c1c2d0303040382e24655800286100300700b805200180f200c2595250b80d0701052701e0b11024180c80c0c0c0d94a2203000180100404c480c00e4459603d01940455141c1c400e01c6209100941a11000441503110040200c80101d43e21129404110740c1ca00405424041c403603090f11415000010a6a0400c8911300781030181403014140201420007101c07000715a0307a656070303042a0045d14016580e00e466181140500000e0f0000309441e038011050105920b40c500b03690081710110002000004141c3c3c044011364407034140303a800020040341c0c080c00030502983c0075a8401e4402d004682c900303444040821801007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 244445710 1250 244444460 244444471
    0x30908011404120207060207051203040b040807061209020117061c060209120613060e071a270f040b0301090f0c0806090a03050724020f1309020301080a0b04110603 72
    0x405010710003040070f511441c07000e180795400a41041814000002c0d940d170a90311405115554081d400b44d24100c0510454010389001c00c4d00c181e8480e00c4074041c9984100c02d11640000454204d0311281e403030414480c040c00140e050b5540f40104070725103c148080000a41000d601c407110303804014041e07000e003031020810380c410b03440943c1300c1001d0f00c10010707000c19002525505401030b5041041d80420810099044c5600490004254503521105444e00025030007566144007030000c2841c4003007480c40640341c0d10b0004240b4001900b4485550510009001c0107aa0060802000300c1d890f4a015044610a8200507000048450080d11003890414074200103441192220700288036040c1e060044651003a0701070010032070501d0790740c0c1c020701911a021019103001010200f1451400c6958400c0060441e014819074440c1e0401e04121956442801483c20030701c004d280004001d541802524101c40a24000c0c1039040420b46500c9080c00300140b00700c5059507150100344481d51040c001e1030080 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 244446960 1250 244445710 244445741
    0x1060504051e06060408030708070602040e04031106180606120a050d210c020d1d0a0f150e1305040f08040b090f0f090402040b13020714012009060703090801 69
    0x5482c0c000e0a09007100c800303001c441c01800100814041e80c0400000c40d0b9140d50702908103030351900c650500c20b00a01a94002e503410194034414001415480502007089140503401c0d50301c0d64540100c62130300f12100000c0441c2940100e000111540390541a591100c1c4000c81a100b8046c80c80d680c413420700c001c0d400b00c400450001c01c00714140e1001030449900c02240a102080359140301e000207940e91601a0307000d4100102e9035040700c803c0000300030781c5600c02ca020302019889030311120500d101898500030a0540f5449511030300c1d040d4401c00c400e4142420207442d000da41d070440080000904402841030380c0c1050030324900000641494024402840c070b29826a0703e400c021010031007048140e1030901c4c032441d0030704c800341c0a50352510b400ca60066412a00021021a0380000c258014103070755030720310654408281c0303c041c0b10f842503400641050b0440200710205008003200881104085450303c6100d09005141c0c0c2401e10400030420180a414001d609980c0c1d103400d603096a10305502810705 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 244448210 1250 244446960 244446991
    0x50a020f0613140a05060606090d230c1e060d18141002041d0a0605030a05010b040b0303040807060e210307060c05030606070213091e03090608010f06080601020106050405 75
    0xe22200d42d49210034480b12101a00130585240c130740550340c00014004500c0380400041503245980d407212130b00758031036011104100ea1415002895a101c401400040780c600581102803141d10b0325020300e0008095607050700001100c100c003400001d4008100c059840303503039110b040000300c003014000300c800c0d8030954140044250304c841c0c0c941860504451040300500500040c01441d00c080400c2500c142089062078840c1d8602560728050400d960200f0b405000d10581d4809011041d0480d141e0f18005850900c1501c03200341c149613032840f451065501c4c030b40107c8000c0c051584100301c11104410010007500c112681006045030b00542110680d4541e48001001000c0021034010407551600c9402c01c3e504500c2d04e0008218540b00d4040700030f201c1d100500a8007802e8030250301c200c030b00030b400070149501118040c846000031090020709601140f210355000071a14410202c95041c2c030030703030120014001c1c90140309998207000a841181595207826000c80d054485219242c41201c601d10416803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 244449460 1250 244448210 244448213
    0x1209030418020733150f090b0f090705090315281b0503010312090305121312050c09090a020a0303080403020a0609062403050c090c0c03030708010501081510050a020f0613 75
    0x40b281c5d201032002d0f0f80486940c0070405125002e141e42e04640c0040e0000c10901c0f40c1d08002a81c46c0e60b49410f496010402c0300074014030307030341c440080c000d0030605a04591007010b00c0c0f980991030341c5e8210b90383c544d80c545003485400030050384140800a1082800b000c500b00701c5211b0b103d0071110034110300900055000c0010424403900300c0c1d1a102504550801100450560300ea00c0d8446104040e1507068150003d0706560034480c41c03d2031002070403100d15464500e41145085d9440d40c01043e0b159204481a10225402c1d801c0411403543c207070350082032040303120310310398081c0c550720802401541507005102920303001c03940c203000c0c002140d48038410004005160003800354070002e0590324015000500401400003440c001510012208100c0e40300519139550700362a9064401c007519801103000100501000c10340007008903040c0d40d02600c800c40103603a0003903408641c034000d20031503920400c1090b18500c40346c001d40c000c00703207000c251066800100900c10110319048003940c411540f08141c0d800c100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 244450710 1250 244449460 244449563
    0x15060504090c0306020f090604030804060915091a0f0304060e0601080c0109211703010e010e220201050918100e0f0f060409140312090304180207 64
    0x140680411581040309240c16110b40d208400680001016180c0c001580e0b03007060111004d550820b600240503555450312460300d10f030142c101c2d00c25080810369040000c10010110310300e0b541146400e0390b0f901d50985c0b034083e440c00701810000340a00c240008100382c0b0f030800c0024001303500c07587c0103010106040100040b00b170300d0440e050f07004100d0303500554941c0301540c0c3e01103042c90480c1c052244085000a40c0d4040780d466101c5040000c2092810501c854145008100618102c0d00b4400309482107030fa8918001d0136540741100c008160014104031500c1565014020540c0c45006140c01c50820850f00045800c5c1ca07454800c101e101c0c50f40e902040300c140000800c2e8005007540c400c8000c0741d81025816110201c8024210307000c05581c1ea0006426600d860b481a000b0744c5d000b206009010084011003616503000b48400c50303080b80e038900010806400042110111429104102214480002d0040003900903c104a8645140c00cc2500c000c5688000c50040407020340081c3c030140c4007400044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 244451960 1250 244450710 244450721
    0x70803040b101a16051501030b04050c0306060a030b15040f06091b020309010f0e0303070c15020a020108060402220e0628060e041d030c01061d151201050415 69
    0x1000f4030090b0724440c8001026240650f05121661603514100c4c4c22203140040c01c0c001a03017850300f02d00752940000014001c46000c07807800b641c045c0007074481518a043c1803540310303201107404503080100d01004100052581080f50f610456113080b0384000c094010014050758090038500002540760b4500b48540b2a503407245905004040710f81642910300c0e2030010b0b4480c01a149440d05011405c410040390b107014000580385400300034181d1380d5401d914608040048114001c4150010440c1c4034241441d000003078901c5141d405841e26202d56458008000103580408a00b0489c20380d61800203400020398550300c80a092641c000040c240341041c1032249450410b016040c030030107441901805184000c411005030f443c00e00e800345140b6540d20106001e040405021603e03071410341c60f035401c050740102c0a4100446910000d2240c0fa03941e01203c01c1c4030080b100c1240c0e2420300c1a0104c1c114400d03503a00103d03001c030040c01c1030041d904038003c854216003080b01c0070b07206c0340c4010040013608465071041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 244453210 1250 244451960 244451969
    0x30d020c03011125030909150e010509130b0907050a030602040e070c0b0402010309020d080a020105070f02010c090e070201061a070c0f080a031419181401080a090206070803040b10 79
    0x3400c2c04d09010690486400d403000e0498a41c1001d04594041414480e400040240141e41414000030350401100461201c6c6842640c8419134090000b017075074600503580500036000c00303030415910f0800e80c81d00300d51820060941541c6104030000047c1b6621a10003c80081d8002c040c010303207503803420800f2400b0b02c0008041604100c4da1100c1040080c1710030000542140d02841c00041c14180d61000c600c82901a06015214201c0403410000a0741c1c1500000d1007844243e40310301051600389000d030f090b41e8556400c2030100c0c08800060044042007408190300292503c00070030f056554140072a42510b50b140c40d07064209001a01c1424424032006d001c000340b0500205c2e0102620b1b03d003d00d40c5544500c2e10003810026184006109014060180c482d0300700303111075040741401500000b8180b0303007800c9601c00741810800e8001510002140d41d400120406850f005050b60390246000020b01500c00300300d9201800b400740e4004169000c1c050b40c842d91250080d40824102440c1c1d40c0700340c00d1f56500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 244454460 1250 244453210 244453241
    0x10f0f051e0a0b040f090606081f1104091b02010b0a27060b0a020703031103030f0705070606081f15350604080304022107060f020309030d020c0301 65
    0x9001489140c9a180c0125400c0648151010744824507040b02818612040c2ca5000382004c060400300381c550f42c0118000e51080c0c03000c1090503510304100b501d40c101d206416268101d0f0865a02841d092a00301e03c65800400046901e00f613200d946810445250342e04401007010041200241590248211407542c141155000482c1e443c4c0010341e40e0a2000300481000314034050640c41d40990070760030840c0980400180707261100001080203559a0721440b00394001108803600020b8050040120703401001100220b0381c00340e44050098550b075000c4881181e015685001c001000ca0040c0400c0450703085e42260030342c00c0481070f2040c0c81a1080705090590504484100b005148035083c42d01ea04d0104000194100b045424000c1c540240140206005405007608020801c5500d0780150b12980c0b00701c0c1da00c5610080c00142c1d803061072a03541c4404040d4010f140901c05030740140c8050002c102940304507440c0c899446e0101c0d00b061503084011026a20401040e11103180a000750031a104440c2ca = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 244455710 1250 244454460 244454471
    0x70c060503060604140613030501270507050607050f0a05010c0809030a02100c03060b0f0a1e05161e0c05030607050903030304060e03040e0f15010329030c030d02010f0f 74
    0x3c400b4460344c80341500104031051802c281d0303100c0d403042e6921491460506014680e41c0d0a041c0e0180408422100030170801240384c440a05002824002d01c40d0008000c0207402c3c02c00381400701607409240141c4942c8521813041415903010001040050300c0382d00046200d046025014020a0010305a8030807600706005488200c2c2d40010130f10364107402d890f408542e8104101c015030041960780c2110010100004010800c0070396480123048501e06960b460200702c0000400c190b5000b502e620035400034008200346030154910074030142000d405180c4d0304003607103254a2001000904940121030706c0a40d45000c20092030305101d490b92040003804c0c09450448110002500c9100061004107400c1d6201c0c6206100401041901c01a248500340038501e0304100903000b607d900c04664203446000400c0d0b4020442d48280a0700f140803050a9908180111500500c4a50001070072a16010311810501b189503550411000d5107040751034000041a0b240c40901d03d00303982103101c0e20b020103400e29 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 244456960 1250 244455710 244455721
    0xc0c03120a0c020411130306150803090a0303030b010302130320091302090c0c2a0607080301060806031c0509010915021507030f0603030302090306092e0209120102070c060503 77
    0x2040b803141096040340d00017656a42421200e8041c068084468004191810013004000c81d0707500411a40c020150b5003860a9507810105560303105002c0d4164001a06003c10000039009400403c48003105040c05802c03d80d02585680304804e8652003510013642c2606080404400c900d0442c0500c1420384240580e440d200300e0940d4907401d001e134020f0240308a00000b4000a9008040d241c013100b00300244c480314420090400c1d0007042d454a4034140c8840c407620761a540c6004422900c1d030581c000413142c01c581c6020025142a48000c00302c64140c01046190349541c0030b5980e00000c000d096844141d140c0941400060400005800002846000c0ca1007209100e800143c2c101810040881182d40f540e101041100603100030541c4038855802d080001c01059096009010252800e80032034103281e40300540380c4e981e54400003c0d60040f4108031034a104543c00040601d0544024a82c098034103201d00d0007040024100204940703480c0d5010901108002c8004405001411186400c03421400e00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 244458210 1250 244456960 244456967
    0x7030b0604170f01060e01030b10060219020325090b0306100b0f160f06051f0612020705061302100507050d0e0d0b18010c03020f040504020d110c0c03120a 68
    0x45010b03068096001c0e100041441004200a0300303240001c070000d00846541d00c2c1c00e400110300a000440e03044207280001031074584068181d00031075480b540281615041429240d16240044d481a07070180a40303000360300041085110400c100203250302c3c00300d4080c600758101c0116040c1c0d0282c54869044907091001169040c9a107000703880d207003404555a085149801825803041602c050260a88070286170148000100050505c0340260b8040c411707a6541d0600118404e0325400202c0c10f4060708806006244c443d510000b4004c086007401031070f141160f00c030689171140444a07211914040ca01302c20842c140000813070114909400c115080c01c40c3c5130f0380c403030f29014155202401c20256140b0260942c0d207410103008050b8020412410a00b08201d0809446c407000c51003921543c2010003c0fa000c0b0312038421660640c0d03040e8480c6007028200020400654041140604002d880d00400c0c03a07d0340741000100452880c0ca001080c8011503001031600344840d084440203145014005084425007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 244459460 1250 244458210 244458217
    0x21b041104151e17010e1008060726070c110121050105040e160308030406060e040807030306060e06070213060b1c0e0d0504090507020a0813090e0a0f031b080f0306010807030b06 78
    0x201071090341b05595200c006140310310075580310151503c02ca00900c200590060104404105250002482c800b40480071461f480f42c29216180090031440d051008918010081282200c052502904101032403412040708105440c651711116650001000b1a01d854400d004042404401400c0c8582061002c2500c000307803403001510807080040001c08001e05540100040d0118034031460190800d810100500e0700010011400b29140c14404030740903010f1546d1050404005217042e1030150302c0e034280408000c07031003040c018090b160000030551640c044e000c0c015602c6810404e403941c102400b483e000fa12203000c0751508940081101028840c0e000007201c0a4480e10100410644c80c0c4803422842c2c0005107a02620b04080800d20039004201c0040001c00c40d0050710b01800f107000340f034040c03d4544d902007100078400d0740705803072290010340160564414550202e001407042082619114a607074481042200040400410001c06603003101034144c0100440c581084400c0424000c10510710 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 244460710 1250 244459460 244459469
    0xc031b0a080d021e100612111f1b0212030a02100204050916050702040609060503160e06010c030c1202030a271a070206041d0601021b041104151e1701 66
    0x1510882100c00c0c0390b0200000043d85d4800c0b10100282544e0710902102407903070301011188060715000045040c0b41102c2d0006084200012401703542c4404202603501e0307202c013540c041e8179200610840000d41d071085400c4819a0b40f504c05150385807007002d4001d003000310414500522610600040c0225212a559503500180148148403200c1030003d0a482a0046200081d48141450b0021920050a8010500719801907085640301041c03070725485180c51842c0100460f5107007080000b070301584034440f0b080016000e818072510141d0030f529011a43c07180383c40c4017400b603840000d06070b1410b03038448034601c02d8510b0204040030301201001c4100840d400d41c402d42e0000e503000c60140618244500854500c50f60060a00307540d1580c070b5110304029480a4404810119001d0000b0201c0d4000709003a0343d04000d00340c1a98070345440300f0400004242c0c4403482c0c21000d2007400007088010a0180d00100c481c0d01d41c48407080140502c98401d03050f01482104800c000150040f000c0c070083c0003000c0ba0645 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 244461960 1250 244460710 244460743
    0x305090a0b04110a170703020f030309010c021302040807080307031209080306091504021c0f020913270501020c1204050d03110a020a0e010f061b02060c0c031b0a080d02 74
    0x2031040c000011a00d00713844d00320b43e904451a40c0c070400651000110354044910035940c08826a00c684205601c0b4010f0170200c83c0445d110118440062900c001081a86101c1d03400050a0503120300d40d292030840e01d84c014041c140e01c001000d1042c503410403030105e0340c40302c40304092120a050350b0b21020700707000c00f60040740142c08100210f0301004006001446005024100310749891001c680368212500410200070300d64940284680815800c1c02200c20740c881c058200c411110042c5541c4000741030520b00300c2e540801800403140c070380c0c50440000102c680284000341e12000c0c1c51426030300380200b002d80819200010481040b00352035040d0f444400507010300304014410743c56503c49050038007046c0f0083d4012005c00d800b15040c06660361407070595503041c800800307440c0c03148000c3e2a403401e84c106c242102c0e0800b039690b80052924000500d08404810151a80340c031021001c40d01e031444170000401c080504140ca080c02d400d151140d00000e149200080030f40394400340001e0340340c0d4008900460381 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 244463210 1250 244461960 244461983
    0x7020706032a031e0c020c181b070606091103041a010501021b12030301030c260a0209041b0810180b01051c050a1b060309031403100306050108060103030305090a0b04 73
    0x501d01907900d0001150013441c0d0500244100f40e100035100c40b6a2400c591003106607211a1864007a00c8a400344219441450401061b12208a00c0d4454100c0801100c1050300d66901041414550080d401c80000584405440703003418a0907011480004007a024a80140703030040210b60390001e9400a6000004400290117550b44081841001d85144601030340c40004000410050515564801c880c01281018503a5640b040c0100d1300c80c4c2a403252204641c0b101c05182d0161901c5944590042d104960540c00c5042a2100c00102c01160388191902d03040999a010344014174007800c000c26002c03a240251400c810340d5074000c914010f002c0c640c02582d4603e0174039074540c10101591005500f14003290040c481c27130718261941541c401e95205056104240000d03495020713014034030541e0703415118002203400d055525500d80d00000c00c94624000d44410010200d00a44189030103000c9a00c09402198158103002c0c064030b00117012034040f544640580c00200e510490440d4200380d02005007102e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 244464460 1250 244463210 244463231
    0x120601051b1905192a15020106050102010b10080a0209041107050607140304200f0a0605070204051308071106070b070c0b0a15060e0a090507020706032a03 68
    0x60340c00070845160807803241e004640b0404000b42002d1001d14400e02c200c8070188245800b032140c0d9100030700e00510340b02020042d0a9405800c0c020307401c410700d1541222400316070382e40401d101d9005548a0202607591660144010759080c0605c00548506940c0c2d14100303000108028000780d0001c02c003940c9154003240001e0140c1d0340b0303005201c541e00c00e0414076840c1e9680b41846511088140c0d241c4010500303002a0040c0150044c050781d214640081640c1588000224400c209240742c801ca181d000303036000d02e041490380d0b940301207401429090f81c681d911481c262041c04121100a0708000c2880c0745001d190780018141411920305c41d50201240b00340303010140c0428043c0c06203084c002e01150152040200b580d6020140d03202d95130098010030407640304d9012410445e407290f032503e28004800c100500065004070401d0601d075001800c4807001d50340c1c3e40b408030304494003903641c400140c22100007044601d42c54010380f40c14221807894900800351501d001c02504144008400a054541560302d6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 244465710 1250 244464460 244464487
    0x201020f09041a0303030708010801180f0803040c050303040906030309050409080a0f030b0a090227100c050c0d030509010917030a0c020d02040603030509030d05041d060d1505040c050612060105 85
    0x1080c90f03000f404990701c90500520191a40d102402841015840d00e51050560001c60b840602000c0d00810740c44461025611884d0311540010820381d2a4846c200d00040c0c81e8404200030401096000c1000840c1421032400405589590b0300131403049041c0101400854004401c803030150300319060841c44071031640b40a901800600c109181c0c4450022000110a507003078005001c0c40440c1c3c01d503034440c6100c84620101d01070300010394640055100035032502c00c60003080026400c5018100b100c5605844c100041d51240c402241103000030710204421516580110080015140d0310a00c050035090396442e0b15901d000e1402c1d000204a043e2401400350344403160702c40301d001d801910500c41140c480c103010702503600c01d07007034680640300d00b84521590741e12500603241981d0105569482610a00358804d422002c0a045281d200d031542808400040d000c041d031103002605051b021565281a04005810403281c2c1d00080c0104401c002a4070040684048254404003d00b0601d8460720503000f1071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 244466960 1250 244465710 244465751
    0x90a0b04030e210c0123030403211a040b0103020708310e04060b061603090e07170c030a140f0f0f040812071404141203040b0d020703050d05070809010c0201020f0904 73
    0x86d89040c000140000c0c5035000300f5010000c540d481c42ca00b103110941c0e112400700d919003690303140642c950324411502480d0030b401140b0741400501d409424901141c55004080d8402882e42010850000d882158071b1032200004c0c1c00041a2540d000c5a01d01d090074a621005004000808a90381c4441c69155590b40500365100602500c5445034243c42624007c0c1c80da034828058151540446400280028800c48007181003040c8076444078141c2d00c403c10845e5154001612000400791a041403e40783d00a01145a100c1c007032f400013a400324145030400030803000c0080c000c0011504100d00f004042041d050441d0054450309041030299900c01e10200c500341180300d48101118800280040c1c2421004080c030030541c4200e038440d4490000c07614aa40d01d1286100c0c4840070401401102080740040d0701038203006029007019840e02c009a02e80c48100d540881e0b0240200f1058014025020307000d01c03c1c44980340d1240000c520708150600100814010300140314030a0340ca0f180c075282007081a846c0d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 244468210 1250 244466960 244467017
    0x18020304032d03050f06060a030b0d062f0313020904050c060c030c01150807030201050307030b061603030b03010524030102070501110301080f07030f0209090a0b04030e210c01 77
    0x1c03003603642101c207910840b4444040480000c1c100004038480b50790b80925603000c0c000c0180000d18104907108280c0103010700b44942035010300d0341184400800ca290080f82c0c030750415000901c000008104159124058001c18800d80f1038050080000c0020144650421030303070100e03207a80040da0350b450490b11780303003002e210f96800840c081910032031917600102801a0110600090012004861444440480f184034005060307111500400c00740d406940119008501843c001c500c64007100b0100f1016440403420412840900c000d44080c107905114081554004800a00c1070781001d0a038188850b100d40c82c2682000703003050603080a03940950460307584030340c004001d002e0f03508070300c012401d00e800034800c03180701e8007030190410a0784c80e002c036224080d250302200e10b25404260303400748401d403840204a24402d00c1801d64a0001c145040e0b2010b00c40c030312036500c8413a0210358a007804080091202c6100080380184880781702c003000820142c2400d402840c001c602c10b665548070060382000b4000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 244469460 1250 244468210 244468247
    0x509241c022107140c06070f02030c1f050705090d11060d05010905010e0606070b0a150306053103020705090423150c03060303030a0c020106180b09060306011802030403 74
    0x108030b08400694440c01e10824031134442c00e400b80741070010340f542442010506503080c1c0040000500d41401991207a11550151040381e040514082100f0f24002c4003e45500c016403c41100c031803003290a0140681c07000c11803811900f04900000494403000102400404029190600c1d400940b900010342d0b00b403400c6580c09208a5a40f8000800100001e008002e0040b080b040002c5180c100728040362605d40d480a01e138800c0e5a680c840c540014020310807100241140c80100101041590044074012129030100042c1a1440c0354100342c0104501500001c8000160b020404250081280c0c011590182c0d04c2c1600380d9180e1802104d15445642515011501d10350354000303545000030621112880711110032030070703140e8829090060204031040780e0f0603401000056038030307499500507043c50100b600000c50100d482d10451002100721100d56074074140e0322080541245007844255030401c005034054041541882d5025034000c400c80c5494502c0c1d0340000105042500c52141c0d200c0c0c0010941 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 244470710 1250 244469460 244469497
    0x518060d090b0412020303040302070333020307030605040606020a02060d0e03070309060807030b091302030708030c01020c0114070e120705030703060c0f0810060c0c0e070509241c02 80
    0x60302c95900701040d1030568140703034100c0720502440d0002045a0080d034058000f0509180382d6030742c0740b01c5c81c2e0b820501e05040380100000c1c0380300341c7c81184011003100d200040c09a104d1604080041c2100d040354003c620450074480704100007600410204850381d01665926510071152024101420040300c11042d0303840b0014005081c140d001140c2020f64070f03d60740f551450786074600c00300c099602c030b0f407002c0b644001c100c8041200e54041d0140040b40034405400e41c0d88103545d400034036040d9000030489c034000c0e03500040d4000e0444420300c140c1c807003004070034480c0007241000a0020b0025180f9000726024206010120088002c00c202040003400c0090403100415268070305103019000c1d40c02c008001c10340c42d245500c42d860043c884588126418850540103620301081168800098030b01910049100c00c0c011440310f03005001c00388140d4030350700c40d656170703221080901205114180292800551240c0b000e05194480c000322050320361941389810429540e030240307000034400c69205002519201 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 244471960 1250 244470710 244470713
    0x9010c0f110307061707050304020d02030a03090503072c07090807030309030b060301020304020f0f0f0a03120807090807030f03031e150902040612200c10050703020403030518060d09 80
    0x40321241850060b01641d00b260740e1400103580c076a415141940d010750650000030b00c40c40c8038001459115000400072003002c400354000c282441c0000b4410f070300064040505210360f050400488004080d84281c00b403c288200640c3c0c54580c140040c01100100e0320b5022a81c8140300d088001c000c3c182281c1660b040b40c1d9a071030003420502c024441200c0c100343e04000250345180610960b0f101303540203400000c031468082c080100321440c8615040e840b4403c0f0030b0240709602c90071622800745226901000f080440503030041d00c482ca00070031a004202c6003070703014441c10b07801007185000c90b0360010503440c8081352803905030041c081d0034407400201c00c58241040301d40d80c0e0a4121481d4404202c80d40140f454407045c000003640f14600a1a02041400c0440c00080110380e10041110881d10f86120100e200401a107601d03500c051030421096022401e14264100d052180a4201c90320381021071a2510319074015090703005810610a04040c1014201d10136101d0804070707602c509803202d0410006989 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 244473210 1250 244471960 244471973
    0xe0a0209010201053d09110403050f030a02071a0d0c0f110607021506060708031906080a02010909020c160605070c09020f030412091d04020306090c1509010c0f 70
    0x40c00c0c010341c01c01000c1903e801c0407441c5164003100914981c05c40907151100c01d034060b0350008600310f000c076521100003000c1c4a244251500341110f0110150754915609229240080350500190150410480c408046800140c03c00c12911f10f10fa5010701c00d4050010040c80740280241c02000605140c0c40c441c1e85540040c5488507032449480700d03540412920170751599030100300c0d0000c0140e030113110b42103040f1662481c55a4040401841503140040c0c581e46c290f020f0700f00346e1b06441c0480002c3c8540c104195980035150180c4500e6008000050f00ba80008000c9813940c82014219507001030b0740152040c050140040342c285205c070420443d07965250080030390707214080c141d4403000801c4005c21040c5050086402011800c140c0300d0a40e10b8548a03c0e42445031712400c2c10500580d00c0002038085810001c0c81b002030082900c0d0710080c40c20703006050401c50002c1072812240c02000381000070b582e4140f510a0141a18071070161603880d104010303180c0c04900c440143c020455002c08000304200d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 244474460 1250 244473210 244473217
    0x62b0602120702100504110d0f0c12150504030203040611031603050307090f050f040b01020f0105040b010f060c0209070806041d070807060f0912030e0d1203051b030115090e0a02 78
    0x507150f003143d00c2c0030009040d100448100f40c4004000324120b15000c5110300c0e000103c8150507008003001c0030b81800e5907071a000c2c0800c01d03a0240300e111207208415001c2c000c4070740a500b42076524000a02c001d00d483d580c002c0d16031241c0d004800501080e2484000d003c2010002d54018081550a9140000e0241009441e80e0400c071070b000300160801c40d0126020070481c03500800c8440291403031680c5034000c001c2001500d41c0301c1b4014114421011445038070b01090041900641c02011441c1c515418401b01a49808003608500c091000d20b5010500503168a540e00d07a0000291604144a4a600340083e003d4601003010310020410b03003610503400503010541c4400c07180c0c048100e07585181d41e0700702a2000c415040a0001183c092002045402c2008a2020400c2e21038500128420b0100b400242c02c5480c0500a6803201100f06010740640d426100f0305410981180709984404547d000800fa28441401070050540d160b14070074a0701801561040301401300a8801449483c200302d10400a42 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 244475710 1250 244474460 244474471
    0xf0a030b0f04020702030c09090a08030106030b1f020d0e03030903030c0f07080c01080a020706060e070c140303100302060903010615080708010f0608040b1306020a02100b0405062b060212 82
    0x41016210705110310b46407084840039039000e0003400704035410b182001941d500040242203540600c51341c10001404c1640198040d0005840c0012a400050f00340101051400010320403d1120381c00c00200a400040d0302600980c2454071040700c98a04000c80c1c110b002d1248810380600c804500d450035014045403141d0040c000c00126403903140c0e10742c94156200c010440c2180442c0e10780c40440e07040c0d01c0ca50001c11289010f000301060150b41c415038003200381011180030340002e140120500c10441544000300700c03041004011401c41c1004c0000303508010b07681c40000d00c60300340001d2403801e03074800313411007402060725040c048498a05068013800d181401c0f80d1f441c001900440c008540c000c0c1e600003507400e881076940c5450441d616541c51075080603000d00185c1440704081445400030742c1c5400142040005e0ba4041d29441d010247c18034156841260708a106505000c1044144c0e1250485a04408254070840385020b07000050700401080b5644041c01d002d00000f10703c0c000390030159080c1e0044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 244476960 1250 244475710 244475719
    0xc0a060c0509090a09020901030213060503120712020606060421052506030c0237031206050603010515090d060e0c0f01020c0d11130e070e06010207080303041203020f0a030b 76
    0x82e9240c030101c20440b000c45c41c0095000c8030041c010300242c104668840108900008000340b0b00d5200c500003440c008866024190000001604008016509024290440083c0001c180604008000910303900540c001c048041040c17401e840702d000c4585030144030340ca4004040d650103031210f020910040d0a99080703403090b01242e071000107401e40f0138810b10500c3c03041507000d00703174202d4140c0d010a90481202c0c0134031135410340c0340011054540130408000c000341c4680c54400c1d41a582010100c15144c41c1e81c003161040c001480100515110a40451507040003034050940e2140c40170b00248001900c020050030f10391030006640e031161800100103401030310071140410030f140b4030801207988544c1510718540180c0c010361540c001a50071074403544401d000905903111030402d00202c0d01194401400c03c6074a9020550401180c1c0414030103d401010030b1020700344250803c0d1403683c0c0da10016100034042c1c0688850903480501c03942c156440104007801c41582c0d00c01d10000140548a403d80043c0305 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 244478210 1250 244476960 244476979
    0x705071a06040b091003060513050f010e0705030106080613081204050a11040911041517010501030c0b0c06010b0a1b1218050307060c110a0303020a050706050f030604020c0a060c0509 80
    0x21844e0030a0b00600c1a5010b9a29400040c15695000c000e4580a000c41c09110500058840018000e03c2000c008295690001070420040c01116107409210f60210b40264501072060101120204000d98401405070007a514402180361820603889040e6103945007a03110700512082190210b000100a8092941000d1035a040000c020460304410001840025800c04040c450300b802d41043c4a4044da519040c0090b035a03840b80900030b0380303500080052a07552040140104181c2080c00c1001d0f0040c1455a0300b482c2c1480c94440d91007206003d54002e0302d80c00b0560042c002d1041d1102100b1f250740001c2a43c80e84813900d00070b140084181200c5001c5459121a00c0c41e00400c0b06200045070307401002888458078209042c1c1700c0d414a0a810340d00003440078202c260544802c981d550046101c1d074010610f89141c0d080c50741c1402c1c5150080c07800c000d020400000600720400c00d4981000044030b005a071400c0c8007800ca845d0200c901e00050829090030040c080d039580241c064039841e2800d56400e0700 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 244479460 1250 244478210 244478231
    0xc08040303050f24040e030d0e0f0a050a30051c0510150c210f050a0c0b131211011503020303040b07080d09060c0e01080f040b0705071a0604 62
    0x22104544004444a074440c0c070701c0341d0b80700d1801c1c080c18813070003d04006000b0f001951428115400380711070b80306d00b5031107841998030b25000300082c0e1940242c0c20050f20802a8a80e40c451300c0c1c0d01c51701d02c040c0002c400c100604d10f51310410b07141c03c4130340e1441c0907003d080c0131101c0b980a862500003503448100f02c0c075800c0c82405a010a80211403103002c200203843e05171820003020540c01201040c8500c2001035020030040058611100e112426440500384101c81c40c844100801e41c41640c8a2141042010f002d13a00045400c24200e01c15036600198166040d91841829224541810700c09032050300088204070000da005800744103a0700c1d420000740101d4000342c113262403440251200940690040200300064288a07000d0308183d44180300c00b82c0380800005242056a06090741510070598070101c003601c46411a94122070140c1c203080c0b010091820011729102c0d03180043c07000d040000c0d0303000041c0358544104c0c119003c0d25404015a405400580f040c000f00d20001c5402a029603c0c022134502c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 244480710 1250 244479460 244479481
    0x18060504090506040201030e01181a01060c03080c0a1e0c02010807020c062a030a020303090c0409110d06020d060815090102032502010212010b21060d11060702040c0804030305 77
    0x1816079000002082d850704e807070b40114014031015040c00f84555854845444080401607404100c0d40074448001d00ca004a1059610100d01a031260b010702c0400c4005400003a0010256a4009080202507450b11030b039001c02e607440a20200d01190095441e03e05604c40f54001e22084541c5000382e992030140d50740e054050b130b40c81c5054118141d00140520180030072043c0b1105600c500380b105c182200da105595001e0034619004034aa42003d40c0005c070420004420401410302039400c100c40600610b42c107900c1d030300c2d8880c0d41d0714000d40c040c000c0f66000c2414001c0503011171701c9504a54100b00142940c4102c0341761121080c40c07558080115440211765044014000d49010300400d0a8104900324800000014841501942019550241304004040c81c1105001d03001381209500203076201c203046060303201110481800382d2020054024803407161503400c411400180d2007106104100300800008504c0d0207008802940310341441401041541d002c40141e00661203920140260b4480d6217070003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 244481960 1250 244480710 244480721
    0xc03060114210f070e0a11160221070303030f0504121d0a140108131101050d180303090318050114030c0c06010807080c040908070201180b030118060504 67
    0x1a0440460300207000146001c0c0040b203041c450140750302da4800c8600c914181070a0f807030100703000c0c5034000000c04c0000c80b81c0c1c5448283d10845078202040701c0040802c9403203c0e4010001d0400200740d001058600719212000703103490a5034190039000d0184015581660344030365902003200020304101802d20041002e005090055900041084800c82d00b602c080f03c11802c00348a40034238620b00701d2100f6040d1100c00c00c40019107103501c2003002e11011500050890040501000c036052203c1d891003002c1900000d030740b21441001d181c6141d407481c2e6004040003800400582421001d586200c0364101901035100407102c0e80b2a0711400704d40b9001000b20440b06d0514400d85002c41c035103900d0903a401e60288001c592108201c100075090181680d21245007031b4098005886540c4004014001c1540400c4406140c150454040c002070503d40c0d2070f0f0f0140c0c09460402814003068070417801040c025103441c10301a0818800c150345940c0d6407041c01105000c0b42d014102064981680441c2a04060049 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 244483210 1250 244481960 244481969
    0xc090a0c110c0a120203031207031a191e1d010602070b04030b0103060507050c0d09030c09061d06060403080c0607030b3304090c050309060901060f151812050c030601 73
    0x550800c0740b800c40d800c4d11407560044100e80c103000402294100c25860503071f01e40145540ea40c001074a04484450043c0c00d01c0340715541c0c0c41000b40c20840c103104412080a0825605658130711071240a000d50b030040c0c201c05a0f080048050146410150340411844559049441c2682150703601642d403001c1180d00d04c51804098400c8542d40c00500205130181c1207039400c0180b503d026071401200c1c00609081a030b00300301d00d00c000344110404006002112528a0203040c80c50010400c140c906460030b40040701d00b03001714074044100800034049583c0d00c0280d8004542280f87c0f00c1d0b40724021084991940b50486080b0042480c0c550362840c18103142d0303004411003d4030308000c0d0503a82e0240b100100104400380300205610200300104070f1240c04e00500c40d0a40207500e400c0d0312810448011801d220000740061844d0f894520100030090142c4018811240b0f0b6100104030b00810607021101030386880c100390369450340e83c000020349440e83d07a04000340c94091400c0e290034190110405842ea0001e108 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 244484460 1250 244483210 244483219
    0x207150c050d0507211a0609060703030e0c03010509070f12080306130f111b031303080d230603010f050702030a18051c0203062d07020c090a0c110c 65
    0xa2200214041d40007030b401c404c050901304048181064885030308411104501021500c0348141c8098001c10000c54038040c070308551680c00c0c420488041005170248140140416486840c2444011018020080b5041010b0003c2c002803034412000b5a0b607498030301c00e00030940c0c40c5c01000284540600d440e861000d0340b10488a10f0340c1c4901c810030074005280314403007a2860382d4800ca07003088040da11030b0020344003880356050b8a0350002c1102e42d003540c0e543d500042080d0400c110364149007101c001c500040e2a0310503c00d03034aa61010b0180401440000440b41c00381840003c0f041c0812100100383d03210300411402403148034014201c040503a41c00380c42d03090142c0d00a00800c5007050003448801d840c0c000284d584c07054240d40e00c002a0b11214070200402c120080c903286481503090500049074420000e902c020245029502d0800100d956a510011100c00c0c14012900c1d0610034010250162001019a00c05042444c070358030080c010302e07064501140c5181d882d013440800100f00031901100080 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 244485710 1250 244484460 244484467
    0x108030901050f18102a050601121403070b0f01050d03080c030c1c02120609010303050904110909100512010c051617030a090507050a05060703031d07090207150c05 72
    0x3c2054041e030806005a00308005014411040e91901d88000255044036510880d880301c01c00c5c0351307541c24032800710304145070805170032604085038000600390f0449007512069642101c00f030130b00c00a40302c2d40000350343c0f05002c001180018003c07034140e183e0060b00c8465031004180d0780e5a080090880d011000100880e030440e00040c00002d2031009154410016000701d4600f440085d000e0003c48440ca0b13061100a5020442c04d905550100311242d00c1a010f07034440d501541140c0f40070f00603001702032031039100396201da07207040d45160540140e4140000140246019060102e8240c1d28615940102c43c0944101d40203501e07920014001c1114020b9140c44261510f10740c0f00c1c560081300400d01c010355002e03070100c00c44800022100011407142120b01c00005070083c09150031810800290311580c81542070341d90a01840e070380d040c2243c00c0280c1c5800c001a4a1410544021803a1002c00520b001c40c01180c01c0040d400340c1503002000c0051051400c841022801c81c074100c01c07200c4184503400010f10a1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 244486960 1250 244485710 244485727
    0x4060c030b030d080714070501060f060e09010308090117010e04060b010306060e0909030f0c030415020303040c09090204060b0d09020f030601120807032a061a01140702120123010803090105 83
    0xa0f4000c45d004012450032000f00c000c043c820040981c008201207900c4d0b0b56862080020720001d884900c041c2c10180782480e082d010a50000e132014006001c098400c9000168080300caa02508103006410a080d6001c40b2035070f0b60791141c03620030314205c809a480c24200603070250198880c0c41020306440082e10740c40c403803101007014003500103401440700450f444200015840481464080c1c00780c2c410100040da5118200910700507415408024801503610600a0200054034402140103a0340c0c604c1c1c0c002455806c500000307024001c00d9210704c10550000405400c20361032034009502440c0290741280910350060b0034580c0d1070b0b60901c101c003c603820921820740011103041c0140460390081c41d040c800203000041c1c001d0700c0c0000e990034603a0f98201d0007010003040303078501410a910900182e8250800d070042c0000e881c1c00c0340c1e4903a00e42e113a04001401070031559042d811150281c075240007004845012002074040c00c0242d2074002c140341c0080300018903901d000040f10110754045c0e40d60760906a25 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 244488210 1250 244486960 244486967
    0xb0a0e120a03020d050a05060a0609060e040203070203070b0a05060f0a1d133206060a151803060506150a12150b030f041b080c0d0503040b04030b04060c030b030d 71
    0x300c0c00c0c1e00c101a000c00080840000c02e01509001d921a03140004241c18a40c0030000b00c204590300c1031050001c0b04404018080e04501500440e840c1914091b1782ea540b0b10034100d00b1446940c0008100071204814000101c40d0384e03010724440c503419103900100112000812480d03501600c21521000d050b400759540c8006852074940c0c02c96254805090746910507680e498101c50b600034510348000c042d003595200c0c3c40d162046014650016809000c550408402040e11340c049030080000d0700045c003554980030741c85040881c2c2c0341c003000345074007070081d481c1d24151014000c1600c5680c492a5005502d0001a68580890b0002c02d22620b4110b4210340984811300940000b0541854140d04030f0000034100c0b021100640c81234074055614409480d091178081c900344c1060100c88201c104946c4144211280003414491581c4100c503400c040400525009196101c0c40d042101ea10401140000801030000c082070700803441010140940680854110129004441510f61503030000300c0c40d0f0f200601 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 244489460 1250 244488210 244488217
    0x34050412050f0105010632091f021207030f0e011e03020304060b1c0f150509060f0a0b1003090503090a030305130503060c1209100c020309011112040e0a02070c0f030b0a0e12 76
    0xd4098140d003003412002c0002c040301441e071680110b19202c1c0100c2003629030305000c5141cbc410702a800c101c0c00e10410b614001c1c0b0580e00c48800d0828001034110780c0503075a00520301a01518a0301c03140152020300304800a010750403d0b00c3c1243c00d14105603400c0311600c0c101c40103a079a0183c0750500d44007030040c1e40341c1100b0003c5007a000d60350240d001c400803543c01d08a000d1644a0880180103050138208201c0d010b10201c00180b42d0b000003460044820000da8400e140b60501b190706241c0030641b4240c60a055080d0311030289400d42c0603a103201c0020405411002500018106840c0703141005d5440d424582c607107104480701121458200640036881604120294025001804640700800409456030841da01444102c02690001c0b03501e4400d50ba200300e0111103202c030200a018100600d001c92265401a8000c984080700031130002400308110741e050791201500000400003080c1d9840307060b40304c294503020540300d6400100010715190001d001d0b025240d62410000c0c1400c0660741d41d495040d41 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 244490710 1250 244489460 244489547
    0x433080d0507060f06060c150501030503191b05070e100e0403031a03010501090e010b0d051b120a0c060909020c07050f0613090e0634050412050f01050106 68
    0x4da80e502c00307804050340d52062801030141ea880c0c071803090840e0304000c0044500441c20300304041c1854014400100c020003640c1510600445a00700f18240e8007040d6a105651441c2000810400742501c00344a0000f0b81345084640485407541d1607160b048594221502c02e009006c00501d0510108000a10a5000229010320141050517026040000a007954001e0307001d05403035038a850310540d0540c030078841c01c0d80f81c2e030044880e01c10b17090360741c0c4e41c43e1b440c1c0d05500102214084403c500001a40742d100f50440b0b60383d080e6007540c0301d40c29030345040440018035000380c900041d6060408191410301d44210f485d0610044000c0030304d1031034407040146080e1080c0016400031014005d511800c1140484440640002c020100794045102d001c1490010010720109032403c810001d0070000846440204c1c00c85000314401c1c40038104000d09442a11866000c100030503910480c00051100202c2d071440d20683c1040284416643c0f082c0888a041a900c0120500b00403507140360901c4550034130a680c400d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 244491960 1250 244490710 244490723
    0x190509241009050702070501020705010903200a030f0b1603050103020f04050a1d1c0504030b0a09020312070303051008030c0312060d060e0d09050913060203150433080d0507 76
    0x49444200c440c00380d8100f84c801c40d002d42d0200e1814000e030741c2c050110364080c010a2070715500c0980345403504400c04030300200300e038600000250100b10039210610000040e6402c4982c1c00c01e50441d07072610801080049a41090250140540300583e078400d0180314100c0303030010082c03542455828200310003808098605c031940d544c1c40315041e101035142c07035030849205c1c10038000e000c03008009440ba040c031304c21071802c000c1000f40800061000600304210550822007030800020180e04500c0840c1c9010013078800350800701d42c0865030b0070402d94903800c8180304078140454580c28a9640806a580b80161076504c45250410b03c0314016a000060304240e000310000c1a40650303078a42d0702c4100c2101d101e01401d00007a00022107446290303821040010003441d003590003d07070a01d402818a00c16030380340d1100400e12034002000ca1064004416242c4450078024000c1140b65544e0182114907480d241c03104502c01807241089103101610b000c94000c407803151000c6d000005260600b1540c9a1010100700d815 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 244493210 1250 244491960 244491991
    0x30905040c120c020f0f0a031205100b07062301080c0301050c0f0d140705041a0301060c0605040201030f050f0a0608150a0c05040b0403050312010506070c030b0c090919050924 77
    0x40503001c006c0c41c035041614101600c62000a8107000704a41c2c1c4c000642c8203080e040505100b203101e03a1a00400c1200c04001881e52144038914201c3d0142c603018002c641a8030b100c00c4a0700031801403504190480701c0038021168000708140600d400c1e541c1c00c03540000314440c103104e402e1054200c0c400803c0302c40c0b001c100c000361405001c812006424000e40714440040d001140c140110010070251640441c0c1040300c1070306540c90142d0003440c1004030903000340074076151004202107901079000380010b003002c10f906001c640303070411641c0b44000d0120b5104040d20304242000441c280701165590514106002c2c1c04000c3d900c40307083c1c2018204086003601004000c11000806d442c01d0b402400245100f200912b41d1441e906c3e051510748070060704003910030002080508001103046070054100c0b81e110030340c0c800a030747c1c88d03058200c24011400b0791a04420150200994000741e2000d0a2280482c0c2d4020000c640300e0a500c550b941001611640740804482903e40c0300c1a011840f060744206480c0702c0450 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 244494460 1250 244493210 244493233
    0x1051c02030a14010b0108150103020d020c0a031e090b030a020c030c1b0405061f140c03040806010f06080408180418030216090219030f090206070c03030905040c120c02 74
    0xa0911151010343e610700440c42108030b000e00078002c001104a091904440d5420008403e070300c3d803401601e8260500da0300144c90b10026a443d010b0b101d0404a400641d19007100c5810301a107d0204609040c00501c40710540c1c825103405202010203494000c0803032130555803400d1091009510145100326984014428141d000c00d082006d0540d225031114841c0003000c01205120580342e0181c980343c41095014140501c00d41d00320140c8009003410700e04501040342d0541c8179140381c400d07182050081e000008000c04d41044c0051510b04860381c452081c3d00c141c0d6180300459544000340d9004054000c01c00c04240002640c40340703c0e00c180b00003000019800c1c800581c4103410714102034120b002da084080e80700d10048030000040c0c01001040c03015441d00d040303442029000c04007114410281540c07a8400008542594400c41e00194081e0005555185c0c034240f4000100d00b03448205d00088070710f1070102c0d00c0d08080c0100d2015846a0b1958004120810060000f82c031580101804500c0344005566 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 244495710 1250 244494460 244494463
    0x318030e0d0f150c0201050103080a081312111002070309031202010621050c10020729070302010b0a060e03070302060a0e130b10050903060c0c0a0506070f1106060901051c0203 77
    0x500641c40789100b0110700e8814540383c0151404440c0300303415649041c00400c0410350a03030846500101500d8114080e6450b800c0c91050450410000307000d04148440c090807075608000c82044410818003200c4004440b0000b660503442840d0000b00001d00409040002030301480c106224005180000b088907602d421286581c240d912041411070b859040701c540c00d20005214540c1100010768640100d000380000c040c2d40c0303c1c51071082c1000312100180c00c0350740351610300c03101035265140c40c039080c1e80300540d0400038041d101e40744120340318124580b40025400c0c020f001060300902c002d170107000c0f85441c6400304185030b0070940700f50701070080031030308019155510f0110031a55584d111000a0241d580010300c00c40e02c000f8090203050ac007003005500182e42e80021620340c8410500220350b502d04440e2030181c140780e16240d004045110b0b01040c44100b6410402888a442042d07850309050658059065501c0c1010344005811992140060005007002c43c0c100c034800800c1000c0e25480f803003550101e03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 244496960 1250 244495710 244495733
    0x110702010302071e0614010801051003080d1d0106080705010507030807030506150a0c1b0b070b04080906030a0b01020c1f1409100e0414071704030306050d05060601030c0318030e0d 79
    0x220744d0107a6400201c10000380c5034800c1030148c42a0802008145007540b05000701030400d0201900d04407020070b00303101107507550300031004620070780d8095050241260900c038081e000c40e0258100c2030180a43c00b08181d480f5030186c0308065015940c664268031809400c2c2c004207000303404940c2018440102c001070744603500050007420300c0d0307075168050107186007488c2484942c107140c4200c0d0320042000c204283c1c031003d4142e412300c03500700b21100703420b0302d0714501100c00b48201a030307550b003124000c0f0410108040c02e60245841c11000e030292114100c83c041005060054900840303402e008581060341c40350711a41d4024414400389011900e4408507600041e600041c145003440003c291006005141c02c0600034145d185d500d0800c00c8815051600000d0001c180c441004a00c100c1c0c51070001e000d00d8070a4025000400c00508071000480003800e0075a00e40804a401c2c82c042420402c3c2c50101b1303403081c8500c4414640c0300e002c80c103003006d45540031208169940455a4803c0b2960f00881c0880c1615044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 244498210 1250 244496960 244496963
    0x20a030b0a050a061a0f040905040507030614040206220f0b090109090c050702060a1403010e060111060403020606060c070314010516020a0809042c0c0a0801110702010302071e 77
    0x10800c251810107541400e50320300030001244682030200c10003040080c10700c0b805071484004800e50311090807900e0034406015540c00143d150b8206000d2000f80a004202441a28001c540a0000c68008402aa056130007034400a400100402015a603120381802c80241d1001c82d82d8940c00e042e0342c81c9141560811680c001da05000d4000030800d4003582c1244440c0010708180344180103010040710050000c2c01122000b0380a800009010030003544070381d0705a010b64140103080b98807941c4400c40035089000403100c0502058100d039000800020000d046440f40b54190b004000550340c2d4010311801e500300c551812868420000b0100001302c440310320b003e40f12280d900000b010702e000f55440c030381c80c003030180880155080100c6600100b41c2200842d08001402d45003c96004074007205c1d400750300140c2c3c400b80c80c890100d007140d164080d030106044220796412a1b1402c800c5031105641400c07070710070030703c1d4007015441008180300550198015010540c00b07901c1c64454070003020308007403000824010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 244499460 1250 244498210 244498223
    0x30a03091d0103050d0509010c1e1109060d0204020d09060603120212040b0f03071b03020a0209061806040f1d0c100509031e0106080102120105030d030b0904110a03020a03 75
    0x1001d00414800c1100780c5108009400c401807154510380b00d01e40c49880d02d03820301d010000c2c0042d01d6441079014110354255582d0165500c15a203012042d030f0a800600e0707010448280c48085081e64462414088031805441c000f0b2200901540d16400c20000390701082240c0800c0382c03610040300200d611442154010750013201080480c01c02250000d0401d020343c00303201421034083c001403010105050030340e400409400c00199890322842c1e8141da0b542d00291036144074803011550b075400c056000c25410728a81c0300b1303915000e81e52144c0d8100a10003404545100c50514507000244092520750003c1455110402c000074044405005409100c6c10442602d41c49a001d1f02c6001114200214032544207001ca16106040901c8500001d444000c81006060a1030b40a07441d030385480c00039486100103142100003103617244600702006102d04424844c41d84640942e96055494074040d0044e0150031200425014131555141c0d02c1c00d00c220810200180c101d9008600440181c4403100d000c400741d4082c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 244500710 1250 244499460 244499477
    0x1e0203120d0e010c17070813080408010212060102011107060f0605091008060f0f06010507020406080313031a090d0c08090a0b07050c0d11060c0c030703060605090a0903051902010b030a03 82
    0x860b45030135904141601c00401040c03c00203c80500490f41c2240c0002052501002c070341c4450154181005202c500074140580005c1d001800a00542c01000302c005184c580300001e660b40e4005a0803204401c03200080c060082009100041c25903100e200f00044c1d031100011881d0b1910b000c205200c3d4200e42c24a50211014030602004408005240e806420b5041c5031009103032401010a600381c0240206040c080045049011940c2c1c540010001d4140c01084030744840442c08002d40e601e0b020310080d15100b08a000b40c02034464040b00c034034800d0550000805d600c045c1d0070822140b410410340195a44201408404019540c010f8804000d20031601a103445150718180142028484400c4500c10a01c1200c0c0030b0001c0c0460a00c03010700fa41c102c418a4984111802c07003401c05000c44190f40c1d060045080102c100004c59020009580050b5040503156545c03c281e42d040710308038000a0301040c0d05101c0c4c0085424004c041100f004032903c008a9440b0b8050042807406041d50000c801040005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 244501960 1250 244500710 244500731
    0x40807060210110a0c1a07030c0905010c080f0a050f03011203120516081302090c0703030507170a0f0e011e0509070e040809120601170d05071e0203120d 67
    0x108403400c82d44500000400c86240e188615078818800d4007008010b000b1450025024089140028001c2c448803a8680d01c0c0d514000c0e8000700100b09000110703003c45d00f50240820603500c070707040401d48030364800e88a80c07410380280c481e4652074204840c00740810408006061300c00c414035001e54002c00820300d4120100340c1920b07010300325222040251007038903d030108100e11000311805140c07a0356418141105652140c000d0200401e000da00c0180d0001c820f4818001d04005c0b5000030503006001c0c3c0d40800180d151a0811034140f00c05a0b000070300c0600c000d002c119841c0490340a14205e00119000140f545d8180729464203452a440d0501b1901c42c9034030789c1d54022001801000d901440c01c1010380413087c2014460411070002500140c10164082042106c3d13445c1e0a0b0900e511088180072640550b0b075038811292181280720000109000e407010103181e0364011403e03158484c1d400900c03c2c8a500400701d040c8030040d8941c0069a0510640c00c403508951800d03c0180f140c030412039800f15055006 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 244503210 1250 244501960 244501963
    0x80f060105060f0a080a0b030d09090b09011508090703120e10140a0e06070b0c0d0f0b060304151e020a17040c0b0a02071503090516030305030a0b010c06020408070602 73
    0x5a0040d4002d0808001a0352190409001c6450f0813009040c2116542c0317500401c0740c020580d240c041a054400c0c6240c04009036000402d800c1200e00103082804880142001c2c0000640b080c840c03030340501c042002c01520180a41035080e401030a0704201c0300e056030b59403101e429041c0a03006482c007042ca11380050301c0b1400c00384040c8040c1c54150034141c2010140c094034810380d101e18210f480400240100304880341d178900040703e202d540c21800c08880c508000c2a5000b00f60700800500b55580e00c0d0281c4050a020303207001d488003101008003500e0850756103894503804900031160b20100d8a9071004004e400107001e12090f50b154455140044c0c840500d010058078401030043e200300115446400c001c0011701a24111094070480d0742042d440e0350410906a00d0700e111508071110030261210000b0003281c0c1548002ca0040c040c8040b56a808204001107407920420701000d00012070400c0003e0410429820020700d040e8103240c0013225410a40304c12040341c00940200080b60455182001303610f90 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 244504460 1250 244503210 244503223
    0xd030c1a0711060c190507020d050105070801080105090a020904020310060609091406030303040f021f18060503041208060d0b010909050606090106050a121d150702030c0606091f080f 80
    0x820801440a0708181c003245100b4020410350081e030100c2c0d0118001704900c10030540780e02c154083c203000b45072110351070254086c140803103414000030313450000020111014040c881c02240d1401c05007007440007030707024040c000200420a0341c0610603484050741504951080e1402030806940e0b06012a0034080c0c600300b43c51401c0c0007440700b04464800d01c10390750350101c1284d800c5684103003134207141c11241c03000c6448040c81140b0400041480890707000003070742000b08c9002d05403100200091030b6450b840281c54a02055801070420508884c0c801d41e01c902034010503402c40c40051444100102a0b91030000c0a14240c1101c00000d1704c17440301d0360400c0340402444d0317000081295000c0305036051400090550040b00c600d501003022150081e0411020380c2c0c000700c80948800080c22815402000e80c90b41e41181d5000285500c0c0e142001a9400c0d201106031400c1240801c0503008544aa00810416034800b410391202503004129850081004c404075000400028001d010000c00300311301e503410f211 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 244505710 1250 244504460 244504487
    0x608010b060c0c060a0314070203090102010609020a020a020f03010b03070b09040b04090206120c041a07050f03040605041e0b07050d091d0403230c0102041818020d030c1a07 76
    0x150280200759a12a010582e095903000c04c0d21060b8907070f900064110098081c11100400140340d003000d0000c12036010000b045000c400782c00034020640d890183d40101d10605000302d0050b00301c15050801482c150045855007079004001260350081c1c078000078108039580c0c4c030071115140009810946800d1601030459a2401204c0030030180c0800d80105007188075a12890007281c40180001d41041c034038806a030081c09120007481c40340f0f11040c0e520b249581c40b40310242c40b18801d800e4600e410100c00002c40782941d107555501d07410945008125442c000c007400000d4581100900d01042400702e00e4060a105401280148044080c00d400602801c030103801c800d20403404400310f05010840040001c2d0001d501d841c2c04510317113440320025440c844003000c44540348900007034452074405054019000b0344414180617014001624082801c40e90040d0741c0700b00005800b12000301516281100c82d4509001c0c3c11b210040d4481543da400030b4502e1040c45c01103e005002c2440302c0264002c403e0440c81 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 244506960 1250 244505710 244505719
    0x3181d070909020a0f030b0f0a12031101150e0f0114040c0201020f1204150203070e0d11030a050d0f031a0103051b0d050f060d0201080a0b190803180a0b03150f10030608010b 76
    0x28a600022070000002800ae0b484141515040c03003003094070540d803a520742000e40c00200424040003140d140721034454880c99050f0b6030f0040c0030501c0389400340c50b014103c1d00b07403000b42540c440000003800094141e005c0c00f00159503082c4040d4464409510061100e68001207660310646881c0c41c190130b06549002d02c80080c24030501c20880020307000080d000304500300325034003400c600007880c1070311045242ca0b103c40c0d0036015400c1c0d91010000f000034103040c40802c50301c0340c00343d4503141d80c0c0440c129543c6c0c41d0001c14a021100450031039500076030007281c201ca4040c02203890380302810071761030b00340d40700d000841000ba42d11010020714a14241200c0e0b0080c03411a4407080003002c40c2c00003410501d01402c6d072001d85541e22131395a015030f00c3d91740c2010b80b01d50b09c0401c0d582c0c0b0b903500c256040d281c1e0404025000ca074280c0c50003500091414500b40320589110360701e282d055844800e00c1c440035601c00b5802c0740d00f010200780c2c0c0890325541e030f5a20704600030b22035402180460910304842d0966150068040c0103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 244508210 1250 244506960 244506979
    0x20103060b0c030702130b060a0c030905030109020d1b0e1503160b0720040c020703061103130303020a020a0c0305010e0c0f060403110f190303181d070909020a0f030b 73
    0x1480022088131002130b011280b600c410130841c080e0500400102080651200c00080c0708032140303410110b0841d01c9400380d02d8603644203549074181400d950340c0c580c0007940700c03070f14450395070004da0381840d800070302c0c010700c000081c0c0f440d201e0700390403140a01074484d402038800103c400c5003146001c1010203803098510b03e07101001e5140c525405101d005148009003400100c0400700e01d10041c04041704d8039104020070501c50710a041e41c0103515800180070660b512030400303c40c203603070b0549041142e000b00361003104000c800c0e02c40d482c1140203401401680c001c50041609040208840da80d001c0065401780d03000245900a202405140802e80d80c1c10034002c00d2080000021642d400080d00c0c2100d40104000b014060b40c00001078000b00600c6a50350f104070b4884021202c0609090440e0580380700e40c80700201a04401704082240704644071741c00a450401e40b015000300c6250400c1e9403c0800c50411000003910b0704000d800f681c01c0b422078400012100c200d501546a410700890000300300c1a210b107003c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 244509460 1250 244508210 244508227
    0x80715030c0c020105070201020a060501090207020301051b030c16020916020105090109230c0405180f0109050304030f0f0f14010f0b090f180106240201051515070b0a020304020103060b 81
    0xc0381581c80b01074140708000c80d6540c256402030201d10041d95100d0740402c4a0340e107500c40f840094110320070a9009604c1d010000748409400e40034250301807a140c103020f007195221416500b00d50f001182c0303844141228162040140c54102d6944d008131902d400796240010721400090855100601030b003040da051034014004513400780c18210b010f18000b00340207021901c0c2d074412458084030480700d61b0800e02e05010402c0004a51844100c081140c00980b0010b4401381c005030709072422110041c090b50030030042000002d25040e1100e42c084d00ca0051341c0900c081c6a220100e2008002c401620140350307059086a11700d8081c400d030950700d00d2182e020440d40010b10081200e8060060102c4641d40c218004144a480f05d51041090281d414000340b0100d9240d050851080c10300312030142d800b016a40f10301600d01e0044c02401e100d001e0000c0b03000d40c2c403008007041104c910951a410130f860041088104041102801c1d91803262403402c002582d01d044c03030310004003200e4013039002c280c212009100c2142c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 244510710 1250 244509460 244509467
    0x1208040303240e0901020f04080705011701031104020724060611030a090e1b0406030902010801060504240e19030b0f191a060a02010c080921160b01080715030c 70
    0x4096034100500b0601a50350313150544d00a00c6410085804410041000205182c001484500b660001e990300240c0c002e0320441c5030768020742800000c00082e0f0a90b020100c5080990280100c1030013905a0f1030580214104000c0c0f134120b00c99003021058803210280540747e0440301c4070008046d0040210307e0016030200c01889421a805411400c40c0c1c00303401315003181d129200d40d005501da2a9450740e0355a03620300300580101680c8404074041080440000b80b000e004100762402c9840b1050200c005058400f03200802880344802041441040316a0381d102e5100c0c00002d0800d0000c10741c0c100c20071411400d125110800041031001c012104008101c0310a0f001003842900341c66444000c00c1c01d810b4a10b00407401608a003c0c80e804c860041400e11403d0740c1500300041114040e200c0d104030b0f03100d048e13001c1d44030003400340c0350040a4042c15080d15034601c524002c0545044824208901c4069070390b48010f981d500380e0010341daa511180e01440241d42210070b02d2510710180c1003c1000624100018 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 244511960 1250 244510710 244510781
    0x507020a1a090d020301110c030a0f0503040c05120111131701020a0207061d060a12200414010c02040e031207110607141306080108010e0f0a0f0f1208040303 69
    0x40307008a040f08070031011034400b5001040940900100740703844090001015039250800c542c03010001e13440007008024540a5021240940c0d00b002d10f48003007905203824841542003c01918807a50351f1202c041c00c0280c2808003034038020046c0c60864402520f058a000724807000003070303260b038164070400101040d140c0000d01c80703003180c10908101c030350704400110022902c10f050300030035080200051000d0202d940098030f03410b030b9024440100120045c403411070104d5048070101c01c00720007042005004583c462450100825014500890380301070648c00308003514402c101c4241551310204040500c0002c000d07229a110f000c0b490071000008003c1d18040da210000340c03240b4144205141c030107509030329010880380c070303400075482c03c0342000e9903403100038013100c42441110029480d1007203500003050b02103001c4100c07040000c0140790702c284544482404004140b070031100780d4503010342d19001070080c241c0c0c1e034910000358548003120300d0141405030503034844013690440090072034078000c140640074030f01 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 244513210 1250 244511960 244511977
    0x606090b0909060f120a060203160f09091503050a0f11180103080906070203030a11100603081213050a1b0f051305101e0906080708060726070507020a1a 67
    0x101320f0310500c48013207001c3c1041250402503d0080949131824001250011402074041c200300c480007042d401b00407076003103584132003510024015000810030302c03400d608520b0b111900e00c020010322680e00e554061030000790320802c0314107202d1a54043c040c04865540480303404800d4484100a9145060402800c5414000200008008501038040f512104240c880b49640502107947d9226030701805007440c020f43c21102c18a200b510009140200d060080d041102d41c0070b00001e007400400c03e00740d41080c0c03004083c1e500310700d941c03100900031880030400410a60b014459420b0146414500f0081c02e1019410403007024000b8002000162200b4000e8203005885000001d00e91b110b82a004001c5000c03603100b030740c0e45041b442c405010700015281c503104070350b030440041000175546c2070219169609031152000c260070880016800c0d60050407404501c203d01140210b13102c12841620b101c480c41518210001000800c1101c2103003482d80740344001e0f1201140032002e0707170300ca070406c1420751041881 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 244514460 1250 244513210 244513219
    0xc13050a020f22060203090a0521030a180b0901080f060f04020d0f0e210d06150530060103090c03021203090102300f09040905010606090b090906 64
    0x3a03440120741c0c1500e0410700c4a080d0303290b42c0d41c00240d0303803001c001d030070740701604910040030340040d0190000007210000e40340034160740745140c904020002030355200d000d1040c0d880e0100903030580920081c002071048410380d8807500d00040441d9030010f16031481d9001442242010800b01281d070fa08044002e40c805045107030b88125a0b595070118a10310110301e66160020300201d00800072208030342114140484880040190350030380307030100340c4d41c651031550380d04801c89545c410824000900c1c010003100880c400041180c903907518a0000c0440c0b081140e0700054400301d040301000070f125140c6011103003203980d84510644801034111034640e0191201d030502d5640c0d5000d40c10032910b50301c105d000f1034008107044002010340487c01d0b100d9000580d00340c0140584000b0084a0150041c070b03000c41e5943c4403242c4040c1180c20144110f80d4000d800013038090b4005e05c001e00319130f583c501544020f503110324000b00b107007880c2280180103400c1c0342e0883c058282051190715555201c40c2c0186500460448 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 244515710 1250 244514460 244514471
    0x81b090d1403040303170f010b0a0201021e090f1f03020f0705032a010e06060f0432060a0b03070305070e030610030c3c03080a0302041a04051305221506080c13 70
    0x7506900a103b00045402c0100120207410b068010040c0500541182510b001444164600070451125241038100f415103400d90140c80e0b510703100790f01501002a40414561603c103141d1603c0d855a04103911190381d440c500300c04c0040c00100504007905000e5178000074000011490381d141d271241401070245000b1541c0d0040b5098507601c1380c100713842d0701c00c0b0840903401d030024004111401c030554032907002690704440c020880714240001408222440d1045190031034450b403008070054200500f4000802084000450741d41e50b041c019039001d041c9600e41103000e1855132615100b080d24a611840150a81100c0c1c4003000348112010b000c015560b8051104420500d101d009140d54039800107081c403000403403031501c0c058142d801032040e80d807140070301c5218944640159169101313a00840d0740122241050b4180060b5542003190006601c8031000820703030000303400d8220b0505032101951480a031181b4080b46040c0362046030040d284480281c904000748001044005d600442071480203036864 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 244516960 1250 244515710 244515727
    0x2030a0b0d020603040f1b08011a01020f030d0b1807020f0d2c0d1703010f090204060c0b04060e0d051c06030807030810181b081b090d1403040303170f010b 68
    0x100c1c02047c00d81c40502001c040691180e80d00e5000707040100305280b41d003644c50700000342507000185010400000d10001c6151002d1160100050620b086103180c120000366030244541d40c0c25010140703d40740a900900c4e901500036083c500d8001005210818040710509568260105a8103c2520405034008003031003600040826000c0e03c00800240c07011218032045082d242c500d0b001981200c200f2001e11042541ba802060128842c52080b0341c0811605035290001415910003252710501400000503840401100756007024100e1000c640020360029070211052032001100041961401d8100f00103411a510f04800380320303002c0c1c007500340040b8000240c15080e002d0804009480182107481180702e465040201800031040240d020652041b12600d01600c2800380fa849044401c200400700071410080c100a98401808035410804800b5480c0124071003002c6140d14445120086640e01d10b58240280101c554a9024908030700751001d00c0300030700f00441c0d101c0c1911210b0b05040d42c0c3c2c102d02d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 244518210 1250 244516960 244516973
    0x60d0c030b0f10050906091c0203210a080402031501060f03180c0302041104171501141e04020f0f03011e0e0c0a030e0f150106052701021501030602030a0b0d020603040f 74
    0x92144032588014045c1c0f808d503800d031541c0c41020b880351003030781100c02080c0c0b110422078041007105189100c112051220b002421710800926403c1030000e0240c2d03208000000c039189117004c09800100c0803c00c2c0342c1882040c2c550500c61280d46500d40d00d0341480304103a960355040c1e620a50b200180c481c40e126031802042045080889004015076080d1a04420000c4159030b1118503a1088030340c4103500c07900000d801da05007102100c108100500c00c60b50a403004070100003034840b085050340c11660070701020703180d88400c00c02080f000b1520b1140316140e6241c424107240a1000320890b003420351550a0820034082c81d1004660041851304020307840759443d0b18102e0041c103a030036a00410388910019140e1002c004035080d20f000900030543c2c0016038071341d01c043c0c440e1302c40c4103c007075440c40c0d410192020310282007594025011051058a0000301c1c164070030314400c2c0080c0c00540303419500006116400b2182d100d5000100d00a5804005512007070700004c046000081018001d011400e01c1c55081000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 244519460 1250 244518210 244518217
    0x903080912072706030b073203090705030706080a020f210a0b011e0302280f080f061813060c0c03081302090c0a030b060d0c030b0f10050906 62
    0x7030500895640b295141071140d40359810300c100080c1e06a500c801d015100180740a0300f0705607900030300d5051150310388040840b49035402c0b1304d2a00010250110b02580901045800e1951b4002100340070303240e052617100d00e410300289521061103a0b000407002c0001541150b003260307101c00b143c000181c403013504d045044018032038418110510318550141101300c000354072440c0c0c00703a042641c080052000140055945520b111000c80c20041902c2c14041d000e03110b0740051003c1c6a80b02c0000c54648500b007400540b2003c1502c09c10b010840004000c844503030300120540e402112003025404d0b80c00c1c1040402c1d10058144004140812030100240307801418036110001168404020001c60248050090110110ba00f00f24000f40c080303000b2400b4007414408028007280c0040088560361901e481c0304080d030b4403154940051580b07d0800300c9503561071001905060550200200d0300300155080181104d0000140034810115001030b1549a16440c02c02d80b50101c407401c18995500e86071000454500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 244520710 1250 244519460 244519489
    0x106092303070312030f060f050d08091906230301061b0c0e090c040e03090f01091502060109050f130308130206130602190f02010f0c0503030f1008010c09030809 71
    0x105102c4000700304040707400c080100c0000d698081051001d008540c005594007032041240310707040c004c0240080d14000b0030b203c40f164407809134107240a01d002c0215900a5100180040c0070f80400e07000c00155801020240c0801d080041041101105000c000000d0006009800802c52070b00350840001038030348402c1d4030b165006080406000e0750ba40c0401c58500d022a0340d548640a0071104c82d520341020b0044800b4115540c02860038102e5100902c0321001881e440c3d24104259420001140088051102400d09040e40644074541c1000c40120584102808617034050300c2000c20021019039a000d000d00041c3d05140440480e00d07050002c048007a20710b6070180d84100c000a0500402c00e0300110701044034015000c1d81c0795450442d820031030030380314414040c103155501c508200c015803145c0f60b40702580300d0b1820144819802916450f245800c03c9407840b24998105050168410b46072344660000d0003608020302440581b42c030020000419440000e00d2103e0200c1c01c000c082c1e0303454001a8016 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 244521960 1250 244520710 244520713
    0x6010e0712051303030b0f03060109020d14041415040308040b041b0605070b0106020a33020304050c03010b220209030a050109030203071506030c030b1503071403070e0106092303 78
    0x60400c0b0a015903c00d0440c41c044000c20b03e40426135005040018110400c000001c000d440540c2ca01030070007002c2d6000b4100c003071445548403000d2100d010103080885c0554001c1c0020b07400310100c009603a16004401c095100985101010171001035408148150301c0782d03000981000e036403924917108401c11059100d40520100c0355900ac91000e610101600055000700303112031859a8500060341c5a0750400d070050007250401504094030400055102100054915034040201d25401542d027280c00540b0126100c4d003210640c13020a00c0d0034091000e00100440b90b800c1800d04040c000c0c5907404201400203913158000c54215040d660070300c080000c1c40c1d040b0000b40007403091481d009480f030b072040204456415004c882c9003000d90451051006595100d0003495000e42582c070b0381035840c03030010308054070244444c0306074600d510240076140003000b0031840c030101d103203c00b4105404c01201c0c1e04601b04010042c8010440b60351b201000307004031250f41d2201146484404005810240310400c0213805 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 244523210 1250 244521960 244521971
    0xc03010c020a030212030702030921031810032705070b0a090602070e0c0a030f093003050606041403031308060f160c06180f0c030201110f06010e0712 66
    0x5150300451495242d6200c1c1e400d0301d411307101c002e031400e0721130109486c1107006a006210b501414105144d520020808503507401c2602c80441b110b4505c6c607800043d03608107a10340b5000c2d810590500700c0303e008803142207080600040d000032990f50600340c824075488604145031100c00e0103000f03052001e000601140744481d55144900d500160007a00326110303003c01031054000c002100c5030381042841c0a1582040001d24007031041030100c0140c0607071190101c0266480401900050b6400050f524084042055082d42d03040004a11001c00710316030b410303082c581407104009459450794103c500b03407a9034425090402441c0401b00b80746000305203900c490700c2c4040c1c00201d003508001500b14170036050180807540594480100348804071980b503018010480311102800040d51a80210741041914030b40f003038000001d510b44007d080c00c3d1301070a80303458880311014000e43d60700c400340d80d602150340001000300c4190400407a98800c014401e035903113544810045032034217100b41e940e6280b1446c001c006001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 244524460 1250 244523210 244523231
    0x4140a0f0e0f0a0c0f0e060402180306071110060e18030405180a0b0d051b01210204051003050f0f040f060c020609061803040b0d06050603040c1d040b0c0c0c0301 71
    0x6a450703203944144d801500c4440e00040002c100b007400c00907143d40c041191502c2e01e8030010b0002a41042000003500790b100701008179179481c10001c40b84110b10541d641272005580a4249003424008034450023002d04000c0103101500695001980010b021680c503000c00f440d4415190950165030421548002c00351300c8103041007629642070f801140c01c20420013800740740000b000f0594000c904020060b401400305aa1600d000c1c00701800b52104c1810400600d41841e241207900c8000c0c0400e0321800350780850207008900304001204100c6810f07081c20011424403000d010b140c10801030580d0010b0b0410000182048201d1001c0c0c040558420001c0c00f01c1840c103000a52583d02c2120703086580e104050001c1c4409034082d034482c0155000303d014510306401c1c100d402c1151b17406114000c0235152074400000f5036444e1040158490717805a00c07403042c41404e09002c014031620701d1034450048070201050001050520114a070084c0803920349559400c2600c403007030308080d1000f0105905520b0268600c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 244525710 1250 244524460 244524463
    0xe0604030c050c01020102070b06010302071406010b0c060a020c031204030e0901030f050606030a150905160914010f060e010e040e0604030f0f05030103050a03081306060b04090b04140a0f0e0f 84
    0x59006214500f40d0f03151540d01e4004900301c1c060f2180142c0040543d47c0861040d5000f50b004204030b500501485091611104a640c078000b000c1e1712407499142c00160342c1c155030100348580364008060040940c6400000e491080c0e0f03e000d0141185600c0d480400410105401500d0300d03900c26030b01910401240da52814181c04001403650147e496003e20700000b0020f02d004100c60801c0c5038000800100d014074aa01d11000700301e10481254944100300003a40b0440314164508010521818040b811031034003041d8030b86551040c1e10000f950f142010003402810380100181e0300a207000c0c81c0c111030119115000401804550010076101e004600a100a042d03200302603500080c2a03444014510940e02d10441e4240300034030000e84107801000210740000d10903003006130843c9002e0840b441c02e01716a00c03007008440c0154000d42290400244c1000210f015000d494000f00013182c040000c454030b440300c5103034100002c10043e5503c1d40c80f006145d50815680c090708480b040c40003180e1400c6a45400396 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 244526960 1250 244525710 244525727
    0xc0d0c030c14130e060406030602070605060f01050a0c08131d060a0f0503060a05070302071b0602060a0204031109040203120d09020f0307030f03030c09030b0f0f01090c09030f05010e060403 83
    0x800004001c40c00d4185034000c00000c84410212030f071001c04070545001d5a180c10200702610582d441600d5080020100d5003c1c0091b0a80e11700602c000942e90034510100406c0c2061150704506121060001580c059006204d0050145d003004145603a54240e80401c007044040c0e030800e1100c004644448050b20701062501441508182c9035503411300d458050004404d60340b0302c20664158000c5000402c6644643c224a030000780c00d007405400d241c410b9803003401d003105000c0881c095204140c810040070317a04200c19034001c0030707002c0e0440c900340c01c0d0780b01e2030805040c69210900405510001c2011500e0401040e0a82c03031145007020780303c81440f080003014100880701a48a103c4054110100c1d2801060b5442240c2d0311100700108114159000d4010303250741d007005001c1c84201d500004c0032072080c0e54190700c01c174034200c0200b80514010060780c0307000c1d07410380040310794515002c424001540c2242421096135008030060070600300b82e02c0c015000d004413441581b0680102e005200c00c03da04807450 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 244528210 1250 244526960 244526981
    0x120c030d0c051f02121f030f0f1a070201050f071b020d0204051009050a0606020d080c07061e0c030c02071415190f0305070207030204020702061b24010503030307080c0d0c03 76
    0x40344050b02c1b02c50386182c502000c8001e911001e041c03a0400c1000400c5140e0307418841e4441c202c1d00420a00c1901d03094003440c1c1041c603a485265070710b8100311160742d0a1203907d40c000c08055644449090401005050b96200c1000100302240b400044066540780900c0d905c00503802001440186081220495848100c1c030549009506100c049429400c540c0a074009982c1d0720b0303004000301c824000c400c9448002c043c2042c1c0d60030908212950124030740e8016240382e40b40017020412900c3c8400782c05012140000354a208151030302c51649080d0340d01003042002c41d4900440b28000d5501540028180000202e483c0030006001844044420040010600c00c1d8038070345030b00301422800081039090b200121450401604242010700040c98158041c0c8032841c00509101d0418105109025048241c10718804185c1e0280040c08000307107800b40c0049598251703501c019002d51402c0b004c0f9969000c060102014051410001408000d5960540d141010f04610602017424500d10240c002c1118442 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 244529460 1250 244528210 244528237
    0x4060c0c120f110703080a030b01111203060108070309111e0301090609030f050a052d0d050103020a12020a05040513020306010f0609091a0112020f0a050306120c030d0c051f02 77
    0x3d0f00c2d404440c04203c200c1160380140e4507a02d01a1070450842c0204401d000e261b0600840100140c1d0030300d000c00100700303801c5d0b000d000d19a5038103182002500140004060001705410702200c100000c02100d00c0c21132001041e200c203881f8802d04590506c070070000521160b0517601e041c0002042c40010340082610b60f000c2d4a031540d02004040c1d04550318442d008840011a000300864446902008a4000c003588030510302c03105001002c1004a159000103075403416591240c005000354034044181c84010008003501074407414940c1e0200c1c4400c00039100c1d15108a6640d400194200300007000240401c2d030090603a4190746c2c403098540c02c0003040d4020304000030780401e0040f42500051103041f1345000981101840d1418040046030060115200031b0300c190380a000c0c40040c1e0071141d01038500450300b515040d48914040c0300703201d0518001c4c8900c404651050341c101280c0d0300e01191a01c0261050f1404810240c0c60741001450060b44c06001a00d003c5080c880a00246440d400380015504d00e15 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 244530710 1250 244529460 244529477
    0x70210020c0705180601050412020a0b030c0a0f0504140d06090f121107060e0f12030d0c170c0307050c0c06030f06270a0f06050409050d08010b1204060c0c120f 70
    0x103084c0c030020b0030f045030140c1c0441d0080100b07102d444500949400750034801841e98040c6611045042c2d85038200740d0740ba4400910200348078000681007100d15110b41824600300781468584096181d4a1100c401d000307006110a409034020706c490703500810394040e003102c4c07403214514142c6040ca01c075403210ba00e0400007907030119080711844c10202c2d01b40e0441c1c83c6640c441ca81942610100704100d820052a5a481040083d0403501110148054407517400022400038880d00d80c102c002e8181100302000e0780e402d010328810080c40d038031184141ca40001007807030031648070030461079014a0b100003441e0381c81d0302000200402070107140c008480c81c401c0d68191024040c5900c00c810700784110410040180c50742140c000051a012500d5100a04142c0e0180c00400d001d56100c012900321200340600781c03100d8105040d4018442d401041c1c20b40102032034200c0914200c44030003c4540340501400080550742c4880762408518495003e407040903400510786681c203240f803480908050541c05039207000c1081c0d007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 244531960 1250 244530710 244530739
    0x10f0212100e1902090f10030509120f0f0c030403050f010501090f020a020c06163014040b310e09030901050f0307201f050c090405070210020c0705 65
    0x1110201c0c0961004008059949000e114280c0a034204811140e0451b500b0120590a541d41c015445080c100f0b50b14002030506000f080b01e42001c241c070142660f6014204000e0900704c5104086030611404480341946401424086c58194890b9500c0074200744141581c89201443c1076105504807202007008020100c450b030b007075000743c0c0541c01981c4056004001603c4050420100808200c00c03501e040c9020f00009540300080d01c000784c0072035141610707007158070442c02b0910f101c5902c101c074003410010710300a102c120503481403081e0302801a00709001304990302c4d411042214010507608184100382520900c04030040c0103201841510700c6080681c0209a0070701010040760702520040e581c451a04d4407413410380c101a031000d400e900802c103510041d0400b01c03080d1401e800209080e80b0150a6080015070071008207000d10400341500c605e03002c207001341c92040d01c0441310240400d880104075603a40010690500c5080e44004410a0001411950900010684600342c6404403103030440413070b18 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 244533210 1250 244531960 244531979
    0x1109040e0f1204240e04110417031c05010e130807140c010e0f030304050108040f140a0302010c08010e010314010e06070905010305130f14010603120f030506030a081902010f021210 79
    0x28843d264042009886004117604280c0c0006030700e0860318680d140340594a41614200d40c5807030103c0942500049600140096801c18a080c0d4a840303100074012541844000800d43e00094803852401340c85014490800c00d0800c140c600082d0000340081c0f140c4030001a1a8542062141d40c1d0700246508000b801e030351070120101d03a0b66960103001503090074100070041d904c05101400555110324800c00c7d200000741414800c010020030034000d484418403600c1c001c1c1c207644081804a080c08113540040c030000c01032181c1076044075040b50b2408102d00003401014010110081102001d00550701013081d4039810000d1601103641c00e030b8041003195a0100030708141403002500400804200c00f13204c020580c1c400c03010303601c00344a00000a0065891361000c2e91011000d100c1c0c000b160700d40e102e0340351268051088943c481419005060f0b10070056403511000d110300f440c0716441d00b280001400806100350321901008044d00300856640e40c924018042c00381d41120400c4516442480100d00001c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 244534460 1250 244533210 244533269
    0x17060709080c0f010504080a03020718020307020c0105070218010f050a1406190909060306091e050a1b05181005120304050616020d0f060c031109040e0f1204 69
    0xe0300c10141c08050054020440c98030303c41c00c01103041090074040880c000c0824003d40140510a4009045652074032034508182950703003010000301c0c0d1051040060164000c6083c000702c0e6002d181941d50b4070f10fa40300088001000d0b000b1800d000f541d04e030002c0341d912015130700c0d030080e07030383c111500c41001d07513540301700584040c1000b151030f08100d09000002403481c1a0902400207400781c140b003140a601d80d81b00f20112083c0c0e0340107603001a1100061001e001041000340383c020380208950061040c283c66460740c44041c180014203806406c140c880c1d00171a8010b45001a00c0e000b00103c0720061070300e4628410010650b049040d04105400000b03180c50f01c6400350480c40402c6025504080ca0001000f40c1900301d10003095443d40c1001440700140e6803042035000407442024000c00301052410204111281c0120103000c0c035241481200e00841c00380e0a407104003404940114492120b50034050508402d6050305003180300d161840b100b200c40303030805802a5a14070761084105034454409120401 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 244535710 1250 244534460 244534469
    0x1050a0e1e030f222103141903140604060302011707020c04021b070803030c070b130609081905120f27150a0e060601080a0f0617060709 60
    0x14407841c6038140c4402000700c02030002000800780e0b07080007a1008034211030b5004460380140322041d048030080b40034031120030502500a615018142501c66202c20b10b104803500000b8040c80402c030104180340004030103c1d960004132840c5a540804c014502401515502003048111500c610000e002c0342047c2c416001101d070140c0d19900a03400722216500d8a500150003602140100081000d064079540018107940024807a803411301e440c5001040d080c1900d80c0c02500c03003a00b081086c0300001070a03106541c1481e40140c0200600d403103d50640050600341c00c001412a4144440071042c030020002828071f0000d01d2590300b2a0300700c82c60342201d640c0b00340110600691040c40108507400c20309155680d1124801d00110301902110090506152506502d2051540290304000e00710340800906908120030362400e0045c0c2018101b96078817600f000349514100040c000004090001ea500031040c00b04100e035080200030f1f150408000c80c0042d00d614040c40344070304c0e03001c80c1104d0303c01c01e200c00803034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 244536960 1250 244535710 244535713
    0x1110c060702010c0c030204110a0f03050705042606010b1b0102090319050c090903030118091a07090e010902040501030b030303100303030b03070305060f151e010c030318031101050a0e 81
    0x80740c660040d986180032220544040003441781c0800181c81d188140e004880c100c01080c3c1c2c80d45a6000000c0c0807846032007050040508200922184540001c10384090b038800208030300128a403482c0410a0043d000700d845040c0c4962800042c03085800001460980046048dc0c030540652030070341d500b40c0c81081d040e6030700750b40008610140100c020707010f030407114450001d803169101d030800021250a02903912084a4100000420501da041004019070001e217142c144401c00c01600c1d0884407081c1c0c068010444103403600090082817080172202c01402c00384280c0c481d00e513110000103000390000d00400e4003080c600a80898545000030a8900c80d000b0400d43c500002d0071981c048018041c260b400c81e8141c410510080b000400500c03200c0d1144002c26504074862906a10300081a50001a0ba80c0150b8001d181c1001c4e50f18184050f481d81c40d82801c2c550305110b09032400f1401424819180746100040200701d130100f5034031694036100d0300da1480003842652105082c02007200d002104841d9a07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 244538210 1250 244536960 244536967
    0x20f03040311060f04150e09090c0102030316052b06140f13020903030d0212010608040201050703050a12061701050c031e1801020c0a030906170112140d020a0201110c06 74
    0x50b480c08600901c440e02d02c007804c160600d90740b44240c098136603113110000c001c1a42c1070011006410f1054109a10a00c80801094401ca08000203034803072102a220680b46d0003050380e40d80790b01d4041c10072110010544505043d0300e401200d07100800441055541c07091a062040001e14080c884401480840004040e0303d95609240c0c1007050300d0125211501c1c40540a0000398010b98080c0040c111103107440d074015a580100c190780a08a02c0142c012805202001d01400090323603000041c1c500e4030703601d03042c01135581ca00c0003816104901121450312545080006c081003000712a1204010785410310300074019921080242260390000302d41032180c40741d4504441e9000c1201194840e000050400e50084045c12540c43d1800c0e6805180c810643c0e03171001100c082010b5001d03400b14024802071520460040304001211414031041c865202c02450319a46881404550741e4070302d051100450403140701c02145040651a090b013208142d002c01c402035000c070700d04a00443d0301d10784040c0050002d4074 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 244539460 1250 244538210 244538243
    0x807090507210e01060e15040e010c0509010c0c0803130905090601061e0512010e060102070b0909010608150d05010507031d10150e09060f0703090c030206030a092001020f030403 78
    0x410100d0b91020f041e41d281c19001a80302003c0720701501400c24861801c517161089410310043d00c43c200c00c808110f83c0342c0b00d040402e60f6404015140ea820702441c0050700c12055040c50a0448090340020215000004030910508101030350354045811945042c40107654903040d2a4a5034000d10440012803120040b807000050316125a503121001803c115003083c9481c2040003c6000c00d8004000340000401400780c10740c2c040140000400d01e52000c5480c01d4549004901e40310418401c60003444880400f01d2680c010210819002c0380c009400301200c0b8142c0c1c1002800ba0000742c9201c40481e01d440c66000f12140d51884c4098206a25001461846c0c2100c1c80313000103247c03203040c40a0f811060100400c0c20740d09404072a000b8400d035030082546051221400c4040400030700841c00b85490040d20800203a8440803030004c40ea011200d5030349030740c1e4440b050000b0303100d0714200401c420068240301e40b09082d05484c5500030042a0300300c3d0724280c061100d182da03d10a03070001400070301c40c1c40b50310030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 244540710 1250 244539460 244539527
    0x912030f0809100203090705030606030303010b2a03070b010e01060e09010b2a0d0e01050403050a0b06041112041401090510020901230702040522030c0204150807090507 74
    0xa800600300b01c1195100b0703402c05507440890304182d400360b81075000340304100031038541086443d40001c8214051440c1d945001c043c600340384204005000070044100720320711046c008a40d440c60714800c4c0340550780d441c140c510b0a81da454400b40610b2250819407000464440e11a100310141c0020142c9070404036400d0035104292500400d6401450060407079003928154075042000294843c6080145110410441c01600044e00002c4181c10054144401c00c003090000403800b061f25080340c1c40440684481d00072074050700441d20039031042c1300d0000f5080a6546144080d5108601850200d0340c0b111800607508c1c00d03200c0c41200501994000003101c00b41030956401406004014100074030485000b070018029100318080c1c1e01c1070400045505002d60416000f051342c07101e02c55150360a603403803001c246c01c2550303245d0348050100025440020219100c5500003a5440c03030444030400b5481d65036035165134884a60054514260400c40840c28580c00b40402c03528814001244801142e40c10b100358 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 244541960 1250 244540710 244540727
    0x7120801060c110a0f0e0403080615040302010509031204080a140a03020a0209190f0509010513080d0c180b1b15070c150608061605070c090b151204030912030f 70
    0x10f5522201e00b1600144041541034100000d00b2808400c240915182c10701504c40d400c0208007500802d100d007440c460341140a01150203072942420b200362a0040d9102003842d100d4000d05811203030b0030000b004158030b98001480c1e0402e0348a1440400910011900540c4403401c012000300943d02c803030000e80c0140342050386a5446949502400c070b040801c50700300400c0e01c03a40c50304441803540d220244508030340280282603104442500401400c4000e0303968560f240306400c1000c0c040782c0c1d1440c0b41e4841038482d000d004042514080c07030340e04458403400b0039005a80640e4160107102151400b004800b40b01140320702c2d00c12000c5a6454080d03541080c1504e00612800c130031107600204000207440f0603901e1055201a00411004020341e1400c02500c410440d40030110070184002802803900146035000b03000c00b602e0311410007040d0a543e641c08100d03d102000381212003d0070111f4918006086040410311070340c060754414034082c1d50b400d098000d480c0d07040c5014002803070b0010b034548a6030064407078 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 244543210 1250 244541960 244541993
    0xb04060b16031133060109090b03010609021201080d080915040201140315010e0d0b010b0904020c0d0507020a0e040b1303020f010603030503010509070219061e06030807120801060c 79
    0x3030321111980300c1c142800d041981c9041c00320140b00710400c480180034445884c490703c2461500c5071803403c0a0002910b10f1290707110311501142c40d00000c542d1a1400e400840c02040c0c1a070b4190b4031040c0300ba50070b0304891400d01400b1654803541900108051007010b00c80c0c000c21594000d01805115008028101140204142e060000e40491209696403d034000c501c03640c10001c2e5807280c00722003c0010010718400320700340e115000b4110100302180c24109460704450101010715034410400c400704001e4003a580d000c1d0320072b0040090410100390407000600d8003602c2181c0c0c12511a40303401c824101700005540140194459000290780500d4102c2180140c0e13009004503881002e01c00d140c41e081d03803030541007200011800f000400940c103000c4107154001c001800a80700d04240203042e620010b01e001ca003c0c00450b00c81d1a01603400c4100241000c001140446c01e10100c0d890b81002d0031280c0c449071045604030301840484031401c0c031905e1000d0580d051665460240300b004c1d02c5511a0264001c1c1c07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 244544460 1250 244543210 244543217
    0x10c090b0711150403050303041202030306281e0e1b030f070306030c0801021b0a030e0d0f060f090302190809240304030804050708010e0a0206030703180c090b04060b1603 75
    0x1082401c482440f000b41c00114451002103640b40380614102e41d00703500540001c0155442072090007019903400b02d0800c680510380014a817034484007421500c40a489510055500080c0051301c05d0f100c4680c035101e03098542c40c400c01406500c4840c451542841d0180845461032814008a440c02c0ca0440a06421039204c1c0b402192542d180d86843c51001807641c03003d8926903002030b0401e02c019051805140040040028180614450728090940300c400b441c03032440b85c41410341e00c50421062000102c0056005481003041d09404002c40340107203402401500584a0084207075407002c43c640c902211580d0140c0c40c9401c0c2000b02049c0080f00f040d44588100411b85d0101f141c500244110181d032046000365950a440d04160808504140050700301400d01e074100b140011348203000088c22503000f581980c4050380c03583d0324402100108086250301e9052905101640188201c0c0c004400583d541e008040119039042c804103c111034942c460444101c0090044000260200c684202100c2c000d06 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 244545710 1250 244544460 244544479
    0x1f1106010b030c0c0c150a03181a130b09010606080123210624030708190f0203010c021c1b0f02010c0b040303051605040303080f06031c030e010c090b0711 68
    0x100180500c241c00c03030030404521b4041803200980da0706003d050043c214241e03800804d51421340711104038041d40190035800010010100340451000c041c000441c1d03400015407085070800d402298060202d610841c80040c00190010a200314240180c911010303140c0f030070b15a0b22800c00c040c40210003410700300503520b258407800042c80390418400e070381c0318a6001342401c2c101c0c1c4c00c040d1170b100c003c0e440803043c070301030380c003030f000501c5422000504050300c020f6240c5000e1401a041c90b10424105c82e2890080d0554280710a602d540754000600e07040003800003031300301d483c40c916040803966602200b10005160300b0701400d50000c15514400c1040890041c942100942c8940d00c8100280000340c0b41180040d58a07020080c502401c006020040e841c0c52504614142c9903803001030840801034609807141c416240490515a4108508503600d502c4141a03200c600d490200039005140c0058075260355405c084130111403a12030048141620070a07061141010780c00d8031039800300d1580700350343c80c0c1101500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 244546960 1250 244545710 244545733
    0x70303050709121103070b040501020601120c050d05010515010302130b0d0e0d0f031104030213020d060f06110105060a0e040b1e0103140f07060504231f1106010b030c0c 74
    0x10f401e02d009040860384494488141807801c241607100000d0414280300500c1a82e0340414a641181c824190500350b80006080c1a6800c07142c50707100130340c411aa103810780100001908454850694611140740301c41c2240c0043d001c0c0d10031010010040d20035840c050262400c0741c8080c207004102050b0000c1d400c0690a095441c0c40742e08620500481c0c9820300360511107505000705d00340c08034541e1040703007424950390105da11079040c4400d1503015a00803074000d00c014050748c459801000e0003012029020b5440001030310440b900001c2c9240e550a0400144c05810542030000448ea0029a010b03007560383c0b6281c10200e80c40c0504141c0c55595042081a00442810280c86c00396004080480a03914080001c80c501a00402c07460015000390400b04201c503000429901240c112401143c200c142482403d4100d482c41880145c0c4000c240b000300c042905007000b000c001c001d05403104016011034a003407940d1403600b4440d03a801d8040801c001041120454043c21030000100704541c151081d5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 244548210 1250 244546960 244546979
    0x70c0b06060a0201090c060c150e072303010606090609090b030c0616060e160e07020c130204081204140306012d0e072111040312020c120703030f050f070303050709 72
    0x242d44440002340010704c41009000442e800d032041121031407404c00007501e21411454481c0c0341032085903260b05100d407080c3c40401c061b0b0b08150382150000d0003004090340700d62003d000b16100d40181400960039060100c2c0910740c2e0f02c03500d08110001001004c2400c0310a00700b1540790710010720038107240c003041007500c00900030b030240341085083c41025007040010f01407203011807180b56000050038cc1044061000c401d03004103401c80000d6040c0e8001c82808041070707484000e0f104982c40003010f8483c1d10300304180e81100101400a452003181c01422402c1d00904043e030382d060a0140c4080c03003c0321945070700b201210126000341e408008030948545540c42442d407040d40c0741100c1100100c0c5c5031100304c03030039149190b42d140e00c0c4803e0705000304010085c12000c0c0820740580d0100504490000b10750540d40f500130051484011002005600c031002000700c0551070f6440b62104901050b40c02c03241544a9008500391504105220041d5050408035241103002d02005001c510a100d605440465080c44 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 244549460 1250 244548210 244548233
    0x406180c080102030402031212060d140709020304020f060a050f07020307051203070303050a41010602071404091505060a030209070e0306100807060809030c0d0314070c0b06060a020109 81
    0x30840700058032480c1074010300d4102449002c0c0310301040c108000d2006c88464228200e600550142c504900d100020719260003102c485015803d0a4420b550000070b4440300d54000310b1080c1e10a03110a03039448854001d00980d401080e1940d00410000d002000709508014041e007202800101168034699481000c1502d1550030012604960000078204043c1601401617a0300104400310030440c0398000e02e03000c44210302043d02c841c00b1111540d8080c07840b4140d400d1803810f51844130040d281e40e5960b10300c041e58070070f860302c522100c44103112504203c0346440d1103200d0641b50081d0008480c0340c01245100c0080030024011507000307032104408005600c900450a200d2026071311a490300700348100030149003003c000c0c0142c1c0c0d28034600809211440e00400c0c880c0480d1164104003000e5101d016070350741036009000c00b10b50240b14104103407034600c1d815000080d2000d00e041540d041078640006c21101c00401d2000680106005000714a00741014030080c00010340b68030001681070395503915801c0300078 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 244550710 1250 244549460 244549469
    0x10030213060501030b09041205090303070b010f08060c03010e0406020a05070c03141009020f010507050a051002070c06020d021c260702071d04200907090f0503150406180c 75
    0x5640307841c20700555070544174820866400b218000b1152402d45e84002200580c1001101004030204170790665131020010303908803940c131200400b003a40c3c503a440b00303004804134400c3c0788881c8600d0001c0342e03400e2541001c03241a03400b0030007038a4247da070f19211000a9440300d0013040400204101c20008501d4049161001c4d511581890700b0f008400b002c803610300720460b03582045091901c403007400140e658540540102a0a0804548941c46414024100141e14101520130301905500300b89110381035000340091403080480042c1580c50340c81c1244d0342c2c0546155600942c4c00007446a14161000b0000c401d0a549071405a03485105c5041340c100c0d0171204142400f000424005002095070107000b03540145c080039185013040c14203103000001c90b0314054000303003614800300d1401c103035420b00d65803404400f032014042d95518145a000202061071900c112106180740c0d16002c44c1d140380c0031032590b00d0f4007003074402c0c081c0c95261a00c4410003090b003125081807210494481400144400f06600000c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 244551960 1250 244550710 244550749
    0xf0a1509090606020c01020a15090206180901090e0309150c0a03090f0503011e02160602070b07030b090c0a03110705250b03010b04030320101d030406080f100302 71
    0x46240103441c0080d02c0303541d00400c0039500030b213400305283e9a00041c0301d4681c03900110485540780e01d500503c0000c10000c00041e402100c0000d00ca640684480c10940018109030340c2c50400c1ea0342c42c034211040b251788082e094410f400402c1080250716100d0803424600d048007403102e103070050310040c4c20b190135841001180030680c4c005c0c0401590703400580500c0140b01c00e400911201c1c0924036903606a188460203011025030100b03140303110b070540c13170b038010805544180c0c21580c0e40e8070707030400040c005022188000002d0070300d100c41d001130815a11047c0a20340c1182130fa81444030340c610660280c888071440201c0c0c241d0501085002ca20100201106450155911184484541c1d90200350307014540004000c184104010000380803d442100c0c00c0343c2c1c05180c006841e5003081d49021840e4040c00072201ca92240c40c0b440422022a54010400d400000a541142640c000c00580c1c07240202d10903240820b41d01f100103000f1090b004903180c1d04c2450800b141c502c003a140c0d800944070b01580c13035010721034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 244553210 1250 244551960 244551977
    0x504020310052e140d0618060b090714090d110a0b0301080f0a050706031802120705040b030a02100f200c0109061809020a0e060c0c2d0f0a15 62
    0x101e06890101521603841c50782c54051250074800084160a0b0122050740900e02c0b00c9017800610903a036010042050900d51302c1d5460940ea402d020000e0b00940c41001c0c4240e948401042c10b550103a01043c088403141210b00782041c108104005d400010214151a9a0380341e0074124895555202c000e80039102080b10b0b942c0383d50400611619200c3c0c0c0564010080d80003034010310100d4000103e840484519240c0485c0e44d50b0401c0d80d2002107a040c0d40b0003504040203031103445111001080300e40a84209490401c03601c0401c0c0209907031136018180107034103d0541e047c4c1c004000d210305255082d80300b00342411100d1022406580c0c0c0e00c000200480000703038000c80c41c43c00340c960f4001d0b8141c00a20440c1382075101030a04c075560108120142c880c210034a80d000920040d038600890004850900082507248c9030380800d0306254035995512046445240b5462110141c1000010308000d04203014000c1c01c40310b44440288100440d5000c90180d0041c5804030000d0150541e1841d01851000c9030b072140c41 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 244554460 1250 244553210 244553251
    0x30c011e050112050303010302210109050c120a0f11040b030303041202010c080603030d1a030a05010e060a090804090c1806031e110a03050c0409020a091703040f09050402031005 78
    0x1101d5040c2c1000c8a501d0340c044180c004100000b051300d065a404642c40c24030074802c160710080c0c0070304610710340c060f5508024203113043c00340105203005403100640744000382440407002943c48456a440040ca000445000343c0c0c0403410480540100e0440684006483d042c403c0009195170000c5600300c0d02c1b080f10300d554441c84d0303a0a00410413000050300b02000c0c03600744040000d03100c2c002ca109402d00580d0700c451182c0b01d1b03a003801710080d0448029095401c0ea80c0c1d031742040d901a018402600c1d9548c42a440843c28002440c4500340b5031030380090f0300030304243c10603510102401c8260f90020070428820803110700d0700c3e0058084001092113803000152401d665801c514804162815100c440745054105048e00d46440212081c1c000350346400101940c40007c0358800340250740003224424400b0130501e18141e003004040e426541001c10610030007800c62002580c9220700e002d1140c00e541c0c640c400f00864602500015005407004013135514580034610b40d102100d46c1102d920032400251a400b10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 244555710 1250 244554460 244554521
    0x5060403080c0d05040e130204111b060c0406090b0307091805040210030903020c0f13050406020408250b0703030902030a0506150303030f06060319050a09020a0b0903120c030c01 78
    0x83c3c041181d08140b402c1c5445c1484843e80420003c2412903807039482000c83c002c66403954024441c150040e00703450b80701d400c000b400b03039042ca00800142c0100d104080c0406c20850b6084103507811504280c0e180c1e010a82051241d81c11600b019000c00140659458040360075001c560f4001700c0100700b50700c0083d81e4030341801082100000ca040010a00d441c00c2250701c080303640810141032900013520b00030340f10000900840c160034515170126400350f00d014140010002c4580003007007120005011181909a50070414030611801c0e0207007404036614440030003680105c440549041c6000c0e042c00100d04600b07130042030500e295804119000d8000a00f00003104900a0321512800d100b54000c60440c50b04440c41440c440000c0c086070b10450000c00003075510351400000c407030b540880c04002d1000d410140e2a002c080c0c0510b1100300d108200501c0e000c600311600805031050054024000d141c846459082400c443d4414182505140000c006000000d1800d0203981d448100203121a00850805900c0e403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 244556960 1250 244555710 244555723
    0x80d200109060c03230a0509030f0706092901030b060a0b0a0c0c06170a09110a03030e130c0e09100b0408030d060902040503210d0501060c050706030e0307030e0a05060403080c 77
    0xb200c041780a130200040300d030b00101c2030303a03801102514000f4079620385016441c03560280c2e1984001012002500404200c01c036040341c5003c2d1f100e1181811102582c1350703c0c0024171820040f034107000d00c0c1c810041021844c814a500d40041d005812501d01c1911168018001d40c802502e420121b02240d208004000000c070300070006108500e000900c0348170340000b00c152170764050220005947c4540462080c000c0b501410500f201c40141562200c0b0380d41d04d40031f06040521a5110b104844a10140728041c000b8018000100d55a03a5884d00a1110700304220075420060040d2041200300f02c408200603030320340010720103480c002d0002c5465120410644081e0344075600205d200c98014802000b02e0348000032010741d1002100c8100960541220b28040103004258072640d001d0700300000040e045401030307540340b5041e000b0740940e485240c40d44001c1e400c1d90842000090103910403c107000200b44241c141000c003c81c0100151251640d0302c001800540268000741ca1030755001514000c400b02c10800f9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 244558210 1250 244556960 244556981
    0xf15180f01050108010602120d02040506160507060302030f0a0c02100507120b1206010515160f0302100c080705070609050f0c1e03030304080d0905120a030e07080d200109060c03 78
    0x107244660420000039100c818201c44031208c05808600a04841081d4058402910001d0105030711a69840400d48081c8580c0c40c0590b4070b401412400f1850500c280202d0703201e000c035988082090340b03500b603c0e000100702d083d00c51030440c094981d0100e02d2a440c0d0042500130481542d95007050312041e480001150741c2e082a9a204280038144135000c520003044003811190115903415030150030f402000114440da04036030654100e54200c0070100401d4042005045001c1d608465201250040d4501220741094403200842c80c040e000840952060004080039481210086424180c85c0d54540c50840c50700d8184001d608601d403800f0590810401d000602c00c42c03400143c000383c2100d008240c492102504c09042260000b1340e03802c0c840c00b5a04154881a40101254010710303000b41a141140c100305c0944001070300b010401c0703100701000070307a00041c4ea41100142c44040307200344043c1d41144504110f10041032210b41c045100039020700c02c1403c40b900a5201294141860340010103c8041c004c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 244559460 1250 244558210 244558217
    0x60112050a0b211c090801020a02150c2107050c0f0601060215040c0612060503030304050d030b0a05011e0309120801050102011103071e110102040605040503060705040605030f15180f010501 83
    0x605441044000900200c0b1050042d42c0300002400d0240480b030b142246c0d0407950031503000141c2090065400200801c182c1d0303040f6030800c41500e401e1240803940c0b0032070003042d05160000c500015035400c43e424190300f12006050691a00b80703401501814a4140005200540c000c440100041601480465100c940d410340030030880c9080d07580c088650000780074000c2080500481c0038051942540201d01425000741187e031240351500c0d00c55640c66207003d065000a06080c00d80005041989c801c106a9030140c681c0d0800300030301c0c0c2002a81c0c980586071801055218080c24000c81c4a981e0407100040b043d59541030590f05260029007034070340d8140e0034034496004108114100798803d1a000d0b50706600d62903d13041400740402200d01d43c00f00ad071007541a51001600280c40d50b0090014811a80d0540035170b0f030140c0e05c2c02800e0381c0c54001c521802c1e0106404000094141d074000c1a46580840e80407045480c07109284049490f0045517214010410492414084404850520540104000d18 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 244560710 1250 244559460 244559509
    0x7030c02190906090b09010e1009050c0409020309030a030606052506110403050d2a0b0711030a0909060b071703090a0c09020a0216050120120c03041e031703060112050a0b 75
    0xf0030454013270725486a074213503d80d59408035890100100440f4001c012031401591682000081d454030b0781e11205460021030320b044030001c0c0240c061130649900c5c1c003055031508601544d40e24420110716082800305c4000750b0319460740e0705a00d03682000c0c0c005135008000412030102682170243c8121303058000c01914007040ca4408056001c1d690070003031513950000c119030302a16440400c1c0c594605105680f8080c2c00081601d054403544103a26100b10394001c041444540c0d9901c44069440c81180c00140a9403c00743d41e00d088101a072008540100b1135034102c80c80e180c0795031183c0a10150603080480c256030000b92004a040e410026400c002c4501e01e20390842503d4000041c0290343c00840026456810070303e401103d041c1441040354030300070360314080d50300e407036000c81c90340ca0340c1c02030180f0b50f51246090040c5001c030641111200c02d50b60320801100d812502d1802925440d04000c01d0b240c10045495624050303020030703020b41d50142c01d08007400f0407966008002c01035894000744034000a03c4001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 244561960 1250 244560710 244560721
    0x806070302041a07020f030a0b10050d0809240307080411040c0206060f0409021c02030f1b0105090a26011a030319020109020306090a03031107030c02190906090b09010e 74
    0x400007071140d03aa900e0725560300c44c14804104403143c14220258140681c0422100b44401403030340c544149030260600001c192200b08005418854001c040d2941100f80074102e458141600000744440c08122002c0c034182c0000002c55403a4401c54100c0300143d4460b0038403040080301c040f03440042c4011182401100d101e500000e42e20100186240c0c0300344000100881d90791119030100001e80d4010f00600101f200e060451262402c038404128004e00c1841102c07180d95002081c003ca8110881c08000c82103100003004440b960001c0e9800c0758880c808542c0044d004051a40342500c904803a641c5c800760109860742607085880e181c0c0e15443e8880c035580c891010b6600801201c05e0074000c42c48001158010070800c90040c940f0b440025014030903901441203440b00043c0d0102aa84695014080c424580041807940e0050000050109950304010b42c0180b401180c4404213801025280c014169035205120544445034811741421360340c3d0450b81d0b02810030000850140410100504150920 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 244563210 1250 244561960 244561979
    0x605030616080712020412200108010509041104110a020606040b0f030c121203070203120109060506040512120f120c0304080712141209010b0307030308190e03070c080607030204 78
    0xe080d0410490590424903890f0311660596015107014144c0720741f5141140b40080e802d004e00c50040040c0f801100500f80e0a62003558102d0503100301506100e42074031140c0d40c40c204071044925040d072141d280e070035211040f050100a050001115401800c090a1142c01e102c1205c501d0200d681c040c0310003008000d4280c400084880e900340058031034604945404240d0ba003003800d00e50011001002c0041800562070b800405801e0140c111040718109903a04c1e020401224420f1080700d4010000b03210401181c41c00389407020194200d10203407080801a050f50195503480380504003803444005c140005412034035100c1c1d66011007401000b6183d810640c49a4080703000340c85c0c0c02068824038900c10f1084034418006030040848801025840d050011032071805003030219240100f540c68420000042c4c42e001852000300d80c2c06442c2d14000ba00c0c0e91211aa403050131042c6042070039203d4246060010080005002d03142c001e0189100160602000d40d04110026111404060040c0030a0108900 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 244564460 1250 244563210 244563227
    0x9120d1a150405010e060c070603050f180a1202010e0d02060a0e0c0f0f060d050106200604030e06130f0e012607140a03060e060a0b03010908181c060605030616 70
    0x80c2424610020803405e80080c085100b2498443c0c0707a8080c2d0800014040d8140d005203000342888604103400e0750b280b004c40a064168058041d00a5010040d0240860303da000c0c040090300c030510000c210160010702e0285000700b295130400046c0d001c10100f00d040c40e61486518240c03107026025041d0f03500d030040001c10000421280500c40e40001c2503c01c0c3c550303500d03011204a1401c83e08103000039a595a0040e100d000c0700100c10480d060f000c0c40703242c0c80c1e50020070034621442d819110302d11210184010302c4400c1d0080d0342e00b103260443d0b2500106a414080c0d030780000800641c1c0c0716440707540c1001c0000c0600a84800101000092200024209100440c042080d901900b4902414000c004001207140303646031b001900749071400001c00c00c0b10b0804100c0d24880ca003955400e00c03005814005260072108604000381503400e003407160140106c40c00399a81c51111004042203c3d0080d8a45410b0189030051802c9a40c140d0751782080060741401d0007100d0707007d082c0001194680d440198050074200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 244565710 1250 244564460 244564469
    0xc0e06150c0f0f0102183313060512070305040c120602032202010503010306090501060e0108010c030e0706090905040503040905090a050f0307080f0306040e0d05090109090b0a060809120d1a1504 85
    0x81f80300d805400c1020600306440c04841aa0000d119403103405844d0300b90a60240245e940d80107402c080108140340200111041c011801d400034501d6954208100c000700310140088803c1504010b001610855500b00180007900549005035641400000250008841c009005000b144000b085e8050303a004415281102d8011801040c00700503458001d0040080d50004c019045038640042044da00551203480c0344452038408101e4282c00b6580300e5580c0080d0311981b030000d04a0791060040d8016a0840d60b0407900c100126420070740c4031151281501c40889004215501c202d286c1070030b1000421040e4044242c10000c0c6140c107241e51600c207814401d9100000303001c2800004200d083e101d941c0b08030f900080c8141601e031041d0540300d00400b1036014080d40c90020b103100501080400340d5104240c0d24250082400d00c0b118944002691841401810503020780143c0703c4540400c0c501c2c0c0b00500c0ca2020310000040c1040c2e00c105259020384661003154003907603c1414688803021a41708031820380d0b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 244566960 1250 244565710 244565719
    0x1606030b092208070609150c110309010e01030f0c0c120806060a0f36060e031c0504033f0c02011d03150a0501120c0e06150c0f0f010218 60
    0x32902410040a14418100c0c02003500d40303080410400d00442451307e040c101340c0d002c000c1c8800e8079030a0b400c9a135400990030241c0e43da081080114520341c02000310410301d035810704000c80c04840d080340703140490b4100b8100c100881e040030f03030240400281d15070018102503581030003000c1d41400e00c040340c880d0149140c603070b00780000d038071005405d81e000740419000400b100280e004034241c0703024890010040c01c60900060328112001040c42401400c00502032070024005000c00c01c0c80c2d60200400d400c094003048140082000040702082443c000c000c8083c01d07a010812004007042c1151101002c6010070001490310047d0703143c2200d50003003174080e12a409282003d80d1200c1400c000e144482d00054079a4988681412840200d075100300300d1344140e00e01c8400308042d0b83d0303440000c10000031800000f410901100d1041c8844003003000c00f42e81101c000b4100910070030021020b01c0f0399900c0000140030719402004200d240340d20400207210b9002038030f0001d5003400c0c59104200340c002a5155020303c103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 244568210 1250 244566960 244567021
    0x32007022103030a020310030b0702011401140d0b041a100303020d0804030c14031606060806070503090d050d090212010f05060f0a03021224010e070201050c03060402031005031606030b09 82
    0x5d141f169050000356821564805960900040c06402005054140e4151801072000020003446240c5030b004025006050130020070005e81d1003030b0f002c040051044034010310352000110380b031600200c0c15101d10003400c0658135a82c20340c200030b4a0003500f48000790402107140100000241c0c000c0c1c1440c010703940011307031090f86502c100c0343c103040d40195030311031800e0446c0350180070900c603245d040841150440350944200b611180412151880211010351555110420404040d80708000502e032400030a00c00150b16202d590001e0a041c507411000001d5030345a68040d0f400c0200e80c450190895000ca03401030b40102c1d4178021401e03080403440040d114507030b50004140750004c140314125401d15031003d004444d0b00d00c0b243c0299220400e00458000c0406140007444440c0140b080c10b008600541046045079990b00c01c110180d48000c09a00720451024000211a20200a0b5013948040341d0f034030381c0c1800c1c24414010211500111214414071600082c41401c9421201d00d00340c00c454260410031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 244569460 1250 244568210 244568221
    0xb031308070f020301020f21070516050a0807080403060f0e1209060904180311030a0503060d03020c0a0b04180b0901060c0c0816050103050f06030c090601032007022103030a0203 78
    0xb501c0200b80c40180d019400001c02101c0743c0709103001490b498204114454400174501102d03280c2510450390314010800c200280c0410786201100240241d00c10811a40c048000341e450500d02d401030a81155050400318050080200601603010301c60300a8030708001c0c070303000180003da442208540c41400f1900c005407403038060720345070100c03070180e00080c0003032007208481c03841002c06c4042020160009001520b60304183e400200c200c0300c1d0901c80c1d580c3d050460f152003003045000300c2d40d800100c0c15840f5406030314429071074490560b0700030201c0c510340c907031160700d130015032102005141000040f46140c81c0208409503907000e44a4190741191901388803c0045103000b411041682e04034035024402c0c3c48000c0441045a141c660a0720401e03a070501241d21410000c0020440c180d0303030076034035412035440d84880d42000c100c07441c0d00200501d008203445000e507400708282800440300c2603c0240c002228400c0d070400750506503d1040f10010349084888414520791079001c00b401e25018203070000702096 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 244570710 1250 244569460 244569473
    0x30601030606020f06010e1806090a030e06040f0513060e0f04020a0b0f1b031c02030106020c090f070c030e1c0507050a060f0c0812010902090405010e0c070305070c26070b03130807 79
    0x11003081c8148100c039140d0820ae0f0f24269100c50b0341c4400c40008403400320040e000d08015040d2030031200d41c41d48811146052104008058500034409051349a403500006203c1c481061458000d403c1140e01e0b030300c6801d01e0700520060102039000700b1403414040144082e42601c00d001c480c90b13000300300d080030300d01401c1c440554158030442e000124880940150007011000560095040796180e400b1110340b038029505120000d07600b1503411341c44002c0300300000c039414090244c03c5101440b9140410b035441c00071001400030712054103031003810b000309080c100400104011729406000102d07010340c060391038000010501d00c0d05101078410800102180c80800003206c0641d8020705000186014a42e11f031036104001350041c0a072144624244400000c0314260542514040d044c1d2034843c6141040549050b20389601c0880704803841c102245001401d0000140003100740803451054101032034025078210704d460199048805c4c1130100304107200c05041c00c032640e43c448690044074151100110f0030002e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 244571960 1250 244570710 244570741
    0x6060f061308060115020606220e071e05090a090c0302100e03010207060203160c021e12010218101d010c02130e0601080114010308070303090c080d05030601030606020f06010e 77
    0x1c19034483c400022419032016155905c1c1001715908444656071000100581c0c403d03101549a1813180c100408030030300304950050030580ca060790454101c80d0390b82d032480e22809000351500440c1808000d040c0300c281fa099448940000c562041400a0b0760302c4c2d280c1840600c3c840c0300091144a2015500030554041c41705520320344070084c000c6480720503905008000e907004652421a072400c007001080303198040c002c01044980c01501001e01c981b0840d00da06155483c541515900400d1410f0016040109000501105a1203500209071076401c000744030701c40603401402810310000b04030500b0100000c4c500d04003a0300702441c040701c038007003030b40042180c03003100412a03032030603040c004122144880014414120b07150700e002000010381d03900c20801c06000030301005010660420020021a1194002504641c05031241229280c0d58a841602e403804600d405008100c1c0401082035a603094401e01d4010b0910340003811601c07401c10621611110305005034150401e0510200d162a03041c110003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 244573210 1250 244571960 244571969
    0x1005040812180a200d0302150c13030609050111250602070b040317060d1709030c0d11040506040507080601030c02030c070b04030b0c040f060309030302070f0305030a05070206060f0613 81
    0x1540c2e140401030070043da0404e1101412051218a070f1584c05542c100507001c000d1a0740c0650107040d4001d282072501d0925000a01840641c400a00c41401c039101540d600710000c40c440c0d00e00140c40c0c50b840c0341082c00e5550400b1080041c00080c401c0746451400c2c803c40320741d203070b40708440c41c2c0e000109460300b40e009004104010300410700920411080540090284400c1d21001c4a0303410140e41711030400400c0181c2130001040321410302481903000041d030014040761306004060340c00b03202c4010301040401c9400031050b160040308a8a91503070303003058401c4a8101130240d03000d22461034440005052514040e104a04055685000401252081c0261b841c2c904044051b1441e1913510035182c0c030503230804d00041c0c84008010011480150801c800c48003140c0124241001031890400c0c240d0041510f44000c0d0f0030303d5004c0014100068480348030040c1148291034107500c03070a2003011501200c0d03004109009644c0300c98140102607a4401031045420000c58030f07075654004085160940c240135500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 244574460 1250 244573210 244573213
    0x90902061207180e04020306010b0f070f0c0302030a05100c020319081312030603030e040903080f07050c030a050301080f060c0319060f030812070c02130f1e0e100504081218 76
    0x1c013250a0514008180c0036500807002c03960180d0300c8603400455171042803400703280700b4410440100010280d940c1045034500950310b00440a40e6600800e0400004000c101c42c1500241c8000900c12598800c8800142540c4002d60070300c03d810f05000e00b200e0f1118000c4007400b00310070014030182a040124030815600c9000100d0350954440040c01400803800200d0214100c3d00d04040782e401d062060766282d40d0103660300d0601e922108110203155201030844420800c0030080700450700320802c014105c0b003a0b43e695803592903140c02410360078903240b003520800c9500100c081c04a46407456085da5040703120b03000012156044000864010714255014424182483e6400810702c00f200016101030701281c1d800804076039036900201e0b100c0c203d20b00029444800130707080d031002600c2c1ea4006001c1c040c103080c0014030152200010043c030302c0131103c0381905589070381000d18079a4041c402e8032014000a44140402e00301959101ca4502418200072205040240043c2c0d0301050b03c5008040c1c204000b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 244575710 1250 244574460 244574507
    0x4061802190501090b12040f030215100f0603051603020901020a05060a06060e030f0d030209040e01051009060f060e12190606030c0b04270e0312010e01090902061207 73
    0x80da07103661a4450b10845001c101000c90004e44251a401191020084211908060390f9155030310a2983c0e442034003502144666050618240042001c8501589100d09120105898049400c0c110344c00340e00208101030404003030207003076440001009903031062414003503110014100102d01d08601c0d82c402602c28420320b42803101ea0784842d0f00c003038103031009a41c079009003102410526581c0c00143c92907001652203900340481c1e980c8240c0c083c00310890018804214405180101c5080d920142d5100b030321041042c0082040450502c55200180188074614040500d0a14007500d0082210700c078a01031140c580a1600d11102030000c60104000c10411085aa0460510300014012400115008601c80c500070440219180940e4115003038000c1c180142d62880801d40c0c0402107141a25240f1500c6110282a0340414809817508000c0035a0000d400c1d89403103038407054800c06921141c002c924015803140035882e00c008803400c1030b440002c00d880c0d940354800110303034184066221000364030020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 244576960 1250 244575710 244575739
    0x90702160e06030d052104030909110c1606091a040305010204081e0a150e0c1f1701050d0b0c090904080a0f0905130906020717040608090c03030304061802 68
    0x1c01c114000d60b030075000c4a0580c001c01500352035a101d01c01d481c8020340485280e0b203201c0203143d200154854401e1408a0a042c1c0e24a00101501d40c607c840004c1c9280c08156600ba5010400c454980c0051f4418030380281468001d015040b61b4072030044984000340215840c00c254400400c40e002554464000c554a594070134450f62654061031409200c2c0c11405094421600c0000c2d084140a8002544420b101284840c050090662030900310050050b150440b10341d9a506040c1c0c100b000b00c0f80c040b0030421091000c001c2c1818521340e442c10718034032510014001e5450b0342c0740541c12240d10031070211650b00c07044049a460f000310801c0990103140d02d802c01c01004850381c0a800070910302e440b100680b4040c0002900e01c114180a0070760010520059107070070403542d410440c8028041c250040c60311055071502c6e4000307000705208400507080080d08004440c2e100340c2d4550b000310001c020713000c091100e400181e168400508003030034081c0c49168020041a0108094600743d42c010700d40c40342ea4451 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 244578210 1250 244576960 244576979
    0xe16060906080f070f08190f05100b1c0b060d05090a03120e0607031e050a05041712070302210a0507021905031b0c0901030501020711040b0f09070216 66
    0x1a0140100068602e0081100c508500d2802d0f400341036103856040f45d80281070740c1103075100c5c401014520340301404100d402070400349100d1550548400707000454603280008070750fa810182940010031041c000c11110190340420380d440424005c080101284481c1d00b100041d0325030203400b980e5550f0918007070034820b0354003000500403100383c842e84911010542400389003080700d68608000656420440000e005640310341d01c20802620f40c522a250240c00c03010154048400c11902100301071b640c0c1d018481441140300200080d02000303146030b880c0454829401e904510080c00d0f503400d06801150405c481000e29404c02000d040295110740103180508000d005000c0075105400035008011001c507440145048400f42036800500441c5400c1070301e030b03000305c40b41c107007410000d0721703000712001d0111560381c6003203050085008400240e01c4005504004550394010000c880c455446c000c1004803c0c2c4441d035803030070411412100c80c01c03a41d172245000ea00b010083d4a103038400b24003400010419101 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 244579460 1250 244578210 244578227
    0x708010603051005011409181911150a051e0d090b06010908150a02090a03030f020c19050d111f0e0a03030c2a0b03060f01090e0a0e1606 60
    0xc0040f500c012103440c0e002d00c00c03110280219002c09070704a0440a01e801d0004480750410310a85807004022410b9000d41d0a141e09a202a039101e00c00b402440180101c59581d00307021307901291a01310040801e0501400f41c40358801900c180400071400020415402007080c82c411400700042d550361201e00400c200802c0607040448010300e505001c18580d501c40c2c6522002ea651940081105c400806080c44607030800400d07049505070200480c00d500e8490065510040d4401e403103480c00355450140181c1042d1036a800070f07016410510200c04020f0f81800d0410844000b61103c0e1502401d9040400c0d010b2a8211385a030440c0141050042d02c06d0161514248522242e681803020b120307817010440032007404d1201030005520f03a065440411103110117105070546020360001c0c1e4503d114103640304003d090b030011040d030802000300140380c01c0080d11242d861200b4a04038070000d04041105032548400b8008410403595039002c15060030082000d0341060102d0403001040d0351b40c03440001c3c00c0c0f00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 244580710 1250 244579460 244579463
    0x1207030609112124030f010603050d021e031602010201090b0705091201090203031210080604150605031f051306060e010f080d0507030c081612080603031305060f07050708010603 78
    0x96040400c612201c6900140e40c060f0041004549481c2040003540c103952013010107159050003040340120004d4024803a400007184298040d1034001e9085001a0410503942078540441e243c040e1103502410380482110f100040b980c00c03045a00c0d0590004074010005920005e00c0d4020b4078080c040e80b941c000010b014600001c40b140308204800c1c00586007614140a0001d40690050040d102e02c036402c180e00383e50140c90040c004117540e550b120707041d260100a40f000d544204503143c61110991031406400b02400c400d50042c802d034034548094103d184c200b25084e029440e510310100da10400b1480040400726004082400500e486415407440c100c2d082c0310310401d01c0d486810001c1e040d000480e03180c403070080903150103042c4a0f0310b45043e034003c014644100c03029041000790b90307071340822040d12404883c001d500c401e00c603440f140b401400302d0202a056074841e034014800011116400c105800c1034034400c1d280f00e611a400501100040c2c025028010b240f40078000c0301041405055000703d0440303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 244581960 1250 244580710 244580737
    0x7032f0c030703030210051e0117010b0a030f030c060f1109090a0c05040905070504050d12030e03190302090301020405040204030b040501050604020403020a06300903090515120703060911 82
    0x4180c0410155034001d076110060158100c201c040380302c01c071142d01c8140d002e03042a074100b6185103d03108012880c1000d810012a1620381051620024401d01c5802d4200c1c00c10341c1c4412426085450702c4d00f100c0101d104c020100601820709000704011508080d4000601e4201808001c040309018400c0350418050180281f00040c000740c442c00843c080c4090400d0700303442d003030b2030542880741c440060000240b50700144282000001042e494004410301254015000c011641c1031424005050307031071108081c4a01c0d8000d2003804004850f107d07644424158500b00107076905002004a40640950350000340d100d4404240007040c40326400005105c0da114100800607a07451000b080700304e0080f030001941103003600b5801d2003824004c1c0941030b428402d0f03625084895002c19424641c401c0d01480c502d002945801c1318500b09604060701b100075100440309811415203945422605008418078441c25010034408a0039450103035110001400308900148503a0550b22000c240e90743c0101458042c9 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 244583210 1250 244581960 244581973
    0x906130e1e0d050f0706020715051806010b0901030e0a0206030405030406020d080c0a030b030a0609200913030f050f19080610090b090f03072c130807032f 68
    0x881000c154100a0002510f5450410b000e02c1300d50240d80e00b082800f03e400c160300300407500104150511030003a010009002252528200744020000c440340741e0b580c40e00380d200310010f001001c80d4400740c43c2001d20030b00c0e00191000e421541646805080380000e03412610010030321051110110082c82925400e07000c8880d6230207121070840348a002100c840408000c248215034029200390400d00001c00011304940b601c81c00341e00c51004862120004070313229118000c0d041c480c03107003e0303c6120407414116503602c5a454980b800076650ba030545001400c10088503c020406405842691381c06c0441203c0c2e141c03034165045007290070060703ea15120105045100240451404901255400300569280403032207180c81403055207a04201d0907660b0100180f40c4241603902c003085800001c1440103240c4c40d4440c0d041000e541900c3c500c481080d02844040d00300700c400740c140c0340b48085d2141e102c0d80059035889141000c841820001b00d10500c0300800b8000c00714520503641007101c03144802c1095070103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 244584460 1250 244583210 244583263
    0x90102060610050703030507110610090605010302070305030109050907030b07091d09030a2d05070204061406070b07030b1c14030a140304060b030a05030714070506090906130e 77
    0x844502e80707440c40c00000d81c10402c0e1070000303202ea08072039004840c5041c81400a042c0301022424801c08954818090710100d070100202e454074007880340200400e003811480c199464400811610050180c041007586500204195110402820009640200006006040c0a1401081240c6a1042d4a41c0103030030342e81c3c0c80800a080000b20300580d07145c0d00552504c030904038141c40112500010354501d2840d0309006000704501c1203681030600c0780307580d0340750388000380e01c1008111001504403007070714800aa80b1008030b803282021500c03025000701c01d0380d0f11a6507101d821005001c1100d003032504100d1005c207980040c81b0b50402610700a2081405078501030300348000e5070381c034011031106500086800205446580e46c110041d60468024203000c0b580280c0b020201e0f02d40044e064084a081c0d00c005580424084041600c92598013848081c103405440c00000490600036460380600c43c0310300720f01252550740c030de09400400303a242030f9003480030b4480c083d4000c3e201c1081c40c02034813910008010321031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 244585710 1250 244584460 244584469
    0xf0506042604150f02010b0a120b1303020d23120a0e0c01270b0403120f020a0305121504050406021902010513141608070501110318150d020c030901020606 68
    0x4040d02c00c0030741a0740d0f007070300e99000803548030003c000e40c0c0040d5583c071007541c506912a81c1c2c02c0c40c080c00c2d5180c48111000342610704551951070045c28a5800b08402d0b424400195000c0340e03104c0c0c6046070389007001e000710135504001911001026003699428001942c00c0464504a56052003a100008100107210002091a031100c00d1400301500152064a544055440208140c00d00010054204d96110b8840081081da40c0c810742054840340380c0c01d10550851584000340d2100007599102074072281556070b4010300b060141c81000f0404c0840c200014009030603003c2e0904942a00030030510250400303042140003035200180440c00c10220b40307800f00761b981c014001c650003042e04650028450041d0b40707901c421150040e0b41d6141d940103e000f0342a0354001c03410a07034003918141c809030455603d004005031103052001d0503261103400c107100e99200490410420401c01c0815102e00b0780030303140c1e04103504051141880c030b184041c1c404030301001c000c98000050420f480080c2c0881d4130648640d070800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 244586960 1250 244585710 244585717
    0x90510031a190e0a0609060204050f030d020a03030f0b03030a0c0312020c1504020103110a02070f05330c07093219140106081905060303160f05060426 66
    0x2ca0141c028a0b40410a070900e61204950752000740a50359440c6039a540d00e000d41d09204426104c5035000314042c4501c1ca040c01800a40050031401404504080c200c080c1d00c4252010b0003406166845417070160164040d0400c4e581b05000174260b996a010703984001c0c1c07a00f0b0403000b0550001d070b540011440300d062203201b100c8502039104020502e01b8121041040b000c04010412410141c0700d042c0c040c0b9082035080a481317001015005001c801c3c1c01d1128040d2043d90a0f4041c900c030301c4c000b0701e480a98010001e103064806920080360300c42400d0b107208a4500d441160704501080c85a0702c0c1c0080c80a0072a4011442d0403a0381a4041400704040d03010503002448002500440707000e0303000b05980541d1410b5900d0100100c08010440aa0b0300d0022800854240d00400104e012001080040c5040180440c4620051076003045503003400700129982e0700601b203050030542190584441030014400001c4869a800340442d5031614152a041380c000300c201724074060350031656040100d212030710000c0d03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 244588210 1250 244586960 244586971
    0x2210f0405060d090b0f0103030206070e100f090e0903040801051803030c03041a0f0106020d08010e07050d110307020c1309080f0f07051b10020a02100810090510031a 73
    0x24141410304040030003680d68001d4011540955840c3d00c0740d8001501c2241c01440740c1c00c0424441640c0d8590b040203401c0c1003005080c002040700c0b0340c42c240c0595030b07540601c640303d0480b4503041c01007803800d0405031284122604403807203032400700f410003020650010003801900c100c0c1d0024080f5840d485412202c8181c0180300d52015041800040c030b4151989015540c09030242454aa4030f88000c04610100780302910218507034240c032401441b0103a010000042c0e03032000c6181494680d89000000790841c94003903e10130400100041603511090300c1e80000713141c0c990340d0060b207a690800701006540e0f601d841040d02c1c0640414040504504143e10404003081c1c0c2140010345070009220314100258006106000c82c1030003405880f010440411031101e42c052880d081c01d17440c00a0408210404001c42940c0085500c00702c210310068070785e01c618134040612400d000c0d03555103480e1140108024150081c1050525220811642000d1a64100212401070003040b0b8030103055083e440111300d04446 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 244589460 1250 244588210 244588237
    0x1f08060c0d020307050d1503030923010f050904020409090231020a030e01050403031409120d050a020412052b0f0c0206040504150810060621110a0221 66
    0x100940711420303001903910410b40e244c0245011aa82d100008480d124101821401103401051041640150183d009000c00310804913101d4400032a46800c551914415410814400c08c8003091902620684040e510001e00540d111a10303000d00da4010500f5070810307842004d0204101544c050014692141180c91140c104544610001d01601a41c400d074045010142d480e28006456078081c403905004911075070300440d924440d0707d2415007503170029180216903041070f032a02000460700c9003142e03c0f4400c1d044012880ba941d2810b008000e0186034041c644140007011181c0400101082c40481e9a00422117401d40c1010000360704038040c5510100404034481c501c01c4201c0c1e5015401181d8003510043c00d16281c181c840000ca41a200b0300c1404c00b0380d220800384140001f800a11440030240545c02c3d042101c2490040010803c411015114000758100088807c1e007503001e0b00309100c0300a4840e2055510f01314400000e43e81d410001b94808240706031203541241324017101c11604800506035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 244590710 1250 244589460 244589467
    0xb0306010e07170403020f070f0b090123071a090c011d0d12020708100507210906021603020c030a021003150905070207050a080c0604090c02010e061f08060c 69
    0x5801d9002103000781c80201480948051614800d0003044103030701c5184a68040d010307039440428818a07020250300440089a03d00c0d40034004100082c09407003c80c802440e0040280a06080b108106260610b1105420340000344e100b05000c0c810703607407207000c2e82811128519a5600b0303040302d0701c0760425a0340d0350026505405030301510050615001c50210001c00c140c8400c80903598820380040112128005600803c10030000c82005100520014149403c02d11481c606008006c0501c18031400303003518108039a0740345a00d0381d46c0360301035612158004421941d8621031500c842c110210510300310f0041c441e61690400a0401080c10103903540e015081824211902c00103601600d805550401c004c800e0290001d8000094020180a500241c0107070a0f41420107040c00101e4406420010140c1d0050300c0c54409501c50404440440d010644005002031010358200d02401024078a51900e128200a000304260391540200c1e18680c80c418001d00301d966451946d890343c1e4210b90500c6181400d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 244591960 1250 244590710 244590719
    0x204020304020f100305160914041808040e01180e060402011b0b010e0406140c0d02160b0403030506030f0a110d03090312050705010c05091e040b04020408010b0f01030b030601 77
    0x540155400510003000f805003045940040b901c54021a8099000251220305000e401c50b6050031540d9652207a281810310141041d003101e2000180214080c01559140980c0743e41c000c00c0c0c80040001d5a200341036564803581c0d030010340c0306280203001d2603555032401401c1000d152034521807060241c0030000030b442140c0d1142c00545061014100060440194030709140018480c0003140c0d010705038600b4485040d06050a0102c1101c2c0341400b0348160510640a000344d403124a41510040300c20088056614607984424080000b203ca02c01006541001c0c01d00c002c158250700541d01c109001d03011505032a548400d00342e6900314028020b4081e41032000004000d0410b100740c807a1107806400d200b260740d556517079111410703410900c5040000c0d41c04911035040003800e00807250310300054a8454202101e92001543e01c540003101d0401c0b20b0401c1c00b40032056140c076000207400140041007103441d41e90f2035110034040c012000e211440b4000240c800d005075030003403240000310035000d0003d00e11a03080 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 244593210 1250 244591960 244591969
    0x60403080a02040531020909130f0611090f03010204062001020c0607020f0c0f31050903040302090a02130510140f090f150d0c090f03030c0213050f0402 67
    0x107068031031107076020080403901d5201c451103840c2000c02c407581c0040e40c2443d29006049240d0f44403120007564010030015015a85a85905070000c60002001c040b919484c500050300400301800102000e05091003080da180d08030340680b01c44003042d601e0307811020219082508078802d900070100030070310031a842858005403034180000f40032a040010310704417280c1d084500d8400112030b400c0c01a40b141c244840042c0e01408580d9182c06c007900c001c680440c4500010761119580300b03114020b84002e540d0300c101801c0c00d20ba0020400f514900411007428110451501c0303030300c2400242e00545080d0003040c400e14042c800ca452200c542c0c80407410390340c1041d0412401e56042400c3c1c0b420041803450320142d003140d0100402030403d180392600d07905c0350a14207004080151144061007100c02c06102520f50441904440c28030400700030018035a469840207440030407082d0045000c405a813240402055001108010349070f0080f11031a034020003807601c0d00705682080300c1c1c030000799039000c3c0800c0040c1070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 244594460 1250 244593210 244593227
    0x610030b04140601260c0d141302120d02060609090109061a0a06090e070507021207090b0f03030306030d030c091a0a030605060307050a030f021b0a0224030610110a0515010f050102060403 82
    0x43ea400c01140d0100003800940910723009035030305060424810900c00861805000e4840c4e03103234810001c1e08a02c00503002c06900c5034002441c1e40d025400c50800100b4030780084d488a80e0099205008204038220501640c00a041840400d40910901d1601003603680c0104040c0c1c0c201d612110001205030349081c4225965000341d40c08a170001400a0780f010003003000e0041c00040c10116900140710790280c002c00044500342e2010a00a81040003840100c4c7c17800300d030100310b002513802d020a508143d52400c030340c400241d0348902440000c6200c00001c0c2d07a0007000501b070070102e541c0c041c40810786440030005607220544691300414010800d00d00c0e03050090b0004903a0101141d401400c1c50544c1c1200580f8186890090b581c03030700320410301e604501e40898603108402502401c1c402d02c45665000c0001488050b2005102e030761032000400d040c903c0b6114880200d0201c2055402c0d5404038a05503a80342c9a035000c07d1150350000c40045500c822803401e450440300144d005005039152038a06072400d01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 244595710 1250 244594460 244594477
    0x9010207030b0112051603050d0e0a0b0a0c0605011a04090f020d0603060c1e0e0d02040603170309150c030408030a06050a180617060610030b04140601260c 68
    0x40c003100201081e80340031010300810504030084000f04207807405d6402e0000105e10195000404070b0140b000c00c4002480c0500c1071940d0500011500310000024481e46d031651200540c418009a8038140c668002c0f0781045092040307905201590700c40d07402e0207418201009491709458244001c00805203160801145184492401031800c5e0f0b2000b007800c192421a0029105180c413113841248080c1d100c00840340e6001034035002d4005699030880200000035031840c1d50300c1905131102e840203558503640201d004561000c5014080c200c3c0304e030a010250400c40300890140100c981080c0280c1603c0c900d603100380817011040d451036a55a0b030b05042900054448040c0325601c40010031706484075410710014141540b03150400c0704042076031405840d207640001c00b070702071101c0d42403140301030015101e90030034021906d40041041c0e2800c100d0050484034241e0794001d06102c2c4084450480e4030519018410a0361500801c0300d401c0d1840700b80c1c41d1040100c051200110b0000b0300b1030500d0001070120b49 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 244596960 1250 244595710 244595713
    0x30e010e030f071a011202090f06010f0509280305120304020d0602030406090b073c0311130b130501050304120807050f131403070f03020103090f150b01020607031808090102 76
    0x7549560b0004d0070f4508240c00825100d98290b4012055242c24954213074043c00701082080340c1d00c0c1410000781001c0c0801303051000d00802180462042d529002408072000852307000c44041c07042c16180002c48c02c0b007840261050b00070903650520031903c0204481c41203030040c00e03020046442e540c0700002540024004d50320340d13650f801030781c00061520748031034000c848665940821b80102c0700e80184e0100301000b03500d1a50200301d1020031030b52020340030101e480702c41c5c1000150084202c84660103485021a410441d45400c4d80100d400100c00001d4001d001c0b0010307403042c805072220010f43d035520040c2c402911030b4404031216410140304512495000e25a4a40390b070a2044400c02035051740c002071494411680300ea803040c04402c088081130704054000b2001000d030a850141d03034051000c1c0d0b13808040e0416445441c80e13011300040718142c69082d6482030000e86001d81711079140004281400f42c00340107001c1c0801080b0100e100f40207002d6100e182c0c2e003a1880900c040e03620391010360701180c1514151b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 244598210 1250 244596960 244596983
    0x90d060903030b12012a05090603040804060e0402030c22080f0a050c0315150406051806040b0103020c0705300a030f0201090309050f0a0504020f0a030e010e030f07 72
    0x940940190003403244652404603603c411401004601040003620104ca03030314260059842d5811049a603503498160a08410301101c002070403280b5219568001d134119200006200c108044070000f03108a13500c0e541d030849509a000300b0807050b44416101c10244640601150342c4d43e4900c1881000c04555250040341181c2c1d030f9060403030038800c8800c0720030302c290410710b10001482424024030b2201e0f00c04401402031200544202c64050f000580380414000c01640c03d170201e0b07151756001d20042e00780200072021000c1d40320102c80c2c002d5403c40d04603015500700781d49551036500a009440c02c4503102c0300501109405c0c5001e1200c0a050401c040c04d000e01c1c459005944204040d0701690248482405041c00b030100d030501501c800848181f8004680c07602c0c3c83e900c0800d600c00d000c0d4090300e0007100c160011020700c100045144260f6000701c5d1340035100044c1d107680c00c211070008102000050300d042c00500301e000101c0c1d08a40307200c241c42025400c01c00039800c40030000c3e8001c2c030380544a900c1002c1c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 244599460 1250 244598210 244598213
    0x5100810020315010e01090f090b1203030714220906150206010803090103020f0d05040b0106110a0503030610020f070603020921030702011b050d030f0b040b0a0e09030408120d18030503010b090d 85
    0x10232280c1a40501010b594840080c840e03414030700e440d0702e401000381c0025495400c0481c0c0c010300c0b9095408a28400820100d202e10580c1100720220592020002e1490542038454021800034503031441500144818540c150b0022030000c11b049040750b1b0b500001c0c50030302440b000150081c0d44144510341e1040d40030400341da092146489014055806102c80304000c0d130404c44050449180f60408500550062844038001000003084941c0010151b4103c2d4030f00b4822017003a880e0a500c0c50303044a860158000c0800d031030382d240d4050041c00800321260005010f5400c4400810005821400c415401c1000404003650089070046a4100c04120001c411f28142e1145401c040c804011100001d07120810554500454001d010b80400c003203e007041003100e40700010b170341004244502c405500d026400511584824000c1d2802094010142c0d06070b41c0c241700078000c840e84400d42c41141d00d40792087d204880102e030f0040a500590544072181785074240341158100380c00031241d40c2d50100c4014140310 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 244600710 1250 244599460 244599479
    0x1032c071701060f0608010b1c0207050307050115050109050306010311030a0c06030f0c05030f0412110a06050f010f150c0602130b0d0516020a02150d05100810020315010e0109 77
    0x1e40c8015000000103481e410b102d000c41400c43c15520200c00c019407040107100c4a00c001084840d0b11151903113008895010901c08030281c028003c000d00140400302c0d025044c0a4190000980c2240c903400300440c0c16210340041d9942d250134000c55815620440050000513144000c050708040f009040b103050034580d40e1000c0000c0c407140c02c8140002d460305030201042e02507010f4000000075070b081150030342c50512034071541c402004101410001542d000600340900945200051396002000e42d140ca402070304002020b04820b0700d031540c083c10300900018000b2101c050340c5098546981d12302c451408612401c81e803c911425055525035400c01080e4546082004800020045032210a80b03800701001d42c141103d5000702021000100d070200080071030f45c0450307005801035044441c9a240004000c002d03010f40108a50444a11b240100b031040f25070200b21014111810841183c81d0a0340030010034043e400183d4071405d01011002d01d002c00e030341c000d807510900301d0b1040c5442c0c0303102503588001e0f5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 244601960 1250 244600710 244600739
    0xc0d111203041406010e070c0b06150c030702010215090703120e1e01020c0d080a05180d030e130b0f0d0f2001030614060405190e011d010501032c07 65
    0x1155510305078503103549603800904c181401000709050018203842c10500c0541540044440241616420340005100d503a9501645280c00002900a5207a04004440c55541e0388408810780c003500c1400010607200c14001951403042241001800b01e240c0ba41d0703600318010340980c1c00380b0b040c005403a140e07007c26100e2060f5070790b804801c5074034001c0c040d180d0000a03041240304e40c1040d0091118941d244013054000e42240c405202a2a24170307030300c2a41402110f203204526420719400000b2006802c145071b171041c45594918130446101118040e0050604111908001c40c142c003d105003050100524020510003100f50188169078503040d00365a816500460140f540303010394040b04e00d40d1400b5649072045e400940700c451000141c80908100145d154000c40c0309180c4203100b400004040e40f00c01908003402402d0703070460465156180c94401e00881c6c0c0040604010a4850f0000607803907100e4000c0385020020344614001c802948080403696001d003e62000c054428850009485400840c84 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 244603210 1250 244601960 244601963
    0xb030f100501060e03030304030804031b0501020706050a0501050a030b27152d011707030803040303050109050a020403261b07080706090e0a0b03070518060a09020c0d11120304 77
    0x40710b6040400142a21201121150082e4003e0081000091700501500d40054043c1007250f44295031101121058003080d500600070350001c1041e1003000325070b400580c051110b61006002c0f90b0703203070700c10300c100585039120150601c2c0000001c10890b90700c2e41448910729004540b500141032000728140d243c041150f684180d051800402c0201042d00072241030400601d10903888100c289142c04a000b0004c18020740441849030f003031400da04901003002ca002198031283c6540c60746003509002e80105400d1003455019401c1100045a040c05442109c059070307802035000700070141c1d110b441040a40148844155400108011014400611010540c0f0610080140384050500341c255044c5082e60b071000b800e103c289002482880484081ca40c4d00c030101581c0046c40e01c4100001030300e03014542e0f200c0e50308102d60b201f41c1070000110b910528803440d030548085214541d5400880308920907141d0f90f030329541001c03004507112441001004070640c4210112011510035a00c5000300740d009990 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 244604316 1106 244603210 244603243
    0x50702040e030c06090601090b0402040e0a0515130e010e0c0a0b0a03110307030f0e06040201050a0c0501110f031e09120706020c01240b04030c090b030f 67
    0xd884450120008a0f40304e0b09041114948420b030a0007482d40b590f0506450310101d007054000c49040b034201c00281e590565406091000424003d0142c01c2160039014220503595030300c040c50000c00450440010f880c0580c41041400c440001c080100c441e040300002010940e40e0b88400781c11501035101d07050307445219410850080030188221200c0d220b0100900c44500c2c1d040e130200124103002c0c80c0401c580c8104501859030b078032040b50001d00080c01081111900ba110340140b41d603091254002044810410b100141c0a030040ca0034220080c0700032081101e50311041c01044849036030f8031001140c40c00d10f48c0a59489144032458040d130200002080f1007006141da045504540490000300040e40c03c18850415503007080d20103548460480d100800d110810038102d07030403254003151095084c0d140c01091400742034000400c6078540210400310b01c0d03110381423103100d108504041 = true := by decide +kernel

theorem cover : BRFrame.Cov 244424460 244604316 := by
  have h0 := BRFrame.cov_init 244424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 244424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 244424460 ≤ n) (h2 : n < 244604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
