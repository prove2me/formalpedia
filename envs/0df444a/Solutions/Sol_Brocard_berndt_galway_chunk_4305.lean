-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4305
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:10:59.525983+00:00
-- url     : https://prove2.me/submissions/42f53341-336f-4fa6-bd37-04fd9bb1b798

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 774100719 ≤ n < 774280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 774101969 1250 774100719 774100727
    0x10905090c0a3c1d0c19080903090d081905070b040f0206042705091504060507030216050d170403210615032007020603060f03070302090f07030606 65
    0xb4007407400441d40b01c420000c04004a800c4065030309800b1400750f812070541852114100c0100d42060782d85045840100c2c5850051600413078002e0b08400d450351403c041440640b489411410460003070200c0f00000482006c024015a0114000a0845244902c05103400711180d401340302c4240c40009800492580c803803240003520010381c2e1280c6903107000d4860f510344c0c070349a000c030141c100d0b40144104004101e031204038400100b03e01c0c0ba681e1b03c16020403521044425202d00418441d072642c49800500c0013035000c5c00181f50003a800038030000b85612440c0d0b0842c068442c01401107600000040514100a40001d010070340403140e03544d0f0303600340c980f0001200100d030b410349019002071b60040340c5000c01000380c1030409021003101c80009000e59681c0f081c0143d95510b42140020965030080000d000d40300f03519041e507039401070240602d8000c01d903000401c0381c00050501c40c003414015410030ba40c0d031001c000303200c0070b1500280810380900d40b840d0709041d40c100403207140b00001c1c200b0a00041103400303 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 774103219 1250 774101969 774101989
    0x1805010e040f020702060a030614091303080a0609021308060717041103150703091103010203100909020f180711030f040b0a0306050a14011805030601120f0b010905090c 74
    0x416903941030341054510400001d007802c0d80400d01c44580c03c006000050313480c0ca00502e07440c589501c011800d01e1910700e103071085000d10056280150000810002035004d0994070300d241c1c2c2d515040c201c0607a1101f04006008040d99002485468030010300c0c07441d0002d9852020702161146421a595941c88a10803501c50724645140084100b0000216002400a0006426407400a0704907100540704250501002c5010360b83c42c0c2c0881c0d42c422440301804155541d50042400642c025071541c1082e00201d1114843c2e440303071a80302a0388120701004c6580c1d00156040c03441c0003c0018122298411a80194410680b0b52401048001844020a01d400710940d8001c40b901c0207001c5c1844e150101c03000056010301d40080c105560b0780c0e4081070740e58400008402400001d400c504007042c0703040c00135040800d18500c0d9100b114082c4400c1015580c00076107941526442c09000462041034503151042d09450300e0000d100b100c2803030001c1444080c0794002481580198101c4405851203414002c2e0004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 774104469 1250 774103219 774103229
    0x110d0204032a18020708120108010c020f030a0f020c0d11030f010902010801030b04060e1515121c090e070503100501080f040615050622050109060f0c080c0f0d18 71
    0x10b1400010031410440305490a4a115866400340ca06862070f90303074000507404945603443e413103504001071220b004240b08000381400380303000078888002d0014085599010b204950f800700321724400d444001300e20070f010420341031401605a0502c1041440e010b607a9940c40d02500703009104200e194500d880050280c40c07032490301130310741401c00d90941e1102801d0701c1c3c0052041d0365071505e42d12082208542042055401308440b12040c0e0b81c1c0c02c0c0480784002011a110030603114407800041da800042d00414907901c0c1c0c48a08003c081d000f6018042500c520407954000c0750641400c0341013007000f0b90000010f6204001c02c1816481e5a515940155180f000c1910305040c4040401c00107400905c1d1603202200e051012203d00d14881e5441001032400d81c017902c0e24105d40a00516182e1301e2003075010075403015110900700350560b5828080010050240610070000300400c01c1030f4041400604000c55810b000381000b42c0d51403032001e01d00150740d0003446410f00c000500c0001c008034542250028842035079 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 774105719 1250 774104469 774104543
    0x60c07052e0203220c06020601140a0b03062206060f2f0c0a060c06051305030a0c2910081b1306150914150a030e01110d020403 56
    0x540103400708000c0d08010013491690700b1410580c1031000070402116082c5110380c83d140c0065041404c001c3c00c041d8181e00a2901000401075032030695950001c0106640805819a44035034510001071000c2103109903401c070b0f07904a140f40030201d000c0e03904000f05403006a218078503010700c4800c0490b071580010844121210034840007600c110b007a06182e1407030303642c440202c855042c000000070306801c4881c0c2c0114045070000380243c08019041c0102c40e40325100109070140c0032919220319459100d40c40d1402c082180540c5071400b0024086040506e100d011046100f010108004501d011401543c203540b1001c1da004000460f40c0c400103400002c4012516900c44110410b400c9c000740729040c0117200c0e106502e607400860400d8500044003440340e20b607501c940b80f0f2843d103c034684181d00450801c9000c0c520759141848801c0d8080c0c00c40302400e09616000170303181c07038415003a0f005200701912010458000503000311144856006082940d001720212101c9040d07800703008506103843c542c000441 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 774106969 1250 774105719 774105793
    0x3061c0507410d0b07050a02070b190c170a090503190c0b07080d02030901091515030b040f0c080607020114090a12050d180c050105090123040503060c0705 68
    0x10b0481c050381034407090b01400030b0781c01c2c07036503a5107045000390b045401c0740004502044659540d03604225860040c00040011440e1056074034004560070749128142040c40b190548510400a10300e0b40e00c0c521040c40b8920545038841010b009001c4040e0344a964464440c110ba901581040d00a6400d070242d408500240018030304142c0000c81c2d00304080a03170740f1860600410000c035400c1c0c00114882c282c5440000b810403618a0101d81d118a400d045a41c290324204000d00d141e050401890305aa4124050020a035134501d4480841f80d41d0080c01400002d541500181d00300000034580d0040180b0b8000b800742c20366805101068940403151304005030300810052000c28580b8000240d0b081c2c0c20301c1c010b0b01d402d1091036140b068828644000ba40940003000e44014004580001000b5000c2407818602c0c20400c00002090800080c06044680c00c1b0340000454010700c65007118010000501540c00c0b82c540103d40019607017204c030050f2214001d42c095041044410b44044280d100064103001301 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 774108219 1250 774106969 774107069
    0x29030c010f0e031005010302090705120105060d1b0f0311180909190f05010f0203010b03160e13060906050108040b191427030309030d0203061c0507 65
    0x1006124148102407100e98080d0b40e149407010b001c14a0782d120700d680080b444e549180b0510651803001059030003084000e11140308a482c200c09858110380f400c40d00640c940b10b24100e10030081c80340704042400d1500c5032801c0113502c4e8000c84031040c0c0c8245500e0420100c0c8408080d544035101d03803071100101d64203200c0d1030010340c03030308050954029031004100c40b0111401c107412055214190300984021000200d4001081004d00507100c40b013540e1902582103500d411038594250002506030004881c07141d000c46000fa1182d4004a80d0060003460760b051424103007098001845180650f11006040081c007280550240c1c10503400350b94021125400313903032110f5041c5d41d81192184482040e40d22103542c8400400d84c0308c0528080c0c0a601404490540d082054661045c03c0341d5081e421034100b0b10411003c1c101c048250340c13a140d001e0001503030b265588400a20f4a41c191503101c00c442c0034004102082c42000284402034540c40c915200c2c008444455001c07141441c0020209900021400c41e11 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 774109469 1250 774108219 774108227
    0x6190501020a061a04022d07020904020d0512041401090801090f14010e1c02240105190807081510140418060c0e04061703030403051c020d29030c01 65
    0xc00c0d54440c1c2c2e580d16940c00c0e41c0c00085d0076640810352521010506c000b061441425001d9542226060f40503664900352141c3c3c08a0804100104068446c14103220950140503061000042c000407080d00300d41d603030b5101c152400802219981140c00a180f03001c01260b1a03805100b0603900c50340040040b017006107540c0c4d490f03e1a06074145220303031035500e0b0041c5c02c00740b03070301045401054035050074421010020040020704e0200d08102d9101c203c248e203a40c0709003020850300140c0c15180255002403c414100d00b031540f0a4540307070b000e0401445900000101d054002c0341010b5010030310a000b079840e8481d124079024030710041c000c501240c2010804202d41e4a0305501c402d55170442d41118001621040d1964401c13600d040d0100b4010644561000340e07185042e10900000d85402c40b04101500301e242c1d1080c0c0da03400000c00c01010b2010010b80100909400c614070111844204030030766446608148980141c00d5180c0c040d00d10f002590000c20709040011823994100501800400c214018100116 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 774110719 1250 774109469 774109481
    0xf090315020903120301032405060109150302041a0304120206070203093601030623130303092a050a05010f0f031e090b0109050c0a0305280506190501020a06 69
    0xd90b00d8803800800313040361a00200603500850196840640c12010190003459030821020241112461300080100607030f00814080195900d41325145491088414250000d10403500300c150308407003d1095802181400c00214840c500c11800d803190388409201c00d0340d0f2588140c1d0f601001d03800601c10310348141045280000d1080700440303041d0a13514048010010210511191500304a0b148010320511440b4051001140380a8144984c680039900d40d0310007409000c3e2030604514035184040090500c42d400c00d441094124a8540c466591501c16070320030050030f071120f0303d03d80d601c5100144510308074826804684c41038482d20101051a00c04450140ca0240c0400915a17103070103008586200902c04005070040420000783c0766000d0070002c00115050344039029080c108000c11261001010a684104034213003004105e9031540d000000c1c440680050907040c21014140c1099440b2554000502031741060f54190341440f4000c24540004010b800744a0150b03000c02c03c0040001c40d0340d4806 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 774111969 1250 774110719 774110737
    0x40f14030109150c110d020a1407050303030711070509010e040f050f1b090c13030b191103042307140d02120c10080f06060a0302070506160f09031502 66
    0x1038545140d40d5010850190246032190040d0303152100c0309001d4002e05da003003a80c0b144600902c1003103c4031a009580d68201d040040c0720f451520407105c03c11900b0441c1c10003410f001000e680d16071030000001080c48024000d01c01c1144154034000990382001c0b501341d4142d480f6030030100c00507038039502c41203080720140c101200c05101b0342c400007080d000b05014046d541020201c5019055940004001a440000e84a940113440c20022601c500000c840a1422a580100050001e070307140c00c1182d04100705420308184031414010f84800014151004510a901c20305c6a9008611813400001c580e40e020110700e00582d01110301401a8050303409080f0010750b00174080030340e41041e940802c0600d5007186104502c0d0348280c520100c186820020f4240c2840185401106403600320024906514098412801f603040019042c850300d220760116220181c00004661035814800515244584040818400140b04c00940c02e051403084000404498004840c2c29554680100c804000d501c40d62103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 774113219 1250 774111969 774111971
    0x1517030d140709092c0f03070c051005120609092b0806090408070b0406020423040612050c09130b0903030105090a0b01020d1206050d0b090f03040f140301 68
    0x44002820780601880d0001558100620b03060526014007591a690000e5841900b0007074840790030960460f1800c280042d4054100c04540022126420514010f442d105c41e404001100d1040c000d01c01d100000301c0380103850700003500341070081c00c8030350340685182c5810220300725010503940d181c6600c8540d0452004420b8508481c0741900400b403071a071a481407040340304020305030601980c016540903800b00d02910700e02c500e4901940c88880c3c40c400e96400800d07a0150401040500c0241d5042e6405400d105500b5094200490039503a41c5404102600f4400d43c00d02e500450030030620700c07a07095441d0b80080108035001d844010407481a03401489a42c09500348042180803521070340b04035028030300c2c14003c3c2d60740354108020301c4141e070b40042040c0022030034000f0300e10184c1d0380003800e1b02c4200201c0c5000f4108200403030710701000e4407156204540c003660b4161603034140031035407241038000d03800c4c00202c811003000c10300300341c1d01c034040c1c0d2083c504040c0742c50f0801c10061010400b0714402d280c0040c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 774114469 1250 774113219 774113227
    0x9060f0d111806040501051804060c090b1602101d060705030702090c0d0b1923040f0e2526010501060f08091501180b06030127151703 59
    0x116151850b90400036a28081d82c00c10721040f030a0601c94540945403d070798040310b00480703207000400700748060401058503990745103010840c1c2c450008100030f000754020035903548861140820702101c07000c0c01a0b110f046826041c0748910f00810380c5c01680d8a000c0800c1c041c2c8120001000300ba6004903400303030b82d140001c1080d0350050751000758284c0b01d41c0b50807000310b07142c1c801100b20030201c50380380c1c05075401400d0340c03920f1560f0040c000100c00102c510b13403207450950886001d00c004c0e140703441000346a00103007083c2a0702d811803215081000501c0ca1217040307a20800390b80780044481c03a08202c00104c1c070034541d60280140515000411016002a40348540031045a40c0007402c403802640040d0008845208030350425510084158110f070101c4000c080d103100440000c03104407818820301c86540f40740006805282407907003040c40b00c010000c004c10784a681d60000000030b03820000e401401240d1002400d030301c1103020302c00c41c501e81c2845200303404901e080000041d151070f0004a0178200c1d12045c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 774115719 1250 774114469 774114503
    0xb031207030306181107060203131401050106022b0e010c140304230f0f01020a060f06050411070308011e09021602030105060102190f030507050d0201150509060f0d 72
    0x80003480054031070b030341c00140715141040311803000c6003c2c01021501ca0401c84014010107802080c0c82d041d0f6000a00180d80e0f8407031b045040040c440501f401860413284c07070700e00e803482c0c2e5065000c1070480310582c0030340e04800c80d64486040b00c90318000d0400008645d01d440403500d64492241c8228813907060428403a5210b1035103600c01c400707004094145550f0b2000606102c00a01c81c1820303551103c6911a403e40d192003400041c0500e40344007403580c0183c00300e42e080c0400707170b10800100e0062600080100b0500d020b130300c282409460035010f42400703070b400e040b950302c1c2c00c103c0c80d403c44401c95016501c0b002c240e400c0140941022006a001c0c46203001c0200700401c2c007540b50b1004201040b901d4444040030b01092060609403040200070070305640010560241c1401e0004131003407010752000204844400c980b900307540ca8003512001a09910460085030103981e01540714140b000c680442140115603140100305040004542c06600040d00444288603420048600c0c0030607480780550100210041d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 774116969 1250 774115719 774115753
    0x180b0f130324090206070b09030f121806011a03060402040f1401030501170703030e150705060405070f0303121a040e070509130b06190e01030c0e070e01120b03 70
    0x25041550300c00090707107041c100d03001c6403010496001d182c28002d10440216070000741e1356010b01701002c2c043c2011607000074610030080c0b04559203003000e56a150740369624103004080010301114641204080811540d03404140041d00604840c070b144000c03112401242e2001402c4c3d0000b03444590016002e00000c2807040c001d126480291094103090029036203030f82c00050503903034103034011941510380005500040c00085004026203400d414011b08507001d140118a0038182032030700076580d407030205114041080108210740514020340460785269251207001041c0210b9101c01004211000b41003012400c1d103030004484008002c05121a080c0e0800c0401d040d1207807000103403000e03042250240014600828616041034010400c4400042e0b2a55260202c90b000362145100d0000c01c0b1032500300e131508260020140545540c8178110756980c1c03400d400c40b11180d000c1d43c2c00012400d40010095840340c00366a2001d00140d54003d19020040f940c100280751001034a0b402d8003409000c1c807203400c80 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 774118219 1250 774116969 774117007
    0x19060e04030c030f0e0f04020705150f0103032607030c0e130519020f0d09080d0612110f03070636050301141603050a021c0f0c180b0f 59
    0x82c0c540051400e01c91070001e0140401e03206440074040b41c8041043c05485480c0340000300704065600594807211802c207a444e1805c103419919001c030241c805c00c101500015400b5040743d100c0c0c1c4480059066012510000c041102214032000107842c0c0042d1100c0c0c400e4101e10780103205403c294402003c60f5011550000c0181c14500c02591a002030240c40554043c0c1e00c6000340d4000070440c10f000304144001d025110340104000d0b0503845e84822018030a0001c01c4079034000d070130b60b010800940e5828840b0140d113985442940d080686004a1005083c038054400038004010040c00080e0708107401920f240d06513040c1070407080c2e842486c01d030105007510021560466406040481a49041c04040c01e44031141d042d006180302c00070500541d41e00c0003d14140782c0c40707542008240c40e522103858800034094400c0120388080c031002a003403d0031840c1e100d942d40304802c0c2c0007070003440c50070301040d078a456504501d440900f0502104000d44007103a000341c42010102d03520039113481c0c881c40c030458403281 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 774119469 1250 774118219 774118223
    0x801120b15040e2b0507080f0f210a0605030c0405270708070611060a0e03070c0e0613050601170408130e10080714010c1a0a1a040b0919060e04 63
    0x8000c512050144180b40c01407000c0c0c0200d211318030500c80d20664010306038020401c0050622034007080c8142c076070800c201901c2008048505181c0c58050b032140d02d42c0341d0400e4206034a411030145000c40c100840700d00401e42a120064002c01881c4444d105200040070000d140c86004243c0000c6002c8844a1030444010f4121030001890030a0806940508010031580140240030b001c840d0180d00c030a0100300964050002e102c002071103000c41c2c0515003544640307180140400043c41c00883c0700f0240800030740c041c00007a200114480000020001207450968186001c01c030300d046a02d0301400c03948000f50b40b052281015a062442002d03905a08002d02c1d0084d20004070624208940c4400a04450b001490014000d19481c0c0ca03007108a80c520030010390050400600d100300c4410300146102c9600d100071203a40425079840d08260780c00c014108519040c04101c4015072034200da1515003e5040700000c02001140c042d151b28246600030324205040f10b2080741c840000203590036006112f90301c614 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 774120719 1250 774119469 774119473
    0x60b0c011d010e15040f0209010e010e060312160206040513061e030c030809180106031a2407140105160806030d08040201052a0102090a060801120b15040e 68
    0x107902080c0520704021005200000340c0e00d0b0031034600c62040001400390540312549189640364455007852404400502c0c006900403000c1000000c03d030801c050128101d52844007000507948a510802d9110b4041c503101c9079100c0f2042c0810003001d001c1c00c0f0303004001c0c0d100400c558903181d0368001080d2980d40140e00e15070280c3d40c41d401000601c02e9a04d1107200f44078290188440c0710704540c2d44040100c06400003514030200442c98144030303241d00110140c014480ba01e85401d03980d41c4e0034000c01410003070b0021000c0c3c2c6200e0044413058100610742c9101d0030074100030a048100512608003d90f0803107003080d18141120800211242001c0c807a081c024119281f01044100e010710f4013410030200506050b0080d881240307062103041c2e1106506422070341c2442c0581d0380f401c540000ca0000303014040407480d0103040b8803d428514105500411540b0020b86021a0140d569901512a41e109200d043da1280560003200c001a039580c181c80da20081c907041d0170a402045001190860300f900b00401203503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 774121969 1250 774120719 774120731
    0x2070906120302121c02090409060905060601020c010c0b06100207051e0f0a0e04021210111231020d08040b130819060e12070c030311070b0403080706060b0c01 70
    0x4507030f040c42030800e01142d600e0340d285040031030003c2c030038100c003c03c00a501d03156000c07071405003c0c0c0e42c0e0740141c80301503004541403001002904005840c1c540941d001c50161160a010681c1540544011603500e500003d144415540300014071000000b0701c0102d400318001c0e20740c04201030f5203059040140c450141410300902011505026004200f181050b104007040d036010008454410b10729076200364155a240c1784202420b00107498106500c4907109400d050062814050102d03e000c1c0c95454102107807001300c0c0c1c50300d00c0701c10b4100e4540d104040d11003002c0011144074840c4489400b4291b1b00c0900355011b007034038a4444e0000740d00207812aa00882002921010383c3c21400c183c05e01034030f810f2000c2c1c07103c041715030400c0900041d551402004c1940f140c17109203030480140250300e0300781500e00140342e0340c03d52460042285841808220301250b5941f0700d075030740c0c100c00251002c00c2e00c541e03401980c07510781545c45c1e140c0d07180c010744800c4400b02c1d250040841ca0403860800f400220302448004949 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 774123219 1250 774121969 774121973
    0x30705070f0f0f090c0e0a2702070308131502040b07050c0f03030d1107060504030f12090c0515091002010b040f02070b060616051b041d0a120207090612 67
    0x3105101e58080441c08034a00c2c0140203180761005400125648a10001404a0854000d9400342e50700051036502030000000040c00308035800307011194030854001c6420b0320021003004400c9024081000e00012003142c00520813599005d100c841031805080046903d100604211046e82c1c06600004124000400d203c820040d00b08107400340c9008c04c54209a0301103812002c223540340070304c0c1e00c19580c5907101c0d0310700c0c03460020a008030782071950041400d200702c0c5454100034018901d0803405c6000540c0c500308904100e4260f100304059203038089203c0489078a010108003284000289102d00b0050411082c02190b49036035100a070802d140c0c0000c5540c4143da805c000448040f0407003032500500402558001852507400c1c183c2c4024202e43c8140c4450748070400c030b041c03100b50040090251040a82c000000700c00a070f01e07410f00c400300f20b506000750200c2448030010f1114640034910140e00442d0824005400f070ba040d140000746d5032040328032a0782d54270b941078103646441e4040305510b0500809081 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 774124469 1250 774123219 774123239
    0x50a02010917150601030e0106080c12160605032211040f0b01020c060f0405060d02030a11070f0209061f09080d2118060515040515010f2003070507 65
    0x146003901842c2e180c5140a003020b034072145100014044080039034002038450780030780d001d40004040b01e402004600c0e121103a5503518020000400e00ca800c0c004840303010020001400040c1c8001002030000d40d515040b002e40f265000580480c4220036442540c052010030008502d10345401150b21103080303940308081c8811070303403810300281c8414140b0000c0002070341c000501d60990041900d80380d42e01c0150340f0b1203d10342d000b1030300201c0c0d00c03000000c1e102d00e01c504c6c2a009503005100501c000c2000c0103513400300c0007240c42800c4c0d000b000452000d4070140545400401c140c0d00c60800341801003038891f900d5404111101a0b0300400104010f2081440100410800200501a141485d42e100d5048039100d4210482c95403902086c3c0340c0b20303805440c0c120300c248205101b8a90001d8203002c41d052440c1010b0080341005d86103402681307000c001481110b0031011043c3c500b001a180c1a80a418058040700c54a26900315803802048180648201c0e00040005121050040016018150511207800e03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 774125719 1250 774124469 774124487
    0xe010c08070207060f08060a08010219022422050106061d040c0e090a3b12030a0c050f0d0b0108010e061e030a060e0607030605011d1c060504050a0201 66
    0x8119400510f05202c02500f01048246040709420803492950754940040c1c4400010380214003594000718040c480600e064541410040664098441c09000e148019008450501c0702c1c103c2c0c0303910b0b04003107420700129075943c864a07100741c0c100c08484140c5403115820742d445680140005039114600c0d1004491a10f52520320060071107042c000030784150f000621000c150380b1050302c03494150011440034030041d4007021084003c981c4410441c2003400c14407001c42c4043c81041c2d80700e0240c89440032281c002140d001d4801a0014006040d9241e0f40c0594005180380c008860520100f00100e13520800440042d103440600c405c00031454181603800100300b0300041e80201d40300b0f240c00b8140141c43c1d8901000d801c5d45074041000741c94030840e200000345484038070100504003600d0b00104005801c0c02051251196546072002d01c0032542e680d004640c41001403c09104400d11514404900c0c60f040c243c88122912402c4915000403a948440003150310960303044400303512000840c0c0440d40c100b4140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 774126969 1250 774125719 774125731
    0x90f0a03030f17012d08160504061e0306020a020a021503041a0f04081812060907081212060121020301080601060305090d0c080c0102130806100312051602040e010c08 73
    0x45a540b43c40315002440700d20101421108244440301c211205204905c003006100e24000c075204080f4000d031f1540c08203400d001d40c5c1d0003903060401c040740540e00002800001048030b2045a02141b07161900c40081d0049009a021030017602046409a6542c103120406107080d100c845030307241003900d014003604e07043e0032010420803440b104020f000220200074590042e0072031100350741c40800d940341c10202507407643c00e1944401d0010407103615040c00a030151203040100102c608007519545001e541e010015204c9040003810402110001c801c40e100d180c0094060600c046200403000c000b8101d18102c00c1c0c049405980440104030b902020800140100043c0c04d040190303081c48000d950300d0303840c001400c006102102c080a0b00b00900307e000c82d810a0941c600854a41c030716249642d10a40a52040950612a44d40440d80f94a4000410411203a0101c22031003030a0f07583c1c4040e505a0450002c226590302e82d040420003580720750050b0300780c4403501c8000168500c14140090015003014200c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 774128219 1250 774126969 774127007
    0xd021c030603120e1503070305090607030e0709020f0c01060b0d05010609060507083612030a020d0f0201060306020d051906030c140411070b01060801060206040314090f0a03030f 78
    0xc10004181c1e00c540c503e1960000386000644035542e034010812800ca0301201044d140c3d400002c2041c0300d03515a000c00d0144865005442158895210841c2030f15012802160241c04c00b000411801c15558020012200082401801e00ca4040c00440c01c50b041c6038402000044001440e401d456698450a8090030040c185400700701e0030424001c01c580201d42e0000c0036010300042c00400245540402260501c2e80918900c402c3c112101003000d1001c0f420141c1e011710380740c2d41c100140d90380c04803d540c5102c24940c0102141030000750100d0f40f00614020700310541d580c884c40400800c2c0310b4001009264180074010409003410078441202d41031110010704031500d468030500002e010a60100110b52403e000d02d035040c0081c400040c003c000383d14582841c040001240c03004c203c110b101d503504a900644a1b42002c0e130740c600d82a6195042101d008000800b9080300030500780a0001405101c0409003519600d400d2110118040740b41d19081600820a000c41502c0c031250711560080031000c036881 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 774129469 1250 774128219 774128231
    0x30c06070306290d050a021306024e030709051c021302161b08061909140303090615040e0a0204180b1501170f0610030e0d021c03 57
    0x683c41d2a802003540d071140c0b4100c082c07020700c1c01110000342a2158502c045500304010705010796084020b500400c0b0880c0c190300d40c014006032003400400d030344002c00c100562400083d41e41031000d2450722400b0a1000d0b80005040c0010303c1c8071484101024201c0c0d00c865110b0350b80c2480880984016090b5010301c1c0f00307105c0207515144040c10b115040402c1d6a051310441d500310342c02859400a0f014804214181c1c000c821952402d120000d1a5102000c21143c1d81800d05901c031068030741c40c1c1d00f048400b406524440c200e0214038503195031040e082e07039010f100165050030a0802a500f90b0f07105403081700041e030250050040101c0c00c58a4400c1c1400200d8003000300c410201e01868451840d640302912035980c0c1c60070307464104c0c403804a50318000d502840450251501910030411816555242c500083c8a030600704000481d10b5403541c0074040c140310300300e0541d07070301c0b4100940c0c0010b00c002c01c2e041544a02c143c4001c2c1070100169902c00c5aa50080c2106091440140844200424103134080605100d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 774130719 1250 774129469 774129479
    0x3010522061109060c030702040b0d08070f0503040b070b070e1c060209060702040e0a032604080313060f0b13020403230f07091406030c060409020a0c0501050702030c06070306 77
    0x55200e09030030354000c00200d00050a00c0c0c038840c1c24010160080d412200003c0e2001400034040020b015440c403c45081141e18504018060115504a00200f491404000d4040440c107815103500200e40705a046a140c00d0b2030740200e5400744c0100104880d400d80b21014000a26080036801d0300022043e01c140c01b0400c200c0d00e003100c1c181d2007204040c10312030f40001c1143c041e84a120480d4410f81d00a00140040d1480c600d0cc2952509485415000103024403850f4010042c02004402c0c1d0240131507100910b13494a44072000258000707090380c07100b140b01718403400c0003841c00e0140c0503c41b804d100000406251000030704c8000107124108400e8035204000610001d41d85510000707007080203202140c04000701d001e11354981807464803000034034401c526000804042c141c005456031480003860023495110142131683e03070705604800b01d50010040c0424009008140d000d010b900015181c103051503e0f140d10749608656003503072141c005800c00540e00741409410041240c0007100751504001c018544 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 774131969 1250 774130719 774130771
    0xc020604110d030306050312040609060f0203040302010305060103020706050a02030601090e0c0711180a06151e261815070e0d2a0603060f0503071e0b0f09030105 71
    0x501c110301d110709001d90200d0103043c8291301030000340c00e003d400c4455050300702c0154038058000380704d541c0010303020200103d0080c2c0b285045000c4c2e0310140e0029420681180c1c015006844001c08160402d075083c0f02d58400f09246004090051030350b514016500e04103203000501d840226004913040010090038050b45400410480b60750f1a0819640c402010324040080ca083d18030003007061800c208201806007504c21a80b007041103480d2928680007100d415076081e541c2c910311520a0821001042d1000340041c01040c481d0182d01c0d04403c4002040ca112901000421041d1050a82c0301c2c0d40350b1080c006402c2c1004020a04001008140990f02c2c000200030b29a041c030324095070140071b440d5040f00800c18240d4a04002ca0000c1180c0b06042c0d500700080001c504007031041400080c140a00000c07100413402c0c40f002a904050b029211a50401c0c509c0c0b0f400900d10f40f46e0100d00c0c1105a40010801d82c040b018140581710702100541c4c880d081400c15081d42c00140a0b41d1212a0b0399012124249007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 774133219 1250 774131969 774131993
    0x35221a070210020f060a06090b090c0307030c05040b0a1725110a080301060f090501140d0902061204051608070e0609040c0806010b07061401060509060d1811040c020604 74
    0x411640b2010b040807181c2d040b424005120031401c110321640b0300340042d0751440d40241c1c0a075004618100300a100715820030060762030036510400844010800b06841750701c81d802c1035000d95030714141286040d074ac80d404a01e80340d224091580002d540d45801c2d80e0340200140704940c12200b0306040320b000244003603554922910400f6803905014800c004070007400001d2194001080e00841d140b03843c1d41c2c2d241806480110105a40390001c1ca10340004911507000321460207a15101d40695800c0c0700a10030198001c054854040e070344030700e040c000b0030207440786501094070640c45000945014003003003140c68010a15034100c034030f007a0000e24092040389880c452096210380c0c00c07a040182c6460303c0c01e09044641c2d0a8108008a0003440008240603141344010310996115842c1004030000d101c0038182c240800317028903400903004010340405842c00d00e000e00040114041b0000d210300400314080c4800111440c1220386001c8105110940d141c9072040c02544500b6002408c2d4502c3c00c3c0d5076940395042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 774134469 1250 774133219 774133223
    0x60406140d03090519050f010804030909200f040806280b04090f08190203070b0f1807081c0315170a020409051b010c35221a07 56
    0x950300300040a01d4401d0040d0f000400014089000360003040c3d078404040016402001e00402040f40d4100c2e46510440d034080c821a050380d600c0c10480e0400030180c000c2c1c641240301c0c02c261542c07824002c2210f00110f0080075086016100e940d500c514064910342814001464034001c009080c02d601c40800c0c0c0c4032140d03a520122814002001d40300480060001d0a107100090b042180c0079080702d040042c2107005110610384245103401d01221004200d0341c1344541e9200900c1c605245001c40c01da0350468454a4010554896516406080000300381c6803070041d5112070f005d588041209000b09191802c910440080e038502400b001c001008140c845000902c51750541c8400780842e005400018003103034000a90041c400d00481016040255071000000516000a090242080380729130140e0348400300d582d03101401039950000c81c4000f0451640080c02d04e0448042c1c2d001c000344510840004060f542c03801c40302103e03a021035591f10b1314254450b4002d61403000005100745d03a540b07156000e85134015 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 774135719 1250 774134469 774134479
    0x110c030c070b041d13080705061512030702040b041d010501030c0f1d0703060b0f040e0a20030a020d061520070b0706060302060a09031106030f0703200a050406020606040614 76
    0x2d1110811403c05d04900b0b140a041804d02260182c2000800f25950740101c10202280d03414071560000c20050b03105291b078483c550343c810080713500181465088080032200003040050010303800070400000101840c0a49196503440b001407040240071686000039100c03e0301103009483c144011851000c940f00c244180240600c4005011540329801410243c4100e140075501c50703c8104a590054002d030013400900d43c2c0b00d00000e005995544548459401ca1230001609035064076101c42b010340c000b40040d001d05800b0040c40e00181c40d0380c01884020008000d00310400081d07040000c010300c4513104881300003400e0350748020445070006400019242c003045034683c0d414503481c1640040859910094020802045400c45190002128021203005024048447c810b040c10402d052000322507036821100b9100101e4501c0b8801e6106a04008072100c011001031841c030300e1a03585400054601d0700140b4001018811554107014494200700c041d10184009030600d050107194581080c0018014 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 774136969 1250 774135719 774135721
    0x71d0d14250608061905060d020403020303030c04030203060a090b060f060403120302280203040608040f060609050a18020f150d18031407021f03110c030c070b041d 72
    0x300c0622803000204056000310340410001c50519101c120603201e22004141c043d000108503060406520f000a11404540c3c1c1c191414501045020342200340b07044d9450b94244030200041e20300b0802940102e040c194a030761140e03c0d51040500c0e1030001409403452074202019440010100c08034141c1299007102c0c003034100c0701c4000c0400d84501942c0e00c00340c01c084141d01e806c1d04980e01a03000b05003600000890480d4610030004800500c40a941130800603407080004014580c0705500c1c0e50340103403260036501c0f401101900c03108103480841e000b98000c0c642c1c1c0d9007413103941100e44c400d4000d945c080c1c1d445844143c0e180d4000450002c44803010500a4082c4c000780c504800458040f124080305a113010010b28104c003010408080030700a00300c010801c2d6002da060364542d10320960b4113850307004064509200c0303114170703182603000d41c04c00c09c0d8141a15403840162001c0000c000d0200800a40015521078050f28905440d00605500c80007000c00d0400050020084a80080030b150321000c0220001e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 774138219 1250 774136969 774137003
    0xe0a030e150310051c12030924050708180705102606040f021c09050f1005060a150215040507170109061103010b09010c0809090f071d0d 60
    0x1c00415000180c1c1d1003800104010000354010030032420b03618280ca048540e43d42c14100000e003504040800342c48850300702c0344000c600d032080d00000b189600c9140c03504807440080801da555200f201010411594552040010150f4010241940b00c50011900708a80320315045142d1181401e000b2140142500045500c81034080e041403912040e15180c11140403040e282c000304408010307650540324905003da020451100c40c025141015013280080345040c1d241140301004000c584000c49030340c0900301079404101001e010660200721a84008036141c9000400c010810782c1d6500185601c50760050071802903580082c5001d00e41401c00c1d10305050f0b4680d420300601c0d040455100c140d11030010403954800398419084102c00a10030f0400344448004c802000c200383c0400d018082d10007030103005030800386d03100b1b014160505010f48099490310020740c000c601d210204076080e1408034144c206101c045940240800745090380325407142c010740b18170320000d90108280c00000e030448545a9543d69 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 774139469 1250 774138219 774138229
    0x507230c0126100806180d030b011709072114010507081315020d0c180311040903090e0412020708060402180c0d0f0e0c060408251503061401030e0a030e 67
    0x80a072014108480c03840c40d0406c03842c01c0150741c81c4141ca80314014804030100690080c010f00941040c16190310440c52510b112580314540000c0c007070109413140703070b000003540712003c407030607109080c0100c00b50040b000c18102881623114500d110001c6a16003400c020b1069840a207041c2c00c5009410201c0100049003005040114202c1c0c034802d85510000f14a1a440318a0740103106801c07031500c03440500500c820300c481429906201c050140f14402d03208440c0c0780b9080d803140301d105102c0d040450003140c8540c445414040d040707408490882100c00080b40d02130301040150020182040105001c1c0341c1a8085420500d0784400a03036490005001700d0881d8282074180c0d950f40960210802c9124030300304103a4060500301c25041c400d80281c4560410030b0610004035801d40700500300400114850180300c0400e02d040001086071381e2001000851aaa513007281c034180131000307541c0400c9182c104000c81501681340754000341418a8145846020075003c1100b403181a09818038503101c400e2100429 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 774140719 1250 774139469 774139501
    0xf0109090f080d0c030f0b091501020102040e0114031c0207030f020105070203150a0b0d0515060f0916140301140d033005070509060304060b010507230c0126 69
    0xb403001d280070420b4640d0b01c0351540002c0c07000240e5038085c06980000198501210710300c001d0250000c034441c00088261252000c00c10f058103062000601d096680d1080000f0308000303820032140b40011101410552900304a01d800401c0c040384001910050f01802a46e68003662100500e2611200c56841c05c0d0780c054010390b442a038024058a0075840c3c5c074801c003901c02508a4610480c2460000c129a00c1c3c01c0600e20522a158050010032084000302031103101940003c181f42d500414084460b0b181f40c4884c200180601130001540c1d03141c1d01e402e0009000d0070210070345000250700c18030040148041c4125214034118080d00c0030301d0741c401c0d1800c04484a80000d0020750004010601c0c24610904a60b801080080009130800054481c11012105032150720240c030307480081400841d0124200da4091004a50141445031030b1801696a040e100031142c0801c0500075070201c40440781d100c00b800310019810092805051f20841410700e2442c0c1c0c8079174030201e400e40b1003a100083d804c000b651000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 774141969 1250 774140719 774140723
    0xa151d060f07030231091a0d020f040903050a030c03050606040620010204120515011208031302100906030b030c01090620030705010209012c1c1a1e0f0109090f 70
    0x5011003c1340361701520400300c2058200c140c49030501c00300040003415440f65440420541a0300002100440104240380440c00d4082c0d902c201d5101ca0300b50300e80d403070344184240c40f0b00ca0348440d03448840e1170002404444903103001c80140340c2404104059541c0301d600719402d0783d125090040c8200c0141c0701194140e0100030240000c0d6100003408543d440302d00390005c00c0180f0913000c46945112059a40e00021028480c8803142d030001410721001601d0117001d0b660051a400c11007503a00c4140d0000342018440740582c8010407034011052061650601640d01040c006600070b10ba510403000c002000350300503100351002c01c20102c481c1140464015584080d10358000c04503901c0c0e039003d0030310078000d42c401444180402d916047c4052148000c08044080d1199108204460b40710030003803000120200d090b2040b580c505510b020001080e041000a00c0300d01c0144000c41c1d031a002c0c450391007007020f100380940b00c100311008010364500c001d0903ea0540300c84180c0031419480741d01d00f4a60441c1c1d00c1c400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 774143219 1250 774141969 774141997
    0xa030204180b390f0a02030d2a050c100509070b0f1305011e0f09170604050601050609090a1d0d050a020709090f03030911030a151d060f070302 63
    0xd00010241ca003c490209800200b02c1408540c50b60148468441040b01841c90324201444488298a0b4460280402d010540142e9242c5136140c08000200d481d900004000d02e25014402c00e03c50b41280c4080440082c50b050162030907041000c040e03a05c8000c03004103131445071200001a001d40b000e21940c80107011026005481e500d42c001c003020300b601f2040d0b80f80f00c45200c0040c00141036108a120680c1c1d0800c1c0807030b0020100c90501c040341c0e1844004180c80a0050381000042c800c0561403c403600d444a000c0a81000d090a240c118100401a800b003407047c2014816000e40da665594850f400c003c1122001071a0060340302040d8202101c440d54041500174101181d603c290170400402c203200c043da082e5551a13031201404404c861003401e0243c0180381200e50840064003d6000000303860180601c19541418200001d14281c0781c880200c0f82c0800f00d4080088905080c080d03003032406403162041402082c4813202c0c030b90703601006104da408009030b0004907202c94002d50440e541c011200903 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 774144469 1250 774143219 774143221
    0x1a0d0803060405042f030d090b0403080711101106063007080a03110d080403050a180506041e0b03010e0c1b0a060e16060801060c03120c0305240a030204180b 69
    0x8040e2031783c000032000c0c8038002d0091203c44000303144075130700c0b01054800d01c1c01c0c10b905040c29511241c0c0036030400c01040b6032f100146601d420155441c1d5405200060182d0358868103c02020721003400d040c00908454003545424140c694916a40c4c14000c4205d41d0140e18500c40012b13440500b40b4040456210790000e006d5040103505050b80108180c04440d48c02007103840e9a20205d80488030303914220340140004100384514212180b1802803030010b05041d102640d1003644404c002001540329034806584810092003240c03200e0301c00d20000c401810120b24190542d890011a4006036000130140c042c025000640e12201e42070300051150090071f40801c40d00001000d2074620002c10701480700c0b1149114152122100c40650b03036000083d18400e9548180b0303a403030b0030000e030381c06480c1920407024042001c0c040c490348074503403203103403450304c065a03011402d41800c41155466850b02000f404020315015a1001039803030341845441280d6050703070001082d181c2c5e100071000100525a005202801c048 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 774145719 1250 774144469 774144533
    0xa05040c050409180b09211b0f010501080f01150b030402220603032703060515041401091506020c061e0d1d1902090c1306031a0d080306040504 63
    0x1190b950801449260500d04a8072100841640d03003007200009601c9910002c1f01400e9100000301070102003140e030841c0181d504c0104007440c01c2c0710000603000d04681d550401003012103020040a060741055000800c07854010146108508000380200c030480d1138004041000c40d1508441d401ca81000031103400f0180c450030f00000040c08041c401540080d48040c1a1004400c0ca10b1040c44118050030402d04024510307602c01d0f014140080204020801c5810001859101e50240c280c420555404000c040d60501d500312017240ca001a041c16002418401888003603000261207524800071126240c603120700044800340d20010b2500410007001c0802c030304204150303036084180b40001c0c1c00e031110100151481c49a075100d01440002401c80040a040009070801005803908500240840c5103060500c41007407060054682c048c40c00203079690294140c900014800c041c01060844208280003281d13100c0801034080505000c1c4160303582c6002c80c0070030170601c104080c0c0c4441c40080c410300c44162 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 774146969 1250 774145719 774145751
    0x20708070303020309270402040903050c0318040c02060103050d0503090307020a0b0c0c09061e181003170a08072d0c0c0801060b030f040501020d05040b07030c09050a05040c050409 79
    0x101d01d6550003841c598801c070710040030981b5004403d1402c1c000000e22035a40b40c0810003d845c0d1f92005409014040220190034141031004140c2c055201604c41d0b40300202d4803d1004540c44604100d0841d04464018000101c02007444018080103260842e00c945684001c6415442a000000d43c012031800001600c00445030103441010401c00c02e030360300c8003044c0060105094040399815400380030030070b12540030507420b0b03025217038484050314080d0000c40c280d81c001c403a200295450008440c4d801020070801c0361031581c40c10b010303151096040c200030440601070302400300134004000b40400e5103100b80702e40c5411846000012030310101c000c1e01c003800b031001030038115840720207540314980a80f02103103100c1d05000b00b0003101c070b0070318940749503a480882c419100d92014004440d00e5400300b00d68140c0e180c060040f00d0166011708610005800e0109003c0d08617400010340740300f13011590004100a40d1043d00d51802c50708140c401040c102180c0c4030032101c1d4404c68019108a038a841030b00701d10b519003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 774148219 1250 774146969 774146977
    0xb1b19060504060b150f0c100e1e0f0a0308220c1e05060706020f04031205041d1006050a09080610050a0e010311010e0a08030a0206091015050d030207080703030203 72
    0x200700130000c03030780c440c130a000103074000c0d040d090603482c0d04101d0002d4a5020100412602000b04213032014407640702c50003801d5a0f103002948000c1d84c04039408410510406880465100c07140d00100740c00d805c00307a49207440e2520000041c050229000005124450207800b8840da0500d44441c1e09940c0024540b031940900351b8000c882c01d074010442d919004102041804003a01e60060195041c58100d603243c802a500010030a440340601f07200001c00640c03410b140305010308035a11010344550500400100a800c4e000b103400c2081b400d03a05101491549141c088181d9010345400c6503904103205040c5d50002c4598454803031886003d041040e41c01c1300c2e1840c581030300c00450f0b000d40029601d0300320341d01070030081c007020308120182130b100031081d802038200304145100500011515942c2e028594295080810340d5005a049001046501c42050101505c50b15801004108040b0708801d80c0c28031a038240200c40c001c8185a616a0505008000110090030414101c400c000d8492400a4032030308 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 774149469 1250 774148219 774148223
    0x5131a070905180103060b1903030207080c06032202010e0607200102030c060109050403020111041404111e0c1005090f16050f010e010e060a1809060b1b19060504 71
    0x414803404100c80c50004010114205480b2030f18035281d0030742e181d1000914060403070700c0c1d01c40340100c1c0920804000c2d210410085000e03030060245685003a04003800e25041640c000c1c0304160810801600314040582d02242500d0300400b11282c0c1160300c01170300c1c0000403507411580301602090940400c01001030392134141708405043d04107074014100580c1c0d240152161a005a0421801802600d502d6401194400c3c0284004076820440c3c002c120095071058215070f4031001d0fa10b040c1003090038680901b500320346403e448c50307140141380b02d240d0313862094106200b018050000342e072030804c203000c01000211040210040206041c88040300d5030f12071002c80f910707800380a040085800078441c850000202c401c0501410400914a0f0044603205406c000907414041c03410303440b0000382c8400001d403800b102c59480c0d10b0841a2110ae915117034030a42d6100004103410407800b8000c00e04000142c51001421200c0c440c1c0114400890f01d04101030405600d10540c1c1d9850b6900901006800c510b000e94 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 774150719 1250 774149469 774149477
    0x30e0a09060515030906070f020c0402030a020c0615130b1f02010b12010504031b0f061a130504080703051b10020315030f071e0f180e030a080a05131a07 67
    0x100f014690798805000880395075000e5040b400004446900a01c021142e4601600c1030b208a000e150001600b203030001d0b0740c860541039002c10030640801d81004a42e410140350750900050320312120019103203040040c010f051154649a852040da1203221034442c0026594039200203a002c0001c0090081089659041c860b9074030300d004400483d03041c0301e410b01998255851030002015108480040740300080c04561000c1d1840107100850002c0c41080c02d0783e01d025802840e034071068030801c40394449844069140c6840e0409100000b088801103c0395241e04d800c0484d11806030314698441d00580b482c50003580d0003400c0302000d982d012036005510503102450360b0004c00f8034800500d03540ea11440078032001648080010b0009009032a443c50a40a40707122407403103261144600701040001c1d5004a1011000c0c01105440f21118081c00045800381c400450401d901c1070002002000b0207415040303000da5980120345128100001c409020740c0086100c1c0e842c0d0030b200c1e06409049801c0343e0141c001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 774151969 1250 774150719 774150739
    0x60230040b0c0301031208150d0b1f06050d09030207030213091b080303280c02030921031806040b040b0306030601050a08030702091f1d0c04030c06030207030e0a090605 74
    0x4250880c2c1628180ca0300074901501d030144000c010b035009100a0030414650f81819000040c0343d80b00324000340c20a1290075074030641c1c14288003110700e01c0707034840603001c0c1144011401c0c002160b01c07200b52003410b8441280450302180300e080690600001380c07c081e400500c4611514014401500402c100c1d0744240442c10200e03c803400b000740b8103900c40c095003032a81c0040020132150090541c260103003410380740610f51a440e81e900c080b03089890040080d00980c00204030f250081c501210f0090124014606002902d80002c456640301d1103554680c0140108000c0c0c207200302e03113a035170560b406410190340032655a030302e950030b1940c00c0e00304640c100c0c0701e4494000041440c0c240321a0310700072501c4803002581070040036400c1040645008080c1e0002040650401840165201341c00c8000c0040c644040340010341c2d100250f41c281c00040581400c62003c02c0200005801c415000044465910300140c07204900d190440e4840075691440e40e20401a00f03011420320f40c141d10a800300d034011601c01c3c1c4c1e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 774153219 1250 774151969 774151981
    0x1805030408070e0703090803070c032a1e1112070f0f080d090f0b071b060804031e020c0d060b0904080c010b151219020f0909010b070f060230040b 64
    0x75601c2c1e0f100018240e0303e003440030803185401003e0ac440210301c6800d024120314007903005544000c1000c0c202d01904408902c000d02400085c880d1464a441c174030103041c00548442e2038031002c00303c1504000303000e00d6400c0706070800d03440280b1a000103440060780e00440640c0e10914025080302500a0402600505082c1d5180500403005003048030040b0345030480031413074611400310f01d4100000c1a80c00c541d14152091500320590003e0b00689010f880340314890400b420014080c81000c182c582c515045d0700c1c583c0d000c0d21b4000070116a5800d00b00c03407080d0110024074140000d80120308105420030300c0c08e0148410004013901805104003844000c00040d00350320304111150008081100385d0314000c214107200352600401c143c0c2e01205e1010390340915845400c400c4100d80c00717001c1484003068003140c25403451408550260042440200103420130000e134039520003150b410803008100a500044071803504001407510720741c00d030000c1100d814800d0084034800141c2400c8130110b034a406000b0001e02 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 774154469 1250 774153219 774153221
    0xd080d0b18070e010f0e0402041d090303040b04150e1b0118050a0302040f0b0a090603050c0f0303120a0608120c07050405070c0b0c09060304050318030d050a031805030408070e0703 79
    0x2c070402d0300f90384084805001c02d00546101840115403030070408210414445a1118002040280300701400380d4080400d4144040150b08060510402c9420401c01e11001c2000350b4809a041608118940c04603103410741d191004000300c40e0682514000c0c9a10141c0d20740b000200ca6001d500d007a00c41688165100c140c010702e0083c140101c60f40301070b1b424414000350030158044070450008450001b0400110800161014050380c002c01496071101e0003070007000b03400d1100d180c2d542e10903661040035640c403100103600d9000d10707400b03185403445440011b64001e009030000002030512800352940b00308203030740007183c41e48400c0314040540300d072400015040c1001d02c1410321440c15940c03168440c8843d030f0303245041400040d094000d220001c0c000a1000d81d1040c0045018900c40d078000c40d0341e011868078a0131074400d0030038030300e220380c21050700b00c000303240c0107411600110341d54500082d02444084401c440f041c801400500944000704011512010004021050340c2c5985000280e80e6034400040b4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 774155719 1250 774154469 774154471
    0x70e010c0305070627031106060f0f030109023a08160302030d1a030c01020c0f15040312090501110c0a15050d11030709060309021008060d080d0b18 65
    0xa001400400089001c01d00c20006090307640d02c41c09021071810048a9010404080e20702c41091001412080f01c0405070091003400180f07068501400d05481c2c098006981c154150258a00a400c42c404c28a034543d402e611590740d05500401c03030898100b1080700c0107100030a17840100320440071105400254507500703d400340c000b0741c090b240c0e41c98200c00e020945000c03504003604070103500c01417050404c101c0c1e460051840e03130b075088011400c5c0c0d401840308044c542030840c42d0b5a8195049442c03d00320f9511094080082110207941d103444580902803501218440c940c0050551a181e042c1c082e401580000004101c030b40036030310710240c2c030324030041c4a403501d8401c48045c0d4000a882c50803c02080c0c141914541d00c1c1072414203505013400e0030940340540b0300745603a00781c080c00d0000c1008103a0b03030000802c1b00900381a01d800c200043e200e030301007410003a070b05c44d040c82805050000251155240100621615480042e00c1d8866140c13074003a80207012500210303803080b19a00d0300c4101d1081000a19 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 774156969 1250 774155719 774155747
    0x320071409010f0308070c0e130b0708091e030d0212150a0e06010f1e031b2c0301020418060f141807181d090102041a1317060a0507 58
    0x3443c15140346a81d00030300e80e8000ca1080315030410660b000203203449408040383c81055125003a941c16851032408503a0150024200004c3c0510719007404021240091589403500410f00340c1118a91030fa400d01d0300d54018440c800d03588500000d2605100c0c060300b0a031a001d400001140350303944111000f00241400c40e070060b103071a1103044002490310340c4140041c1344c00d21194145001c021004900c9140d8100944c2c2d8106e0129803680c682c00441080d030209100e400312540380c0250324403c258142c09400c019030f100c0040f00402c1c030101c02019a42941154020451407100a1103c10603000c0c41001c3e000601c540020710048040025002200e05800d01f10b040d001014246100044540c00004030390140190302002080040803a1200344060003501408162a01000240052101c0168180c1c0144000d00700d90041c00204007184445151304e00a1400860440d00e074641c0014018021209a10500400840c1c80d402704101d000400c2040c080e40c421001801180c0e10000b0135140c00e0745103042 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 774158219 1250 774156969 774156989
    0x180806130f060902090103050609071401050a0c0510090507240504050d03030f0e0f0610052218120f03060302030303060d0609020402040609060207080601030809010c032007140901 79
    0x30380c00015007406011a0451182e100091030400341d40103e00804401d80040310541d005000784015200c0400040000b00550b409500070003010b4070008040c0d000b0781c40d909003070001c82d14411081100602052040031007c5200700509099810401d903108110710400c51301600c00740c1066800001801d51003a1441e2507101c00f0310b07240c906014010405041c13a0207900301a641c0810641c0851a4002d60302c009a0480c0182515022590306604150700544215005402c0c058200565241c0f070281c812400d000802131869034100d603501da0042e003e20032600c1c60344001c8015910030444ca0382c001302805145030f9142244560160300c144d08840550001a515078010320003e1100e2500090000c3d01621594001ca01c82000385e004c50241d03001034115001042c3c0c440010310400e40c0c10403c900c004c0080d18010030b0702c0c0d40f5607101c6c0511445072003007541c10400010098010306000e441c860300411100407400301c1c030507501000c264503560710340150f46c0c0a84043d4109240c1d07150040c1050b06844400c10 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 774159469 1250 774158219 774158251
    0xc0203010222061709120d180305090a050d110603090f070f180c09170c0d150b0102030a120504020d1a1506071502030411090702030418020403120e011806180806 71
    0x8461011340c01403d408410315032255903a800510b0100d54000c0701c64401e44030342f5220348944040007081ca90b9508560b005140302e580e1840400c1c0a015188205c42d8280c822030759a456020880c1d00305410b4a1100d1514410840001030b10766905035107008403182c40510940031165180e8001c1500d40c5c54506c000003d849010074441074105030300d0703440000380100c12162402c0c0201d02260b520030082e041910f031039203451182c056441032409068200f000907c0a9850300c0c048480151012240e00724285c4115a114001802c5441e407070841c108182c4c0145400503044444020802803050844000c01144001d00040c0180d060500a840360b080d8072412050482810400d054001d400c01042a6042c8103803241c41180746e260701003202c0c084c2282c6e40c05144c1c0c460030860010112080401d94001c910300c100b00c01c002207008056143c407201100e24104007032807a06030049403200501c084642c00d110700c0d50700001e00250419017141d4502e601001240361559a00101a200c00040f207080031130481d410 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 774160719 1250 774159469 774159493
    0xf190b1305031e2b1a090408071104021b0120120a1b090317090d020405070c05010203010906052103121305060a0501090b120705010c0203010222061709 67
    0x340381c83c403001540380c0c402c90804440c41d803180915a9284141004040354a0240454100d14002c40604a0204040c00603440d05040030841c506002000584003200c0421180208241c034844c4841548004006548694180c1d402140a10040351501c00c50361801c60504c00088038071452100d040740000003141000070002002800b500001c0440c1d01c0c607903443c000080d0f10b40560198407a60b900321b0b03039518241800c519091131848150030b46803142c000144100e810b29070301c00c5140140305038140c4000c80c964542d400c003034401d2101d001c0001d102e54001f10005c240c220b1307547d0100c402c03104119086101c03060104500802c92003a00c80c80c1140c2d4004205440c4a5200300144580002040c140d51241e4405511a42c2c2895410b48921b3301d80350701d0340010082040a402440d40c08170381101e101c0403018000c1d092503076581c04c030311803a8144031582c056601035503420741c1075481e1203113601c640c0c038600c07152100c8084052510703000f028080740802002603c0144035820151147d00f01500078000d01c2010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 774161969 1250 774160719 774160747
    0x9010c170307094419050303101e05040c030f0515030705010305040f03030e122214031b1305010902091914211603020f030d050f03090f190b130503 65
    0x10f04c41c40d007880c41040f07012040404125603070900750380240090b580f01c1c00c00503106083c003103d9920020905d9031410108500f0b0300100204000c45000b16400250008901410b07000340c5030320384405003598602002c100c0034219100c0000c4000c1c8043341640c0302551141c0066080300d0082d10050700d403044031010031001900a520507222000c9040441d403401e1000300344000145d1001d1112040360101810604046082030800300203801018404c1810120500210b41c0d0b404415042d4116210408130040351911110a10780800742c2450f4144201d42c0c550b4904c5c000380d808124141c1c05485103a400c0003880e841030000d9410344030944031040c40c0410fa6010094980f01240c9a1042d1a1219080c0d55102c4010446401000550440c1c20882441c40c010084584032100b4020b0290300885c20b00c02d01c9640c400c1c220380f0305599190109460743c880b00c03403203071030150092018002e03803042d880d000000d46491120381c241e1521900c00c4003203503030311a5110b0080000c4654028481d41c418002c0014aa143e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 774163219 1250 774161969 774162089
    0x17221505160c030f030509010f05040617100b07060203013008030916090c231e0d020a05070b0901200a022a040f050c09010c17030709 59
    0x140c0c102d03815040d12070b01c6010402c0815501240401c0b000545a6a2075070442d45440340c0c0c2d10701d07044c480d08241c6441c5025003281c004041d030329400d0000c8400501d0007400145108050b003c240c10068840300c10307203080380c0254800c0c004c02c1003032241004825510b121006069990700f013000840000e022150351503a1035a000030f040c00f81140501080c1c2400c00061410920082c102c0c0500400c5c0c100f503000307000e0400f50405076446810a0090003190001d18100300316140620744180300c000030441800c400c9401d010384614030304668000598800711b540d01c04d014105c0c46001d01031404454884610700c40c01c90b411840e04d0302800b00c1201e0701d00d086000c0780e00680103075062401590031182c403031701c05424030a41e0340242e032195052440b070380142410f140c4159600e04e40d00c20000c202d241800404401c09000e5000001c0c100107101d950403041040290b41c0c000303c040000b81c59070b140c0c1404034002e880051140110300c044c28400c028030030044c08203484214049281c80340e030008810301d21024245000c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 774164469 1250 774163219 774163223
    0xa080703060515040603291011010501080c0901080109110114070b070908150609061c08030c190e0d0204020904060b030a0b0f18070305041722150516 66
    0x764600000a95844440d001c8283c40c10051020f6900e07401c0860140485001501280d200301d0610880601e10241c3c010803020810101e49544400320901400c03118010a540d8051440d400d040c0002018600040c00310780516040350000c055070780354420350313088420307000c400b0301201c0000243c02030360750123070401200300044100314600c1e00210b62129180c0704c00984440c000141c4082003003001c0390082c07113002030301d084c2400d5000003824030000150f00d104003d0040c0b4030401d440042129024220010302400e5940010304c25220b141020280c078546e040b00c3c644d046001175254066045a203c1d030b1050b4164140100761250760000740e02400029080030034050780056513014042000404074000e0b40c8110004100820004000b20038000f40d03168041000d8010307800350000800c004034080f2619444881c0b45000180c40c1c0da603003041c485030100c00010b041000d1000840031503e54200e01c5102a07032032200900500307956980b02508410b1041c4660000241082c8940118240c5e5004605c040318 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 774165719 1250 774164469 774164471
    0x230a030203060a030f0b0a050618010504020f2a070905010605030f04080c10090204060e04030903060b01020a0b0f0f09280c03020907051c091104051f08010608010b0907050a080703 79
    0x113440769a01c8042d401c107004140ca00340340180070005044c0c0c03540581944410b00360359031300c050101c0014005ca41501030140c54841da40104121442542c0c4400713481c4501c5440460140d100f01d0003808100310010300740403c1d083d000c0d08001095041c01406454100c40890b50780c41d203141d480d1100c1002c54400504126103144041095159807034042000d034000403e030020010b144090b80c410401104d08591044507115000c904100100350045d42401c222504500d021540340101070040f400d002c0ca14400412851091050042022503030003502c0c0701d0079503040444013580f01d0fa00704c03581d40c80a10840761003c004280030003030610400410f94265a100340c421401c4141c07203030300041d003409044844000040c004100c05803c107130005a106604008001d04228049564903a01044caa00400c690300903a05c440200c1c0c81c0700141c0004801003c0700c610450030280d2140c6e00c1c5806480f40e031007440119800c1103440d003580e09d0b0082105015040e1601c07014501040b44209898003100140302c1400c0c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 774166969 1250 774165719 774165739
    0x614030115020a14010b090a090b0103020108070302070203190201080603210f0c01050708070216140d050f120309071d1b0409020d021c201308160303230a03020306 72
    0x340782c804c1c01da003032a003448000b181080036001845142d40e402811170550600b0301c400c02c1d0100b00b07984001ca055a4080ca0000555a15143d0541c00392080290003900340c810483d40766040c1c0a0001c0c00c081c154800d80c0c0c0d6401d10780300c020825039200d824100101d888048a0350200444060b4001440190300300705800d414403a0306245a400c642040f03484001160b140010030a0a40e414030080300c00300c2e00408107540280c00d0413040c440300316606848e030340200d2424400e00706010080280754510340c1028100c801c0c004404c40036040d0303904181d901e03944070300c103114012460060407100305010185030f00e1200c44c036503285107105190040e43c0540ca10006000c0001003001690340c0028078060b040003402603a9101004d0703044c0440030b800440403c0d000e14004000500700e0b800c0c05d00c580070410700c00c2020f44510100c1d204400003855940051450702c5249000e40c0814103900c1c403102124040c0d264000f00c215588455030790a039111006803411a41040341c40c40450099000d1500f101000d0580711395 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 774168219 1250 774166969 774166973
    0x316120606231e0315100803040b04060311190e1201020903030d020921070f1a03040212010f060e09150906070f021c02010504060b0f0a05040f11220614030115020a 72
    0x148205d17100c241a00c260303908108140200c0c400c0300780b4000c2a0500040d85080e04c0d11440350001e0103140102010035498000151600e00340030300703865140c1140c00b10fa007009a01349130007905a203c007032009806140380c1c48110804400600c01d54000001c05070245180c44042c81d5858025480010041da2086203869048016261500b121001101d2507009180d100d06003070303400c402d8004a030300013030440c42c204120a807038801e00001d4982003070b4152003c28456070600180c134098240012540e2540d03146c00400241c004207120120701075001341050394540e5249024640625104445026990703100401180509114240e1402c40d4040d03881524010041c16804042e42c03d040440c41c40180c0d144e0080c0024003a10380b0510312180342c101c40a86014442c0804112400814811b003032040e541c0f911004001c40080e040724002e0940654100e0f07980000f4403045582e006202d080520b144844280491074038003440f00740e2440c800c66030707880d82985c6c40c18840000c0030310000f07103410841c010880c134100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 774169469 1250 774168219 774168223
    0x30806130c0504030b0a0203060a1202040f1a01030b030c0609150f030f162a0318170d030204140f04020c0d020c040c0c020d0b060316120606231e03 65
    0x1258800640e1510faa440c50b6050440c444003014052001c9035104106010195940380c1e6890704880102d03255110015030f900004004007503d000c0c1000c030b17a0425018410035280060f20840c201ea00362800c200359410141815501d40c0d42c240d505130042000c20100d001850701c00c820301c60701140700444c81e1500000c0348041200380c00a48441a80325131384014070090b10007010bd0345c2d905044914202800003105038901c0c600100d5200b076410012300703079040c41080c54800c002c0c40d80031071500440350300314a81d6814284440c078091500c20129000303841196001500c00c3c0210b4040310120280035600c000b08000304240008541020759201d58200921101c042c41400742c1d4228074601d40245c0a400e05803003c2c0000e440394402c00e441000640c02201005960f030440492100c2d401041d550840d680350b4020034035110588003040b90f121450400042c03628038100c0741807015446031409110441d0384022001c2c03240707a501d00c0481100e8031001402c5050405540540c0c0d204040000c21400f02c11440200c3c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 774170719 1250 774169469 774169481
    0x110f070f060824240d1d0d0f090e0f010501140f07080a1b0606080606040b01050d0c030e10060f0b07030c0209070203090a03050313151709100e06060307060f050703080613 75
    0x4c452800c01050600d04a0414481c07412091a610080c10307560510030b0f10284c82d00308852061090141842c0c1c0798004504c42c00003107029107040400d62082c0c2c1006269121000001d1180c2c074002811038a8607400d06031907400f03035100c0d0350144480a0030040603a41e514515080701c0260420041141b0981e80005603003214400b01b5401203100041042c00d1100745410010700410650040b82052900030b6281d80c4101182e041d65a5958000303a2940e4a0034114050207404031800020300ca00980c09070303101c901c0da0160301241c0c1ca826001403000d81d00c8100d0b840d00e00401d840074012914030059040035080503410b2aa00000c284180d81c5842e1546002464021103500b007503443e648007040c0035800c40e00844104000d8541e04456001c5040502d0740100880341070300f1900c446038000f10104221030020000107100c2d01121005100c0030010b0295a940d800003107e40c140300b40700c0c00000003402400b49000714014802540d83c180303810050b0300e06480c00e010150551750400508480c003d01522288222 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 774171969 1250 774170719 774170779
    0x60d0b0703050403020c010201060602120708040b03091606021f0504060b0a0b0c0f030f1b0f0604060506010f0f05180102210a02120c1b01110f070f060824 68
    0x2d107410281402440c02d424130b9071a40c10342e031500d00c09100481d0005002100150041030711a61001c65203040c0c1114041d0790f102e0075100741c01005120900740041440072098220001100240c1d0742e6030340c102d95895880300008100c02c0400030707844440d081d6070003050340140a4000496541d50107000b14001c04407035400007000070004034041120f1201444001c040046000080d8100142198922501e101e0500f0b84c410030341d9480442d040705107041c05000744010070030059070081e16050400e8005040304540c41030004a20640d030428160180400d41d05c0150283e60352400c200340d803000c001450310300541081c1988181858402916000c400c50350b88003181d01c11598a441001d48041c1c500304100b400b41d54084c3d010700c0001140c281c0042c5d4074402c0c0c0710725046009941100401a20043c05402c8590342602130b1030305100c507000000440d80b04488030000015441a640c45080304d007100c042e01e08031400320a41ca1039058200034945800301c03605009040032004481800b041880e00448052 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 774173219 1250 774171969 774171971
    0x504020c0109210210060e070c031106070806040b01020a033e070f05030f1507121d0f0a08090411210603010b060c0d0f18030507170102070309030b060d0b0703 70
    0x600b03ca9143e041c0029400803101c41002c0c81843c0c148920020300390001041c40c41001030000c502002d00d88a6004051141c6040e0b0986400b030500740c0c001070000d5804c4070894069820030052410552002840c504050b40540d1282120030f4207000c1c90880880f090f5944c1c0310078030300383c80141c09215154695402c0868010040809514110f140e071841c0b132695014a200f070300094801d41300705c0c201099400f60210000c08101e1544c1c1e82c4517054032008124142445218a0958080d02e450b0200c044007585504e000b00321907101d01030b020340b1941e810302e45000516240c0248032070045420302e6040b4258910607901c0190411250002074103844594540440a601c3c950050124604080c0304040c0b046006540c03207443d1120001c2684d5031810205a00010020522040e0341400e00c80c0c0b9000703d9482c01c41a803415015a01e0818a41c0e50b0a00e005101c2402c540c504080380c60320052080760300c01a4107449084200f0b01d192540b503081179004100c0b54000c2546551000003403001d003a01881013006440c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 774174469 1250 774173219 774173273
    0x110f040f090204150506030a110409050103030f0e0415030803040f05030a0221070b010b0307090503012f0c0c0607031b03030e0c0901061e0309020405100e100f0504020c0109 76
    0x1080300703580101001c1300005407182024845c0d41c0360310045950200650901090300d0003011884d0340244116804000c085182c500040704040c0d1060a445d1685026601c400110801da4104411101076407121012000c81c0d1000708001038544000d07503070042c050602070a0810590303c0309410b50340300405840050f0410300040306803000c88000c401c05d02286d000d4030ba0032b084455885800081041c0110540f490000c00003c031030911071184030f406448094020b02c41c0010300781200041d5034040035040c02142544050b02c1e0212444815190906c44074402414460300c0d131014440107504c0107806800f044109010251510f41c4a048459950700c00d640000d42d1510100c40541010707103909061f0700c10750030100104003e56004080802d45070f50f2001070060b038008280d060b4028581914000d40160925003080769464801601c401203403480d4621000a80c2d41c003010b04109052805050007041982c00b060145061580c098400034110200006040780341d0f0301d86003045d262110000e002126007030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 774175719 1250 774174469 774174473
    0x6050904061b110a0f060b0a150306091a04021309020f04030c060e09221a15060708030f1005040e0105060f060c0a111f030e011401060c110f040f09 65
    0xb070003003440b1031582c0c40e065180a401020140c0c44030f04078139001e8000222410050184038255210a0000c00c1c0240800c401c5a50b1304450458601c0d2050380c500481c2c43d1070320016101204d805100900c80f0752942c01d000700341c030800800000f07420203001210500640384d030110b001401403004282c101004070900c2d440340c1c03452900c1104890039400500801c03003c5250180304d910781c00c989070f8001c014144443c81c03025510304c0f90441452080c0015104a04002095144005074064180121864181e0841d205480014400a0b20821000800da5242080000c0c15a2500c3d070040707401c01a9040588000390741d410000f4261114000c102c92540d42d18420711003035103022502004800c20030b6a03840e05050400724982d8803184030700030145c803880c0c0f003a0506a242d580d60500481000381d09124031604651b07064001c0041900341c0c502e04081d0300e0084001c001100714041103040750184e9075658208078240daa00c0540c0b03030980d810103801c04020303172003a400c6980b1b030b010b15030000c0d41d10030dc0004c180f2414 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 774176969 1250 774175719 774175751
    0x801080a21231e070b0f07030b060a0c0605070801030507030809061b060f0f060d03052101030c03140111180a032009160512190911180108070501030f0605090406 71
    0x1e207840c2ca842810410b0b90000359017044019480100c488680c01a6510444d06402801c8484055540440b001034500013190700310680b00c05203409010204096520014207480c00360081c0001303051a80440c1e8108001038010004202c8004041c0c01c0740d040c80001c481c0d070103c45e4101e04074000d03190481c10410045240c00050903902400d003107080001424020081412004107050240070030038001168940c1401c619a094620140740030051a19079490803e00303400f900602007100c0a0b04800041c11445405015110028490744a02c1d0319017200c00340144075001d090b48074a60070802560001011440740224001c100034106454845500c01104010090b80d00074408500d450051080e05030140d4810169050508610002c0c0c200340c54110a0b0030500d10103034a9032000fa42020303007450411601032901101c03100296568210741c170801b00460440502405124019445031204000640c441e070030540c4604070040002400603103440102e40d81d00f0b03007150143d880507250001380040c241d070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 774178219 1250 774176969 774177007
    0x90606030f09021e0d0f0b1006080402100818060903090f01021212040c0807091a181504020c1c020706110d031e0e0d0801080a2123 58
    0x480340c410030940b0700a6000807410450509554141000f480c41c4031941c0d250603d051904981203c400640058546824182c1d035508541c0c1500440b00008002034031402140300501036640105500414900c0d0341d0121207a200003000c01c00c4002403042001ca0103482404010b00681055000c0d50340c4400c28410303c0600c0380c020051504660000400e030030203030241001c4c0c0314509642c8408007096110703030038021040401e43d040411540181800080c3c071f08096030000c2008101e007200c1141c85801e00c001c03c8502c61600d907009100c200c0e010001503001d4000c3c5451a1701803001000103042c4103c590806242a28411020400720188001d0f00c4801c0e40421046009012510f402c40ca03c03e5003c044588035641089503100707241c2c95500e540e006a070980d080010400c0141300230001d08a07502c040a03941d4010542650104010f20004103920030b001c036090002d5608004644110a900400189543c6103e441c01e42005404258105801484071000d541c3c080c102c80503e03112026030303240d9116800 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 774179469 1250 774178219 774178241
    0x9060a030603051b090a050702071a04050301060b0301211509050a1502070816020a0b0706240f050904080409090b010f140112020703090b040b13080106080618010b03060109060603 79
    0x44c6580c14500d240d407589000e6501c56000074000c074a0f030700e82c840e05a250910f40d030445650806480c22140d4410074200107401254000c80007031200c2580c5010300c0404c0c1c4002e00940038440d203149410f0046280c81440e8000b85842101c190b59202803480a59048900024040b5500e400203412002480306075881c5403400420240210310f0310070360369948a802d100300d4112001c0030003d0f00425080d55150000c1c0f10007480451041580c4404500c4c01ea401000107490340b60144c1c0c20020070f402821060039202082c2c030b03003000c245103d45090204000035180010401c90344003900f00000306281809000c0d210b0854890136010791154148442c0e000c0100060304842c01a0302c220300c902c003050380e128110f003c20100b0003c2c0142c1c1d03000b03141011101c14169811004414000150020700c0e407084000404800700403203601048141c88003921800e84186110b03008203030b8441c1003c2082403141121b20301c02c64050800029000c1d440d2070209040074004d901c10310038a50b403518100010394150290300b000c4a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 774180719 1250 774179469 774179503
    0x1b1b230c091e040b040f02040501090b0306150915040f06080303040506090303040b1303230306040c08010b07031b060f09110301092103020c030c010621030c0807030509060a03060305 80
    0xd1070442d0388502d40d60000c1004c1e050203c0000401c00307011035420280841500074100307110642e101c104a1001d040341c10b05950007486018000355214144e00d08800702c860000704081303450f4983c0203004007110600d4182c0b50f8003613541d00030307101c00301c0f11845542d0003402802c001d5038072840c1500b8540d08080c2c000f0008647c2d40c06c10802c202c0040c51054240d540310f00f0006c1000300c8000d05040440f50301c8200b40d00300d120024901880c1e040c130390300720029502c1500100c505100c040c0081e141180e20308401c1c0326238100500244010800070340a40b0b0040711071a00c41010148000d19911640249d5100d03100c05c2580c036a80344008004d100c0c1b112007556082000303400a0003031111650b60b500360f07000c01256580803042c080c441326500302e1003a01242c03211800c410031251a0401841202c0c000c080c1c2d8481d0aa00e408000312911042401c1c4014090343c41e007684503482c840b0f1864442511580c0074000c00c80411504112400003560790034007038848003c003903500151142c01c42c42c180c5d15041c00ea0001798400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 774181969 1250 774180719 774180751
    0xb0106230304030c03030e060906090d0203070309140609030a110913020f01032c150f06030327100e10031803031d06010b0307031b1b230c09 62
    0x5200c911040300d812503410718003050419107900f41100200180302109903e17006a4082c8400c5400020380c840c003400c0d1000540340569165041039a0300c0c407900600070003083e4000001c00030100f03040440c0e40ca403030010b8515032070401200300181c10143c5040c0f080321a2103c2c0709004403a4104005d210780e0204038005802c00030f218a400040b03400301940700003410591103184145200d003001244180030003801c4907150071034103508402611109400c03c40395002520200141403508542c643d60702409025010b10302d40f0401c0001200d038141d00000d518110000762030340b036000e40c69007a00300c0c208015035503c620040708102c0810950711440040d0400b0141000500d035104002c0495020100350b00d1304001440c07070b10000706942c0c0402c46007801c2d60240620b10001401c211460b00030b41c420b071032940e07081180c079018035118030240c0100c1000d400010440803440581c24fc18058199049000e00d80000c04015544a829200c62005101060740d4203c95102d55681c1002003c464010707108901c3e8501c8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 774183219 1250 774181969 774182027
    0xc0406050a0b0d0e03030c04090b040204060903080304030203040f060305070224220b0f040506010e070c0b18060703150b09280b0c0c0a051008041b0504090b0106 71
    0x120701e0881c069168500c000048452042d2195445a552030346203a080d80e40380c0c0b0f894040c40301c103600248580d0507098108545214a407a09100300c606559880d122111314508546401035030360030050089080d840104001318030500380d1241d24000f40100e1b600800d8525003020001c2c241000c5034071050040c044605200410440440d040e640030607502c2c0d640000e9a945440c0c144211003042026110001010902070ba180385600b100e44100e00520448549990700c100d103007148242201c0d031000140000202c00c00055145200726001428100112548581d2050399420100b061742d0b44408699a0484c004210040c01800e800622219919a00700000000403903c1d03401c0c0080070601408074001c501d20b00d00c50407003104000d000c0a00f00300382c440030b1803407006030b6441e901c0ca0000e1096103039100001d0580b41c440802004804190b07540135040c1c48503594106a08002e10324807101e03242000c0040341c00d40761882041c3c001c1340241d01c0b4032043c0d45003000c040c10002400c401035000601880003248 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 774184469 1250 774183219 774183229
    0x905060f0937060905010302040b0a03030e0f18072007060e040c0c151e1b0804050f0d02010518060c0a080901060e01030b1006050a200a06110c0c040605 67
    0x1090b81c5402d003411010705425031480c4203800326124003407a5180090214641505030f1286050701d1007514100071148008040000c0c50150b80f100800281950042c44e08600345520303086c4030064003801d00520040d5030074056080c88011600c150020f020208100701141825401c84030782180e190213012400d06211000749a10800403615001780c1e11036548489040c41886800c1c4030503003080c00c03803012070f16600e040406081d841007803a18800c0c40b0500c44080307040c2403240e000c042101400700204209100301c26500000000c1040c1c5950051f00c1145808050a0201c40c0b024020350780001103a18111050f24070b00180c0034628401a4403c400304241020791500302c2c1e900580504000789142c0d034480c031040c090b045a40000c450f0700c402c500000200402000f1303040c000e5500c10600100c4a031580c07400c0b54140510710301200012008244080304001180700c21000000070b009a0701c0e500d450707480b92400d40d09220003a00489400046040707000005024035048407104440a0018500c0c040c0024 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 774185719 1250 774184469 774184501
    0x31208060420070f06140703060506040b0d18020405070c0308090f030304032001091101020105090109260d0c020a1712160e1f09050405040804210602040905060f09 72
    0x100b50000060403c091006003050401690341c40101406455111112058690002d54202c4081381c02c0ca5800700e17540c54420180ca058420580d00d49051030344889005000e080c4033360422010111441d82d100140e1650300499100791096100d21000d81c0389440c0c010803c0030300030700030040788c2c219641502c0d51803030100450b90815011b00d0100300408600340c0842010000b540e85e035025603c0c1000c15130802a0400c0c20700381132a02600208905c0e547c1000c102c0c01c1c1d0302080c0c40140080c200e80046000701070010100451b6024080110b42003d14070441407003103030a0483c007800940d0203803030b01804200c02d0740d20801020101011660800c10400c03801d6004c41d2018080090720241c2030700c2481c146100380c11003104e20100910b600648a404180220300340311030240c1d030f1700140141e1300c040b4003400c00d4000d0364040e59200080518003441d00140a10006c14000032190741e1001d042004080b0300d80380003900103071501314000506030070701d04100302e03401102090080c050014041004801842a6904 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 774186969 1250 774185719 774185771
    0x50904060c1b0c1d07080a110904050c0309070f06140717030a0c020618070b210906061c0f0605150d0809040c05040b0d1104030803010312080604 64
    0x7051032071030301009880d035950022640c049940008402018080400941d60464800c0c48203070108440e92407180021120403281100441c107000041102c2d03200c00d40c00704403101e031079141c1d403410802448005002e8071003e843d111030541d00032040c440d07014818071261340100f100307c6601340264034101029020f50101100c544c0e804001007080000d20850350241001c20b200c01081d0340da645050010342d8010160107002d40c00500c030b08030019101007404400416017121050051001c10320b4003201c0c81076a40002c134031981034004841d1042c1550b00c041020790050300180080d0042d07203080e0301488601981c05113035101d03c0a00664040c0840c50382524a8221a0041c42c0030615540b44440c1d405154080c01e4220f40052140d1401424050240043c00d10f0540455090080a008420440d454041c1e401744043c80c140411507182104000d51006101600c51400141071507900d0f10f5100d1240c009900644010801c2828080180c0d4820340711a8044000c882c100a84420b900305910302601462071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 774188219 1250 774186969 774186971
    0x315010608040602162a05030a0b0c09060a020708160303090312110f030a09050d02010f08090a0c06050a031409070b070f050109030905090a0e0607030209130c091e05090406 76
    0x1003010702c00940c0488400701e014007081d16009200303142c1142c101b105840804044100203410044040c507980229044a500074010100d500c0c6a0300e1702e492554002e017442c0d055001c20040b9414039180c98025040040654002c0e0130b80c54030381290f840c280303003008145040240d004101400000d0f0031900110540385c101054a900b81d000d03040c00e441d42c8054027401031082c400d50071030040f000c000000170301c1c4a4000340d60301580c442da5003091005502104030001d011900354005130700708500c00d941d9543d0144060007200c1440115840f00c4c56010000c0d0048000100000b9401ca41c40340c150040380b02c901c030b078080702d081e69280c09407903140c030380e44c540c0194400800c000403414140301101003c444915040b00003009001544d24010300805414468117000301c01b08000034104400501c140c1c0420440380d4050706a654031880210000e501090f00240d10111400705005104c4c0741e40300303e6081c4c0032030782c480540d81360401944031030b407101d1101300301100381051300240144d8480d8003c294109502a034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 774189469 1250 774188219 774188221
    0x2061b0705030904050423030c0c010e031504050d080c16120c14070e07050f191718060a0e0307020d06020c0f010209010810150e0a2607050315010608 66
    0x9807850652041c4141c29a006051074240818001340440c100c61054a0301030811200b88003d031051b88a02400c0040240d13500a414101283d500801c008196000010160360701c540d01201c00ccc00601038162025101a805840741c0f2804a40061503940c0140c0302d0649282462050410202d256800000c0103200840300e401e620701c00b9001d440c0000c0306591040b003612051405c40c28085c4d170b5100d5403280a1401e4140408115034500550489110314003070410549804c4035409525030261101d1031200800000b000507002110400c01c056000c1c0500d41c211001038000e01c54a24500300e4003070541c503c3c1c10300c1c0003011190306100208541100d80c0c144e5001d080c5042c981001d07802801011000c000b10300520034100c180c0035066008009240003601e40103456115440412410916070240140b00030304401034001840c0101c41c615102d000040c4605070003600c0300320300358010300700d180714400104030002030040c560f0702413010401a04e01a00109a00e5400c1d40c03c070110f10300306215103000d000441c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 774190719 1250 774189469 774189473
    0x90112141006030f060b040209180601090e041a100510110712030203042d0b31050918031c090204021c1506140a0c050615030d02061b07 60
    0x12000ca41c41c2200e20104204082d9030b42440b1040c0c0d52207a0302250070900e01402400e8601e480e10030350309681009454503411090f0356501d00c0707858001804031410311805181c00140c24401d0385078030348203520a000480e1101025001c0440d00341020b03002e82c84500c1d6403081407000b40c0b135050100503250501d01e4580c1d03074401d66501c22400c0490035000310703c02000805003102896000801442125461483d100701c90005890603516a1082582121030301ca02d02400c020103429040a03001c05190484501000707003400500201e44201c0000b0b070300c0e001c0301005040180303140c003560140e4000e040d1050051440505a4915107a2003141a02007102c5d0328050407103041a425841641e41ca80d0191003155070f400908112200502442a011401e504100b030710b085481540d0309040890b69144c442e9841110418250020340c2c226101080c02c00043d0001d040204404009840c092000300c8040241901240245400d02e2600d41034901554400828040003820301101aa41600d40c20b0205803141024 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 774191969 1250 774190719 774190723
    0xc03051b090a0e070f0f050901020307080a030f06090501091410030b04080d0905060a0b010e0a0b09040b060d050f0c13140409051b01020f28050703170d0b09011214 72
    0x5401c0601028400d10070400129085020140006110789500388030019405040b5914423500b0a641d0050300b09221000c0040c100f50050300c1d80300c8141c1000f01d00b1041110905080b00d1f401c2d808071116503151001000034071482e202d60540f03c00c0d80c02010300b0a1500d80070340320a1700c40c10311005040c82581c8001a0901c075000d0190b403404001404107020f264070504000395240705c26284e500c0420b140940503100c0e58040c9100d03501c81c0002030140d40110389080d8041d482c171b41000307009680150b03c58490b03521036a02c02c0e00034101c1d100070860014807402c2c111109511a08014481543d0440c200243e400708808100603508580d0086111203a0082041c0410007426000100400038814400620702c03011200c2110042c015081e8200c0321480001c4441d0341e42e80c90a5065250360705007900150310054200c030316403881280207034200e8484039941d41e16030008607916580907200d070328045a40c0c8002d40e401c2c0039070849884211403041c0994141510229180d40502c2d00500c000203501001d0000642 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 774193219 1250 774191969 774191989
    0x150b0d35221e0f0f0509180c030111120604050c03040f08070212010c110303010f060509061e130515030a0b010915110f06010b0313060923010c03051b09 67
    0x660480302007010a90070342e04500d4a25401420040c10a1590224081c1000c0002c44215400280500400c1d19540346c401c0040319590300c0b1010342d0103813484c2551142c80c240290810454095241d9070303900a0f12408078180c20700601451b00ca9810b100c2408001d038405800c0d240c003d07401110300e69903c505490080c2040c45010002904a28001d00c410103410041d0b0005880605940b04e0079100b0000c103002c20784070b04c003d005035132040902001c2405410311500c082c03e400000503114602d8690f4a4425400749042850b4020815000003a41c5032400c1031081108018501135600500c419078562044215010080540c10b042d035175140b0a0588d0f03032182a040b801050210031030801a025200020003640c0d8182c00400140308090f000200f940340061140c0c100e8181400c086e04586070500400480c02c241e100641e1600d882d002100003051444507100d00e030487c103007100d8803034518000e40582901d00103445007051500e41401c01c070500100010b104260940713005010380d290038000020341c1000e6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 774194469 1250 774193219 774193229
    0x7140a06051003141f09080f030f061f0203090402030a020d0603120f110a0206031906080a1205070c05010e12070e0702060121150b0d3522 61
    0x8280000d008100d402c410041003624020340d011080303802c0448036540d81c1c8990711060503101c00141444030102c41268003219805106091440c50310100c0000c00901e50010307242e40f9407030000c072414032805144c50f0306600552012661090520050004083e40f60301860000900032a00003000032180c6285504841d650341e0000420000d0317640724103200401c020070106a41c0402c0c3c04080989c200c5018440700b00d40d0030a14002001140c01c0c81c2d00340511500080e001017100303525002080d60441d50f90140b074014005102c0244903209003400c1c40f919030903076481c0c50401c0c01380070041d200110781a0842c18082c0c170f030213081c94030b4039029020208000800e210040c00041c0191280840c6006100c124180035140f80d900300ca00d581d0701c8600b0440d250b060200300103040f41c20454000001042c1039140030711070310400327070000b01082c00c04049020610060310403540c2c1085100c1d05d96402084095845007105103003400303c01c040e5022440000341c816240c40c4624007114246554513038500101c1e40000d01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 774195719 1250 774194469 774194471
    0x1030c1a04150f020c01051303080903010207021305250215041515050f090c0a0309030306170a060608060106140f3001080604150b010c021009030b0c070807140a06 72
    0x4002e000c0c00034a84400011100018026070485a11a6110b8410380c1d001009030310b01d0b90078807451542c40e01d07000c4e4000c250701d0342c25540900c50440544e64203d00188825103424010440c0d05c2d0a800c80c003d02c13600300503004600e480100710b01241c29030005142a603140c051540842079100c0742448905162120260b1031a90b060a840300c0e6000140001c9000310b031400d0b95000c1c0b28072041c1c41004bc00c000100c81051900109200400310580310b41c000c403540d58068180001c4803620b4103031007080141d01c80d11585541e4403d407010360411105100700c1c0d00401824028240c19410110020200c5c0840e400b18103c1c0344000c10190460682c0100312008a4458400240c0c01500e1a6500c000c2420618042ca41d07060403000000301e0b5400464028400c0d54805940b41611742526000002002c1800e0000d04201e00301c0c2012006840740c440070040c500f0749444002c180c0786180b602050750200101052580481400450006060706081d140016406032120084a0400c01868541072843c0c0000d03190b6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 774196969 1250 774195719 774195749
    0x3040b151906030b120f12210703050613060806010b0a051b060103032307020402071a090102190306080601060c2103021905070c1a09040905010501050f0901030c1a04 73
    0x90f0781681c031030681c4090585454110815400f035181d101d00f5070011255040d0040c50541289000400081c60408441503501d012044040040785071100304580c1c010200b030f6510140f06082c03420104c04803521b80610014010715080c542d070251102c8041c8030301c00f101180481c0d40410207018406807034004c51510030741c4903030891760324030300381e40e160207100582c0424007002c02e180000303440c9805a0030a10304d081645240000660a0000940c000001541c110740300038884404000c4054125010f40c0080c1c002607284c2c0c003030010b4085502442d196080600d841c0c840e041000300300108240b0f045071902c0c102035140d0a11410603000035840f5a401903490524624850b9020390103030301138a142c00096200302c0c120120103006803414450588042c007000031201040100b040200080c00008042e160100e0030401d2901c041010f503010b03060201e98903515403006202c00c4c00e1010110301043e2040352101e02c254519114802080d00070302545800c0070400c0144d8042103c0c84086600401d80301982c1c030301d2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 774198219 1250 774196969 774196979
    0x3020a051c05011d0c04051e10170a180206030406021209060103150608030319020d0f0504050c030105273d0615051e040f091103040b1519 61
    0x309000d0040e1040d01301e04015500c0c200700201d10162084071a55101460641000200030742c0300005021403800000c220940105502c40c106009a40303181901d0300300c40c0024145e0007a500210091860111600d0158507940c2d0100c401d01400b419034050341d4184d90b135102d5023005800703403040070b0040811110035000d00c45411303000281641200d00440d101a41a50a180c00c070095600500c1010007a030f0080c00800e12200355510501860309084400503c1c1100804548080c1c9070ba458210f80d945540e4410002030190030711031415600b800b10700270000c40c07a0080b02d14a50300c80d2103100051341c2074080d0118042400c100022040000621281107500c1c0006d42c0300101e04803115420354504100300303400c40c44882d4a00601054403807950501011200280d400c40711504400c1d810b031741000318002800c0001d80f00c40b000340040c040703d8481401c0b40c0c5c1007601c1070058500070070803540e11401c01c00c1000b0208101103142900050b0f52609010312440c10400682d2880401c0a4a816000388060001d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 774199469 1250 774198219 774198221
    0xc0d050907090c051314120607050c1b0a0b250f1e020a0510020316030e0306070206100b0711102a020d030302032203080709051e0103020a051c 63
    0x40ba111050244102c8510883c00c40302030141e13444155403092014818001c11840e03440c01e900f20316000d864103100c0c6008030503c40ca090380950f07484020070000148050342c4002071000c258103400441515a240c0e07058800b1440391420f41c4250980300380301060400c100685800c42c21280144089d01400c150f155080000314804804022200d88c40b00c116200c0d5845207144d2001401e9400400010056182005110000600c021a0f40442c0400c10138903540348004262000c2060180c6c3e0342065080500003031501e0088090301d8001954080400c100001d81141003010694040b001180d4540c0300034900190700c00000380e9500c0d4402c0f01142100d043ea648860702000c50700ba80c030300c4459141c25120224018203a81031001c0e401042941140780031074000d800131a0056001848040e0885800d00d204094400d040c0e01100083d040c0d900b40f1200c590702c0940c2c0005400e08803900300d01d0302100e0034003a4003001c400302c607103046c0341d0042500c085150003801030303622007001d00f0075401da03900407400110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 774200719 1250 774199469 774199483
    0xc05070b09070501080934050a1715011802090604090513060c0c0515100506120a0605151e040504020d091a0403090311030a060204081b0105090109050103050c0d0509 73
    0x180c0001c00305c03c0040c43c1400d001422003900c0440c5207101c40005d9803107641042d001c000020650070f10107030b5400092262030b02d1030300c0d000401240301d4400c07910301035004040c201526944516a01000d1030300500204940410042d1000c41d40040140d40d20a082d010945c14002c039400178882c107207403000b048810507064900114a600c106420002342e172000909031342c892a040c0003e0041d51020151802c49914501e025400c1a508126890201c2c1c0d100c00180c4540e0100140320412100041400391843d0140980c101404046400d0b80381d031950b04840d807103180070301002424168503c42000d40581410380441e4050700d005801075645d80510805217010b0101306408035a44007200c0c42e0007003c1410b0751015406598580d071071104840c0303103407141415044d9510385103626000310020100003880c00c5c8021300082003c0c10240460f41c56807a000c0a2030030000c240c01e418400100a19200d60388c1c04100f0742c00743c0d00309003030002e0103484000c1100c105000d092440001725241a0030300c41d20b0040041d0320 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 774201969 1250 774200719 774200729
    0x12030402240318010c0e0402070203010b031207060606031b2607051c0606321201030b130201050406051b0102130810060f05090a090f031d0909100c05070b0907 70
    0x70314540c10380c80380c40c4c01c0325080101c010001e0880e928494040c585500201007070f034001000803a2030001080040d0400304038041070240c00d072001400e5410020f0710300a05008041600f0100044d81420b026009890340004d943d10801100d10a414201107045804510303241c0d200070380550924207a00c0c050f0950f4448416050381e01d410a10010b41811300b07020307038030175201caa95982803407a509603519404076500c42815400d0440d44540300e50100600409440c003490001c01c0c0c505e00c1c1d455410042c0a0201c00785c0310701d0b4081042c0307041c1c3c009030340c120048404840443c6040c90351840740c031920401c0301203140007286440d4000501d039080549102003040560b200300c02901d5031000030300481001c440c1203110380c80750684090b20410840c94420003442d03019070004004502e061a80da41c0c0c260f18894040218042032041080d166000d0100340700081111050740e00c8040b6040c1100034940d00c2240560a21081d9101d189001201d48100141c1c0d140903071182040405040400030143c0314501e80c028 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 774203219 1250 774201969 774201991
    0xe010e1c030f02040f06030b06070f1b0506030402030a0809010c080d061508010f0306020a1403040f050606040c09030620040905011e03082205030f2a03120304022403 73
    0x82d4054035201e108a8085802c681c0c0e1424469241481c280d01412550840c0c9510800034032185002c580490860410a48a100c0316180400c0c000002c0700a40000d070001c40c01204244100401610005960203010303410800b03d5844040c000d00483d640c1a00c980d000300350305404141e030a414161600243c0960302074450384072106000c428210707400c14091050140503003804400b040805c0c4190300400d1341c1c101c2031030f000c0507001040200c04a04c0e4401c0d501114003140c100e00745018400d013406090b0b04818103c2e400d000580c08203000405403aa42c1c0805080140d07180032400f11034465595004da034040c1c80d81da81ea201c40c0e0743d00300d80004190900c50000c01d003542c8807141e504d4000ca4015142540c0d4005401410024801c1240c0d40c0c3c0d50741d14071a94141c071b062407004142a542005903504a0340c0d0180141009102d01084440c010782c0b1003910030081024280000b51998082241c0d003242090040c4180c4a03aa07500000d08200001044020080c1d100350752400015030280056202c3ea140c800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 774204469 1250 774203219 774203231
    0x2707030506090403051305150d061a0715090f050604050106060206040c1e0915050f0d170a0509061b0c03070803180105120c090111030f030402040e010e1c03 69
    0x50aa040d5441100c026500202d08000940000c0c01100606070030105901c1581c1d8641d00e680100d43c4000c500e41b2602045040460381c500c440c1b4046c00b0380006807408042207031051030b082405881c0c5000317072000200314035400440c20f0445540760b440a90400e410075403102c003540075070070090f8541d60155410740756542031590200c0c1c484c1c00014030501a640c00072041088074a050307840381c1c041c0c0340803500c0e61b110242c82200140c0301100e8002c048580210041c1459100d15210400a5024103d4407050040054140b00c001107200c01081c070110400c011074181d43c0b02c4d08558112464840c80d12180e512000118003020401100100062942c6041046464071030b69401015641d229511030a84103600400140f42c20852910400b103640a041c1003850528000c01c0c07034442800e4007141c00c08903121010840001d15a403100080740c01c00d40710300c0038515001c61681903254a110081021780120f4a0f039050202c5103000354041032801144006450304820710420001c60003411178603410000c0d003400d07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 774205719 1250 774204469 774204481
    0x60902030706090501080f071106181615050309070b0f0405100203070c170307020406031406240d080d0504060b1002030a020a0210031d060103021903020315060a0527 73
    0x10045401d4130300507142d04406585031800801c0310003000300010f08000a01d0603440c500d00f0100701c001d0003611084404204810800e80c10381c0382c03041041c6503803240000704c041040340c240c0c6055050065200c40c41c2543d60395403a02203d903c6c0038015030140010381c00002d40e5010340c0c00321074058010b5a408651104407081544e004903928040c408000d016003182400030807400000400c60141c5d03030079030001d40c0e0404c40c040d0001022075146600655000d860720280c695001814086c1c0ca078032600e01c00002c03540721811040c04050002d081c1c0c40c02d01030115072401d1801d2102d25429180c6440d0381150074004c510b000e140c4038000c0d0aa07005031a0290380b100f060385049500100c151350655800d9401840808600d408201501400b2807092080c160341e03440401c4c2c0d2245203401c0c00941c00050b0b000341440c1d403452041c0014550004058404174001030404c0c001030381c1c0402d10304088411011031400c10341340d08001550359402c0d82e1040354400034030300310030a841e910400121078024510001001c0e031b0342c42c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 774206969 1250 774205719 774205727
    0x152a0d111c060e010b0904090501060503032d07150c1416020a09050613021c0612030206090303011a07140d120b040b0f06030703060f0e0105120705010504230d060902030706 76
    0x17030007004100e18080c04029800c0c2029800040070500420020540555800c0802e0959111142a0322015442c00d180d00c00403030001843d41c20307110300d07184481c41c10085481e4208600501c2c0d01c01c05556403164401c4181610454070500e00c4c590f41c200301655100403205400c2c120310000812400340b042054001248a031510031588180da024012205041d80c8040010003940711034540040c94001d60050070703e00440340b1500000d01005040d000c1d0b0a0050300b00030b490b104004282c41d195038030400041c00014400d10245000d0229030b0101501c0d00000d2070660078102c034141020ba0a032203241c000d503803a254800c0340900150f580311410405410321109101c1a2864410800c1c0c0140c3c003486d0942060412100941d0b11810501e0001030041e02c8044030044075000d07034010790740300320004014030081c40c01d0403a040401c0300202c0140420bc1c035090020300180a18840c00480700d0680c230310008841144001401880e1001f00700c0400001703640342c150014030604c0300a038083c0c819480081582801 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 774208219 1250 774206969 774206971
    0x3141303020c13060914011a0304053a031b050c03090f12070308031b0304030801210507080601152a140d02152a0d111c060e 55
    0x50303014100b40e03005081400202010701541c10712050b0388034000180e4a00900c104e4500d0180f00c0350b941d601d035140c030340d030001c00e884c100f080d200b4040e03410424880003d500041000701c0e0f2240040c45400c00c07406140b540c6202c25007403800b0354034aa4448100919661591100c5044143d00d02100e0790384e070512204807041e00600c09002a10741c420401c4481c5c500c2c0032030000d04010070082c10140461000317862981402845d40c000c8800c980040140a085602c0840d8407010001c0c40b40010b0543c42e10b40c42c02032131400188560120442004003000440c02c88102c01412650800201d5180c26503a205641e940c281c241305d4000c00c450410404c18115105944150016140380708584005407006a50b1411880c0944c00b01c0301c101068002001402e030a0004a05001d480c3e000340c81c54280304110500201d0004100c0f01118030615600b44869400d180c810b40e00313848884800340c541c100e002d0000b0061850240804003d50080351212860341ca08800c0d5120500c91101480b0b940d50b507223006d2100d000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 774209469 1250 774208219 774208223
    0x20a0206040905060f0a0303030b030c060c0607030b03030d020a090e010b0301180b13061202010311160305210108031c020f1b011104090e011a011707140406031413 72
    0x8820842000814403c3e00810781040e401401c08901010803400100d00070640d90003100480d44540311082c1e1454244200c4020a4003554061714051000f150b00d0784580d40105404281580d030070366400030b82c07403c0090f1040001004c20455031036000d140007900c0c850051040f00c442410803800803500001c4030050f01d0407121405814181614038103d0391002d0140c501c8856040340702c024901404050a000da0402042c1d109aa020755440038000101542c0d9500000c0c1c10009081106031000e11941d4030140400d1b8061600f540c60b0303440d02001424406c134035914008002c06050001c2040040400200440b1a00b40c034100f0341034a0000c211410b07401808407030a07952509010450310b4190714502c3c1d50304200f620380001040f0101541078030b21a00207030041180c03940d84401e904051342003441065407480304a16481c09060908000030300c680c08030389503000000c0c120008070b40c2c0c0b140110002c400ca2644412110713240e0707844c1c90000700142140041200c00e20a00404a100d604a60510726100b40d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 774210719 1250 774209469 774209479
    0x204020f0c0f010c1b0318140103201801050c3a230c0105090616020a11010c020604030b0a090303060603050603061807050a03060c0801080d0e040911040f0516020a02 73
    0xe211242c00c4174603003a004420f40c00d0044100c152059482d04070905e902030501c203c00c0c18201c0c0e01000c001401ca90200e440b50300d01c0c41c20740c1e40310001100d8020070344400c80c01d03102c14150b41a40400040322a0300030316003038882602c00c0d011100c0108030414000714421843d160600303c007005500034590303008052042040419007d0398070b20401d1080307003941d0040403078101d131691070400b1020302d00782101c50440c1c0c00d01042c3c01c110b00780411a01070111403d20002d1620041a01001e2350712404003070340c0440d0005050240365400c1030115140c09096030011038004074035290900d81420518054035950000b2000203280a60100e01c10340030748252801080080c1c0102029503520110603030008016100e0000e91150001c001025640c420381d03000514424280400d10301203040c002307400d552060700245156080300103c04407a55002d0000703a00e00310211030104100202e07003040f00c41c0400b0b40842c69002410443c1c0c4072036244194102602a0207400b8020107a0742d0344c0d00041303840b40786201000350b1007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 774211969 1250 774210719 774210737
    0x1050415050a0c0f030c210917120c1b06031302010e06091e030d050307050304111305240a0803120a0615020a0c0801051b0310030204020f0c0f010c 65
    0x900c64009001c9002050030003115103550fa4071071118044c0d10b064118001070103170b0500d10800100244096402c00c807020368440e0817440700310251000c00786c3d000300355002071820800050840f081040000c078404c50094580e80b500800c0c0803580358803600e0f102d04800d44403c0c04043d0b0300d003056003c69204804c0703103448074101102e50b40111b030040034544025521600500c004030742c598660000102c026140610078640d0307042c01040c1410140d910310041300b842000d00c208031990750040100d80d4096840100780d480040d100001418002c4104030300c103e46031614080103d080003252401400c40b44480c200c02c40755540904111303499080703000700141034009002c0c03e41c41540c208001908a2155040450090b88400304d0b000e00740b0750503d5460059003d13240c00418011599099409080c4440023480140360088070150b07130602107540107080032800000100f13845010780b00c1c6d40145a009000717564803440c0030a42c000d15001001e05007018003031843c82001d0302d01c05200e080280220b540342c01c80e070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 774213219 1250 774211969 774212009
    0xa050906030a150f090f0216030f02030f12011e180f020c03181201110702100e030717070807030b1305071d070806091018021b0a11010504 61
    0x3036900080c0410400c036465000300300300300d442c25040c08007501000b56240c0455107080e440b0020b030b8010350310420086104100450709507006490b20284560903041041c01d06841810403440c500c110107418402d00004251a6803034070703080542c103040380d80020107005051404136604000014900c5804c001c0b00c05149104030609076504070f1011601021001410140e003903e41c00c3c150f9014000800c071601c10392148415524010401c0c051111000c1d0081002201c020303001d5813640b10b12003011744600b40b0403095004040c4100c40001c51a58090140d40c0c03926582c200d0880f86140c2108021b07658058090040f5041d040062814101c036044114440c890700d40012840d0340114260043e1030600a4007800318100e040c0c3d940b1009804180c00c201d220a14040300000c1c401000900700301d203e1030880d030038460400f001540d84800d880390300640e6803003031044d145420002d1140040000000381e090703c039081c1940c0c0c0801d00d00102802504c0d225280b620074001100c40c2d20440c0140380b00440d64401c042d003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 774214469 1250 774213219 774213229
    0x110d211b030e0a1416121709060903190606140603060d020a05062101090203042004200c010501050102070f0b0a02070f080307020310050705070b0408120f070e0102030a0509 76
    0x220342c80b00d40c8190380180c8803a8035404d4143c07400c2c010300c80c0d1036808102d045541122100820006007000c0b4030402c041d218903985d0104003200c107010000800c20110302c2c0c05a5a44200c1100c101d045c00408550504c001c51b1101101030101400588a55140c8000040c0018907005d16000e01440105a10314680da45010011903052002041e40c104a0b108008500c03900c5e40801092112018203008214107002c0c10003034200d0105810101c0e403140180144400a500c2068800400703014098540307500e01803070702090040c02c82e08030034089106101d200e68291011000200902c40c0943d0080c0075580c0c0740c100681e40ca0300c3c14841c1110054440c1010040c54840001401c0171400500c142d9a07095a210906005219180c10405150700001501021858104583c034a854040034062185140242001d0654011444081c00c183c40b400001400c01c00b19a044808600d0120b8020315242001660f4205404045a1442c0800c29003c6140055800081a00d00000c00b41d9a814548507002c82440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 774215719 1250 774214469 774214481
    0x60a150c08040b0a02030d060602070506040905060301140a0e0c03010c020c0d0c0801020304080d0f0903080c0f04120804050108010e060a0b1b0703080c1209150703110d211b03 77
    0x2603041c4909010100c0ea0380c2d01c890080900c3c0d080ca600864591010010080850f0b03502d500c00380a661042c40200f08a44a400c245d80440b0005000007415a8850000c01c1c00740041846144081c1010000c0011025813540f040031900c01c401f040760f00b4018464141070803105450340010240e440708070100c0040c80c0c02d08408100d51b10070704041406a079910825030aa820585e400c0302c180c0c1010442a04841c2d06100d0280014490403080c0b040d0601d645002d0b10b4804080c00d0003589210000720004620a80c4c421107006210b09816080c004c01a82040e4110b40c00c10300605000480c504c0000980402040760701d4020310b0000e00c01f0002d5888c0c00c200f078409600c41210950301103044452090802014401140190f00403400b00b0b0340e600114107513a042440e101403a0595020034840141140c5a0640591404111038121555000709003010307950310a84030b80801c92445608500241c55900100b2100120340c41007030002901c090380d0522055807080307100d40c000c0e14441031025400c2ca111b0b4000c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 774216969 1250 774215719 774215723
    0x1207090b04111801170103030c0204050f060d080a0309050303150a080303010312030207061b03091230090b1014090c2215031e1b181205060609060a150c 67
    0x588101d00f17108560b41e0010320980c41600403402d405103190940c00c0c14011582c0c001c0745010021881d10b42100028031054a03014080c107426404220402a00e000c0c1e0f10400642da004400c69450b8030385003052014004080300c0e2240502111000003a0901c0000140e0b4182c2c0e5010b052030341001d2420b24114020340000744181c1750b003500c80700181280102007010700e00031000366a010030407442c1800c01111350440f100b030303000c20002c40003010765807a00c9070074050341a40d54000494003003c50b0003545030050440008040c14103184803003480a1503c1c09003004003181c50744040d5910800d40c040411201600481d08040701c844100034115810b22100050040e0b011201d8440b03960070f4440c65111140c003102201c1e83d003c25542d4020090120f01140207254001d000d4209001d420700e0000040c00c0001c00d002402c0521070b05981e000b125241003054140609040380c88241c0d400f4803418100d5480d10f0541e00c1c20b00400082011800c54201790036100192854044803901c6d000c104c00044480d45110001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 774218219 1250 774216969 774216977
    0x109090215040305033105041d030f070c081b12150c041a04061e09080d170f0103120c020d05030a030e1608060a05151207090b04111801 60
    0x1888644080c610082c002035401135008640351640c034400b0001006028101501c6040c04c84002c45800c20801440015244e081d5800709a08000e0881c2c560001004070000c14039020115041d5100c1030a10b000c0c1080d1030290144404140d81e42d120b05440308295404e06010882d0403920025038203104418055101d44102281d204215212482d081c040050300c1c0944020b0000504000007400d0390709012964002552840c43c26151510251440301a50007906500e40c0c0041c880744554010030b240f80003840008256511001100d00080c4200c4000b42141241ca00b45404100006101d5290314143ca41c405002d0200c0340f0400030540c0d520380d08200803030744400d16690040000d0000d2011707010254840d01c02041503d08400c5103428500428480c035041d41d0032328000c0140c0c860024405400c108000d40000b02e588607600b4140c03074003041828181e00108a10b0100c03100d8003001030000d0445220500c00c0210318841170420096801d88e640040090070140140d203400310041010000040301410 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 774219469 1250 774218219 774218239
    0x501030209030a050a1412030c090103180803040605010f060c050d05030c04030c03051c02060408030a110403020d0308092503120309020d08030a0c090602060f0601181403011b050301090902 83
    0x1032142d1078a45d0700d110854140c1440c010400c00010100700d0410f42e1000400043e0940c50200c0031207000d4024080507904042c0c440c410301e2441c0412295000700f464101c0000c2d907807440c1034203254000e41800c1c0b25200311100318110002c0e8a9100c2e001038522580e01c0400741030303c02d030100021207080d00f0140130790307619000410000001880403038555000351b10620151505810800c680c950b900d00704000c0c901990002010000000d0200080782e03445400310350f00158000602a4400b018040d58000a42041c2d40c0382d1148241600704c01490310400700c5004a5041c1c2048120900100b40d00090f01d80d07204a800700c1c00e10002d1365520f1110016145440d0000d0b2400050f00003840e8107581c004103980d01000001840000601386c09880344194103402c141c054540f9100e802075450400801c0c1545040400003c107000740c0c49030000d0308110303040d10b0201e003049440b01d60200c3d040d81c0c00800d40b880380d880c0c0148a6040c60010000340e082e00019102e0b241035a1801c00c140c40a4210020120703032003c1d070343d4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 774220719 1250 774219469 774219473
    0x705040b04030302070312080f04062a0201050411150a1103070f080403120903111002010f051521070b0c0a080316171005040e010603021f090b0c03040501030209030a 73
    0x180c00210f01990052001c1d600c3c0d030400d0350486000103c15000c104010007049031075800b040041e60042e5201c4070000b0a101141e680a0764684074050241180382140380c024080e0354150071181c06240104200000c1c420490200002c21400c007003821520382d4240b0605c2c4000d40074035460080041c0da14180d038900610307540e4029921680c5d0300e0032540b51401217414414080c0d44c0a5039002031400e03040000200e4216121100900f8030700028a10851552030015050742c0b00b034003c0e420f410b0000c041031255084c109100c040280300c1c2c0f075442e40140120341d408014107a1188041d80305441e680050030b403040c1003c0755101180d00a0035591709078440d802c41d81c800641d10710008d511545606001002c08840710030001d04440408681d4450304003000d0602c10540c4115140000310740046500003503103076031154164050f103c83c1c1d2019600c41181c55050f1a251030719031b4040010002555040e080c04d40340c4401031200d0080380b441d0281d50740300780018040c0794025801014007440003411191920b20030303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 774221969 1250 774220719 774220739
    0xf012303041214040f0909110405090f010f02071101080c0c0f100608030702090609100302030105010b07020f0117060f0604031506291e160501140a0e0a0209070504 72
    0xd9070704482900340b8810a02050f58051a124005640d9840003403405140802d0440c1c03591440c000c6e60a410396811070242080a094104420b00f140a04203210a00c0c0400810740c807402a6100305c26035501300000c4001c001d81520803249983c0d406940c2d03919a108110046428120050400c80055800c01154a04002c208200740d0141101c0d0001c2c0344024440c5803841c1654041c1e805054260b00a000020059440240581e40070100341c420076110b54803900c3c1909116041e600c069015480e0100120321b0006410044c840035009596011b02101c0680044550030418040b1135400252180456040e01d01021111510003001300814281a101e40310003c2109002c0c000103107850307844504020901b6071101c581c8081c0c80c4103c035081c0c010052042c000f694400d54804c00304c503010585500045500400542c0c03e400d5000034a510000c41c1840e0450080c0f8400c0301d40d04000c00807000040c40340c041c0340035049000742458040c05e01000d0a500f480440c0d140941440d007403090a000100d019615 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 774223219 1250 774221969 774221971
    0x306020c0c15130e011508071b0803040506100806010b030c0d0615020c03071a0c010204031e0c050a03020d060905150709051509010203030610021908090306090a020f012303 76
    0x8500c0e9490faa800c0402c105000001c0c00b90310442d0061115001088207001c84a0b8000b04001d403030400c950345603121141201c10807040000d44c50000b844140540a200751240a5482603100300111703902034030392400d8150401a28130500100358040b0005000d030b82c80100c0035582284804481030705011180c0940000e6070030700d030400700142e0b0a07148800c00e15581000320701c04803041a8040e02c00300d41069024000c01005508003000740f000010701032110344096044600440c0c211140f0342800e038058000101c0c3c0c0c1d01444054862511488002c500c600e41040c42c00c08a83d402802440c0c407000960b16103000e0440711206070384a010740400b2100c9401440c0c0103610030100d40d43d40e04a4182000204000900f00c03190042410f85c060103107620598000080369000242205c0e2520000741414040b80303400000c1462500250740c802c0e1040412458901820100000701c095500076660440c07119580c0c5002c03030000c0c0d408814502e410388a54000d405103500c50220212050842e100c140c0540e6840d40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 774224469 1250 774223219 774223249
    0xf03120b1806010e0d08190507020409210906050304030c0f0b040623090a3009031109040f0b090313081006060819050711010c0e01090914010306020c0c 67
    0xa50102004a070f0340e8410707103045440030211003841070424203445483d079038002c1c05814620b801c158004509414000e01c1910328840d40180140019180c80c500034080c0c0c500d486c80340e400725640e95100912039000300c0030901a6502c0d40e64141c2941c2c2c681d181113aa040b181070b4150baa200b054540707200803945501760b051155001c1d800c0440d03802584080c050446403e103002500c800101c20900080c04004148105101c1e001400010307000c40e0380c42602d40000014100d04482c000d501c4c1c2d42e1282079003056401007180d0203681c100c03116062000c1404944d0100711030050031036121041800000d0418000b40e90490b200904036402c01300030350b1000c0300301c1501d50845c0f039080c0e00c0141e06030b0494041d4098100680107600d000340181c01c0006034003a02c00050301c001e010064641d03000503462032003841c40c1210000450002c0c41108401e9801800301c104a2a2150024000f01004035080c081400742800309062a55a940c04e030380b941c7c0b1504000c2d0400280c990141c00b60420000b2503590b01c0c0b0603444014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 774225719 1250 774224469 774224509
    0xf0c010e061b04030803130317090115050103051e070509060706090212070303080c0705010212070c0302010617100e10051e0901050103030509011107030203030409020406110a0f03120b 81
    0x81070001c2d03030303002041c10766181c02001d1004020610010b0041d03015260483d03c141c00351003040c4102d141c140c0b04409103002c40120740e42c1000800120941c150010751241d0300d0002c0030003507142c030b0b03100450548501f201c400b41d040d80c1502501d0170b998840341f00c1d198403402a01d0b205080c15403040010380c2541c440481078501d651900f00300c000307611b003c1c000d541803030040344014044680340d50307009042190010500817400354041808424400c003901107401e10310014402e031082e031a00130700203400050030600540056182c0307403020030f096030702c150030000110352000200740d02d610b0340e5017201c00b624000340c020380c16008154680741203c10600555000315514401c10840c2c0b41011000924450000c0103a00b640c0e041c10010000b0039001011500b400c0c40030319043c074002c0070980401385040781507880290148000200052080700c41d038060000d40b8001d0780e807042c425013034950940d56048023120144c94802c4c411104000070f4050760075962110102d1f0400704501c800c0300c000070590f1041a0f04a0344c14 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 774226969 1250 774225719 774225721
    0x13030215100e090705010e090a0f0204030c14040c080612031c0617010b0a030f021f030c12060b041e08011a0f01390f0507032310020f0c010e06 63
    0x3681500b84940d0340800240020904140b405000a000701e0240030346500858014020031006a001e821802c820024200c0541d0745a6070b914101c072801c01c503407284448908051003420214a460b010308003000c107035560780d0071450322644100f1503900e20501070a11944001c000800c1c0c0300440307086040003401d00c8200014241d1070030b62042a0f0720701c0001e60b4a4147d24102154580d07036220b09134007043e2900400c001c12144c0052021401024001e6400803503046081c1e050000c165158010078007150351981c884003085001c80004040c0c1d005405400c0303151700248000d0000c0706d440b04403449007a6004d4580c4645582d5403c80c20b08449070f10070101c1c020307103624060510b9800c12034900c1a402200f86070a088425a9906000406000c10852a401c00c40c100e5503410102c010307940389104a403c805410100d040398580165140400e01c01140c404171245480da281c40c40c80d84034403007005121809045e00040d0800300314002e510400102c0c0d21108240300810000f80c0912899000c1807080e4010001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 774228219 1250 774226969 774226979
    0x50109060816031e0c0315091403090f06030604090f030e150a08070c1103030409050a0501080309060d090c0308030c0c07081603020d1e050607090b0901081303021510 73
    0x8080c040401103440c01003039281000042c4c401c007400000410103030501528401240341c0300b00d034005698800b0b00030b00900040117240c8003940d40000140ca110b9420030034500c520515540d241e0003541460344c0c0c401980d9000f1503a03805c2620040d035004600500009116070381e0b60300d5039240e80000c00d050b80018418000c2c9241424400d141c40a40b0018849140c1001d604801c010002103004140b10100710001500740108501e034402c034114800c00038144e03511151914000001400c08a810581103800c11000242106011044400182c8081d0a007440c3c008a010950051310540350126442c0c00142e1000000c0b07a0010040d502500040140c0340c0e5078140c00d0070b16440c3c910b05030071868540d0000c030807800413070200384e003041d04aa42c1991200c0841200d818200041e40010000d89901c070360325a80c103810000013003002c51186005807034951050b80c491320400c21a00900d55154041090070010030f01c0d40f0120b81c62074038050b1113441142c40351003860384d0901544d902641c107608400303480d04092107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 774229469 1250 774228219 774228223
    0x6052209060e150f1510030615020c01021902010c0308190504030302090f0f060301150e04090638040207081e0309010608061608090f0714090f0412050c0309040501090608 75
    0x2e0844444c0c0c80e464002d041c074422405404244140451280c6008404200d03198020740254006040b410142501400e480e00c0c081d407504940b460160040c028035030fa41070680700d444480c2d0034164040c5d541d4015910156005da40000c000b4000f002c483c80490341c0e1861003001e03402034500c654401e135409a01c0d880e20030240300c01090500c2d0301a04c907205c03810410080c1d44522040e2811122007649040b8040c038907800540c0c00c04000d0400c2e40e0014105a00e12052060ba03400c158411940d100c4080842a41c540705803404000203080000c1d002801d41403000c00e03280c65000341241ca805500c680b0f00c0c0c02c61281846940403e41c4007001c91b0081c0210070080591001c1c030644000300301050240c0801d250050030640c3e140501030300c4a01b400090004101141410003206408410704012650515101c1ca522210040b000460611406450700000d0941e0200d464036806a80d11046050a100500340241c409030400b181149252200740000d2078541e9441c040d0300c2c028594a036001492908101c5554 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 774230719 1250 774229469 774229471
    0x80a08091c150b191d1b040303140d1a0307080f0a060c18060809010c0f0c02040902061c0e01050a2a18080105090c0406052209060e15 59
    0xd2085451844140c0c08120319204501d00099a82c00c0022070700341c074030001401c859112034030b401216a059004903074411401618154850482c02005242da11754140410054071105402c03040b0b8800e1104100090007103200000075012000000d080c0b1201b14124402c03281445484034511101c40c8030000c09080500c001000f5000c0300c8050b1010b41303d10b070350496880d12204c500802b000d560f000e072040d4192140b603603c42c1500c0d0100c4a0061a0750b2958018229002035070307004000c0d460078100c440641d00818050900c150240c8401c560392076a502008024101102c09a80040741084101600d60301400d0380c041c11400458005007040300210030f1421114010800104145000003003402c01d16021660120b501440d404240000c01d101c0c000c0391401078510750b0848507200300c0e40104074400d040d0402d034441d91109040701d10f510100020401901c060303109058000e150440d1894000f401c000c0d134580048010400802c01d0400c9070b41da901226401d030b04001076501725032014500042c5180260b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 774231969 1250 774230719 774230749
    0xa05010207050a0311040e030a110606012607020f030307020d090b13150203040b19031a060a050a0c02030f0a0c09020f040608090115031110020318060310080a0809 72
    0x1401e019060201151048903140070282c5000c0340b02c03640c0401551103402500c0316505890660b512880541d9020f02150841c4100d00c1c5c075030040c3d800040040d44162402d6007102003018903c3c01c409100755481c6514032001d40810210300034003103000402d040c100004c40c0142c00310b600508144440150007080d0890680001022041c104882e1400f00c2600c02c5400c1501d600f0701d41c8107402426403400764554440c5078403201c181080407800201010401ca903041d01120162028403501c030201105110408102d854540e20210502880510a1245010b02040505401c0c07041c142c81c060707000a0700d011b44580b048000d81d8040e6844004200001c1007980040031062802d5003001d032004021881c0380920300910701001219800154010381c00d4005101290f0f51240600d0526222304050100c0e070801103c0d1406040440c1000c140d0f60710000894548092815030050021f07140c5080109070351000d0882104500020b00116034464140400c3c3c0504c2d1045c1c1d0529079408030714051000308441441c3c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 774233219 1250 774231969 774231973
    0x20105010e040618050a06060905070e01120c0c0f0503130f120813030218100602030c031e0c1204080c041a040c03020f0f0301080c03010912050a090b0f07020a050102 73
    0x42040340407060800c2c0e00309600800c041542c8000d4000219001e0303074610080c0452064141e25000d00035554000410350307140710070522140e554010f0aa0386030340d42000d9030340062640005100e80100c554424440d201710351a240800c0805c40e2140b070b0006074800025205e940001881035a100029825031000b021460700303100c1c0d0a494945460203d4011041c003811818001a8056869910000341409076a005010901c03501c000705058641c501c0c104e5000300c04c1c004280011a1701c42c00041a16100c100d468001c0d8500070100030321001481c0040c0c005041c4100c280041e07a00380c50140040245840300c0b084054646151100d114544024003c5a500440c9055140e120a02c1d81c0c1c45400000b00c07050b500418942c0b07101c5400c40091060505001000b40040307511914880c1d00c1005504a41044003282c0d50306240b00d04060032a005032000904c42c221a1840304119030040e0081d003138800180c24001100e660741d001d00700e40b0364004001e030f00b4240c2c0000760000071450b11a0403003015213403e01c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 774234469 1250 774233219 774233221
    0xc120712031716020a08031b0d0e0c19030f15020c030a0912150203060111011d120f0301051e040504140f070807061107050d06021e0906090906131406030706020105 72
    0xc0040e444461002c0007908112001001903404040094440c0c81032402c03641481d0b0b00c035103c042540044c0b00350540584140112f01c1c81889528001c1c14607540701da00243c031040041d01d5a81c81800b0648000000c440b409021094403129001c2480500901c00d4513901039540e5148022000302842016009412100c0d68a510107010608001c2680030700d0340740b0200180c0e41c0e125030f00141c80070702e55800c001030b003036081c820300003408a02180038924906040d03045a50180d50342c01000000e00902d0341040a8280a0004100501d0180008000300c0309201104441084810114003601d8048405807000d40c1c01c02d1180e03a040c0e408100c41c600c14034072500a4071001e4100300c413158403412984500c00402c500d48460030705850701480100000c2070020015a004101c81c60803402039086581c40703c1000315201c181515844c403403011110410002003040303241c00c0c0c24900f00001d60304080d00c016000712900039109100d82091064015500940c400e4801d18a4803804040c134001d0a50003100440e41000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 774235719 1250 774234469 774234511
    0x30f060408030a0b0409020909011a030703083a05070f080603061627050109050a080d0503220c050316290c030d050907090504050c1207120317 63
    0x150950381c111443c02d00c081100300d1048000340103450030030006940b1840c040240054000e05620050b45064400c0c4a64604c40c401010903855014601c000f8005c01c0003085443d10b09200303090802c006500b04000000e40900910000e049900f00c0c0d000c44180350358590500c12003503009014031b05503c00b14549240300b85024000300f921803101802910754601046510f201e014000c082040c01c841951250300400c2203050b0000200304410300c43c240c08520491707000f09840c240022164150b8516800410b40300d00c4d80d807002c43d5030343e0005013000d500a4030788001d07031500d10380c3e215009130180c011086141410f0503c2d0400d42040400c42e00200c500e42034140c20020a9503903580790381c08091101c060810b18903030582c00c034400d00c01e1400b80303c19404009044d0980c3d017025030105005030040340c1216403154440407110200c03003054402a140f5408031400b40807a107030007454402d44080510541e10080d5888100fa07241c0c80c840b0700b04801160300d881794034000540060203140d114a60047c10a0b4a80b00d138 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 774236969 1250 774235719 774235733
    0x50118050c01020705060a0e31090210141902010b0a08030309011a1309022806020f12031303140d09171806030408090d08031e0c040612110a0c02030f0604 68
    0x2450b0031405034038115109091440001134503241a27a050350f242034441005030300c4400900c03e24001724440ca070041020505284607680181c4410304842d840b81c649030048015001c42c00440b00028115925030468401c15100c0541420080400c0c100654030b0303083c0500300b02d0a40b40049203003440720003005030110342655803400c1ca0400e03101d01580011201010b0020a16003000b042d0f980451a030001130a00d441d0211507038680440b6100c1e400c0d140c210350603145154542800c1c40e00340208120074801f180d182828080c25805880c0300c2d04010310b540700007401d55105900116000f183c059540c034080c8051121400482d441052003980c01131401d201260311421120584010342e0044401100140801c80e2800850b4007000000344104003203885032400704178940c011142042c40c0780320303604c40001e4482403000030360084804030f00003801c281c10050211a94800c00104c404125141da222000500c01403008200100b07282c0d071103030f51a0740f880c0140f501e08881e42c0b070600700c15800902080089624 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 774238219 1250 774236969 774236987
    0x606031e0c0d08030103050d020a0f03031e0507050c0106061713140709020a030e0a0b010605130f0b071703010e150a0510020604031d0616050118050c01020705060a 72
    0x804031400500d100314505103800a5440381036040740c02006040b0901c482d08002c2d6048a1103607085520000c00d00c001240c07620821760009044141803440f0000181c040d0700302d40b0b15050350344419000107400e50560030545405451000c0403030b000280ba01440202030091002800c800d041c4620800481e982c1c40c1d1001000034014070500c142d0218210402c21800130f918120300c1310000302c40c0c0441d2a007c0800081d40a410120b0120f0b02e001c0c1704244d0b0440c0131400307119007908a00c005810780e10f403c0c015603150784085100300742d80a401c807010841d4401300000c0c00143c6444084151031704010718100220000310a40740320084418801002130f0400f42ca0810b6008005001c0781403a41075a80c0440c1070a0226000f144e80808000315196500d980050014400c1d030080e41d585548000c0f03a040e8818030340c2e0b407401c1e07150040810419850004d80c50301e60042d00700d01c102c00005000c05204406003141e000d5480c125050340114003060b83e43d40c1d0400c010800fa0a040343d10b545000100c1c00060301c9291 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 774239469 1250 774238219 774238243
    0x26040506031602011d160905150d0629130504120302090103060f081b1002071a220906060e1011010603061503020307081513051c0801030311060603 65
    0x3101e248120000f0310039002001c14010304441d4864507081e00780c0c41601c0b400c0403d511030a030b030100c61000483d02c1050160074003422000c9580000d010411090140c9040320351720aa42c21503c803030751441210a20030101d0010b040882c0070070100c3d1000e104001c8409100c0c030040103d90704240601c4081080e0807854584024141001a580c2c440000180c001d0010383c3d000d514102e40c4c0c0c000c0000c1d41c2c4408919942000204035030b1030038402e1800204410001d1240c044001a80000c0c82441144001c190801c001d01c00c00b8483ca041003c0720b078413090b0702d0001100f110140024900c00700407101050182c000580300a04081c95210340000100c0d641e04003484104c4100103450b41c000c070130384600b940640040c5030044414400c2401c22b81d40001403612520049000740725409000410b8180418910381c3c00208656440790750303d40b1000e40071040ca0160058030b0600480b04080e5040c292004442d00c0c0f9100c54071846070942c9541805428003071000d0700d00d0300c01c1d0001c1c0f0421045940105041c03010071 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 774240719 1250 774239469 774239491
    0x30c07201905040e0309030d081b030106090501031508031c090605070918050603060f07050d06060e0f0a12020f0310050703050a06060e01020c060a0311030a140907030f0b061201092604050603 84
    0xf40c1c8603105032b01e4105915001e154041d20000000c992142e10070f400c0c42c01da900a0b00c0501292031402c24420b20b0114501c51000385400c280700c2e511494000028501c50308a00c0380c00460041e811f40c4600b402c0702c0094440a000c504516030801c01c1348030034a1a0320307031000d00d880100120700d40a0702180e11480300030446003110041c0c10004d60b28030b0240080d1018003442c8002000116242c8401410500c05103a1040c81119100e21401b031500d8801d000300240e904d16145980a01d103190700b4407080c03544090076990305024515041561901c1e0344101c91145425136008a910304002402804490701d98201800300145900003103c2640c00041b4800c4107802070311444d643d880894411402032071107908040043c0c4000040c4601103260703400509182401000440d0541c032441415903940449104c014017104820900001068425080311b45c040c43c068904108500052441821503000e888100c542c010703442810307440d00380140c075018881100a290b86103414101800505107010050080344a6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 774241969 1250 774240719 774240721
    0x90706080417030708180a03021e030909160e0a080c090403092304051e010311061204240216080705070b13061103030c07201905040e0309030d08 64
    0x40902c1108525060500880742c403800c1c0100b000380201c00c255641000420048642c1c40481c5c1c0114599100ca40c2c941c0041078241303034600c0320034000300c020380c101e001074042070040701001c2d150150cd40b403061621005002c83d00d4a41d8401030000344407200c0150043c11000014090000300050b042c210000444910002d40d9070791404603056903040e0400c00e0901920000d02c0c241494455540105e04011a0300b400503944442c1e150240c16400e881e00540d11207004010000f1400c170308446240c0420140c4914900000070f68449104c45060f07c1c100c03003446442c071030880c1651072400b1483c0c484400001c1945440803451840c8115141118083c000b2000050500200103040040c2d100030b03c006480303151603d0701807400c0821340c0000d11440c00860003000140911960200849118803003400c01c2d1410082c260301c498a03402d07258070850940c0c0b25503101c1a40d1540c1c8029120a007807103a0f0001c0d07590309040c0400d1100b034400c40c414082d0b242c1c0c401d01608449540105500c5508410752030520a5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 774243219 1250 774241969 774241973
    0x7120e0d08041b03150606140a1709070801050c041e03020603060f040b04090503031e06130c21020a0207050f130b010c06020309011a18070513090e07050f090907060804 74
    0x140150340d900040216034500c5c000075500049403c82c808a0f040b60722444680d504003401c543d181e102c0c0c0240d040005130303002c50350140303e5203054060341c0060200b400c907590161100c20701070840d00180c0d514281080085010002070070703a05420907061140400d1403401c0c5143d84d0200341140806040c20b0310441c91700401550315104d40d80509000f21005009100900f9103043c4035450303600070b0303640403484401e10600d241c80b540301c210142c0c00342c940508100000146000070600600b0000c101c2d0003001032220781d01008001403610039449003c89440141d4911210b10041d19042a50f48020301078400802580c60903564005000b6503060043c1004c00c840320320400488110040590040c005840401404003d4205501c41381c5c403482c40000c2000315060400411017a2030081036518409211440081c0d03035103105402401810100c144510342080c0c66440003019540c2c025400a4244d01864040116250488010640320800d5800707003040c0c100b04582684a1181d400340e841880980c41c00308003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 774244469 1250 774243219 774243263
    0x51201061b0c0f0509090a030e060f0702040c02070602102a0302040312080105030c0904023a03030e0610050105190504050d05030d0c080601020a110a0504020307120e0d0804 76
    0x1402503441100b802c045521801800c3d10f030782403801100c4c09900810000350600c6400117908010030742540752280400314103001c004440c0e0280400041c101da06008150041c0c450340101c056590743e036009000c083c1d042c40c000038034280501490403041c03418540c5400c03050004480303002c18940c0d00c0000200740c0104500c160043e01c02d0341c1c4000d0449120b10b82040311907600c00c407240d041c1d038000c4082e502d15200000030000310034401e50300694000703050700d1013001d442500503140c039070768a4000303510032603048080ca190b50800d1440001d0b0082a222180c50751100d00a00c04076038024040c00c0070f420018117041c0000e01c02e000d80e030780c020741d00c04661701c481807403030b01600541e00185802814050718181038074205481340c004151010702c0504000340e021396203024218440c0324a2f410380c0100004801034884400441d060030001740c0000064070049480d07151400250710500c900c0d2140d40f02c041402511a08403049a0f4008100b030704043c040924080d0b100701c148e5041360304008008059580144210 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 774245719 1250 774244469 774244517
    0x3060a1707030b1015020d080f04061b0c14190308070201021e04150e06091e09130b010806040c06030e01290112020405090103020909030712020c0f0105120106 70
    0x140403d80103004100a443c0c2e600d841d40250380f5604118400c140e0002000d0fa13842c0707000400000443d9103174000417a604900000c86038881d00860b00812008500c28501e08005180e03a4940006590002d90100b840380865441070422041001414464484e1818000195a00e440103040040c1400840c00710341c800d40542c2c420180c40703c204c00310170a0407000340ca026440f41c4150051850b89589042c0c40e01e000704e0341d000c0e4501d8043c1c41c151520140c1c40400c03209107640300d041440d1314402c4400300d4287d25805502072107032004c0b083c1000050114100b0302c816400503405200c0642c800f4080000103a01042103004440d8607003804240740743e0740f00c2d41c00c0c0508a800d011807544074402400c04a1801c10300c503a003500420a032110398440003d0640da109a10441c020250070000c52401000107040c80304c6042e900c100110180e03401c1140c40c0c1e1ba51003c000d43c1c0c101c1d5000683c07100060790751520340b02510021001e0300742402c51815090592a62507085c051054009210b01400e5411440c55450034417 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 774246969 1250 774245719 774245723
    0x130201090e0903031b0903120d0207061409010b0603070f080a090206071b0909081608070f11150712030e0f010617060a0b011d0a0302100503040303050c03060a170703 73
    0x550090b10b0001d2100f039032a0000c5a840d20203030611003292020342481400c40d200c0100c06409010705000d40c04044885501010160300c44550030003a2401182e0580f09042d0031600c0c52221041d58101015500c1c00e45440e19900b6110b15020818050700300d801c994030058100d0b1034180040c6a40e207040c100c1d0010b0600c500d019400190015512082202013580d0b080c0040c1040345842101e40c488668004444c1000c0000741108001c101280780104070b0701c80b49a190384a040130354500081541d813500a0700203080d08580c900e080d008015150710b85115011404c840095078103080c03403425141c2a0f008d071046c11511040c0f541d95054020020f00030f10012054900c42c00083c400702c0d59403103200355490a0303040341c0a400d009403404191406030314002c0d08000726050f510080d04030b00070700d8401c1c48030108400d444e6001c91034500001c016165800696014201500d40c29103a10b0700e0b04016081d503000409810201e6030810400c541c0395512038261050320640030540008040000100f0324041d003075000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 774248219 1250 774246969 774246989
    0xe0714030c0d140a08161406220507080d090e06010219020f0d0b1918050a03082e081e03030a020d0e030c0106030218160e030a140d140c0613020109 65
    0x9200c1c9403480780d80c03418103c0b52042600c00b503941d80f0b25540c1901d5050a07175400031381c3e400010034103403507040c1d4910721032110703000d207003502c04a55076332032602e2510070103815403400300b104094108504019038001540c0f1031004c0c00941202c0060b800c1c01450301c00c40d8400281b182524460071411921407036159151f0940c040d06050050a05031950202081d07201d80e0121a20306085075500c1a01e03080901103c410b6000f0020a8114201c0c0d40540700710600a0450041030700e0068130b01e01e03d41c4494885091001102c0c40044c0d0b160a241e040741c1400b111800c50b4400d11003508520007220400411241d10040e14240140c5481b42d84214402a08030450b042025110204940c41507800661140080703a2088503007103820b52484555003030420044034030110b00942200305501d0345001c3d1460250b8010000c0544d030300240315581e010300a100c000c904121560200c10000e035a139820004141c0b6040354504400d007800810f03202c00c0d60b501c00080103095420001d00b000d0007164000c004801c060205103807 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 774249469 1250 774248219 774248227
    0x40c0210090318060e06070201030b012703030e030d120513022206060f020606090c160b01090b030c0d060c180803070b0705071a190e0714030c0d140a08 67
    0x4000f0802c01505504910148000000040c4580601e0701d2544c3d08202410741030400c034858005500503d000b1241134140702c503101c00e490031000e4109400080c80068542d540d0000e0441c10002e24500d40d58001a00a5004543c101c1d01243c12282e000c1140c200144042032a9072400005140d1547c00c05c5d00035000301c0c2011008141c103041c194882c0b0046c027454000c000f51a40c5a00c102c91421102c02c040c005a008400824494140495215408101c194406161240159240e8603800a4403070a89640d0f200100502030110b03940900d40b20a00220018102c00310040c1c005008080c3c001c4000301420360310030501c54144d0186070880c45420541c504445010b50f1749082c00d880341c1c406402159030600850009410341e0048059031030640d0401100c0c0241944641ca2103200700e00906003503980d0780210f0080c45d07143c505000e03140d055025a4082c0a00600d0f0450700310130b00070800c20a51180e0070a40d580209512080115400320350405210003036109506001810800340d0b440142c82014002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 774250719 1250 774249469 774249473
    0x305031c0e03040906150203040e0c030a140705134e0803041703010f0b0c012c15041e030905271503070603150f12150b010e040c021009 60
    0x5c0d2100c1e080740c0b250a0032000c4c030101a58100d0300c1e48254011081c05403410170120307940158050286500c85c0e000b03400002ca514041d030307200100c02000c940e4000000d0340040c88082c00034640100c1030041a0142110105d01d80200502210b030100c0031030a844010307004007000c90404007480400303a1800d0001c5a184402250420340500c0e401124141c0d08003241014405503039405000700c904135410b01c24218030040c180000c0d003041c3e500103107102c2e41c15074039518064500b401c8102c03d1007100b01c240e046c480700209907036001401c08034000010140c2e61480c104000120750205002900040304540d034004800d00c0b803400396030052054100c15000116004800e20408107420980c1030081e45c1e090030191030790745c000740c0340d1400e0a8054039501900302400810040380280c00c0501d50101400c034000710603444580215441c406640070003042d20000d4620b00034403440210050044a6030381051051056420001c1d0010416656603400b8540d60b21414120720310070301c4400e0748d4001c84030003800809118 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 774251969 1250 774250719 774250721
    0x4030303140906070e04181a07030e030705152806140618040209060405060f03060f0109120b06130e0a0c0603090201020a061107050a050a06050106090305031c0e030409 74
    0x2441ca80040c4452207010030881100000d2551240e01641e50f0103000c0c11070354007400050240c03a05216031800390001780c0c0002075060f0314045282549140700078a1480d2248006040d40c080942100ba20342040200201250011550030441303903401c46054425200c03600b840c1803402580c000a1134407042c04a940d045207005e43c00c810111100f044030040458a4030302044420f21609034000c1400c1c120705941500d6080c01c0d00540f031503440040405041903643c40100366958021400ca6a60400c000200002e034500700c4d0214208040c03e20700011424100010600070844e0084060601c4080f000024100d03642d4080c260b040d410708071030034070014000a00c1559282c107240c3d02221410317440d1102003070a43c405c0c4918641c0540584c0100070320030706600e5a8005208010b160310742a0710800c000008268100044880c00f4441d03001485004220b00b803e40c129901078012400704920360f4000c2000c907030008182c500860350f00301d00124061100712079400078404114011414040490700040301003031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 774253219 1250 774251969 774251981
    0x720150a0801060e061b01110a03020415090b1c090804060c2a061209020a08060f0901050421020c04060618090612030507170706050604381504030303 66
    0x403611207200c2030b43c071004161544850405042d40012050000c21901d0a00c00b05041c001410100001040a10307243c0c107140036400400c00740c0110b134000030200110010046079a07980d5803540350040626040a050312150700c90440c1d12640d881110040c0c40300c1b0764982e40110781c06c031342c0003130303000e503036070760303e01000e000c4d03285062090785d4005080e55180705214150500060780c0542c5404022910300b80707002507444442c1c1d40030819034071390f4503030b801d0005803079095800011705102402004c03140303050540840c040000034042a010390410041c0000209801d00c20501c1c0c1d102000c81c120005840d080892a03c07051001860741306061800000b8071036001141c0e03d03038400011160805141e20340c00c05105803000c500c1507600420080d500200881c1c890400740640600c500519a0b0800308100228500d03000040c2c195200c66580d0280052450144214904a4000c01c01c4600340b42e0121071065014050244003624170b01d454070102000c0e40c40b000d11918401600213482e440d1900c0b420300074000c1103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 774254469 1250 774253219 774253237
    0x30f0618051e1005040503090a0915120212010f0b1305060f270c0a0f030c080a0203090a0209011706090708030316030612060b0a1208072015 62
    0x1240140022091210345015a9000e8010009104511080c610b002000702d40c0c0c60342c00103601401628108950483c007415001d40d00030002162100700c40001c002544400da404805c00e5498800688800c401280090003101c41940700408101e21900100d41080342c6c2c40302c00f08055180c080c1184008405a0141101c65015a24048000401891001190404da5860351300c0040d5030420a01c6183c000c07492000190103406141004004040710b251091050b60515404480440c50b4680558808400c0d29050394a20301844420f01e26000a4840320000c0c04034a034148c0c0003c00030314610001c00000070780030340c068960744d159030b5203c04440329074084007201d0900380100404240c40200000d0440295540b440c05107185807208280440c090103040040000e06d034031030200040c0500e000b40d0584105000707050100d0040003040400244070001c0e0807480b41146d2030403080380071900780c80c251074480346d1108100d080e148001510000c0b540e10800c031264400314988201c030342c07090301c40003411401d9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 774255719 1250 774254469 774254471
    0x91e0305010b0612040b0a020f0403050703051501061b051204030309051f05030106180504091109100612090203070f1e06050703050f0d060b0f0c07080a0c1503060906030f06 76
    0x85401c003c000f643c0c0f0950b40c1c442003c0394030001040125000800441d00000070b00c40c0146030003c80031000081703400590055810b034020003010014420244030400d100302e42003544402c25818458081e01f915840329090480e00100384944003001010410780c0d050509021445071600e0352450001c00c00002c90007024016000340c042d200c081040c64000d80c002c403080b500c441e4116030a185048580400e40e080703507500c80c00304541c00101a102c034403c80c107801e802808180103e0f02c42900f84000711001900b00c4c0c15022621800300328803a070105600703001c00d81c481404100c0f10000d00000e403030448190014005400c18001c0054181401c40074000d80251298400a019940f108141c42c0342c0500000507002c10003c001c038189000b4104010070184583e0300340091055203a05182e605604414205070902030b0000b03410003c0700041052000405900c402002d0008650341d96003507041c4940f081801d403d2404101148143c0207400ca00090703d4a075500700070555a80c2403c46048a00840554400b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 774256969 1250 774255719 774255731
    0x11121f09021b0a03050322060f0c081006020606190b160c060201090803012c07030f15120b1015020a02090609070806060906090934020d030b01091e030501 68
    0x14003000f00c0d00d448000c0d01602d8540c1982d035402d142d000c00080c0d200c0d080f4100c01401607140300250b010311545050000d100c000180c0c9801c0448003400355017000d00010000f0501d0401006006d90000c0c07150b902c0303d429202603203480340461180954616582045134668000300d06c03515102650051541c400780144184810603a41e54004d030301300d440f2080c02401c0000100014058441d26003850741c5001c00e00514003201120301c0c02c802010072070a03500c1c9030000c3c2d2100c0c40b085444405004040100069502032850701e40780081514480c8807001000b0a400142400035165800400d007030360007403807141283c1d0445034400000035211604a10101c0c07007007404101041043c06e102c6c401e01c0c804c500d0b54a40061580300c0c0401c100c1c06811569510354400740c100444440d83d04d5a02c03071a801490a4042c030ba180742000c003000c07c81000d0a860035001400d808208040b1181d0015065aa9183c242800a1040c0301c503001210f000c0500c2d00031240c0e110030500c200320420074291204080700d000740700030007407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 774258219 1250 774256969 774257017
    0x110c0a120c1505070206060d0809060a270e0105180f070521010504050a0b01020a1416030b0f180303150f0d030c0317070906030213090501080601061211121f0902 71
    0x6007100c641400341c41d809c418064030840c0d00b02f01005002094540c01c0140b021001913440c1c81c0612400182d41d0351002c0c01c0340e01041840504000107015140840d074030078001841a04211032628020102100c01035490003140c0720383e014008862131903041d5911803000013004440319400e1407080c030425014034a0320703001602c007982510580031030f0038059000c0e19150002d03803540190240101d0b4041c0e514011074100d4540c1000c0c8003a8200154410011002107151140c0322001c03c482c001e01d901092424a000c2c4850b124001c4101c0b94007100c442c215490350700d00c01003c28032442c10001440d41003040300d0440000c2c55040200162802d02c80d50b80da0303810044091441d001d411040d10204003044413003005000d16400380d00909030031140e40e0b40d80c0040941c0d840c0075070700717a40003031707011100c00e0704201c0042c0130b450780c0a10445107104124809015403d003100d107240c5184185403072082c040c41c03003102042c0c00300d02c034001c09a0051a0b02c485400000c0d104c80c081c0f0022f51211180314885030100718400c0c0c3c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 774259469 1250 774258219 774258229
    0x11706090304031e0203100c09170712080322030302070203100c39030f0f08010303081506090d050f0c0108042d1a060103110c0a120c150507020606 65
    0x96030b50091200207038052900c4c0000c103112510303000700d80c50f0062581d1401c02c0d0440c1d03c00c1720540c0b2695030700d4500345403074400d1118414034015695011508100c0050000302c1d4074511070a43c1a40c0480311994070303602c01d8404c0d4024554400000307c4106558030310b1040c0b41d03258028064850088058400d4601c088100c02e0448132480304650100c1d20201c2d0403481002d54960400f00c48200152402102404000c0703c00e113000206000c0300892503a43c10308008660018a101440402d130414580a505585014014060081c00c44a0b0b001e881d65150b20f990b2540d80540740c400b42c1c044c1c00400c80c005c540c0384c059110f0140741200c01c5a48603070b001844c41503108202060041350042e070301c2a4401d094030440034840f04201940c1052802d41d1180c400000c09179601a40000c01c1c6070292402401c1c11000103065681c221280411640180301301c690344040494600b1145a0103000f40d5981c0c0d003600380c10343d0310350200d21000d019001280d88040564900c2d07000309101300c0f4a130782a281181d441c501040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 774260719 1250 774259469 774259477
    0x8030f0606120c0c2407031410052106100801050a110715060302060a030603050610080318240c0709020c0a0b0c13080d0807050f0d0b0406030203060117060903 70
    0x14030092190011a2601804000500100940a042d80d28039031060848180c200c5282200e40745d40c6481c0c80402095580c50f114040c490301d000c00c7d80104a0034801400010450f5900880707105802e101e42e0b4043d001c5840241c21035108080c4195021171400822541d414215440b4000702e9500b0100001c040d01e0041c810707840c1190000c00d0460514405849044c500c10110301c144468a98900d008000350b6a42001b800c1190b0329507501140c190b00303500d130850820b40050300b01001508111418800540080149c428854000000d9500281c40c100064124410102c1d1000302d0719813445000384080001c8018035581c64058120340b25a6520201d0780102e10984803580615040985103400040d0241c0e40140c00051780c014050600c0e1a4040e0840c0349003280d44814540e0f400305001100403500701c10788561180380d90a2079400c006190901d007581d4480c05501e0ba60581e9103016042c2142d40d10b502c1100559000f5040765000e42e10390503a45850120080008124800c1034005012050300000322 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 774261969 1250 774260719 774260737
    0x114220b0714120706200403050307051506090a05150a0b09030615060909101a031f0e01061107121a0c030907053c010f03020c030a0c05160308030f0606 67
    0xc0b40b80a13015110840240b01e82440b10030315404c41c643c924900c003500380103003010f0b60203440a1559800d2a2516603d085c48000035403401621100410040303540d21402c1650210450101240590390b028003d0560303d03102c428141e0080d1400740224541c0f000d40041c0000f07003c1a03080754841e449003a01e0110400034494180d80c881002c0151500600303040703441e5a00500b0300c20517000540d880340d00e00c1d50146c01c090600c49480c5004410011003503d550b68070b00002c8592000b440809040041107494000140030702024080c1420030703280100010040c600051100c0c04030088514600e1410507040305d000340f43c40c01601811804515084022003c236801100c3c2c1900034800c8501c2c100600107112102403080350103810320816103150319134418030801d10311103440701940041a0680007400c0000c503c0914000c1520500c13810781000d4001084400c01d80f01400d01c0c9141101910346103181811070707002c841c5000d40d031090000c20090207038059800b0701e20740101250309a03521018800540108141 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 774263219 1250 774261969 774262003
    0x212040504020c071206020904060b0703120203101a0c0d0206100905060103090204020c0606090c090109170f07030803090105070c030c060b0111010c0c0519020114220b0714 76
    0x82005a0301d8942d009056118090742507514040c0c0e00d203800304080038401c406594031900091000f055142c207100702009803080d41d504508144e01900d00410141d031500783c80346066400000300740c1003258106640e0040c29403080d001802c81e0320f075403010142d4200c2080c08090740701d120518901c3c1070020a02e14802c05200c01100011342c07600301d0b0f0401905016050070f061568402a020140c0c030765000030009030340030300014412820603109009801c1c40080038800d148009000b19955033380d0140d010011a002e070744501d41403004a04c44181441c4d0000203050036803103013200001c1013205803001b461240003400000c02065031900345c10b65081c01c10341700050020750b8141500c0e0003d440743d88400042f2106251500f42c0f80c0c044c205260840b0780582e082404944507204000030401c0420541c503c8920064500f1860150795001a0003c0d480305004481e40b80c0215021801686010358181601d0004c0e001118055984030001c0d665840360700c0a6407544a43e4103070041c01c080001e401c00e210010409 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 774264469 1250 774263219 774263227
    0x21c080a03020d060b180f011d0d060f090f031e050708130f06120b121c0309210f140306011103070203010c0512160f0302030606131403010c0212 64
    0xa0308800035481220329098030baa071204040380340b420000260641051074102070250554010400201301d101248450400c0703100e21040703410080c6040d0048000c1d03800c1e1040c0324201d91074074050307000c0c2c0302120340b1254030f40c07820312000c09100c4501201ca00c501c0c0240c90381c01400f4040650440d01d410000018130102d20b0410049001801e4039000b020400461003c2054850b2070b40941400c0c200c50703500c0940082c3c9001018404006940304249400310211403d0900c42ca10301c21050701ca4400c01e483c1c000c0f55000c4030078500d95030b029800400241d5440b0080840f07000308560700611300030350329406a0000c0e80b0600c81141880c000c8003840000c1855058003402d640d01c42004450281c00d8002a45090209002c0c800058809000340e0740d01000b070341c41c0c25072a02c0c10740d00b402058032001005580c0703503130b20120144000b0360000d03503030040500b41e03150141c2d03696190008117150b4803840c2c441940d000c4030407100064550040f000800310317400c00c4009005100503190100c1e902c813000c25000591050800c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 774265719 1250 774264469 774264487
    0x503010e0c09060a2f06190605151317010c0806030c0d02041a0d050f1204060f050f040b0a030c02241933210b0c090616021c08 56
    0x2802c540640340501c900300f80a030301c440c042540802a602e03501d03c51030707200c4814440d02d0b1f003050039030884050b841042003000741d10b002c0015001c042c0035030000200031400242042c0050007114660007500010b49629810103043d440e4070f008212001904000030080c60100712a0700d000301e0140c034a81070003400300500c001e4503020400101080b4401c0108501d81504168a0340c480220b540355003070144000d40429100c440001d401e148048018484903003081005000705031304a060984414070074904030380c9513031405802d42120f1003550010f070115039002c29181d03001030307054110604000599003a51582413081d170508042d40d52402e80c0010308400080010b1020a05041350784400350a01804104480386107820008142414035125511100043c0fa50711034404905000088c0314809114003000070b144002c14140440c900000e0240d04500b002c11507100b500001d48ed54010010a400d0392903c1c5100042c102801c0a1012401540d01082882c094110444941c0c0c1c030941102c1e8882c505001d0f4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 774266969 1250 774265719 774265727
    0x507110307080a0309050a080a1a0601020c0d060f0605010815040f02162009040309060c0312020a0e0108010f0609170f0703080c0f01050903190507050d0503010e0c09060a 75
    0x94241940511032654000381a80d010029000103e001c0c1d210240c510b810141400258140d982286419500c51242400080c081e0340c02d402c51040c0030041091952138003c0100e040243c0b0784c6a1560080c0315192003402e02201758803ca0300700c600340c0340c104401ca030303920015240341e80c00b2140c0b000d00c10803404000204e41803e4000741409001101c0c01403500204464480b085038010000750794407040d0501d0283c00364032812000111001c1101e02035280d240a80c0d0090075500c19000d42400c004807418134104150181c520404968046070f81903488407600b0800070b021040507051540012014400040d25011201600c0b05440c0f450780c92007030703450070032441080b000d281d01d030303c00c4e0944500d422000000c9424401d0308042c5110b1502e060360b4000414103a8500f941344214120036914004c18003907110400030464005c00c14820800903001d001740019281d0780181302d400f41003806040c00302420b05500c075000358103940d07a0902d215071175198120a114107009200c3c0150b0010003c2212001440c02 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 774268219 1250 774266969 774266993
    0x103051908070c08070609170c2701030b0a1116020118080313030b090c091f08010509010516020303131502091f121a061308060903120703020306010507 67
    0x4415851070003801d90f540d602101243d600440e0b9640080300b05100d800e6220342c0041c01056080c940d4816000842102500c600e883c5a009100b145410314040b002609400c0c103010301c003060440c420700c5680d01c1c20616070b5080202c44441415250a89002e21641400151122a110742c0218081c141095005540d40310300711190594070844c081000071110401c02c000c0135100b801100c5481614903500d464107076418064284412a0000588600d5644884800c9984142078001c6500011740c18102c42900e03071084c2d08851910350a0000b041340d0540b05410403030190700351800240055500900c2240c503070000751441c0d110455202404030108201d54a89070740f15241e403200614001d005000203425450141c1d03c10740200c526a4000e0f1425080002094406507c401c148840d2071440c408141e90082500d03814440d200105040d0100c0d00d01191410203000400f00300e41d103a0400c80c0d11a0340d01d801000c030081d03484509034002441c880c424001d5070700805041e1200703400c00007641e88004424034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 774269469 1250 774268219 774268223
    0x23010510061d060c12070213180f020f18010509010501020a170f0f03010909140c01050a0305040f0b191a060a0309110a0b0c060901020306090c0a02010e1f0506040501030519 76
    0x60500201c1c14085041c003051100000002900c6d556184c1342c814480340650300380b41012941e01c0c10351a01c900360501018000119070004141080e01e4861000941194020788030ba500400003000051400c0103a20409040ea04229a460314681ea200012a641c40103604000d15000030403a0088644a5039805803410f1109000d200c2c0c11b00c1c411200c6e001c0f03690001d90200d400240c44031a0803040c0010000d020312841188000342070030280b84000030f03095101d00c039481070803da40c801c00034041c02040925424a10f610410000e89410046020580c0307401e9090800782803442c0c80340600341080005100e0702e400703030054500c40c1000c8030b01400390000c0080d18015100e4012440e46481c044d40c1c2c00e020740000d003c0410348162226040c0310300c10f251910007403000c00a60f00c100701f4080e20b03580e031030041078bc0aa0340145055849010070000c0740902000d10340c4e41c40d14481d55601c2d00310031061004000400142a030300304030720341d1503030101b0050f84c0d402c1c0f00261640e00503a0f00c0c42100000881c0c0962894 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 774270719 1250 774269469 774269479
    0x1050405070e1b0f31060c0602040308191101141b19090810020313020607020604090203010b0307080603061315180f0605100e010e0402010c23010510061d 68
    0x440f440c031005000b54004070a4141c66440003408843c000c1d10f0204403220180500b4655000f802107040302d540b501c45030301404007440005e0192008101c5542c045402540d800036900b0f885640c0700d034411083c40c1501203008040b560071003803103040090510460460740c108410b01005074a0f90745000c80e84c0c00c42ca40050202081c100700903000100300510710080c1c014280d45038cc1d09075141c0342c952410010280c490085941c010004e100c40c04103030b0000b070121150122160380d62541e00d4400241c903442030b6070101c1d00190020000040c0312403500b01440c03040c88540c83d0f004640e43c501080645030a4122a44030381000e0400c48040030404000c0112418191114002006480840000c40610b144801100c01341c41c0300d041641000030500030304d5001304401892006403402d00108010007101401040c0c4ca0381d0b00e4030001000d582c418080340c4000c0707030041c5610b000c00100102d5412502d0304040503d005600b0100030a028a42000c14101100c000e035803501c039000c034100108851a45050405a802 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 774271969 1250 774270719 774270751
    0x1915090b270115120e1c0f05040e0a020909010303020601141002030d0f021b1c020f060a230406020d2007021c0b250e010e010c170f0405090901050405070e 68
    0x342050f885048850300072000240a040c41c41d81341c030340c1804003846c80310041299141005458a42000a46040c0c45d141c100515041d030710002c0802c000d0041209a5900141c40000001450740100d96681610341a00803c2800380c0148140421020928004030041e407040065601e820256403114403450400c2c00b01602c0c10851100f0201c0702c040c1c050b424100d80d00b1414a0300d89940b10040c1032035440700140060b0151044082d8855144c82004241600d4161a00d070883c0e03051205124415184840c4421940c042c20107060940c002c0d04070900001c0d0307907840e0079441c0301c3c2c0303011a010000580d42e060b08468a004540d50900071141c07180c1c0ba6060300b543c02e5007000c600140b2100f900f5845804041b400500709540f5014401600c00490b040809202c1c603003607807445599200c5045030142c042820071002ca03005510b44101c180c1034130f11507a9488040401c60050050f6050700506c201e8004498004064542c80c05035801c8a03003d44005095a2207a03d00b0411402d0440d040380d4409100c032014281 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 774273219 1250 774271969 774271997
    0xb0703030e010c020d020f070807030813030c14100216060e040b060a02060f100f15051201090204080708070f0905252d081915090b270115 61
    0x1e540302c2c00e8043d00560440e50b0000103613030b070400403581c62401c3c0c3c41c01003c00d94076180c025a2a001e40b40000f0700041c800003070100380b40d1a801d072000011a80310460f00700f0346540e80781180c08240400032852181402080b61080c1a1001950b0702c07510341380702e080044840ca0101c050381e00c1040010140d070001d847d03c2910780180e03941d5014120b842e1198000e08442d03e0210820b52201500401a102400828401780201e04404841c032041d0b4041640c0c0c100c000212408c107448a00445003a0600303a4944000032802d0032440d0003800c01c80700444126003030140c84841c419200d4501c0d018950805581d03a10030030101d11640c200c41e40105155804043c002a01820740c0104040708461001150300f403070403040361003020380748600c1d80d405241801c0120f4184840061405402078070303c903035810400790f18580d403a0107940300d402e508129400c9410350320354540c0f840010b802148499032040c0505121200e4551303505007100d007030742c40c540c2040300c681e0b0038244041d9055040c0714036036080107052040701d0303c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 774274469 1250 774273219 774273221
    0xe01060302041107060b0d08030103030c0309030623090d0206190209060d1407050c0c091506040f0f0e0103020105041211060d0902090108030a09050f0607020a0315110906040b0703030e01 82
    0x2540c803442240e48101c281407805c04c0ea8401e1403081e00a40e035003440038010031490400d03030341525458640020049480d050441348904541c00103008289090840103400a0030039640c0716031900300c4e000b91f100d9903e98500d04c0d191250105604c001da0040e200059090700705040300400b0320500c03030300107040c05400d00211f60a6080074510382401c03592201104020a4200c040640c011100e1505a18100a00b00000d4031081c1803250680180415404180c0818034081003144190004c0c00c640c1e01e4582da5440e91001d2100c6100f1a00c03280310f02000481c646d4a0303840e02030b042e40c3c0c068650034501898030280c0c4032009030b4501d09560f101042100365550307640301c10080251340032030711000c2140005401046001d58043e0f109948a034010403516081c00d400460700e0701150400c854048a003002080030401c40d100b0781d403009512899a5a01004000b10f01e85201142006450108403541e6a03c0010085110700024140e2250301803200f001444100802032030910310901d4003007800300b0401c1d00300e4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 774275719 1250 774274469 774274481
    0x90804060206071d10111203070c030305091b19080601060c02012c0409050109060507020f06341101090809040b0402120a0207020303130e0106080702010510090e0106030204 76
    0x4001604442c05011146030311a00c1c0040c510300b0414107507907100c410800204078010306500705082c01180c0d03010300c40304242841000e201500000469540e0300d0543e000901c40c50341e00ca01100404d00d0040812070507440000d08144028030041c0e81c1840e00d60322410031241a8240603102c141c0c1c548503501180c503440034002d05000b4151600c0303150303116581d4400504403202803416510112406907404565102c181800342c1688015540058140760300e041050243c107070441d01074540381c106001d0086555001605480392100708050302c0380303a100c40e21500d0601e800e070101d00d8413100c010300320489a65101d0062070843c1e041420034508203040003202c070742544c81001c412b42d40c0c0500415040390134105030050141140084500b14a8124120020000840041c01d2200c0e025404141001107440c100308580b1070b800400e2002d030b0015034071510300050110074010750303000031281d80115421038014007d02d401040400c070400c1c4101e050420f070000510507034101030324540d00d0b681d0010160f11184922 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 774276969 1250 774275719 774275729
    0x30b06061b0304031a25110304030c0f0b03040f0209180d17072307060b1c03021902010f03051902040b0325080c0d0f0e0105040614071d04090804 64
    0xd1600c40780b035410b0400201d01c4400c3c5e00c507110600001080111140074074a2401992034180d10f069405d402c20003107400c40d908001c014100d01c800200802031000214000045442900c44103075082e03141d014200150009035001001056202c07608401468480f01540d8002072030710001442d03420b141c162500c0c100500a2090115004c140200c1e404282c810410354868554200303441402d04c0c00364000c61080000c011800511808103251007009101d4202c2000600c1c003c00c4aa811388045460ba001e080040600310090700c16121120400498004500d2025805844000712000c8104043c1d004e01802011500c1c5c00321160001d196403542480a00081e008078003406441c2d10381006513204190030b8100905002d20b2960040200c00e5020711f14139400800301041a0701d0b101c2c01c030303035030780181181001400300c03a4240a150818440c055012921940c0100300030301224200c080001040102030340d280380011a0000c00400c3c48038106a417201849001d0300004101459495050340303a005a040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 774278219 1250 774276969 774276973
    0x506041e06180309090e0304050d0c05100906020c040504020607080d090203121209061308490e0c01030902220c0207061d040504060e0d0807110a0c030b06061b 70
    0x5200b06143d07102c8600070151420700800c0212903c4074110301e54a018a01c140d0f07118000d01c01d4140c00700322403500b003c80148409007040106d81c0c50628090b09090f00e500800d0014420103002e42d90a141501420f801250050052860b00040da1a980503991140701440221a22054000010f84080252070b86c1010001e40c0b194803007200c40320402d075800001c2c200c800700f90302c8031091001e1000c000200002c4107074005016079039080003444c00d06400003010188e0040300781508444003501032081e1008000c2c841c1458085540350042022421203804521030a820350082d83e200285501940c0f001c0b405600081140010120f00300c0c04000d80342007010301420007601d80c040c3c46071441d0100b1284000d0441400c00c2020072020510301842400300881c2140300e01d4179a80498240312050b031101542c400000241d6500140901c0b0142540205071001c00004444c1c69071680b03082008a00620041e0f03000c940322008a2554035200031004003d0407035a40f200080006410035000d0300010341401c401000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 774279469 1250 774278219 774278261
    0x50f010302010e300d080610050a09121506090c020d08061c050a020405071d0d0f08071407080d0203040b0a0311040612140103032708010227010203070506041e06 71
    0x81c042e810318040316005c0090141143c2408801d5881c1d2095003c400d803107180131900d90783c91540480f8030a040f54800041b108040a40f0300030b00108024078000d1510914050001982e1290380000b110009141c6c0320058100f2000c1c0c2c00c6c0207115244035500000001d040449000e480c0a450340e010110260803512603006450350011801c0500800c1d070308c44000d08005034220300642c1800c5c01d1400118840b440340000c8ac1a58040111030344100d03000700c1e040b004654a41195151446414400e9102d410b243e200b2650f002a0105000a4100e40450540c3c007941c1400d240c03401d000d1490308031720108414940c0b80e050b03c2c5600e03461103001e44001c0840b0342d141c030b11041c0c00c01d10305002c0f191080080e0390032111750341c014070100346c0001140c90030b182101d4044104172040b0304180c003180295003103617140354000a5044d00c0e00141c145060891a4417841090000841c00700599681c0f04d00d00000300150000c0300094003055082c81800c0c0070000051032480324940541d070b110119400400b404c21000c08500d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 774280575 1106 774279469 774279559
    0xc17030a021614070b031006080603010b100504030b060108040f0b06030a02040e070501080a050106020d08040c030204020307120f0c0e0f01030e060708010501080a050f010302010e 79
    0x120500d0310180740745448030341026000040f0820307120b580030104d4140c0104080303e006112854000c50406e05d003003001d0781d220340c1c001c19181d4195660f050601c2a501c0e40d22221032484459aa642d542e43d00718a4080f002450290005040100d600c0c20000040d81c000d03a0380760200e4100c2c102d90150b03076850000a1514803010310013074110b400c0804a0111440008408007030300d4003602c44007a69074408602d00d00729182446000016800441c080c881d4502500c2c1c2c4c20741048c020301c20701c681e058403074020034141d0b44256110400141d002c000c0750b10800c0c01d442404440191224144007281518000408000055460b240f0641412039150170580c0280d0106810842c4801911124940010083d0201ca42480303220b010039007400c00a290154240b10325407080e00d082164084503400c54004451130081890241e030413014a6034245002d05200341d20034682043e10fa0f44405d030304803403 = true := by decide +kernel

theorem cover : BRFrame.Cov 774100719 774280575 := by
  have h0 := BRFrame.cov_init 774100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 774100719 ≤ n) (h2 : n < 774280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
