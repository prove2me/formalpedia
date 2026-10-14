-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2824
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:51:10.738179+00:00
-- url     : https://prove2.me/submissions/74335db5-b7d8-4640-b4c6-f95d1aee05b8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 507733812 ≤ n < 507913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 507735062 1250 507733812 507733823
    0x1404030e0109030f081b1f060501050a0206010e09210a02060a09050a0f08041509090c080c04030818060a0c1103030903030a1112040b03040501061a04060305061302040f03 75
    0x1100c0d4903940308001540980350003e007080035815695640c1420350780030b0b100810000031080341c00398103008240030242d4100c100c0c04c040406019011030f507504403502503010506010041009403071503500820349a044070342526079480e2507900d1600c542c3c100181c3d00d81041c8043ca641701622444d0140384040c2002c0381a035800c0701d05a03501c40d03480360304540703481001810a901000580000076549000e640303e00d4404c0c42818245075a0720604010700080c40380840c0850440c010070700c4100c0c210320400c100f80000b454040001e04201c28810410311540c00301034410170307001030401082c070f1012022904140024107015503902e403003140105540d5858004454116004140750401e20f000401e840100d030b0000d018510f000082141540c1c1584010070f0000b40340241703c2142208038010001e00b0040103035442803941c91801d8075005003110600e8000000d802c07804940c100720100786000765010b03126541000141c6840d0500060707504503560160032880e9000081c0860358040300d54961044900c1030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 507736312 1250 507735062 507735077
    0x30f010f050406060e09041a070c0228060c08090d031709010501300c030623090a020d030e040f151a0306100903060c0f0f03180305130504140403 64
    0x4000300000d03141d03d0312030600042c3c10103c407522945004000a81c000d0301c21001e070000d0499104842c0a002003c80c0e080d0041071701c040f041001d505102c10b02e14004804400ca40140c865030220501c0e511480707000344030800050b0034044c410800c05000307c482c8101c0c01000b0f07081c0d0301c840d8980201849031a0300d200c00c14145500200e500280d050254038161036443c610000c60900c1524002c0c0100e040e90352120808581034005400301d06819003402c040c40c00f5200120344252101c0380d489000b02111000c0046081c65030801c20050404207101c40c0b103550444410701c01c1060f07818212201800801056030080c078001440300403000c2944541d80104510340c40051056075502c00c406923800d11a224504030307008000050030303403920720014404002142003020210741c882c3c4030304040344d401600d45404140d520401c4c4d0300d1103400003a03c20446d24a46001d220b071034001d03042c00d00c0b40a0403c1c80142806404290072005a01385c061040207018003500c10000860600d40d05c4a628109640640225040c0c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 507737562 1250 507736312 507736319
    0x60303130905160f09090f0204050901080d0206070804240b030f0a05070906030b06040b030a050d0e010305062d1314011d011203141b150916090b0a0b030f010f 70
    0x1484150080240944600070307111b1600100c0c40c09010baa02203c1022603003040003180d01e0340c0d40b1405030301070300348800104102d058404011340361120241101041c03004000400c4001810140043c100611401a440101d031004c040b000140c405001c070150306000d025001c0ca01904002801c4400c00d000c1c00c112060142d0301e4081004076009404040e010003035000c00100542426006100c0429002c7d088803403003012034444a060101401c003010004021895083c0700d583e150142c5500020103d510702c0003410345180300f1041e440c0403c0c0700c00c2d12102ca41000c124903620f218403121600710301c1209010b544a5840760f40540d600900a414144004889003051800510402c905803078042c00c81d00c98904064409540035150300100404501c410817141070b00404680300b80030409442c000070890f0104078280002045801402c070042c45c0d0045e85d41c55207010429000000302c8070313940310003d1012040000f06041149a03006003001d447d000041c840b200c000341115a048031041e0000b0a6140e46 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 507738812 1250 507737562 507737567
    0x405030a0507030516080c1b0f12030c070b040e0a020405130f0b0603011503050a0b0109030b09070b1602041a030606120f0f0c10020c011706120d020f010c0509150306030313090516 79
    0x80034501d2381d40000c000410824142070040e409440a21000126410008051140d501e0902260440d12004802113070402c5000c91600c000c0b90011a100d80550801d8107200c0402c12070029400b41400275502e483c54054002502da00405003035002400301c99682d030315000d0700c1503c50307031200300440020301e4503000441001c800d21482c81c0c01c00c0160759101d01d207459500c400700d00700d03000760007070b6510301800100040c1058041d004154036514440c24002d03030461401080100c42140d4106848101c05031016101607901048895114008a035143c070224111020301e481d00f422000b10400a00c02c5003600c0e10509070004d440020307281e04451071950b00312420030498079a4541e844c0e103408210550017079289042c55500309640000c0242c8420120100c200240d0300d440403010000000d6040032900d1081c0180030f005844842c081d0341480361402c00c0000200e22081d0103034505005028000c40412a079540c00d2048034526258086d402c0c80464aa031841d400510b800c0d1901070724281c154009002460 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 507740062 1250 507738812 507738853
    0x60702090f1503070321050c190b07030c0c061806050f010302041503201302120f130209010e0a090b01060315172505060a02010203011a030405030a0507030516080c 72
    0x2940540140911a81c4014100444594240c410140b287c14810f411110f00c04014600300207085140c001d40100507070501e602103c0c2c02900000405051503c2d0f550f0740d43d00a1402003181d6801400003844030740d01c03602c140d19034040e076400400b06403c0c442408100d60b019104141600c0c0225420041d41c0e261400c02824844103210003000c2c00002e1035186004048000c2c240c1841202130001d510138042c4007070700c000300c1e441803000100c6070048005004d20f42190703031855a88403092841c840d020503a0781d0005035182105100b900c4100d883c5200042008410381c004503a295030040d801c0055503181c1e003002e0050b041d200d0343e45070a0700d0b9164001690340716030440da030003600198001e0070307010301c00c5080c034074076400382c403010481c5140d00b000c0010702c0e512080c0040c01e10289941c00181c695040c44609209020021034001c055842413040c4004a070010048901010440c20001c0d5a2080ca2409940c5400f40001194100d61800255828055404001c0256111510075506000395072850480005d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 507741312 1250 507740062 507740069
    0x20a0f0e040605071e08060f090c1201051518040609110a140a09170a0c0803090108060d030e062803020705010b01020105090d0c030504170d17090a11060702090f150307 74
    0x60317400c4070100244174041c0e104560000d00190548281e48074150114440000c01c0d070740340e588080300258001a40d0500c03e005800350000f107844c2d00c20081c0c012698040e82c042c10a00030b001800e141c503084800e9440d035009000820720301304180700880c2400c0342c944580d0007419080f0041160701054542402206048849042650300c0c2c80c80c08609101002c0340000702a51000e406108185140011030990011823000f400c94100665407000164001400b491014104500403203043d07480c0d02c002500000a541841c0040c5d87c61510744600410082454100c0c80c5000f0310388401440e810641d55050300100300380ca000b10b00910200d407540004908a0700121400d003000d80181c0742500c0c1c55489141c0c0c0e07503a403a00030b00e0424109601d815001082c24203030f0100f45916440b20214114841d004100c1c0440f0315004601e420061800410f041d407105e00380c0400911510411080e482940e55440c16124000c0d006000c014092600555080030700d601546d100b0301d016241c0d10b1694140ca000140718095 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 507742562 1250 507741312 507741347
    0xd020a09050411190f120f090b04080306011704020d0b09070b071101080606090f0609030c060309010e070602030c07090c03090f06050709080102090f04050c04050913030f0f020d0c020a0f0e04060507 87
    0x6010002c046c0c00080a01c1c203841643c245c0c403480d8440100d0321034426580203c3c080c0d40c0d8142d0b80c3c1010720001d0002c0c440000c0c064009180c800c05c00015035140c00303070042d00c0d6411004440880d641c2c42682811702203260001000c00d60b0104880041c403400081c0e80c00d44010a80780e14060751110000c002650040103040b9600001c820403002080c140301002d02203021014044606100440c0009401c3c0d400454048a1580d0745602c1410801c108205030f40052001c2e0001c0d41c6003940c2541c000d511802c481c0601d0808030388034410740d04640e21a91000d0030643d0032002c41c038941d080c41d00d41031001e800c0c10380b0f076200050011100880e14003410301c2290321075500103250801503404c020600001c0c00c4010030161120000f0300001404d5102c03c00341a00c9501e00002004646c8094540a4161400603640d0010040341010007081c0580000d542d0205107100e00b02814100c281e440007840303680d030719044a03440901084e000100303001075002890059214110a001c195502002180d1903003100b4000c940 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 507743812 1250 507742562 507742577
    0x60f030a05062d130303110d02040314010506040e030a2105011509060e060d05040204110a1e0518010c0c090e07080118030206040219030501180302150405030d020a09050411190f 78
    0xc0c1c020f1b1f00100035140ca03141a0390800503a40741880403a001640b050300d002c00c0101107480000b600b80318090707101408903420803580541d60051556800b500c400078090000f8111800c4c20002c1641240110f15510740c0140100d40c1c42e5000a130b828180c00302600c0200d80007400108140d030145041c40d11200003e403c0c079040803140e1441030f014042c0544280e0300b19036101c1015525003e080d0092820a40c15200e00880c1201c0d00700400324030340700d1401442040303014801203000c0b80364150340d070454043c00d2034008080f05650401600744540c60348080380440c5803803d03600c42c4210220300c038803c03184000020050b0070510074a40780c880c2409200207005030400000a001840c14400411102d0310540f07040c00f485450355500380c210b5400c5810b0a4540c0100f020306000c1681c100a040c034000c041844244541c2416594541d8038058180c2c80b200003a008118884041d202e540101c000340700090040c0702c1440c041600400960110b000c0700160311040d011100c1d4180a03841000766600b00d69035015 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 507745062 1250 507743812 507743851
    0x1e06080a0b06091314150306040b04150f061509031104050c0c060c0405040e210c032208071d0403030f09150605121203060f030a05062d 60
    0x200241410a02254098000c0c40303500c465031030341c80420419549446000801c07141d40c84001114175401400c180480c400401164100e071404505190025441001d4800c2c03510740c0d00c0d110007441a0240c19100380341c50101044414000303a04844100d4580b0300005034541c1d04000100c81324000ca0001424070310104c1034030f0050381002c0d402150710075030381002c0505000a0f5522030b0300f4081d068801d00c101404c0420306001c2450f01d80f1402d0f540c41c1c01100100000440316850b0000e04204100100713484501103a0085014070500440d0800441003440948656250b4074602d8229910700038403420f841084008108c0712620b0341e8000340c0a940d4082015546e885640c02c40140440c03c40c24070806844580840001c1d401030040c6040c0c1000110125140b802c0c10b0a00000c20350301c5020040c0c0b9401401c4426040c090304007102d800c904107503420740c40601c0a80109281000f0320500034800c0c4600d030704101100c41c00001c462050046040c06024600340d007112001004d20954190010120008515 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 507746312 1250 507745062 507745081
    0x3110c0a21020d03020708070f060806040f020405030106080307060e0309240f04091b09060e061317030705010b04060b030f090709050712060906030b270a0c1e0608 72
    0x2030304051038a801c001c084021640821080704480a040380903a1000b01c050107a03001c1070007044081c25440c401e6140003464480700420034040078200c00d000d030b565904066071420032034044074003410002e0001e110980c0da504c95141d03264840c0e4000c1d01e036186890000700c0d45510100803514403c0700100354080d9010502000b04011105c05c2d9107a5038444108002c00007102c81101810003414440000200380c41c07591001115440e1000040c8100807445c4d00034014980c100703104001401c000d490998813245010f00c21016504d0942100101500040f05030f10842400402040d07150304c03840080c0f0200302024180801c0e05e81500070300745aa001800050a002d140b4014903a0180034002180d00e080d545100503800c4403420303540040047c00b5510380a1000d8110f004003c02404400000c000e200d00e1a210018580c0001d0004803000400c2c54204000011150411052140b60815540c0c28852454840f41c082c50500c5948807094040303e40000030f10510300520300f1107200c1e45a17650f0f80d68980004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 507747562 1250 507746312 507746339
    0x40e040201110f1e2b0c05070515040612020a120c0c06050708010f0f050d11010c06020a0905040506040c1d010216030b07081f0506031e040f03110c0a 66
    0x5001d5115506141c03103010350400540700d11440d20032446903250074907110716085c941003050101c0e407841c42d4100c100c54000c0c240d4040c48400998600041c148985182103030400311aa0300441e4448601060006440304240c024811100580c466103086898130710500c00f03a01581c00d0900c0400c0440c10140e00201064001c1742d040c0c009440c140c96607510366610b580407141d0580e0054002611800144804032031a9101c10280c4002c182802603245440e000070129141e15200410a06916031407100030f90240c0262802942e000c00191344801d003040000701820442e20071103204904060100e6094206481600c00c036251503078a1310300c4803000c01140005442d0b240c2c00d142c118481d00102003528544034040c2c03009548505401c060f0350420300c0d001440b180c80905442601100146203d48042c0710f000004110b5009032141c2e600ca558100c401c04040c4e0000544002a01e5080100410803000a180b900c0320703131013a1203010307030108183d480c1c1c3d1341d8031102c00c055900a0b5a5803030604c40d940c0d41010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 507748812 1250 507747562 507747587
    0x7210f0b130204090501060e0915180f06280902130e0f0d03140f06030d11011508010207022803140307020315010906050603061023160314040e040201 66
    0x80540704007960780450111074410380e055034565500c0100b8444446001091508200300f10010048001030760050b110301240507200700c1000d200b104c16601c48090600c40011085003110548405103800417174080c007021a1401c1d090a0110048169030281d000d00c50019090b4014040e45034880f680c9401d00010a071944008140748902404c0254402d01004484d00c1540c0f580c0d03012502d90320b502c25074440035401603c05005035241e0320070040c4980f4002040403c407001d603d1f0007003c00d00001c882500500c207400c2949440c010450001c1181e4805400500e0388a00c20303544220300f145030f1808207102c072060f065048004214400104041140e0030f003a04405107803002968504000c507800249800e401c40c01011100c194800108a03211145c45150b000345003c0d1120391942c0383c443d0004400030300e040d17049400e001020300c080840540c480744c00244e400180d824503540342a807010703e09100d00140005c41c0000d02240410311611440d006407401c4840345007492075241c50340d81c01518800e00c03138034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 507750062 1250 507748812 507748831
    0x1002030f1302011206180b060c1207030302130b0c2a0103092a05090a0603020906010f0e150d110403110609030a060501090207170c0606041802030a0507210f0b 70
    0x813840010700054480c0c50000c12001e03d407150001c004401e44420303549683c0c1800d2160b1014804207180c00800b140a0319104c0046d01c03521341d04d00f05480c1c160004d00070700f1800c2c415003202c40303008514400003100402c440b107000b4080f03841100c41c42c540803481402190b4141c0d1501d5a0386142003495019030000d819092140c0d0300740190b00e8841e0040318a600c00b00030344811141c0384400411284c00e080640c641c001c800100d05108e8141581c02040c10154064600d03810050406d080703c04142c414081e80d100380400600707103054103960b02c3c11384445070860140780c40f142c5d10b03003c80701148104500840701265408111500030f94010410050309403c05045036070035000342210480041c2c0c1a12034940a0610343c880103844184038100700c1c1c80e006100540e150300b420100550400b00078000b450a90050040b03802180150020380046031044140000940501c24400802c080001c0420224140d0f90450f80000101c00340d10031448aa0080040140003071071070400c01e0010450044102e0b41c060030380c0703 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 507751312 1250 507750062 507750077
    0xa051507050102121812030601052503031e0b090609100b0301121209030f060f2910090515030a021e0921030d091b03030f021002030f130201 62
    0x181c5030340b400d90380704900d508050f5600700104402d403010200c0030140c003200c1340018501e085028892540c14400a0182814050f01046041d065040301d05101c40748c1c1214103100070112020315001d8090b160402411009191580c110740c0e010b0454440e0030858080240204c1940d1514000d10040d0030001e0440e480d8107451420109030a115070340154000d02001000041420075824245200b28601c0000e00401480403c01c001040036041c08510098006400044141ca01140b040003072500d5030031504034031140003201c200e018902c61489001c14080c0c0380c0c000714441c4620200c0c0e07001d00c4d5000e09540241c2001c0505034007450b003005580d000400c4480140313481084680ba00765411050716443d6109800160b07601a42030129019071014000070b2072400c14041641043e071070b8050301c0c81c00b0003c0c40e82c231464141481411100082014410030265512903120305005042030500310034000980b00f4803a070406024918030859208008403002c000c80da4441c2e070070b04409203030440401c1c3e0400030380 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 507752562 1250 507751312 507751327
    0x30d0b0328031d131503050a08030a0e12070212010b0901090f0e07051f0c0f0609030318081905040e0a0501080708030c0c04050c0d15080c06090307030308040212070b030f060904020a0515 82
    0x1080344000280c02181e10580324503040c105a0b0a64458044208cc542c02c2411000c04a140361030645a4141d4100d4001c0b035815400d009441c01800751280960740802410000a42c0e20700540c8030b886101103188090003aa008000c1207607854107180308240e009036031852284170801941c01a0350141950346480c8402c444079885554032221419402e9803801c0da180c0a1004054152041a8400502c0a20641583c0150310f400c80c0e540a007001c528815800c0e2a21111424420070442c3d015040c40c2d003011400d03003400107542c1c00400c2c090140385842e218041d00451140700c00420360380c280c0004401010000007210034000548005801c1d044420340510400c0c10500701c6d8060600e4040001c1c6041103031924048885140c100c140303030094001c038410400c3c0012502d02203016001d0f130f501030400b00241d454510100342c07400c0100c0c0c690745103070248040201e108050000114060f1300031f41c600410f2515410304200402809540c0290b001350b490b007040110b42812500f41d0b40040985403032900701403c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 507753812 1250 507752562 507752573
    0x3020f13090602030601080108190b18010207050c040507090b1e04090c11010b0109030b0f100b0a080f1b0d051f03060605120f030d0b0328031d131503 66
    0x304418100e840b00d0f000700030030289580c80013100340146004c0c2c00500803c041503504010942d041030014000380551000a0034080040e01030048804207034000315680e00c501d013003168880d54080c4c04030384503908120105074040c2c0700b481ea01d020740328030150079480c2c080c00000c07125284c440ca4481d4160401c2c20f0100007081003d0f40324483d01c500007600c07004c4220190310b0b00242110003c04140d4188412010244003080c10729449503408012009804240d80303c10140d4070100e400c60f4010001038000244c0688210f0340b00c01c0b03044c0108010422351017141ca90160b014400d58045d001c0f503070310305800c0c0710644840711039400c45904080f040810000580081406040e0364000c0e400665a46807640010401410700807510700c0c0d071301581c2c2d002e01900515104019240c2c4107801c0e03110b00300c54403520807602a0b5070038890301c0c4034108a210f00800f130025507803420041d0041e008059012500b0403040f680360140e10410840c800e54001e143d082c03081049000140241220381c8400710680710103401000048 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 507755062 1250 507753812 507753821
    0xa0b010c0b04081e030106050a0507020a171f0204060507020603040c090e010c1205041a25080f180706140706020705010e0f0f070510020f0105070e03010b0111060103020f13 76
    0x43c000c0085540e1906442040c0c2001046511243c0001d03c0800c0108403543e404000d40d480740d1164500140d41c0c1140d400000c04060f01500004021b10f226041f0720941c04d400184514044a100b50070750200c80b25000b904102c0c0a0b034410070000c60f00c100110001880c00702c0045500a12134800e500409031510204022148050304c442150b0795681c5d901008143c001100d08280c03017500c4000d01044c0b409035100c0403500311b207081d03014103181da000101c0d40d041309840b540c00246048403410981d100701000014203c1c802074941d50f550304a01c4010410a8800000c3d03103131001010380042815a241c48400c4440d1401403180c02d107500c44c240b00e02c40c0002c445000403c0040c0c0507200105a403620103480c0360030304108840b00100360b807010700c3c1042440000301e452400c0300e10845200c1224001480e0681c140403108078450400e51902e8104030111341c1140108007890401d6000300320b1103404000554580c580301500f01902d500800040006103800f8241242054018000c1c1c1a0440329075580020784 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 507756312 1250 507755062 507755071
    0x5031308070f0e1519180b100c0b0115090302060c1c05190806010c12021506191401020102090901150e0f0607060f18050303090d02060f0a0b010c0b 65
    0x15044044100700381c08049600d07002070203c94424003101c2c1080d102c0c000b800b40740a501d07180030319061104441e1001d040c0740008020300843c4d2010044400045450004101802105202e41c41510036600c1080c07044c0002d490030307540841741624690038401421002c10703441c0c09101c2081030168001c00140c0b01d0703102402d451000140100b00034030144118403041c1b440860550208902408030f03100e88900c10344c0b0031095480c2818960825164040102d078050b100410181c103400b110b48850080c3c9500103800041c07940b41c001c1c2c0800e80e485050400480c00c6030f00000001e00d0042c4603040c407c40e6415041d41142082c140001880c00540002107100c0c0f4034241d100d030f0114401e035104c00c4010ba8004400501023801207030b640700010b24940c00910540255040a09a5561030300c003810060403030351040720f815500c08654100340045107843c6503070f1750045aa140c2c0b10b0080d9803c0442541c000a12140234030040030034020710340c0e01d40c40c40350000c0c415010114100700306800c1c0c240100301801ca94500a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 507757562 1250 507756312 507756329
    0x50f01030b151c060504092609090115091430010501060503090601060203092209060518100b090f0703020f120601110c010f050d060b0408060613091707050313 70
    0x300e0180400c58004c4884551006015a0a21000000046140c41c0046a0030090402d940c540000041c1c0200c850007845d0750300e604990010008103440090720b502c115403481d640d465820792500e50a50f00c2d4003000c00e50025802ca0348043d502c40440d01c07683c1002c4080911003244842d401040c0c5901da09550003a400311011902c00000d218036118144101405810203000445c0b6080c110000b00724003080340050341c4041c2c900301c1e80718408003c01e60011444243c00075014042401c06924000284940d4004403103d840b6400074801c2e41d9203940141234126400034130381b0b8103d40c0c400701c8043d83e800006004804040d401c02006020140702d401502e88030480a8182100e460400b00140405481e92601080381e40501c09000441e0b1f4043d94400030408945809504e80b1a050600d0b400b8000350703004010740c01c00204e03000c00c00d00d00c00164144200c01c102c0341c9800d10075007005640c00311840024041c3c5a180071151ba00e03400181ca100030441c00e40f141003168980b00d2065684520f44085400c01c650 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 507758812 1250 507757562 507757597
    0x3200f01020a1e08040302060a020901020f0d03060501030b09060d02040b1201060e010509010b030f0a0e10320c04050126040c030210050c060a0f1503030c0b010f050f01030b15 77
    0x640e40b480d100500c1c003d000030b092141d6507050948000e5541c0d0303c0103008000312600020107020030f910078020078000107110401c0703484d00c0e56294400381c040c10490180f907000901d040c1b240c810500d40004103a00035040901888209642ca400780006080b81903096600b10004803015800001d003407013904010501230110f01030300d5040c40100020004103a000e4104020244244540e0f0603c2c0c03580c0315040a41c05000040104011100d141080e100308915842c141c5032088440c209035440d0744c1d08101d00002000400700f5503c0d0659803d4245c0286c8071020303a85410f000c01d2110394012400190b20441030000a03154080030702d8114031090048070b0440e007201c0d402c4c1007041103003402c401c48046001c1070b0414038200750541079180d941d08801040c4440702610b40420000c122120343c0200b400316040e20310265190303242d00b80908040500001100e480390440000900c07072030780500160030f40b90020a02540c40c481500114040d0101036821540885c13104144c452000c0104000e10312100084102c41 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 507760062 1250 507758812 507758837
    0x804080105061f050a0f0e1203030a0b0a0807031506030f030c060507020102210c070507060c0c06020309060d0e15130204061a070b04030e030613150903200f01020a 72
    0x90400315102043d624100e09005040d02250460309031420f200301c518040c0b0760891103860844201d10802400340d00074501d0503000300306040200007944159001d413414000c17080100140424409241301b024001d8004610500000740d0020540d03800442c50100458115120f8969425030401c01d001100454804202d203001c000080c05440da1004040c0000c50800c01480101c000746945c041e0090313007524505000602402c1c41405452040d60014101c2c1c40d200d4440380701400d030b02502c4405483c6505d261302d0008180d031000086070220035000c1d01e058200f18a2200400180c05caa1004084074020041c02c800d035800e4103101d051155803080b0002029110038010b000807518560010045480148601000350b802c0204503040203900c48070f1502580e49a060445d440011180c41540c180266000c1c0400c001071303044410350346070103a03c00c144201070b80141c45084070070390b490040c04a810b02aa60302d1a82c140005208005140d20607180116142c0c40041d08990001c0d000d01c012405202640 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 507761312 1250 507760062 507760069
    0x12050c0f0d260118110c01060305070317130b0c010f0c051c0e0c010c02031005150103060815012c13110102030f090607030926010c02121c0207080408010506 69
    0x302002d078031205454140c0d50601c000034000503055100303000e1075602c420680004544030004c84002d41d41010007042000d440c0d2600f6522000b00380310a83c0c50301c4003030450581c1c03000001e044505100c070381c44170480c440380f800ba5038404031303007100c841409075550b2070300080c403441010f000740d6010078000c0e5200760ba280c030102c542070190480b6075801043e031f40c45c00c0c0c80640342010000d1451090b95003420310032640710091001920348104044940700342c034102028400112406001d00d0181d0200b42c030180502c0c2c1d224288280c0e03c0d0090200769035030441020040040034a0480101d210a1002d64000f6480c46043c0321082d9071581a5075200340d50346c000003104248a4101c02c0300209503424806180f5101c2201141030b001c3c0901c2e40c8492284500090003000c0600407084c203030040c03a160313004400c401000d80b0440c581044d1240d1844c055401d11043c00c04807880410310800c44982d80c1c2c030050030300c010b01d03275036110382d60480290724580d940c200043c4011650031005000100a1702c0c0c00881c4a2a1503c1032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 507762562 1250 507761312 507761357
    0x6080106020705150304020429040c0c031d01021608071403060708180304051806210a06150905091c0f0e04051e090312090a12050c0f0d 60
    0x320085411000d001e00c40c0e580d404082c44509000004d074141c50361524000240100489030301c010025a480304440c040da0011686010001e004907810000180c8000054500c1c8080000050000781880e910b040c000c807024512352000311061045403045820058000410b54464020000341da100080c10000c0c480e410f04140745081003034015001600b492040900072a2002c0c107488a901c0c000e00348140307452000c1003030b24011704d401008003000c4540b0241c1502031001c103464040c0034500c05c4644036407060203503807a10948500c04008016a8440d03441d600300404002000000c5c1e11990700f00064410158041c0314054042d00011700000200d16050301c4120015200d44014851f80f5652130542903004143d84580141c2503401054640d1812080075020301c4044040114400c11028030844100001c007400070004c0a1104400b240c5070030005e01c0e0b54403142100201580030740c02c010b42a40e40b1400103009408c0484044074a141d144442403820039241042100000351500001a5001840c0c01d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 507763812 1250 507762562 507762569
    0x120111030718090905150c1201030c14030a03080601050a0e030111040f1401120f090506150f03011812110d030c0801060f09033206010e09030f07111c0309060801 71
    0x1002c0040a04d5542c41c2512624881c4043c80c5280880002071710103940e900072598075084503186001c1d10340c2c503440c01c0a01c035402402524050488104003000302c0c100004d01c51a039981644038070b0350a030b50395401100d40342d10900c0d65000f084242c406902c02c5031024094170250b0f6526005050b00c072800d01284080111950b4840c4041c0308041c03a000c507299800041d4030920410403507010880d400d403032030b10b503000e403055100003031841c4500c10801c181c159410806040084085941c010000f908070201800c0c0c4d441d00b82e000701200592103402000460383c800b0003000c0718040c01d1170522103100d410424105880c203054400440d0725060b0070020305500c030718458094040c501700030314408a8040300400301121800f0003460b5801444c4800100059018003a8030042801ca5040801c181c00c5e25090300c900c0203108094541941c000400c8414202000740c030041554030701c205040c607400b074a4503014070034491b01d829000800050401a54489107401a855034001d854181700d013894214001d103030f0f120591 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 507765062 1250 507763812 507763829
    0x5060d02041707030c3c050a0f03080909040611040902070224070605041b060203040810023604020a020102030702071a18280311010c0b0105120111030718 68
    0x5030140300040d45181803a060396104000d0a200c410358849241c04031086d11041d1200d5988460401c40905201d40c40c41c0c141c8200799490000ea07540d42a86890208440c040101621380500086409003000203000d68007a000d2800421810038205000707242c0e138802d0b00060881500003c4110550901040301c0701c501d0f4183c4100c010401080d2007400c080d002e2030000510040e100c0e030101d4180a82103600b809512480b2076008401503440c18040e6503a4014420106580581c0d078030015a124203100b81c840700c2c00301a1f0603040c40500b1801a400d40f151a910008650445a0824800d40c82d18030181c032101810f600016964103107010064a02a19684070b01201c0c10a1105540030b002c2c24016504c6030340c5e00030030704903929500c04c00080c003100c0f10842c1214118610000b1070b100d03000c00c1d035420040380e008120b0444c003141c00000444500c003603c08080c0c01180280010007182c00c00e01c8c04a000350203440000110140b41030400f2886030720076140080021074000180d90f02c42c1084450000511909 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 507766312 1250 507765062 507765073
    0x4031403041a09072d332102030f06030a021003020a03110304030503041a0c090609240405040605010c0b0114010908070303021b03030a141305060d020417 68
    0xa035100400c02d1020100c0b80c1c5482c4a110204040e40010000d02c0c0c0580f41c88105454003044074520202d844044004210300d02480300000603504e034243e0108084180d101d00624859444013002e0302c4006000f024000420001038110440034044da4079030100c500400d1000743c1d40f428800d0394501c00d45030142281c0e00c240c20641603440180d6400c0e402d00c5408042e42009a21203444020540c010300140f4800f110b000700000c1007000701940301d8011442913205041d60304286801a41c503000060049400e2240500c040204c0f140a24054000c1e01102c2c0000380140d1507030015520701ea407480c00501c070809040270042010b00441ca060301511010f058280b03007806c480c03004c139142c01c2c04110061050444400107036441c20303141d0744154000c60107050351508681e04a03a0780e1030001d40c7c4900f06840300c0b0b02d00c610184501c40d18034000c400c59807518440d50390700105020f0321049600507401008100f4180440303010004840c3c850001030011f03023404080042e00d9a01d816083e014072070f00ca007001d5a40380c014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 507767562 1250 507766312 507766321
    0x304150f05030925030c0e040c0e0108150a0605130603060e010209090c0706110a022103060303071112010c08040c0905010503060a0c120e1b090108070e0604060e070804031403 77
    0x40e29000351381a4801c00000d4101e61000c440307101c15180c0016101206503800411749404a001e914081c0d84100c4c03944050903603d81c005040f07440c1c01c2c040c0c901560044000811548454803134140c00c0382e6800c200040460740e8200103052400074441114051707440356400c0007403020300e11500b016842113900035407910704450000740e20b15900501c203405003d4081030040a00c2400d503c003c902c10f4440c1c07400c42d925010030002964500d0841903c0c03252240d03089804513240b180c07005032809a10301500940c203058080c1d582c10062070345001540e4000d5441c050303034040943e0034003030071118404640320903c3c542410700f0705c6a00d4440302e80080110500b0070004001980300050181d6000c4071002c000200002e10000440b00250800381038660b9904050500f0036082000c503800601203141c1c099880c40904000512200d00c009104240483d00b081c0420031201c0401d91005034800401040003070101e0316019040445142912134030005014902048101600420500d10b030a60320b10289066140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 507768812 1250 507767562 507767581
    0x20303010501022a042a020c0108040b070c12110609010501030c030206031306060e0609070e0108160c2307060216030201051803101a040203040c050603180304150f0503 74
    0x1101801c901c82480c4d000e000b0060100136100740038041500078010322112084132041031030851000e090480c0b41d0031000700d03001114000510176403000010384806100c1c1d030303454440c48045180203003d04113100c44001040c00250f07440c981681d000205032110721070b20084c2d21056140a5004120039100c0e031402c80184041859454040200c03a411581035940e9a101070380705c815403043c0080103122a040c0400130030f42c412400c0050744100001d59070001c3c40d65846600715524070841ea1260701042d070300d0011400c808140755400392171300310606015040000f80d540d04141200d05505000da02400721200c03460714034003441190018181c03032004082460a001c402c20000c02e5031300c8002d05001d40041c00c0080303c9050b902d000343d803100040c252082010307468591009094003041428803140318450489180c9418800d40f4050f54001e03003010519401d1070280001540081d00b5134400c2601c0303003208004c80b0310400091001c0d003200c1b17070380f40c0c4800007040c0c015140b0150b102024042c000d00780100b020504 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 507770062 1250 507768812 507768823
    0x60603080a030b03073f0515060402070f0210050c06040b07030e12120711100b03121e0307030207021201090506060607120804020f0402040608061f050a18050904111002030301050102 80
    0x460104103000250500751503008000e405000b1040c01b100800c680e0040c8100804d007044440014444099141d0b95941007100b24881d00c40010242411551480c015081030000d050b08001c42d41400341c070300040715640524011046804440d4a940760f0204122164140110f030036410300c00b00208070354006446512501d01500e020304001c44018000620014414010081d038000344806541c4030046034242e400c0a000000d255601901c1400b40110f04d00c01580c080340e07010950a085100b40c1c003104c0d1303201c0165038005065501015001d200810260781ea02c00704c6100603a84000005201c8140e107016410803a005191521910b0140601404140003200c580e10516442c42c0c2544295100d2001134164000208440e0f0814404a00425400c2e000882c29000340f80444856074160024004c0407490701521981800041040c0940a407050184c5003240740740c500301d06a41280c58032400441c0c0d14480481c1d040c0d0307580d080410800094102020fa1004101700b9102551031507042c1800030f035484 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 507771312 1250 507770062 507770099
    0x7050a06090e0a0203072106380c1203041e0b0a0c020c0a050111010902150304060506040c0c03110f06011409060f01021914012a08010609060e0402040305010f020c07080303270a060603080a030b0307 87
    0x40bc0700200003000c00c0030048010b10101450110209030107010704114000100460300f188200c3d02d4090651809400000c00f03c6000c0c4c2c000301540c42c03003820600112101080c80f5030250b055920b0710320300001603440307a089080008103d04c855880b40780c40d0038050103444000d4001801585011902420b8583c49851408020340508040c20041c080c0801549030040c11304083c41c031030040713400100d942c0c140310340c0342061300000701c0b00c0b80b10301d4403a6000c2220920701d05006e01c2c05a4402c11201d001010040d4a208240f03010b8803a010103252005102829100001d00c0500344c0168496101c80701840155014100c01d601d14020816604011010340014000c8c000c10b01170201e1050220104d50300d50301280d01a551010003480b000d40070082d144080d40026000100e90302031444045000070001042c0c03441803640b4040480403900000c1c0030f109040030000070074201e00a90420300702103007840c01603c00540c0724404c420fa40e1b4000f850004d0450300346981444c429000700c8000c10100c0c0d02d81310030041d807 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 507772562 1250 507771312 507771343
    0x403090b180d0302030a020d051606111c020d0c2f010906020d0504030905100e09060a03050105040b040209130302070b0c07050a06090e0a0203072106380c 68
    0x4a951601c0003100302201c8110042d03001c91650707290380416034040007034030400c903154088625505500e60207480d1400313400c1c2c1380004921718010722000300d20340b6085070b4141c00e0106259840d243c1244074014806443d010524a9a60000b84480025060b88a40d8410f000309140102d4104900309409000f00358200c00d0343c804454000204031490f8080d070103e0304e00740d40700c601150784035040b01d030350b20181c407007202d0980100f500c0301e0000905052004050b4601e041a07a80d15210344810313410401100300160500e40c01c40100a400700c00100d00b41700e00d41c01345008144262051405104010640100400c0c28065401030b42420340000d40010b030010030364080d00c07000317500c440c02d42400600d421443d03401581d21510300000091150f400c266001d060340c14005c84800d15a5030a150102a840107a0f00c0c4d80c0020301d036500c242100d280070945e44400089280001c208550342740010f9002d84020754074412518164111141502e4000009002582000d4071040c24105002407540c0c072000d810144508 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 507773812 1250 507772562 507772567
    0x4050c0f04020f1303170a020a060903021f0b04050c0906040b030604020724050c04030218060102010608030307091e0503070302010c060225060b030106140d150e01150e0403090b 78
    0xda5595015642d100b40b4000c8826160311604502070440181e500c81a5480c0311178061745007a5030340290440310369a030307150000c204031803140c1d0b1408020b051001c001c2d000c40c041d949001d116588120320308020301004a80210b203071851741c0d041000b21140500030350941a4200080c948980b00c2c40c1c15034040310b0b001000c0b5601caa407032101107001b80c03144140041c4202c01a5401400381107003100b000c1c440a1110404000607540c111403526248030b240806588040c100d99005026804182c81ca40d1004040c40045022591080214030b541c00c00d843d14004915800300a0000c030100720409140d8982c0b0422803a04286040c0100e910b0b407100340006070400031080d110100380480341d0104c03910012035000038891450318070508280b011001a044459a0901d000f0b080d807845c05004500a440f1142e02d00e12121407400104122401450401c40d803404400c0c080d940b84005602c03640000111000c0007265481881c1c030114112606600100e9201c04584184400b01341d1201043c000d031030f001c0760084d6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 507775062 1250 507773812 507773839
    0xf08160f0309150e070e010b040b03040812010e16090b091908030708090405013302070806040b0f1b030c071a100e0618060d020f031603120804050c 65
    0x2009800c90350b07030140a018100140e1803040c0850741c886460816000700341d401741a100d40c10000011001c0c031503900c40080601040c050070155000842c0c109200e1561545061010020082030b084240e20450400110808100f40001010715500d0a101c0358a007120f90903041040c800e0300c0d0300407842d46601404130309542c428403141503440c00c0080c0103400216601c1e4102c5240041c0c1d5940204c1d075040c0180d040000028159a1801f84d40103108250000e01d08a10303603544690011001c60315555045104a902c0040c0b2013100b03001e824026402140c2c00740e03031031510b01d41c0b4518201e40071f800c1c40403119050440803604907411056039000740700302c80000c3d500e40f00e90a00d0003544400d02100d100d45078600c0c0902500d000c24200f00002c59406082480c0c5998962041002c10740031f01c03450030394400190001810714900302e43d200500c2031000304443c002e4148000400e01c1c00c442da0904101542c2c8401081c0140550039024918640161400c2101c83c0307820759406c0d4035010051105800b80c1d40010141 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 507776312 1250 507775062 507775067
    0xe16090c02210a0207051e1005090414010503060f010e04080913020a020f010b0a140103110d060303080910050103080f030403090e070309060b0d0206070b09030702031b010f08160f 79
    0x800300c100760341d0b00da081011a1907640159015412101c0580300e03c00d070008440c00e06180c45510340301d02000c214114070548052200341ca150501d8601042020810b403002c0385e0b01c41c0f04a003640442c107a013407691503041ca401e0606d03089004d02010002000c010041142c0c040e2408141d40c071952048070f043d2100f010101056402d1810401803140c036001050050202e940010030f6513448a01e034000b03000c421099400d03c0703184541070041e1101c84414003000751f100c2d402500041146030403410234a10740001c0084500444e481900200d0006804100b032101c071010070410380303000d455100c004026070351559555900e9407051083e54044c14401100040070305004010308401400d10f200421641c0c50010385c002c00401c24218102c5269242c00601c1c0040e08104071030304002e990140000d484c050b800e0300c644c0764cc0c51009100703205620041283c41c00603101840070b900c80c0800c4850407094885464005028000d080c402e820810074040100069490b841b801039508542a0900b200350f8070282108 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 507777562 1250 507776312 507776323
    0x90f021213140a060e1608070504090201020c030a06140c1c11160309081005090303061507080403030302040f210b0a1103010f09110315040c17130302010e16090c02 72
    0x240382c0c8901901c2d43e180c080c06910f03000440750401031001d1300c0340078182210991541d24a400b4100c03140e4400c010a0101e0b05040d4000161140140100c94281038032900013481e040c00090101c034130742c0e120306030943e400701d00301c0c14a070b00018100070f62400c000368040c031288140ca07580308484029888880001171000c141d011560302003a00088858030002070305003e0f100100510034080c0c140b181c4051100c620a0601ca064060900c00c40035618540f910410015500b000b0001500d2061041000c1c1002507000700c000c1c0000c1d407081d02c015845600d800251081200994015400d14a81c4201e100d5800f152000c00c020043e44411580c050b62100d030241030081800c800d00190401c000000450b0f040540002070046805a10040c80201c0d4960700c1c2e1145404252059108869404d21f032103c44e19003034011903440d458030f250480410b15903c18460500c0000e90344240c4410a0b00c3d041414142e080c044c0002c540744000c0280001c0302602d424200c450702d548210001265160b00c21031440744207128 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 507778812 1250 507777562 507777593
    0x50415030c050f07050705031204030f1b15020d030c03020304020927150603011a030607081906120203120406050d020c0c061201170a020a03061e15090f021213 70
    0x89030304d42c100c4c3e141c0140c0c0c0300b2090140b18420311a01c0b03001405182d04104903015a0740c480810310000c002990b034440d080c500e1216414450352a403501203442c000f480500003c050f800d50047c0210b061910000d02150030141c101810140100100405611030303200307450704024055124401c00c0588040d0254601c01a220401c1c940201c942c1112544091086207000c0c500032802040158002006c03d40e4501d9100041509900b2030000103090502584885030310036001e070000182203092141e01e900f01d50580d00507107400708540c0064015802c041100044202c014500c591900e820000c000c5e1060080c521500e40090300000c2e0420803e8003070180f0f04104070040e2071261944601c462202c0b1812090052491808400f5000001e0000000b00805002e8014210b0100390b8155100c010141460303050401130035014100d440e24216803485201c12341c10502c03e030007102c982006451030a60724045c130045c000d02c0c01031001c111860b030302000894010050840013040c804440ca803500e04040da00b00d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 507780062 1250 507778812 507778837
    0x4090209010902040f0914040f050102070f080714070605220801140402030d0206040f0201030f1805030d06050303040b0a08070207030803040b271b150c010209030d050415030c05 78
    0x200005821007041d0044d00c1501c8040031040da40c0d540b681b82c4030040b10140407805840c110810041000b262198849070380d111300400001d450719005807130b50210380300014402c41e0301400016001050050043c0c03d13006000e0309402410f5501c0c0b8009000b8210300884004240c5014410f1610300e0700000311750820000c04456000b4000c111103200800e40d052022101640070740036401c48202d00900c0806c02d58401d035400400500d81101c90f40046000708100c0c20286e0b5080c0c0e03039001060b1400b651480c44450f051044000399541d0107807508900a8864503030156000344e000b44414400d6409030002c0d10110b000b185082540e55039158000c1749007a48070350010f0704210300041070000340103028003241c0c81000c18041c3d10720201c801481194410204e00140ea080750030044011294a06c016001814108000c0c6043c044101d5910300c1d5034107501011080c1c0c010307076002031070b07035000e040030310907907929030f81505101d4105854070320f038030590070b00e02041202010b80d50030070070603140d0103002911008140c07076 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 507781312 1250 507780062 507780079
    0xa0b06120c0112090c0b03070e03190b04020d06021b070602010b0306040206131205010614010509011b0302010e0d02060604110307020d120603080d09200a05011101020c01020a09140a0303140702040902 88
    0x904a42c2d006500541d00c0100149034038141c0945c0b422b001414840321000302181d549800d8542c4c589070a540da0181007264005198100c00300420014006080703094041e8421140c07004405803403900d0070320700358461000e6906040c44851155000318246901940641d82580d44140c0e08a00b45901d0009030444082d0030780b00d01050041c440150b006509075101c140100c4110030802d00103403024020714180b030340010b201e844420440890074418455241c82070002080c0da600910040341001c40610000f00143c0c42842001011701d86401002c440e1500f94200d64a58181280000e40b00c100300c0504505004005012484000700c9a03c010700554000381d9007512013280143e03e0340a0300b080e01c0190b030300c09407814072101001000819401c0845e00104603c032920301d0200107442e411070100480860b07550900141113004400c2c0014903441819503180784603d810000c41c03080c80047e110599000d08451401800003c0c0c1208020041c2100c2c6c0100c1074840100340b001501615003200000d401c013800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 507782562 1250 507781312 507781319
    0x21306080a050f1603020d090203030d14100e0708090c03070303052d04120305040b0c06041208040803240a080d02010c020c0607020108040309170a0b06120c0112090c 73
    0x2200c401401014104414070154480e00da40c8845404151540f02c0a00020401514281d009500804203c1c00f001d40124004801741c00003800d40d040058808555500ca54151100b01d00c041c204950200c0000c0c1101071180c242101d401c1c3d007000041040040c4100341020400203802048101c074000402000c803550b03280c81e03203801481c41e00440760309604040020750801c1901c000a2409120700c03101c8401c0350900c0d28100000720b6107080c0550540a112003008003042101c41c0309c000780200c0085800402180c1050310380603504601c0b2000745010002c03c00207200c00104000e084a4100081a55400340210010700c05c0700c3c800c03450405180c3c0584c00c0350700040c03015008a038650302c03e01c0d42d400810030b0101c0c680061780c07140300500728168080d10400c041c1d00198050340485400902a241074000d0603100e05066041c42540081d000490f88400c0c203190801420003071150f8420025104114004401d03048184e4400034128007030b0601c0286c070302c03455282c82d07180d0110b4007044d040126007003156907 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 507783812 1250 507782562 507782567
    0x1605130b0307170112020d06110f0c010e06101a091c050a031808030409020313170c011d0607080a0b1018090212071b06050702030a0e041112040501021306 68
    0x80fa803481c10668074860b0001400c0158452000c0c0c969402034011802080c4d280d13100c1c00100103901e5580301200f014841c01c0c80c240c80550142400356013002c00000d500360325000c0903140c154000e0544058808c1c802061104850112400703007420341242c0c43c075442d080071200281e0f004001500c0725194403089202c0b05c050003000100c001006010752101c12003441e0060454004680b00d020b880c05681c000c0204000d5003100b50300856100010000c40d480103802541d40000c40700c0e465004080d84600459044280760081c40b41d4201107110a20031424103010890050b01c60718020000c500b4041010005603142d10107802044100ca0001c0420740341000600c4060002c108100070009840354401011803840b01038821981c2d00c150602850042d035440c6803084414280024100a90b50b00320720345000018401e02866001c0c2280350080c0d916454524001032040d411080064400d41c1050400f802c070032a03200460711840c1c252002d0b554503584030f042c4980a03100e4a1942500e04030701e0b41d00003c00c0f59 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 507785062 1250 507783812 507783827
    0x4180504020f040506060a050c0a021903060c022803210903170c031b0705031c0b040605130f02090307141002240901150b0903070e1605130b0307 64
    0x10710860b40308010121003014003003162000c43d07aa5030042002c001c80000d07640102c0140000a0502e401c980c0ba00e400741d40844e4a440030144810700c0c103110903505204000d800d00840ba10758549100a1600c404680394401421070025850001410034803184414544a0002c05407010110b0b21200080101ea000c03e2000b08000d5009900040307412412003808014102c4d5540074038001141d090460311501c103005e141900d803460f9095280c5041068200040051000d091a4503500175041c080d8040f050814055a2059407580d118a2a00400703102c0c039507840b11061000d800f04040061302d611a0310b1248000c2c81201d80180d45845030a074005100107012058103c002c200b80c5200740f9072403c02e0b005995810010840c0c0c1076400d4940d2000c114245000301095008502070008900300b1600314400110780456000741c146e1207030024249000c6e0504011000c0103103880e00c0800706030300e81021070b40900821005407004110000030100704201c04014000081c0c0000041c0c00d50741d041102c0c0180510 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 507786312 1250 507785062 507785071
    0x11b1d01050d0e07060e0a120b0a020a021c0305060a0506070201080403050904021608130605070f0201120b04230907060915051b060106030f090b0f07020304120b060307081f0e0102041805 82
    0x4161f2000049800100316001000e01d0350300c103d60f94480e0b00c2c2d401002020f500700c64080f40442c4944030044415810b900c3c0c105045441d943c0b00018a03041c0702050012224060308000e024840c00c215400041c5d81c405041540f050700b40c5404e54640c2901c10001e8040e1150062001040c4612070040c028031441c1001410758001034120f2078841c9940d010203691900501d40060708181c80955a100994060b03e18005101411303000068078000c000c00140c2100c840640600ca46600144c155504000100090350040031500007059a14030300140100105200d0040c2c02c2c2c0030303070500b2088081d40e000318103482505040c0e12140c0500550084415500c5600f40f10358000a414601001a4881d491080c45402a001a44a19036545d07694682c01c4041003c0c00b0003086120400c40000c114458003100d1030b03403a02c0b13214112694101703042090310701816500454081e40010030011109155608101030f669007010780030401c202d941c0c4140c0c0c024011a03101e1201d0b4004054070362480c0f86280c0c0300c14405c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 507787562 1250 507786312 507786319
    0x10e24040f060b041d07141c023609130609080c03040b0d060f1505131503090303050f01060905211e0d0908280204020c011b1d01050d0e07060e 63
    0x80341d8620070211020b0200d03034211f440700001000f4412580420460842c51446600342c007626200450482c00e0084040311000f00c659980d02c00104e040d007001c20100d155854088034030b00f880e41401c498070390503a00e61040050002d81e030340000c942088207070310590b48408110401c0c0c81d02c40d581d0b1403140e8401da0052042800c0546404804078003061510b44040035564801102405030075202c5050307916030300c044180b444039001440000742211811410205038002640c1c00308100c00c0300c1c68083c090b00c4000e4004005010030000500109a009000008641c0200c1c2c5c0c0b09072905441c0c176400030711b0340810070f0711006003d83c1011a2490309100300c0c0105280c0c00c50300325900380b4158503040342c07480c54600030300031a60060110f40c000107051180394003911140203280012200181d00180807079102d0006090181d4503000741810508078408120381c2e80700b580c1401c0d03c100d04410b040c102072541e2481300300d060090128002940441c5036110102c45802d0500703d030200c4c3c1d200c040c040d022000700d0380203911 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 507788812 1250 507787562 507787619
    0x3020601060519031e150914090307020d080712091d2403030903030c0c040501050a080a02100504090507020a061112041401140f010e24040f060b04 65
    0xc020344550111a08440c14080c4600b00f80f48224040340079002c1d0411080401c131200c00806554505d0307100b071134500030f0031303004c400c050301d2601202a00f03442445802d510034540c0f00d070800c80c2d40b6402100b2902d9040c2e044440e040aa1550310302250b10f80100d01014141c81d085030302c10000c081d006040321041e201a04010000740101e110b442c0040034044400300d40c440350064220103505c8204a00f903100502c014141c80c00c1c45101c070f000c00d2440c3c00038120441590311040315001c080c103080c40361502520702610b03202c1039181803013810303540d9407003c0b140280140c030f1071521044c4642c81071050398042c1040100030700c150304000718001c1d562103080809558031858070301c8944411041404446243c2c0c2e8445603a4032036681d50300c030302c8105603031b51546181d035548a0f000141c00303003004034541e40300e00304564040034a941000644e0010620051001c4000304203078140b0442c0c1d6042290b08a140c02041f1004100c424001d01400040d00455200074403c49021902242d4011080c224100c2c0e00c01100c0c4408 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 507790062 1250 507788812 507788819
    0xd05040f150e1b03030d2a030510141503100b0a0309050d110a0f14010e0304090e070b04140a030506010602010903030b0a0b041e151d0118120f021c03020601 69
    0x1100c103d15043c0d0703284d02d070f407003000315080f90681904010424091401c1c882e07845144c494440410900810307419000941e80ca08111089003007481c4203016040d04803004454440c2100402d0885d5072400044000c40740210000320583c1c02c4214001c040c1400f841c44ea612202103032400780213009480000c880e6030240e5080440117902c5116141500301c01d4100070415500c1903103904000c1704c40c07190152100b4180f0440c000904009004189003180c00100941c2d8680c98551000c00701e400e04100240140c110f541e08019058003030701650251740e01c4030361000344071140b24001003080686500081460055100001d80c2c1c0e60190700880072039000e03440a214210042d000c221102842c1e0007070f41c28081c0c05000502c02403030039500000f12202d889259507004c40e262041244210030100f070041c001002e01034120010410951002c551400a080020b071074006854001001103c501031108250b0741d00341c680044c00b41c901100b0b011160060290a402500d840550040e030407045001d5015104650001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 507791312 1250 507790062 507790093
    0x180d080a0506010c0b011701020c030a0c050d050310050919140105010311030603070b0c1e07051305251404090b031c0e0603060d021021020405060d05040f150e 70
    0x51318820f5002c0207800603a030030102c031300c440102c620011400b01c1d982402045c4540d001000101141902500c2c0c8141c07414040c500a403800303805440402c2000701c10700a00c844035408444200580d00200ca1a500c1641ea859207042120701d4400d40b00409803c1070f07200d420150765a00000d06a481c02e903020720112a0110344541c03a44810b036907682e01603112403801c229102040010f880f181468605692200a070340b02c80060800ca845c070f40740c003141c11040d42048149002051800c1e04101080d0510007403074418908816030400840900314100030b0701151001030321a6200280e070281c4020b039583c90711b8507114050000c00303881900a000744912040041041070030704204450402c02e82d28222207840e507106111103030708040c11450300180c0030b40030100180d942c040d0782900c1d00c0741940c60301d0040c80b03054060325412070300801c802c5080f0b1041105020030b8031110210b40d40345001030300104041c0c0300e40c81e160058104446c0040d1504083c004510b801c2d031040c2e080801d19451407070850341005030b00d0018 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 507792562 1250 507791312 507791327
    0x1050a1d1b04020d0b030a080d0b010903050a0f14010f06051008310204061508010f0b0406110f1906050714181f0c03110303070504030308180d080a050601 68
    0x1162694407107a050300603841e1039001440e00480140c800315480c600c0300c01003450318011000c106c07908a000b0414038050b500d01d00c200039080000b40703041c01d080c40c60340d150592680001c06001d09404d1000c1d40c85001d0207030140d40f0840031580100208002c00e8a400348400410142c02042d1280c2c00300002d06050501c203900c010300401aa1080c030200640142116048040e6928094104001c810310280581c0d1a031152000409021281400300520384000802d2841c050b001640c2750a00481c2c21300c40c43c203000e020f0b1020b483da01c0c213114174400003080d0300e9032074242d9422485460b8801c0d8400322108900c150417001019200f44005d2040340c55554050b102c0d800d000840404000e801c0c0010031001d01d01000300718240700c000e48081c5c510118540400702da110444441c5000c1204600c00b00c0401d90700043e01480c2d0681c0401075030650400c004001d219200d2880083e0410808a000c950305400f481c098050009a104c11a4840c80d06e030030011300040f00c00c80c0c2412405150400084680d40600107 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 507793812 1250 507792562 507792583
    0xc201f0c0f052206081f060f030e031b0d02060717070c02010c02030a08030603101806050717010f0e01061112031003230d050f070209060d0501050a1d 66
    0xc0d400050184076a0841e40c0e40c0100c024041001e9845003820320341040508210040d0400c0c1da1210360600e401c000310124412003072020039013aa0114005c004150b03200c0c2e18a90303c0645071801049000c1c4c030580251a40c002c15a0385074000380d200710b070400d204400189041003509941c003503c600360344008050f1038007001d0b030800d19810f040560026060303d102d1205954110f00c141441300c0c11040e80d802003490010380180c100e500c440e0020074000303540707002c01551041681c0e6507428040b84180300580c0f4201c2e800c0b0b0b02c0003003045885001040c0454040c00131100c6200c0070741c10150941d0380d1080d1182074032000c1d228055090745a14004a4a070b4801e83c030645000c50080c00a00380c12603507140b42085903000604140032001e10f4180070000600030341a040504454a48014040c000b0f1040b0504115040b010b00040c80001c020801c5107002010030368019a8044420951079a03c00c0089981c0c030340000c1c4020200c1d441d18040160480c500da000900741c400c0003000c200c02034040c0380042c2da24640c204 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 507795062 1250 507793812 507793817
    0x5090f2d03060906010b070c0e0f22050c0d05012304020420160302010204080a060204081902130f11031f1401140309070302040204030803071b0f03030c201f0c 70
    0x10301600c03550364024180300e449000c108072107955a24a2540031002541c0c2b42c1c28201a100a1015002200031019155855850090340000103560b5141c0e4031000596800d0081103004008014400c0c2903204e0040180c103080210075412800050501c101401c54040740b04500e050080f054921000450902424160003040e282001c40704904588072444982202150f4003044049107600d000c1c004807c03071034840c140c0562502d08040c5250b04001a0600c443c0c1c0300c074960500381d000361b5100c0c02d07030141094194100107828040442c6103400b622500c00c00c40d030254400001e000080000000e1000c13090203010b001805a500c070391040c031008007800d40a600240e0402d00310803003220880300441d0000f48248c1203a041e43e039030340e0109042e0382040d48240e40c07455000c02003048854002d011000c00c00c03284030b4000101440e030303a1000b840126500c4081e04241d030700d01010903041d001e01d01d500001e50010325401c8603000000840b990319a050608101c0c800340c0080340c285031103864080d0380b40148194 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 507796312 1250 507795062 507795073
    0xf06040539040f0603051e15152b0b09060a2a0306030f0602130b0906071e060e010f0b0105190804051005190606170705090f2d030609 59
    0x201004040c00000094949013641c41c9000400a02e00300300c004000e2000310100b81d100111542500d04241000c4003501d5141c80a104104003101080c50000c204141125941543c2003015803101d5503000c00000c04040c040f59411002c20f02c191000101e20501e044070464846507035502c0c1c14020f45020310044c264101d0031440c012722142c60f20100404a0516190001c4c82a03034a442d1005582e20148042e1400c66000a07074000d102126084c140c058082c2c440e08624004070080450603611841c10041c00c03a52074500120089134095241b600820341124041c40045024402d060003000104001d900c41441c1800d01102075000c5d2040d1b80660781d45038041501d0b00e01420090f45d0882e00208101c540b03001366140841c01014500c10140120500059008130b00c25810f0040101c80582c0c0101c0d0504c40e01000145c940d58081840c0c650000301494016150140d02d00820b03400381c400c108032075203d0610401c80500400003100a160b488810103140d00e00b00054040c591654003d44072402e664014 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 507797562 1250 507796312 507796423
    0xd030b04110a090603052814160e010c11040504110a0503150f06030f0f010e07170604030e0303040b0f07060c031e1a0405040302150714040501110f060405 68
    0x40c2d0302c515401000e040c000013000e400707c1c0c02c0c220080311140c45c06800c81e03610840300d03208148107000c00c1e520a140c10080d01c524440315801a00049601d000703d810010501c000b4030810103505468032101c0c8000e00140f0032801c1515000c0c030300003d4006e4160007015482400038991500103030780804082c855056203180e480c0c0302e490507200c03c0001e102d5a0588500c60151291540030032a14110343c08550001840000d00c01d489800c1c40c4440d4000340d42c02c11215034012000307901069064005615042841d1443c0026011078107601465100180e404000318241d600c0c0c0040c82c00810440d84244030130000314102131b00c140c046907001264803201810725134980c059000b40354007908802c01c046c680345400005680c00202039810440f01100181c0202007040c3c44401820700c09904a0311034203020b1201c2c041c1c2c12503002c0350700446c4541c504000c2c0985100302110b4061040c10150003401c0140c0319286000c3c20840e548080141d00c90310800043c0b8012401e20b43e010602921175031925001c000c80505 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 507798812 1250 507797562 507797567
    0x2031618090512030c0c0105010e071202030a1b09080c06070302070e070207050603010f0602061501051602011e1701140d0312020d051810051b07140d030b04110a0906 73
    0x41441c119418820595581c200503203120142d84030b6421800c4040e41c91380002d414500b50344040c0d00c15880d4540300c805011400f46c20456102c1001510000161642d440318584005810f001510b41c0980c0402c0e400081801c3e4090f150100f80c9206800716018080c4030320610145215542c1c000d80140c20880d000c2c801d40c22940e40040c0c1284080c8101c0b140b1a449000082a5500a82c040ca01074081801b0400c00a41c0502613039038400007a052880740301210702e0019003248a01c00c10711024207580e652980071a03010f8030708516900500d103000c50102c80c0e003900142034092b0514421051607199000051041e40e1030442000046000c0e2030310580c5803456030240c1d20500d07a40c0903109129000c0c0000d15209160344610b91081c103039030100c0c2c040b00242e0540039080c840311111080403c0d0400003001000106450f0000352102090030311070f50f845139810b00400c00b444a502e900c0301ea0260707060842e80303d0f0741504000311904c01207a00b08a41e5141d030b20a4103ca120744498040418001c9200300040360 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 507800062 1250 507798812 507798821
    0xc07020613090203070203090a05010f17060406030f080702040e060106210207050a0f02090a110304110f1c170a0807030902060f0f0d0e070b0301090b040902040c0c02031618 76
    0x10342a49107107580c1030315a464881660000c0381c1e0b035401a400801c00e084546002510800245400c1c02c0010403082848401400b40d940141d50695425010010482d039441729413100c1d008641001c8112640042e5150040d4580e00c015002d078801c0d810091910250744000c00d8440c101c490588641d605020300100400b0003528a00c0d50400466080c8034050109209000302c0051600c66041c4081c0800f0500c1009400c540140801d0081881c00000030350140300807045039045900204100c159444560020701144819401550408400c4450081c1d4101c11080c4c281500d21400740107551140381d40318006a801030b0341a000c0094070380c01c04150082c0c0643d011481260000c0e00c414074041006d00002d429510402c21400031000016080102e52154482c0f051240c50f03500103003094518003665450140018020081450794800514180d50b980c0d600104103568050402c0c40b140212010103001c04854180580c003900a203040508e034140210007240545950301720300000380f001c6112030710040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 507801312 1250 507800062 507800077
    0x6030f09010603020d03051207020d051b0a0c030c1a030402090601110a0c0b04050a080f0606131401030b0403080601030c08070f111e07060503040b0a050405100618140c070206 77
    0xd5503581000303c090b844031185580000d02a03203e00c2d0781c48400e83e40b02c3c000b10343e005201104540111045101c02a81318003100c103686a0403202c0c4140c800c5410150381440f1031800010528001180000300f00456105050111103402ca02c800715402844000d0f4843e10007124002d500ca981480085c0e1190300034000b0710700b0080e4403011200103c1da2036442904000360b40d0042c803d00300c0041410403040c40d10b04585001742030b01001508071904880003090342e905010344054400e1840d540c1401450400307500900e01d940740440c0d003240c01d51b92810103905c1b00300141c600340d00144c41c1800240440d4024000c0080035400ca5641e00210340e41d0250480300005009040810000e50000018002c0d0302017101c0c50030144103848007039420081b814120700d4071000351322180a218040c401c21020400d0040400c2d40428060008103031075955203059400c3c017203c0040704420318a00080031403010101040c43ca03034032400f01030400c0005658200e1b0090383c0340481e400c41c4102c00800c5214010f06012020f070510 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 507802562 1250 507801312 507801331
    0x90507030207050f0606040b0d050a170f0a0f09051c110d0b0a06051206220309080604121409130209010e09010e0610080105010f0f052101050a08010b06030f 69
    0x240949992801d0404c03484220010555000b0070a011892034244907124425508072407000c0860440d5a40d1601d5180d03d19015200b000105031020b48010a00c0071585040a8020b142d40c1d50410711602a20903100c0d40c0c40027000914144001c1090300b401c466800071502183d10300d05801c40590b03a5000440c8040d0180d5802540079248803002544410445009914104010892508110500040400b0303400b440070b141e40600d040c491070f483c0c045c040b40d0040c080c04015400501160406583c400c1071588031020718881e4a0820043c0102d800301d500c0034201503991410300c6c03007290010008502842203a19070040c2a1001f401540c0c4140c2d0007000d20310010704122441d092000d0010b2000203099108030303ea06080c00800c011071421000446502215060a1200d541410002064074850b29280341c01d0040b60f440c00c01c6501e003d9029100d03a1048981129038070301e007903442c0614000f000c0c070442e40105050f8601284110381805801902a0b0203409682941d44802d03085186803005007415a1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 507803812 1250 507802562 507802567
    0xf0305150a0b18090f060403050403030f090312021b06090f060d09060213090b1e01050c01112d030717040f02090a140a050f01061110020a09030b01060804020108010905070302 77
    0x1825210398107242880f40f003041c461621440d00c1340c02d41d8242000b10001400641100c410800020b4200c03090710140c80d0035240190030400c1c02c2c002a103c1800c3c6070405440c054000c8442d4814650005002c404d044041c030411407000c0c1c8202c240304250081030180b941c0100f00306410300c02420841c01620324103030b10010125540000d61200c1080344c0c000d410351013281512040601100d18580a80e01044105592440709020007088824090b61058140c40c10000e00141c145820b0400750484020720010f491040d0b82da01c800d00f503145450144145c4004502c0003040b10341a03202c1d480040da03100e903034551900c541c1c45000340072003403200800030011554004030b1240800583c4a5103070981c4140e417041c400144404100503817808001006043d0421141404100802d40c00c0c1c680c8443d045403018140740768100a00e503030007400d0420100c00080b07450710204421585940c080d034040210307405003400507003d903240c28003140c4404048601901096040c001000590000d40c05298031140900e401030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 507805062 1250 507803812 507803831
    0x21614040b100216120c09020c010e0d110d051c050403180323010c0c0204020d0b1903020907021203011505191706010906020a0b0411190806010f0305150a 68
    0xc542428102c041d90040c1d01580c40d02e103d10744141400e81c042d000e8800d801011501aa03240015912140116200c40390045000d00d52070600f50010b5880800301c000396080d10644010040804070720480d803140d40d11806d02c240841c00d010328200c030031099600c0118030a07507085080342006484040c00460400c0b4860050340c1a240720117140070b02444c8126444110303c082815100d8603080800400490b50745000c144450258001c0405400f15034140e40150300c459203500701d0f200420f0401c42603074110b51300050f01c00c91000c4206012040ea4402c550740411034462501c220780c0c5520b180d080390450403003003005200305245d55402104046240c500140303001100311100e08010908031484011a0704801605942d603810b845040d44800c003840c056020601c0c2c084000d54400d18400041c10002e6018045811300c82c580c0314010320380e40041c01020040c4411780102e4503a80c0d0f28803c1810b00c0c01400008508444140551400c5079040720060505d032419002d00b0070b07072a41c0038108110403951540501c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 507806312 1250 507805062 507805069
    0x120206040510110105010b04050d11010e0301020d020705010e030915070203100608030918090304140406080303040b04120f0509130e011a040513020105160302070810020306040c021614040b 83
    0x1000c103031595546100d03410075404503c1c0d0a41c0c406800645070100140014880e6890f0055580f606541095490503034128800c0142d030403e0f0400003d5030554000140e8503008005e54008040140c031074002006000c1010580343c3d240d028802c070880e070254000c96242814049803000e4007225000800350b4068060558011084400540c011181c40d0808580c0707110b076140074414a901021240c40d00100d515140300480d480c1c1c03280c1d000e00c0c2c1500d00040c0800c4100e48440d80400c0290a101013281d5503424541440000c00b24221011600c0c0d6503800b51114560388260014500540303943c03111401c0001240802c101144900c140d58043c95403120040000c03038003405600700d9903d2a40140784580184802d00c019540c0080c100055940022006001030740d02c40304452000c000040102480c00c6140740032414402a540700704541c0c1725407210441c0704401640118020b12046608000c45580b08200781e80380ca9490104241c847c0368003508020310014021300e0b406c81e100080c80080c2410808000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 507807562 1250 507806312 507806329
    0xb03211c0b0303040608040515090303071211040308220506030103031d03010603110415080304090b0d050a11100f080a1d0601031a01081902040207110402071208070f08011202060405 80
    0x2c1800602d0f1034087c442804810302c2607102a6402038100074461500ea082d041ea42d21002d0a4002000000d1800c08200403207070340440130500b8042c14181d560ba075603007406116501f1989816802c1d010010940840e0105034400000702d82d0040c00340307819a81f85480568040f10f940c1002020780e440d2075001010f5540a100368400ba502c40c4ea0964165940b00050204803107800240703c00001c5003100c14010000c00105540032100c0b042c50114180c001400400e4080ca20350100400c144101403484040110194461049601c00e50340d80032050545d02c021900180f0f44010b001c0410030174000700308070110a80040d80c0c00b00801c0c103414680040440014600b034401d074401d6690003031208103215003692540c1441d0040c0036900048c4480c544158401c0c28500e00c0481c020700c50303a07000480000700980e54206040c0420020001c545420040c10401110940225a40e000030004000134100a004211000030284e00d0f80d1070040503802e05060120380c5555074816a44950b0034800003e10b90f44203401c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 507808812 1250 507807562 507807569
    0x3021b010c11061503060412020115090c1409101d0a1202030f0111030c07241b020106060c0b04020a171c050a0507031808010f0b03211c0b030304 64
    0x9649403403501c0c401c005802d082c2c0140c0a01300c446607040603410a41c1d0001070031500560800c00090143c00710a000307034014450099040c0c60118004400240e00c15580c0c060f000d11100c9445102107200e8954941140b8407941110740e40c010490300400c5041442070410054a60081c5080481c0302d1318200000d0a60f4080e611070465032041d03017076083c21401c040c00150160a03000c4001d1003111400507c181b071a00000388103402c030039008942a8148511100002041700750207001c514070704054441403000e042d0031940188506030f0001107684181c414401d0342c04480d42035441e806d004806607103903903400001410690b484a0640720115610542845640d4410915001002d0418080a0786d0300001e00c0b8030031450a010080c8502c020040c0c0141c04c50300015454517010306040681c2c00717001d040d00b00503000205590319151011070302100a910415070020200d0031941884980c90b0381408907943c901d0030301c0c02c85400b4400c61404448c03000000718603458000000c2440080180801d01e142c00690 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 507810062 1250 507808812 507808817
    0x9020403031b2d060f060501080705180411030106031b02031e070b10080d0503060303090f01030e0f1609060f170a0b0f0403140310140d0b0109050708070c0f0303021b010c 75
    0x103102000b080005d128003071401c0030003042804503501e403200107000440c00400440901100150407400b0f400c2610389841c9001000300200405044a100b100c8590024060100440d14002d4051000c0403190004010201d41354000c0d4034100456060400c1c3c01200e040f0f01020a0f024010040000d90b0ba60005108644824040070141e280c0016285003518500b109014003900b0000c0c4091528080212041580140d40140000d03104000480060407086074102040c024141404050040411a0b00070000700300110082c3c82e0301d4240038400c480f40e42c80f918400c1c6088090030080c0740d400084400c240b40407202030b06c0008286072900058407400f19900a031003040c070700401c0101500120b44506540b03401c0000c0e411854090300b082c848404e0390242403000225505014035a40c1d690403529045503102c4400344455a6034170410740509003c0d00c8000c0400d03040c0000034483c03807203a403051600030f40080b03602214040644045e8000c1d800b000702c0700c13000310381200d0844460909009840d01c1e900f280e0b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 507811312 1250 507810062 507810143
    0x10b0f0f0d0903020d0903050303040204020f0403080d050a0c030e03030109051008300a0c0b060a0801020f0d0507050c150c041d1005040b1323040c0f09020403031b 72
    0x180f074000d08105142a4507000e21103461001d00124000009a0354045ea0540c3c0040e61030840545065060180750300c010502c8a0004980c0d0318501c068004600505041e0310074400e800d0024825816203810044a0549900503c010000b4a4942d004540c100329440c268100007a00c4014441c10148000e0448112040310845c51099510004040792070401c04034039142404040b42c0c005188552110003d0074848030344001c160742c0e9552090300d50080100c00001c55440004100c0004142c120010a9a20710f00c0c007400605400e000c5c0084a4503588140050442004010042c0d0700410b000390295801c100c05110200310300c0c12008200141c01a800c500c03108600d095680401a007049411042c00b03142001c5800c0e540d603c0c0c5011440041030711701c03008242ea0348480c107001000081c140040c0c02e03070001032042c0700500005401d0b50003524034050600500d02e8540aa090681c03150740300003000954047d901d6035901c1c00c80200c026000c2d1003040d0500d0b00a105408803d4611510f403104280c2c0d0307070803 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 507812562 1250 507811312 507811331
    0x140c0613031403100306020a020c09012603030405060601050d09080310170705100509040b151b0a0302060402010e030309030708062e062f0105010e0717010b0f0f0d 72
    0x1025102c003400e2aa4801e1540c0f4040300d01451003180c43c0310080c044ca0700429030030b100b135000b400b100c0c1c0c04803006030180c402c96a41d07206641611950719840300303410380d5410994924042c04000c40b8030a236040b50003800036845031401102c0c90751060340c01108ae03643e02d41c80a000204c4c0d8900850181701207620070040c05040071620040c19281e5101c0500f1980b110303004002c103032504c031040100210542050380d00c940388200400e000e4107a80a8590340000546029111061010042c1052001e219150702480001140c440e980305d141400240140c0e0211000a005600c602e861140185020b03060742d0030000840080303894007019400171911500002c0c10411045402c201d41c10f05e5481644451180500c0d2012007449001c036409a1f07002c00070f10354030003120749145ca441c028006500500521b15207c01c0000d680c000d080038000c42c400c42500002040700944030b206003050456214009001d9a480c080c1017044590110840c40003905040c054154240030f85d0014001e509101900070451110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 507813812 1250 507812562 507812567
    0xf0a020a110409150c030b15040905010806040b010311060918071b230309030f060609010b040b030601080a0e01061211060a0203030c070812070c06060b0a0c0201140c061303 76
    0x110a401d038007880c5441203800100f03a50360500300c0c00c1201104000b4954003048402c070041c00d0852a015081107040c190750030300d808200d000707004492103030504000698030350303800d2a203503a01036070040d12481484006101041d0700b0500001c1ca148001c005900d40a0103002041034024800500b2004110b40420007401542003100324900707240c11202a1040080c580c1c1d0b000461480c280380340c0f03908000d130120f00401ca034104101d030b00001004044505a6013441022039540c031701101c0c1d49009901200000465000d87d1003a80c0585140442c414111ba44400c011200f6010041c0752082041c5c0b1400541030751701c030030b10554015200d400040c240c9040b950400344038054540c420301e402035204000320b2100c0356004c020380340c00c56401c0d6012035903461036050594940c0190011018051000e50601c00d9154102c0081034845210300401c0c800d480da1a01140c82c28000c80c4811000f0401903601100150302c03549880991000000d40942410300c0c6104e400e1404504072030301e10301140d1654010041c5038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 507815062 1250 507813812 507813833
    0x2102070605150a051c08031e040b090d18060513230913020916020f011506031508190c09020403030806090a0c2a1407060930080f0a020a 60
    0x3200380e41d05c1e60800781c0720100f03d482e8188640d02070002000400403c01c4c191000c81c0402c0c0d8065070b011603100700c4c03d041c2003880208805840c0c11055214020080b400036000300400c0740881031200100e50b00c82e1a140003542d1b2a8030003500b00c0f50241e207890012072103078a00b01854040c2031200096840c03480010080c003c00c4403018259118200c0d1008110380143d641c55a02c0764841c540411042010708402d4007030345003807041000f04046500348801129082c1c4003c0206c1b049030080c2d5424400209200c040141030b0340f46004410b00354104e2498581c0c3c9002e003000814900b4483d4843c152029902c060130800c0760040c0e00102d00203a05507091089070315014030001e4100700d88131010031100b96141e202600d5000703041c4070419250040c140e0801410141500501d0898000c0d5000c006200080c2c042520b03007080307024840100b0f8100c0c40c00309100c03408511154000e107062050400051042d1b00c0020000d03400c0c2d20484200702d007041140302203100b0601500740b16259400034026069146400c1c10100f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 507816312 1250 507815062 507815069
    0xf06221413020309030c1b1203160f02010504090507080f1501020d030c05160803091e061605190806090c1804270606060e04090302100b030f07080f0d02030a2102070605150a 76
    0x29070081c0010303cac05110349600e280c0240c0c0e00c05142d140c00c1d082031005840701d01603640005d04075403600c0100100c0c1504a58110f01c10400302c00030600f01c0d910894914082d8a2440c8a580184e214401c1001c1880c041e0b407240200c401142001810408220440d5018840710305d8102d80ca4800071040c00300f001c804000c0907807168880d42000c540400d45084182e40d07520000c1480240d070312829400c070349c07541c0240300720b0703481000d08040911800e402c0c01002d480c90074151101c0b4085c4070520002946400e4540554018941e00c580702d0312094034120800c0302403d000e140150951200b00020b501c2e40f4004801942410320480001c1041441c0c450050303e41404007800a0141d03003000b030038000180d030206a500400e03281500c0000ea000d09070010034030341025440240254861100f0110b0f400740000351541c40c9660110844c1d5102030f08950482c0c90b40035110035400817450b84040e0349050100c420100700c5003034140d000181800389a46443e0f007680d10550751090030070500846c0000e01d0900c080b0501c082d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 507817562 1250 507816312 507816349
    0xb01030b0a082515030f0b1804030e030c1305060f03370206040603020a09080f03220602070e04240e0f011109040b0f06221413020309030c1b 62
    0x7442d160004440d540010415244c0030150380c1e560010010305960b1115201910140ca103000f24424240808002e00060314241c0214550001a01d800d24001403084401c00c030280010000301c3d880b04c8501c001d0708015202507030051510980055075107080185100d082001b1002c900903034400b4090180b1584c1c41250000c092002c0f00b05c60000d41c480904590495042d4900145e40b0203403c0401c54100705560040141c502031102068040074001001c0d054221800f07070841076241004146152260640c411200980c0012100b0802c80340f04000081e400b5010340e010031940151012130143c840c19207614070b40300a030382c1e00e40d40310703100020803045094042c00e02c004c12a207484000940494080c00e203166104030b441e03483c0d11055490700308611000800c09011030b9114419010201071000075598030700032840d400400000c5440c0038000c004c4211902a12441d0b040890444038006940020654070301403108010041d5014410443c41c00c4100f41d941c0307450030781d16116041107403c0440c000c08807070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 507818812 1250 507817562 507817633
    0x5281e12060c350a0f0903050903070501050c0a11011206060f09060201050f1602010605150d0b060a0f05071a040c0e090d09150201061203050705060708070c060b01030b0a08 76
    0x1651520346100100f20000305880b20541e40c0c48526005010a00304620905007021481c10416802c500601a244002c9081d1603580361140c00444141c00f0340c0d00e401500e6400f0082040100315001003411075000185440f00500350b44649040076070702150f00c03210008012106810241d94001c0c9400c01802451000744107034205903400098400c0042c050030b901005090480b030440c1c0c002d510580c018440a002c0700030880e0a400c02c401160000d038015156141090201940c5140c141d040301c403641c3e025111410192100c0c102100c003a049482c0c2141c507612440c200044203c02200c9544c0300d40d00c50154980c120f4200032660160350809442155154170011380c19911070f406c03100c1041036406140c04484052503810040340500308a620078070111312101007050600d90300c034000700700d480c0c01001103c24949405500b2a0290b10845901000501e40c602200001f40c181c0c114814421051501081c1c00304070704000f800c0e01020b43d0040b541a40910319003a07404410382c1605010f6800451440ea = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 507820062 1250 507818812 507818867
    0x11401151d0904030e060415020c0f04110406080411061611011112030a061523030709050d0f05070b0c06060307030201140703230405281e12060c 64
    0x200040b03000792004050007070b03680e2164020b441d103038240c9008028800803064610030803400652603402e5010218080d02c4081a100001d003028000c1c015409885044645068648481129428400380045581154fc2d0700b50b11000d9076641e000d420b00c610b80858214a1022034035100201c0d40f01e0f403a9035070500c1841c0c0c00c9040781d240c0100c1c0c968800d114049417140e40f60764584c5020024400c54001002d00344485440720131081e07002c0700c9511040c66048050348800e400800f2041c403400308551020000351002c1042c04541007003039847c400d243c0310300c2043c210300c1d146640d40744c180000c03600810403440c1d02151150313104000b001203a412407401d0740600718990460300024103a4401000604950400041110415102d01710701074400e040c2c485001968810544540041d42c010721800e840350020309030260b02c0071b01540756601048070080c40d85262502d00a2141d000c0d080301031071b0012040304000c00090300907640410341c0042e4030a00b40040c0c210b140050241400503640e03c00303507080d0600c1c01c070078 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 507821312 1250 507820062 507820069
    0x921031503021f0e041404050d0c12050711030d0e270402121005090a0b090f060a0c11071e080607020a030305041e060504051b0a0e09011401151d 64
    0x24a01c3c036030b8400000c01801c40b0580b0070380e80350080440c90f40e0000e00e481c8410542e441d80c1210980500d1181c010354200d41e1007210116006000e0280c0601041c0c06100c680352130340d025a00030200188100e614079020b4a0020000e4101401c10740a01d002c941c0a80f42ca5140e440c04660003140031045d05480d240e540304400e0f8400b203e00f80207000900940f40002400458502040344904100341020706200e1850b20b540c410f602c03070001030070440b05081942d01044072008046040b40c40c02d81444018400c558640c00c00c4000740094015500507c0150000500075201c1807009a0183c40810100410080c400e084203001c1b03145c81c0d001292a400413400c0c40300c00c50340407038100b040607010301d00400d248d00c507800c08501e007050054082401d80351080c0366a04000584d04100d00c61740c01001680c10504440d04100040c00c40400050303840007060400340500307103600002a41103080c020000800d1800920360b411130403030a030848443c03070815240d084800796022000d001c1545156078001034500512011 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 507822562 1250 507821312 507821329
    0x906200f0c04050907140904030c050a0c060f030212040f06020d18260f13170606091b0706090c080102030106020f010609090804090903140f0a1103030402010503010b030703092103150302 82
    0x7151f200b030000c0310100d020b25101384c840d00c030175503004800c0c2c03050b01c1034501e40141c00f01b80710b2040c4400300302c4905c10034a140d0300034403e030f0300c0301101210354100c03c0d5100ea442d04000d244140c0c00b118055404d02035007002c22150300c0b8480c0780511030504e1503840c41040c04d0041c585c0c80c072410390036501c52800c1e21314100e05090724191800c1d2042441002c3e2580c030a6207000000343d1107504440782e42c089041d0000c079040400a03201d401007005a642080703d8030b4081c00610808220703d1207554189041091000146140c2e10175418640641103c05209480d0605542a03920a034800e80042e40100c0030030b00100820302c90b47c8003c0600b0318003003201303060b660349042150140b442060030175950390150354103141c001c2030b05c2000703500c400000c541e440d00100c1c14244a50440c600a000046541010070800350001040764051038058403010b040d6844c01e0172114030f5600c010b16140405465600800000c1e03260461b01050440e01032003440311107035012005040b940c41c40385165030110094000c20158940ba100c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 507823812 1250 507822562 507822599
    0x1203090d0206010b0f0418091b0315050105061905090901080d08070e10050703020309030106171b030c040b1813060c08060d0201110a08030f04021f0906200f0c04050907 74
    0x944030400b60098450001005508c202419020203140d0b1450250055040301c01582d00c1407072007900e11109000410100c0d07009002d80b40c0c201d80d007001001101159400340d40d09084052070a2864030b4407000115554600a0b4450065503200c6241c1c14000e94000c56000e0f8000f040d8a070400d8410303e07070300000d86c000c008150010240040000c1c1101418070138000c8a40829029000348800e641d11865011070a54100d04810035001e02d000c052841c040c1c03000c480c144214001c1c0140301050400c0100001040642000c1d60304c00440200d4400000035803d990780b00c3c01285a074244038508074242102074442c4100301d08104200841001259950008540310454082c03038441e00503c83c03036110034503210017020b020b070079458040b08104040c5a2600b9040c8200d109070795400185d8064032180160782c0354800014007142e0100f000f481711502c42d03a261410624481500001c42018841c0e050170041c3c01c03006c40d45640c0040c0f240c000700b030400740103564020856000404e800c1d403030b0108143d0968218038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 507825062 1250 507823812 507823829
    0x3060c13060f0903050303091e01060302130b0406030506090c190503031c0f181505010b0d0c0309020d12090803161103010f1103040c0504060302090f07021203090d0206010b0f04 78
    0xc201070502c1c3c4140141005594000216540c0307050002025688422110382c00c517108041185410f5520810300406040340d0303000e041d10f00e50205402c50745010300302090006420650b40c030400404600c08010590042003c5009420305a20203018015040780c9405d00444128400b44200107540f00003048442c60541020105080c2e11044020340185c5044043c4001141c01c000036843c1c00060010b00742c110900c02d450040c01c4080c020030315801e840c3c0074440c01003011000d00002c0b03000080d07500040c0c0003213100c1c54006500c0d1a83c2d03001031200c04501c1c409540480f00c01d0300540000360420181c402078100c81009500b4910b041c00e19142d032446c268801400040084903a000c42d8509406c421000c504900d004d02c0000350000804010b50011101603416040010f03000031941040e00c250001c0d650045c0101449650f1042002d11015014210703100f14070540c550b00c2a030261413000785004000344006844000300c1150021714104060b0000107044408000141d00c0e243c044049900315003a01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 507826312 1250 507825062 507825077
    0x10f060801030209071e0906111603140c0924150a0c020a05090109021201060e030d080621070501120b030c01030b1801030501020306040c052d070f1103060c1306 71
    0x44004456016106e101202584008081340ca4031540210550099640d50340d16801000d00104134030341d59810403814084070400c40c603000e02c04140165071100d00c00c40c481d0103c0c1c24040011010071040c4c0300440d03000303900d807060081c41e01d0000c1c0542d8190403001022528184070b0042c801e420500b43c890f0200035818041c00c2c1954000f1521503003542d0b00208401003070300ae103560392180c99070045e5120a1a45100d1844240049800b074000c020116000c2c10103402401002d500410656002c1c00c0030300841e60200700d59800b100d50400101c4081e031501c0c00320f406010a0307450310300003400811070700240c00501c0d414006082c07450b807000a02c2a000040034600070402000381408601d10f07241c84072105150f001048008400d0220540055008040035541003100000140c01101d41d809121007200003017415042c040505800c1d2200c03140001e18000403185803007000c0c3e49007410324203010001c440740e55041c0c00000301482c042c0b20715a0700061001e00903282446a01d001340c80d440c01400742d0750901c81c54 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 507827562 1250 507826312 507826321
    0x4030c080a150b040b0916030e0f0a0f0303110703090602010506030c15030c07050a060501030203150c1803070b070311070f0b0a030903261605040807120512120708010f060801030209 80
    0x1160451500c001001c0e06d003e41030f003803040303140c04100048003910b00800d06221136508200c00000701a8034901000004d484540e4042d9901c41e8142c0c44030109404258030b450350a68090140801841c41510944030350000e00e240020180c25a81e00401c1c2d01c1c400c1d00700300390b0440507840708603001c03c0500c03000040c1950703582c03100c07010482c2c4c0c0543d02014000d40b044000c480c04100c8150700c018182d900850031503c10034108d201d0065010400c441d40400303000d081c40400f420000800481c580d07000c0c001e00340c0e803002d0b491b0310b1900f420760032601007076002032071706d500c004c04001c0c0c1805040c02a22401c40101c040a05021920031144114940801016502c2003640189440307198040401c42c0051403401413917049650304c42100c0c2043e219019003003402a20301940e54029000c40d0210b40d000f1020300113152401001d0b00d020100b109040d41e1502840750091204d0107540002c01000c807510700c0d070300014140000010042d4005070001140c09803011018024140c00468150442c1d03411100354000f641d9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 507828812 1250 507827562 507827569
    0x303020706020c0303180106080c0f091315090611090f0d030306030b0a0b0f010c050709110d0204060503010f0815040b04030c06050f0a0e010917070206040e070504030c080a150b 78
    0x2000c3c400381290002105000c50031503a00d1801d4804041c100c0280f0420f85c0f105003498a48402c560129881103410301210720b02d0800700050380e0f04c01c9003412140c880d00000e44400e008a82a0001c505001e981c0f89104030030400288903c1c1880c1c1c240f212000e05082019020901d0300c2016541c080c8201000c001000406100e600407001840c2d114003402000d041000e00070b80504460228a841f03102d03070625001195220381400316003590800000e11009141440d800020b015040c202c062505007001004886001d80c001403004003129039603550349601d00800036542901a42112009400c0a02840d1035050307080407454000f42c2190b401044c68886103003d50300300c5803100700140003605001c02c024034100c8040403603128044016082c012a2740b214203507800c0302c54403d4014044c03100c41c00240c1c440220341000d840c1d03091010b040a494151214001081c40c1011620700000940008050040010744c08005000f420f91900900c03040e40c6aa482141552a49135029803440d52413440882a44c0d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 507830062 1250 507828812 507828817
    0x21c11030d1707200703031805030a03140c0309060f07020103060b0304033e060f0a090c18090c08070302010906090b090906240702122808040339080703030302070602 73
    0x1140135007196a85952480c002d000d00c43d00300d01c201180c0a14210005080c04c0100c0e441400700d5241c0e5584050b403140d00342c0c0c02d02642252032460321a100c14803101549071507540003040c0c00c014001140e5113403075040c40014196000c1e5000700094001c24000e000000c1d030030140803907500311880030700e030501d1550542c140d0b4079500380510703203c007039500085094814001180e4280150312951a0039110795403081224103603600b02000818040000707c0401000c00c5c4d5010208217240304041c04552090b1607100d030000c402854203c020b654000103c02c104540e00455828010201070a0080240e407030008180030a0240100342c134000c0d03640b1000603d240d0307161f61440c4030310006070b040320808460a4000342819000031004038060705d440019601d0304072000a0040d031039030051514115441d12003004001c0c00074008001c41d4445414040440000c1c00c00c2c3d0f0502c0250364106e141400641580001a040c031301c5008201c0c10f0b595110000d002107030010441e44182c03601400c0c05aa69482c502c0e08034005d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 507831312 1250 507830062 507830117
    0xb0411060a200a0c0b341103150f0a0b2215080d020708010501170319090b04061707080601140a0207030c060810090209010219021c11030d1707 63
    0x7134031100d50103c1c020483e100a8070107003143c0111404c2c0c0001485040c000603051082600c800d035000700e246800264000070680241801409070b0345008544800c8005008060300c140005603801c800304400d00b980382c481d1600d500c030304842010b00711803405405152240c0a4009100264548480588041d5000d0044c0300500b0050210ba40d500d000b640002e4075610140100b040a500708000004d0f0500e5042040300b0802c0340c40c0c007031498060f4503289003400e01d14083c2e424050001c4441c0c0021075452242c041d000034681c5403900d100491b110f0a040d0403e107001003a801c14402d0350000d00ca56270768400300080d070404114401c80d682e01e040c10016403a009031980b00508400c201742c80804c21940c480324040c000c041ca1042d0386038450302d401520702a030241031032450040c4d00044035101903040405410308070fa1b0000d42220500810f042e042079005110300800d64402001010340e071107504040140c0e004210051030302d03045610000c403100843c05009812501040065001c07004000d501c07403528105d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 507832562 1250 507831312 507831323
    0x20d0f020306071d30160609061202030f010b0306030a0507080c0f09090c0402030705040b070b060109080703080301050d0303060807030b0f070306050d15060902070b0411060a200a 79
    0x10f18000400416003402d210744001c441009603a10030b02801c000038007001003034600c281148400704035602000020210f000240607840b6910b80e000c01d040e00360300400301414680c0e803842007040c00d004015005200e819100300c1440c4c4100200880b1200300c505581c151b0300052202642c2e80c031500c00180c03070f00080d44005061402000c60018051000080c14051290f0940340c4407540c0c00c00c64200011800c0840e14001180c1100003088018030f040c1d40116448101400c00c0d41c10962034192000040e001303040e04031003a50424003800190341e00711000b880189000780080c0305643c1035940d09040c501045c401e0714083c56a80020b0301c00c140c0203800003000307000058200e480056403400d044d0a00e8400307550386c4e13090104120104903c2803003802600c0558401800e50340407a500b42c3e8502ea0310110615681110b0344d43c440020417814043e00080118600074000083d42d0b091900749004001c07101e048861241004102e0840459000319034003849810041100a1040795683c00e54202500d00a000f8103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 507833812 1250 507832562 507832573
    0x7060905160b0c120313060c0e190302030d02030903060103110105071415010b0f040605030a021b0619062607091802011805010c02010c0c0e0c070506090c010203040512010e0d0306180c0804020d0f0203 88
    0x188600ac140310021240200c040380c80c00802c100080c0c1e160b100e0700f451180c00d50000c00062000c030b8400208414541410f1411038900340c100c1c2c03180b04c400303401110403035a180c0254440d0705964003103802181c0505002141d407440d06901d211410700b944034901c00d03a07043c00ba02000207040c02c02da56040d0303040d41c1c1722070b00e80c01e00c2c00c1140171381c540c3c490390704030362a036030500030b11302c08400713104081c89104159041980c0858041030100007101c0209044800c15009220b11100030a060504d4061aa003a4902c040520340e81c0d004c80c40003400e68030307680302c01d940c034600b403043c0400c030703503a4048813142d84290203081071140301c4a03030304052542c0300e0540c20003910200d205061040b01280300c1e005101080c0030304e0076501c1c9034440083e03d40d1150100e000190060b44180802c3c046440c1c4003050554142c3c59400014083d0000802c00c1d04020304000381074042652904100000800004034a841240c841c00070803100d1003a810280c480030002c1c102074000c110f001c0d02d107410000002e403001d0000b60010100e60 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 507835062 1250 507833812 507833839
    0x6061c0609060b04031a0c030604181a090c01031104060e01020a0b101809050717010e12040e07051201090b0f0d060e07170307060905160b0c120313060c0e 68
    0x10801c0d130240c4005c60320144640c8a0402804a440c0c4150103225035580043c0b65807200400c12000d400c0c0d1a480c0024003200311000c50004500d11104285240e2802d00310f0136616100341300302d0500181400c65410705042042c025445a10582200c003690380a00b0001000101500100d203000c106100c0200207545a00c107012580e9400482c000484203e83c0680000b50301d9079074108103903800e006000b0700d00c0c1e01c03186090020180300444071201c141043c000242000341c1d100380d03d28201441446100c68600040c0a0180051aa051642c00a01410440d02d041158440700900d02c0051241400c81c50b50b07440001c00c00d94408012000030034004101400345100b078242400100042d01c5520194846c03042c0000e08003c03e55004414400460081c0d41441d80342c0e00c1d00310180c842136400300c50700c0c0208600c00c00359403d2440c815001d0300c00003800035100d4801c10701651800c140c09051164a1000340704210000405644078000254003d6010541300c1600005880014500c0089a032241c10307000c024 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 507836312 1250 507835062 507835079
    0x50303010503160b07030305040201051c05040b060d020d0b0712050c0c162105070510120c030b0f061305310b0f0607050a1e030e030606061c060906 65
    0x5505881084041e01c840c466045022885024503110710f05130000284002004240a548141e6010340181081c0e441c02101520600e0400c141c22980f0b203c0766503420601040c4200f803102d444e8400c60642c1c1c0b4410401203900040d070314481c2121300800048035400003030115440f8002d05042810700c1c10040c4002d04007441e01115942041c2c40b8a61648a020100224503526a24540c2140c12926100b0b06000c46200c10a481c12803448082e0b602c0c0c45800000138494941d11042d01c00c60441c4c3e51480c2610000f0400c010a541c03010012008041c103003810070b1855503d0f0402c0c88084402160b05036030300c840150300700d00003e59a60002c1d901c11070310000101b85512005c4003010281e0300314104a4592401c8440c01c1c11204040c10481d002080d4500102c410304181340100b000741d000d1030448594507580d544071054210680c3da06815024202100030405821000518072583c048000d001607280c6940801c1c1180107891004003400290304040554115660240c40a00007804042c410765072501c48a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 507837562 1250 507836312 507836317
    0x30501080607020a030909020a090806090c09010b0903060612011b02030319140402010c08070816210c110f2e0503090a030822050c04050a020f1e160503 67
    0x30035240d8091140058030061001c55030840f2030b0b500d9160040800c1c103040849009401000103030b41401440000401c11316030800490340704950355801419810404000d0000c0148180d004520380740b0103011000345660003003100d17913100d1400e5400420404907014103034094202403194a800744050303408112500d074007100951003903041c2d01c80e02d03e80380e00042c503460413900c00751341c020b07000c1c00105c020030300540c428003104072100d00426603641800e545807208130040c0d01184001081e00d12141c441001c10490910a03280524140d000c5002501035441c0588030409151005052103940c0ac40b4242b242d40310b40f82011a074101914a15210310141b016641c9015000071160019006810381000544103000b124801c3c41c41e00040c02c4c0d15a01594141c50b118130203840d1641c660780d0202000301e8000000513803204180640c0c0100380c982070460a1001f1164041c2038640c0260041198401d904114800c03034103207502060f0300110140668400c0c0034240250b86040c045800341410700750501200001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 507838812 1250 507837562 507837569
    0x121216020616061524020703080301120201030c050f07230304060809070509010f09050712050a0209090f01050612060a03081b07050a050901092d1a040b030a08030a1103010303030501 80
    0x4104103001d1800d44c2c445010300144a04428280c0c44203040c1240039513150020240c0400b401150f0b5010780300d0f959047c0c0b58209030402d03001c0040c0d41c0a03000540d0380c50701401c80f40305c0d1a810106d2400c1d001c45903a207400e02c00d14101500304040480d420088105140c8480b819036070107802c1e240c48079201d440040a00e007090722221105d104054001c81c640c07400c019014125400d14188610103481c0c001440e0180400502345824080c02103d20003401e4000c0c01400d105001c0c000006980f00c012508201540d040038265280c9010003900512031501d907041195296000001e041c0400c0e81d8543c0003c0140040d0340005088040c0407038206060744282100c00100c081042c140c501031911041030241d800580d21809a01503e60001000003510640c02541180d01e081007106c2d003c541c0c0d1040c0500075010400e651210340d9100980d007182510307091a680c4400701200d05000002c00000044c0d034075119910302134050301c03001000c81e030003102951240300c0518003500c1e540d0700ca41c1d59040c054005c080910 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 507840062 1250 507838812 507838823
    0x507030209010b042603030424390212071103010c0305010302101d0f010c021009180e070506030709090e0312010602030307230408010203190b121216020616 69
    0x3500308051204100da05c40070300612401541035a440f038459514451600001c00205c158000381102c0186941c043c0300307080c10b54110f0b005c400d90564151514011a400d254a0b80202421000544581e011400c8000c4509003400f0350b0300d03582c0b181808034141094040a503070641c40c2845500401e07030990408c0b1b04a900861700c1082e520000c3e00c2c00d5441c400d141512806031202644628498503099403081400003045c90890462410b82d808100348150200c03e01e0045020000304010300c0742c04603038a88010400308030a000c55440305d1080c9035a595a401802d2044401100146c8414850311012004281e2110207008114030144920b45a9019600e40111070403104008070b01c850002044a0003011183d40341c68007102204161541e41982101d49405203800700320000340c031107090010318010b004183d0200d01ca07107113090800044400d032000c0240514a0010440c0b1003000c081200c809890141c450160f0318000c2c2404100b0020740c2480c020351100c3d000c1942142c00c1c0c0d01c8000180560b2050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 507841312 1250 507840062 507840089
    0x201290103110c070501031a04180b0610050f1b060a0c020c060a080402090c0910020102090901120b0a05150a08030d0c0302190309290405060a05160503040507030209010b04 76
    0x94400854800c208000c50b01d60301c01d40c005c1281b03501c00c1c0c3c88003c00c05c481c03a0f0000010140c0303000080a58511000803000c1c42c00700c180c04414041c9001141d50400011600f20550802040014206024100045040e400d020035142242d0070355000303e070490003000c0191045860615100b00007041c0d0b1400e814014815040e50003c603003041c0084600c401c0b4a41c03200341a0750f807240d00b00000e20703000400001004605116211041e201d201380c030062510365400144c1c944a00006206210005074000c0e49144542c3c44000041a98090595084a54180c1c0815207503500e030510200c00190848241d000032940400040d461804009041051100c4009000100d00b601c030480603406100c001010405100c1d0490019500941c041d60065120b503881108010b28004131240007000c40b4602d200700c90b030310020402042024404190f120b0900e0a0400c201e08000200081d9080b002032002c007841030000110741440020070a001c01141e0042601c00650307191801301d69a60014850f80c8007d4510 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 507842562 1250 507841312 507841331
    0x1060908010501140d06060f0605040e0a09110904030903050709090b100303050d020702030a0204150303020f010216030e4209100e0a1221030212160201290103 70
    0x180282c5040b00e010355501c50704224520104a40a110320800310f8865588410019014205002038402802251643e80c4ca0714644600c130541c950004001101d501e00d00400000080c0201400e0100b01c00141e424902c959294601134403208651341001d4420300c1034500c0001c80d80c0b066001034015900c551500c210607100e130b880b150642e100314040103012032014021845907004560151011354001401c0322641040b40d0042411900d000f100d02d10700040800040c024190108049120440c0b454002c5192070544c4402c000b914901200003001c0100c849410320066072803ca00c00409d141c1d0b051500940204c1c1e03178514000d12406a405550b04842101c001400c408107015a036490074040c0c401030541d004039904481e0b4071404413003254000040c42000c2030350000c4010100400b03110b81d00501641650038400b403c888100c05603641050f00400030644d11480030800c21790401203a0108413900d05400c0d00990141ca16403265000614400307005c0d8208a5581e0f0900c3c0e9441002e80b810418070f2203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 507843812 1250 507842562 507842579
    0xc090b1206071715060403080d06050303041a0901050d0203070c03021902060d020f0408030a0c0b060f0d030e040e032209020a080705030403090909060f05010e2e0806010e010609 78
    0x8102c500b0030120700d07052101c00c5044800d95202c0d50080c24034061810003e042d00001d400d0760040d4005442081c4042a0703504003220070721880001c1c0804030700841c1028540710042004042e4054188095803011451090720f9024809072501110800c0d019510392610403401040400c45810a40040c410840ea0703000316103070b440150000b82e802808862904201c2d075004c0740a54445d03c4900645082008005481c41b800e0025054a2308181d51350040e040850604601d407501c054036541c40b840d0144071225460340c030700341181411940b5040c000e83e21491000018000c2800803100902c901000402c16506192004003800304501c85058203880754a5142c505c0c00c130b0280010b2040401eaa20000c10f00180c0180701545d88944030b450f2040304582c60740f401c20191121305200312495030711054094049191401000d0150050713a04150141c40c12403030050742e24603606402c00c08038400c2020301800d1480201c1000142c0300b41000c036025075940d90503520291f80d00340b00d900005020801c3c04a6002c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 507845062 1250 507843812 507843823
    0x4080903010b01051606180203031b0607031b0c02030a0b1005090a0903020c28060503181c1d030d0206062814120706030e0d030509150c04030c090b12 66
    0x360310341c049003030b0110310b1b0352030b103000344215200c3e0000c01d0303d001c1d21040141d400300000c0c04c610724240d00b0151610102c074003091612034007500d9102411300b00347c1c41d4203540f0107406004100b4051783c50800d441a210b030000c241003050800001d0902ca048200b001070140d5800502801c0705c0341030340c00344d4082c1d031115428070441d03040c21030003001a04062982c04442c0352090340c01c10512500c00820383d03081d03110704d0341c10703c450030f01d9002502042e80481000314241c40704078007481c0d10340407201400c400c0342e50360103000220110a04800501407804d403e590f884400391040002e9100c0a0200c91111569041c080e41c1c900e0112401480703010394000c0302c203107909000b0600540b001e00f9191843d40302c3c1841200d1001e40b21625445401c880c900c00b4040c40200700700501030043c101511b0002d010442041401e06240c5141001e01c1414240002c1c062948130002d0907541c81900c89a0040c5a0340382d8058513142d5104a80c00a4400c001e0f03441c0100d1900740541c450b00c0602c008482004000d01c041d000c003601c60 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 507846312 1250 507845062 507845077
    0x12030301030f0f030915030605040e0606010906030e030408011503021903080306150f0304060504021212033d0e010906030f02010804060b031203060307090b100507020a090504080903010b0105 84
    0x81c80d00d0b80380c80c00040001c4034004029129040405000d42c440801011440480c481e40c40040d41300c1400700f0207800e080c0b25a103001109800940102d10b003001c006040038480c2e105140402d035989e113140c0399003903051041c0d401420b0524001c1c403100e41c4504030030071101000d000c2a4412100740c0094900d1400b40d00d41d140403030f41e000011030304503a0348808100c0c0c804003910b40342070104010480945140000320003148240d200341c000080b5428140140900e0210544000c151540020008480c20400005903030384a202e00c41302000ba0840c10503106d0f421009141c00e0380341c400c10281240607a00b0002c640d00e099403002c40b88001182e03a100c030704100344c0c1c03594400501110640b005d46005035201d121180c1d407103405004045200e22220000c80e2408211612021040e480031050091500d01400110000c09003000140700d9890150001050602e4120079081442400525002191101901d52001703010f1240c0400070b5107414104021280c0c010b2003424400e504c0c2018a812660180c015034280 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 507847562 1250 507846312 507846323
    0x203041e12060e16080d02010b030d0c06050c040f0303120b0319120c0b01090603051c0e01230310050f0a06021f142701140f071e020102091203030103 66
    0x240000c82d1961401804522114411405030308a40e090200d00812014001c000302c0000344043c42481000074215400030038554800e402990006410301e43c8210000816500141d0004458490014030821445039904c4040800c1145100200b4550007081106140340c10250602c0400c056000701526615124034264403a002404218007090107144003040b4003d240c18640106144c0343c8802c68440c100b41e204c6080e154407500180100300e4107000509200d04002104908241803902c0078114001c1040e0060411996162912103900b4501d5240004001d50046c15513a040c10182d500244c02d66005050041101d0501302c00d40b402c0401c0c0d14011601c06030b0207003200402d03a40c200ca00301c40d01c1002d2510758544500c2e8040000c00c03075180883c05013401d108004484150486100c5000b83d6060f242c1445034035100e8820001c4075203241c00740e8014107400d517624107036a4205054404889207146504041c8084820390044d60701503000304001c960450324542513404030040d4603502c0c4000d0000402 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 507848812 1250 507847562 507847589
    0x2030607030b0f04110405040605010509181b030406090308060303070c1701060812090a080a0816080409050f041b050f0d03051204060b040f090807030e0301110a0203041e 75
    0x81080c442d0740080d0b280e550007072020b941980032800003801c0c0c0302c1c2016094034100000400300101e16091007070b940101002c1c20a42c0c140709044000602a444e1182d123441c0454903c1c001900086440007191913080468078203d489040506005000344009001100401c01290204000b4a0001b0640c1ea1495201d02c010180310b007000744090745507940b41e0780700401d07648540020450004c11b00c0b0541018900c81103a40c1c44010319400c00000389526405082c071500035240c00400302d106042118200d01c0c48081c0b56218640c90300d800c01040c03107140e200750b07a00c900e403006001c08003c1000c11280a40c0c0100d003e0035400c1140c3c014800e200c0400c1c40b855a0008000d2680072a42c28858000700c200f50086c24814141001100d0b58122031000322001c03500e86503100b4242c541842d0500c540e12180101180400c084100340d03071020346a01c5840c10140501c12880360f4002c2a5a09400001044801044940d02d59113a800065525045401001240e1940310150850702010704204800c50703003034032103084 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 507850062 1250 507848812 507848821
    0xe1909020d12090b0432060304060207110a090504060e033103141c03020702010f1206090f0209090105040b0a0515042408070f08180304090e0106030b13020306 70
    0x60303241011020b0100384050ba840005902c001c1e00302500040901400004003242002182611400140880b0280208800c0315a01640301d02c41074170f6000c0d40c1720a0041c1d5440c050304200d518000c645240c0c5500400c1420b020607100d06941119000d907200da20240590329070100c5a0380c590140240e180011b0b003000c6058400480c1c41950f8046000014403205552500c07900c8050541c0044070801070683c1c48070348417803480051603180c40d031000d01c0b0385011414100303d94002072841518401c084e04012850f0000d400c07440059100100400d80402e0403c400c101d000c03c0740001e50080400c06100380020000010300342094050840b000070020f0070741107210308000412481c07982e00d20303e40342c49110501c004038400c80d060402c400d0344a01110340e07103066a10010b0080401d0b2000b0500c00c1003020854400e40031330303040640b154004081040c3c0450000142544914600459000d48455070600c00740700d41d600019800f190541e40200b144d0320083e41c500e021000688a1560004d400d5445000040e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 507851312 1250 507850062 507850073
    0x216020108061e060913141b0a0503060103110903070305100f0213030201082a07120f0903170f12060f01020d02060621030703030501150e01020717010207020a0e1909020d 75
    0x2d016245c0003c001341701ca2003d4400407002c841e140c1e124000ea600d0b5040034024045103041c0c840d83e03001240c4001e1450214050f0b001450b0b07000141949042c152102106102e89002c0e01c1030315213013300030341280e0b080c590301e081107a81c2d84030400030b0003140c916003800203014464ad40202c8071404500c80b03555030100e244d40d004440c01e04000303161000b81e003003840841941d14500c110b4847c0c00b4244402c91519201d060800700d81a000880020050000c0314002e00c00c0c25402042007821213030016540d2000c04165051180c19124440488a200d01d000038440e26400030301a09500070501910316003580c0010b0b10059a8602c43c0004020150340210001485d602e002550108040d11140f044207004240b40500351454021010071004252030348018085d8512000b24205465840d10b4000035240440c40040d44071000340c0544900800e08035480300e94048250100c03000340c3e030b01628180c003e580e01d201c0c0122a00342a24400f400c00d03110080c11495000034042c6481c02900141003e05000080c0d0b1030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 507852562 1250 507851312 507851317
    0x6030c05040f1401140705030405090c09090708072f070503030408060c0d0207080c0c03101107020108040828030e121209070504111b0a240902040216020108061e06 72
    0x1424100305c00c0d21860b501562a44002d070501070b1282004540707403401c00e03082102650000788082076032102030201110555030704041c1d0740c01c410581030003442074907810340807102c261f00310100303d00e010b0550201d2036101e03800940e481c1c1180c0844040e076000c03c0d129001c140d180c0c0b00d0340c405c01f48141e1202011500500c0044010004617103102d070010b2420469035210091500500b4183c0c0068001c0d4110707a6041c24140f21f0b4a401903030b1100c00f040600c205002049046c00b55441c00b03410482d503a800241089007510880e81354800142550442c00d4442d07442d948403011410400d00002c0c2081c0800ba003200d00002c010701c00340b074032403956030400b4044054440c403004020030449043c4141d01c80041c044c0c03100c0c454a0800c4000010303055a950540100c0510140503154a95260340040d89001c080303080111006686e003400301700c0038585c1000d5621100a000d100308041d41c010720004080602818060020240382d2003a04c4040082d9140c6003000364222524046c0d9505a5102c0c5030000e5a2602200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 507853812 1250 507852562 507852599
    0x908030c0c030412060c120e07121a09210405010c061a0d1103070501091a0318060903031e061005030702011d010b090124180503100606030c05040f 65
    0x450f030070a50b45005034450380054040990f00c842c1d440d42e60040596204107009076400588074184022500706003c0d60750b9079004c0c032403c92244040c11803003080029180440e404001400800328403410400601c540b6060004119644030030186000080390380c420042d1822034405071210f6075a40056116a0301800701004031954201c60011941c0159072010204207504d4010490180b41d08420400d046c50450140c2000e410b02c80901000c1041c051401d40101c920039103418056160f40310741e4103035240d5090380340c1e194036203000d00c030104221000000f0256208000c100001841ea9100c408414004881500c3c0f80c0d80011155210420441c0201d000f107401141d40e2000040600f807400e19416800d003892128400c42e512461740f60110329007441a140509080d025003140a880c9a0118842e011b00841807414441c461424035551209545000010000901a01d007901802c201c401c2c02001540a40710200c0d1611001028940c0706206440c04d91b030301001403c528508000108082d5007c41c0f0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 507855062 1250 507853812 507853837
    0x11805060c2107020714060405060f092b050c010c03121e0c02031c020906071b0b0c16060207060c060f02070602041706130b04030804031218050c040908030c 69
    0x4280c0c001841d05035100b5108403600d13401340003440c0c141001100101d10108159102e84c0c0c0c103000034000c60340d408003100c00118404810300c0ea2801307058003244420441c401d00b901244803040b885171000b8000b030f0b0b1070358505d40b01e0000d07180140038640054801c00300180b0301900103035942500c115248d40941c800301d6600d000301d9401e51030540710216101a01c00b079440c5100141c0005c9840015075203640320040b25884180d0040d81016501c0012030360030b000b02c0602411440c01c01c0303034000b12030b890010744034040e0018009103031380d803148501d0342541c2f8001040351034540420305100244d490b2011402d4016500c05070784007254000e02e525400c0240101031400c400c00c035400c1191070000f03101d51000340010517225030b912605100c0d04030403e0401f4002804400c1f014440f0b003101e40001c66404a40398070075814200440b03141c07100e05085074109503043c80d1540355480c2c00c01d001c0143c0541c54494411910030302c122500c01080209100544085410040100f00f00340007180d42a07098502504010403200c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 507856312 1250 507855062 507855097
    0x4090f0b1902070804050d0f24050a0612030f030e1506100918090c0b0301031406010602060709060c030203120411031009051c020a060207030905011b150b0a08010e06010602011805060c 81
    0x41e01c41d11001421844031880c01c42d03185201c0d24027551280145a0304c071101c4070b000c00080340b52400303581407100342c8075008040010400c0340101c0c039130203680004c2401417600110b66130802500c03462000301109aa08034411140600c84c1641d662050b1200350603a00c0c04450301c030a5502d250780341c001404c100401144d900401440101306848600091802180a8418440075581012201c0c0c1000d0060708800c4c21134001c2c20401a5040d08003110b0ba044403103a02d0f160340408803c1c24100d046005110010112a203a40c05002c144582804d110314660002c4040e2100c3c0c0e880c40d8061401c45141080c01040c5410034149031904010085400c0b03c0a1858010795400c07100741c0c0d0741c0e0300480c0d00640e82140490009071080c007031713540d012180542100850381e04080420098803029141000c02c0c4c21851042d4a5500410043e00c4190500d001001038900a102892440003110340310902402141e00540c0380240512000e0519100014a69001400b503e06c645418855481d964081c452102034040c54 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 507857562 1250 507856312 507856343
    0x4050a09151e0b031518010f12061805010b0102010f020a0e130b0d0b04030201050f010308031506090d06050624041703250b0709140103090204090f0b1902070804050d 73
    0x2034401148118020119100180d440c042001800c020b24190500c901c0c0b0480c6c01400558200100c0f002a104422103079942407060b494082c0140014134803062440004c20240380c100101500020308801e0240c00a00c00740c0341c60140c82089001c2c03541500c0000e0455000d03001c1d1414041313100c0103804503000f00130a440c00c403c0003081007660300d0601100c0303400c0700804000516038280f1610350051840500e000b0300b54503646072001c050101400b080400c0b40348070300704110740d985d41c400c42c0e011503400307482400242064100f00000300b4088540c24012010302c082c0904101503440703d61120f050403401982424104800740d0030045202c2170000e5144020401040d03100d940b0140f00d05142800d1503081a0030f00146000c0f240c01201810360030a002510000748641c0c030380c100741c01e500c0c0e08081c030b000900008a800018041c021702800502030440c100940d205103c1c0c0303015040d00c104001201241c2844600c080c08080b0300c0f45900141c00d001d410b01c03040c40186014035601d04554094104034004811 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 507858812 1250 507857562 507857579
    0x507020a151803090e010f0e060405180712030206010504020a0c12180e070e0d0507060c02010c0b04082a0604080702130f0b040f09020904020f0310050c04050a09151e 73
    0x1410180c1c045500d0a0081103d03d003c03810381c1b070241c40c030044040040303440c028004500715000342c081d40c440c035202d100003040c2c0800b8090414005103008120743c0103030b40e80e01d0003108101941c041a401801418000720320341c10140200d07030700d04045984002800600303480711303804403154132680d000700800501c41d50403104507800c02c0e00240c0100071502219044c000d1001c1c2900f2a5140210b009569103180000817480204a40003100c0041c280312401d0f000c00e2004940711f44d400e40e00102a9038a24003030005000d1444040c000c0d1000350198000148641e00134000502101c0b402d00d02c0c940e00180c0003500096039400074000083c400b41c85c6410440000a40c442075030707810780440c02091b98a000301e181c20318080c0a01d11000d0340c0345008000010003500450548030340280081d0084415541c01c6030749480401c0030300054030031000100000c0c01d02c2d01c11407106074842e104062081e0000540464284007902c03c042d100c50034242440351492404240c030304201c0620215440c003e80c1c4000006d5401d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 507860062 1250 507858812 507858851
    0x20603060603340906080403200705040e010204030b0c13031b26010510030f020405060d0213140708010b0d0c0216080a060e030304051e0c280602010507020a15 70
    0x1810003551901c4041010000c183c0980356205e941080340c40700170300c404260006114010103c1c1d104407850b06401d402030607840d0801c0ca5010310740040c58150840d07108041036004d8030542c0d2040c05d8034101510307108030315890740c060102100440300c01000100001a5145848803070700004080714200c16035140394112001883c3c4201888040c001071a8203c0b460080c40307030a80c010007041040c031a80d410740d00c44c00c44800413050000d006e07945c1c540100b030080d41c0d089042d600300c0382d008001c40180040d690038040584080e40880e04194080000b08401c9402500c40d80e041e11800600030341800303440030702e0202070301e5030710000c0341075000e07101100b24141c0155011001601c1400000d21940707410b1300e0408201da210200000040c6c109006103c0002c001043e911920106c90803030149101561141604150401d04019841503901880400050854a10300100d02d0554107004800350746001c2a4240e94080340c102005070008a440300000754084652010312235510000202c010f4600315050300207 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 507861312 1250 507860062 507860131
    0x100e0a0203090a170c0c010914130906050c0d110306010507021011070b120c0403080a051c020313050105060a0806011214010203070201020712180b0c0f0715110a020603060603 77
    0x130039000a03001038802041140412a050030b1800e50822440c107610355800c00c403445a4030b071182051801440c1581c900e03400104649801c8481004281801c01c4084450381c040b1000d1040c050424180e60084880740080d2449202e060312000d01d444090b41c00c03c2107140744480300909208a0008098804008001c0d00d405001e101000c3c40d035034000c0f21a1036682a0004000140b103900c00c100070700c00100080103442c1c41100c2410100d440d8030105e03882441000410400f00746161001c4104400082c0074080600200c5c0180001c10668941b03600784082e41401d17005404560780b01000400503101e002d040d88200034010ba910010040c00b0a4965083e61320940d4040011307074010842d001401b05600c1080c800c00d005045c481c00d00f2403107d00128001400f48103d60903100042803880b0110824000809024824400c0c0e0f103005455170318540060705110b05410004480d030090181e206000521340401507001040c2030308642c1d41e401005845da200520302030960b08a040300031030864109810550340b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 507862562 1250 507861312 507861353
    0xe01022701020c0604050a15051605070608010e06030c010f0c0b1f050901031509020a0801020d060e010f0e0114010e0a06050403050d0f0f03111c020c0105100e0a0203090a 75
    0x4a5a040e80024070b8440503070b44161086804200070005d6039940b0007203004491400c90b040c03c0202c1d0b06041507540d40100d50701040c440700008060820440c001c10314000f5a04980c50701d240e280d80b952030011341312000300ca00c15010307880100c1c0d0741990f43c09050100001036a41c034150402880380e030398948543c981074451480b20600a6011030491100c83c06a4016000950701007465624640300c1c002841c19150f242990b05a0f6540024150340703a11081c1c401601ea0b880003507690f030b441c204c0b080000744100c0c800c00700480c1c2100b0021400684071201381c0101c60b20410303107510903405d15441c60716144a000804d418000000c5c000b0304113403640d604020052a6075118280c903245903003000c83c140801c1c121000f0801c00703107020000c04a90031680b61981050301e840c001030040c00c0d460050100b8414031002c0140008454001403400d0010740040071b400048600a0100d40c945000d034a002d41c0790b84c00303060301c1c82041400007102c2c21071540c040c41d444207240c400c48441141c00c2d1a401045035101d0b0401c0c45 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 507863812 1250 507862562 507862627
    0x110909160e0a1d1e03070b2e05010507020f0f09090607110307020a030f15020c010f060b0f0f160204020301090b041505031e0106081009051002030f0a0e0102 69
    0x2145031a61088280c821004104148140c64001d502900d0f0030384256040b1034001c0d0008a40e0607800d0400503a846c59a006001501c80c0c140094922440c1d801030500c00c3e50003807000703840039250b80c000d2155011580103031505420160781c1e81c00c1040890310501a41d4201002c110b20030300c81e540c0e0401c0307140a0724141c800740c5840c0c02d1100e0004c1c800316044e01403a02a0340700b0400031b001a140c000e00142203981064101910762001d28058503014280e00b14894100c0c00890741c1b40020f0019480300c0d21071a105181004191341c1d071110a1440c3c021001400c180e40707018030030341400c0403c120080c50342600c0341004e0301400744c095000604036002a001105195614980c2e1981e60030300348901d0407103e890b5402c0d07048031440c08001a5031076100c01050985600905203440030707130300d094002c02c014101c014191044010100035450003402800342c00c1c1d55a1181c10254000010f8500c2201c0c0500a01c0c808000160340308002e40c0044c1810343e240400d5517500b0040b065014a0200d544504205860002c1387c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 507865062 1250 507863812 507863821
    0x81f15170601061e0509030f0604030f260a0b06040305060406020405040b040e1e191b170a030c0f051b0a0602011103160c0210020604120309110909160e 67
    0x1841c16205030030100c1031295200310510b10340000c848038000356955103803007903a84441d02c012a0074000b40009401c850b1181209000c20140c214440c1b14100c01940d503460003030307212402c80122184912040c50041c02644010408012817074100c11040d880c060f004510341503803503403000d250500440d8291125035000c48c06000501c2e09004294030b1410466080c4550850341340c6603602c0341348960710003035a8080ca4441884030710041c40507101310001d1003c1c040400c0340900300301406525420340c2c1101c1a059074000304c1c1d4483d00d9082c01600e40b220800502885004d80d5065842108095059441c3c040b00303000000000c10400044000541e205003250041011390700340098411140c0041d0290390500c0721900d4200700c41401e80b5071101c15480410308035010f0341c80035101d0f0010230313802a400940002144480302d400040b03403800ba600c202180a0031b80f401a200300c00300c1c0c1c010300d002000140099407e003001c1c60090103998005510300180c0302d0f000700d940b0301141c1e0900942d0081d40708407042010013 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 507866312 1250 507865062 507865109
    0x303070c0f090e060718080a03050702031006030c060806031c020f0f060105031b15040803070b0f040f021306170a020429090c091c0b060a081f15 64
    0x1800400e02d046080c4140d14120a03900c3d00d80701c0080c00d0000300800c0708040d2441340303142d04800004215860039550185814203004005920194050307006c4e12445603101045445442101d044036044034200e0840e6003066000c541010b0041c105992610490b191884003e817031146068801002ea001013032094089100641808040403003091030350810301c01000a61000b0505241850f0b0001d03517055148001e4000406098001a0461300e0600c04140803440000000050885034001d2000c2017141d9515030f9941e107040d8007100c0003040740b4228000c1100605064846107201e50841c800404c8050f19040020a45000e603070110310a0fa121141c0541541412b10810000301c0d4003841c9050740c0d00301991203c20b01807695080d24002c5240030b0002d540180e00c201540c4000100074958480001940700f070381080001c00505440c0e404450010410914203d4104803c68140002600c0e100e81c2d1038048070100e0b12006207041c8e13a0741c3c950841806040d0b0032440b14001d05000380c9480804043d00c00c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 507867562 1250 507866312 507866339
    0x150c080405100c020c13150602060708100506070b04030309050f060711030f0307050913050c03010312080f150d0503070c031208041a0709320301140412050403020303070c 75
    0x2111402d0780b41c43c00901445501244004406400742c40c012500f42e20620618000d116005020b00784001032007004c110250701280030303406004c440d91040a00d4139460307103004180c8514854254071020800000b400560200410f680c054080d0400041d03654245d00c44505180031500b0701011900901c00304507445800005210b4112000c500460612511020034400d0f8400908040700703005c0017041c0402d043d5104c0601054441d020542070000341000f45100f00260404e0100321450583c0d00c00e1681000d12130b24089220300d588d04010710a90b2038481180305000065441d41d40c00c060f440d010040421010070040403140c1c42a05004a1640f031410000820700201003074800300a482001d02c00412480c0700c40c6050204410b1b6103164940b141e180940300c00803303502c0b016008100900c0ea00c1d6421004d4220031790603250384100b200005800c0c0401d4200c403022009440783c02805800700380400c0302e103048442558071078109289000c1d01ca800181c0340d600a090b040b00e001003d03c0c2c0505c041e17078860b40d5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 507868812 1250 507867562 507867583
    0x14010f0506011103091507020301150807150507030210051801020a0c0b070f0c0308070509090106020a0605010603050c120406060305010212010f06080609070f090302040c0507110922150c080405 85
    0x1950034840c1a80006d00e1071458501c0050700620003007211801e40da4207520050704010001c00f441e80c444d96800e00d00703841d01c5052007480313a22660705201c46a264003400881e40e08550680c05031100c5100e01d5018001400d018090b80625074401c3c17110120401c0900c0280514031060b100c0c05e407080702c1441d150003c01402080c41c0c04015080d1445000076400c5580001c9595050611038055680d9860480d00c038001c001e6410350103141d40e000000e1058000c2680d8600d10b0141e201403005070b0301c400c0260182e480546601b40a120304003c401c5141040310b40440d04540315400100d0b90715542e45805080e6000b80b101d0202c0c0a4141004211940c604007001c0028003440c00d040c0c2e85850400c000078100080100b101c0c0c00d2102c00f0500c084410303c507520346e5015560080041107001119180240b99801509084800c40442c903c54040c40c40e100009521031020b50701d81525501c52150915003518040e0000c458102650340241401c0c1401c0c010f048d00c041240d81c803841c0314074160500900d020300c01320 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 507870062 1250 507868812 507868847
    0xb0c0405010c08180910080f061909030201060f060314090a03020c1011060f1f0312031e09061a0d20060705010603110a081209090414010f050601 64
    0x801040940d8100ca000380c90160400800c0d901c809440c40d00c1850948500740559229043d507081040610560441105a4494104403805400c28040003075582c00c0c1036451103400001c80401c94600030154000032046482031002044095071404c0f40304806402e82c1203d4082a01d4420714600340c2c8074003015940c8040e035000241088095a140691903100b0134031024014074448000c10849070080d01440341818002d000c413015450a007400c1051742d04141e5801c0407402032280341803e90700d20b15074031105494018034808140c846c00074058008000041400c80b91000c001001d21030f9068a2048540c07082c0900d1011401044084503e00c03d500740750002849040c20840b0700022900d084450b00e10115030301c4c5010117a041c0b0f003000403094098410300815640c00c1002c080100254803003001c04409050b0713501d610f01c1780c50780d0780203440302c5070203215001c0c03950300b40b00d1407030545401124a60418010018003090118580015081d509003040d05800c654a5a0900005582c451651040c080003d0f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 507871312 1250 507870062 507870067
    0xa051b01020f0a0804050906041b0309140a0803010b0703090f080d021218040b0a090905071d0606030a020a0306090c02060f0604050c040e180a0c060908010912050a030b030105130b0c 80
    0x9903200744c2d05024900070b00d0300806603030b000a80c0702e8039a648600d40c16230320b1030804c1c0612404040700501608208000700d442d08541c2101c0c4150000000f500b0490543c4030740b8003400c503801d19101c5689600081d9040d41001081400010742000041c0c1c100003030031300c001c0030b0005002040c4019261451500d16000020b2041003c00c00d02842d074414901c50060403540828441200c1c03000030042da9003908500882031800400c401006400500902120a5051500171242441ca012040058200c841c150405001c00015910000c80c1e40100391040172401c0000d01140c9802d0b04034119055410b80d540903911090070701c005451442c101550245080720284201e251000303894030f0b5400356104003c1e412000c0e00124110000407020303541100041801c5848806d03050402d0100765690380b0440c000300c0c0c405c510202e50808103000c1d03207901503000300b0b00d540d0911502e501107070380350301050810041540e1031400000e513a03028000c0078000e811021450903c45803d00f0001020306000e40b0040101e0000c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 507872562 1250 507871312 507871333
    0x6021501061b0224071401020c032d0703050403060e0c1e060d150609060c0206070308091005010f0504060b1201050f0a0b040b0d050c13170a051b01020f 67
    0x256605100101031203200540d003403030f80f01081c4401c0203040c000c403403101605072107030b05054054058243d09020310a11440030000c4442c0c1400c07842100f054a9140e00200b041c1e00b004104007074016810140c242c034500c02c210000d0820500764100c02011030004070002010000d00c5441d0141d60b64401451000e0041d080801c40042c10010040e22049510924074000f8a2241c3d106400e4a50015007203406201d8000b9030354100300301d64000d00031100031070703070410010178602e228100d051b040765400f03481e03c0d15000040e28141c40010000b0295002032140c80c000d0603e0200a00419000380180820000c2d81c504040402040c0c6c1c0c0290440c1c0e0041005000e5010500d42e55001281115030541c1c0c5a40c1500038207001c100c0d04666500080c3ca10b42001400080a074140e0000300f10642071514100400d4407200188000351084415181000080e42000d2140d0f02d240a9800c2c100c0701e01c501143c04802d05076481600b810807814070003103440c104000398421560180a03d04400c0c000300081c0000f00e41 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 507873812 1250 507872562 507872567
    0x7061d060106120204080313080609161208210105030615060301150e030a0819090b1206031006060c020f0904150f02130b07020a0503010501061704060b04060f0602150106 75
    0x20305100d520104401d00003294000c0360a903045070090588182a25a600d011401142c0108120307c80c110040c465000000c0c08a113021600c06041c03103080070340d407000c070340b0b00700302d211440007140c1040d60700311010051030b14a60003c0840410740d07403211040444540c5410700701070404038028048820002c2c40c40902200344d071400d045a040d40c545486050b400f8200c4a411502c0001800006800d842400c1e4a602804a13010241806c0344140d41b00302c1141c4003070343d01101c0c50300c00c2e0710405400e90000e00090179002504003c003a40000040d0484440b803aa030a081c0742550aa6413044011030980c038850340560920740510715030300704c00b82d42400f075904285d84e502201361100940403e01a83d1458a4501c61451b501240c040c00d941110b4004625100c0e007400225901c0048202c0c494022013800203003904060081c281240c825072608a402820340308000c00200c801001119029503c2d120a102c0c0d546034403901020303010002620000e541045c2c0003a00d09030080d0b402131142c00c810001040340d2075 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 507875062 1250 507873812 507873823
    0x60516020f0a0803041e0b09010b0105090109090b042a14030903040510020a060603140105132a080a11010818060712091722050306070806030307080c010207061d 71
    0x1680903d403aa540d98480c10800703180340d80c22850180e40f6541c8100340082c0300140301d6460040b001003000b00186c1c0302d01030064a051241c40800c5000c0b4145e00410001075000d0390001801540182011803d28503182c0712001d0203a20381c1c8459011901ca241c25502540d00070b00350041d281d89240c3c06891402c1c404d482540c1c078001c0d031040520482c803601c00103a0f03140c824415400d10b41e5100d0004c2c00015128581500c44000c02a4032100c1b41d80780c80001103200e030080340b054240d603820a1155250f0110703a00810b180425841035000841c0e40520b001441d07407000c000c0504918003a800e0b088a45140c640010f00301c94001e08050244901e2140c240c0140c14042140307600880c0c4ca00f0300c0b201108401d10030364090329003a07c010748a8491304820346070081c100401040940c406000384030b5a0400380f4030203101e4200310f002d20754041d44113900080d0f8007409081116006070004040764100040c1d40d5540c0b04647c000003070440c0d00c1c0d4000c6000c604000550041950b8003c91003070121141c402450840da464 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 507876312 1250 507875062 507875083
    0x60b030103120228060c17040b060f1f030c110316060f020a0206010302011103040b03010e10032a090b01170a060906080616050903030d0e03120103060516020f 70
    0x510300c0c0d40b48042c0c514020032081c84010500b89011948210404500900c0c8144080c03c1d24a14144001016903512034581003022070350301d02551000c0e4589407185000101d00402d23194004141c01036074540d559502c06044062020410000080d1442481c010143c404510b5a2801d001c1d050007000c070102c81c040181d4001600c101400700644a0074203041003c0d006204078001810700c0060300e80049540450200c4c142c038000c1e01c6203805040104221a41d070b10a51241031700a40f010b0005000c2c0b00c4030219032075040401c64105462058481d20380050141a820b0443c44508943c500c41103d0841107048070010040c00c04204078080700400080c0841d20175034408500c0d04207500010b14181c00a521010181c0b86a010800c5240d0b155002d5954500007920304050310a100c034489880d40d8410300c00c4941a403c050061421b00da981c082c004060024003c1c501c1003400240040d0300094001100c0c030b07000354042e400205944c1007882d1504c82c84003611559030115006043c224680c2c8100044181d0b50 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 507877562 1250 507876312 507876323
    0x100b04020a05070f060609050a0510060810091d0123150a06180e090a030e03010b0d2310270c0b0702061605010e06070219020108150907030f0f060b030103 68
    0x484d5411300c0e200c001007043d904060112481c0c4000d00496000650080b031040000f41032140083e40c54150983e1a59800c4900d00d4100403000001e01a5096a401040c49144002c81e8060a810408159402c0d80c04001c41c803c1118481000781480103081003c15420880100b8032003d01c60420300841e1001d40d0a018a1042c0040380c0444c0e006149110030400040082040600c81400d00041c2141c84420300304c2c080d00059240c0c088804246018441d42c49014001400d0315540d80c10795454007003040d591024442c240010340080346c0400c8040c820b5203c0d080205000007800d80d1071035035006080052051034860710000c82c00c04000244001e03020819190742401960b1124007a10000d58680324400e4609445c0c030500800c0020443c054210240801d041c81c15a012590341d880200d03035440d20003e11521100c1501c2c940342c0554010b4001c907130441000c13810100707240c3d89080800e4150100381c400307400017039a5411402c030f162100d00c90280c9442c080e81c1c1c00d00c002850481c005c4054081804090403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 507878812 1250 507877562 507877583
    0x15060d1e050a0803091b09070e210a0209090109053d0c0e090708011a040914040308101a0901090515031b19030c021e100b04020a0507 59
    0x14922828481480400e611600712602c20721580303424041d640040e50340c03450034420b0744003440c000765641c01c0700e21000c41d01600300c404560707645808503800c61900c6903168002111450404642003007100241902901e8801440a56a1031040c001110402040c003c1164549406400001c20208160255520110040c0c00740348081e031a40700c00700840c400311810803440013002d6004d4801780e042611045260f8030340c0d81c0030800e180140060040101c92400004003000c1c010303c4020100c447c1d0580480550303940038140780c1c0791030403081100c039a91211450b00f2114402c0004240d440702c50749501c46807491601102c2c602d0039189000307c400904006203240000f09800800d03920030380800008140080c6800d5500c2135050880440361b00980300803400c0280f01d08460303c3e4200c0001243c840c2d0b00e01d15030f016161703201c2d90000c500500220800c24218081c07021550300c000d11a049404200f400c500103031082400c1d010299049030960200700703015900510480e40d1081d040320a88070415008200f0300c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 507880062 1250 507878812 507878843
    0x6010b0304150e39030d12021e0c03031609140603090a05070b0301080c1f111203091b030f030f0f0408010c0f1704020609100504030204050403020102070515060d 71
    0xc0c1016808045101481d84d0200f400c0c0004000c4290030300b8403562510421062451841410780b20b40c0c140c0e00318004034020242008401c0099401040140038461100389541210700e1240c00e1980040c4801070550b001005003c01c044601d0018180e503441c900741020a1031a041c1d44000310307040088803038403400005c00003620300f141c02e00c509403c0c80c0d0f105040d20045511040c0e01e0109420078021091340307100304100c803109400c10400701020b01d640d140c8c44c0d40302d41501030b02c01c583e02d41540c24410700030300132458a100c004508001541c012011034014000c400a404442404208580e071228402d03400818021030010020044070315110036410740310303600c0f1103950100344d5a10507035202c4941580385c0310451042c81ea010000fa000f5048940d662021161112241c03414180c05460180d88464200030256031840e120003040110030301401d2441c00d040d079a400103002c6a90480301500981d4000500100b00b1200388246804041405084080b9080c000c000c45c4245c40c01c0e80b03004110468120480 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 507881312 1250 507880062 507880091
    0x1805010f050c0712170406050322141f0204050d1704030b0103030e09070f02101a03160e2401030f14190606020106030f0f06060f080109020306010b030415 68
    0x54807190105803c690445643d03028020400b40c088030140c420341d40b01050322002d9031070001210100c8805540b020f0642d25800480c6550501801c031102010b40041e00071000a00d400941140c1c5040040140c00000e420311070f5454544000c0b00d00c0e21000d8810041440a80d8441c0d0411100507000070b40e918040821245010b100c2c0f0954201810320409034000104041c1e10400c401d01000003900c0006068941d0340d41500c2114665403c0d2025800041c12080300c54101ea012051112024004442565114000c00c0c01d107610f8250004055610203410300c00124a40318241d000004c01c0d0102030700000d011603c10642e8130f00c005103070400d501c90300342c041854860f82050000220391002840a81415903e401400f1003d0070313003202160414034005030003801807161100701ca4000442e505424502e64440d030b085030a900c0110b030160307900d2201258188410140d400074151000000030b1205d943d004052801074141e0000148180c104100b20000b4810120b00102a100c401d02040c1b0022607410b4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 507882562 1250 507881312 507881317
    0xf030302151806040b06031c020604120201020d021201090c051306080910020a0f080f090709090c090509100605090106120207051c050723061f0801020414010f1805010f05 75
    0x1440b00d5104a070248414419a440700c240160002c40842d1251f4241828005100f01030114840150700f0100c000fa0105085665030a0142885d00c0018544900c41a10404036000130321480c9412a40030014080700301c6501c00c1500c070055600b04907003803050303613030203080c3c2000c403401031108002010004c10308050003002642c131541810142991181e20741240200764050b130b0003144000070507690104441d1404280443c0c0a17038481c50160030703803030300b028580009001074a80440f0700c410759150002d02c4801c1407151a00a0503084017500c00c0903e032203c2001078a64a4024a110b140b42500400200307070498050300f806d1903150070144c0c8880240c1400c50421000310808044005141d0f0180c00c075990140041102500ca010700d5070782c03201486940031004c0545412248598041d2001c91600744c051214590444c83c135641d181c44241c2c82c1c60030582079801540c031006444102c50202005581c00510001810101e0320f00200030740c040700c54080c403a5190307220b04c074144200c0014180f1160321032800c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 507883812 1250 507882562 507882601
    0xb0f0903220f0b2101080c010c020f09010f0e010905361e010c020a0f0b06310506060901020a03050d090605010308040f1707031e0f1b0f03030215 64
    0x202d0300003580c81c0107000b40f5a10100084002e040c10110706400c1092804e00541a59100d0000703101c82d015100056901003c1240d081c0e901411400b01c0003035075601c00d4040380c0602031803040c0003d41440c0151020700084180c00040015040104002c90803214a81500035514480680401d8000050201c449030030981c00458060240030803002c3c403200c00f4002c000e0002c1061000b0855038050740c1c030403a192444000c00910304007402481801240b400008190011001811031800c6010710122030f00035890403204442c100346091520301c0b095901e109199100d4400e43d6024940604540000d44071026098014107206022400d0a00c400d01607024000055008500b00002d586a0500c040640c00520a03240b42919144000c42c0305400c022010158a008600410200e801c603500e040b55518022078036070001c500d001110010480611a032280300340281d40b0403440e00008805c10741050007035000710b030345208486000c00000e54001090100714058100c001d00c00e031205460b0141c14156540c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 507885062 1250 507883812 507883829
    0x12060613080f0105190c0c1502091003090c15080f15040f0f050a0902091501140d0207020f01080c1213050d020f0d080609010b160203060a090b0f090322 67
    0x342d8800850154400c0b0301562a00400d00003c44030b02c02d552081da881c8001e0440010602400f0383c0000d8421518103546084250025041c52245404648006802001140061b071905012400c1c40210030000c0080c2070440d03a4450400f21180000c0c1c04000d0190240c86401d000c42c000408070317016480b00740c01e00e490041042c40140203851140c00945050103502084c42e00e41b201050508100d80310b0500e400d503020302006031325554a0724810515400300b901a0500c074000c061070300c1d24000b65004141ca800396220060310742c4418010311202e5010844800d05004101041c04500050201954060001c0350500c407169500c40c1c915074140d01d84085c00030310b188910410b4900d047c1c0c02140203d00171011038100c40032145044ca00f185c40b01c2c07068841d00d800c2041000140300d0301c030a10004140241240c01861480c94140d404280741050440e40c1c8031003250340f035001808001c00342d1859500840840c1086030242031030458242c80b485030340e03004185500701c100c8d95803400d040125800010104032 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 507886312 1250 507885062 507885073
    0x50f0a0f140315151009050a0603062c0a09020d05070b120f070c0f02031615260f280c140c0601180e121e1206061308 52
    0x780301c510031948101c401a0300c40d0041242041000c6815501e292203030f50700590010701c0006039001d0002840c10204d094003008840c410102d5541c451104d4030004201654000410516160245559113420840f825003e00d488011381c100e801004985a008020920001505d50f030a10000c0c0c18169600d50041150103000c03c00125100304002600341c0301042e10400905030794403443c1c0000e41a04840d007070082070341400201e01141c0500380c002c8885101400f2910303105580710703045103001e1040d4080c0d41418020012140d0450307020781003140205c201c0401e040030039403940360200440c2c0018020014042c8007000100d041c00d550903440c801869000c025040031948a41c0d80010300090000786010905021000c0d20010310030040314004401d60018003043d90030001c4100b540d04140c4e24003442c082d2150b007209416002408440038010281d50b0701c030361b1500c010640c0b0302208a9120084e42c042c005200c440b036900e0b0a0309200b5444001184c295035580c81c88a5082d45408036074104082d60310071f4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 507887562 1250 507886312 507886319
    0x20f34090203040605010602120a0518041a0102010c0207031106031e0405030c01060506030609040b07120c0815150414031c020f0c04060612020f1e0421020901050f0a0f 74
    0x1180c1c002d500590140000f805560f0b2030b072100b660b5486440a8401240808012420965200c3e8000d0040c2000c05402c41e60402145000507080d2100781c0e10f454403820701d048104129607024818440b040d00140013512440307145460301502607504c95945130240b20004000740f00188000c11254843c49880700c1c2c84844e007064100a59aa04091042901903203050030110f4145810015280300c2e0200812100e01d59540340d1f903417030044c44082d103d042400321803070304501c2e40343c041c1c011142c4c450f0055a62950341c2c940f6035408200c001003801c42e02e00401c1c81c00465044000c2541c111003e0b1044507100440c0c48103120080781c43c010380000000d4003c4442c40b0007545940d804a0011480c580b0780c42120744c40341c503910800c02107031054890034004ca03c40c0c0c4000c00c010030054024080a0000e003819a04004101c846290301d00109040442c813904005400d109022403600b0741c205d00a601c01404d6400905a4041800307504180a010300c14518003020741d241da5510050280135000040383c0c60155980e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 507888812 1250 507887562 507887579
    0x20c0c04060b03160302090d0f0c0305030c01150e010f031202030f030a050106261305030412050d020f011a060304210f1d09130201050f220501020f34 66
    0x41071350940c204881c00c190040300c0741d10074000c0d40c689040041400c0190790055580d1420000c2405d0105c0d07940c0c001c11740000100e00240050700d6080490000030800b00020f2441c1d5a4407003e54204003912400e0100501881403581e005200b500d80c004840e06041601050907440c5000f8180460313080c542c00801c20a08203496001789040350350a0700d07003400d81e5a030b140000814100705045545025100700014800e0200c201c2500180c84c007420643c2c0c274141d00c5071500403035946455002e40f00340e4445458003002960401c40320401190020080210009494098501c1d00322a64454410300d80407003c0390500c5142c9094074011441c0b66230300d84546564400162011801100c2280420056078150b1070070009101c41c0840d00b40020300c010060380d2420f908544400b80d11340c090b4100082809861031a80c4040b0003003411038150300301d07000940c1031050001c103582280c0d00081d0440d04076230001140390300001401c82e60954414036210f08184110612811070101102c81c0c2d45242180e44005100302 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 507890062 1250 507888812 507888817
    0x160c0c090207111507150b150705160f0305030a051c1e0c05070f08030a021605010b150c06060904021306300302061b04030204090302060a0f0b13020c0c04060b 70
    0x10f003641d444030300703001010b900c0d451401403e2000d040c0005201d0200c070281c1a0303500503010744900030040c280265104c03aa4015076005100b01710341d01c2c1d0018204403029414030303004c1c00051000c00300309040d080c01c654030262031f80101c01894051050220749414404910303480140d085058120030802c50302c08520461640c0701966a0551492500340060721882c401c0c000c9400307681e00b0240307100a0030255641c2c1006640000c3c00c0d00b106590074807030380d5180d0007290506150a4022000030800410550821044003d007131078030090107904215000d1030b030101084850b03100d40c0484000503d41d8071800032039405d141303c1060118403840c105000c62500c001510072400111680401000d0750704845082000daa03000c00080c01580c445d800046411090300d4150b00e01e40c41d281c07009404c01e9640c0d800b203003c1e03482c1214210096000388013084000b42c0240315601c00c0d00286641403101845540106114110202802ca00690000742c0d0041c68070081101c04d040940142c030412809a80385070720800758 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 507891312 1250 507890062 507890093
    0x1022b030c03051308070c050d0b04120f0903140705040c05041403190206030403030f020304080a0305130230121b0109080327010c1115160c0c090207 66
    0x41d00e0498040300c228071a00c10148039440e10300142c962244c1548511200350403800c0201c800310740d03900d00401c040e01d5072404843c6162050041d4200e50401d490030358140c540e05440700c800c1200c1c1e00380c0c5000b0984d1044801d030460350442e03030324040b910281140d00e0502d40e541e000355030040c3c203041100624a911500a20840381580f860741110516242003546270b400104011f81019007160f0301c1170141c6040b030010740d0460710a040006591004520394000c1e60070441c0c0580d00e070710000c18510050b5405000e026031044030b5810405840049500003006642040e40401c80750950001d00c81070083c1c402c4103c0b035008001407c07207426070001440c0440550059550494035007019800d0b0400325414020080d02c0d80d8050f196030b080d5541c080c0c1e000e08103025555002000c00d804585801c1c40c50083c03240745900990f0f0303a54900700e081d000300c9092500c407014191151440f0340c4401c205507241c80504141c20724246107040780c40d4415500741019100115002a070140380300045480c1040740911070380c1c010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 507892562 1250 507891312 507891317
    0x171605070f0501090312110a1208060a050603061807020a02030f0705012d030c0c020603130c050a05130b0a030b0c0406090b160215040b1b07050a06020d0e01022b 71
    0x407a4076000116462241440010700c1410203011a014050141b440d40c000701c0c1203481221b00076851901c0302c900041c5c42078082d1000c214000305100382030502c0084240640390656580b0320303508158000c07520b0064260200040000e61a02180507244217001041075940c0003011545c9180030700c6d02c5240c45404a01c01c070303070111720722181c24a201c01d01e2004041211810003184200103c80c804290050459a203940b01003004e5640c00d040180d8600c00a9130007030640014081c042800f9162003490880d40da001070f48034075000c103420805680c0301d680311000f801e4000f01c00b060101904e40803503449445a0001000440810100010340d0710303983c0a48100c03601d40d510014526900d1901c0e00c498130030458580200c0d280c400c00036003d070030403426103158501c005000500c3c1a980300380c03c032000c0e085104003450410030302c0746140740c441d020441800a00402c541c29950140780800180d550440307007170080c0c2030100076120510b050380244080c1e03030384445034204000f0302c01810502d20941e0490380042c401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 507893812 1250 507892562 507892589
    0x92f040b030c241204032c03030a030b121221070c0b07020f07180b0a05090f040510110d0e01060609061d03030c030c0d140717160507 59
    0xc1031500240700000080081d00d01c001031030400c541e16810a01400203280d8207002044000c48408080c542035102c1c500a90710b0203000254481101c80180c240c42010242106511002580780c1d0080101c8103080344508001600b103c602c40070820030b0100b40a42c5105008412940d8810450303440101440071412142120511454000d214095002d070f42010015030350007000740000b03070421744e0a40c01283c3d60040f125032681c0014854500811a00b00540b2100c02100e405070070343d164014103060240843d00001282e081801150303c60b0b1009002d240d1110300c10703010a0501400744451003041c190008141b00c412000c4007401c0480d80a200700081282c540184000c1c1c540040c480d120030b41d51107980d41507849141060448000f21101c0104c0c1400b807035501c0c01581640d00704024004907621a004d19242c0543c840b03120304002c0c24500d88411b00180740f94007a8401c0c2c00408480595034070501d20101c00f00460010084c40c017075103080e002c10b52580c1d400d141c2070010014a000840d845091000d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 507895062 1250 507893812 507893831
    0x130602070b041a1803060907050f010302120a05130506160e0402030403020709020a03230a230415020f0a080604050c07150507140708030106020105010e010315092f04 73
    0x2800d120702e00c15254103c1102101250740e041040040000c035a441c0342c001440c50500c40004d04040060701c1080145e440603d080155081a80c000c45140c1c2c402d003000c506141700303040d01c40d4120301c00070907819646a59500003901281c00b901e1110740250800c0840b112494004810300540b00384520800205e061122202024901030084902c07171981a1b000c1c09007a40380111150103500115074250505894081000c41c04100080164502c2a445001c0c60310f030070505c440078100c4088400c064a01c8070b150380900520406204543d400a030700094840e208418141440001c1c000c07810b41405508000981c51001540320800600444040f81c04004644405c4d4140d0040c3c420840002c0c01c000074010110026005a400190300c0a50790071f0446200c540d501c941b0407035500144085500c04d0f00400184240c079424441d490250031180c0d048820341d415034441801a030f90300307024202090307100c802503010045405074865046034500d1034110441040e00742c0140c0301c07500488a90080c0e14008010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 507896312 1250 507895062 507895079
    0x41e0b0a0f0908070209041103030f0316050c0d0f0504091103091005011a030901060f082401060e1002010f23090102040f0315020c1606080609090d1805030313060207 73
    0x103142d40e99200c0312607850507602e5828050104401001030702d441d400d40c00701844d01d8074207000a120b040c070f404850940c0c80c900828589980346e542c2e040c180400c08103120201e550710000512140c1d104c201d007003c40140508071004c4982e80300f103401201006040c1541401441070901c0a5801641e0290655451601c055100b0040310402d01c1a070071800f40003940443d03441040ea00860300001e4010002c920561501410b40c41040550702c0919240e0001421220004002020700700c403030f0f00404880ca10703515108008000000e04039001d803164151a2510003814000d522200c24485400341c24030914810303085d1046605448100400d036501e03e100041c10441045c8200c038291139050701d101500504580b0380380d0305811171b82524000b46500b0000c00c01000301c1040504400c04c1014282d007400780c28548000c1085c503020b000c00f03005006607030600041403c00b04800405401d1072a10f1b4466441014405078040d005501c880d4040c000041d01c1d500c0a40b091910030251030003502240e0310303241c0d0350051 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 507897562 1250 507896312 507896321
    0x30312050f1f03020904030206011703041d090a020a03110406090e030417030c07030605100503190305030901060e011712030106020c0409060b040e1c020a0f0b041e0b0a0f 75
    0x56014840a200001c20040070782c03150b0900810400d410452481c0c03a81d01103070745044103650a401590100c03004119125850b210710103035a0f0043c0c080c60500d80780c82409030780d1690b01040e80c4803842400b0000740c0c1102d42004007086c43c980081c41e80d1f164658038109a2420054486c006014600b00100490548001d0040000050442d0021845d0031700c0e1214000305541c04c1400c92905000804c441081220200591405140203200008032414040c0103030078002d01c145e00960094200070208500301491290f04062035402d030a02e95a80e0352906c0c411030050007250001c00651904100104480114403044c22042e4400811102c4a040d010701c1c03c140d07400700b40320f40c000507845144184064213280d000401304900c076040c041090000500050160386d400403020030682d0108080b0080401c03504d2502d0000d40250010f042140003070303240c0992542b018140904406c054002240030042800b8000484040000002042d1543e41c94034045142d002d80c2c0800303002d4103000a821020810348034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 507898812 1250 507897562 507897571
    0xf04021c0504021e151b1213050a0b0a08040501110a020a0b01060201050603060109020721030c08010b0a0e04091505040308040506060609090403030e120f1e0f0a0c060213060903031205 81
    0x1841601305e10400c4002d401d42c4602c11540380e000701d50441c2d1001c103000b000200c1c0c054020861060307c580b0216841c800108050b030100c0e100712a041c20412140c400c00c41100e01000940c6808403a83c3d445042042c050404031507802ea20802c0000c1c081c1246a01003a00f8120030700c11811035900c0e0741d8903502282030b81c1041d2103803075141d00f101c401008251450b500a0104611902e00180c001c01c50180f54100e0501040c000c0012035268114007001d50303031004941c0d0140c030301c10100a0810110101c01485005000e041c1400b540d0341d030103890309000c114424820280e6200500740300b249082d180c001e1100b54255000c440a20031900460320a03d400e805a4081030800761485010b541e41f501d084002d000d84210300c540d0b900541102d410001c00741001414441c0000007240e558280c810603182001030300032102c1d001810148270062503501190300715860074019140010a60590742003100081c81419080c0c0145001d05e8030004629422041d02412030340207071140041032112200c1d620580d0022135 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 507900062 1250 507898812 507898819
    0xb01080109020f04150309060c050306040f0e0c270c1308010606050a1b05070b0c0c030705130e031312061d070501030e0c120f2a0f04021c0504021e 65
    0x10081c805d500000c00901e80c070041500d0b0101d4441c0c81c0ea150903080314071640c10b8800050001041080b241810700900750868140d1204000f111304040748551074000704040306100e52150300c549500032103a1150060034804c130000712082410051440e962030b41c01858445400c00c40742c03000084d029018800c0e40110740042d2156890442c1450084980910b040409440c0742c0b03005410801040313042041c0c2c406081c0c0101c1140d0350b031040341031b1a4641040c582d02644240d0103140d0a000d01e8540312881c50300e20f1102040842c0c2d5000c00134040f0308600403d20b41060101c01244000313a03d503102d04103004454012030040180c03003003130710f003805407003800300e0303c1314090f41c030a11007040194420350001100c0180b01041e1381074441524001a5803c100444541181c1d000618880301e1080a00a121041d003041c4d0300c00c0380081c0e0309001000c0c1c0d10b040508a03440f0b41c0c540c00441403503407680d804940703806401d074098500500d46107452030001c0c5016241640144900f81c910800c1d14201d200e0042c80c41e030b009 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 507901312 1250 507900062 507900067
    0x303111603030207060608030d050703050105041e050c04050d30080f091e030903160501080a02131203021539130e01030b06010507080306060304110a0602010b01080109020f 76
    0x151002d8010398007a800c121a140d684100000311002c0600c098403040d50038000129950525244c010203a03041030b04114403072480c00c5e803800c030401507146198a40950482e008109030350f80c80041e034154043da6100c075411840c4540c00e842045055490410781410503070002e0030194040340000300c00300e901209034010a501001281007410302d611095449100c5000f2038020303200d1688440b069031507214480d021540003107413a00c0c0518043c0140b104000d107080b00c1d00022454980001c090307038005000544180c0d400100c0304440c207043c50a0310090082c4243c46c100703d901c03901e4001d5454010302201c1c104505001c02103a01200300c0000a41001e8605458800920880e000e21072091014810341d02c0c4c040c0d00300801001c0030405100f500c018048500c1507000d85d03166003007621000000804e00d41c1000002c111010018600a055a402c00019642c468480c2e886240c00e0045071004084203034051003158001450903030540000049032800e990307600d026607032110700009902402806c8203012a05 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 507902562 1250 507901312 507901357
    0xe031507080f1501050a1b1e02031207021c05010b0a030c06030b010806030706030e0a0219050306280e0a052d01060503071520150601020f0c100c1707030311 69
    0x640c1e009451408010b4492147c04035a40d500381c1782504840800071a0303101d152140003507113820b104854080d40c0d00000c0c01e1030010154000356004060060207a04454421501790a01030f096102401d8140064104500076440c8c0c20292034040451040300002801c1818841b41540b08140b098066800507004000c0d082c1803520540c0988085103801c42580716280c07a41c1e0141c0d603603420305074442c1d0001503034820030f60500060608100e0010468044903004007210b181d108414509005900c10080c400101030700701450450422003013600150140c8180340040007004c480e004401141120080702521035038000000c45d0aa40d25031140c00c0d8541c205d880d041200700c0054408240c04400c520b4140d00028160011182d6040660041784007a80b00c070580d1307840b45648061540e041442400245035040c884a902c0e540e59030460533840c050704502461006450050300c04031b81c4140d001505104840d1109200c9986810450f4264000303418012100620134142c0100c0e07660241100052491343d54 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 507903812 1250 507902562 507902567
    0x8040305030a02090d060c0306060c0b060f01090b07030e040b01020c031203061f0206060f1203091003020c15040c060903151808030405060403090f050d02010e031507080f1501050a 79
    0x10200c14001e074007044040440d554240000e40d00c61b02c14200081c00f403141c1a001011140d15400c98002c1c4031080c100e04011440f909400f40d4451070449131a40e07001c2c0c1c2c000c0100d851000783d17440100d9031003010421104250f08084410781c01e03030301603c7c1004244a07084c01240e4410896803455010b0704100b180c030841d003013040000d541c4100040e01c0900c1c0c0c00701a011040248124503275007001604001c0c14420245015a51400c016904071381c9180c440c1d801503201c0340c070303441b900c03c1e01d901c82c1040b2800c117081c40340281c0503a05a02011010340d03d02d0305250900d014a8041143c00315503450410802051484c09001c2c50b50540b900a100c0401040440b500d4100a12141c6070800844e00300000100001c1d01040c0298411071060b800752405083c103280244c0403103450703001403061981c024428003841d20340032803000f0b02c2c0343c0901e4101028809040800e0820fa600003609030300b50565020464000e4010b042c0c1406690003080704580e6035143d080030313095503e003c150240058820000b1100403031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 507905062 1250 507903812 507903817
    0x3150f01120e0c0d050a030210050106050d02070611040906060909090302030714070302150a0f0c0312111215090a0c0c290114010f0305010e0c070c030b010b120703090308040305 78
    0x361510103c0b503640080700b00003001020703a000111500e5000c250480100340c3d05014101c81c11403188801d010755410124040c0150298442c52001140d001c81c5040070701896030044039038284840a00d9503030700c1d100c11000c1c0150002d4007440c00820f00107000000c40ea60075120fa00ca43d0b9416902440c00d0a00c80e0355030341c5e1903c0520000020b40d200d8442c0201c09692604038401300492240c141980e9851100710103048004030f022214103120040e2407030380101e40c0109180304101103490b40055024000d6825504c54040c503000310f20890041020441411980c0710f0058400000301e4040100e5030320542c0c034906407000740c070440300010410441c000000307100014002000717004403e5001c0d0420f00f003107041008002603214202c686201d008100055030444a542210f2290f40b84c10301041d818100425007250000d00020804080080c241060010004207040a0359200d60080c2103941d41c0c0c01600c3d05900200b2a2680305c00c4400701203078806000e486150480c9505440f880301780c0c0d6440c1c0b82551241c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 507906312 1250 507905062 507905081
    0xc17070f080d0f05070804020a0303080601121103040525030303180803100e011502031617120105040b060702010c111c0c0905070503060307090e070506070803150f0112 74
    0x40003008103140c0010004005000b10003003607400040c02040d4494120b042d00c2d000b5006009001801080c000940c8034120a942500e0b01418032000e00d44a0310012142a0640d0080c00034082c0b034800700560742c3d4000320055006500070802c996851411070501440728400300d103e01c030080701c800410000680a90860a81c1420303614080710640403944907001c0a60080f60700c076503d02c681d92010300060f140d241030a405002c0c5550403c24107a0000c9010b5641d103d40e80244180b80c0111004804001d444003030f20b6240702c0852080750320703400281c020a44d10442802001e12031824a02e4046082c24070009466a40741c050790340101c804503030f45900000603a030314680740e0404400d0074000c1145001c0410600342503c1035034140c020170b1615211600f2a0400b5010400b0000200180001075400165007000d88140b2000003c01c0982c1c0b00e062413401c2c0c080d52143e44c10140c00b14240741400f00c07110186100d040050310020003502c5000c20890442c0c410050b03e804603c188000c2410b6411691114078070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 507907562 1250 507906312 507906323
    0x9070618030b090c040c0e280504060312080a020a09060e01030e0f101410030b0c0c151501020705131a031b0a090606140307030f0e1b010c1707 63
    0x806850b03072a40d00110604035038449896210f40190409403d0610420130007910610b0072401c40d5282c0703c00180c14800081c480c00040c4580326100800c501c03811010401001d00030300c208070950b0b0300d02c1d141d43c6503086a21940085806a400200e02400c10300844402440c169900300c002c0381050010780e0a44140407123641055a10300c4040c0c80500100710284034600100018401c2c5034031109007005507004603260480445000040c01100c9039000f0400c000d4961044e2640c01613900c42000740c2c0d1501950501008a10503001c2075074000754100c41c1c3d80e0240f100c60710f4001c01c1c0040c0c503006903510000c0d8400d00350040c03c0d0540442511040d40d121101502aa40c0f40f020364140c1c54000916011802000e0007820076803490054441ca07007000c80030000c090720841402a80c0c41c20350301501c2e802c0c1c10690340d0f102c1d400001c00a40c01030700c0f0b540000e0205203888000c0241c1ca600c0c00c042941e604500c400d10441c0c05004486a140e076000354050703404140c1c000413000d0416414071300025907811403001100c6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 507908812 1250 507907562 507907607
    0x1302100221030a020d0e010213050d050a0f020d2a150f0f260106030b1801051504151707030204080a1709090c070c14010e1216080a05070905090706 65
    0x3445c100e008202042c030b131980015860305000c440c0b400c2454660703405944103d801c403240c0d80c001213010a40381c0a007604800128005413407400440d2240b845918010170107200d200d141a8000c00001e1103c203005502c0407000e24442d100d03035048680c0b40ca40e903c414007080400c01c0b0000c0340ca00c2800f0440c2060064130348401c4c0915145d03601a8000e0120307691032481c42d544001884519854894229004411a1448226103104903160300c80f240600031180180003900c14031440407022012100142845140d180000d135201c0710040006844200752082d91024002151015119000341c0b003c2d2410f62000c2e2140f038401d5a01c011030391404140d4580f40e2042406640116551801c00c0d5126441d07540010759100c04038500084074650365000350f051a1b1440200c0041c0c0d9900161098100006590300c1111420185141e0f1400380800a90850001008004500190301007620303035040c2d00c92011602c40c59180d42d00001694402c9504c00250340c014801003110a1048100071004582c10101c2103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 507910062 1250 507908812 507908827
    0x609090a05060f0d0b01093e041a0715020406020d120e010203071206050d0b040b0415020c150f0124110303010306090b090c061801171302100221030a02 67
    0x43c1855030740c16042c0c6170316100c0d60041182280034015148604104155036400d051900c10340301c52000000362034603c2d100b903480101d2841d035459049a001c0e00110100b020b19041c60b441040e01030f0f10400b01103540c400c1459440d142c600d494000c0c1c909036560381e0041c041c2103002080c211009031030542c100e0b40441c0c85003152483c0d10028402107001b658146d84030220b016881e40d01c942590141e80c89a4000d005041020010910a10442e50000c0c2e001e00c6411094485060485110714132a0301e010b2500e100144403e5032010021702c01d82300c041c180c0140602c5a807a082140034444091041c039103185d11104000e1010000c4040c2006150840d007071003201500e07001c00040c90751700240c0040f03890aa0301d0155505110b1481340d12035000340382c04010004c84030518041000b0340500070a0102840300403a4652040e0b000d0300601c7c080c550290503048151a00e0345c980039080602c5841a40290602d200042c222413002c1012950a0782101d00c40b80e620101140c201d52940c8002c2019245550a20a04 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 507911312 1250 507910062 507910069
    0x30b1e01170109090209090a03020d05091305240a0e15010908120d0e0d090501110705030a0b0a05010f350a0b0106020f0a05070b07030e0604170c0609090a05060f 71
    0x98042c2c9038500f00060403900510600032440c10240c9600302980c400d485000020b83d0014040010a2035854510740707ca8500c2d0204180700d29a111050080d801d040c100069007450a1889070b40032030b402800c2070003940c42c130203000300b03075100d030250440c1228608002070b440d20803040440c0502006240c2022140e5503003031503509204281401001302e0b040004d621400e480d95002e0401080c01c4003002d000309049454000e006612184682d030f050010004558901c0e05003408590020b29010782602c03c00b020510f84032003022000c07074100450750b1800b800410003c200c101e1800c2942d600003586548100d10a4101115400c81102d101c520520102056000c20080c014000e181d07100b21030141d4254101700011341440490b003000f035070384e0707200200c0c000c003044e800a00c40007140c21401a103603495102d41400c494240c0380d980141d030459000580020764060701c04508580c134079248107a4040c03010000030003c59100744a5044c0e40440181c0105110403038990000f40c100e200204854603617420003011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 507912562 1250 507911312 507911357
    0x70c03020604060512060901120201140c030c0102210405070308031b040303080901061a0703110708011803020c03011a0f130c0c02010e0a03030212030c0409140402030c01030b1e01 79
    0xc000a1008030b62005941781000e8240c0d00028111b03503032402c035070600d54000c000c0442250068100603181580010141d043e50884084d1005482540e60b2215001c0044d8040c0d40304100003181a4441081841c81c1d0681e68071550082e507002002c2c040103803854072041e6060308050700e14003c2c202c00368081d47c00d4405c100c2c01007004520079241c041c000e1600341c0300d0908503440c6d0340c000090b1010b100003d2460202000464400580c18101501c4038044100003e1a101260b0015a000c1d0700e0300c80c444010144400152008034802e43c01c841c0204810340925003642c40d071206580c000201d0050f255407910305251140c0460102400451140c0c081c0740488080d81c240f1004440450381c07103a5900c05550b441000890320500560b10622400d142d82e4009660b1001119000b03140c85021000c698400c8614044600404160006112600380210103100150003aa0101d110b0300c01c488070040294068001c0d0018042d00400c0481c0b01c1c84451030400605070400c03615410800c0000817010040c1e0071058 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 507913669 1107 507912562 507912569
    0x12191b140915033301030803040b090c06040302210105012603070503160f0512040e0601320717131a0406030b01090302060a020d02060105060717070c03020604 70
    0x21001c1c40e09070161007481310b03004e0a0b00c000003d1101e40b001035405240154552046901d58400072907440e14085413540d0044020701c410405442c260080310b00780700c02d0070b00810b942d00c4282c84050859509812034011600b104402c0346418641d407000c1c80c1c0307217201c400041d403400e50241c840c1c581d03d010360b0b18040306880a4103200d5080100c80451000040e80c0a0219004240002880d8025030401c0c0074000d140816040054441e602c12200c02c008103000480c0e0000604e492a0314041007084d101c4d03460740a403000c10000c00080d0a040f032894401900d0310540752101b11000144001d042d0030340c011202c40c220b07044216032880d102c404580c1151294100060007018650068490700c0f11a0b0000c0e44c0f1603070209048105a0300071500202d2000258203845190b0303200c1d800c120480c020000c010741241d00f524441d1a0f0408100d0007000381a00501e079004134180d4030b50004016602980 = true := by decide +kernel

theorem cover : BRFrame.Cov 507733812 507913669 := by
  have h0 := BRFrame.cov_init 507733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 507733812 ≤ n) (h2 : n < 507913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
