-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1589
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:44:14.671598+00:00
-- url     : https://prove2.me/submissions/adaa75f8-9527-4a60-aef3-c93fea9a2010

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 285611510 ≤ n < 285791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 285612760 1250 285611510 285611519
    0x16030809010e060d020f13050f0a03030318020d0b01150f0e150702060a0908060105060f0712140307020303070f0e0f100e0402070602030f0109270309120308071206 72
    0x140140c0c0d10386442400d081c0c400810030008503509106079000e03400d107580b0024000300710300c4000000d008070480306410043e0b20b81e200c0080c4000d0314003464002d03601c030f5040c0b80308100191107a0080140740101d01021038a004072a800b15464246681c0b08403607000c0200014080ca0340d50f44040a104412441c0080c01c2c5910001e0141c41c07000d243c4c03540350040c00342480302c0b12210103520444480e40e40c090206641c03020704070001040400039020f01c070114040c3c000001420b03e04401500d1a80d0306a08015262a500c1d0340c4202040c00d0a800e000140203004001900100303074200034511940030f81c1c000c0c55591038054802045600001000370611000c8a1020b1540c2c4a181c034a41d103c5405803000014110041400e03151501102c5001da4440d000141c84401c028880e005580074548000002c030050b620b0f0400c40c42610300d003004809144085041c1c004540c1b41340d0500144050080c01c00d0f208050b20740702d03e021311390007d035020703000b0502c2c520a0000080e031118450720150401d84003042241e041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 285614010 1250 285612760 285612773
    0xc02030901091514040e060a05010f020304050402030a0e2a0d030801060c05100204060906110615090a06121a072d05040504020c01050f0106110d08070215070806031603 74
    0xe0051401503200240d100c50824004e082ca0420410100b94640e01c481e541e59185c1c1d80700724111034681c040c0010041c00a03195010b00c422102c2d015141d0043e60400d82850140002034000910901da0300d51207005114490000348003010542007510300076114608900d800115148001155500440319907000a0200f0350080e00c81e03066588030f14040e0000301c51401c02a02e400340b5aa5241c080a01c0040c0004045402c1828001110075503202ca0070405e02200090b915030301c0840b921541800720b04102c4c411450700340000356100318140c1001a00503103a242d00c412040c407002c01110109a0b101641300296400b52419901620610f0301144071480e0344c0017440d101f03114842c401070181035106001270070344c043e1084e01c004e0103010b0401c40d00e07420070f00040d03800381c4401d480c00080c00341c0700d50011410a11403c0c012018040d4000100111000c004080394a500c0c0141028218003562609101c14007402503030b24015030542e030752000282050400c2501308203c20203c418000c0d100c500c2040050f03103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 285615260 1250 285614010 285614027
    0xc120c0d0f051c0504060210060b0d0b032e0b030d21140a15080a05070312051606050103230615010c0b0c030a0614060d1a03010e010f0c02030901 64
    0x1071000c00261090328524202c2d180c04981002c00401c03000c00140300c602d0070b51010141c02100c1c2198201d4a1080d008100c4104680d11400340400d80001080321b079608050300d412216004601604550207079050300050382040e410151001e83e0090340079400e8185c80000e01500e03003080d00480241000c1040044058a08411040856001080104040a20400c07036010f4180ca21012180301c0b91031400c40400c0004088060304614404603900b0302060807070001600c00c07207481d846002041000d0440e19075460341e610000c908001c00c42c3c1003001ea0000c81c400400c400d0b20b03a02c181070100c0c0d81d50442c034240c140300d42c611a500c003085162814404440300b001607669000640d031111480d108452000480304100c94000150010f0096410300001081550085100340d0901c40c04001e81078690314169440101d940e94035601540500c46c4078442c92041d8010944015035110400d50080c1030800310b42921400b5826402696403510003100003059406521848401c61014501e000c0140740040c2c407009 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 285616510 1250 285615260 285615263
    0x30d0606092603090d060f1404050304090f0f0612061a0d0f080705030a0f021c080c0a020c100507170906040303120f06030b1f06140a05090607050c120c0d 68
    0x220042e00614103004035100c140024100c601d440e581390924801805000c1c0d820302c2c1c414078002501541030052040180140e40c80070207185400d14006102024100c030ba502a0001c4c1c0d0340d402c50500c41c014038441c02c4010111940c0320342c84641c207410a0000c48ac00e01e10030940c0c600743e204000c107950341c590340e00e00c00c1150710506072032440485060620541c05402c4008040e4400002c4501c074070b6410504102000c0c4440e0b080b210094616604000a0340c2c803542d400e00460004004101c00b2411600900000a12841102c1c8042413031000100070790740300c00c418004504005901b60622240c0d800396031094082100c103500e4174040101240045c4100d10001c3c08011640480ca07041c003803650464a400d030790210040c0b00064032810300002d10001a5061000c0c802816903050305540c0000f4410f00f2586542c640300f50021010350202c12584c40082d4100400608204106641e61880040d0103c0d60088009141c0901c21106000c42000d10103801c3c24550701003d58981290350742d0030500c1c4000e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 285617760 1250 285616510 285616559
    0x30601050d060605030109030e190b030f1f031203061e030f1a090303071b15050c0702030102030f100501020a050a1113020c0606100306060905060f0705030c030d060609 74
    0x21901d03042010040c60746070442541942131039603e0f018954041d08495220008035030140d070310f4000c5030b1015201e00c0b8510803034074110030600019098943c400301d00d030f621068803180e031110721ba02c81c01401408440c541084801ca5103a00003144810703814407825000d00904d144445500e94025001c65036103185100040900c61035507841e034108544171010710380c016800c00b00101d40b0305088814507200c0d001100d030100042c1e0841ca81e2011f640c01c0032000100507030488040c0c80365281085805018104c01030842c1e600e007804001c0a001078500f44000d40c0718100d502ea8640301400c0459403890417000c5580a541190b120b038807540e02142c004140012210742c8249070000b040083c40218018040c1045000e05040c4085011240020f000c100c0c188503e00807182107590b103040407001e8007124190b000d0100064040c000a1100d403c2c8070b03000303003040c0003501c200d68204800313680d50f2407940c1e0283d850724280b60004550402e508131a0300030a000740c0b01d2070400c840c000341001350300d0300b05c500e06140600e0103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 285619010 1250 285617760 285617779
    0x4120306050102152a0f090913080d0e03090303070305040317030c0a1b0c060f080c041a030c070f0c0e01150e100c141b1c0f03092102031b03060105 65
    0x900c01148001708244059510940e2030309080410300d80035802011045010703040401c0095020030006c0740141c5460b611100e072500b442043c480c2ea0004103651481074903184410071801d95540d5040010304070141c0f09550782c50740c4504618205070301015800306028500d100f8002d10440458642c280c0d581040549001c8151528449501107808500c800140100c440300c032010464580c0f0481d0614030300c100b40c8816100b40c0743c14600032010720861294071054400c0301e1620303c1c00aa100300035504005c01c110650b060003450385034804120685c2004840070350342940100707c4e411854400034010509408280d604040c9203401820191b0304030700b0244213546507240c41d901340b0702500900c40c1094000c03025080a80031251400d6850000c4800300309884a041c0030a400382c50f0242c05004100109441c03201c66155a5540210308408001d08809000303280c00081240503580040c1c2d02059400000f0750b1191070720b030040c1410612414a605035245c1c82414521440e100001c4890440e00144c84086c10b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 285620260 1250 285619010 285619051
    0x7020d0c03150501090518030a121410060906140322050a030207050f1906030504020a120302060103060e010905070b0a03020705100e0f060709050105130e0412030605010215 76
    0x503110819040100b00e030808070302041e840440c41d40020b050359101c00c0d003040940c407642d04240d08584510b5202040b80c0c070401074110020b100700031030b0610912016000c2025810300400e03140c410400c458541403c0030207607003000b200d60704c0034020009006504000c02d46038880441240680b100038805800843da000e004911201080e00342000d50780c1220540d418582c0b58540251221414400c65100744501084aa50b44c81c20340700801d125030b4008840b18440d403902e0010b50190000130402d0780c4c0103140510005080e109a00078201040c40380d8040c2800390306500c6d02e0b0044803010040b03070046070300d031036085000240d000845201761080166070540f100d02074802100030b440b4109000381107001c0c4144685200140380c05c8000110002d1050b0ba18809034420401ea5448045481d600024800d001c1000729500401c01841c1010564500702006919040ca03100c4501701a10216040942400c501006603810307c49c24015010900c0545001c038030510300101060001342c0584030092080b00b8001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 285621510 1250 285620260 285620273
    0x301030f02030c010c03171b030a050a05070e0303070605090c060a11010f0b0f014508010920010309060203240303030c300f010905010602010c2f010203010f05040b0405090307020d 79
    0x42c603c1008001e0283e80c0c5c40e011214401502c130a4cd052240c05083c000815080c500407400c0705004000980110b040211585920015050107071080a0a00038480030701b0603600d85200a1440712041d0b00c9003900404046092400c465281140c135250519007007186e1450359800264a0001c1001d19240e21001d1809818500154004000072500c0450540b00000c046884490005000d140c411041080d540c5040d1603084e100c03814002800700341c18040d020101c2c0903a11000708445810b00d40002c1c848003c0e0348502c1244d00c1a5034032034105900e1405c54240104003039014042013020b80246040d03041c00511102903000759844a6860f25850f0700b80860800420141d50340801c003041d1825042c18190246054550207018040700303182400004562075005004100089410783d0740d1078810602d000d00c441e00f48100380c4100c40144581600a00065030900285d03021307250713031604451524509010401159481c100b80c40c0075074186410000002c02c00700030f4443c22601030783ca000502ca00b901d860b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 285622760 1250 285621510 285621541
    0x10623270117090c0315060d02010c1a070509120106030201080c09060f040905011814010b0a050712201f0e100f0207120e030d050f0409020301030f02030c010c0317 72
    0x42c0405002c001008003e2000041d8606038050a400303480081c100c070154441850000c46209400c0304800a0360001948682c0c10f001805000f1200300c0100d03c107142001e1940d070b8042e20800001070340401d41c00c02c545060055107200e5400500200480742c50f550018002e064024208050200d01007490145602c4d40e01c1100c580d100e800c111640c2c1d654444104800030b090070300500010640d552101500306056100d00100303905109510326050b860a84114400d42c03203c4910f40c100101445200005403000070b1108001189807030350344101206528070303480d010320324007490f0199004455001d000000503400e40d050f1a9500000b207805040048102d150290180d682080c0c58944101c20b144002c0a5002d000054410076841c541124210011035181e0030031100903525030081045100c80502403401800c0c402c0c00e03525020305140e65010340300200c0e00300740d00c2911841c802c69040340440c90207115103102d2402c00d01700026030782e4543c0c0300105000700000030340c0107040c030303078000b0600310004034591 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 285624010 1250 285622760 285622787
    0x3151804031211070b0406060f0803090d020f0303030a05090c220504030309050a03020d08060d150b01110a03050d1508061b25061d2a0303030106232701 67
    0x1940c80c0b104e45411200301408540640342d80749003207004a01e20b40014004400c4516010065090040d0071082001031108800205e0340407107219000300c0151000e1000d0b601c9403904850004492802421007401d0420080b04148162034007210381e1003c42d0a001c510340c010703c104200060540d00c40c0b074150000c00956001804030b1040300c120380f04043d40025001d0081d03401350790795540d0303858420a12444c21b01c1010010300b2209480e0205a440c1d07078070707401016240c0c014986186075481d05071206007230854802c421350010710002015015074032540184000040b10314000302c42c4514100d02e41e0340311440030b00301c008d00301c0800c20201c202c91291015140d10f2104104820842085442041e0034680441000c40c1c1450418856807002c0101e124043e00c840c19000c0a4002c040c07100141c1f00da010402c209184541d0200d0b403002c0d500d500c00b0005035005e00501c2c0c88641030b042086001e00044081d03c40f03038541004042119400c0180c9012040700215445107100c02104400350060344c040550300340 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 285625260 1250 285624010 285624041
    0xa050a030e16230103060e07050d09060c02150f070c120309060c030203070f03060b03060f030f01020406030b0a0e06031f0e010f060504150b0415051905031518040312 73
    0x9012510340600b06064025103880059441c3c00070240c1e0056003a03602500c1208070038280040080d584600800c01010076290483c4005101462561102e040314000102c50005a00003000310300201c0c1c208d02440e8000310b50301304988180c40c3c02d62000b80f20180b01240245060402c0200c1c041d514000e0b0010501c0543c8048144040c00382c01030b0080007904126458800100b0300410160028024481c5109581036111041d10b1030307840b9024402d40906131203046405115500c0070411070031080c03020340094585036501140100e80714081001c20302068001001140d0712000b030003040d0b42c0004074155401c4080c555810711002e01d03d0680000d0540c480ea925482d42004104142c6120b980e0201064a4044604000c03800c1108104c4844240d41c0c024166207a2080000740a240803c29200c0303004330440c5070142c40d200134141d0364203a4251070311100700400c1e4040107010062105507100301d15241c081d0790620840c0c4070302031005e00c0e00101400280a1010480840b102d02819400a555441c000300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 285626510 1250 285625260 285625303
    0x60e0f061b01050a0b01120203070207050f0f0d060f0524091306050f090f0c0a090b03010908070303020913020a050d090c1a0d0e03030103051b060d090f020f060a050a030e 75
    0x4c95003d419403080c1140003414840b00000c0511403442964044c10b042d074001d01c00c01d820041404200400d030300390568004508000e07400e0765070310004d90f400c107035104400103d5403d9101d15510107440c8040c1990740010a47d10b0120411612810b50055454086400369240c1c0c903140c56115500300f50000c090031050501c400c00003811070310a822800340303201000311040f02100200300c40e2503600641c102940241c42d038000704005159900405c1501c20b00500000705110b15a0307a82130b1a5200c3c1400b280480d0300482d001c01c591820000640309070040760307005d500d8a000580c00801d82d01c1818403050480c3d03918400d400600190546000141c401d11a4a90008001003204a99500030115120150f801c20580a80d52036012050b81d040300d40c82001041c12580340307009150020f655018298201301c051080340706048050007800c01450048664045000050042c420746514205070315001c0c201c204040400240c0c040200c507421010f46c94000f510b60300c981611810503981080c010f94025450 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 285627760 1250 285626510 285626521
    0x50d060b19080a1a01051e03010e07110105040c05060c010b03030409020c0105060a050307260307080c162607120602040611160902250b10060e0f061b0105 68
    0x1008010340c1c036038941d201d01c40d8507925086a1401c1d5182c81161403401da564242a40d20340d4007402c007030072401200c1c007418007000b66000302c4a10b068100b6400840810080300034044501c0d00070060441c03080640d0300a0102d450551a032031003124091091034001d110020301014214402c0d800203242480003000c0c0c030b40d02c41e0f464440304040c3d00614042e40b01365103810007040d403070725050381c02400321030024002d0010340d440c003002030948984058102620040481355110100400e000801a00e8424003a0503103036001c2e00202468401015507140040344030a40034480d02c181c058059082c4203d0203044501394100345400e600b060015444000740d6600030100404000c4103402070700036100e491740c1c1d0460020080e0a86559035410b00100c4152951440f01442400f01c0c640003003580c0010001c4d007010002c09900074803c071122406069480c6606442170042036904010942e000b8602032401840400c0000002165200180c0d0030612030040080c0050f40400315010203200c07498008020050303032410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 285629010 1250 285627760 285627787
    0xd080913021b010603051e100c0504030b0915041e020a0b0c0d0f0512070915030c110a082715030a1404030206040605070e032b02030f0a050d060b 64
    0x81c42c8072034004640000c1e9503010100500c1101d0869800c40d000b030000035101d0720f00c030400e9010700c01004000c0c06403541e40d201d060141d0281c190003646540d10555070320300d13600b82260340b000c016242e0111070b0480c4505680519000107a10b03002a0080f5440d078545c001c42c034825850844812000f50013008075000012441e1112000d40202d00c4400181c0e0f41085544600300e075401d00c1c000c181d8002c100d0512400604c3d02e01030444075840081c5003482c0e140b0a403a003001003280e00000040100180d103500d0200320342540178810400c1ea4008000510302d42c2100d0b036a031407c0740225124812814035080003142410f081c081d90741240d66001e40703521030011400001c1d00103540700b182c2c005030305800d00554801c4148214041d6103e141c2581c040c1840f0740b9580d4800300074080142c01c00081203411112844555810300a03d03c0041c058061454070b14201c50007503490000c003004507030564005215441507150241c04607100c024aa1820503941d41c2c0c06d402e024020002c82d00f002107521004541c24a0040d44c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 285630260 1250 285629010 285629017
    0x2304170604050f03070b070c050703061a040e0c06040e0405070b070f03090e0415020c10110c01050c03010e220501020703030501050117010f1517150909010207050c0d08091302 77
    0x5281598601820a0007407a130380d00c103c0c03800a004000d5807001a40d524403070340400d41d080d44540705079056603a1769161541922200036a00210340c1900b550120719181501c11841350034a1280603002e100840d0b0000342c034900581c40f40a0300a00401c0000d01040f074244112400b07000300940322900c1e240f0508083c034860410800072070101e01e1005004c92410400100e151150303503c80b043c9041521101c0d1113101a41107100131100901c03621000c001d00c2c10750b9000f0b8084100442d070240e03407104000b490603404d5903800b0701040b0300e2010410040c03103d00c58609080d0740c41000d81b0307020b107450042c0d41c0b0580d17446103002e107014040b544003003408420198035401040c100d900980c0c82500030b025110030404940000e128079107400e64036032020001600e0119800f1112041030610400f28000200100d40c0d43d6000c890528130030154111080302e514050503503d0304054440002c40c1000f0f020b946065444d0424454548154030f00c000c220304114142080350f001500240c40c54241c28441c802c080d01940 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 285631510 1250 285630260 285630263
    0x12250c090b01123809010510030b10120b010c05100203060102070807120b07030c021b0312210c0a0507061d1509010e0c03030304080d02040305060411040c0f2304170604 74
    0x403003a1300c0c6203100c03207859211a400d44001014968a80d01c0c01d010060290a2200c442c014503403114104040e95031108000062407141d5110030110328018108801140c405050cc0d034140031250a100011610005106900c1d00d2904401a5a40c0314100140d14061242d401802284503100c00410b03a0046030407510000c0b8492203091046803038054058080d12621059000141d000a445400c920300c44099800301110140584d000d4040400e00d045050340700000802d01081050603d0001515a00032554441c0300300c0034150800c83e040600510a225124020380b0785519042000580c004c0e407102e50425000035001c481d04121600002125610121000c003220f518100820384045804180c000300340c1d10060145145a446030b45003025134004002c124000c0d582400040b00145c400c100043c091801614030388200b484403003c01c07003a51841e4030314104102000401c03e040700c0c0c00842c4c40031000c0799440810b14405032a00e0000035401507500c080d4041c44400d00c04005c1000103d40e090049 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 285632760 1250 285631510 285631571
    0x40509160332030702130609150302100e01051b1002030f150a0f0902030a0e010e030301031e0c050d0201021f062402030417010e12250c090b0112 64
    0x2c034a90114a000c140304540c2e020003600b0070442c0100510748401200c0303541099007400100f00307480d03402480c104c03484858040c00c80420340000b8025850310511035054a200f031304d815100b04d0308120000b00540101c8200c045c500150300031041014009011020580030381c0d280441d20791401c80b042c11200503050310200c0f006070702d0380001101130600209090984202c100b52613003003450001140300035800148501189550b80c604d45104100c20f001d0642d01e120101c000b9a00e0394114104485056103030b41e21012a10810180c120010305034028207011241c04440c3c89402a02c0c03400180d0402800b0000c50b084d003002c09403040049030099100d60152034030004010214170b29202160300603040e10210301c000d684248400c004400c1c10b5a21511604201c44c004107003601c00c1381c1c1c814540300e0341108071501500c010503140d4a00044104d40131110400c04d00700b84d800980d648800c024950140203102c801ca0722010785042d0f503401100d041e115400c0710740c810030644189050310300f150303860070348142d03000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 285634010 1250 285632760 285632813
    0x1b03031a01090501050a050c010905060106020d02060a0902010212180904060219080621030f0a030f0e150402150c030403110405060d0b0c0306130f0606032304020405091603 76
    0x603944540b601da419520182c40c0c542c41d150f180d03607055805410000c0042c0c880d40d00d811041d40060f00620100e0b0080c0210340040c80c8650f010321029050001c001c0c1000300300791800762000050303a800180f2803284030343d10b40c2e8250360f130700d51442d450202030f03070301d00d015400410560900c001c000c0c540d4014500020085009085408221411682400b05032000c1d58003544407a20440205c01d94409903038a1600c0307404507450151003400f0302000da00704c004442c0c080380c1d0350540056500481d002d01141d41060340007138144100ca2004c4c900400341c0140000e0302071480d0918122403003610000b1164500305483c00c8a840342c1e030ba442d15429204529010704d0103107007010081407840c1065000d00711056804981f10803e036507081070505483e000181120fa00000c038400c0c41c0030050b4144602c107141c0e16000004202d841c00c00802400b070300c1a565880441c3c50302d011105120040010419410503411100418103495500d009460803920380ea003460350701101c00000042081e0840c411800906a00c500c1c1034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 285635260 1250 285634010 285634061
    0x1b0106050103061217190c051204051003110f0403050f10060515070809040504050a02010f08190b04020d060803120a05010b0409090c031b08010501090b030c010f1b0303 74
    0x66512a00c201810f41d4600550040010040f0040700d417150071240c003850400c515100202c1c0b00fa2051400180411002428003050050a00480c20760b6012000e000b4076040c039201c080b030301e499008401c940405a8404005407003860f00001c0741e1800c9425040716481d1f40e16420318544511980d01c80b0b0049201c5c640c001406c485e4240580c0b070407104000c1001e02e00d0f120940c001c20881c0c0c130500b0212441501000041082da40390300c02c0500550043c801400109a40d00c0090321340d041b00d0700c101e0140f001240410030128981800806241407182002c202840c05001150190045090103400c0d54200540070a0006000000d070207800d0301a141c03ca003d465001c501c0c0101ea0003800b800d555590100030034020080e16420400c0021b20404690240d29500e44554070306085544200c0c1800d40c500004003c2c0150900429014080c016400c0011540c5200000da03504601e03111181402000c00c64990303800d001d0314640d41501d070b0300c1e11882a50381940c58010001e1071a07410b0707030000039202d400c1c150 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 285636510 1250 285635260 285635267
    0x2a050a181803022503022d0103110a0c0f081207080c190522030309081501050f0f0d061107021c050a0809190b0307030c0f050301050607030e04021b01060501 69
    0x100c0050b01074016051404120005035a41d00202d619001488800400000147c441241c9081113000e00e8040e0301c20b4000d10001103109820b810b03c1e060406052007001448804420f044400b808500c0c20001d02d208400d240042c248226480c010300030320404141000c846103e4002944501481d598a402d1035031a03048455842c010748c2c5440d8500015490514130417801900286041121100c1007043e6107511101c00b2691065504102c0000e418070f00104480341040147e0b030b00788203645403e48550742c1088007207010400300c40400c52003565000e088240640740e512402070044d412a40501c00b1808d081503003109a0b000b10343c103e000303420703441c05a0038416054540c2200d440c2c2c04005844141000c1d1608491600710410300b540c400c1100c154186080f22492555009001c0030301201c1d1a4035211308083c080310310b440351800a001d503120207040690790207401c40b419100b0480e20551542440e0400b100d070000020b55840c3c10500c0042c00076030b0640c03140c402200010982c6c0003441050b46400045 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 285637760 1250 285636510 285636551
    0x90a0807030b1b0f0a03090201030f020f03190b1003050103030e04020a020d080c13181409030706090507050405010b12091b010e03030f03041a0108010203042a050a18 73
    0x191007041d8040c0810060402c404208801c2120f0080e424200005444d1240700795200c843d40c50082a81c80320983c04658050040c001c107440700500850030320f124400269501c1c407008180107940003042d520f0f13041e14820361388640c0c610700c1c02508282c042880001c010300104000e000c02e5001c40c9501a00c0201460540221890904c0071750181160604011090f54031342030151009980c007005104203505654065841001098200c054020200c159405841110903060300e102003400d25004000c40d0000000807518016804400094201020704107541880c40d40d40060303501c00e0800c03000207810900d0002414030000369a00d08a041d84a04820079a207880100c40000415081e206030280c940c01007402a020120103000c2e0f9180902c0900080c485a004480495105a203020403c40b030100703099400d4007502d6440021491030a060305c4030b440c000c5041f003590014009481c030402e84400039854040003000050003000440e03407501d0350b40c1c11100d10414a442140e10300b4520040101812182 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 285639010 1250 285637760 285637763
    0xf09030307050a0c02030a060c03020d06080a0b1b04090c080402030d02060f01060f050c0105010806010602120304030c080c1912030b030c090109020a172a030717060301060b0f090a080703 82
    0x100e503e007006400b41501c00013040b07401a41c3c14081e9803051000320700207000f05403141080c0d40d0f00503501c05030f5100c0d2000320f074010303080100c6603441415000c0004000540c1e03240c10000314541c880340e2a0000310350080300e1042da00500440f070700f4090051401500620070a00651007102607070b0f243c50f00030310f080782e84410403600c00c83e80b071a2803001080818002c0b9103803107810b8040d03c0d00700d11342160030928900b592000c0e440b40d54036500003c0100805581070110704401407198800303a00c3d5003010f4500070401c2d103805c00c01a001c1d020029201640072410040148003a4116202d55203c0156090814a00544500c1c040110381054406039051901140aa05400c4002c1c00140c06908200c14140250012443c8000348074860306200c0d03507440400043e510a0084901c94200c0a654501020301e020100981342900582802401503803908010302e04001407000c0341c0c00b5910765031b201c0064090b04956111581c01034002a151036504142d400500241e0307801e981940250b82d80e040751680c1d03100640700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 285640260 1250 285639010 285639017
    0x1505060411090d0602091c140f0304030b0c1c0c090303110f0304030f0c1d04061a0f1005040914060f0a18020a020c2206051f030915050c030f09030307 66
    0x1003100064113590190602c0e0001600000d48800e60140c071848160f0050b0080c0c4000b02c1d20041d00d480b00d80104161444000139178081c5083c0703495031740d1703030000100040c1260155000101c1e10030303000d01c42c404481d051030f010110284030b002c40020018003480c526020540008100e844100031b401800524803026078400b100851900d407664842185807000c0b91030446003104c1c016000540c1902c0100301400244d0050201c0303030b0743c3c2858a844021100e00d524694800b01c0000b554040342d0f070760501104e030713001c005807403211650811280880e5140300795009800010b191961a40c44400364103a0640304020079500742030300290100070843d0020b481d00c504000041d441c60103c030343d0780c0d05030041d00810240380115145814601c0000e4065400e030700d502c003500110045c03100340400d100d0007a03000414090b5030f0703400c610b002002d8807940725440300f8201d0280f54030740e01600c003000000f42c2d84e10038414601000b0422410124800302d001c0d030083e518050786001a20105241d04000300840e80036006545 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 285641510 1250 285640260 285640279
    0x1b070f05012102030405060117070311090a110a030b0a14060a05070501022a1516180e01090926090906061603050306030f030405030706050313150506041109 69
    0x4011501a8240601c082c080d121200b0001d1521640d0300156025605c120091714044d810702928007001c6900d03200724200396110700c1003040032038010038038502070010a9441c0440d070b50311050003030081c000e01c24080945440001b807540b001079169001d00200942107c01c1c0d1602d40d43c60790103201c143c070000c0341c15901c080d00708283c42c0710364081d41c014294107101e00000f5040204417010b5608101a801120317551000459007070b055444140101121103220004a01c03d50900f42d404220441d401072340a42072005a103c01140b81c01288400d00040c140b0310000143c960711218090b0252040d2a02224030140040229030100c0c128000d12030f405800c1102103007440091010001d40c50310160040303800600402000070017406505002c110725019413621a580c1c14240203141c50424500044855a001440184500d58005c1483d5013214090310f001500da45958013060004141c1040017421510f01f071200d441c0300c2c840c2d5008584038200449007000500d140310400040352103005000341e0701012030f9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 285642760 1250 285641510 285641519
    0x11509090b07110f0703050d12021216030f051510020607080c0906090306041b06020c01140c190b04111e0409051011190309020a030f050a02090a021b070f 68
    0xd0700d01e003581e040e0490459460459400701320b418076a04d80c00c01d1707a480d048400705020380d0380c1050080500c0210071504510344226800940020407010303009403c000720080240e101da5100ea00003000d042500312041249040a007661604001001c100078084c0c143d441c2900c001e40c0c000b01e05648907100780e88890105584603039000b0102e1b4003071105650b00203004e102150705502d0070072a0510a511076200b01c92a00342600084506496690103c0110360000b11a122140d070303c0aa43c100000f01e450310207844400d03182c05182084040a9980d0030450382d2a00d000900880704074050040d4001d60302e003000e0481810900011380103000d2401c1c002803805901010700e0070a81d0105400e10300510135503200c04101364644051301c1c0c40300300e4150f000e071008c184c40105c0096034110710395801442c201041000595400303e800030420744000360141080c490080207004081c0411416582c1c0140550064508403008034020342101030080300513902c410b41f041c0581800102c3e176090351180b015a0384224a003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 285644010 1250 285642760 285642767
    0x240f1606050c0a09180f0c0804021e21010906090302150a0c050301051239040605010c080c0703020612010608070f0207090c0302160c0e0a060e01060302030612070602011509090b07 79
    0x2441907640c2c0d60786c0e485113519250955803180d900608034542d109401e50038107004000014903000c3e0000b6181142c0360121881d91f58403440040400c1e010181904603800454200e801424030b003201915060400c0172601c100340c0e02250101c10780c0c2c0c90008240040e103070044400200d840d070030751032008140204010300086c0f41c241085100c04000404954211843d0401000b05805481c000d0062003441c0100507103c8a0300d4000000c1041e003a241007003c1c0c0d00e450002018102c0300a4003501c1500001440c2d00052020720010002e1034018002640d1801c000c3da1115100340240b0840300096191b0002c40d160764270450340c021a1021030740c001c002d1241000e00d02001011813000003000e15a080100542220080d0411040f45004441203c402071529810b00401c2134000c10000c4100d01d0a01c043c0080c41070540c110341076899501c4d0041c0c483d07860b000401c4c0c81800350001e0301614410740400280e5607a054000c08540c1862183c1c0a2178030350384070b0301002600d4196000a10300030320500081c191034031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 285645260 1250 285644010 285644039
    0x1080f030301060c060b12062409150a090c050904050105091e0901090b1006030e030a020715030209060d060314030708041703070206040303030c0e0f240f1606050c0a09 74
    0x36103800a025200c2a000410303038407e49408000c81d4100000300200d070942d0381c15003031259449114000d2901450b00001e06080d0707000304030203040510a0100c00e086c1d240c8c0500c210207000f200c002041480c51041024109402c5050031511503420000040b5440c18150350b242d01584051041c00142c480451104121517402011802c0320742d039500001d000b24480c00701300e50281060011510880f802d008006080d00c140c2c0044e114554410000042000d034000355180072110050303156089400d522004802034451444a998081c0010801d045a241e0662012084030310403010740741084074146040d134a0b40200c48019210340e1007840204805008003c0600741c8642080c11303203190a40560000300b882c0c1040c1c1083d00000e90310205020300d280c1124500071080012a10b696143e10b42c2000940140c05100c120303164229100319240d00142c20384207443c25021005102901c0e890341c070007041c0034000110b008bd981542400d011401c840000e50840d0501d00c15076640d01411418410764455031031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 285646510 1250 285645260 285645263
    0x705040c021b0f1005090306070c03020601090930030c030605061b0c040c0c1101050304020a03080a03150801090213150e0415061d0604050f061203070b01080c0901080f030301060c 79
    0xd004841da680c070f0307660359440e000b000035860f00d6854844140c0d209052410703100402c141c0a1115100701c820220740c002507500d0444442d542c0108800140f46002188803488030043c02900e000c800c02816003500c44419802c1c1c1c03101c9607500f000444604c0d40110185c0780d8074032625400107000c00ca401000c0010084540c9034810340c40841d03c0f11400d201c04130b41210030b03004000340015031004030b00d0100312180d1252720151509203481c03801c0d803e11750000f4070b5600c46807000400401d000500c029000f4025000903d244002e0b2044d02d403030694031120700307000c0d00b040c040481c407400a07451584007030340e6940b141d00b61100c444212039802506004801c2c1e0f40c0b04000c0c20640b403005400141030303071603002c5000707250260488a08030500441000081c0d0011036000e0701c024400e5040500b000710b0a03888048180d401001190091000b1190300d5903141180f051150207010018044008070f100301001451480c07491090f40d0701c013810303a629818551242e040721200d40081d001000100842d0707202d10140710f00e29 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 285647760 1250 285646510 285646519
    0x8012f0a11060a060807060c031407050a0c0320090c040905060303070804080c011403070c0201030b0117161e080403030506130e070302011101060f0317040b03090705030705040c021b 80
    0x445058540e1442d1660440725800004e8440c0c005220088050103010018501420128201c16450313030090003400b6581000146e0360b90124a00e02030020800c480c174112500400502200f41e12810030441e0600f03c0342e040346002c29a89080c2516091100280c2d1107107903038051180c2440c0c10075081c1e8020f8603010700010340c11311091003074201050040008000a28a1100510602c005400050242e00441074509134040007441045806600000f04800301d40d42440c0000d6080358250061716011072030032900300b40b01c0c012070410003540d42102e110741804000c5e0b00c81c082c403c1c011591b182441011759000c030303000480740004540000e010f40c00c9540c10100040c11118003d403004544811100f0342494000035a00c41c0d4010000d41d40c1011080d40104c2d2450000d019003420b0070000313408103050703100040030a9280c45440e610740d4081e0040e03c01a1916450095907420410301d0b50fa950b01045c020584240180200040c051801f071107500021180754000d06180184c007800110000040f14035980c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 285649010 1250 285647760 285647777
    0xd050c0c07120201030506090c07020f0102070911040e01120503070308071202160b0105010302031003020f120328020d080a0e010605190306060e04081608190908012f0a 74
    0x2a080c0502108010b084160800001c2040c60b00004040d1003001c0d01040c0500d001c00d0a0084801c901000c03141c1c040d40540312560305500000040745030408a41c400810145400e40c60a102d210050040c400c4039140800e01a807a601d4100d4040907103800180103200b035004005110010b4090420745da0700c4540b03070030459800461140c0d0320060707078098010102c801507104455410068041c0e4801d0141001380303421404c51a15045120301c04481d4000030f4403403c810700018071981d880c505064040c0300076506a03910781040c0403e03807940f0007800c44504c1c0b0908e01411812021880020b843e07001d10015660244c1d2a169849580020914800407440654070f90710701280c50784605458011040401003071540c50fa00d94107100d0221b50fa190484e04040c81802c0500000c07407981b80c1034900c0d415807110107114031039107482c100c1618410080700c0320041c14071600421600f45c202c080c07401119909c034002d20250401030100442520040341034110510000c082030a06004a00a400540441d0230403204 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 285650260 1250 285649010 285649027
    0x7051f1412070f0e01051b0a0f05160603020708040501141b070f06020a11010e0d05070303030b040b01050a0903151d0a0c050a0602060604090804030b042f060d050c 72
    0x1441d8003005030082400303444800d1118056100c58071002403419450014499441e01000078030501c03c0003401c0010a4407440399040f401d109010030000240c0c04003480342c10b0600d92074426214081d481b85003010100b8a9400501c0354003d008894802e540b04a0795442c0034105001541e480c2e08841d244d08103241c0a00c185001c0441880d4003030300f86040ca0005201507031605403400d04070880e542241c41190002c0064400203940425040b02d000d109003030081d400f40c04400402d0320080303002c4025156205240c0d00206041e0151300c42d2404e424247c409121081c0640019240c0f407245940b04000070301092010070105140c4c21015200305002c05000c01c0c840e81c40114a540703802010b5203021a0b0700504d0b03c034810040e00c141102d004110980e80005018504100a9126000240104d000e030b46c4608964003080b2620080358051540082e40c9070180c01d203401d000c140f500c20b81e42e07542030601c1807988000016110088a03051201d004041a141c001c2040b841e00250801500d0720003404818000700c1e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 285651510 1250 285650260 285650297
    0xf041509090c080421021002030901020c07030b01080105060a030f0209061504090509191703040c0308040305030315030708071202030c0d0f0b150f1c021302040e0907051f 75
    0xb800032095a41804078101402e00001d240804c0f03107004d20b600c0250b0f001c44070054000c226444251412580140c0360360f00d4500c0c080c0640308005201c0c44c180180d40e8080b082041070f556a90503211140000c224581e0707502c007401840c6407203020160030704030858070803401441c0c6054250340c04140a0905041e0740000e00d020b01040e04150428100541c45004200c900ba80400c843c14600c44045040443c030811902c3d280c107440b0404104c080d560400200103418400103003401e5000395440103201e540d459030f9041c002e890f0b4105440208a40c1900303940c2400c0f525001842034151042e87d07015000180ca4036801e03407644180c038681280c15015003c3d0905159640c4004003201500604441600181700d28281ca4210b4005001104003203100030510034075100c100201c1c2c80c213001550301d2020741e0440c80c00030000c030800100080d885070b40388460722030044040c0c0160040b1050f00a81030010b8840d1038056450700344d5401607a8110045c0030004980c0d014802e0486100c0c40c050405c40b841458121005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 285652760 1250 285651510 285651521
    0x60d14010803040303080c12070807020f100212060d020f011d120f0f0a0b040b040503071b06020106060e06161a0112020a05091009050709080f150c0f04150909 70
    0x403050303500b002c64100306041e08401b850382c0c04861813601c10324001d800e451080050710080c080204100c0c101c00040d20590007080308a50716840342c0215072042040410000203035100c07110f092032202c401c8000c14a20305004c010b43c011640e005024240002c01140111051401f07000c1030000030078065640c4000d520780c82c0c1c808500b0314000010301000c8952032200d600e0310191244015540c0c0c85180c100020404c000324403500154003003d1031a003602c8506281c0c0c55800307216000380c501c1d000031a80c5030707840c0d0581c401d12007100c81907002406543da603030b101a280304006c014102e402080803c4000e90048918000d10209071268001541140540c0300a00141509800aa45181160540c1c20540c41d0000c414001001c00b20303048480340c40e0150341da07428070030584102031100e502c4201041c00340d800784c19010090007100086500c074a51243c60a55184030b041115207480d4038803400314040e40105e40c220390114036203a000c5850503190410211030404603420b5801088a001c10104400e031311401071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 285654010 1250 285652760 285652769
    0xb060d0e03090a0506040f030803070c050105150a121703041b03110a050402190e0102010b1002150108010e030a0f031808070606050f0d0602030a1d030a0f0914060d1401 74
    0x195122112503040c001060f4072908030511403c0e051100b04810071141c0d20140541c6d92001e007064807a19072075001d9641c0b0841000042141d400e200c04c0103a45101045c500d20043e008481c80744803540d9502d08051800d0086d031025000c1d00d154090311950964020007150024070951103002e84110282c11688054030680088a4030f0702c04003258007042c41c14075009405000210f50452402d0600f0040144010345200302e40e050200d0302c480745001da0300030750240f80d491034044d04401480d01161b10003502d43d64004404034094100400100704d003041407180034490f070490f600652070b003442d481c03043d02d500c0141c1510710101134481441a4981e0b40c1c140d4101c0c6c04030702c10030328552140454903119003134840c81d400c503078055428180403009694424881030041600000e00581d20f031562506c2001820b41a80c20750000780b0b50045c0070020302000401003601c1911a41c84492540c12000200e819030044d03c1082c2540e07004112168103072038075500600b150110802c3c00a001b280182c0030680540d0309078070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 285655260 1250 285654010 285654013
    0x307030c14010e0112050711010c050901031503021c080d0f0903030b0d1e150c05030702101802060a0e1306050a0812160c08010f0605040e0a150b060d0e 67
    0x108070030040048814441030090804100380000c0074002010403c0d8044800ca105e601c0d107011490041c0140c0d4506400c1007031600a100e000004100a40141d11100120b40024a80310350310b44668100c141e498240ca40c0140692201c20700c0b00e8550a21079007200c03041e10458070820030403803203841e18030401c0c2072084440030201710a80281000360403a810030500c1401420162a4100040e010702061030180494030101d81c0900c5060914080500c01c01c5240b016141c40d003600c0342c00d85a00314015500c104010340c201c07043e001e961039078842542c000701c699003556040380782590014a010b50140c9a180310610b0552140510280050710b68000e8410103d10140e4a04051107030303041024001c00039100c00750082c403c0708107080c6451018440c0c900341140014189114070100301203005440020000503009224004251403168024000c84c0708180c80b45190601c100c41c9420b0200c1c0c41d0160940203610156034a0b5a0842603025203821030329140d002d0710402c0b0b040140c01492213000b00c000c40140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 285656510 1250 285655260 285655283
    0xc071e0501080411060c03161a0c04080c060d090209040f0c0605040501020c06090303040506220603050603030d0b0307170601090f05090a080c01200702100509130902030c030703 78
    0x2102020002454000c0ca040000100400c0049540d1098140031072106950240e90b0302091a0b1450440c040c10251b00650801000e840c41440041501496400d020500d104080e803604038041c0302c548250310920358950480c40c03400e0b0f102d24010300501151032203040c01241d14444d1354005100c40c1d03000c60703088801c241208824410703c1407203840702c0068115400e2885ca002c0c18140040c0d91888110000f038428040040c421032141c030300f802603400070b03c1c0c00351400f601d032641c1400b5031516801c080c0081003103080003200014202c0c030034016240114000383c041c5103407003210400d140150084a0b0348a42510500200050000003c0840e8400c03265041c0034145075410316070b035001510b4a00502c441030504010038041c1d40a0040303152201160b0040d003450b6107907007520242c0d01402445032a60742102c4c0d4032914500d1b440350b18000702040d40c400c44800400700d020507403d440500407901003a4000c82c03140003040f150390903540b001c100b05000404503060000044002881c00c071a5030003c0f1414030313061 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 285657760 1250 285656510 285656549
    0xc2706030b0f07081005220204080f0f010204030807020909010e030f090f12070608041a01060e0f0a0b030610140c01060806100b070803190603030e03150103170a050c07 74
    0x1d4600c0c64010700f103890300c14614100150f0240d07401d011800340601c0390000c41c466400601c00120b88503c03080001c0030645d115995050404d841d0f2090841c0040e1034058030140c648010810320807907040c2c0b544260210f003030289580a0026998004105008541da250003c00d00d101040001d0601d801c1c449c80c0d2a41d96004c02c00520107010450101d0b10b000d100c1228100c1d5400e1000710780702c400d90780701d80b9240c0c030b907035840307061070500702c1d11445500306040304013000407800c10b6202d400c5180700da40c2a250b90300d00000352002d2280000b0380340715603540f2510500100d040e500e07240310150000c80329131500c1510460365400c070b4180b5501501c100d4000381c2d9070740c50810150005005070759101221080e0b0f180101d10b04034040b101c1e80b140300d20013420b40100000041544d01015580e14042131116400c02c0f01644074500908603105960310305202c1e07c500081d4a80c1c180c0c030403005030b0503030b0740c4103070710214412039405070000c3c42d0041040719043c0841804000c1b41090308200c80070040c80002000d02c41480b15 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 285659010 1250 285657760 285657781
    0x20409081309060503030406080c071e0209010e070f120e03031005040c050313080d14092d0a020405070c0b0412080c07120e011209050f0601120c2706030b 68
    0x441d445080841d050080401041d1740110685007180c0d110b0501d04010307610f8203005103443c032450380d0040c11103450f20700350081f035000c007403440f012144203a80700280390340c0b640303c00410403500325201d0300060f010b5005100310034450651040c0600380504085040041300c0d541d503085800403a0741d9460305000344070400c030710303d042c0c0561500d2104504000f40ba50074417000f1106d8410729004c02400004002030500d6079022142d00c241c000c143d01d240304040304d040207200305403180981c02d03900c00401d1404520312840e045501c46440d024100b01c00910100310303640d090001038403008005200780240090712402207103400a900e0b1003944500010070401c21011005859000041c2c85911516014444400081c0035042c0f041069106410640130070140030004031040480c1010503000e00b41004001000c020000654210a00f00781c416034065a884034044003050404580140802c8c0c5c81c2407003000710059a6401d2070f0a01029910b0401c0400000b01c000e0984000750720803134800e2805410001d00901 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 285660260 1250 285659010 285659047
    0xc0115050d26180321250602040303020a052506030e07050904050f120a0507150617031e131a131508070c080301050f03010b100e0a0b04030c0e1302040908 68
    0x40030003000080d0105170b01c1111a030140003602c43d10000500d4100034001824245100d04135403184007903540d140c4901d8000d41328030555400300d4940c413481182641050302e4a22145420f1300c0c01440c070481c5c17450080300304c0140c240074100f41c0d454050140041500d032203a003681d41c4030714040c00c0103000c045510940d0b64039000c214003091201d04401d0200702140399024048440b459003200d40014030f0a82d240c42c03a0010041d5034450740a4101e0510352498005000c0054290071251084e20900c54200c81420b4045119242e1171700c0400c0358484082c050605c0d0100b50040311000c6845403824220403043e60200514540c00c841100e050201c0340200440c0e110f8200c682c041c011780b0303020034543d00680e03071031465010600070703548a81200000312003a42c409500081d6290320090030303a03a03108846000a40070b08848000749019450810001c51400e22a00481c0c045030f9000d4200000e03241781c01c040c0300c014400a071031403a2800c02e86070f080c805030b075503801641405030159895650318420420400c08561 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 285661510 1250 285660260 285660283
    0x1a030d0503070504030314090901240302090306220b0405010609050601020a110907170a0606080603060c070605040f1a090d030c05120402010302040512030c0115050d261803 76
    0x31041040001203a44442a101100d178103040103d142c10283c50705040f01d0040400c0550401002c42c000184c40320314a122801c03401c5288101085050100011030581c07180f400656019400080414420140da200a022980e01c1d1910125110381954441c0000303c000e80d0240c4041e0344811051004c40304920030140c1082c4240020000342e0500e070b0b1882024801010b1071031064800600045c40701d4043d90400703400350000000f140007807a040304450005c2c0103d014042c0018180c40000b40c090500103903060084550000725410090344da503070003001e018010011103404402800c05000502d608502c14401c191402455807589401d001592a144030105070720100341c01e0078200c0c10002e80000840b243c60744059100003965460703000680282c45241c3c00681c2240d9900056480c005000c0040c00c003000c2c0c0c810003841043c46501c03880348607100d24061140d00ca0b5024030031200242c00c01e00c0c0b40031000307549614080e0043c00002058041c3c2c2060710003207801c10301c0c40c90b51401c520f1b040c4081c0803d030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 285662760 1250 285661510 285661517
    0x15020307120504151a060a09080d2c040b120c240a0e0a0f0e09010605010c080d0c0201291f09170a17040e06040516030f06091a030d 58
    0x20700c1c0580303903083c044061340510300c0c01a648032030322510341100c0c015140310310782c0142000d0364802141c08028209080342c800d02e55035008004550044a1045100d2141c4010358090000100050b0003107400c007009000c0c078164400d5585000586580315480928443e034102c1c07010704401442c0d0400e010008022841c0510303211142406500400103110580e0075218940c0740160141e00c1c01f01c042412501c1c0d541140304600100400000e000d28a00c010512400807075000b84001030b07840b0b0041d200c0009001001703010980911100c10045100c3d404038031607140710701c000316501194610420108140000508095112142017601400c16801c00c07142851010108410f50301c00342c8005043c0001ca00880c00210b5581b22800030b00482002036401c60b640000746102044504d806810f52130340f044c42004600901140010310300d10705880b07100e1064652f4190780a0116044000300d0041900a000005a660307071003011551240a100e842000c41c08002da80359503030a101c04041c5420001002c0350100f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 285664010 1250 285662760 285662771
    0x60e0105100503190501060e04050a1a190f090b041506060509030d032f04060f0302090906090c0c01092d0c05130f0f091b0509041e1502030712 63
    0x12500c00180c0304c4070030756080c84115244141c915125003d401c1c03540c400d81d0074100300010b1009011000c5800a030940c840e2060070351926400200c0f0703150500403222260741e8014100c01001d01485d83e080504200030040002524010301d5590411310503080e50251200070721aa41e03500314013042d219200103040c85040c0681098800c0340000d684240414000c4101515080001c000d40d003038144001990482d50301c030302001d801c0c1c6142c0082540182c0310345000501d4401c0d402c01c41c1d600034421a8802e1101a11000c210b80c2c42c4001d001005001809000018900300f28050000a080c418a9a518403516881d044004008090701070500484407481d90300c03d031b1142842c0007802c2c0f42c03180e01c200e40042e103030042c10064041d00d4078000d04000e0385100301d150030319400c0306820400e036200200a80c441c0e20b401400e6502d01410044c4004d070b900400d500a001500840c0116081900c442950b48030284606a820019a2225005910101d07440c1d02c5540100030301c20070340c0e0801c040140030120315400304070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 285665260 1250 285664010 285664019
    0x170c01060f1e092f09010807140712110d05030402130506130504081209150c040f1403030f0c060103150b060a030b03100c020f10061202060c0106030c03060e010510 72
    0x24403080b00d1241c0c80b49255121400c1c81802c9401002500303604140c2c00031150501c440390081c0b0644d011418035800980b000740010034543c001d00503040101c00780c851040c00c085040c0d4620340c41c0c8101074801024410508640c10956500300043c404520311035035032948030304040c418801840000c03150454041d0500d41000f0440d241e000c2c00d00d100100321200490f0343c2c0c03220700307107902c45c0c3c414480d501c0b501407400c1007045130b61040025001c00d020900c045451142c3c0c2c0300d02041403240914010301c00c0804c5542d204010b1010300e1031914401c0303034000703007500d02d0201000c05c10103050b0301c0301c182c907030003a00000010400d2243c900f400030b10700000c441c0103101c0c9114050028050b407141c0000d802c141580d59004041e542c13000c21400440012174841003042d003010601c0a59143c84410312880b5510801100b2014016a40107207003c641d16442c5003480c100460f0708020306500005440c4081c0d41d40c4031000004120303000c0b4040c004501607840096034130190903500f400d49070003d008011803050b000c020071 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 285666510 1250 285665260 285665309
    0x21012907050d0f0e04020304080405090a0e0c01140c010e010b012312150310052e050d0512030a0207020a0509090d12060806010b0a0201060807060206010e04170c01060f 74
    0xc02c0d05105140c0f0000c0003502600c01d6440544d860b82c038a4016201008100421070130400400964408403810500c9680302a04841581e40b542e40c044100d41002c0254102c0794044c10704540c3d01403104a005041003404900c070b40c21504041888410342e91540b0945c400e035604002c6101000780c00c40311640001d07001605494503440b032481c0f441d808814030400140e00d820100d4111100780c0300142a03580745100d84004001914054800f50181603036240550810020b481c42c21801d0076038014800d081c1483c200c100001e8003040d81003a9518000c02c621168220b02c518029841a02008030050306d42000307006102c0c4c5108680c126600a0001c04280182e0400010b4080380d00100d40c0b0b0003804481c200540c0f00013900081c1d0040c501131082c8000491112004030141c10300440550003000442e5440002d6542e5032018030405000d80c020a00602a800101c820030f80c2c042d01400c07000d842503030020100d0560fa030001c045142c1c10703551008103008001001007200020003946051071504400c200c0b0a9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 285667760 1250 285666510 285666523
    0x3060907050a0f12030503070c08070b011809110607030c0812040b0a050c09130e030703020c120d170702072408010608160e0d060203010e010f0b040b0a03022101290705 74
    0x141c11b1100100002c0d4450f442410401a00c0f588081d040f51103080c20f1601d501c201400b03000c6d803503c006031904603000c1d2002d207110380c180300c5e9004582e000d00c2d0540e070b4044c0101d07603028500503030400495003a01800700d00888020211500440c17055403141c0741c43c2c00c0001d040c013405050b4944550821003800350003d01d41c015103040b90320859010a1322004401030301c004004641500e80c042c00081100403c0c5500441c048083e0300c010f8070f0442844000110141e2220400c0001402040c11800f00a000c450001c105c02d91143d104c1c0103c07103181d91a05403407005101308a100c2d5000b08003043c2601c0e403069000c51024010441360a0655290401c03003802070038a8280006081003003015040d8200c55603030a20308d100c0d10340c1c000c60215600d58580f900c0b0032001c5000d0194800180d00d042c40007800321194000c031021600b8aa10160a0040303284081740030f50f01c09465640e422004d442a51000320945010f103009040340c0b84510542c1d843d840d282141d900354212506800c7d00180080000b041003c541c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 285669010 1250 285667760 285667763
    0x83c090a030209071106011d100501140a1b060e0d0815060a090e0709031211100f02120106030b01020d110c01030e1f020a080906070903080904060503060907050a0f12 73
    0x40700701c95a14400100c480d81142e401e1070170b007482030340c0001510f03580100c002001c2d4000392800f01c5040c0e49680500054480c0791150a00144600c03180024800c80c050140211025510380700d40b03031503180421f9021114020200342d441c0da94a041c03203031104c802005000030f400304600305404581340051040004081d2014050701407200007403c00c5030644500402406000040c1100b1228100707214010410b050f2070004031501044441d110700c0541c050301071007164034074100c002c01d0740d2000100b907200a803550201c0480807513024810350550071b80034002c00f03020700104d540009084059000091a1059905a00080c4818030155442050006c950400416030a08020500000e030380c0d0858030f409240d480ca018450020780c8040c80c00c825580042284050075510000c041d11101400e07a100c010a9030310391302194082d0b5080001a100d0009884e01d0500140b001501607596004a41040300c100e612140340d400c68130040c00545401c072024000b134010b03020501d10040c1030108058044040c24030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 285670260 1250 285669010 285669019
    0x106030501141f032004021201030c0501020703050705011b02030f0a17120a09031b1202070b0906070f05070b0d09150203090a110319031701050f010912083c090a0302 73
    0x20085c0e104001c00c684103205c140007400856079000310105124031100280000c6030350340c1c43d030741c0f0011b03856100003109001c0ea90030402a241a519003001510001d103407510488214a25130104005a50148610310301a1903e0f80070f081d8121207850045100d0404c81d0104480090502c1b070f120f00400c91010b244c0d407004448200052022090400740c81c0312030201ca00d9958011149440810001d038655400b01700c021907001c4890702522159003c015000d1f10b05100e0300b090041c483d04010514800c440000c05009509031006c1c0794035042c00c00070711340c40485403103100b54079102601d0800401200040350a1100c1a04505500b0441c01c160785038000c88502400f601250004440700f1b640c18400c1d00c05103544031111100000240c50050300f001c203002400d981c8010003200003c2d00c0d0404251061040030141c6d16154400d04100c00c1000c101e006100070f035420103082c010882d44501c1038404071005040e02c1c110480c1c4001c0140c010111340300c4504860034144050110381429107030058842d0990740e0444 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 285671510 1250 285670260 285670283
    0x109080c0906040908030403170a020909150a0f2c010e011e0806010909030809010501030305041211300109080306040f0b09070807030c0824120106030501141f03 71
    0x2d0003d000740c401840301908114000060108240d000110185106d039400180d0040380c1e1071155600c101d00680b10b01d260030030b1943d0300142e5028503203031906009880080c414910b42e6141c41e408451858170f42c00c442c1040c5150014400b42480c03441c20120210075204041c206d540c10090401500d10040c40750420020078224181414680b8802c0c02d009041301008440b103540c0e48100c1480035003e2107400b940400c900c100481d10400040c01694140d170f403d03403280c0d86813520b80f903805c21320b0501b801d0041d200114001540340d00b45e501d01c8500e00354a1044214503154515075118940c03003a1806040f014aa8506165000003c5d8a50140e0350700602c02c6a0010701e42d816186d058029011103403035140c0c0440c2a104000d20036420000d018041c100780e90b02001840c51264055400c0b0b03005036001400b1140c414101d0102c00d4012010203039038880640304440da0141300d02aa400d680954000b02c0b05030751100c1e2108004000c2200b07190340990045414140c66070401d0900c1d50b950107900020b0038920700c45 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 285672760 1250 285671510 285671521
    0xc05030406121410080f1b060f0d1b1b0c061115010305030717030115120b0303070606080c0d03020c09220c03050d0c0807060506040b0a09090c1d010e09150c0a09050109080c09 77
    0x3c4040d038110031500e020500a00402c00d00d4bd6901403003154035500032070b400f440d0380c0244602584485d100594065280e105060902c0400d9071801060000c2e82800d01c2028541c2074400860784a0034000d5100320010364030f0740320501e0440450a0303681311900500f1030600040145004891030081c1700320203400c00354001c01c04400d83c0e40207010500308180d058403000842c60100a040d44c003240481e25a5816924003211200420200d1800c280000d40142d109011900b50781c900003072461f0b085508000116208070000c0489000039a2043c42580d00704c000d1101003050010a109400720070160385040242c44410740d0321300289011b0300c84003a021658403170000702140c0321030f0b210200c890b07401004600c105d65603006000180a071010111a2002e11031400107030750050b002c042c040307484406d000c0e0003540e0030582c2482c101040140160701d2440344025142144c40c9032180030b802606801442a03542104a01c081c1804042c0c1e0f214904200c034910041091850110b04600d90301400c5840d004170f42c860 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 285674010 1250 285672760 285672787
    0x1050721090e0f2401091a0702030d08040c06080f0f1503010513060605030303010e041202280b06030c090a020c0102090a14100c05030406121410080f1b06 68
    0x403508001035a4044005101c1c500110b00b0f10b1074451510070000d140d0683e004080b40000c80e07080390f05180400d00080d8140141c56484424045201040b5180350904641c0c0d00028a0040c1c2c41020101141843c028001400140b6600c0000f03003025081081c818100035103101c124401c018041306610007510089800148000f50468043c42c000f002800039091441e01e030b000f41c200e9914104d0ba543e141c41800542c50401209890482e504000b8401d0f05543e183c0350010314141003540141140600c6481c101302d0407034003c00305811000c5901c40700d4941c10070329242e003040034041c108034170ae60b12842e078040403030b95440c4189900025442000d070300c840c0d05941440c0a40900c521f00340c0c1c402003146010454260300302d00b80d40700c00e000700c0d4120a048150741007034400d82c01c4103c02801640007041306200305400b44c0d21540310888681000111030072038500c000d8041c0002e07a400202104058030411100d0820840105c0c0301b4485c50160081c85500701d081e010b0000105a168003660020850f900030401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 285675260 1250 285674010 285674027
    0xc010212030702010f0e030309070905010f060507020a0f0b03014407080f0d0306210f0201140d0902010f050f0403020405040f0210020d0212070b070c080c010e030405030c01050721 79
    0x40d55170280514003a040c201750300c9030422512000c1c14400c81000240345500b9000d061304944403024550901c0d414088111266884113205030303000381c1e41d05400104145889400b0004007250b8040c01e4980d41065200e40a5078001900003906c228030306644050380b0103212a584158184001e86903100d007501218a0800e0403da200794140d00640305007112001d07010403a9a8854103541e000c0001d03584450901e4482c41c0200071540d964200360403084002030f802496900140e00505080005000d003d03603568250b4404d182015540b42c9070301d184030840d40c01c5505202081c09506040f0305116540b40c2d168282c0c0618400a40300d41d44031408a81803040380710302c60742900e4000c1c180114a920380c4102039a1000111408001482484000c9001ca02c4900503100356940c0300381c0034840d81d00e4660046404000b014819500e2070380420061044040c01d10030740e00c0d501c006c0c501854480f484c140400d4100041820500d05100c0c080000c00002010580d414800341200703a08a0f000c05241d040449415a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 285676510 1250 285675260 285675281
    0x80d0309033603143003070203091002010e06150d2d0b01030b01140607030810050a1202010e180744060a03050d051c0603030f0801080c01021203070201 67
    0x12003042c000f0040c455030340380c07002e081e070311010458501c1401032440034440e082d400c1a451030040b4001d1139441905000300110741080042c41200d00705501e1000007885021900c40e2140540e544a10f00e01000206000031584200441001090408000003007070a080069100400003089200c080320460a0740010001130440c0809140d10010146001020301000b8041590110340d21307000001e01000e00b0a000024900207442c5508010a595064800340805404c045501007811004212a103810b08001c0042001c540180a01c46440c0009070003284213011850048180e144040000003e0f00c410315000805403800c0c18008c0c2c02000c14041020303145403c0402d446a140c0f44828411050520820128040703014911b40e03240e90303080100a41c01444010300316040110181025800b030f202420f2102000d47c4044043d0191f00c81a88c00c5074030a400031400b050040ea0038100c15540214458090400d890007483e10001080001c0d6440101e90320a041c1c03108008000390900e8400e402002010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 285677760 1250 285676510 285676607
    0x1401210507200a05030d0513021203040f05040203040804053d080115090608071407080301060201060f0305060109020d020c030c100b030c0904080a02010207080c010501080d030903 79
    0x905101c0401080115000a03080b800d0b1002d00c1408100200403810100715a4010011817610118840d0640589802000c0c880319030b41c1c203000350006d038907000303c4c0c2e4154202d4440951794a80c10004150909040e17a00514050b510500070000010300d17003000c0354140d40040300c11545001440702010414454407268003043d100c42c0d4054071504400c040402c00752000c688a00e51941e0b212100030906505500208000034401041049000c0c001c85426401c80360f02e00d4000c042c88400d4025014941c44000116040c110000c0100700c1c5543c20711442003c0c101361865040d01c00e185856807541c0c1c0c4010f020303100880c0d5001480303102c80e4680754101e40c0c24050500130740c1d85581e4040b41441d00c4031941001701e140141002c0c410f02e0240390228020603c1c800c000c050404a40307450b2103240d82e41d04404401c03401e44d9400c11048001c104080e014044525900001080e603604101803a03040005020200c02414109400d0b400040d8101c1025043c19020400201e15044141610000d00d0a03005216620 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 285679010 1250 285677760 285677771
    0xc0409061806060305100908031512030f030603150601020a080a030b0a03030804020a090e07060e120102040f15020604030f080415060909030305131a130c0b0c16140121 74
    0x20024543c12481c122400b94042d039610f90704a00d04003094810300300c40246214010400160000b000c0c540e4400100d00c05003152520f884050002d41ca1588030800c01d02e110b1501004121840ca020408050060391100c0c001a0a08080002075960030307010350700030942c510120f400030b2441d1099003c481e20750801000b50309100d0340ca01700900321050558040c1e020b4a441c0402140d141c00c3d034003e40b0000c0d140b190040c5043ca00d05641190108039141d9000d6004454000a01c6000001d00150010b000012920003200b4940b810320550821503000300801d64008204010200350454004a2008600c1c100060b04c1d5a1f0780c50411340c13140c06c0759019030701180b8048002c41c4407c43d543c400500d151282d00c04020b0798035580e0001888103503c0350010582c09584100c10480c0b40c3c0210250f03000491101c03281e81a004030303603803e01c4801451300000c0282402017582e6045c68410440704016002c01c4008880c400d09050482c810707908400342060601828489800c4465480351001d840c0c016110800c001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 285680260 1250 285679010 285679013
    0x1b1c1413060e0c03120c01060b07060203010e150a050909100504030e15120c07030c080309010c1409150309070b0c0604030306050117063c0405100302030c04090618 72
    0x40e0000d031400751000361606140722540000041c00003c40c4400a008003410303002c091a900496000407114907655480300d100050070030102e800b4085003885580c000d61a503040001c0c2c0950709000030b214507406200102c42c20096242e03d2081001c1d11000e641601c0c4903a5004142483c00603086003050056182400304400d05500c91082a0607050403a03c0011164256000202900034a8010896444502c010840004059004101e59442410f014114180c40d0300c80c0d00710b5801c2200c035920265111340d80844e03002e6108065400701d80003d195141400f050101007000401d00c41685800d0100c000702040c40c446081290600034010042c0c610380c2c4031160001c194440c0015a42200401d05088020907030390b016869044403001d50541c80c0170180e541104000700c0071802004540d04030781e034045800ba50180503205001603150041120070806184050004866004141c1511440403807010310040e5008100c0c0c803c9507004682c0400c050b6240c4c10030740002c2400000c013025030080d03c5051030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 285681510 1250 285680260 285680281
    0xa080d0c060b010903050303010e09010e1204060f03020c03070609030509131a04021903090602041703030f100b12040606050d0302100608121b0c0a1202091b1c14 71
    0x451140c441d81041c0716031001036006446403206800014541e80090006225007098000c0a0341c2c030254501c00400c402050b90896418000078420040d0b0320703000002c090110325048804000180f03103078581180b4110001e500317140c6038003800c4030090620343c6644e001c5040c580f0030740903103680c1c000c0200840c1100c0704c0c02d65003030001d00b01400004d030a001c0178091483c1a2a0a10a46903090800003600640d00c070801c500704c004118030300d0200c44050b420f000c0803594512a180300000108800001e5559040100003c4000c0c01d00030264500040a105c00380001003030303401a500c019800311600c0c0150f0b181c03481d252028013000d80000d03800c0255205510149540051019004102c02904100b1235841d210029201d00300d49110f0103040408101440a502814030441d68950803a4252a0180742110004682c86200e50006905030080c2c0c02010a5141031400540c101c41408400765500c442c410183c441070054000700d1152070142901510403410540140381a0725a00d0400d040c50310f0801c0d04d2a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 285682760 1250 285681510 285681527
    0xd0906081003150b130b01020601170313090f0f0902060a12020f0a05071b0e04030c05030c1005060a06111902030a0b0a020a030c0e15030a140405010c02060c040f0909020a080d 77
    0x4c40c81411105908002c412031445241c0d00417006a000d81000c1e07081034840710b2102074240e480c409901c010804c1081d1032a034984050b0142c58002804211260205d4516080d2200481c19000e1989090304000040e030b43c5008072a10740e0700c207003020f00c410b180b03441c0000024061441000c04030b800000358403041c1d076030010060011074428640001e2801c14030102640d1500307207000d02c40c81d0885c0d440105000c030b4000c8064101142c451011686440c03952494070b401c14504c548550f01c61a02c0b9030034031443e031400d100c614000c1e000358038000740307080a00b013210390740c41000404803c00215102995819510107100e0a0446600000d0100080c2410010389000754071002d0980c0009181188155003039104030b90141650034020400c100b0010b1403c070950b580d51001e0200481c03a0340d1100d100182e2899440f80a124074050741c000030391a05a031030040d041600c000c145078a055001c1206100c1e09540303402c4502075400d8003500041551240c03011540c821400d4205045a204d1108514015640200749 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 285684010 1250 285682760 285682781
    0x6060910120203040b040b090c0a0303112e200d0506220617030f03010b21040f03030f092004060f08031e09150703051317070504060612020c0a0f2001020d090608100315 74
    0x104824fc520401203851184840540611410200030401ea02400b54101c1a0400c030300901c00400702d60581c2c64641d051a4191200d28842c0e00c45104000701c030034054081403000c01141c00f440c60a11720340319444640c031050140d54640c9601103141581d04040780301d4518141010035501c001400c050074203007c402c042441c2140000d09040b8601c03403280c010b0103070010541d8401c1c0700e0800c00254200c81ca461010b40400315401954070140041c03003044040c0c40c00c0080c4050006903a40c0c10302464541d414200014070301c1c2824400b0000c1815a40f92440d200040c4255640c0a50311100e0300d183c1162140b0400c00c0b440514a1900b0001c80c1c03c1c000095407003003400e0003200300c03605c50356208148420780307031644034034400324011495020101c441c9800410303990300400f05a50000d035550744d40c0319070304455140a135030071000307200a0b255540f40c00d035601d0701c044001d000030400200c011000a00c209545c2c0110740c100101c980100d01ca440c2101e94840c0a113034000b9808108489000c000340080c11007006 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 285685260 1250 285684010 285684103
    0x2090712060b0a08061c05030301060327110108040302070321020d0806100e0a21022826010e031804020306060910120203040b040b090c0a030311 64
    0x3000200b031034042c021240e15a07696101d002d080e5541e0410804030102c0300c148150750f00204526440010401c1c00158003a0001c1e40b03000440301c0c07014049070581c0c150741008001245050002c1004540106a41700464a092030700124569651034128200705940c0d0000b030030740780300483d2040e2083c501002d00c4401c0127194206c1d000c595400b241183d07000ba00307807070302508100c401041901ea203110700303e10751509030041c02c0201e0855031080458080000c0b50203800140882084610861500a40b062203068011442040400c0d1752000d4a1080d01188100300007548105190b0314094010821030215520303070300003084211159049140c40b41d004600c03042c5c0c441001c01c8040303124a045d2090740c2c01110090003d40c100340c454003d12001c5034428840b90240040710f072144054440b94002148202c1c401c140c0003000c0d080900d4800103800e80039001190030741203800385140948422005108403501850310001548851001d04d040605128083c404610760006a03062034000d1040a10b0010072900f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 285686510 1250 285685260 285685271
    0x7030b07050a0f030b010509030f0a0b090d020c06090a0e040c030c091a0f190308120703050103080702041a060d05160816030b04060e0a0b010201050708270a02090712 73
    0x6100721501d2142c0b95803440410781690b1040320b818401d41c0140c80e04281070622178504510540007a144c40b81900280e09264000b410081c00c0100514000350014008001030404100c2248040e480d0701d015000103005440104611429540c0c110b881c8006140e0b10407548900c1c04c01c1c0c10709006403038460100741c407281c07402d0000103410806480b5542101e00c1141004c80c007100c014041040c107298a0340d1140d40070518036900c0c00c510148100b100f0055110360f00355590f810480c00c0403091500700401010515181c2001003011803900400c9820380b5604a4002489601c1c5000302d80d811a02c1e000d005070401c1001c0741c0959820001d41c4210301801150049042039031079481c3c04c59840780112000440110b41101480740700340241c21007244204014004a074068032062180c81104040761250390740c035110f800342000d55030280704054001e400c601c1c0c9031615240841c2c1d02c1e42d198006401d603144440140c4803010720103c003480203104180d4003c100031350714144800c0060401034081c003542105072914 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 285687760 1250 285686510 285686521
    0x31406070e060301080c0f131b0e01080708010b09121e010f1503080a02070503100212070f091202010909090f020108090604170c0a021504140913060b2107030b 70
    0x41c0c142d0b41250070700401084962142c0703080c40714102c504847e164105030f6a2451580c0c504203406070310341c02e11302400054150141f01b0002080d20000c04801410311400c0014072000a90042d6010306588041140c1641d0302c40c2176021409000d0354040c070180350701030310403506078070008609491f8000100000a00074210809003200844e454147c0381d041e83c55201c841000091000006806018800d0042c0c481c1542d440000c1ba091010300c0c1e920987c0c40d80c4c00140040c91182000701950403204c01d01d4402e251411031030020b410225240580c1c880c03242d4410801c01168400c4038400058115446c040c02032640d185054400c04400d8482203000c1801d040000d13201140015105100e0740d003107800c0080c16600024410196401003094860b0b40c09000c4440700540c8981000100c00c10f00150f045559038908101c00c201c00f0703001000c46200300c141c1020701048114042000300110340040d0300107806204c03040004c11080142d150054540c80d80310700c682c80000085018000c49025440321400c40d581c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 285689010 1250 285687760 285687769
    0x40510140105031b03072102010f030b0d3909061212121b09090c02030f09090a090b091b06030c07060902010207181d0f0d0305060109031406070e 64
    0x9000ea5505548900b010400841c04d01d000b19280c01000b50540745826200c0d525102e000302100c450382012580300c0684400c42d41d100140fa85400520310381045602c034200f0000d0307280015a03c0140000b1903002c88041148003603400ca8070b501f400814480710582c2035400b02d0807046224410855101e242110000c0c4440004007504801c950060f0524144030113101c054504142e0210110340c13003030b614034100c030140d07414030040b8403075910b03903113a80e00350038500f040c04e200ba580400a507500b190014408c400040f0301100a685604000321403207142c50f620007550200500c03c8141c0984107150303060074000c245030003243c1680030905520041009912581c00c3c403800d440709070303190003001303008000300000309400e0360040d00224130500c1a02c1c4c1e80c6d41e40e082d0701d070341d09201361400c52841030b81c0d40a0b54903130b4121100c10901e45d8403210094407a1061600216444403122030300c510906840740d00242c6907a100d110064051035100101c00012100300f0032142e80c0c2e850072168940882c0070840100c42d00c0c6031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 285690260 1250 285689010 285689051
    0x20a15110d2906040b0d0f0e010504150606021002031509011805060102070609181103070e090115210f0f0605030d0e0f040f0b06121902030106051e12040510 69
    0x1000c0c06080c58146000317500a6103030b00280c04c200200369903111f1144078201c02d004420b4480c0d0307170302e00209940c10300781086000d10181c1d0040680140ca010f4042003141d0700414581d000e00c1c051840181c40e0742d5150341d480e50480e003004510b0340c030403c010000300c0c800b8610803107840d90480e459000c010fa41c2d01c0c030006a0fa11400c81c045c031408584107000403c0248a03454040d202a81900c4021030040b150350f4100034250000d50300c07800400c803c20203692450a0a001c014014a04100203140051490402600f1010304004211209000303520100d49a100b07600645241488410100031150802030008000c14107801007502c03e0180b030072a25401c0c5c5c0300d4111609500e100414040800368000100700042410081c000e82040c1c0710400444241c0d150000360501e43d12058811005213000a030904444214841c510105031060006002541c0d20009903410300402e6492812070081c00c94610540c0d010310080007210140b040104800c004021486c80b41102c80320340184403248520712092000030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 285691510 1250 285690260 285690341
    0x60e03030417090f101106070e031009080d0b120307031e05091f0201090b040f06050c0304120c170a0f0908010605011d060f0d06080c010c03020a15110d 67
    0x440640c04250b0352520351701900f00b2160a00303060001d4565608800d040850858842011031042a50940c060800340880d440000c2c94601c10440c00456550383c00ea280180083c030f0072060f9840c141741c40151202c0c43c40d80c0c400b00d04501142d40300c0240345402002c040f510f08000700346280c03011079420303c6400f078410303224500c02c01407019222900d03040183e4803e1140180642c110740d280c880c01d90210700280c1c00103014900501407070410000030304010003552400b0b4071400030f0f1503080007007202199105130b5002c54030442d49000c0441e00c50030b060245035070040514065030600000b60580400b90095a524802011600c4508202d550b030300380c80e4200c6a0311710502d404a9a02080d6000c03000030481d181503c054010135032030800c03040410201c8a90041003081c4c603041c0c0d540d20203001303142c1f081020304901402440c0c041c0810045640094442403070300c40c0142481c4c0c000000300c4106030a80c102941d41958801d0003070715800d010036500098840d4040e16207000305a00361007148480c400d04207119a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 285692760 1250 285691510 285691519
    0x9060302033403030203090909030a090b03070c02040e03071703060105181c150f0605152109070f0e0106080f0c12010f03152c0a060e0303041709 64
    0x182c00b010700200d20382c4841280068206404901002d04210b090802850081d40210388450540d4217010038584003800301d0660343d005010601442d584a480c08040d9403850880c140c49468010b81a5000c80300140d00035482070070500244544280000a800c1090050842d552031010040d110091440b0650b40c060004004110784140108200c0004c0c00c040d9000c0c1142102c0022541c4050582c414120222072603410b9000218603414140500342e07240081c480100220f520f44030020343c0d105000b80403c0e0615202140a051000f1104010000c1841d440c25115007171400c00f140c2a1600e6044c01002049001c0140c00f00ea15150860315905944568031202640e482c1d0582982d01114000c2504800c2c420410642c00384001c3c54070074a000b064001c2d44180f8450031071500240c901108115201001d140920420985c108441d41440140400b460601c013280311900c1d4500f000c1c034246d405860744d41051300007000c0700d0001005600c42d07802802035401a8ac040c10140d2003074803e0300f101c1c5a02 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 285694010 1250 285692760 285692773
    0x60e010b0f130c0e0a0803030709080105130609020d060f020405031207080301030b060d0606030614150a03021521180a0f150207150506100201060806040f02030102040b0d02130906030203 82
    0x120005a03c910003811290508030300312461180058000c0c0c0e61a0001c0ea520381010081c0030100f500b1020100241025000a11503860854001042a2234110010300341c503854a08480030354031641141c81001c0e030803000600c04440120400c00280d4410300c1624003a204042104007030034044016a41d0301603110440710303d107901c0d41c0ca03a0104458060314099201c44801540300008601c2d02c42c143c01144250fa0208401d11070aa02201c0d945000b4040c01c207510040400b400035580700d48000082e65411205803680290814401c3c150b0700030f0050850100c0390510ba0f848000071341b00c000314030540b050086500c181d00c901c0c500b591141c901440041603001c000710194005400c0c095469101340301480010300707003c001e0700c9a0024440300901541c8071586c48060044a0400d60f03046001c00c01540002d0081514007000c00d60f03500c030014005000311808501e943c2c210343d000e404543c0141880d100c06a12201d0410320880254001c0d20102d209a01c40d050000380d00c9000c0c000c4000700e80c1c009000d00312 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 285695260 1250 285694010 285694039
    0xc0108060a180c02071706010e0105060a08070f050c030f03010302040b0105070506010b030403050702100f12060b180307150818060402060904090f0b070908070b0414060d0204050d060e010b0f 84
    0x24060f50400e0200f940209900171500314034249081d00748040907401441e05515003015030408041c10b0700903501030002013040c0c02ca000d4101d5411500f10359103140c082c002642d80c210407640c0f40180303043d00485000005407029412282005941170328001c840401941190400650b0203100d02000109150828401002202540c1c00a140d0050090801a01d004415030008030300386211280b85020860b0780c005a20090340c06407000c449290035001c1003181c181001c600c60402d00840042c10b5504588840703c030741c103071402d1042340003c160318510002004455840a0500e01040700d4445100515640b18280070900069150080c0c0d0042e245920f0480140117200103402444801d650030000c2c6800140007652a10040348201c50369618002e6040c1071132a03050506401d41d025905400c070501c000d2202070780f810707088010103600b110f5140d42c80b0141d18003c0068082c0b6405030b580300350584032074400e202058003c5d85244207544020002c4030040820090011200f0803040e0700103510341d01250 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 285696510 1250 285695260 285695309
    0x4030e060c150103080325091401090302030106030b09060a14060f0d0c06050c0d0509090c03130b0c0910050307020d030e01060302222313140303090c0108060a 70
    0x8600144031080d10100d12082c030b002d08a8400a910444015800108103d040740064803101c190400a04400919051a1800504694060192500b81c410f007221400c216070056082d43d009660160080c059103a490070100c000c80c03400c6134020202c2c000e01c00040c402d4042d520801060310301845c64095240c45901c1442800d000d08601140c11000408483e0049081d0384010001060540e440d140d840c204100510704000c00c0b200c140d02800410f12059040d5980c404a2641c402c4030b85290545036540c200410302c0d40044950301800e140481c0051001e000c41710360003000b25034000e641d0b024055854100407a0343d17102c12121a00141c10200c010b80b40301e4030030b8102c40c1c1c039825242c4c00071425075200d40029070a4031240404200c54140c80e088160410414050322901241e08920000088001c151002082c08000c1a0a42000c0401620030802200c08241d001340f0352144216034882c5840e0740b09543c1d0b034545041e0343d40890005000200340e480c104190106454592500c1c0300550800c07051003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 285697760 1250 285696510 285696517
    0x602030606040503011a0a0f080604020402220906030c050a14040c110d20071805130c0314101802040b0f100801030c0501030606050f0d3c0504030e06 66
    0x100d9101d0400c000000e80b030380d400d000e0151041d40c6085508041a8406c040020051b0281c4c0010900c4041d0501001040e1000c01c4041e401601a500075039100302000140c064000d0034042c01858102a88022071900d0241c0e02841c1940d204031220041140c641d0104014040c3d18802c00182e0010b0100e0440a414079400c4140a54000d05240c407a044641410b01d0521304001150780028038a031450b02460010414802039100100000c0c1a03401d007000c4c3c1d40e00c008000059509200f0b82c07584040745e46052180300303114113603030401108840b00f601d0f0315002079100034001020a252064641404140c0c2d500d03c101083c10544a0203050411940d600b4040a001558016640900759040055160300c40c1003403c500340105544190380da60452402880b400d0b032542210f4105882d0000c00c4c80965008421a01054202200d40d9201c9060300120b00190841c880034800a28a20320f080040348000502d019418178000d030321350b85001141c1c003403034201c4400f00d40240000d0030541001d001b134103041009 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 285699010 1250 285697760 285697771
    0x9020f12071d1002071820040302030601030f0c08010c080403030e0714010f1202030a090309090e07060c02040209042406030e06010317300105041a06090409231c0507060203 76
    0x1070720b08046c0e4a0300c1141e01d01001700060a402903e58501d001c010030300f00c01e0b541d8502c80440c803c0d41800e0464000c6036a0b04014007000306048440700c1600e052103100c08040008001074030082c0401c44814000810152054408401090900303011100500003c2111b000303807142405101c0241540f20011501684800301c0c0c6018030000090030860a40e00d0300045100c0c1800310000f1a00304042d00c0d0082a45031158131140740d50b440c0040c000241c2c035003c10314504481142c60b1524280d0098000030b002449800c01c170b1644686464020041d2003158a82400d0815055942c08069960745500780c0643e11182c440340d589800c06001440081c42c2074000310010070600c148203080104c43c21000f603403007410015039104200011005a119510046800e0251130150341c01d0040001013005264030004101c01540300340ca000c0707482800c0d5150340c0d10241c50190046032016200c9080b56210900710180303001503000e400303206200d00d442030200c1000c01c81040300b0340d6003601c1e0050f6500c1d043c0094101406 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 285700260 1250 285699010 285699013
    0x9071b03030c1701030b070e030a08030601030507120f060306061202030a080703260604060f05220e0a0308040203060c040503151b070803070215060609060d0609020f12071d1002 78
    0x41c0c3e040c0103408a50807a01a511511401d901810b0014015105900d00039003181319612100700880010b00e50001d8a400450a00f404038064464000540d1800244681901d00314601603140403004515005203040b280500001c01036103854040640c7c11400f42903010790181d00c41d0380084001030043c0d000f441124041e10f040300090420360203c028651240c00000e140c0381380a000d1080910302803160000411840103040a07083c41c02021903242803405275000081d040d400448401d07482c0c02c1d0049243c15040d5015501c50101c0391901414000042d902640a84580d00018141c0b150000458060f00e800400130110300249044812411100608004565001814402d240014600a000032a10800c06640c991500c140c009113808c81a501a904800220060002070340761801240c2001c103050b1041070b50750303849040c03080190000f80d2140020a2000800c50542d0b101c0c1c601910500410101d06000e07a120300c1411104c80d9403021440403266030791444241d1500d00301900d814030700d140b0700 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 285701510 1250 285700260 285700277
    0x4060518010e031815071a060d120e01030e0d02070609120f08070812040b06010e03060105060f0f090a09060501020607080c120403020a14010203150604030f0311280209071b03030c 79
    0xc0d0198461b088203e040f038102e05011469180010300b01c518950003d0103841010b000e00d003c4c1c94900400140303640000500100c0c0c192a6542c0c2d201e070704450020300090040782c512410044c80259240180d11450300002e2040d48041415103241c201201c0d07041d04140f101c2d42c028505e03200d950090303003c04000c942c4d0750403c000c2401c2510b841c0c00c412348075030f00230315401009140507400945510501e400141c807035044200140507a0350b0b042d064070149109400380d1515030003a900c0d188803501c03940c01216071120840c007000404030314035004030003903131000ea0a0320441d4803800c00644105c081554201d0300400107004626801a105001c42e501038000c0c4104e40104c105078036585e10a40030414159102c2c0d40002c200810102917100c00300a6003070907242c81d40f400345582c844007801c1c1c001610041c10400001c032113181c208400c1000d40d140c400c0381d84070170311061745121700d10b01d280320b907050100e002da610040000c031100d0060184444405e000d401d03c0107001500d0340c003240180790215500042c0304206 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 285702760 1250 285701510 285701539
    0x2030c0705012405040209010225080f0c0111030c0604080901090504020d050108010606090e0402130605370308092b083103140703020904060518010e0318 68
    0x240111a45000d0070141ca801542e03d16256100c00e0303000390489030003035004100d81c7e8540e0f607001542501ca03000400a000c1860810400031444400c03503845100e80b4443d640c0c20030300c040d00205409000791400d0300d5148600d048000d849840340160400014150031030ba00113408280900300a04c410801403504503941a268000102280c1208100c1480e0300c3c0d60f01c0c0180300c044c0b400d00c40c00b0301400c40ba0074001c040c6403170714004094010000380006c0c041da040c2e011800011001e03811400c054071005001c00740c040e1424406148080141901105656580c4014500c00500300300c0001070344c0d08800c110b460b002c0554203105641d8410102c04001080020310380c50300f200341e8410002002d1290801994480d44008903c2c408950789090000325466401d035200c1c8030341e104811004982c0c0c8203404990040c0700c18030f0582071504030750019404c5001403041104100d0036a2000e44a458140c0c081c00304d83c20b00345c020718200d4040c0c0e410b030310043e8010028442c900d11320003803c0e65281d0b0020000182031845 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 285704010 1250 285702760 285702763
    0xa12020d0c0801020c0c01050405130b04020d060e07170610030e070e0711150709030b070507050a0c1d10230307030b07090905060a0504020703030b03010501030b1605040b0d02030c0705 81
    0x1140c0c41882e207658003080a55000d0400e20280e90301600900e881d504150500001a24005016100c036404d190340e000b0072486d988407901654016011071100b003000c25616030501d10709900403603828001a8024048101c4040c40c64850740c01014042d000c1e90b455041c214081d402050104c40c1c0c020b03184030f000310014120804c441c52505c0ba0b036260390b0f00a0640352403410342d807405101c1410b401440c08644200807141d644954190700700e94110301d950280d525001d105961911807880080d019010b0780d0004030a200444101030b0448005196500c12501d000c6200500040d040c1c0741280056440b01040090254030b04203801c1002c4a11408008000d02d5800a844d2207141c0c1d00c00c90f02ca04a80c010058941d400105a10040003403a0051100386400780004222036003601a01d4030480d4086142c2c0103040c4a580103c20402c0090020017140d44c490a00c0d80046c9000c40300350075a8802440141b00a600c21025582252a003010301801d140341010003c0194100402c403031180c00d0180411004140c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 285705260 1250 285704010 285704033
    0x102070209070e040e0105091207031103121008030c0c04020919090e06010510020c01050f0d180c080a0b180c03030403060b03010c030903021c09051008060f04050103020a12020d 78
    0x1e00d40f140c00304034000c071090009480d0114040d100d2a49403004102d0b0803040454000000034401c0c0b2015641e05052406039102d01501d40f2180c41d602c030101c1d00c502c02c1c11003000414002c580d5000e000004680d21002d045c2c0d03c0c400d14428803116089807400007410b0426401514000c035000309032003d039000340303001e5442c0e0000c030358080c060840d2506001c2c0314461051104070b0140070700342c0f08403240340c9603404040c1d82d802c0c1e8040e500d4100100020f11500c4e0090303001c26a04e03c041c0b8401e0900c503445000d9030700b442d803180c110815201019051000a00f000c4005480981c042e40700c01806a540d0301c210514101d11704840703486440740642500500349036418001400554030601001690102010a2600711b59a4000e0308050528012086000c203400240300604440c40000600004a00d41d2046800020f6580300c10340020020031342c0c80b0116007040d0794501c0358500741c4855800303508242c200829030f442807001a4008015440510101010034089040640042c00702c1782542143e03900e0320780c80b06 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 285706510 1250 285705260 285705271
    0x4290c030f0d0b09040819030612030c0302010c0f0e13060801150609060906080115090503070b070302060a02030c0301030215071a060111011104060309050a0209041a09010501150309050102070209 86
    0x1e8000070260207010180c400e4854403101a10300e0f01603490240d84100d554822009802129285c0c2c024600b00d25209401460180c40b001031b03000341139152440c0c040c00c51101d8a03022009942081d8040054511680c03040154903840c0d1745203c40450807505201c00004902c5003042d041e0345550f0003188010702405034000001743c0c3c80b610310083d40b5002004291188a4002d6410880d42110030030010794090000e034103561400340442d41d0000031800550702090319038000d0f0340601981d9000109159500042d151050181d000e44405590b0107400104901c000c0740c14a0000310240014030150611064400c000303408030301910b20b00b0040740c50701401203e001100803000c8510404100d0a03580c00300d4030300c10083d9500028400444190f0b6005a640030b24010036040540cbc610b144c0e41402801c0150018085d0041c0200c1000e08290071325421302c20105010a45400e00740340410b002d00c0051107000d04a50b19254200d89902da540c2045000e403000c80c102351401d41d000d021400150b540d10070090b00030b8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 285707760 1250 285706510 285706537
    0x3030409050c04031703011508130b070306060e0a0b04171e06060a090c0c0209060112020f03060301060506040303090302010318082d0703080f040f0b0901020711040204290c03 77
    0xb6451840d007014505c550700c81c140e800000c00e000400504488400440c8580034504044440350355804aa45240350075501c0504065101e105100c1d80301c0e0181c1c040300943d0480d54400d11282c05c031209020f113a00f8148140b032548241004200140d5a080c2603405025000d981901d0810904100303100800c55501c0902c80550000300901c00d0b01c0c030f04298401c00408074000c0034010222440e00240401c0e10402e0060700030410200081c1940c2c0c85a0301000c00141d0803213045481e21010300c11240b46402c00c0354003078080c1d0b190420104083c40d1281c1664101c0c0d6040d40d910300c510b030455004401611004151000c003090251105000030120300c003070501000c10790104182d01304004c103140e00b2118000401c5074001020004100413a50080405601c100c640c6840361454845152000344070b01304d074402501c148444401e120040710306400038483d05019404ca600d81d101035400b048100c0c0f00d01c0c030031120f03c1c0514089980808401c5944066083c0341c40d00002d003440800804181560300c001c0600a01 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 285709010 1250 285707760 285707767
    0xa020a140a0905030115050d1101020c060a020705090601170c0a030b130b0102010c09290c0303010e0f1f14010c061a192907240507110601120203030409050c 69
    0x68102441041101b0790840c124600051400c0d000c110300e0402030f4409041ca0509203005041a402006400708090313020b0122035440380441c0300251a42c441c0c0c05510710401c41fa4010078520740c402e0b070050f0403607003c001542c895034445404500d4158807000c41e90382410703100c101d084a41c0d941d580103070041c2c902203500400d42d046148002401c66040403040c609101c0c111400384614002c00790040903241c503d9404907803804103041f4400030390241c2c3c006038000c0d2000100109041c00f00e18000c43c01440e080300382c00342903168007180541c0d480740e04025020400c0080c100f0840d1144501081c0f50b40384060501c0e5645420f0380d141d81040d1a5150034001c2c40804014050740d4909040c800161142601d540e040c1ca80c038107088030088040403206644c0803041229004d075200017070307a8003155689035000f80002c90052040301c03c1c9180192030703080386500b2454940003c1e0110300840c2201e0720b0080c900c001c0d05a80c0e003418a000320408501034103981620080c00041034414440c403600740a40b5001001ca5107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 285710260 1250 285709010 285709019
    0xf04060605030a03080703050f010308091003090618140a05210c01050103030206060a060309080f09190e01030201110f0a0212010608010509070f05010215010509060d060f14070c0b0a020a140a09 85
    0x25958041d007084504031414004101048a84064a0dc0070b10b08640b1001c0441d81039a00710081e08003400050300e0309140103100d050992031291442022071081e03010030410610008402e403a49250302c1c000c0c140750020107100040700301c002100c0e8602210807291301e040403510b01004e030031220240c00c110096030101c002d01c50a442e00e00c03103180c01429189070170700060313042c2e0303a032600980101000600c0c50400801c000c100750b900c04000050b51120131444801856580241702c1d000e017028801680451202030301c1d409225400b149000d000b031034680041070441416402c0c003200ca00c81c48444031080d5a11040803542920070f000d030a0040c000741000380181424000f040250031101c2e0300ca03d042d50b014400c40a200180d40402d18111070044559008550720344000c920b10034400c03000280203a203000d00ca11440903240c1d10041400ca09108582061740c2c0748541900d1228101001400484003200080c500042c10780042110307084525200c1c801ca0181402507800f500410024008103c2d518000d02 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 285711510 1250 285710260 285710267
    0x4050a1b08040b132a12080702040b0f0319020f0607030e0a240e240715052208040504060e2a03011403120a052503080f04060605030a030807 62
    0x140c0081c43c00049544c8011a0703642d0a01d080c2066040074a5a450790700381501101044c2d50342801003030a01c80c980030032440da18208960354000341d0124072507031401020041c0380c00c003200c54030701d1000090020305ca44040d522582400b1868004101e81c011844810012991105405071445034407030f855000840044004000b4482036640001700c1d204c41c0422496020100320b05030301d13030f0140181000700d005240d800101d0850724400030000102480e0540c0d41480c80e5111006201c83d80c0030301c03410300c0401066054602512000d40d002a501c0302d410007101e41e005004680c220340c00b0302c44d4135507514250381d43d400302d01942c500b9440900c00044410800440403070b010601c07003441140c40c000815a00c03124010140c00d00040c003c091001a01200d1840c4940302000300e181c031072810a00141d242d00f904200148142e02001005800000034203440020910110400742482d50540301c101059940e082c0f20090050010400e4032455250070b0001560340341400050390703c80c00fa41c0c4100301c074902a507025 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 285712760 1250 285711510 285711533
    0x20f07140d15110c010b1807140423040e070f0618050306090606120c210a150605030c01030608151b0a03020d0e0609060103081b01020c01020c120a05070204050a1b0804 74
    0x7d0140d00604400c80d00c4107a1587c42c10b900c8803d90408289030506190f840150b03004581201195010261042c000c803a01c9440510000c3c60448082c80f296003011200c42e00d0794030340e01c1003400c00c002c00301e01480038074007031042c1c0d80e044600021041412507a4000081c41d28005684401860304140e0900003141025201c3c80300f0503500d54020001c1d00e1000001c68006884810141503844001d0780c00b40e44a941800400c19140d04004c510201258076001500204014450b03148248500303d604807555000b40140360840c1e40f05005000351070411091414900002024850b400001404110b0003082c0c1c070b00604000800c40c1c1c3d00586900c9a42d10313001c102c1d400554496a44da002104002070000c001a4883c1900d40c8031510588424420001403148001c02c54038850550000c0345000380c500781580540f120072001da040712268183c860b60710301c4521031003811000040d4204001c50260803c0e800c8070350001d010520019445980320b4034000d004142c10a8040010031035400e201c01d01c2180003c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 285714010 1250 285712760 285712781
    0x90c030501060903050c0607060f0c080f01050312040b0306010306030b040b07140408100f020d110904110903030703140d02220503010513031b1a010303020f07140d15110c01 76
    0x114600f40c00e40c0c0358a80c0e02c011414010f03100c0c010000309541045131941000d032405030324a00038041c0008101000d040940c0846a030304500c1c5640d00000344074640000d90104800021401c07a02d010f080a50f8500103620007800c1d40d050580712a00040062045c240b00340c03149009441012040c202210024844000c4003019114903500344814448003c001c280c5884005052500088408010084001034007490006401580c42d01c54024040c1c988c0d54000c25508404480030400c02420802100d01c5000d4454000d4055006100e0b56000901a0080c6460b00e990f8240c414244211035041c04140d0b0b02c41c079182c9c4003801050440c95070b0851062941c401410084009001c90324047c10309000c41c0400f1a0058104005100e0039880d400002140f03034001500403210032003003a01d80c03441401c000401e00c4100c4c01403290300e081c092030000200e030031410703a20114000403401a000d001c02803040701706001604c034a036401ca00c039015151103124941e44103503c0707003001c0d40340c0e90203060050031a5460b003403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 285715260 1250 285714010 285714017
    0xf060a15030308060d0c091b020c0a120b04050f0715030b0f130216060204060c030219050604020103020f0c0d020f0f060f010b1c020a020a0b0c0c060406020c01020702030304090c03050106 82
    0xc0c070019030070159a9a00c11401d4036030f04041079460030a481c1806041d401811018548910281042d440c21254001c12086400300c0f002c00600701c060250250307540c400d44d0b0024240444450000da9507412994001e8000e908443c01c020b0340158a9040840301d07440082c240c4505010850b45a42500601c1314200341164a609802d0040003c200024200204100501e50020715501d10b6401e0181c0a0552034000030308540362601d804001e010501068415805841400c01103403030382c13415110140c0556031250107420780d40c490703a0040d0082e40009804000c40c0e442072040b464000d07020003c494000199500600d00a440e00c05554145040c1d0b882c1108160003000400107003500768801e4504640b500d50400d43e0303c40919140c210300504003010003050758000500f082c000750b4002002020103010b00c2d00f001041e21049a4031409114010450009800000018005c0707071080e07002e030081c4884800058a82030b500d600080c15a441504000d290a98400e40c02c80c090b42e05101d800e000d404a401c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 285716510 1250 285715260 285715301
    0x3050103120809071401020114040c031b03080403030305060103020c0613030f051303121b0c0f05010503070c060c0905030a140714011704020a120605090c09060d0311030c0f060a 78
    0x1000310b0315510f131030003280c1002c8900c400400c4164400d502040c140c40700c08024018900742480d10001c02c41d0750384130a4942b4601d940031401410012413410301201c0d4842e15203490540345960076009041d008181c241856424440d1003241a41448910b02c503141c00c480c0a60038911034074000d80004c0100a03c602080014000080310320750052034a001c1c1c9420010b1110001c4404008680c0c000c60321940419540314038800000300072130f0003860310aa60075440c6113580c450301c40004680703d0200300c03214070028812207035150200d02251701080b5065601e107806500e146c0c482011a10300345e06000d00b22a800260322884180700e0040c880c600c00f6010302c118256400c5181d0000038801e091002d4801d03805c0341400003103811541d0340340301d0340010441001e00101141860030a5401408200c4007110680260046041c141c40c0414169224800090000ca460900e03600c040311940c803040d542040c3da110801c040d540345141081101c994040e04401403a0a14003c001203040d1804400c0c00e070020082013 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 285717760 1250 285716510 285716521
    0x4030b090a02152b090c0b0417030a090302090a0e0616020601080d080f07031e0f0b030106050108011e03050a0b060a0b091e01030902042909040210030903050f0a030501031208 77
    0x44070807100095418440b40d0204030302c1d13924a004114941c0c00030b01040740303803000092600000b40940201c91f4111a00e0303242d40384200c2241e88902c030301c0644070002042a80240018079101d005036130440e061002c0055486481c80c84245010f130151002c20740c00000312030541082d41c2c10401e560140c0245805090703900f00000b00a000d102000c0c14140c182100c1a0015020350b12940c000280c204004083c15407440e1200000303c010a00a0302001d4454100500102d041c02c0501a0308220791040c0d40e0110507038030b05140c180ca000d524030391a14801d82041d038000040b41c410885500041d025101c240343d9410711400708040301203942d101382d5400000b4420891300b65140110011030040078020044684c0c0d41d01c0c0101c00030070003a030000b54400d103804e4500b444101c00200e10381d01240011200c070459621881003001d40703030b02150b0003580122640d0710f959490b4400d811058005203e410681d06024860f20910380580023100c122000a6503000100309201281c0c2c4400720300003171420541749a0425 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 285719010 1250 285717760 285717787
    0x2011e0b120f070b0a0507060903050301030201120b09070513030614010f080604050a030518030a060c230d02070609021e03012a03110d090803060f151e04030b090a0215 74
    0x8074428440e0344c2c18040b594081e054007a504483c16198403240030004005180350181454000f030101381c0c00107803420f400f01014450f5120302008180300601e81c52281d40c8500c0100c0301c0f075004c0c650410490a102d0000000560f160040d1400d9009010f0402304642c108030252a15180907030002c0e103194048024400420750210f00305000941514003d80c3d1030307000e80c3c4c0300564007251017106605489880340c10300901000307503c852941c0703503955100701c403207004110703030b44443c0d81924a43c0303a0100f002c10801e000304020f030740103015444c031031400030858100c41d40002c0c600d54000841701c02034035201800307810300345002c0c85003002c601c10f10030400300c101824030744005038040c1028100088c10350b65218104a07880c030109591030180000018050f2405500e003540c2030b60030a9482501600340020740c41d4803894a00160f102c0e44100c01a0f103414100e502c0c003070444000c41c01d0444c9101e80020400400840c02c18186244a03042000c020007252040303105010741c01021004034600002e0a00110b90369403407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 285720260 1250 285719010 285719023
    0x20105041701020f0307020d08060108100909050c09130506070503010e01150309060f0906140714160f0b010602100e0615120d0f020d03060b12040302011e0b120f 71
    0x100d000d8107000c003070101c41068028860030940b50b044810220422440076800501c008c201d0045641c1c0800580b00c40f0300640740c4140680e2640c442030342d94013080c02214519440f10800602440c02c69525000d0f503c0450700c0d4103025140182042003511814044c04002c2020903005034080c40d001d4655850080420000603060040c549034211750022280258401d4001c048403d0700414100a10301c0c0000884d0000c09000000310f40503424a15401f0030b8170b401c01e4100d445500152101000c5000441c030000040c2c1c01140c005e500d80300c3d41c02c0030390049121131049030390b694482d07824552194184003001e8505490ba114001e421420032044130044080410030b15003241b24240c0710b101603c1c0020000c0c03040044c4d0700c04501745200751412840d5080e030095480b8407600c0d0640a9a18010040c80c0071015102240100710011030100400c2102c0180e21050325841406071000040708007001c4000100c01100740c118544460f210446042c081c50441c5e1026509154000100f0103445e00303075100b0380c5485c2c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 285721510 1250 285720260 285720269
    0x1b071d0f061e1306050a14090403030c02150907061101020a020a021207030f080702040507081e06010e031614010c050616031107080d110a020c0d02031f0603110d02010504 75
    0x4260664550300580030882d058802000f00a58100c0c0c070200b6802030041d803141921400c1c1c102e1000440034020240d000e2207081c0607060890715926074409601620101c040c24085104029160714860010203696000b854010040c1c00404e1130301c000140240010a2207420a034810400c082480c4d17000200e4210080d07068a1200e1402440071025084c80810362001e09441c80c00040c40c420400c030074005000c9103100f140c2c00c000c0f03a00ea092040390f00714411150350f4a018005500000170880b105401940301e481450100c9840b0900030110b4141104800c3c0c41070b83c001685000d011000042c3c803041c000000030302c0c0041c0702c07944603240d06960700c03000340c4146034240001c1460b200607880fa401c54503c00c5600b1000c42e684281c03c0c40c100b6031581c030130000f2401e560f03d441c8803000c90484c201c00b21006001940e008060014030002004044103600d07200b240d040c4140d11402c00380154050350500c003481c035020009144d5140d42070030940e0110040100388110402d080030380042c1c1c1c100b02650700f50ba = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 285722760 1250 285721510 285721519
    0x90f060922061d0706020304090e070e010b0f09041109091605040605090409050307030207031704030803180a020406090618061d0907050901030605072d03111b071d0f06 74
    0x28406a0212800902c504aa0303456029513500820419000001403013141e01c0600c2c01c01c05200342003034607903e03846140509841940300c41d00400c801500ea40141020f8161712454920788041d15000600310303440c040c5444c504a8001c28a0001460a003081075480703403010022401c581d01514006182d4420790244109100002c0b42040306921150301244000b60320134112543d59080d414081c7d40c0703001501c812180320301c0c1c504020300645e45900949040b41e40c4040c0407420354581c0f4800039903004480b092400c0c60721070b500242000d641d4500460b001015844000a030035800e080c41a141035408400110403e4180103080000b241c1c1aa0246071482250b9140c072400e03141c260009052500075402103500c001c00c48004800d005070b591045005000d140c07601001c8070820000980f43d2540f0101c1c045480c14141c0c0420300040c0250131545004001100481c0361028102302181c1c01410300d07884180c44d9200c2c0c0030500034481c001480300d81c10032005045440cac514051900c210000b10007405076019 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 285724010 1250 285722760 285722771
    0xa1d09071b0f0507080a0c08030c07090b010c0204060e1602010b030a0209130b0a0203151906030203070c05061e062d0a320105070c0905060d02090f06092206 69
    0x10301c40d10034009104543d121003540c002d0b035601c401d0280d071400e85400540710b07007219890000300d542d0008102d80300a610400600815460301c44a90014000f02c5485d6051020f0490340d040140e0305e62107032074040d0a80c0341c140303030701070502c0442d50308581380e444202400d40e85003140e01c085958000a9007a2003d43c11140b941081d56060b10008411b0b40d1960000c01000740a014005201c040b40c0145110322040b403940d84552074100200302c61a10b41501d4542900c03075080043c01150b200340c00560f4000024200b9180e01002e42c1e80f1186401003c460381001c0700189804024004442e900f1070b03030000300c21030340442e12100c0b500100b0382054446a440344106403080241070309032200c241003c000c160419401c200603540d69402505c400240c21044100d942007481d0241b42d42c003c4060381c40035500302d04881c03d15824044100020b00000c2c008030b46c4481c0803c480001661600780c1a8860342c0341907a101c846041000602007035100240680b02c000340c1180340c5c00755070b0602501c010041074002402040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 285725260 1250 285724010 285724013
    0x3090b04050603010306201602010e0904020108241009030203070509161b0818031507050a080a1503080706060f060509061b010e031c0203091c020709020a1d09071b 72
    0xc800c03100800400890703401290f08c24000d0110701c002d1244c14002c3c0c80d0021100035031020089904421240240031850000203e082d00c140d00702052200c1c0032640110201d011141c00240300041d040c0e000340001000ca10092085007400c1c002d0030300800301628140740604000346d840b11204550304454080080e1605600d4920701108020402d0b940c02409455503040c40f03014038180c01c00840b0231240284204800b00c0403462080c1c2a080c803980c3d1540e81d03542800030701c0720101c4591102402961041d03842e1204a0034030030017114074000440c4622405961070540f0316295060f54065440700c03001c484030340d03401c020b25a00001200c81c4044104d038029074418a8865030b0000d0031265004041030741ca804010005210004018044031114541090000a40020141c2644001c0b105c1804030b8008400c81c680101c000045151500014019204110340b00c02c8058100c0e004041e44c200002d00c402c1c41010172105142c020000b90742c090341c000c511413428480c09018044080250508813400800303110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 285726510 1250 285725260 285725291
    0x302130609050c030a0b01020a080a0f2c01140a0903032a23010b1e0607120c03030b101709030c01050103290906061e0402070f03090b04050603010306 66
    0x1405002008100314280a1040041030b0030880d1000c00c00c51400f00c8040187d0700014011100b2035006001501d07020b0282402c0744c01400b02c2c0d0301081800b000741500d8189811f644503012400d900207500210080700741e030004001007010b140c03001300b101e4100700c00d001240d0301c480c00f00180c80d0542403100400400500d14159102001544000c0240b109609003c00110156012446007148200d45405568140c402d00301c40c0801647c40d4003818000344800302404001c55480443c03401082c05040c0301440c3c84d54840c10411403100300004828003504010036030903124401801c0c200343c0c1c40f041140d01154029007000502d40521144035000c0b4001100c100d400c00c116452340320900000c0c0220b50392480c1c4115182c0a003420600c420058110340c0b1030500c503200f0800e12581c2a2001040141c5696082c0445600d110784803039007018031806405881d07100c1e400240f001e1441980030800d040b116041c0105800d04542203140e45c104208420007031955007a0030b0343d065a4200c81d00045509017651001e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 285727760 1250 285726510 285726521
    0x201140103260403060e162304050702150a06060807030e060a09020301060b0a05041d06031009030309120f1d100302250305071703060d0f0201020a080c0f070803030c04030213 77
    0x74170042c2011070303400041e02c0c00305070303c240c19800046d00c0400b176482e0a002000c0b852801c604a4003440c502c0240c10142c42c1c40d42066400400e00d00582d50003c203030344248004408100c80c0000000d4443c80c0170840a03521401d5558400300900d001c206c515000c2c041151a00005004080000c1e1540010f1056650030350001d00200040d058082d0b0701c1204a0000d8101e130483d08c200d44c00b040b1000340701a060303045084064400d0030000c000e000920386a00d61074000300b109180680402d6039071b803500c82c001131120041d801062440c0d2174030000792884100045c0321074110f00d403080002e00c40c80c03503829a50b16010110f1454602c14240540ca407824070702000c0130b2540b1107640d5030901140008040c18581c0090040c006a80035982c8800d40320300107408032041740300540302c41e07400c2002a440c100200c2c03141d407410351b81c42d403051064038481031242d12590a40e03005a0700840058200305040402c100040180074001c0c0081e0740554103510f418140416580a01c2c84040e000b04081c0340c0d03032840d0b00540da008 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 285729010 1250 285727760 285727763
    0x303010312031406120c100f1b0c0612021c0516030614010c06022a10050f07080a022a0709050103051e0f0a050a020909210f0c0604050105070201140103260403 70
    0x12021f11103042c000c0100401c00a11000c00402c0001c500180e210300003c0102a0040c5c000740103941a07843d01c001201c800106c19020b01545030300b44a80040410905c01c10811540d0001002c9518102481c2c00c0400b120840b0f0780d10281441d04c1c1d0100410580c0c0314103030400500c00d08284000700c420381488400b07442001c5201888803140c2b8002c01490410200308241d19169104840f0001110308025040b43e2042c0c4001c141c100082c00041d540d50712a188003a40310484501c050704060000d5502840b00d0420f500208850744100010040d020040040c10008c2c217010f0000d00440d45103032250740e22440020b01480c0b2086a07214841c100500030040034001c01c65041c1141c000c9a603600b4a1034407080300d0700d0200d1141509a0100c0c586180004007020503801c000600101c03004e104845020310f03030018000303001d440018800388990003c14042a8070546c0202c0c004542c901c2c044000a085412000443d0116401c100040c00454951004040000210000960b8505061352200c1071800760394030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 285730260 1250 285729010 285729019
    0x30711031201080d0c08090f2b0605090c061801180303051e030105011b060e01090311070509270a12050a08060616021e0904050303010312031406120c 66
    0x2494100c40301e91124050403640c005013928030940f03090400b1110006070a50203000c00409001d185507030301e80800e03508890080180580804c900030000300030b1500e843e46650110404001c207030f00610105018103507114103000c016100c00244880001d01c94000c5020141e02d00b09540b4400b1601d9014100c614452000c3d480c1507210b0039542c2c58010074691001003e10304889040421046500c5071300c09a0f8103a42058652103140400d00980e4645d83d00c00342e0081c1d80154030340980004020080c802c400e03401b400f0f55108450080264092807800032158002030051944a0030811800c0c200310315203001c0446101e0202c40740355a0002649055642800640400f00103450b800040e0707003003002070003004e0340da0319000d205984103c104440383c024062803c0080c036a5041500c0185003840d1100310a40e00d5246005a50030801c01051400c0700413142114203500010052043c03011940214418020074039061101001d5129210782c0782c02c014040038080d2600d0001d031034000d43c0611500040350b43c05007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 285731510 1250 285730260 285730267
    0x6030b15071a0c180a141003090b07020a05070509010302031e01060506301b0c10050106030204060813020604140d02030114071107030b07050c12041401032f03071103 73
    0xd600c5181350710104034241c420b02500d10842c0315080c510210001c442c01c10001e036403401c2e8410288001100200408010540d40705044030005180c600700a024120950003850900168a0031610b00f00c0c1b1600003604c503150f881c00401c01650b00060780709002140c02e140d140c0f0091010301e13107409400300390070650f8030040200c1c0080703010044c40f52a120784006c0c403024584007151104640404002520b00f01c0782101c3c5040e22250010f0b1842c014450001d00c030088130300c841107410200c800c07206e0a07040000002c1d000102001242d90020131a038101500c0c3e2031b07078480d81d0b04503030000d15284114403074198030003525003460186540319684600c5440e006802400401c512104034400c00800702c0d200710105200940000c42502d002031001c0a681d80b00a06000603129a0415038142e0828100d00c0ca540c86104c020b8400d8541e0100500010721480100c00301c42c2e504000094207a5012506584207000c0c405001c03001c51140e90981c2103c1103201c1c48681d0b480d00c42c95810ac4010001400031401d0b0310000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 285732760 1250 285731510 285731521
    0x1180b1c05280504030c290f010503060717011404140a0902030f0109051b03071203080a0b060a021c0302090a0305030c0f03070b010608250305090706030b15071a 71
    0x40ba00410642c1014001d9164111080c1c0100c901c1920701400144918541030009404140120500076070460100c555241c2c0c0e40c4900d6011000320380c41c40304418000c00401042c142008481d40101e014180b104400040d82c80ea190511014440c5041c0c001e4600700c000c500e601c80d0f91220000c400304017041249880d000d480030703018000f044c0d0224000d100d02c2c00500c401e002c06215581682d64400040d102c1c1c4850381c101001c0d100028521160f142c014240c001890710001a072510241d4072030346901070140762414014046481e25290300b80a40c508202d0040d40c554086800d0540164041d5150480c811a803011070080c007810225a0f00100e4680002c0144007001000d41164041c40c401c950038105006282c64490140c400001c000050b1034005001346400303410343c1d03540003012200805240510408106100980100ca840441e5440e003d212607054248049000ba1901d42014086100355030301152012240401c11003802d000812a10200322000468803005554400c10620320f003040c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 285734010 1250 285732760 285732781
    0x40c05090d0f0c0e13051c02030a0309080408060103030807080a140c03041b0902121003110904080c01050703090201031401080601090e010e07030821040807080307020a020307080c030c01180b1c05 86
    0x40170300b52040e208260450004100c00e182000d148072280d030185051038000380b4141c024091442044840b103400340700103d001a4108241d5001314003d603038000315828004405848000090003c90005050816000d156030100340802d0f040f00500b0003682d0f0342d40e00c0382030007540c07000740001c3d50484194a01001854200540140402c0145243c008400d0707202c2c03050a82c005102440010402400b81168030a41e00c0d01c040ca4a82c4280280500e0707203003121036250340b030854204075006c00c003083c5d480741401e043d0b5034544907008840152907021a40d82d41050f001c190ba40b241482030001d95611500350345070120003074220f000d01c000c1100458200030341760310f407040c00e540100076104920421007510701603005000c45200e0040d6000f8040b113282810703a4942640340d5000070140e4095205c2c011081d40147c60800400c030050500078003400298501004140c244000c07403501d5030400901814030300c81d000c9800444130890340c0b080382042d50340790444e80a4801c8450200c1400c400d610303000820024000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 285735260 1250 285734010 285734041
    0x301060c142b03020408060c160516180203040201120c020a0b010b0406080601020a210509060c0709050a0c02100c021c020304210308040204050c0c0a0c05040c05090d0f0c0e 76
    0x3a194424182d0300d01c81c03208400300d010714482c2c0601940100301007054580710f000102145440f501000c01c0308101a1901d80c40c2c0030041d00400c002006048003000100c41c1c01c907058a604071000b5007503140d030610390002094504804014000c6c26034030010750a106000308030842140d503100d075002d10b1660b981c03c6000c5c038075001481104042040030300000d01030361010034400805548034644401a094030281000d483d0a08110303541400b004100b40c4180d0398802001d0488003424034014800b803410005800261880500901917642c11f207a0b0700318030180c0204541c080b4503401c800c00110344001c290100c3c81c003540c607102c2c284001c00c542c1100c400543d004c030082040e9403503000c031690180e015070380e0141c01c0060400040c5c0000c11032404240185020b803c843d80190007a54524100001c00b20720604041a002c4116812180c0c031408010078141400b41c0c488284031400e01a08043c110b001190148105c0a402040202844281002c0000401c0c2080142840c401001c0c818582454140001c24 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 285736510 1250 285735260 285735313
    0x501050603060718152a020f03011802090a02040b0c0a030e0102030a090608090a12020106060806091b0c030708030711150106020709090c0308030c0307080a050405030301060c14 78
    0x242d100041c40c118041d00d6041c1690002000003a80a0714000b0700080c0410001020801c00404030400c031880c1c164030042c03001980203400d0488000800f4410440070250340f680f554003e0b418401640c0c80707070070404030f0b400e200f40d010b44480e0000e41d00c00c440c00000380301d285c0003580c1600340462a0401441c001401c0b9034181d10035100c5030301c0701d203948005aa803800345030080c2c0000388800d074003403182c18860f0300e14982101c291412a0711302d9250390b4031041e161903080d80040060303540e00d00c1040500c0d40401801c3d04030b0f05c1900c0c504864182040441070703010301040400c044c0f88000400b009104420400c4520f060f03000302d0320a0712406c081c6c030014848000a0850700241c414034441c400f000340b841c51218100c4001e90024102185000140806082c442c001610000c0440000001154801c4020b52242110250b038031b96a1078601405002c4400281c2444a124505030412000580003c01c0f41e040d1061424900b400c1101031900c12480d0700b0100304982c0c503000d8950301040301115065111010b0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 285737760 1250 285736510 285736513
    0x4060209030f03190c0201210c0e0604080709020c07030819030f02030f151903061506020f1203040c05120a0b0c0732070e09010f06151103160501050603 67
    0x10281030080640e603000b44000c031040c1c9107030f603102040d103140244642400380d4418100309504e980004c100c01003040c1014900b59599880f0b8511110164ac0b185650581c90741c01c4980d64101410032408a541e15180d010303224159134002080d9027031a80410001c4011580100d80c0390740c2d44a10704010803215468401e02d40844e080a0310f070305600c1c1d1280240e138800c07030001f900086242d03941d0280c0c00c0c2c0142c54081d502d030000b240040f1041c20b5000281518085c2d8041c02010139084d42d0200c0c42c25565001e07610205c00c640040310017155101d00817403407a22010112030041e4407911103003003c001d03550003540221352003010795507000100340010844264071401268030005641e10002034050a00c80c80303000920810030440e18003a5086240040c411100f0000141940c1c3c0c00d445003c01c0c604089500050003a000c040301b007088500d400d004031009198549401d0106915000c0e00007980c0710803d2100003442030008450107503007000c00139200b02128040700c0824488142c10300c9030013850140d072a02d000307 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 285739010 1250 285737760 285737773
    0x4090203041103121201060c02010e0907030e191703090303041b09020a080702012a120209040e1f020f030f06010309171e0a050702060a230d0e0d080a09020a0305060406020903 77
    0x1220702520044239166010b03100c80301041021400c010302a030b0b00400c5602032603540c0b0300780c900e09081044007000d50b506816107040141d0b80380c20030081075070359890900c501f21010010003080c500b01006481e0020b40c8080e00350802e6100d03918071075600c0c040343c1107840050b1000c24650780715540950f0f0a030007424660000c100708004580c6421205204080c0c24034508802c1940664982c0320300c00d5609140481000181030000c0540002d041d02c41c0c4010081c0154090f600c9203040032940d40c07000c3c01d00c60300400114684142107980903542c0c00020600c1f000d12200320001503640e4002d82003500c0c11a445480c81e40c0101821044118640103142104003100260304000c8003241d072041202e100300060340341c1d54100b45003503080100561004146608122240b034001e0742c03c5102c402c0c080030710f2180441050302d80001c1c240310b400300c0c2c03480342440e5410f030b002d07201030301c0380c181c1094009400501d9a0808a801080c80c000b04107211202d80c0700421a01c600c00405c024801c556024000c1271340200c041d11007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 285740260 1250 285739010 285739019
    0x1b1e09040c0920180d0206040e010303080c16020d11030a060204060f091208030402060d020c060a0e010c0c030f0212030f04030215010f090b0406030807030c0b060a030804090203041103121201 84
    0x2c0d454400c0c1c0500d5070a0104114445840011a0311302c050700300300401c1d01203001c0c080d85c0422135607081070744100d0340e00041400500c205034105a030180c4c0000302c8804030381403050300c1c80080959214000d000e0b00409002d01c900c0140901140c201c03601e02070107811903110200303a01d040c0000394070034402c000020f41040140c0844501c100030807000c4402d003031403004220402e5100c06207281c0c0041c200b20f030300400c100200c1248001030300140100940d424083c01c154a894175500d400c0c2e03014800c090f00341ea4502203040c20240d030071500744402141c042c039140d00704201b43d8500b80d150084506a0f1000041d011082000c0244400d44c1a407003984283e00340c4280302c9140d03461f0000c04e0400c0c061001c4d800c003c00702c01d020340d101036808025040f90042020800d95a00c3d1500c406951051600740c0006820700708110078021a40b200c281c010b0016529084040d1a5469010b868015801078100302c0d500000400c2c140200c0481c21901448010142c0c1c0740700e107690b85080d001d035000b50541d000d0540d50800028 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 285741510 1250 285740260 285740291
    0x30a0f2717070b0103060506040204170102040510080405150c0c030c1b0105030f130602130311092401030e010204031a1906060e060c0106091514031b1e09040c09 71
    0x1d80302e5503ca8840b078030341d0f425a40c0d4800500002484642c0150f424030002074001c11070362041c4280f01c1e40c0f4000603510360526050002d001d03000803d0301c007800f0080050000049001071121032080700f49035420925200c0303500703e03050351190898200d114032011480c0402402c01041c1103804050744d404010080000c0c400641d0240400caa00d4201d25501c0b80001760401c0b82c0103010764055204060040c03401204508070b001c100c8035078006860340101c9901400c42030528944003900841e0001c2c0c000d40846480750210480080c3c144098105074030340e03003071608040c000d4050354040c41c0e22512070b040030104071440303094854040f148060940c0070645030100440381d07485200103941c82e0f0b0346c0d1102c0b0f0b0000041400310741e9101608079000b82d035940d9000038000101d03108886511100c0b00111303010a1611041c0100c02046070300c1d00d8880d0300404600e80030b442c85485001900721068601c5d80e00300705400401c0c41c3c009900340440d40c0240071401000b04204600200c00705a40ca01e85c3c0c01c00c00f2640d5040c41c1c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 285742760 1250 285741510 285741517
    0xb04061d06040e031e0409060b090108090c0a23090705070b0f131113060905060a080102031e04080c010501030506040b090d12110c070305010f06050312030a0f2717 72
    0x580c41604204805c0c0c2d92400501c03142e05241602c984030901d4142e5516903041100e20315402104c13060804100e00480b580d0003c0c049800c494034a0050240702e0010000500c0c46c0003610585500031840840c820301c2000c10200000c03000c1d0000c0c103080452400140161150340310038070484190304801c0000e41d8061141c00c000380581a134094049140f211540c40240c641e805242d8030358001c8480820b0166550140a00000b41c54090000309040c1003d805008158402d41c1241090740d00500030405100800003940303510643c8555005065107440c24524400d00c1208a5001103500f081d001009120002904a0249108108034110b5030b40d008411502d0382030680000001400c40016103804004e260801c45406543d48804c03880c0415416045140840030303401142e19035106c2844d0316008840d8400e150040c041600600f4500702c3c0540c0c920f030140b0005000311a0301c0e50b50b6107441500605940704071082024200b100d980c0503001c48640351200610501100e8401080602d10807448060055 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 285744010 1250 285742760 285742781
    0x3020706201006092414040b04020c161a090603040201110d0c2f0f0f100c060f0c091205030d050c03060a0801022a0f070b0c0f0c13020703030b04061d0604 68
    0x20320340c150406c940004022942e0504a6110341c99010b1708040e90744510041035110462002050f0002c804008202e507101554010b070030302ca00740401082000280c00850399031020454029075a41e850348016142d100903000e020b1824843c1da1280c451054200486a41c0c090246a1038400d2803c5128031200308040010b14185014100551405a0038a40d10100f604400245010070a00020002c5104101080107510000c0c805651203818003929200d1f00246492200d418020a1020100074007260007911810100121004805081c0b24091095800c2c0300421a01030090781000c50141080c0e40094500c0d07441035009680c0047c5000f1305108840d0950b440200c02500ca100d003142048800303510702c1d801b00c1940121181d0390384410061210001400c15062142c4d01da829214505140c4840004940119482001d4249241e614464248016481c00e400561b990345140740031070107407000480c2c0035001030401071b02049440c1008100846110a40342c0c110450769868100f00035109034518 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 285745260 1250 285744010 285744071
    0x32006070f060903031b02070603050903040602060711070e0c09041401030519060204150302070c090c20011b020d030b01032c0a17120c070302070620100609 69
    0x2070315400216036420410300180603060025548000c07510402c041154541c0603001600b15100c01e11043e40c242c8100b0fa08158018001c50502d414140c0203955408003a102806101403038548a0101004011340000b1340803a5440300c91038241070f0600c0400c2d070020007500d485075080017049051424007a00c0d1a040326000001040441c0072043c040465191110050f1440750b000c00c00030a01040b6494007401070341c20755074010b0380c604d002c0c100341e004169107070070400180b4146540c02c2c40007a40031840d82c00030000800c0b072200c2603028880c3c182c01800c0300c0c41007940b0781c2c03401c8031a020142d03004200070310743d462151000c0c805008030a00460859030641c02100c01d42c00d40d880b0003883c0c074000c400200001d407144411200d080d51030342c0364540030f010503203281c0d0890032000500e1000c60395800310a640000c3c5e4039009504044544d60b003c0e465103c2c03401510b0401c850010321022076104164013017101070580050350582c0990b4801480901060301401c0c00d09400c20710320340c1150310802c40c40e1104070841071 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 285746510 1250 285745260 285745283
    0xb0f010510021c0504170601030c0b0a0c0204050c0d09030f031a06180a051507050d090b3117070602030304030f03050403020304090509030909010e09100e031303200607 74
    0x815951940400c00c250410010184000706d4480b21404161000b02e42c941c0c0184240d41c91840c3c001050142c0d900600541d00003480b4401e00c29030081c2d5085107859048030041000d0b620802040305500a0f40e01800c492420b24000c00141600660710074034074412680d0a002144540c41c04030b1508010142490300200100904c0b10905c9103002020440c02008000c00005599a400110309a00400c1140080c0200260784400c004c820004040d1100c92418180000b611348141e0801e05d0240500d401801e06041501000c0c02c40781c0d080d072030fa02210050b081214180c4815484100101540c840c0c4014800e80d500410300301e000109803881140e00d640d410f90100c141e02811000380c08068801c4080d07100501000c5003010395401498841e1003090300031740d180c1c03812408001c0c01c1607044c1c0c8800d44401091003888060360000c01c038003034003c21042c1c0c045501030701c940201e4694824548004022424240c0100c01c100204005a05a04d403021194030003141410400501c2d10035070200801d0603804a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 285747760 1250 285746510 285746533
    0xf07030807080c070b30010e0615030901020904050a060e010510140a05070203060604092001020f0d020328020d0e0d0c0b0307090b09060307050919030b0f01051002 72
    0x280c000c20185100b07481d41414103c41900444c60300100d81c00501420202040801c00020801c00091a1510f1051030000b9104c01c449001d45080040c041e090100488900041d142c1d00d6024010042c0c00d6034045082d560700c2c00758001070007900040e6240d0700c141e017000e0104011914038000e440580c1c04405016080e6488c181c100182e4025502050040c0224600e1180e0040250409005c140541da11095611a1070788101410031780c0080030644250708d0581a0b0300425086c4074450003041c0c00c0c18000802e02100d0005034540221801c0440c190321900404403801ca9011015051104605c042e442c601c01203000034500c00c1d1781c100041c20060303000c0c0381d010341703a14801c0700c0040280f01c01070003408105841d5100c02a14800076005200160000018460040c0e403109081e802005400c00d01420103c4000001d5498440580b0100412401186407007207940c4801d2500705407007048032190021341c0c1d42c2c81c0c00d1000d070310101c1c0d9107190203804c0302c000907940c1032000f150350100482c2d5001d4a04246103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 285749010 1250 285747760 285747773
    0x127090510020304050a0506090607030e010e1b0102010905071d0106021516090e0a0c09081207020f060f1303060b5d0c0402090a090507030902040623030f0703 70
    0x74005e941900c04c00032584080340d802c1c0403c5014415802c0980070902e0107901c0681540c02c1d00d65805060703850041001011035002c20141c3c8110101c41c0c0351031091018a004034003508440c07101800501a1010002d140480405a003c021403107038180b401680e611346050341c807182c0c0c149480d800d456150000402108420460455080460400e421900e0f140d00c0001c100c0042200c81e40102e40c0e50740e200c94119034100c0c0c0c802001303050381401408080c80c10341495604d4024680c000380103003a8180c0e440e540b55220001e44400b011203001080d1120400c103880402441503101c04d075a51450501d810455081040d40b410602c18031020441f078224414141d16078850f240c900c00305402404440045010f451f20034025100c1059030b882c1091120141401c0e820041c0500300c0c01c1c412481004802015100c205001d401c0310907641c40041c141d81d541030294090858100d000b54014a8124045040007003440600382d00d0308500d443c1600d0040c81000d0540d80c26074050030a00941c4444020000a0f92 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 285750260 1250 285749010 285749017
    0xb01090303051608030115020616021203040501020904150f0b09150a031407032301050108010b1308070e04110109210204020d05070903030f0302070b010e1e012709051002 75
    0x41c200f80607419107503902e644455400c2078211540700c050040c0b03440320300e41d030400c221608000c44801c10080040380e504065030390200100101d01d182c1c404400541800020b6058a400e4400900144108041d80c43c0d001244c02d15809445404d103542c860120311310b41c0e88815030f00300486c050112400e407511800701010310381005c0d43d49420140c5a030744514050700f043c0070b900c0c0a401d09480c00318010030f4808152100805007200400d09502200040096a9006102504540012040e140e031507030f5103010f10744000065041113103184680e000000e0903044065950344214080c00c250394101882c1d100444202403c4d12416003c44005036501c2d041a0125000141c040c3c4002c000516040b42401440265102203680d040400c000c0c1070100181a00580c50042d0b40c2c1d0185021031030040c150750380c42d40e2802c0c18007c541d6246100c50005d02260b0130050745034a801810606007045680d03503d8038411501e030356403d90361140769040e400b08100f2001e001e00b000306070380300c0301a0000d285e04c000320800942 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 285751510 1250 285750260 285750277
    0x2090d110f18010801060b030912250302031305010503040c03060e0c1201020c0105090d0c0f0c0306140106020f030f0f03071704030306060305060901120f0507260c040b0109030305 79
    0x4142940c44200c0d520b181a005203091900900c2d6200c0d03161400380c0d0b003100d1407a40013041580e030800070000d2584012034104006a40480b445444290f443d80d81d580000b00c1c0c00a00510340c43c0c1e20300c1da45c1410f030000054003d04d00ca0500d02103140751500b00450b403901003541c004143d0024000e0a20004600c3c1d0422803070346011000701c64900d0010800100351441e0610300c0c43c0c2503580040c1c190b40703090080c011135601124500042906140d005001055101026400342c044041c10401600b045400c00101c401907402500500c1554a001003451202c40280305203405413040d400c1070140c04030084103441c12454203001d45170070141c560a0346440d0703a100411000400541c80000740611100d130700f28600843c00b136600003174030f07a007000405012248003401071071007038407040010051004200348150489074400241c0c5405291450301901d07242a030b4009004240e40da554815007500c141d0f80440100c01868200c03038041c1284d2041c802216816201140081e05040b010300c04280500014000d10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 285752760 1250 285751510 285751519
    0x309010c031e1d0316060605030105010302090f0a06030215030f060a06051e0c0f0304090b0619031808032404050f0106050318070906061806080a090204060807060207030c0902090d11 80
    0x10945074a0442c1517901140103880b003003585980503014130080b44245006404240c000300a07550564000070511200200a0020302c8448800510030703040541025000b554041e154000f0b0510a00387d441082c2c1084452990020f440c4000841500d40b100c00c00003241d02a850b81844c2105602c40e0500000740740300301c03a481c135104110100219904011540d0a81c0030000559161410305160106550300621307020301c9004140400c2014503c1211030381a10005800c00041004016080102e04000b100000d81501e0010082001d5011650b030f0030b50420301a503e001c595510b9000400c0100c4405484100b0414030250052103290f000b200116000b4500c55031000c2c000080071100307032509000c0c1c0c0058803280d444040030407074a43c02030901c5140c40300004602c140c044c01c1101c004c1c08110010030010100c0d40305e041e400250740b1603600ca0700c00381002c0c0040d00e150319250400a951000d5920003254114a101c00004105c0c005200f070340c02101004129940310141c0d03840d0303245000500c01550350b10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 285754010 1250 285752760 285752801
    0x919051504080d030b030d083409050312090d050708030a030204140409020f0f04060504060b1b060907060f17070305040c080c010210180210050309010c031e 69
    0x150303aa04503240301661003500010398950400114504150059600d6400d040c02e000303080c5490f59020440000f00c404d0741c900b5503603075034440107200c450004114407000d036516240a0200d00300044200e55494072059143e550b10f80d941c079024181d80f000800e5080c00b2184081c80700000c00c3c80c0050681c90b07600d01420803140c9140e15405850b0031503100054002c0429400101000000440071080d00c0c019011241049040ba19401254845400c2c2107054459049001e105000e90381e90f901c08005420050010010552a16000212640408507101881600380c40c0400c41c2e0100040ca1441451001c1c040c1402518060741035444980791008081440b1908000c0000c14504220366840360205540205030f80c1404c0c1041035461401b07400c2140c01e41c21040c1c1d8508540d0f00020310103442c1004a00005440c804c0d14041c160308080c00388005c5d0b001d1008590740102540c0400514080c800c1c00b402000800900300090b400c8494060500b0a08409a090100c0c04491588000d0b56540a051480e95 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 285755260 1250 285754010 285754019
    0x210909250e0307050a051f0507050316020a060c02130506221406042009060f031323070b03060607020616060b0604050109030206090112111323062d070b100303050919 73
    0x3550020500304cc510317544032014000354a800503840d1b0040442d42800304102180e41c0201d1803414400e100c602000e500c43d404280c00d900c83c0c6020f610f407115a00c0550030b1020300071100c44060400e00180c0103c82d01100b001c18006c2c54103115501c403500880c140000c4109407000003490720307040400d0039944460306100844141ca01d41000303510440105030b031040c40012a1910b4082c0c60081c40081003900a1103041141e8188001440c0c42903031075032081252a5603a840c0010403034841c1890094020b03001242181000845e40c2c00c40b07541d0703845102d040c0000c80f44602403010318004da2081e1400560380c1032041002d400e00d10000c118001062400350400b0b000051400192504483d0740e41038010300203031160150300c448041034090580d01450710018035145001d116101d40900d00244a020002014180500a219210340c080004c1c0342d241c00340e4072200b812101a4105c0c1900b65100c2d4011400100c3c2121181900b1056a41c10b0312041c1c00c0014840900c4040000d00c0d240361004460f6160204 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 285756510 1250 285755260 285755263
    0x1005090c0d24060815040507060c0f080c0c09130305070b0a15080705040e030c1b010915080a1b0f08090309060706050405210909250e0307050a051f050705 68
    0x40b400b16000000b00310035160100d00d0340f400005409000360000c038602800001103001c140b174001c07030f036807458034141c980d0590820860402d00e0110082c0008400100e4010f107030b00200e8242c0341d050003151503108650301e41340b400360b5481c080311004000480c208540b000103080800d8042d088000120b00090790390150b0501c416103004c941008071968815081002107140a00403c44420300e4840a1422720480f00b140ba41e80382c0300200d0901c0c80702408010108280d1103099401700501d11085050070006414001410340c4006503104400c00f42405e00700640080301040b500980003003580c82c1080d09a060008031015500500300c240280410029032611703541d0b11001e000c560740030320800141c6c1d0408d0301e04a40303461003070b000004000040c00c02110a0754001c80039030341c04c1e0200765410300c0b01c0e82c0c40102110780003101002e07803070340c140344003004507442039200007810384000c010707011114080e40341c0c000c21401003c9440340e00d80c4104140c454001100313505c40070303080c0540c03a810b000d82440d80554601e07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 285757760 1250 285756510 285756563
    0x503010911090d24060302060403020402030a0b0607030804050601090e0309130608030a090f08064b0402130e0a0219050603191109090c03060f031e1005090c0d 70
    0xd9540401c1c011030301140c40003c04d40d6039540100141c0800a1925650200b0036500a5100103480b0b19404000503146035615004030007880701c02414141c1d82c030024600a09a1b01055409a81600c254000800d01d01964404c1808000204000314113003c0c0e82000c2082c4034260b401140e014540b50b4800140c4000c0030400350001e0100c549401c08000c0c10108002c20020803503006034910360203c4217115841465181c04005081c4800008886841ea00f0503c0e0000411500c2494445200c452003141e81e524121228000c61085440248402d240582d1b54140da10100e09400701f900030f00312a40052504d00003000b11f03042c03102c0700005140d580d04009440742d00122a101001041070800400e4420188560490480b43d0041e80d8241611040400d04004c0010b00c012501eaa000020032010b03910303241c4800c815036009080b1548108540202800010300c0c009000c914400c00c00200e0000e246402218401c5903104020320003009807400700700f481101008181c5410307001600c018400c40024200 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 285759010 1250 285757760 285757763
    0x1806010504290a230f0a060c0f11031614010f2703060507090501110106120609050f070303020f0705032404080c10140a0203071e0306050d0507050913030503010911090d 74
    0x103000041001c0c410721404102005c8424440c05191006008454000d996910855008990007500640078500b040000313001a01d9691302d403050900000c0c0520081c000c4500b598002540f0042c040241401918003400010302d0802140040f10200c0707004940c01d41c055804400321000da40019980d85030542210b04c1070790a58001042110180710658020b526130311071005440080020b58980305050010241c01000145440d848000c103006000b8108400030088a80009440d070840c0e582c54080e6685040083d13401e113502880340c002500d86008a480900150101c1c1c4442c0800d82c84c01c141020028021700840e4140300920003c020500208800e40034881043d000040c2805603200d0241c100c207004042c460136a00402c2004080b550008102c03113001d01200e607081c558455040b040d40a014542c1040340c100300304d4900d0f03809120000440c3d4085400540c0d10440b65218410700504a511401000e0045507081004220000d0035600820042591061450901c0d110000160b54100c0c000740 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 285760260 1250 285759010 285759059
    0xa0c020604080c032e020d0204080d09051e01080f13050d0503010f0e19091106071506052b02041b0503040b060103020901020a15060308031806010504290a 68
    0x94a15420100440700148104560040f00c0305a03136007540c5030041507030140710641600411f144491000c00d406541c00b2b40321240580341e2541e605540101510228420307a80b24a03c003640e170f005044500308400e6040c00c8107a441d02010b54503061080310b9448098481d8000500354030490300403500501003803000a500ea40e0b003540e02e500d0315643e400e029030607802003010300c400042030102d07a0741e2162200a030903401000128a05a190504810001e0100715154100e080000e071842005907a8081c401c0c850807104042103195195010b00238601d42c10006208a1204a41300c490040d82c2041989500c5100500101e081d0400211025180d01e12071550404608007009210810042e401d100d680a9000c4c81d0440c148000f20380000d59035500c0c802e011f024440e03d80b049589403a403a0b0410400b071904045241e40e00c0c142482030364020142a110007056000c0d0740008600b41c50240030b07038502042105100400780160503420000300804441140e8888030868000901420b40051600030450510303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 285761510 1250 285760260 285760273
    0xe0315071101050a062336060108010f0302120f0706120e01021206010804150603120f0309020a051003110301150801060c151d01050a0506100908061b0f071b170a0201050a0c02060408 80
    0x301714440400a850141440040c0cae00501c654443c0b40c038000e0846c0d404643d00c1140f2103071039519a09100c90050340f4015801000c501041c0c9541080c0441614800d440e4204643d550706c4862508034050780002c00b11904c1080301040e00d9601c1002c220790424000c00d0030740003050340c4089507822035001d43c0c8103e964482e075807416005240c100442000030003050405005a0419034002500305645000e8103118001c9059200340c4603200c0e0b842101c0010000f0304040ea2541c481d842520301e03026505c14940065811400828000d120b0441000c51a81c8009550b80c0704404a15000c09070180300190a1000c0c244031050505103c01d000e2240603043c03100c80007401d41007120038810113403032054180b8180424200e0801402000084003a8003003001c2051038401800c240d60264103101e146001d40a400000c42d85205128851038150000505002900000c560319480120340d60b4141c0010325003a08191181005540581c0041c841500e4600e881004060180d0000f00751b50480d4211a149503c0365 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 285762760 1250 285761510 285761599
    0x14190f080105040b0a0b0f070c0308120124031d0a0b0919020d121407081201090b030a02240705010207021017070e0315071101050a0623 60
    0xc0401d014000c01e0760144681d89902000c6030524210340310302ca4810400003400301c59800003409850340d4680c0680c410301d809689052112940d003026400b0031043c40030100002d030600d6082e012010030119442000c207640360600c070640003460310a07800307010344008442c128010203007442421052886410880d0b000c0c00e007440007516210000c01c8280c03502d0010000301000d82e0700c0120004905501c580151402e4040034002c4860343c401c41885c0c132104101081000800c00c11401814445614400c040e416a0b030b0713128070a058a80d8002060780681280b100c0300c0140c2007600039541728003900e98510100065003005500d6540c800d40c4142c47d141d40c0030a1103011464103c4012152000c0c07454a00921460841c1c11181c0f0940502030b00c09000e4142d41141603500c081c0200b404010840c00701c0c0d0004d2500c000c01070640302c0d040228165551034500010400b0b000d40c82040c06450580c00f004401e42e50080610103020f820001d595407001c3d140030444641071400c5284440000030071010442107111 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 285764010 1250 285762760 285762767
    0x7170916091b02010c09141807080403020c0d020a030f14030a05180406061403090c1504060e011e0e010c080c0c0a060302040b0304080f0702032505011d0114190f 71
    0x900462003c590405188428081c1d02c040c003102a1400c0c2c94060f02d20b0354100340010781c0c851141020542207807000c03082210f0203800520661146002c0e03002c0d512208441c0003000201c041c0040700952100094105001040307500080280340d91143c2c0c410001ca420203079849140d0740103401d4500001d100084c0f40c050718401c00b10000160341c0144c605200785410850054425140144500c0c007041010001401d0100c0030081c0d024488030141201c42c0c1046410000700896101c0e020310381c0880d80070340040c0c1255101c4c622608170b2851140b140000040c645504441d070400d5055614104400002030002080300c5000034080340d41d042c0002d01040c030814007888a4507006921a009140c030612042185001d4a000c40341d010394811703412603442c40a0340b8900c00c90302401070043d4051040b04050050307400d1000c00e00060002010300c011180345c0e1840112000b8400503031105561112080e031b80c0391035001d04e03503090600890301d41c0c031400c0040c62166034144044403413044000070130b20000901c0b150f41 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 285765260 1250 285764010 285764051
    0x110a02040501260312070e190e04060506011b142803030c05040b0702090a020708130303080a0b06070209090a080c0102030624071b12080712080717091609 68
    0x20540958107000c0c46036402000441c00074a1b0324184500d48403104201e0343c07103c481c0220340c020b8a822000d0561100c0b0400c2c60b8040c00c03a42220403d1401c0b001ca143c070341c016003201c00b030301d004a8540070f02e0081a5032640200003101e280a03007280f06407000340b40c4040303000c4141d2810800d03045035100d03543c80604000301a43c0019142e0f5081c0241040706214000e61402107801994041c1d03480030540c1c80340b030b185100a110310325000e0036011010841c211040e400a2540c001c4074007a5541420545810002404440b00311103190381c050010081c0100500f00300e0328035940b0095031000e803080d01100c2c5d03c417040c00f5130117048074a5869500204000b01031030b018100014810318030f01c4041100b400540d4160a0344540314001c0c2410340004061042c000c0203c401d08060540e40c842481c0124aa142c000843d07004404122807082c8400c031405c900c0da10582001e4405c2c5965640c42d0703041c2d80c40000d00704122a0140400c0000e02556a50394422881c1e0301c0980c00801c111440000d000559101c030482061 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 285766510 1250 285765260 285765329
    0x7060501140105270402190201050903090d0b0a0906021309050106090f0605090f270a1a06220e060f040c0504050103110d0e03030f09030712110a02040501 68
    0x4070941c0082140c0d99001041c2c40301c0c080f9225010700208180318000000503c4900b4040e4403d00006080001903a1041021b1860415030000e0096440d044203c0740c03640681107129400100d41405180426041051542c000c101b6020020b440250381e01c428060303034400b40920210108480d4204540401849001c2c01040300d4036143c95244c0c00c2080d110158907041c400d070020064040b03280d0b6969501c6a000d8600c416004081528400d00d44407803102d004a10b0295030100b02c2100c00240141e0fa00703000c0c1f86030b5481e08580182c0f2081e090000c00003503811984881009180e40451a100c0c0c000c02200b0101500703112141021174581101000002c0f450038225074000c2c0d00344090ba01045400c0701c10b480c15070b4424280412608520105100b4600814200c41e0109051020001d032009001c070085015080d40401c0c41b683d0b5840883c0c4565a216602005040c0c500040c203600f0054407031081c1488200c8802d05032103002240d80c00040a4500a070401c2013088690f030b40500440d09085840e40162 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 285767760 1250 285766510 285766529
    0x50d0c120c02010806010507021c0302060711070b07020d152901180302041d06160207080703030207090504030309050d0e010315140607020d1a2a0313240207060501 72
    0x301d4195000800032140a40160305000300800d069086541d1009440c80440720303003650b036051060741d08001351340da08242d88010100e1484c1188000101012030722105076949111068078052042d400d1045080d0340740700543e16514989101900c91600f03000b00103490341c1621602ca0040e500180a40000e900d801010381485121000c80d0b001944444d2503904907a0101c070009041c1c0f481004130105000185c48034140d90203103004021664483c407805203002003140c3d0841c1e100383e40700c2c42050754581c580c0c000640541e100003420041148a40c10583c0d00034800d02c0c000c140304401d651f40d1403620180ca6040340204400030300070011545d051181507615111080d002c081c03d407508c41455100d680c0410314034003503200007480c1002d43d206c084002003141e81c4049103101c484412494203150307400c00c0e40c4041d00b41d440500d003a510000e1980301c00810045407982e4a10f9a115803030320340d083d84040712003164048040c4640140702c910301084100d00407078101015030f440125240020440b40140c0010064 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 285769010 1250 285767760 285767777
    0x210209090c090d0204051b0f071e020603011512060602010f050601030614040203041a0405060421080f0a0f050a0f0e0d0509061303210f140306010c0c03050d0c12 71
    0x8503a80c843e548403c15070181d034009541e40b2031204444101c00c1444002c61407401c00940d454040daa890000e1a030705019081c80d220f045500701d00340112a5444a020b94482c10901c018010500c107402002c00560035810241701003010f643c6590240c40842d80044090f075503031f0340946d00521442c00307042e50000003461304200003420700c920018a82c20703250341c00c0e0155601000080400c50705c0181c3e6110011000301700701807842c20303151540d511101140c0454180001d06501048011003094840f082030240d120303460140c1d5003003104040220700410328048182c864058041e5001140310301070080a4214020030748001d000003680503140500350800c3d15910004907800425030000540340325020444900341e0301e01d0240030a01601e2525000500200e12603001100c0d00c0300f62030702855400c3c5c0c01c0c2d200c0c0642c504080d030058803441d015040d4501d075444204006220b544c42295400d002621401c3c00c0a045512611510b142002000c1d00030003186c0400503000038418217400316a003401040c645080c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 285770260 1250 285769010 285769027
    0x6211c0f080402060a03020d0213091b050a0518030c0d0c1a0708040e060d050f0d03050a02121f03150b0f0d03020703020609040902130b0907020a0305040510210209090c 74
    0x54400c1d0345e009001c150340800c0243d01800b070b9404403540d054201803107052041d2200e180a008000c03021549489030310b041000002540210161034582680303803105400c0000340d072020303400da003e011901036041c0200c5840800e1699901181c01509e400303400710f4421241441d45401c40100200413008500300706104078000126075100b110140d410a60402981d5160340012854003030042d040104103025000c003844044000060b03042d8104001d980c02d20964032a807150500700d06c66000480c11000582c0000703403056401c07200501451303904034240c1e001c59035030b40c544c00c01e11000d855082076126107949440d4201e1501c2245006803000440c0c460048024aa0b0040c1d0381b414035210081c040d20b8081500c04e65641e0740c0d8041070841c0e030054050034040c0c14030103000e0001c01c40d5015140c403420404011544092000032039850044c0c0c1529014541420f01d410404600062110720017004101d00c005054948603010345140c1c41c6000b040541c0300c9039140e0810801e028000c0c40100150000d209004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 285771510 1250 285770260 285770269
    0x30e01110c090a0b010c0213090c0e040b070c080c150610090f0e0402040b0d030512090303243d0f2a060203010b040f05060304080306211c0f080402 65
    0x80d003000c03d110000400c12101001030300d030b00540b00c1c0b001e5403101002c006a064611650041c0705454402c41006190075294580c0c0d0320350310000d680240121030080005008240199200341640340100e21050400d180c000030289002c507148004212410403100b031000a007403c05161089505a04061004909100ca1030147d41698403910680710001170105007951a5944a188444409003611041c0c402d14203000d04181d0003105103410441e8180d00007038500c0000306c20741c0e014018001d1645460b00c0000d07a5001c42c0c2580e400b08030f0f403003801c2052802c0203400509094200791104078071094140c0424105600000c2c0601155040c0b000d01004000303026404000b140d44146032202000013182c1c241d0f10100702c03000b42e03500109201e20000010a002d80c1c110b0140040700c6840040800d03050303c802c2407200c00c3c0400d80d4010700c440c5050003c1102450141101e0305007000300c0080107520185c803492030b8900b10000c1c1c40802e00c0e079075404c41482150380c45902001e401c115803d08400c503081940c08038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 285772760 1250 285771510 285771529
    0x521010f020f2b020a0807020c0f090c0708090a06080615180909100f0e01060602160306020309160e0a0c02060f1b120103050f240604051008030304030e01110c 70
    0x41a80c55a40c0c031841e83c44044016052014444000085444214180c8040c00c0100240d079583c016200309079440a40f8034100c4600e1007410000b810881c283c3c2c55440c0846d05036049244111007660090240c2c4840da1034071086c83d0000d022a940710701c040c1c00c0030400d000120810320000581810b0030040103801d1031091004d0002540e0544580c40913503101001d4509006074004025401402e00c1540d05225819070001c1101801401c0200b240540c1d50600340c2e66030b5284400c1c0a403107400d8100800c0450a0b0398051341d8850307560030640d840054802440e0081303145d83e80113020b0340081079080c099a20410b114010040400d4001010030f8288040c10408035100100280500520303010082582e0064000740c42d68010b401e4849096540c403132804030740780c1d030101d44840d01030700c14205e00a00c0b451143c108001440c070084c0078802c445d01c074442880042d1400030481080564107100021b0150b408100840c4114040d0b5602030480a10500040c028682d02f075002c0381380c0d4441c01e600100c594440304e14 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 285774010 1250 285772760 285772777
    0x309060403050d090501020309011401050103090b160203040315020a090506090f040e03160b04120203120c090d080403080903011d030a030506030a021c030806091e09070521010f020f 80
    0x31540303d02650145002a010410300200194000f00901000244c15007110800382030b815540500c980e01c1da001101140d210400103402e1421b1000481e081420404614205080c14415645402e81740d440b062407400c291100c01c0c0f141c1c0c6d8005002803403240d108500502505080343c0c03d51801d00f03c13000084003400305c0c6600d144202e556017032603014007104004549903040a41c4040c0c2103000c460500e660f003800300f16010340346001d800c09038040e21480482101c86c0701100b204001d6540d216861210120341000b2001034000c045a11141c01082007440504010740c800e0800135920310360311052500395020344003842e159154407503820600d10302c084182c0c0c0d0321400030710300011036541d2940068680f100040c40a500552500403841c0d94109018001e51800c0c040e4880303800da0b0b00c0d9103045c40112003045034141100c6080b42c0e051480100820496a08105040221400d49448100048030340c50620075103924040b00c1400100c1100e0300707004a0f81500e1390808110f04200e20203088220a1144001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 285775260 1250 285774010 285774017
    0x606120506010c060c0507020909010c020a0b0a021c0204051003150611010603120f200601121110020d170c04030f03091d0106090e0405120f0c0a08030604110309060403 74
    0x1d070069104104481c4615085841842814415900540703240e20a6030141d006401020000b80004014090702000035415402008116039689980382c140c44041c08080695400300404411b441c0107030358104032014403100050f0740b14904030402c50849c410f0600c0400385400c00d0a980b00f0046404001001c4420505054010404800c59103006152903003004000e03e011403210601240c0c05500c00c0389481a64585801441d0420402014960499903800300c3d88e01060050001d40b0b40325180c010320b18402d16100010000003400500e6500f50310180b900140d20007040380300f84a60010036080811203580c3c2013a03507400c012840442c03a11450001801c0030300d0f85041642018410407102000300b00d40080441d91110000031800c1004c02803050000081c20705d5000b1030341e070b180341030018029503018000f45001c1d4420030070928540c03c01402c250301c0740d101b841030080340a01130251113259440758540c25502c0c50000100800c42e0b14403804e200040e070082c01040740a01000500941003509402c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 285776510 1250 285775260 285775271
    0x1080a11190b040e040b1b090f010504080118050d0e010905100e0901090e01110306010c02010e011803060e07150504060305060a0315050612120a030b0a090504030207090b0103060612 80
    0x801c1509901c0d81e0722041040000050004aa84040e030f403240c05039100d006144003c0d02e8080340c210160a0030110140364020400c504401c61601c002c10f0080420181005418070350703110306080c00c5441100204010f08442011101040428040302c0401e0015040800d0300104180009010070090b028950040c1c40c003044220b610b80c0102a4620340c114010001d201c00e40c2c503900410301a00b00309201408541c2418000c0c1e18950300c02041d28428001a501d441001c48541c0046449282015005041c4946039145011924408203844095802a403010030b451800890480c5410f150740d000c1c00301c076440e0101c02181c0641c48030403a0215080c525012075907484000001e0280100c0750300042c10065103405c540d42a81591700100d1081c4800c0711011803850320070b040640c40b03c0504d800306011200030010188124060360101c04890809010714007415101c00000040790700c1680d059001da84000c41c1003110043d58090400040020301e801c0c880350b0b00c0d01c1005044a00c40c0c40c0c45683c482d03100e6 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 285777760 1250 285776510 285776539
    0x1b0503070506090f070501230d060e0a0b0a05030a020306010626070c0b0f04030e120c120102070b0112020303030a020a0c12030f0605090c0a0305091f06050901080a11 73
    0x82064510864001003540c4903400c102c428269100100c240c5039800c1d00452100043c1903010304102c0032040080f0140e041c0360009020503030019400041904030040d6111804903802c00120b890b14440e010b5004001100d6481100f0024890003990081384203501610581005881c00309800b811a0050b00b0031029403188040c03030104d4440c82c0b00345c800013102c4802c00c200400703a0280038805842d00403601704000e42c540c4009000150342c100c2e0098081021160b003050340e810001e034481c802400d2401134800941041c0c00040808540f0010b501040e900861001c040c003928116050042c0015540043d842841707601180d140c2c0001403c82040035404642c04014a0180754001d48940c2d02589821444c490b03646c0240081c4440381045110700e140c84030105490820300c8406008401c070080d641d05040d48072904401500e0024004120f41c041c4600c000103009034220fa1050217441e4810100301d00781450103208042105a02462595000040071408141e1f103c1c55200f030360701c1c117840700403602910 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 285779010 1250 285777760 285777763
    0x40f0905060310110901030c230c03120a02090a0e070c03030207170310081b01020703060903030b060d020a0f0813020904170a08060405160207141518031c1b05 70
    0x1641642ca5002d0504c03503071a0382055040010b0080180989041001583d082d034201c0b0034510a91102045101da00b2403c000a220321014102c98905401101c2c9080f0011140c500d800c0d000b50340000c0410703004150700c10a803a0100d4581c0240a00d00d041a246207400c00009002500a640180505600152050078800398a0510b51001203640342903949050650109840000e1071040180e035014240108a00354404140311054100590060001d107041d5100d0000518250b2412000d042d5580b48040303140c0c6840300079005006214000507140c50200d200680f40820014100f0b0403c481602004080409005010300203501a03400c24015550351501c40d040c030880c00f183c180e41840200c0d0060446030700504140c855082034038203012035103643d84070500501200b8460f80c09604511028460460100d280407541a4003d00012402040c4405151180e01c9031411446259510748060102d0604109002c04802442d120700d207100400c0d04020810109028041c00710400d0310f50150038402c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 285780260 1250 285779010 285779023
    0x18010f14160b130c050907020a14010e0610090c0504030f080a140319060f0509010612111209160506030105011b120201240b190c060507050915040f09050603 69
    0x140b21520b2011401d100c80e02ea0701003403000d00101c64540030b802021a407401c00c6d42880b0b010b29100e03001400c00c42455a5407840c003030070446501c00700e90b5950f040701446500402880d400380100c0358101c81c481e81010465019030780030145031000e01600b08802c000044002d58174158494120200580b103801c0040119044445840501c440e09000300038085490550a8800c140f405107080c10000240c0d0340380c90201d40e004500c00d4550240d002e00041001501520b070740312107203d00460000d00d8500317031f4204074055004900707240b03442c3c1a18401c0000102040000d506040900204450800c0c900800181d103440140201c03410480344201590204078110240c01030103500c420072003200700646c440240208001100613203640c4071004015500740940381c408040d2507014000d90b00e440c1c00380c1c900501403d60200720204000388034044e0f40100e1218803640c0e0040c0c40540d61680d403040414100001c0080e43d85444504d00340420040010749004075030301b03040b620928000303d11a40c0314070000e03040c83d5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 285781510 1250 285780260 285780263
    0xb01110106030303051504060e0a2004080a0b0a1a040c021006090917070b0a0c090e0a0c080105060c0304050d14030d0c180503060411040204090204090218010f1416 72
    0x1070070603802200b090b405030041442803c030f808001d070601490500b0401030340d02c1da01c00ea8600e90301100c0490720503a140d07001540d076880040c054120f669070341c07407042046030700560100790030703030020520359040180b00c48810350401c46000c41405994030b244041c1d5105035030f01c840b647c4a1076039010681113850003030113207041d0110759090404c44655102d28910181000c140c04540360f5040e590754001c651072940640c0e00c200c0d000401030380144e503080000d00041079000582c0040c0310020074005020508070031190700c0342c1861100800c0340000098081c244510603000301d03104100a02c04403000302000001d807401c403a000c17914010341444a0a01844803494481c18012030f02000070009003201c0d083d0005101c50300107940790b1401e0b0704a002070400d404500d005003581a04968041008a011141d05c05840326004000500c1c10fa0341d048100304a034841d6002c402c1d07031a0017103008034440315800c1c1c03540c1102c1c80a00b00009810009440104003410703e1014208280703011a1071218a0f115030504003040d0b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 285782760 1250 285781510 285781513
    0x602190312090c0302032116050c0603041103061b0f0d110c160603050402090103020f1201061d180d080417120f10050306280c17100b07060b0111 64
    0xb411424201844035031030109034020b128600c0c00b02c5003800302206080d02c502d0030300c00c6542031030f010f20510800c0040400c801d848034800d1841c1e400190351840011401548a6040942100c000c0000e041c103000c0c4c020302c00d60343d15403240651740428402c4022a940c4065000000b5030ba1448200c040c401413030700c098400c0a8241c0810078402007840000c020b0980062070090f118425034943c021070030f0300c0040b50025009900c0c1401040182070612048079900d40c010b000030190307500b424440303084540c1544032202002c0c0383d40d0250142082004225000340a030700510201d18680180c0b0b0390f94514020701c400401080b900081c041c00f007085401d0310032690a0342200c0da20b8880f0b80822900c0303a03040d00c449150b07003500e002044080c5600d0508404507540980a440301c0c2e030320b05104030b60780d802c90151820720101c6000c02d44429821446039403005c001c162140903c5000605111038101c200400b10841e15100c034005101d01c032480015a280140d00ca40049a0100e01c200100e482104488860009 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 285784010 1250 285782760 285782771
    0xc15130305031317060115030b28150507020a060f0c050102040b041406190513080a050d080601110601030b0a020d0c0206040326011a040308070302010b010305060a0602190312 77
    0x18804010003c41203843c020b400380500508031032203980359142031060a00d0b4403840c0c1841010a40a80c200800507e8000c2c101003c114210601c00fa410410400043c0c11009480083c414850781078400040700390f82c0d14101d41403e03826400702d09210001d001307600901070301c0e010a01d60305101c1d00741404403a5014009649841e521190301a0540280c00b88440c0d1240c04c1c07484401c44e04100c1e0a40c1c1d00d51022100c180804400940151425230201c81500c464011a5401042c0558100044002c1e20b02c81c000910140c021030358000d03e600c1c07000d0041410070450080c580f00c1108005101410340e130b00404144c0305038440d000144024415000700130200350411100c035615170380204010f44154042d8480300400c91070340003104035541d600c400600ea0018050014445844480c00700500050035040c2180742039101d40700c10102d038000c448101c0042c0c0d115800101d031540c3c1401910340201d41030702d10342400c605258000e9100c0c01d0b811090702034405c10b00e44000504d031052403128040004a0800c010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 285785260 1250 285784010 285784027
    0x27030807060e0106060f080f062b1203060e0a0c170106020a02030706021f0203130602040b032a0a0302130e09160e010b16060e030a0903060e0c1513030503 68
    0x140004400010740e5510340000040e1113801a403951081c102c031030b47c4061040e074580c03400b40b80900d005899150070001080240720301090020b02c03040c80d03520415070664484a01e19088403140c8848540303174101814032a040100074005d54421b50804512080404c14211214080b90750741c102c0e4190280800d004000001e41c140c01050000c4054005c0c1c068840b02511520143d0303482d00300700002d00101513815520320030101540d018607004108180251441e490648402060341c02c2500b004e10b4110000040c032691384000c00000d46008040c41540041d040c00c0080701c0f120380125001c030781c140340d00015030324100840d000c0402c01401c4903a03000007240c00c1050300341e50b940094003041045865010404164003410209031030480d0480c012980c680801c8004908440c40f40034030407106079849070b8180b9149101840a40f21020040da110310b22a403070345c181102a903640d650343c824180c1111921003c2034540d0a4881c10400c0c0340c00d8000c0d0f941240b0340300c1181c01030803584040c00c0e80c00007041629 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 285786510 1250 285785260 285785273
    0x1d0c090d08090103050906040b0115020c030a03050c0d020d02100906020706050f180c0307060f02030417280c05091503120702040606140d0c050415020f0607020703020127030807 78
    0x1903140382c2a07a003003045590b5002c0b607940c2e030082505e01901c4452010010031810002100c8003c90880d54816078504901c4140420b00e08000101e003140415070100b0103c4001c0010411a14039907503e1004042c61601120040d40f9548200308542002d03454140040500005404940699502c00010056032801172009200000141c6003041c0d09030101042041e080b00010303040d02d07900002000b400010303203005415a00141c00c1d84144080d070205020001c7c040500041010b060300418001c1d0000149807200d02d5032012040034803c80d4a03400d11041c01c00f20302d4212000042e140c1c19180451903860f03051480070700100c4110741c82e526200c0ea6a10440c59000000601102341c42500d09100d25a16103000361408210314103051010a02840100c017840c0031500301035803811a41c1007491500b41c66690311030034040f24203084005a8851221402ca200d401c011b00795000d6001d2000c0c000460031680020204a01c3e1514449500014125a4a00300c4264083d5000703681c40009143e4401540c034180 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 285787760 1250 285786510 285786517
    0x30a0206010609061409040504020f1e101e0305090c030d0207050915151606060b09011403091002131518060203160206030406110d060f0803041d0c090d08 68
    0x103030000f40c40750600080312030258030842030744c20070002d14904122100e81404002e080c004c1040c2ea212005001c00c2c3c02a49855071103c0c042514003031100104c4490005114404400d0207207201000701d98130420301b00c0c14680310841a154060301d00401d942d1a0403170540e1400c4044896103901d4040d1100f00c2c0100f0390000b031840308884040e07036881120f035200e501c0c00628a03800f10703c0941100c0903600e01030601181e4002000030507248a403907601c1e081c254540c041290382d41c0d0048003c007040043e800940c0c0d170700980440c0751324a098080750b15501e0a9507003107440b41c2114120b00189d64000c101032030724541a4a507032001d002080e18802c1c03182c413052002002800041c5411141c03003003114010640c18030100844442c2d00021b030720010035501075420710125a0000b0310a40c0c00c03d0b555903007481c40a00b0f0300001c1003103024500f0041803c904000004108001e158462003003a03208003c2000307240c0c000290080803046040b8090f0703441d51120070108591240c40c60880c1d01142428058041001c7c0b00b018 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 285789010 1250 285787760 285787769
    0xe09010605090103051303050901050a030908040e070318020a14040905150121030e0d0812010e09010e010e15040804170307060f0507090b0f07021305011d041a060a08030a020601 78
    0x92000f51a0010042c901010315500640010020800c9c01d0040d40103200421800b145031800081c0100c89443d281c0ca95001a003100d450090a031050150a0340e0601a100a0055681d07842140e40b0880d40020024425440f03003800700038501c012090180d80300e500c4818110f4102c8181c3d00705840700c070181e00c0c1c3c074502405100500c2d000d222644045180102441da0201d0741619003164408a02c01040304103901c4280c12a80340c00308000c0c040041100d020306c076000f4010385010010506146040e942940c4004840110710381c90728428100c0c0040010790403e480d080b001210045031160f040c451440e10594000d0107010040c0814048d80c0ca0300003006021340c5010f00010844095040c40401c20f42c1c030207030b421500240e4904401d03c40b41000c580101108800002004c1c58040642d010072100180c1006c170000c0326a0701c00c010044100c82508140b00d4488207500d0f1030f59480d25a481407590a284002e00c10351034654000280c0540740e450400d0040e06109040303e81b42c3c640100002d6039024240207 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 285790260 1250 285789010 285789017
    0x40b06040326070b010504021804020c100f0e1b06040509090607020105150105030a0e071d060301050108011e05060406030c03050d02071509050616080708210c04150e090106050901 79
    0x2244900941ca0304281d640540e4008103031300c8035074a48402c00c40650030024020807002803c01d051042907071588010714620980d50080c00a48403640403034011105100c6a81c3d441c1c070b0402400c00d04940700400c00180140c054001c10b681310b10b448011442c503000300c1e00403c5c0c0018143c5d0a10041c05c800141003840f03200903038024085650703031400910002840711030250110343c050001c12141c113050341005000800c19800c45a00b05c0d6034680c401c466070492800d440ca2489c4000c00d200840c1402e01540303024000d400000e112104a9001c401603644180401c0c440c034581d40c00100c1c0859440b41c01060085400c01955122a5224102191603091a134809070261182c400c0004050102c00c040308402d1042d0b03190340c44103a11b004240000d80e0f004c40c9041002403000070422000034504009411680d00940c14680c49100000740700c0e00403000101c513501c004c0c0f10300f000c0211000110f404ca0707040e650a1a0044500400101c0580f00f218504803890b81c00000680085111035100015029541003641d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 285791366 1106 285790260 285790313
    0x807110f030f071a0c0306010c0c0308040b22081e0f0f01060f060201050f040f0501020903060705090f010504080a0605100b04030b011d090a11040b060403 68
    0x203a0024020708089001810700c07007020180518413030704a400072182d0070404d41407106800001d1205040224202c800010040326116440045900c94401a01ca58841010340c009410200300c48000d03d10320009a120322001c080030000711101d80d000340c0180d4006440c2003542141c1801c94520034456410034058074001007000032100d5107101b00010340c4c030b401c100c11340808100e0356008500b1681403100340000310990a42440d0090361000e925240a040752900d203000e0f005511100354180a030380e01b080806500f100082c00c030700000307c5050790020a450010350b118007650182819039841800841c00040713107680320581251040381d010544581d541d458051950150f041110f04000843c01000800c062102d1404400040d0308042090724102c01c035207986248020340070b44040343c20b801e910844e40710b50344210b80702000038011a595903101c0c108441e030344225440070b400121528 = true := by decide +kernel

theorem cover : BRFrame.Cov 285611510 285791366 := by
  have h0 := BRFrame.cov_init 285611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 285611510 ≤ n) (h2 : n < 285791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
