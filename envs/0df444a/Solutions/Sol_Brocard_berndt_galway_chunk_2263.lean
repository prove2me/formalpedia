-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2263
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:10:53.45605+00:00
-- url     : https://prove2.me/submissions/55ff7f81-480e-4192-968c-7194c9aade22

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 406834532 ≤ n < 407014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 406835782 1250 406834532 406834541
    0xe0606070f05100912080a15050402090616053406030b0a030209161d030304062303010308030609160e0111120c0304080d020a0507060305270d020f01111813 69
    0x144680c03150011740c10704010041c411303d00104030400140c10300c10000b907010702040b4844103440c0203460169403501d0800100b002d920900c18032000030740001003a01c00f80140400e020001c207222241410700d07003d103040b00c42422515a10500706c0ca5400340f00800c0742e64000e6002c50203d07100501540101c950b03070380000e086031004131200c1445415124205070304540c4102207183c44aa070015810507031640da00825681e0103203000300070a201031004070001d82c01c2c800b0340c2054451180f6000c243c0c4ea6071a80380040c00390700190344031402102003a01141031540025981040d0001c59918061403e03003e000445548651484d0312402d03001d503009a82d2101c1c07509000b0001d46110300015603a99240070002854101c542035243c046401032401400044d002041c0700e801c90b551840c1c080f60b69150318044814191075202541d150000100d441c208100c0c010603c03c800a1080e002c0d662401c960341c40346400d0ba010035218003410305081004120001580c0201d51449201030080080007245c1b840e04030846 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 406837032 1250 406835782 406835801
    0x6060a171005041431140115060201020711060d0608030d05040201020d020708070b0f0909251b02130603050f01020405100f050315030f12070501060e0606070f0510 72
    0x12040003014002424940100b4218a008404d58165460944030101c42d2809124001222030000724404082c0411942410075468110046040510110200500900c00c1122481d00000c00c444d00140700c074010710a880c0640d0700828519802c9580f8820454641e002081d800241c0e80d4a10300440c590310f080002c1c0ca40b030300103007400140c28103203800064a8000c0740b180140455100d140c09000841c4007050400c21129810846a00e890314419220f4441c020045119040861201000000550881078258600c0c920310b1070b4903440300d030701c60840c5c002056412001400740c07824103110050070503d0103091061316034500012281d031259241c0d81010401c400c0d08070160740100c0c007403042d450140a070804840803030505041c811425103001e056400010000b104018103084c0e60920364400344055031408114000752207412102c5610880d003a040480c00ba250f80d844c05102107070310b001120550740208002485241841c1d0f85665101e0810600d40003100d42e402407100f86c4100303421074010701c41b22 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 406838282 1250 406837032 406837051
    0x10c0302031801020306010504030308060102100e0c1008010b0a0c0c05040603080408010b010305070f08040f1217100503030417120301030809013b010507021003050115030e0606060a17 81
    0x124286203210b00a0941004842281c80e481002400078907030b080f01c202c0702200e030306042c802415510180180c2c20113000c91000445d05050612510320a0300c00700da407101e8074000300d0340c0c1086030b0355032141112905400d0040c1c2c2c962513400c100f56020540240c6000512503c00d0030842460380d1240301040070f036500f542c0b00700c2e9807400105003444100028000d40051000a280401003481c3c164802094520000c2040040c400b0000c0810240550b41e5268005950809400400080c807100c00500068070003200d80285400100800c00c0004560242804c0310b400600943c2030504103949039450f06140e40461015214200280d4074101e40071010b90b009600079200140c4070300050001510540701030340080071494403612161004100d1240c0d0b07916031701000354051075a09031a001070b172f198890b0309000b03988003a0020001200310340c5500040c0c161016142040311b60f40780f100c1c0c268103558045180315010b401120014040f414601c4c080e0110707030380c40d10b00018842ea0614641d0050142900d02c0e084 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 406839532 1250 406838282 406838287
    0xd080408060118021c0f0f0908190e150a09180911060307080c13051201200703020307080d0b040f140c0702030307021302250506011d0a050612010c0302 67
    0x72850001c103518140c551003e0709501d040c0c1100031403134103056131014403544d03650340e5115416003d06607440745201156000b01000082441d00340721130035400040f8100304214601214103000e6105801c042c0c0302d524003600c100303000700010340c22806a402080c002e50420840d40400560058180001000d42401035070025045285050018620484d000c085000d0607082081c050080c2d44849425445500328403481e8854100c050301c0314143c0d005a2103c0e40c4400b07454400001d40c0b5042d40031070300008c0202c80c041e030254100c24000d060b5000c1c020300600560001d01c000000715003040d00034010071081180001c0c1c45541000003d08551955080b4910075945d8000d010824420711013107908805404142d038140066580000d036079110301d0301c000380640b04052624070495560b80540d4001c444014050100500300000d443d0780c100144400d5440b84202000041d251010b91074400c00b01c05444040080c5640d0700f9281d0019001c0034050365000400000d05880b90031003071145201c0c0411954015a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 406840782 1250 406839532 406839539
    0xb0c0d0b0901030b010806010b030601020d0e040e0a0c080d1e08090114090d0201110c0c131104030510060b0901080a0e0f0303101404020a020c01120e0105040c0312020d1d0d0804080601 81
    0x380b030070b41f0580114611600800511441c0d80c0c002816032011541341c517248001c2000c080108002e41001e0301555900d100e111002c508104416800a007940d40f10400c1301c10300c507590602155035044148401420950011500700b12070f01c1103607180d03803203d5000c00201c2c88803210003007031004000c112600d00c016048aa08002c0c82d0398207000b0142c2c0d8609400d02c0314149440c25000d6510303a000b4120007071041d4680385074000f0009083e0031103c03e105030740d4005600ca07952410196140c00c0ea11502e055402d10300360000c42c00c40455010350300100410b9440d405540e880c100210001c1c241c58070014098406c8046109405404100652065200b8111510320b80d1805105661100c02a0040361003140140030348003400f80d000510440c803003824641892890300403035100c0010003101107280303040c0d401c0400b00030500c50b000c001001280c0c4540300c04900d0440c2902c0482c0c030303003100000c03c4001411440309010301401070070590107014001840d120070300856540f10851540203600c200007a811200041 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 406842032 1250 406840782 406840799
    0x3804060c20011202310e010b040b0403020d060902032a06030c07060c18080705100e100809240711210d02040308030403030603020a120b0c0d0b0901030b01 68
    0x4440500d03041241c0d00003200d107907001030300034040300048821041e40441c0d5140710f04a80d82a0008062680511210903050b1a450000d0740c4000e02401d8090f1380d4440c000140148a01c0480d0101d4107449001420b103800c40c2e0800402103808001600c1260b16060002e001d6034051000584405011620080c04903100c41c00000604001d04d030141300312414010071422801100864074140e600060002d16994411000c0da031000c011943c0c20403481c1140000301e0801400a0010103540080700c90031100f2000303182c11039002c4000030380d0036001111410400d2100313020345191a08143c10b1000d07a40c004082a09101c0141001c442c0d41020403c99018844425044002080e401000d200500b50740020402840300c00c1c041070740e460780708200000b40d0340d01840352541030340e02440c4e000083c0c0d50b882c02c2c1410b0040182030280000e80c440e140310403000441c03030756800c0800321302c607404840e100341e41e500d0144100c0c03030350050f000c0091010344030780c01030205643c4c070007039540610701c00d8071106a99410155030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 406843282 1250 406842032 406842053
    0x1506180204050d1211060a0606120507050a0c02061e120112020619090b0408030c01060906080a1502040305030c1e010207200a08010501060509030114013804060c 71
    0x418044920401080c403031521200034403520240c00c4410303102650101101222408800248079001d07014240a1103007200c40e903088134007160055a9143c3c0c0c00da400360314000450344c007502c1c1c19000c2102080149801f0707016103180c0c405a4001401a81885421002060100c01a80c0402d50048000554034000f803031800d4050302404500f090b04991100e19408030740385100e09102c4143c08031056410030b08032403040c0c10b814050400d00c082e0030f444587d6001d006650341c02c40006d8028a5003010400b04191441c0e100340c0e0210f44d51240108040c050641760004600120032014114540070080031010070000c0008080901c04000140882a0f91504050001e00d07110107018241c2d0040002c0c2e000b04048070252040002c0d411020b004640301070b0002181100c241d4004800c550a0134000034400c1d820a010300724000d8294001e0040c0c1440e1807038810340440034040c940440e10040c000c4d1849072080052103039491000c40c458010004070104851161300690321090005500c03880d00b10800960118 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 406844532 1250 406843282 406843319
    0x12090e091f091a040c0302060d0603120c021f0c060c091d0f040803091e010e100e030409020a090e0c040303170906010b03070c02120f0d02071a0d02071506 68
    0x20810000e500b40e501c0500c01001442c071000340890480203e4144054420a41d000716801448242e8840c480c00030400038080500c020ba0707041c0c03400048072813902d0140c1180c2c122a68028542480900324400c0785410702c00119180040010028002d000682c881c07150710140c5150b5151004075270314002d42900c144110b00001800d400c0300034244a144503020059540041c1d200c0161340c4c42c0d40d40c01c5078180ca842400d403019860242420725465902c541075001d450280003100554907001903c4900310300b6680c1000c10302482c1d500c100820051610b1035806030110403103510709007500540c0c440b01124494015a008074200e41d00280030010550461100081ca103d2444803020f1890031055094581d01305120b0341d203070110000001203110340310b0120781c2d501503401011601c3c504060044c0703540d10300c40710042c0c0d60070744030761a007580c0380b41c0c0000307122411a0320f86000c00711201065401000c0720341004103111886502807003d00009841d40d4500000540b0411001a00d14034101c8209600e909124 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 406845782 1250 406844532 406844593
    0x9180705060c150402060f070f0b0705120609092e0513020d021003020417010b03010f091205070206131413050c04061107030c0305030d0b0a0f0312090e09 68
    0x81c800121101158040ca400f10300d0000302c582d81c0e640d00205410388507145c640800030700005040d0040060710721032610030b5400303049803408680c1c40e200300340c1e210322403000d4050340d0203041c3d00000e003589840c3c0c20065000710b08a00740c600e1000b6001b05600b699841c03606800310a682134403000e80400e00d902c2000c7e84480095100e80d001c030413030740210f0015050300c100039018650000e123021605009804440007002080e81003503d1000d01c6140318000c01203040310b503110394240210825440c15a00400240c140c00520004224113034480503160359101e1901240c0116080c020b00721030014060164005040d0402c089100b95210380c20032807100407113070f04501d40d140f0b80800d000071440c100040d03509072207440c02c0180c2e1000e94000c016142c030300c443e8401060180c41800200800c00c000c8050b2402e081d2840d03003404048842000c11140c10558010100c6010603001c081000c01d07482d01c42e9001041e032500300565400e4403021a42c00c0d03084102c80090550340200c3d92807200841030a00f1444000c5003a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 406847032 1250 406845782 406845787
    0x50c03030a081b0f0f0c0c1306090f02130510120f090b0906010e01060e04060803130501141e030406090210020d09080106240908060f06091501020c04020c07050918070506 75
    0x510322140034000c491441560f0030021030b003c18002007c012041400400030a07081d0384007091925040030b030805c0e01844003094200045001d480204d4001c1c1d8850789441c2111062241c2403400307000c1d9100241c1080820030202c0440131202c51390a1044d0507d4501100e00401c9004c4603051107140310401030500b840d00d034841c10042040e01d0800260300c1c15109286000001c1502a800080140c40c10341c1205402d8000001c0150200d512803011b103048074400c2e2692041d000440804000c14060359640380010744d01d403041031154010050042d07910920401c00024200d0181e008101d900c030304d5091800140e4802400c0c4402c90760000101c9000b0146813009002c194208624402c1c514100201c0201815100f600985064003884243c1c010f80030303650440700315151600301042901e000781c541034094900700004c41c81e0b00e1500002c48100070f0040c3c00900d203a80c3e06100b803100135800744d03010401600a80c1004103003691104a41d03030145081c5a0181c10180850900e141407070010781c800d07407203031004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 406848282 1250 406847032 406847047
    0xb0f19020d0905010e010c150204051014090603060d151406040e0703080c010e030f0901030c050405061206030f0109050102031501020105010f1a1c150501030225050c03030a081b 78
    0x2402c480140d850a00c1e0841040443e640140c5900c522268000c024010112540d007010085501920850700101c2c0c0380624105441c1094900001c21401c080c25071104002c0c41650f4181a0015500038001030f280c8091081c1684034114807184680e18401d45a4440451101c001d00706000c10f42c0006084070708100e200d005004241c0c2e101241d22004001c4840410540c80c02c5100b07500090b0032a00d1a0207032aa2130001030310050169012664043c00711f80342c02d48208000d44154259000c2c1e03580544030f203140c0382040e15520704201000b802c580c1e2610079035000f540050028001e1a941c9442071001580300c1c1800c2c0200c01c1e80ca60628811411a854000100055000e42d140c4030210fa00a2180010b00c0a003600c051031544a24121803000b0782010107011202030300c070351284c034003c542c0280ae8801d264a600044007030b84903030a011030350700408071003036000c000140500000179403080c403c0b546485105000300e401e5800c284404c0d0041014001040280e1112084158400044500700b0303141600 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 406849532 1250 406848282 406848287
    0x100501081e1509040b0403090b0f0a0522081e0c01020a08030903070204051603051f0501050c01020415030902131107030f020a0c03050f0111040f090203100b0f19020d 73
    0x190803180031001c1141202081841e0985088000402e40103026401146400d050580104e001580c040307002614151002030103804103001d4600c5c078080c080d041c40c50500540ca0464483c4c01c0412007100c407520f5030b07100032078911074108070300f009068400c0030b0800707280d1790201c44d8481e0405040752402741e0071201d00c1240c00e80e808200d81c91044d1b0701600d0307103450307480380a803640c07a50040080094009240409001c0316102c40204900254a19030342070041d980c6035158111090380b800501c40721b00e2a0107205001d1076000d000503080c0c0d200200001802c0c5595880994144c404040080d004203985815081c251f04000e82420020102c00c542486042000c0d4124440c0d80704484014040000d034080041f40304d0b10030301c480c071809a00210050640c549905040f512604500344910b0158070b0800681d240103042d2003900c0c1114620701070140c8045ca42900c003406507000410180084904007000b0841c00d00e000040c00008441030702040d20383c2c590500c0c0c40d014020184010b030555000580c182000c95 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 406850782 1250 406849532 406849561
    0x3050108010b0d02091f17031b030c0a03080604020708030c0403020109080703051002090d141b03191217150a0902162013020d1a0102060a3210050108 66
    0x2400031b490f11005c41c00b80503c0d00d1848140d070000d50040d814200d50b25000302e0300001038000301101a101e03095108000f40c90940e24441c40860b1344283d0804000d85011034060080545e0040c0b002c2c101616024103661040d4032940308031100c0c604054085814415564804510005000310f00e00400e01c10b41940c44250b40c42c03102250007001c00b87c000944102d2038880106048440d903201d80d03000741a4003800d101507158174100944c60250761031006c0b456154a40014070a002c1c500314034250742041c1c41ca854440700c3c04049031100f0107020301040f01c800200308025201d44100401000c441141c1026010002d407000f03664001201d490040c44003412011240b00c0f0454681d500180340382c0121054a840c5e1240070516524961190000f8000d0400f033b1029002030025130b105030030420402200001c0350070380c007050100c00340c0168040c41c001651070a4a500118804035044081040382c030280000e181412585d110314180c4c0c0555405004205014040c01c00207003a090074800c1a40c07512900206108 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 406852032 1250 406850782 406850791
    0x90e0d0f170405010f0903080a1104050a18090f080703170601080a0b2d0301050c030708070807091806090e07030816150e0f06090606010203090f1c0303050108010b0d0209 75
    0x90440700d010508005095010580041c0d001074188801440380c14050b080e07420884000e8501403c240040c0e6000038504125000d96500819401e0503078180804081e00e407207904c000404455a40703502c0004200350207050150a031140c59071542d00c1c0740925008103c2d42d14920040c0c8140c0b0400c05004d0075a8103d9920355002d850000001403003000e510000d22401030412810900d0307040700b800040100d81d0075038501d11403171080c0d00034072882d166071031282502c0c03000302d03080c6001402980109007198481c140346900600b43d45410307090144c0764130400200051180548019035500c4001300071180581c0078203500412810003800702c5520310f0b110b4146a110b800050380b43c40b0160b0f0000e80810800c003000004000d40b02e40f0801c40030001403846903403040910042c0e504c3e0710410b00001c181000000748540704420607400b440c11700c50b180003442280c80400c07c0c3d16034440b040064000a2140c3c400400c407900780250b801042c2e9514282440c0d00315a80000118000c0614840341800b6889000400382c12 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 406853282 1250 406852032 406852067
    0x81b0c030a03050706091b06031404260421060b040507020a021207090515030609071206020d0e0102120f101d090102040503030406052a0604120216090e0d0f 69
    0x68066a180040041c99090390041c10318403030010105844034004014403d4500b01e450030492251042c02c2c0b09a00e20f400c980c010643c401325504043360759404005030ba040920540d10a041503119041e400c070344440039048800010154501405110032401001d003403400544c0c0170091401c0c0154025110350402c2d0020340a8507545034540040b140810104000744901d04042045041c502c042c507815140300190039211b0312814007c0f80350f484010030300b07070b08458074202c40140300c0b40d65540306d60181d000540e01030b400319510014501208000e00003800000380e04542101140340844002c8401940039100803098030a40c00709202c6101c0088100141c0440c41c0d01d800c040b036440c840c0c00c0d03000e4030640c0c10203600350001040015540e6040006060b001c0146401d000d412001030b50011010712004020700d80ca40c1c400c41c0800c1c0400d0211a151007954201d1040e15194000a01f0b4400020041e87c0807030f03961a52110b2001e01904180071040003d486441c0a1911400c0101e00070030a00c1c0c1455030418 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 406854532 1250 406853282 406853287
    0x30f09020315070e0301090c090e01020903280209012d0b121b0f12150f0d170318010b030f0a12120c1d01020c03070b130e04081b0c030a0305 62
    0xe04d002d060f0454003544018024040702c0141c1c42c0c0240700c5042817180070140e50421503560a2844180280c80c00600060000e0640d40c5402c45075500034544011808c02d04440c01d51300c400561104010203000c0e01c0260104202d80c1c111145040d80306600c00b070308903a0b607009030740240540400b50040302d004000343c080994403034136800000c69107001c2c8107809031900340d000650b0210038424100505490b40c41d20034814040d68400142e030202400380480306510042c0c0c0300100c18145001d00106002030b00528072104494141d0500071160750082c4d4a001c0020000058007070084000d0184011540c1d0942c0600103281c0801c94090b40d88124102c01033442c0d0f508a400040c3c10701c1078068004528900005010825002401428120b0184602c1d0500c40c007040d10000c055000003100d007a0f010000c2e0003400460b161214214598222012142003508000d0700060b42c00d0b0700342c02300ba000b1801b81c80d0399581c46102a18504580e4408815500306070018001c051b0603541c0403071200c00c038680604146a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 406855782 1250 406854532 406854541
    0x1060f050702031c0f1b020303040e0c0d0c181202090604051306050f0708070f02070312020304030804080627100c050c0313050109083c0f010c030f09020315 69
    0xa00f000e1014401c0041c0e000101c82800605900400c5c0180e08078498895805c540119a55003003030740c00d5088080d406d40e1041108003c41c00d08410a40d0348548140402424207580001031400c0c1c4402e015054001075145a84105400b040c01140004083ca05100350304140694003203641365900404e1a44942d5071500001c050a41c5617440c0c00141c0d80c450800c1207103250a244401642405503010b00009207070000007031400e13009442c050000741c035507002040c0c040d140d503861000c2e1741d141090030740450006001c0000054500790107003019000c0c030400317000503103090085140c0c0f21645031602003161400c2000214805000300e0801c1d040b4000090124084d030708100c0541ea244900e80601b00e291000045089945070900806c3c42030b901c090341e5124280781d4501c80140c0d9807100b483e1500e40009001ca1105009290010b11042804080c0500e14445040c0300342c1400c1142004401d00030b651a083c10360030070380d03251080950f51100c13510204401112a00801ea480c0f62071080c03029088800340125 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 406857032 1250 406855782 406855789
    0xc0409030201090f1a0c12191503030815010201110703110703021e01021e03090d02150a0207060f05041809060f110405010e09152218051501060f050702 67
    0x184030450700141ca03a44c112800380b400984895002c1c02c080074003c02400407590015800046480030b540d00c40c1c140e203090b1201c80c164002d10a6400409450741d96604900c5441440e10781d5603001540a5110f03c4068500f601101621a140448880c11640340c040810590000c3c03100352400c0344c2c0c03d45021040181820311042c41c190b8940c002940c420306400515403500031a41001004200c2a403d40300e0f001003048200f40c02c42108422120a6001400032541c00d0030411000720201c0d000400c401510036a80c5520400c56102c0e021000041c1c006240603c081c507040280c0c5181c45902c0e05e0002c0c41c280ca0401e0134141c0c0d11500d41c206012a84030304010045c1303c400d0700a50701e083d004000802c802c9050a00c0a2002c0e4054400c20380410001d617114141c5282c48400305e4407405114080c001400c94000400080303005800319032a801c180b80c001c00300f000354244500040b1200c40d00603c2c01090715070401615000000184401c2d2120710b40042c05a06e62000d0012a51041e07810041e0700e600151000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 406858282 1250 406857032 406857041
    0x8071d0a141305101103190b060a050301030c0b1306080a090501110c0c1507030e011101050103050606333411031b010c0206071e02040509010e0c0409030201 69
    0x440c807411105002d00080c4144945900b01c103034800e80468070070103d0b00c00520281c41180c044100300301001e000080c1049604403021b031070b059840303a000410000325030000d445c90b0007010900001800100c018410444074107581009007038140340550426041c41003c0201060f00c0c001c0e201006540004240c648569800c4007a60540c0b02000780b240034100d9002140c41d80100c10400301c0d51103411030f11035a03400c2101c040d1285000380c91005203092016101524909002042d850410170301e038800840e003403070070320a80b4042c510171130141015080c060b0800070405583c1d10303829140784456015403440b041229891080d00341c0310707a04035120b41c7c44c1e0081041c061717041343c0c42910400c003058610401c4000313480c2d034050003440354011002c004c3c15101030540d180030a9203c0881788a520f0341b0394000c2c0d8000c1901c011002d200800051910200341d4a140d0381d0180d0054040d41a00e800c0400c03011031909002c0d807903000310984020011080700c00415035540440032070040c000c50785d803031103502030500c02e401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 406859532 1250 406858282 406858301
    0x5070e0f1e22150f061203170c091504060e01050a05030a050907120506011a0f030c091f030c11062413052508130803060d15140108071d0a 61
    0x1e40b041c81440340c3e2031000107011001c0400311294501700010560b4414001190305143d0556207000c59080c40000c2c414641601800c450031031282808000c003166107810310440d11490038002c131500e441c60540d01601c014a12250070b4140101846000c180c642d001e410b89500c9225440085031988840d00f209040030810342000c514070501405c038406011000030f015049400c10742c0c0d181d040a9815150141a010b02e401c0c1c001442010008240b80f080d14030040d000141000708003070307080c601002150160600b04421200400d44035500000f40070740240140031060080409401185030001c10640036080070b140a041c1002c40036080103080e11101154010036512180811060400c907112614030071a03460341041c180c015082407010341d840344c14218083e800f00380d41900c548119035150365032a040203017195040300c0f003000c3c541c000c14208000844101c80e2030b41c5c0010201e0b9400104000b40105030400704240d8005030f070800012000b803800a29210b0407a4038103a143e22880280b40241113074a1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 406860782 1250 406859532 406859543
    0x60f0109180e1204030c1701021327151211030a030c0c06180b0702060c010c091701270c080d020304061d01020c041805070e0f1e22 58
    0x2203082040c507003154000b401c0504458203c44903c0300721552165144101d0000801e0200098802c11107a44820b0b0380308100d81d80e480015041203405a82c8080c200d0b40c81d4071580c00c1ca141d1a07044200300c03800d4040110903c1103c0c00034840d9001c0410100c00380c40441c4140c80b80c0469080d6000d080c1711014280c0c440c0740780000d051f21042d03025801d008081004009059034503030000c0070001080750050500000c1c49841c0641d16007500d103045603c91140d0080101030381c10400c10004a0500c100030311079540c0c1c080d07042c0c495803155824210701d002c0f80d981d0700b014070748980c1c0742000e10204103101090409030244207100105a2040e03514008021040a81c0050458841c401d041c0030b000f9004409803080d50f034940e40d048010199813000d64503003140081083e015810044980803141003076000078101865448101440c8040740ea039841c54049960310140341c4a03c044c0912074211402050640c01c11000c4200c01d090705010400402c0102e00540079920b014100e5045041001000941508503174229 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 406862032 1250 406860782 406860809
    0x402070b010b091503040308071b0203010504050d020705030a02030307060c03110309030405100503070e19150c02030f010b0306220c0905070f020111070602071502040f081c08060f0109 81
    0x8400e6145990040e04880d40309000304c0321050b01040940003628030481e0148d5400019450b070007003d8841c44c0d4400304010110050a03650005614240525409544200d00a10101c1c41440f00241006019080f4a200c3e070010308049003d40d030f0000584a03a10781040002450000c90308003540144080d01200d942080048104400690044090001c8070401c0ea003050040300c0c2c005040342d480c0300440d00d200c0450304626003c0c0f1142801140ca0f410041c0c405a41700480740c58881091945c01030902c01c07400205003600260031418180185070788014400c000740b007502c0381c03030340040e45803038004145440280c943d00315000301c030405044540d0999005039440801e00c0c0c07654071a134040c2c0800c58180000c01e54012580d440b8610510904001e800302c1c50040741048416514100031707520640081d140035028a038481d501d00c1462000f032000304016604e0900562510b408075041c002c25a42c40e0b4510340c400f403500c410036600030014561040f01140c040c0e005c0150440140c4601840c0d0b041404140e621 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 406863282 1250 406862032 406862039
    0xe0901180b091002040509010e1803130f1a03060d0c1509141009060c06270201020f030c070308160b04140c040902060f09010c0b0403021b09100b090402070b01 70
    0x8941c103103406202c00030300782c607110b01c10184550141d22807845400d4000003003d00411082d640e14000a401010425100aa00e501c07620700a10307641000e4003c43d00e840403800200000300c0950f0140e40105246898141c0c1800c1c3c40000c41c000780002030850380a80000911801007040065811b00940b003031b10420452000a02401448141e05002d1400c07040c0300035400b51583e260010700d07141c84601c00e948801089040030380c0dc50700401c44110444d01e0ad0780b10480725244000d4074907a002c0800c0f171315481c0e602900745030000918200741d03601180400c1d0001c010032030710090082895429a80c001c018a41d031080390800108203010618070140c8070081d804140400c1040f14410800c100c0c05000407030b02040e001404010841e266044003d50140c0100b0000750302081c3c1c41d000d800c20f420141803107541101262221a24040101c50480042c3c00c11000300340c0003100102c92541d104000d8501c400b1034078010300b54100180c0c4a00030031840c42c801040038a03203903a49070101d03880503030f001d01411040e595 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 406864532 1250 406863282 406863293
    0xa080406031b021c030b0409080309010c020d08040b06010807140a030603030906030b06030a2711010f080606090108090102130f0302030607050a14030c0409090305030703060e010501090e090118 85
    0x80e03922035480385031140007034980e000c1c3c0700081d0f13000d900360690f41491245200c12030035802840da0703044a6402503145c00d42c090105400d00040c40c818001d0f00300104844081c081e00a00b054945410305042c403401406000200f012340000541c48034003821301030466100c0302d03001c1c1d603c01e4500610640c54080010312600240d413540142044a01c0b83e184d0b4012283c407103005130142c901d80d2068580020382030000510807403054000c2c510180443d000c558819480121056034020101000d540150100700b242c9003d503440240440205c44070f18101d0300606102000400ea0b1040050301410002020080350b0143e0007035040710700c040070110484440544c5d840345400a0620b40c0310a81c42030161030001041c4034056021034031000880e82e03c001004d829005008030507040035141e2031003c8018000440c01d900d40e8820600c0540c025124140c80e4a880100181500c105400805075000d0a00040045982254140c01550362841140d02c150b40c540d03a078507004001c0b0b850104040380c01005500103106 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 406865782 1250 406864532 406864541
    0x7050c0906150913020903030a2007260f060106020f010f020424090b0f0301080c2e02010b090408071202010204080c06031f0b0d060509150f030a08040603 68
    0x440545520300309545820811040035100b80031001030b6041007104803014a030440c01500c080101000042c1454810b0010a2542d00404541808a405580340040c440c20074101e189091a040300107000c07003410071480400d11514524505440a41c4c0c0c80c59402c3e0001c20f0186103000c01462040365141d40c0d46910003903841d0303000c00b03110010f54a02010341030044854000c460a54045207000050b201e003820303001d17501d185200c4540c4200f10004201042e0030342000020b1110403055456a5180d50400c0d120604140c0803408044c03145080b4180000e051007808081f2243d400045805d880b103180642080e070160400022080d0b00503005000c02c010854064003410103e40100c0c0003400c66007140701c00342e00701d1146019104103a8004490080540741c11001582c1c030154100d000e41d05128102418070a420968000032031659000c60001e140c40e0384c4d48039842c01040104d85c8081b0038200000b40c040620302a62a86008003500c0c168010706881c1000440c94542d8000446551650388a40050091 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 406867032 1250 406865782 406865803
    0x2030726012c03070c0510110102030702010504020a05060910081801021902010c0801181104050d0614060a06050d02071a040b070807090b0d0b0a0f14030c0a0305070e0603010f020705 80
    0x2070070ba10b841da000d940000803d030f581d0980d020f509076481d14184001c00480003c91076240003081011501104074070401c2c00035502401041d00003188904282c0304100380c0e120070781c0085000300028050398580d903454610b000301e49092810180d035542c452102e10b0007840d4404e106204958000100c0724030760414030714481e0400b82c141e8001c10050244000c00c0740c500d2001e1040415107110f800c80040450540d80c015400c24002c00e0b0a00e00c2c05696002103400b40210060a8414039600d409019000410341c00469106004580c80e11455017481e0015005015110ba82d407101680461b0405c10403542c0000304010072203070b400c08001c0e440d041c03a2000744c1714021200c160004400f8404503841d03601a60082c0c0540c0c2a03c94880d041869920501d00200380d06400650722074145203000030401c410740403001c01341504071b28403e03620100700e00341864036001d6030099000e89282d0340104042200883d401098032511403c0e0304d4141c0b10300e40020b000d404401c2c000c1480910000388141002170000d000103a5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 406868282 1250 406867032 406867091
    0xb04060f090518060c130e01080a0c0b03060d06150509190606030501031104050601020a2a0807050604030b13020619020613020f36061207030203072601 67
    0x1a5a40f4407240d00b21460715008003220340c4000c0228210307141e030a010b400741c4601c00314140d011a0360340b42c40000701542a40486015003104150704240800e29002001410090415501e141800c1c40881c20300750302081c01900362a42d4440d88800721941040010040500500c042042c8c01c0017070f046c4a40c01d00c03102c1c03529070f91803818100182150003400303620f040329040715031441c6980c41c401c18040540401441c02e81140604182e501c0001d038580d62941c6400c40701031180c1641c8000c2c0401210914903904910b801e54070040c1e04000958545044a0950f940110f0b205802d49903603240300e10684205000a50200002c55180c002a02d50780c1020300c0d005030380e421140c86071252801503c0c01d1810641c0a500300111f8800c204250410881c41c64050320903552030401c80e41c10340000c4c2080d030902c00880403a80100400e215946c1341c5407540750309254040d4003610502d45075500082d5544503622800c040861419440810000034501107607044c11000000e01402c200188190900410b282003c00d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 406869532 1250 406868282 406868291
    0x3060109080706080103060207050a17030a0c0801050609010c0311070801020a2c0603060a0b031306050c0f030f070c120909060906030203030d020f0c1903140a0806010c0203010b04060f09 82
    0x840c504001074180031070f50f594403502c00307613400c40d12148080d5210820a4800348507030200e1100141702113000000000300211465241d0600a501340f082d9098104c01d5006c20650a005119980e216401c80e5030391442400c0c601403c50300d901d020703100960a518142440d000345000000c2e85ea8042d001803a08c0c16007a95904000e801008500100140888903c10018072806884281e07003883c400650700030300c00030094050151313190f5840c50300c3d501c11540140301c23641c0702405000704a040d012306500000c14406c3c250510160150143d0a400010016595055600003180c415070007111044055900607071031302c0b51100340380d1000d0103161483c881e024800d0325050300001c846110344075150540760700501071440c0c400e0310240c100c0070707422a5000b903e0801003003142c02e0011508101080c90130902040aa01c000aa82005000780288020650301d0000c200f1146d204a070b4400784166105109007001aa40c48142c0042030040210340101604146000000700c2c10626400041c1c0803200020010300c0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 406870782 1250 406869532 406869539
    0x801020915251a012301030c0e040903051201080a050d052208030703020708031828080604060c02030307080109090c150306300215070b010306020a0807020d0f110f010204090203060109 81
    0x8010350101200c440c80d07090540500421b42c4203410041c0310780403a103425224008032000040450791510320480101d440091400030603034508e401d040c01040c44c94007030101510951169a00c3c3e0301540450810001c002492040310000404440b10350207140c1d2805140e1611801c0c819542d070b02401c1c055000d4480c4c004009900100007040714100e1050000780c80c0c40151000521050b0300b0300c2e00d6051050a04903c01e04000041810400300400c01c100c000c041c0b500746818140100c0343e031046090300f1508108200400950402c1743d81d0304581040c80001041072640c00c02c40000c0e01503030044803070001001c0780c0590480d0301d6007109050395040d041c0c1c41c4001c21901440b03160403458002c03501640d02040c15a2015150980c014803c070317001540c10900e08001a0b0318032141c805d00341c200700c800c01c0e4003050130441154031510407070744034a0500050289214442026212420200006d4208050039204d01c0111209001c10302c5400d004400075500c03140c4540100010b50030840349940003841e81c49001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 406872032 1250 406870782 406870799
    0x50901021525030b1903030f1403011401020307050d081017060114030709090501021306031a09180a112e03020702061b0706090801020915251a01 64
    0x42c050a0310610032038019010555080725000040440000d042d5607120400d41611401e4403080341c1440f01d400303d0a001d0542c0b4000d0030b040650f1300940c0030007e0346070310320310055035410840b0b042d103046c4038544508074a8500102c0c590300c12148020600e000c0c140c04540d43c140c100401502810b103039400c842c1040d44500d0034803403019036125102c4096110100410900420070140b01c2c050030042c0a80c3c040546802c00303041541c1c68280101d85907980010454480d1072801040c0014008030316050200c030801485a441000380070200034880d009d008007240d407060b4080080307180c00400905440b200305150070300380c4a90034a5113049005410108812040302c0d604c0308109051204803100a4000032462300840003500080c8080741c120b6020002c407001615840445002068248010002d50b4105a402082c03c0e41961015000d80c2c010700c200f80d2660364421411a520424860341611b0360b00c58101c0000100540010580b50a43d0707440d1001800303125a000c0400d208101c490780030999803000320 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 406873282 1250 406872032 406872073
    0x40506070302090d06021b03040806010311040603080a110118140607030c0207030b0c0d0e01050a1a0609010e0d12120b06030103020a03020d0c0803041205071406040e09010212010605090102 83
    0x700e6600054000405000503a0343d400342101005e11821407c00604403400c00d8a10b80c45608222091707400800108200b20148240f484281e205a030306000180c919601c0d40070034041c42606a0a1241951110113604030035840200c0c1661440c0c15400e4070102810007004181034090000c00ca401100006061a4024042c0051000071035001304051840d5484505584001400c10035002d24200035132440c04102e0301518441c003903000c00004203420070f40c0c840b00c12182e4000c0c0d418422481c50342526260758a00c000e541300c0e002e00303080909015000308006140800340315030041c0100040400700400d2503001ea0760012031040d200c805c004901e043c6d003c120050209206c0254001c2031500141300500b1324940307040303640b84250b403980d00080d02c507240d1500350b0b00301e078110b41070300c980c480081420b0000810066008055041d05040b036644c0c1ca1012550f10b1055016a110b4801c084002c80e142500950440d0341d084c0c1c1d0b12024a0341561515402001c5500501c50140180700702440a601a42a50b14 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 406874532 1250 406873282 406873297
    0x3060f080d1722080301170d02070614091203090102190f170c0a031112120a0510030618022803060506010c1a010e18071e051008040506070302 63
    0x40e0284201214070442c400c40c60000c011000c02c00e110301a02a003221590181e2503110721880d5500c0d1a503040900d07075505140031500c41081640425260b428031038010804400341d41ea81d1600442c10b12400081600a110340d010f25500607100c40005a08600040b010304810503007603080d5654107580a4041880e1040340b40040e00c4100341400142c0040c0c207400104280c4004040740d00c1c1080c0c0c201c0442070400010501c11750105003000000080008244021141000410f82c99070034aa12001203680742c0030001d1003022401e55031804a070000c00400d12880c011a0302c1902400b0a1040c0300002c40000c8a03124204d0180780000b0041c0105110001c000350210006150f07019140e140d0740340e6801500e800347c2307210305201e0000801c034003289000ba090b0221440c801541501c0307514228010030080e2000b0003221a0700048112040b02d00008204041201c4000342569000008409000311503501350b03000a0b0301124480102081e96000030000c0d22032400340c1d003500d103541d840110540c207030300c503603036 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 406875782 1250 406874532 406874537
    0x304051c0906051909090212010e0601050a020318121204050112270c0503010c0c0b0c03010302100c020a0e0a090c050306090a02011101060807080a0b011a0a051b060703060f080d 78
    0x4c400e94040c0894001c40c1c2e032040c1485c2485140da03860344010120307441200245446d5440c980180090003a0030101d40d0001c3d07003882e005107404240b1030003d45a001e02d508010394407400d0500361030315a03102840d2644a842c5241600c0034210400c000307503510380c0140304460124080c2200c010305042035100d00100c24444400078004d018a0f06040300c15030324454400c1351494524a000b0034140c0707003413007103c0380350080e0b45510641c0d039114104680120802840700030012010401440140c6403030140c00da900d001401c140490242901c00210100900d40112076001111000c105070880d20340c01407035515002d22014004141c40c3c83c01d0513201c4808032080030042d0f10142024006510910441e03411603102320000601135290900f45050589541c000d030031030740c000030301c038814000d0b034082c280e004058540c0591a111351a0924408500a903104400bc0c01800b048034480c8600d010141104841c1850aa035440c1c80d108070040c008003840e0140f0710142101034000320b101c40c8009994564048641c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 406877032 1250 406875782 406875787
    0x12051302010f05090301110a0c020a0902071101050a05071e0b07020d0e10020a05191704030b07030209010c0f0507080d021b1909050106030902100509010c060c090b0304051c090605 79
    0x2e03035058801c1e6221101050b0199030300c0c40340c0c88004040740c003d00100388095551440d280e0340e500401c004150203822002c0b50038810040040058801d0381d07180c011071001e00344a81c40b02c0310008141c6041c00703001c030050b088508500501105031000c400345a2401d04c107000114244d141c040c1300b00d96a041454920000c15900d141203825441c0c14903000c1c555140700d1048904445071035036000e090160f401450140540c41085030b1003000020503103d010308c58a05500781c10a0300e103881e1038210780c202400f260181a8001380207920742e4070601040d02915000b180c5264408168a0325a070344001c18400d8081502a4804102c1341c40e101051103c030760382c10030400301c002d84105000c1110074103819181404124404030009101c000d28002d09000380400c1e02c0001e03040341c1b54014041c0f0012844204d00801c10100070700d101e507a0300f0180080d10550481c0d80050403001c2e488047e1440002504203d0300c500c40401000204800000d0907000d4411800300c8450301410041c0549455129003d16804240103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 406878282 1250 406877032 406877057
    0x15080f0d110726060c18010305040c120c14010e180606040e090c0f0907081306020903030f13050904083a0207030809061003021903050105071205130201 67
    0x690844012001004180e80740302d40d40791240d40303240f12400310030116002092226400243c06110141d48405448030080c40c1003031140c5040c200001d20355500781495076400108042c40760854402000d81445443c003605035146041c02061210b840c8503521459450050030291944140c03040f040d004006080d9414900d40450820f0840900030000340d00b00c03009001c00900010700170710142c001c1034200042d000070318088050084400311090f0060007002a40107211145a00c190380d50b43c0250140c0d82059410030600d0400d01030f1196241c01caa1620021444040000a50004106000c4891081d40c401c0c1d54890600002c00011034002d8810281841852030790344081c45c205078900f091088114400ca0703520070518007a090000303e1124140d022641c0403c140d0451508ad0b00041c51900400301841d0000c0d48030902c1c600c5000c001d018181c3c406a003500c010320701c0c2240300a513600c44000c2c000d034902104018465a01d003604403001c5810f00001c2062610716030285038403190180c0d500b02c40b2110 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 406879532 1250 406878282 406878287
    0x30f230a15030f1502300114010309050f0610140a080d051b0a0b0604051e0a0209060c060f1023010c0f0f03110d0207080c040902010513030615080f0d 66
    0x1000c09031051400600d10381a1907030780740700030821415120042000b00c0c1c9080410404d00114083c0d00100c444450f005010088c0c0310700c03017400b036681d007481c0208242c0c086180c56410920320035251001481500709101c6c3c08000c101e00c050079601c04d50381688001070101708011100f20148584203c40d0050600030b61254460300090001b5176881c041d030301c1c0c1c03041180c0a01c1c0ca8180c008a081d02c118000d00140100ba15082c090a5000030454901e00200060140c101780b641401501502c2c08540c00103010004e0f840e050300381c5086815500c25181145400c1482c4816420100e0b400c04041000c11408280e10002001002d101c10354021a00c01c1540200015151902d0f03440c0c0c103440300c1c410000c00c880000c40302108481c4075440b9030b8508040328002c800e5580f5000c1c042600e4410f540048405100c0308400169080034840116404648006c150005035507030711414a1042c001d0400d60320100a000e895000b03404804113240d00404034680d10302ea56512095140746004540d04070300c024200c20751 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 406880782 1250 406879532 406879553
    0x1515080d09150f050c100614040203100e0901090b10140d0f0618120f08150306040b100812130e0708150f0607110a0608040c03030f030f230a1503 64
    0xe130038450302e400000060344d46402c40d4440e80020130380d12068240003052031a004503c849000365019411070422000c0c0030004e43c1e66000d403215003c84500002c1d1008001d41202c071240d504402040400c3c02d1691240021084078041c0c0c22000000d40b0290398681881b4054064582e08450120780300351145d5100c0c0c2c040c0040c0c0704950b00c40780f900c003243c4001c00e40d2105416a002c02507110750442e035003000c1000e804054001e100c603060311218003001e602600c011903401e50040d40b103000240c03d9034a160044d0748881c4143c1040780c06215400d24080c9041150005201d54030041ca480c0c80c81c1640c800c01040b1035807003182d200c00020743c0780020031007122880c11207003a90315000717102d04a064600400b00e001600210801d1b251141d080385001080d0510322403040c060700452502014a240c00c1e00da00740c1032000b0788002010451600d0b10070f4102ea05c2a03000404a850263302072000240084080074601200c01500c921640200040380003114103220f04c141a825010b200040c142c81d40d1541c10102 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 406882032 1250 406880782 406880807
    0x1080103080f0d0906230a020901021203090717070315021303030c11100302040f1403120c010e030a05040303030b03062505071505040b09011e091515080d0915 70
    0xe680702c04c003100001e039450240c81518901403080390101005c4a000c003007131a1000d80140481071041126001c1e5076400304410441000303180307110741d072512482611031408856030702c03600c486050030800e00c10540c40417a6800c11240a00001c803103c0b120720b50628100e1180e850008482d002c040d40410000e40201c591422072400707144450608102e07180440c603800c10312180b40001a900180603c0710501c10081a009490b04400c140806100f0b080407d035107129070048554180c0c4042890008000e00b500300c1040d11109401b96a00c0350082c21000c5d01c40d03000380c0004c40101c0e0510b40200952b090004500e0b10513012054501601c0803c1c28004240b00360201800b810060100701990110300300882c00403101034000342c006a83d280a0800d50243c41c4041d2100c146a414030000c4065801104e90a120503440c400c0009411390031440c108803000044201d2524050400c0002d201814845120760200c50341d100a64070000d40d5070f00121001407082c0990f428119a000c8070880c502e1140300440b00c134 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 406883282 1250 406882032 406882057
    0x1103190c0816170a020c01061e0306020f040801060312200705060a1b12090e041502090f090a05010905010f03150209060903031314040b221d06040b0601080103080f 72
    0x180c804480003d9244903084840c03c1d0041d400040b1000070010900c0b880000b4000000081d010560141031049540307118071014200c00c3e00407030216009000a4215802460514001c000c1191759180034540100b1081c176003c045a001c7c00f1a0807581d00d005007141102c4000e10207810300c0d43c00c010803c003045d0000458641008a2040000d4200021901c50603410340900c1b840304c408484070070020400030503030b0000c44030500c0751400d0100041444505a91240000d040907131234000440106050f40800405a80d1000a1000740700001000744e100e14140d4204c09000e11050383c940c1d07032502c03088010740f00040200721030009148240245501400c60354000601c6a460105e200000078039507004514246454980303c0d404014a03803030706480d142d19140c1682e0a104002800c0c00103102036101c1010000c0d405001c00407a0515880c070350180004403038410030841c00c03000c004e42895542c00116022904190500f01094466028000c050704a941c443c060501c1c080c1e581e03900030903d802286e0a00740 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 406884532 1250 406883282 406883297
    0xd030e190914011505041818020d08030f06090106020c0409020409080c06090c030c1503060d15090209011a1e041d06040b1014090d02041103190c0816 66
    0x140c4481038010300d4440c1540d24000300c0b440d4101242407060580c040c40c0740050001c1000100407071032810742c3c807030300324140da800002d00004100900142200400c01c025800f41c090241041000807100186008541150078410a42c2d02d480501060b00000e0040d0300c0980c0c441c0c0da90440c1c40c5402d400212f03856101903c040354040765039a40c014135804c000c1c1e200c001a00244100160242c08012003034524004800508004c440749001c40d03c55025002c1d030300020400000051059140c03010062002c5500030007007214160528110802440740341005c03031154110400000381c81c030a038510354010004c0e0240807440c00d0484400104201c035440914a0345030350611001030000030204030342c1c1d0f52407141d103502c42ea140360681c208400c40e800d8140044c810300400750080c0b04168070114820f440340041024550b03031400440006c0c0c11035030005000707600c1030819030200300420040c0007841c09035001c070804d50a503070400e14050041e80d00c10507443d000542d0031030000c0c000c148501003034030300c4c0c0300c1c00d0a0940 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 406885782 1250 406884532 406884539
    0x12140612010e03160519022d090403050904061d0a0c0903050f010501140d050a03110705130207050c2e1413060f1d0607080c070608060a050d030e19 65
    0x28215081074101c16040751341c20070b030f06081c400144040010050b0f4800d54600403070517940021124400d41c13141c81d80c40b05201900381c03440c61880794102001880246201d0341880e15180003009507000810840c0150704180340041e8140c402014954046440b29001c0d0711950303112015401041c40107110b00810640c10800000300f003041c024404044050300c0003103025070400560aa651300e03007400c500d018103140c003842d0002c100c000c10180c0b98154145007550000290040307040c6060768540000d40c0c000301041880780c0c40c0280340e00500b100c2e4410800d440403030300f44c8003c10021a01d5602c802c40503202d8506503201045048442416200c0203042000568803214444c80351900b000074011500d00440358240112070704145031124084c501e14100019001b1031040c0c0c440f802d42c42000902840000c00c400d020820f0344001d80b0000300384181186d405607a038000c000d20b1900b05803001d6009146540c0040f0352801e01c507501c01e00386505621040904d80501c014803134491800d41815410b02c3c407600740031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 406887032 1250 406885782 406885811
    0x40620040b0906071205030a060b04141e15130b0c03071205040e090105040212032110030501021c050a0c1e0309060614010e0301020403020109030201300203071214061201 75
    0x11100521a940d03802c2d02c030300d0700207208c0c022a402508080d5048038240420025521026171060385060240d902c050104040d5003503070190000b01009503441844040c100c00100d2005002e4008448a1142400c40d01d0b641d5811180510440c0d03a4542039410820041010885001d840305040e0198a095460555292514000008103903a0b054031a5110001c0c441903180c070603c000381d45141407026525220440504030010505481c1941412464500042c19455143d81c0c400c029600b1800a40d80c4018490002800d806800194520903141c08007107040c050061040c071400042649a054203144c0c00c01c14580c001d003c04280b00d042540341c08060740025001c1c0607001c000c00d0341d00118501c0076803620000d03045206c0c92088a0190b8414842040581e03440f01c81c0303108594081c205100c00742c50705103807039103901c1e0307950b112070322240d020000e0420042465009604c101015616500c0b8220740080000c296003414840c450b845000d200458403e20f0681481940c500715100002140c10f03462650 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 406888282 1250 406887032 406887053
    0x1201020a0309030e0901050306061e030d0522061e09051c03090803210603100903090602010b040b060f090616050a0c0605180405060a08010912110a031211040905040b040620040b090607 81
    0x90000583b0202d0031010341c60358104410801001712030b80e035018905100004207030890040100d80c028086d0b40ba600071076802481200054240503003032020640042c41c03c100065a40841240011403c550005203604003200307450040200600f200d10021054007651013003a00581603503803500132000c507110318801038443d0301c103070500c251183c0c0d06c2146480e00c041d003112501d24107140141d0500f000854144e8034042100c2e4000c0071800c02584403070114021403100e01400c01900c01d1001c0030100b83c000d0200004000b50328500c5504a80c40f12910340700220b540c1d00501112032249206580c50410b21714140d00440c1d03011300e0203040c912040313607501d028030300b5200305420540c1d40b0031000407120003680c0d01c6040c00401c07004100c01010121071a42c1c0c020300442c030b41c03c6d55800940d6074048030074484081c401100c0040241d80c106000a0030700d4202f81c0091031060328101c1e030716071400030301c3d0340d800c810408410741c0c0005503007525080030f1500e0070003007443d84039900c0f183d44030100708501c0001960010f04c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 406889532 1250 406888282 406888303
    0x1106070c141c03050c0c0a060f061a090f0616020409020f0604060905030105060a06020d0c0c05090f16180b03061f09030c0e04080a0e1201020a0309030e0901050306061e03 75
    0x4000c2c00010042d480a41150380162007440c0403101003104450b00580004c18420080d4003000c002400100c10265000500480d0010300c1e446512942c40c5030b424414402401019200321403680304015040100661131003240c0c04801040001000e41c405480c2540c070400d0118000b5059005020844c40052425409500f0601c04250b0301d82040c499411b0902c240c0b6400801030b142248140e0030417501940d034065410030380b4108614540c07903400700720328860303403000a10f00507103c2000b50510800c0501004401c0320b01089640561549030606032043d045803000c180c46804011140b401d0a100f01a08da00007084241c01c1012444000c0c200e000d016000480099990345810300da03811494005c81e82e80c226403010704400041014070020840d010b0807141e159000c1d04121046441d03440114941c280d90951407034181d403010845440850701500034250103403095482070850544c1e8010842840310a00801340c05a010100240e914285121030740304603045c0829140709900d000002a00d401216031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 406890782 1250 406889532 406889563
    0xc0f10021018050105130b0f1003060204090209040f062303010902030709050912070804051e0d050102030a0e0a110904050a050a05070f060806010c0303020d0e03070c0e071106070c14 80
    0x140302c0c00a009003881071a411005044d40d1054400c0140c03554040c00102510070544203035560049162104400803010096074048419034440e039807526900000d41140201901580c2817850045400c030707180c40b5850540c0c0d01000500c05108031038021315103c9407584d03202905590386881180c0503030750070046000109805c00300400d051812070402414800c480c102c0d000a00c86c00e201913000601075030103990035503800b40c4080a06840b80c40301d1402d0300c0411100241c00c10f14441c130030410b00c00e040d001188038481500c3d00307014007033020b5561551403151000141c07146006003007500c2c2c50300c2c1c806020b0f0f411a02840c00c483d2021000c2c0ca586080521134501151140d02c0604100304c5240c0440d2414010034050a10a10a00d081c50019022907441c003002000c050303000441a9401d90194000747c1946440700c21a900c582c4d10b490301038a5414140205034580d0384201c0040c4020780700d0034410400c80c903444040c00840d140d0081c280c030300d01d2850400700c64001507665424080107041221418088605 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 406892032 1250 406890782 406890821
    0x161d1c0506010501140313021e192c0105090a110406080703050601030204081507111e0c09041502030a0605061602011d0120030c010501030302031b0c0f100210 70
    0x10005411210994001740c5000c03001d10400111000086a100090f60140c0e440f4521004e5200c0d40300c050301411703036041d6002ca003003801c0d4080b05040c074881d6016601e00440f030b0a082d41100c1303516282505480f844404080d10b01c00184100d041804070203400c01c8110078041950701c04c0c90b6420071350b600903402001c0051041c20412041c16454002c46402020a003000c51038503041410442c1c54800024a05000c066014007254840b40303d0036011410b0145c010544030340c400490305079144510782801a0380184038111802d0024a0034542c42c0340980c3d800300141d1140c810ba00c521101a410003490b602d0300d150303110700000710707601c2d0300303000b0300d1115a850f00d50075001d4814030000d0500303265009d0042104a04400c0810300d40d8001c02030900100c00504400c0ba04246030b0000c1d461440f032006680155401d00f0000400c25800002038a63b0b040c501c8440c07480d5070350303d481055840e01c4aa00403640029020803207070103030400c520310400e030000303e1042e11060942c0c0c261540c2503980030ac040d04118100d8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 406893282 1250 406892032 406892039
    0x20c030f2101060504030807020f03120c01061701110306100203070605040c1811032e06210b06040303050a050c15180c030303041b031703070305161d1c050601 70
    0x54030012800350900e0704100d8217150442e01c58420ba070040b400000d026682d2904000782e990380800003085009144d80400b542e40340e43c2d41c0c50741e0180c00310384140035003031039030f030682c1d005c1010706001d00c0c4280c440e046566800d5540d0782c41040b81403100d03080b10f042035010400c60795010071407a0140d14402d034050f44801210500c0c0c580320f500540c403a0341d055035400d482d21107002107850074002100d8001ea00c450180c060a502c41c034015821410041c9007030001c0042c028001b80b0207400c00030300c100451024841160302c21041150340305640e824181641c0c00041000305000290141d005064132015500e40a818107100c0b00c0040c3c50108d0710462000f92a00303080c2040500603030740071841c101c984150040d01c501103140c8082a640d0001510081090000035508000fa94070002420011508850b003c1c140505500303074116075030b00a80d07441002030f0401c8001003100020002d115036001d8181d540780200105c0b504200c221101c1c00e00441c4d8040c60307041c40c03010780781d1a041c01024800c0c021070207072086514 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 406894532 1250 406893282 406893337
    0x90f150c16060e01020606011d090a050115050a0e1504171e0d1d18070507020f09091f1803020106050307080601060912030314040305031506090310020c030f 69
    0x1d040e03104604108040000c0c007840e981c0403500540003582170900c2d006092581d4441c225803d082e503003190304003081800b084121440350700082d040340c1c0303801000505680050800c84491241000f9000410021681c680c1281002d40c600c03404250205190350415031030346181d00d0014900411f404107580190303401070540b40d200b004130751010080030081001c140440c601030041820003644000848441d40e21100c2d50704d9007659000440f24021180380c0a01e0118400760480d000b081041c0d0080103030481c14030703150410002d1035015544810003000004120742521112071102d40352001115100c485881c2e00318028500045018401e400202d5114146410f01d03141115503400b5001036440b4200412105400225603c181d80350300180316681401400c0a501500300a600100b0345560310003000f0505512102560198442c1250350024000031800c014550103514030460341600554840c0c105559280d004103100c00ba0700f01620705024002550362415004603a41c4c40000d070054140411400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 406895782 1250 406894532 406894573
    0x3040303090b2401050702120304030b010e010b07020a1401030f110a03050901061a0c0f070e0f06040e1009050f070906031509111522080c0312090f150c 67
    0x11081054280000c400f81e803800032942e40d00c1d05080c107000300000c5000554032100b40c146d1102d2040e20850307a43d140c2d42d1600c026800780c00d210f0300d43c009680310b00100d188018441100c2d0205c1e00103048440d01401c0c440384590350f003a0411802e0505a644004004d80000b81c005d4565030002c05214640300c1441050107015600000d114410691404500744020070703800206d80d4449100a907150f072a5401052040d2800c2801b20142d0300301d1080304c400046407074843c528244106102c280c000102c0c1c4540d4188402d880c504680e4580c1604030a2103001d01069070f030b1041c200c0c18050400c40c1e1894001d0741c55241030140319041840c21035220141841800034144842a0b41e910042c0104040d801c80d40314188000443c64610303128070f03c00700301a0780095603803058070304031003007520042c040d41c00c800c07100c9103219594030a4100c40d005d00b51030200c40707280c04504612076083c03840d07005281c4000007080042c000302070b0101d950300ca403a20401089106003038000d050010f07400e1000300314601c00c5040300c2e6085d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 406897032 1250 406895782 406895791
    0x6040c020705100e030a0c0b192309180f0405010e06010f030215090301050907150c08070803040804180608070509071d01200703061d072903040303090b 67
    0x103501c40c4004100c00e0f02e98000b00881040d6034a0320440140240000034200b62000d68042d00e650308401000c6410380c1c103100100744403501810196460a45024141c9001c0e036010308844940c0c0d07030180000b07410741d07140c0d00070001020010280340c103030741041d502c0240b80e0005451034031401002c0c4003044104030382403040f8581403408000a21166240c05802c541649484c0002805401c020421603503119010054030ba826000500900c80c0e480e000ca4400c3d40d9501610480700b101d0140460103c0c018007404803442d0341d907080700c075203442c001d00b948072082c50350700180c02250420320401c00041c480d14a400e19000200c0d1201c40802c802e840e16112a14007a816040f079803140e1b1300e40c020b210314160401e020820403040c240d08500300140110060300c54820510881c0c9441002c0c2d903106880300d00c04242201524800c4804020a1726480d92444c0859000713410905141c0c0641c20911149030040202100c0d080d0003408058040d204400703030040c0d80c00a8408402107a12004c8034010000d40481141d4003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 406898282 1250 406897032 406897037
    0x40305010f050a0e0303181009030f0f0305010b0f070c0308160c0e010b0720130212010b03010b12041e12030f0b01050d0903050403050708031314180c09090f06040c 72
    0x30b15054010117880748009050040d8501c1d00700481d40a15605011840011042c900701f000f404919041c0509807940785a207540000d41030500910310346000e403103010b041c2d6501841050400c03a103a00750743d643c0c3c1d10120040e2640c8270784420000024448070b0007000800010303400040e90b403a4600e0301c12084145038006144100c0002c006100090a141c1980c1c1915044034a000c414100403d00f080c440c5211024203800800d901020303216401950010843c45440381840c844583e81c4010440da240820702540000e0601041898000b510141c1e6494005000d200d11f1b403d40c0303020f180c01c1403000c071262000701c0e01d40140e8141c01a00d40d41605c2000940d0300b0b902c0c424004000b0701800201288034002c1c40d5180156188065414148a44140c1e0040c2da448000c40d80125100d03c10665650044040e9201035a0280d4002c203c0700729400d40ca0740f403004090400c103e01c1000703118405100c00000e0500c03004002c00c0c00142d0681c2c0e01c801d01c0900580000488641508100302070209950420f0444420f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 406899532 1250 406898282 406898291
    0x1202070302010f0f020309130b03011a0f03061902073008070203030402092205061f0503070b0a0f030216060c030c03110f0912060702010b011701030b07080606040902040305010f050a 80
    0x4c413940200c200e41007910115150b1046040800c1400000c0c840714500a405601c0c06482c074080c5400c4840c40c50f00c01c40229040c000b10b90048040642c1c9800883d400d12106144941801d001300a80d000313008003c1c4105c1c41c0301c0d200400528404030700e071101995440ca515100c003698104680050b14a81c000c54944091440d504d4582c0100e40d0040c03002e0501014403a8409a00000c491404903002c804c1b5030290030f60f40107090803201c83c07a14080941010342e0202000400042d40d10f0001500c00c00c0310310090400c0e05001407680b0980b0340b2200c0707503640002d05408003c01c1080800b0485108011071081c00000f8414818002c0102180d0403020643c041c1032810070214100c4c034809040e141568030f404051655030365142c01086ea0b504490350039029502c26141800030050701074100354507201083e83c4c0d0603034002030a810701c9200a400e100103480481d1540124248511900c0c00750781c84100034100c146401d503200c03041c1041764455403040d10700d65522410311290700c0d40d034040d041d04090000c00500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 406900782 1250 406899532 406899557
    0x100306060902121801020c01110304060506090402011e090b190807020105150f04090b0c0403140607090e1b0a02210f0406050a09050d0305040302040f050f130c031202070302010f 78
    0x188545004c2c01a030007082424002c50b441c072a00b50101c4428043e0b860003403164410303c09412149800c1900c0446420782420005900c0381003084003144a41d405075540c140c2500c0324003030300c2030300d54a880c0c0460820000791030203d424903240e001030202c201c0c16110300a29110000d4000c0152001418110440e4140010b000e43e030340101c84150004c120417911342016001c000000b0f00141840c0c80b0060044841c58100b15621140b080900112800382503101c54074101400348585a440c111030720808a82640d10a00408410900d91a03004602614040482c00001280f03101c94100c1c04480c40144d110220410a5950340c3d107415000c94285001e284c10440c0c0480c80c0c20180c02680070705c00402102041204c2e02d54407645a1000401c0054103071819074040b424010069802400b00381e0090b41041c02005030401144a124480c144221515030262202c40415285101c94507080e2500303584248040f01254038030710820301e4408140c008040003851880050004002c1e03851072002c0c44699503120 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 406902032 1250 406900782 406900807
    0x90a0c090501120f15061101060605030a0209121b030d1107360504060501060507050a080a180e09070e010812070609080c0a030909090201050706150e100306060902 72
    0x400d44409081a0070501c3c44404070038002d1129121190b2440d05100a42d404142c1e084005010b0310a603944003420210201045800c4c2e9410b445010300044003000018003c8945501a0600c0000203150710103091419903514a088000045180070700703003011094540b80303020094410481e9540c20580b9144c006500025200c3c290b40c03207402840741c0d030000d400d42c21145c00c0c180c0d2420b43c80e040c1c2c250349051a00070a04001010111411101907150000110303185014030140c44140c2d038004014102d245d40c1740d689004903002000c1117802c1c450a000202510020b403024800036007000c1d41800006d03d0170383c00d11450072140e07a1001c210300d03801230010701c0b411138081240d071441e80c04040702556410f03070380c64102e004100d1142d014042c00e0000c20405040b040224a9680d070b60300907512203020684600b80380701103882c8403600a001c1441000510005840c1c0d07080200190302005080207856a280e460303081c8110116031426404003a110306008000c0c070b620400c800b518206400f1805d014104846 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 406903282 1250 406902032 406902047
    0xb041a090603010b090a0c020a020d0303090308060f0d03141312061d19030212040303180b130e0c0c030c0604061404020a03260f1c0c050906070c0f14090a0c 69
    0x903500306d03070711501c130503001a00070048207288030b5019003103122061003820001d0003005441c3d000c4000503441c4010803803500d0100c0181e0742101d0020500020000580c0e001d503440722005410400c0d0302020301600c2d08413404014248000c10300304101311003071f040b0b600e044000c481c2c160f0701c036800303000070420780741c084c4400043c0c2c021402c0355172045042d62280c20b00307003a40b03001c2018105ca029224005000300405610806680000500969a41d102619980f0342d42c4c0b28004c0e0030803000040c101000c10082c011000c0402d9030480c01000e03846140c04a0081010b003580d2081418801940c0000103202c2040460322079003403103490490441034907091960000b041949079201c0035001c544d5544002c3d0320a040c59004103c40014981c0c1c06698960307408400b0140c0d006100744640c4009140340e002030f2002c1070301a03500a11419030b1114a45800403040214035080a8070a841d0707a0080384c008103818012680240240549400c40c003070003030300001080008103008201440c52030815003042c5403550010328 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 406904532 1250 406903282 406903291
    0xc0b0430210309050604031e0801050306071d04020703090807140312030601170a0501050109090e0616170a020304060b040e070302040f091a0601030c05030c040306020d0b041a090603010b09 83
    0x401c40084540820450180c400c202010700b0718011305c4288010180c10480d200c84c0c015201505600426510f902522048400d2041d15050707042400000d201c1c51040d8520722200105451086c500007000740800d003243c00009045010400c03d040c24040700f0800c0043c0001001c80c008803c00c1145100c002c06d0725480d442c050312441a10100c0411681e070300031400400d100018912001103032030408070280181c0002e21030140072a400220100711422240103030341440b824140201040d4464500301000008110800c03410480940e900c034401c482c204001c64060401000f0160326802c1a044c620f04079501001400d110324074010105401c240c0c0030135075408a0750100c0b0001520f00b1941d024130003400300d44400400346134032a00c1d485e560044428050303004003000c0c7e0342005074035018407081e03450384000c0e150440c0000c01804200005030150300104031b40c6030303040008148400c150001c102030b140e0702c0c000710700d850342c20700c2120f0641c1c103055850a60000045001344109001da80104401ca44041d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 406905782 1250 406904532 406904573
    0xd050a030309022b021203070c210c030302010b1c030c030f050c030f07050d08010503150901090804060201020c0d09050f09090319080f07090617040c0b0430 69
    0x852000940d03031204c451140b5104181c982016160540e010005034203d150801c0340b250841010180e031869001094400c10307503100c2104104141010840c07280b01c4101a54954444c04e40c00d21a000548100b40300d00080d4425000880c210340081c0c00c201d049000c4042c400c02190070742010102003603000501c030580700d405007402407035000011800c44643c0b14402104403540720000300a2415010784004100c0c0038082c00a490890071000000c44042d0000e10070030b94150b1141c050b40c8040428081200c1d0401c1c0381500000e914816507481d00c9960700164401c1c400340c0d60214810009142c2404142070a80789440c1c1041705504104c0040c55001e44243d403640562a840d00040c0c00d580100201d89941c0108100140251210580104040300c1182d200c1d4020005d1400719440c0c501440e46102a60059207070071410520300301651b41c100100520580e4107d0a07000d0005021035030000810250440785804070003a030601565031420a408252040d2003070141c020304c1e011440703d00c0c07502e030480402c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 406907032 1250 406905782 406905791
    0x603100618081209010e040204080a032a030806011205090d12020702040f1e050c04150e300304080c210601260c0f0103020307030e030d0903020c0d050a0303 69
    0x1000300300000c2007a00520420b109032103030f80a01c0403040c2c0180035118030076a1040e111035282c00601c000d034011807203064078541c400071140001030300440c9528080070140085003407000071030307103400c0251048000650109010b030301840f11a580c80f4607440740c5203c907440140410b051901445950700381c07031580c10f010016813100b40210406183c045954a0350014001d0000031103a850441c010680300c001d0fa40d007800702d00c503c9154000340d0f0065030301c641006c00540b070506103031150f840e1015400300724001c03c101e115450760038035940f46044400040c03261150044c115800e48540950b900c085548402154030600040101007400a210781c03240200792001e800d031050005030302010034001091001c160040c0d000101b042d2200700c3c6aa40500101d1000d024040c030b070218901c1e00c0d9020660f503d60030085000f42e107126035010ba001507401c045c0170310300000e09401d0040504e0564101c0180940c446481b82014800d140e8104000e6904034801c4403c50035014480c1d0f1582d030740b00c0c4c003010001c040c59240e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 406908282 1250 406907032 406907057
    0xd0b0126150f09010b03070807020d020c2101020703081501111f06150509040c03050405030304060908040f080c0f33040b0a1206090507090302120102040801151406031006 75
    0x20810b01901c40c00000c1d01c031507519610317580303190016041100d1240000d00b0800004000d6440018084242015138004d0902c1c51030b07510a20440c41d00441d41521780301159665681524800d01c01840043d000e0380e51072500d0304045140005441103409402c0c1080b100705018044a6404103140d004407554065030786c5007800441842001d42030303d6001c8020341695041d81c001240e0098002c3c00440c03c112002c01140900315420381c1100c4007560041c0130307a801400003c00027410759121042c59030003144010f0a00da52020007910b01020754010000c0c0d0b03088440d610740d075401c19010218032514211003e2300c0030200720100115200480c50351201c0514401c00c0d485280340303140c2c00c41e00504602c4034400c1d41ca01c0c00c0345002c1e01013000503144d410820319240000079440c0d501d100d1035000d505641c1d10940d0751032843c1c007040b2441c0040c40c1040c60359507003003000080544091048109071000c0c01840b24110f0301e0142d518903c0910f40854030300401041041003d08600818820241c442c2400c2c1000b25041 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 406909532 1250 406908282 406908289
    0x509130522020d0c080d090b1206010503040507050a0803040905150d0b0c13060905130c0210020c030f070b0108070602010c02030a0c060e0a0b0a0f02040b0d021e0d0b012615 76
    0x40c410000f400c4801804c1e00803030034401c040340d080000300a0f41c88541185079030b0980150355100d000558226052850040b9a040d1300c0340d0002d54001d0b003e90b080303e9900b501e07880000c0030303940143e1212140b940f000504114181d100c3c0141c1d98032003650b0301d10404142032140417807500400f105004080c3e15042c400106814280400e03503d1641180e00030b5083c054a0b10409410500d550040501c00c01891850f41c0d81c00d1014051440c60303100c15406000c2481c0240c2c0b114029402070720008401340010300960041021200280240b1130141c8014034643d45800070103800e10703086800100c11a4140440840440e8002007100c013007010500c0e00200404242c100440101078001c0d440b4841c1c0a1140c030a4288086c19080901500072500200400e80e889601c040891203544a00c40b81c9860501540c4402c4086502902591080d4400d9400300340500c1141c04243e80036408107010310b40d03142c800c202203590000c80d1404d5000052171103c60441503a15008814000078140e035002c50b142100c1036491385 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 406910782 1250 406909532 406909549
    0xa02150c1615231215030a020307030b0c07050f010b1203040605031b04080f0a050d0f02060f04240c02010501092306010212120411010504030c061419050913052202 72
    0x410f07080d041d80300d0f0110061090100002d4074801011500b114080d10280781c0400d050360b01e158001c00810166246691b00c070340030100240300c151811814004100410b000303115144140102c0c4000003003a42d95201004180741c0720402ea400b055005210a2141d15000002c881d0016541c1811320350a581c03941d0103034518030860b00145c00d18051071140c001044400564802c1c8176102d001540c40700d12503000200e4003264685660001644441d000c03031403608980c218550054003801d205500003150141d15801403c42c4c00414440b02d03940c0200005982e8203108041c090205031380180b01040307030b03040c00180c80080b11040e1802c90403624041500340e8000c100ca400d0116949041d940c0310300b0501040c5408441c126400d69103c40881d44c0c400d0b0b60742c0f050b030884042e2948807070443d0181d03080805c103c51a440300e04d000342040303404111160140e0300401c0122550081956100c0e0380f0200402801b03000306c84407038107428490800003400b10103089482c405640f2101e55850307200c5070105000003190380 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 406912032 1250 406910782 406910837
    0x5041a161206030218250c02130e060c0c0706180504020d2c01060902070519260408012d020c010b09040c03020114070c15020a02150c1615 61
    0x31120000002c208a9080340840c8182c52030045c0c8a68007800400d403000c072640c51b000650006811151410042c130344240d000b560f500e461400041c10420003c0d07010f02c1d220080e00c908580500202d840300d030301d80b401c000800c007424407071500ba42c038201a20320002409280e8010340c0e109a80204864840c1c4a60ba0700c0382e41c40c00844503601d154500c0c014903103c4032019600c028a071179424604d000c41c06040e01c0c0204c1d01100e41c8100101640754480030303110308546040c030086030010480c0034100380101c2c40c0d04072104555264038070710f41d039a85000070709800c54031700c0200c1c12642d055008030520804c44010904814a603608070150340c03503800360740460050072000c1c0104ea0101042c4140300510015140680c00c0c0d038800e88481d1490320054440384164050840d008055451a1105108202c524699002070b52801c0c01192041e000075030004901000030030700090050004950150440c03410801516840358101c1c0c181c0b802400e114683e200c8803040100b02082c000e0408402d44500761041c0f0b03a1300c0c071 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 406913282 1250 406912032 406912039
    0xa030e1504060e120f06071805090402060909060d05010c02060a0e0114040303020a052206080f2a0405060a08150a050a030b13050f06092107030807110102070605041a1612060302 78
    0x40d8600103101074098015030f0300d1000000c075081e00c00f00d85810308040cae050085800408407030520012204004400b40300526260708640145017400003d1001d0144031045000c54001e00818a841090f0000703c0c0c03c60402102140e06081205881000c00d10941d0f80141c0c05141c0542c0c2c803400d00000340d90501c07504640120301d443c5031420350410b00f108620501540c0c01a96000303450340b140039009940ba1810788400b0607a490bc3e62030341d900700410319001600078440d400302d0f60600c0d41e508002a0760740c04c40c4c4950b60105005d4070070800b56114503884414500f81c100c0314400344900700004103422102c1800024001b5000d5808039a50040008112550a038004211a604511344200f00c3c2c81d2141511433100612410700d1220081804c4d07120701071501d005800150600c00c607038800301d03601070b03020b0f01000510000b81021110904203000030300d4183d00588001c501c5080c2807500203665409107408000c250180424421883c21001c0713030180700d84c4540b8281c804070201c40c040d00300512603279000070362 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 406914532 1250 406913282 406913293
    0xc120a05070c060b0a211b050907110a0f0803040c0602011a0d0c03230d1e051e04080d1d030304030224070606090b01020a03021c050c0a030e1504060e120f 68
    0x2110910b00050041e550302c030306109031b0008001e547d03241d45a4001d0003034a520042c5038001808062041c621412912201e4044840c2c03140162280e080d21a0f6040c3c06541c08a0000208400c0c81890b0807004020040c5100800002c0402c01c100c24004503001002d91240030400c9061040c0003044081502943e0080807054038000000d083c02c42810100802c28038034066203154032400c9001c0c80c07610008600c0c1d080c41c03902c2c91800305400c4030359502031500071400720310300318803101c80c20142d03406080504000d40060a528413040000382000e40b10362080d60102100800005c031a84000c000d450441341d056904c031022940541c51813200c45460308054000d40720104030f410501015400c08000c5501c0c040c010021011110012a12083e00c201c000d0b015902002039032907900c86280d4501c502010f40e00d005070070105400d0312a424509180740036000545100700c00c45491600c3c00382800000501904a031525140685c082d1680340c6488850b41f02e808040603d0728400070901818110440b00c006581 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 406915782 1250 406914532 406914569
    0x70c06060312021f060506070f05100516030e0106050d140a060e0102091e03070e1305070e010603060b070b0c0a12020c0601080c030312060d0c0506030c120a05070c060b0a 75
    0x30750780d001201c1c80384e44001141c018421030002c0f9114a005a800c0a01090f103014615120f04070070418840e0300300c4062188041d01001046a80702c0c0e1030140002114603841607241c480010b083e984031007500f001ca03915040c007c0281741d90f400001015550300c0400c01041001c0007075524107014090802420240c2004a00485070fa0107600402c8060b2046501300100c9090340c410208540800b080355130182d2101106215628041111691244503100c08410314040c3d03903600c0e400d000d050703804010058881801071200c0b603090b002c3d04002c0c00ea80e040c03481c20040740d6100c1983e05040074001402d03074100001e4180940b03108507064034041000312000d40d1381e644089030f16542d03101c0901c100c1e0720798040c802c410242498044122454050310f141c0000498403200300700308003171800e602c00300d0300710081b014001001e4450078017171071040b1007400c10141c440d0240002209085002004c20406a14141c2088101e68110b205c103014542c100300c000488240400100301d850041c0d4000c5004c40d903524039480c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 406917032 1250 406915782 406915787
    0x3020f0402041e2402151b040e04050f030703050a0c0203010f110d060b0310060e0d020d0b07021b010503040f1109010f030615050907080702070b03070e100e09070c06060312 76
    0x1c0342100c603580111380100e041007440b0880c08a03042c2e83e41e40182c114510400400348400c01481d0405803181c42c41d00707906080b840b000c2060303000d80d001c50003001c071082c10441888400c1c49169942040280031394540011a603000741144194184c10080c00f100b00b11035025510254020112810903520400035000b801c154611290042201c1081090a007070000c05e6668805050703c0c003034804c0175444503a060a21006840100c0800183e940210304459001e025980b02650560884d009018062080c10510310090a00e22a800700c1e9615022054001c682ca0364414100c5c0d5005400245810380068140760041985079002d102d0b40e4851541800401ca01914030141402c40e48035890402c0001860040141210b84034803625030f001281c040082c0603240102c40c8503a1040141c81602e910b00d49850b02c245283c0c005448040000381e13000000074807820032901251541200d400d00d0308105a0003030000c0c0311110b005140e0f008200004100b40208140ca80000c4042c650246884541c0072028000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 406918282 1250 406917032 406917089
    0x406090605060103061404092103020309191a06010c060c02060702070f03020d02010503130b070e10112a090a05070305060909070504090305070516060212040f03020f040204 76
    0x940340c19152001103802580240300d2142110000c4111030300150311101000000c00b81c00c0300542d000e00b0014007147e1908110300a8080500030754500603103070b0500d42a0a03182c40b04001402080c446801d03000800728100b82c0d0390842d801002d20403101e09035980c400480300c048800c1c00050101d81014600f040c031580100700c2920a0050b68200c03403c0c0c40d03950481c0301d081185407001030f4000c11440c07500e82c00f6510075401554000c0305000d1204803800c1e181d072003100c095000c80310074001515110094113186014150300c80c0a0810303262000c0300c03504072800b031031715100d800f45da8000315030000003151031203981102da009514400401c600036510b482c4d60811302920003100e1083c0040c2c80c000003d0700c1442d109051034024024031008002c1e6600308010b201c003d000300e03582601884000e00202c00003c404010908440009818111000e403800b60040d28180f5110609040d81d102804240001e01d2522030300c0044907011640d12030380c90502030104000f0300c5603400841d0004001c1901040f18503410380c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 406919532 1250 406918282 406918301
    0x26280f0c03050c0f15030603010204031b080105010603020304050c190b040608060a060f02060408030402191214030c0c0d06020d150312142205031c020f010507080f0702070e0406 78
    0x2500d0301e890040f4104031500f100320b40b1a80d485188041c0090307820742c509002d15400b240c003030001450107840b500c13142c2c103044244a5184212984c20070a00c0701c00004e00a0324010301c0305013401d5055003030581d1040e031101c003104442406812000c0d40501d0718141e00e042040203190f0f010b0210381d29030311100300a080c000111005401400941c40010b40e0a00c00d00f00d1041e070000c658054005922a61b1b9850385503800600141c2c1d01c25111641a02c070321044611040090010400c9070184040c50718128098450400c218046600140b0171810307541c04c041341a080003501215640c1c0101c1c2c00e45081d600070b00400032500358440c41d100010032207042c000252800e4038050404501c80206401e811034011030054901c0ec0451000c1c880340d81b21026200b0084000074074010488003103529100440c1c90800600060300381240c041ca064090a0340610640a03002c400324000d01003480d10b0b00000e81003100203000e00074040404c20015408500c00e000b054042c00d0b281c0c0c2a8a890704150400740e014004282 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 406920782 1250 406919532 406919543
    0x1803010509031603180f0f05030d08040507050411070c15080c04060e04050402030a060c080a06050d0503340b0a0f0218120a17030126280f0c03 63
    0x1808202401e60000980e4000140e2480404165082c3e82d01103030034183c1c00040c1000308580b25004144800d0344800c55003d805002040c50300d103481c040802d460600201102010f0111103030030700c80810400b007400810740c1d0040d078000c545502c01c3c91000000e0310541c48007510701c4011060100c0e88186812511004000c507a90340309064031541188220b51042d84a0340b00454808000b040c4181000e41005030700500040964081003895202c80c0b09641e0103044100c0003034180c1040099500d2644503035000780600b616075000040050351802c2e07807841101c030050050040500a100d80342c03180d544401801c2c40d5003083c03401000107460f040d00c0300c0341b0540d0420070990070302180401e4000e06100f5946881c15940130340328540c0500003800300340c030400190402036014514403a00826405882c511244400c005421755940c94103c07100c41c520401d16960282c4014200da45040c2240040c00030301c030058650446038030180d01c0c0e100d008000c0801c01c00402c1300c5034100c001d000f4401c10b550f4000032a0f0040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 406922032 1250 406920782 406920791
    0x7030f022a0c180604110f0322140c120a030905061e0c030c0105150d1719020c0a0501140403081810030e0c03211b16030c0509130b07090902180301 65
    0x104003400c014011f100a01d8500c0c03206000165200300705400302c4009644001e211001c510080d291024003003e000b101002503031007085280898108015a00191015103018000114655800401008051160714071510010410300a00c0e4174018544400302210b684281d070345c80f41c14041c0d80c1c5903002000091415407a1000080d00003260084a5801020041003015000c2055480024031040c00317851280b2044103214100c1c81762082032007000903d0042e00203120220181040017080d501c6078000724100f0090ba01c0004420075418141c0d81603e81c040702ca661a1026034109051404240e600c503640308200c0b00400e030780c0f1070b05a88113a1064800000b0354051244143c20702d90380d200615020420a50300402c402445407030103000c3c14a20701651001210200b5845070f01e8076240101007840b00820b09540308004010650403802c0c01071809036141d412a2500041039800c1071180030002d0104041d10b00000c803c544294031103005031501d030300c0443d00da44009441440741c00070045440d00941c41d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 406923282 1250 406922032 406922051
    0x170c0403202706010e0f09070c0c1403072c04030c05100506090a0921020312040b0f070314071b050111220803030c071b080607030f022a0c180604 64
    0x8580c640c5e600b1101501c0ca42164402c0380c14010550402000ba04c200724080c612640001d00c5128104020502d030149185031100c840205814082c60f6413040780580b400c9082419162a074050003c40d0781411141c03601c0c660755600381070b10308050340f03c0300800d58003405982c501082d42c240d001c0ba008000c1620b01070301590703071125034000321202800050074211603c4180003080c13040c041c804245240030310503a818005140301c01c1d0321107501902c04895054061040210000c0c01c400b6483d0f100803145000d02c28000380c07410704c100014025040c00b0401c0023901c0441d4441c0c46003800c0c2e0310065400740007001500d1100c0c03031290751a0410302c0107181c0c580c80c00b0100100080317107030441c02c190b80314140918516290210602e52a6000e01812140a0f220242e01c24201c03010520702c0740180343c1c1c103000d090307145020100241202c80d0320074180a154414000034901a040d04a0000c0c031362110f80054a4034021416058644080c00c0000d0b64807600301c02c01101c40e100710701806400340c00e05a9040c040c405e0b1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 406924532 1250 406923282 406923287
    0x170d0f05010603020a0905060d0608011803020d05040f030201120e031207020d0509010813110a15090e0f13060b1e03011506050d02030c0706051501170c040320270601 73
    0x180316041c5d00142d4501d0050140d85010001080540d4100c0d80000e28a9030f25003200342514100d021030060035803801e0484051680600c00e1741500f83c418a0502d01c3d003420007600101a88072400083c0c1045030768015120304040030b90088992613000b000702c075140e0480da030b407643c00c607102143c8550060064801c204205805907058415004050311110790683e0340d900407226880c0700b09416942c040c22036100f80c405446055030750015144c0000c441b244c00c00758900250000300d20f54002c1c2e98800041d02004081c01016030021341040e0030140e5400c203144181000c501809000c844594890003084e080c4140f03007501021401f020000b6030090003104024016460035090900c151004520200038600d118001a801158040001d05025007040d180792035807400ca070f40c11141c010132419880c600021540c1c128461803100345220002190a01d060100317442c1c41c2c0240d101c014446013540b550b21800301420904800c540328050009500e10091f01c403034001132075a11514050315124000030810552 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 406925782 1250 406924532 406924537
    0x11010f0203040620031e1206090609061003320a0b01080613090c0b0304150603120e040e030a0201020307110c21010f090804050307050910060c170d0f0501060302 71
    0x10300c59292030a21341400d1000407986840404c00c021140001c00410403072400031410240101c50759410741c0d449002d03400608840300801307460240310b0000c2c0d400300000303a074030000714690050702136174006801d0412420940252185003881c8512852407000114410710340440110320100592049955407102d03644030003101c030800700b00d50000300b10400041d00e0703080418511400c020710701350010b1064820b842e0750a018810b03401c582000341c4000248000d12510748601c02c140c072132518040000610795581e007a03040c01d82c0002002402800a407010b400da881c2c3e44144621038008c0c0170343e942e4490701c450080c001c1d801200c60304089089000c9400c06803800003011210400c0142098081c00612184002803141f5820303407000d0740d0348880310322481885c03034042d00c1a550300c51000161194145401c0504007800c075081356001d18612410040c00c900400c00e45002c85109081c40808400b041c20f0044031043c04806009101ca0b00003150b0000d56001d41c40000321305041d003070030001a43c9643c800c505a1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 406927032 1250 406925782 406925789
    0xc0c1206010e100b0406080a1b021f0e03030a090b01080a0302100504140a0f02040c0c02060403140c030a080a030501060e01020d0e03010b0406141302030402060f0a051611010f020304 80
    0x380e20000041c80303418000c528150300724081c0940c11034510b58448849600d60300580010001440e210107000c1501a6800b8000b00942448030314003102c020180000c0d540c241620450001003101041c6072507000213a484040214800010b5990ba0320700084280302420103058101e40051051000050003079020590741074681d0300d0f82c054015200d5440c6610041e1a019100340e98016117403002040c800000c02030305c00394a2060344942c05400250040104444101c01d00c003040c404140e044c0c04c016030340c00d4101e60989034014281007002d1403071007a0502e421014500740d9014414610380d1000d009442000c0c3c25522200d503000c0c80140e8031098201c03028100000351034050307400030200e5110b060181c41007441e000c41c003400000e00c1c040719400244c162403196100768850141d00903890756509000c1a8141c540601d10f82c1075240d0300f0301d680843c2d92881040c03041740c128a03001c100365008510640440c0c00341410f1340c41650302d0000904008121038004000c082c00b1903008910700410600100654045 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 406928282 1250 406927032 406927069
    0x62a070609121b080a0311030309030717040302060a05073e220c020106120302190515040b15090f130206040f0b09090108030408070306021b060a020c0c 67
    0x4580b0304907502e80b081d03000e0802202d040205a00a40c82401a0a00803004148074002840000c1490030042d141c41c2c00610b00e06441d810400400114034000800c95044a600c0310140025400c01004c1048600503500000d40c800000602d0501c140e42c045d014001036405410401d00c042800001c001c0313a1425403110786984220f94104e81081030b001c80d184076041c10007411000e03810381e0007548449500520f9801c104003a60300c03194400840d50901c41c1c500036046180000100042a4078041c1d13460100e64515110700020400e00004c00000f07105213010300b550f0482c5010181020300c1c000066041c21500002003205010364100d103450941c07000e44c0140080e03100f071190f82c6c4640161b0903041c0c8000c141607800903402c0000244054407a4030006c010281d6683c0326840b01c500d40108941d0f000c042e404420503600c103000900001c507011807d4811254000c034010f995a221042c0c201400204800080040c05101c04000764012a600180510100c50080c0c030704034032103401084000d68991302e01c41c0380b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 406929532 1250 406928282 406928297
    0x5040201090315020d0507020d120b090f250c031b02181509100f0807060807050d1d37020904020f0303070c05030c09190506060405062a0706 62
    0x214034150f0000340004152a000343c946101100001709071601a54030703d0040e031000c021040e0840d40446006000c1c105203800340b1030880d9120014020340c0010b094101c5034002c0c00041a1554403021000245402c5a50803020030184018041e103181d50010b4140c0108000b0134110385406500240b0700b161079802460502c090407400520a5080e0008010046440c001110598583d650007003040c410380361060105c0b81d40b414540450400c440340e03401600c255000315414011543c000390000d030f20001c649000340d1601801a90304015200025400c0203c4480c1c0304211082c0a0100714001c0e9209541030140c1e0903e8200f4007410002c40b8010140c4540364651381c0703000140b600b0101c00380c005000401c4054410340c41800241580d001c950211040e1110300c10802c06802d05205404c0c4100d41162550440d182c0301c0035288008102920100307080380d5403000281aa541c01e015100038080c041d020725101c00350020800341403c2c529400c1680c0981c0c41030041c00c402d00c00281c50040c0c407a503948014 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 406930782 1250 406929532 406929539
    0x5090c040b0a0c02011b0c15020f0d05030402040b06040e0f150607080d020d110301060f020a0209070309020a03050706051e09010e0603040303020408060406021c0603030206061908010f021308010504020109 90
    0x3e4a0281e480d00480c10086010030441142d244985401005401144070502c46441c2160041e501d05000300c4060554000709502c0c00f40704d20104039901910154144660769a50714400107004040d04100d01d07501c20340114020600d0310800c17203458403030070750b09403144803649800b06c4204415400c1d0740541d5011200f000700400059825018141982e40340d4005410720068800c0041030b5050441d80b00540d56010004101d0280d001056070503000031400a071504ca8002d0b000f050402c0785c02051281856181d540741400c40d128003d20400941d04401030f520b1503511000000c00c2a84038640c441115101d0f000c05900b8050a4812120b484005860705200001c50038240181508000c20540a06600b40000569490240103480c41144604801030b07a601c0190203c01070006090110415a0304d420300900000e500051078681081003100d161000a0092600700c85002c4070360441000d079400c207965012a042581c01030044400c21821490701c03951120b4a00382240d13803c9902a000034581032042 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 406932032 1250 406930782 406930787
    0xc060307030c0512161404050108010e152d0f0612060a030515071b0f15020903070f05091311060904091b06480f030905090c040b0a 58
    0x116190b40c45050a90070b0841104542c0651541120705c0c201c001c09000c4521a107651040c0099801c1032039400541c10181000c000902640c0d05000764228200070f84041200c810454200044d40c030002400790842d16420048031300c401d0720754400c140300000010500c590314030381440042c00409029241d54204000c2c0542200000300203803015810503004c4c2c10100208800b4051715442010b0070b00d03034880300c3c103000070b0060000c41000c01240700f61303000820240000340c442401d40903260300019010400c8074143c400d030000307202d80c1540c2035040c400d200c0000f680146500000f01151001c0340c00850326591103a1800903030020307000c020050b000b400030f5a0030503d0301c4005400000c0b0b02400c0007901e60860b6540c001c04111410a50407600e200000030000f07154000645400b080d0710070418040390310328140c9400e11804208103944034000d1005074007412001440901040342c3c024a20b0030340f02c0c8603030802501c845000c1c0100c50280b1404070018400030084c20032501200c0c0c480c40564a020001c4208 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 406933282 1250 406932032 406932041
    0xf0e130c030b1005250f1e05071a1606061d1603050c1e04030204060314010b0406080a15020c060c0712050406200106030c080f15040305120405010209060703030903080601020c06030703 81
    0x41b20302d0000c80e004031000c212600e002212010070003807509a280c0c02424421700d066480d5111451100c06002c490040384640d01c1507881440b140c0140d00d0f058000d614143c000b86c14983c011010b40d8203101d10203800c00001071200d41c02050103030078243e038200991030110300f80c54044810303000c40720080100340091510310450392001c00070595440c1c1001e4503070b400102541c00c10391065440c41c1240406c8202c8007020f02c0340800d4803200300c800700302c803a1070181440e41341e0600490151100440007003001c02c9044540480e001204901d0507200e0070303c0c0560b44400290009038084d2007111003004440c00560040007128262007154940602e01d032868021940410081354220b00c0c0e075500c81c4c100000007915010381801604030032001d000b0740204c1c0c01400303140030824900b1540032049407042c440460381040440b684803010043c0b10640b603480f0708007180a41b00352861140c0001000807140d0525078140e20650302c0a12070755421029445810049035952500c2c581543e12940400100e400603010760700 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 406934532 1250 406933282 406933357
    0x30905100c080d02041d041e261c0903080703060305032502130e10020f09010503100e09030a110d0206060f040e0a050a0506070f0f0e130c030b1005 65
    0x3c0589000d0711880405a410104000090007100050500007000f801290304442440b000c83d400b282e46c517058407110751442110780d5100b0b100c100d1100680c42054031004035140c403c0c007178025038044400f02032820300404940d0303003d40c005410301d0081600700344030740501401c42e80c1100045081000380050604100310500050b40500040d1410b180140c4440d00c2e1910884101c7d500010301e10540100b16042c040048030044030641704000e00e21f141c41000e81558900a420f00e4250303143e586000102002c1c40301908040000341c0c40004001041d01d0000090110309100c5e91400c44815117a603005960b003210f608080c01680182c000030303069091000c48000300640060012a800d0701d41c900d43d6042c94140c5d00180c44540003d0b881200b4014100710040c1c21101d03501d0407007400103a800008040d50400c60a26042040040300c1320415512071406035195140c000b420090480300001c003400810283c01490b0041203501000c210042c010740984600f0600d4000c5c0704090021f5128a1504100c4d580 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 406935782 1250 406934532 406934557
    0x806150303043002090f0601080703150e0601110a0809030106090b13050705090a08010509010c050a080403140d0507050a0905030303130303051e01061701050306040f02040911030303090307030905100c08 89
    0x51282004da0340b80703146180501c95200090300c0c58107040c000107015050061005080c5820b0240101f901241840460f049881c61a0440119103448004071350501040c0c0b1164601c0c482d5803075010900414000410b58901c2c00c038002c014003030b540c501c48015942d1110080c1d6201c0420010b60341c441030140c001c280d03c40817502d071035031604507000300080c0c885100d40c0101c1d0301c9a54903810045c01c1c420900c03e107040d001d22400c0c803500300580980000e11062008000804014641c0468200c0b01100f005645004860b1101072200f0b2400501c000e080e0381040714020300040070303100001003500300802100c0c014802004240c002d800541c4082d405058007030501c006000103100450020209550307090701800140c0d0714406140b008560b13044440d101a002035100344c04c48020320000032840544104e4403036042c2c501259548803820006000c141462049030580000810000c04050110040030030034402d4440c00e0f510341d01c0307006110040d00d0150580c80800c1c0e5542c8810701259414003d406401c800d032 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 406937032 1250 406935782 406935869
    0x106050a05060a030b03460807031b0204020315240f0702130603030c170a020c100c20011106160c24020301090c0c0f12030e0304080615030304 63
    0x200700a0202030a89144402c0d505400c00d07003000c4800c00d47c0c0b05541e0b901c01c0400d13090505509030700c40e100b403449080e000406200ca542c08801014180c8003c0b6228950010411074030303807401d0b030180e00b05568092995441003820325034680702800c4240610050510b0300d030301305061042c1d240d00165540d120b5282681d114203102d005204040143c00b84002440c071a40d44e000d80e40d1003515160407070042150917540440ca0600c87c00b0b1a203540014005803002080314102042042c00000762103a1084990180c2400e02000342c0440c1e11204243c0384902142c00e030303202035509c11a000081d072107110a9030507040d55000007881d0f0b4144c612802c59800c410b8000d040d12410b4580440c2d00b00c00900c080204050820780200c010450900f1074071603921a0100d50801003a511069510240000c0345400000d0100741900300b42c0142c02d00c00d0340180100603110040f65078a54440580540e41c0404840d00d4040d0150000c14910505021003a0b0f41102d903060f900d004900c100ea0700d400140c0c401c00032000ca211049 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 406938282 1250 406937032 406937053
    0x150304051e1e0106080f0d1209030516050c090a02070b04080a050408060f070e010c02030607031119020307120906090312050d020412030f020c13020f19050c0106050a05060a030b03 79
    0x40c1401540d1980c2d050000159251030f103403031079080440708609840c01d0b41005180095640c1c0050400b260307120801070000301400c440ca01501d107030040340c41c84004c01c100010740100300800080c4900141204507941c42e040d5880c0c0007010f00f68070414174000d10441180700800d0002d81c951014040b5581c0504050382025200ca12580c64035404a410141d962040c00501071050780100300a03040000030303e03100641304080d8001c2595258041d207400200340c3c1c3c4010110440c100c06090701c401c0c0f140c60300d6441071900f000c8070003540e0707802c608800e5421030315080d64240705030301a2001c034041311443e4481031104c618540701d46d441d421b800c0c0140410300a0410409540388010b00c014409860316207880c0200413110300f1300a0241c0000800e44c0203540c00020307190040d9503802c0f90f280d43d10b04455005607981502e805003808034080c00c0c1061210350550b00911400f0340e002005000915408002000055914010400542c440b4410150081d01c00c116420016100c0e80040360300c0781d000b03012140c07148078 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 406939532 1250 406938282 406938313
    0x90f0123030709030b0a2c0f1c0801050f0312031504060f03031e050f0a020309060a260c07020f030f100f0605030a05102003040c0302150304051e 64
    0x108450002c0081d05600c0207104000f410740c10140c00c04803810301040301e075001808054a0f418140c00480b0403280c00341440b180c05800f00102c41941c00c1d10000e8400614081440042c985941c000480c040b030500400803035036041c50342c68200341450050003000a40130440b03044020307030f1024003001865440c101c2c80b0b1000380c859005180003448001c010340c82c0d107480d50034014410024103840071403051800c0020148903a021082d01e01c240549004031390703183ea041038103074613501c100d010442d0001030100c0c1c60b5005540210900301202003001d10b0161501c0f204105840c0000c0c100c0d80c00c1e8640a061008102605014082107015100a412514660707003030805c03140740c00c0c06003c02591950301c40358040c1303106d0b110703000381401410b0903001402440d01c90758480703442d000381c3d0b61807244841d0354580b511a810703d1110300e41101001000c1c40782e03a03400c0606003080000050300003030380104085400901600815801c69100b150060040c00344030003400090080800706100d0640c8511811502ea055401c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 406940782 1250 406939532 406939537
    0xe010c12110702040b0a091109100f09052214011a0a0c11040f0f0b01020c18010e1e0901020a020d0c0b06040c02030c0d0e0a050f010f23180405010506090f0123 70
    0xb10212454690a81d0b03400c01051511080c5000704011804001500f00d6402c10cc004040c0c0b507040300c080260a0300240400c2d000c080c0c840c0c0d0144528102240300103a40e10114515040e500480c0e000d4a0010301d01e100c6660611412034003e0020320b940e212140454900c00310580c03068401000810824034500d41e85080d0758003107081c1c0c1a0a40d0b01c7d4900e80c420360f010001c2c1c450f4400c040d54400301005545010540741d101c14414208854441c0000801c5d8102e900200300d400300c3d070000201c07402d080c000b403408d000703400101c608009840b03002c091001041c01100a12100e82d8400000c0c501503880d070341408064080051034005510051000c0d01c600311040c81240c82c2c407200ba40d02e40700300e020031408115103d41203900140c021311041058444a903440380c0b1205e41c1113072909080780030300350011100c00603200c1c40a203031089004c081402c41c01c2c1030b8403000c0111070000860b42403041c6c4c1d80320410462507100b002c02c180e030b1058011007001c0e4554001d0f07a03205031044000403001140e00c0352811b80b08495 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 406942032 1250 406940782 406940801
    0x1204060c11042408061608090a29090105011401050c0a060f0212130803071d0a0605030106120b030712060b060304050705031e03070311030705010e010c12110702040b0a09 75
    0x4025281d081c40e0407004100e0f0740c03401007210400030645401c191407500b080e182c148101108011340d500014114100800140000a50004482c40c0c00034a1407683d481d810300d20000111982d60f102c0221f511031005000b0203044e00d800d5031080c0110882180103441651011003e04000e004c0d601d01940031074400c0c450706408001c241c0016030364082c07110b426503000c40c00a142d66020828412040c02103400002540d40c08803160030716070408500c6000003001c0040240e0070316440303102d0040205056601101441c12074002e6280c00040ba94082100300559502c141e05680503071042104010440054030350310702c29801034000188500040010038810f6204036410b50f429030140d4002c00080c24108015500c9000b824404003c50503107115140d00d0307100788000903041100300351000e003040505008135466164040004c002a00e800f01d80c060103490124641e50108403504402da407003400500036101d08070070803010545412540c2e800c010080c0056400b080d006051040041801c400600c10348016 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 406943282 1250 406942032 406942061
    0x220e04080703170f0c1c1415030703050a0311030c0d1707030c0c0b07140d090209091902040b0a08060907061e02060103120e0a06080a060b070809010c03020c0a03060e06091204060c1104 81
    0x1f5280031400e0120f1068108000c40c002c0c2d000c001e0400119802041e040d04255062410710f4100280c0f40c0720a20714092140c64002d01d0040d40c041e500b849400006090070406642800c0341320740d4650313009500f1981030b1303075504c008106100f84000025035420f40c459402085402c2500030f5204d160b001a47c01d4000300d104070203403951200400c007503140105400307038880d03907200040910aa8500710100850002c5200900413604d41203150b01950320202464040c280e030b14200d40d0149400ca03c00742e5541c1d101d1080c0000310b82003420201c1c40a00030110007540e86650340083c0f005034a1a517444182d0000815076008000780c403010b150050b5203080a00c001001c00382d544030044e003452036003007080b164a0303409840a024104840c0f40008e2034074058901c00042420203510440d85801d00340d003858002d051840d0b12400015010042000b150b10101c60b1140d24403c9079103035507d0b41140d036079940e88141007204401c010302c4100071503840340300101826486107a216407240c410350042025148500c001d41e42 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 406944532 1250 406943282 406943321
    0x703170c0409060e0f1501050a0f020a02061206180601020a030c0203010603050a2a0f350d12020a081303090801050c1c06030206220e04080703170f0c1c 67
    0x81001c0255061b80104d8849990341d22031700034a002070103a1141c08210000c3c8140030100c6000603001f40010650240c016024903a030b01844918526160381c1200d101c1d12441169581400c6c4802d8001c01a21404040e0024014180140c40c20303503c000c00a881241e1640d01c9070b0000c000600280140100720b88030798594403c040c4101c0c218584e401e0850007000d000c04148108000c00c03440d81909808441c0080b0351a50300402d0f8548140c0ea10300c6d420b1a1010001c96085404e464003400038819030700c0c41041d60740d26520007110310604d060707205584001c00003d1b83c06002c01d03130110010310132042c2c0c80e02c00d003040d801c455a80c1003600d0940c2c50032a0040c0e58a440402c0c0d0300406aa00c00012940000b095001c1201c0d44c15603000410a0260701104d1455011442046840703503007440003400944074070000c00d51146000d140180c15a0b108000840000d41442d83c05080d458030400f219004180703011221744a03556110584201d44c018442011890b01c00824268001403103106200404520008112 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 406945782 1250 406944532 406944541
    0x1b020402040902130e040c03030819091518020d171b0304050111030306010c1b180203061005030103050703080f090414040b06010903030503060909010b060c010911060703170c0409060e 81
    0x502c800c145c0d0320422101c8000001c010004410110200036241c0c5403c042156490700500c0602c8130401000c11a01d40340f07040b482c00107000300c2e880034130030000340d040e020b104402c0d00c00000d402c0c011800100a4000d050224188d00040405aa0b04006225482c3c41070030302c4188041c1403800000d00344418841d400026050101e940d000143c100011803001c000d52441c140380c0002025180d401c00042c1c540c00030b445441280d96403046000006004c02c682e108500142406580c1c000d61003038640610548600369141d0a10f0300039000c1c1ca04807904003000e071800501e9603c03454569889500d10a603030741d2003003000c2080c9a4a40c40740114400c407041009109213000c1c5003020710040d0140c01329040c8a854802080005e500c581201d910520a03142d003030581d03c90080090140ca5104a803591004010603080e0913407a055100602c0207000d03d20401c2654400c200f840042d110304030001c1e00081c0d0300011040d909ca04642c402c0d8005480010044c503190b584d107140000c45100d500614040c071080010300 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 406947032 1250 406945782 406945807
    0x708073305041404060303081501090b0706051005040501050607140304180f0c0302090a140a05040c0503100909080f1b060a0e0f010c08160302070c2417071b020402040902 75
    0x43c9030044090728100f00c45070450300c0151840030700a00308640b605100d074007501180d100c2c0300007000404118103020f80b108058501540a040100d840c802040740090000800b46028010b0324100c4501a20161510003d911000b40341e2a03d03894130403081c802004005440841010081c541600026000035016041e41025060300c10030040201014010b00c102d043c25030b04c24601c0800c4075074005038942180300030008510300c20419030015500c90f280c41c6000350310903000b20056210342c0298505581d00d03038503144445d049038280c1c440a081e011043c4446e07183d40e002c0c2030040000c9402d1321548050394075150840f504d010300c211074181d41141c490311b0041c203400d009c21081c4a00100c440c02070180e0038250300300074141000100240c015204100c0302400c0d0324000c1c1e04540141360008240c40c4034649690b000d079406010b052041c400d003000300c210354040318402c0b81000c051140d4042241c40c1c0f900d40c880110f8480104220700d0b014040e20505070700050703440b84010001415003070303c0580c47e0b0480e6400c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 406948282 1250 406947032 406947059
    0x90606030b010e150a031b0809060f011a030601051b0304141804030e0111240f09070b09030114040f0606080a08090904060f140105030f070807330504 66
    0x4071814040340040088180c0c0d42d0458001010b00d10300541c2e42c55101079001100070303001d40b80255480d14000030360721290a1740500f000e03200c2c07440c801c00c0b66142d0b114800c040301d00403800d11580e441845124070021122018100450304007005140803230806032100318495561003001d021940700d07800041c0400080d005108101d0740002c0444c9d2615000f0402080c202941c080184014204043c0b45c441c0c04890b8020a0300038640a5240e0842c0d00c806520141d0300d1000b2070311410407109058600001715030342c90810300c15103c0d2109101400740f00b442c0600000c0290010b04040b0303415503e86000c0d04202c401458810b1195000300c42c00c0c031b80da00050921400300d4842d41c0007070b05980c10841003000880d07440c00480700810030595804015a03120300b0840020b1400482c6072004a0401050502482400c0034a0703058401c11800d0701c810b030485041e09550f4246030301c244501c80d0441c500030400c180392040c04a001491804000305c004030040382e14040294500400d4000c500049030501000107076400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 406949532 1250 406948282 406948301
    0x9030b070203180f013b1e01030c0203190512010815070f051c050901050f061011160b0309010b0102070f030813170318030d050a11070f09060603 64
    0x1461600f102140b0103202c4009032103255000b0401c41c0f0803910b50380d203e41c21203000c42d072800340782d8100c2c40341840100301644811035100000c0c540040707a00c000b52504a41441408038118160b03050f00781d00f200190b020f821a0000041540030502c012075420800c183c0d5240001c03e55518030356a5004010400103045060304140c07015846070320304c00b00344a409615660010382c103040140c10b03001a004100c2e014030903800c601c500300d4103881145030f41012940040d0f0165882d03030000d10940e642c8507001560810f048a0055000ca409a04c08490500a202c000000300c40f8030f00340c80100800c0d0a01a0001d081035101072602d03c0c6c00130801480381d0f820b11484006241c244040e040b05803500c0d195503403040190101800f4a640082d400e01c1ba440c0e03140420000704480d1842015641e0441100e5450f50044146450000558a90000a80703804211011110141d031140b6041080540701218079802c080c0301d030042442081c00c003103900c0d0121b080b80030040800707080c00f05020781401801801e0300d004c0706 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 406950782 1250 406949532 406949537
    0x315230405030f130f060c051b09130317010e01030c0b130b0906070b10090608240903070501140406111303020103110d02030103140606030616080604061509030b07 72
    0x1050000140d0080101ea041c0e00340403e04540b21001c070041d9083d00d802079400840703100851000069210382026007c031400c0e004800781c0303803480008600070810322010320100e42d1110280000983e0b0381444071188a00c1c1740a45802000c28441d40c518100059082c1c0011a81450000040040010452902020704000d0808505040c0e810001c01d441308800d01958240980204104443d0748500c0195001340b0f410818080351030904604126400783c0a0050000860078568089851a800251003585003500280014980341a50000d40b44060282507400d0b60f0100300071715000304000f401928030149072429946113905080c680f010403035a01164280c000304091041c0c100412010b0075100841740c080c2000300c3e003081039540e80c0300d007807195040c184100c6202000210174070003400e03031204481c411502101c1050700d4010426070f480c2411124410724040c848030090030284130ba00002e400c0100980045106034881080c060a43d812401c1c50b000113129140800c14032002d00400342d0421141d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 406952032 1250 406950782 406950851
    0x4151805030405010822060501080d03020a0c08031e040803160921210c060605060405030303042402041706150d020105070c080307080d0b030705091f0315 68
    0x10356510303031640180d201d01030510007204002446024000c8000c604507880d00984c0800c8041450500020b103070030f0050504030b01c280314a0300e1041d03010344201d41110f20152640c05040e1407075540e04d40c841d8001032950340c03901107403451070556a5081c80040e001300c0c4100030140e00c91404160036030100c11044205000c10451071000c1200c0d02071407600c180301545884041c1c0d01d080583c103055000c420158807002004214142984000c0c4c3e201030010b9a4600c83d900902c000707652030041020900070760041d294503420030070116000940058502070104008032030002c00e5000c10350b000b0308a03082079000222241c10440c00310446107041c05450790000c0c03502942c80c00d110304039002ca006034454401c020b0500c400010b80d20140007051040000416110381213030b48d10110f501e000031054014104126001d400c4c0388951015140c08192038082c3c0b840a810510300b5600c40c01c40d03410384c140301280448001c050810200c0400e004008829400c410b1042c045040c945000175110000031808030f564408402 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 406953282 1250 406952032 406952081
    0x117210c0304380a110f06012c090601050d050106080303132102030f0d02040e0709170d0c020114120705090a09020711191509030b0c1804020a0e04050415 68
    0x40d5104c0c2c0c0907134a0301d040e51104044030a441c080c01d0030500c402610a9100000301107640218185400142e1450002210070044110712801020f03100c410058126000612003403c01c03a0a040c50240640004078100303039143d6005086a00070b550022584920140120502c00380c1981c407045100c046040a00d017041c03200c40207489006884c6980c0904d8000260401501d602e601540d01034401d044124110313081840010348200c92521070582c900003200030018420f9408903100034000d2084c0c0368141c1540440d4011540d90380c00340c01140d00c81c10144105030b0040d0050201601c140d045403a807903038076681c8004201591326241d02c6240d12500400c048000200149268540d05d441034811403032910444910b1010409181c03c02c1e4003c0803240c0c10340c998244e218100b20222401854032070556218404100340c148a170001d0341d2610342c004039901b0141d00b4290300800c41740f0700c00d14142400e2074a050000301641d1080e1000d50344a0901180051781c4c0040e4425080c0c00c540007030030a0710714601c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 406954532 1250 406953282 406953389
    0x406051803030c2505090f010510050403050705090a06080f0708123612011e0501050609130b040c1e020d090e0402030106170a06050117210c0304 64
    0x2450710428440c04455a5004c1110911013040040c00009021040e980784c904050300c00d101c02441114441d00795900b005080c1d6020304101d43c00d4a402c14081c058980c280414400714000151140503241e41c1c2e00c0d0001003000040c81032038907105002015081e81c520740700d200f5240c0391000400c41c101950070070400e42c40842c1c07010b5446c1c64240180a88400042c03040000c043e020200f900146c0040018900c2d01210720b042d81b12208460307103521010301d11050303000b5400407200300b4051550808000c00020400e403405005280c140d4186140101d003046003040460141d80303402c40c0040c0407803d0303200c1604140b280b9242c190304a115078402000711015646004200c43c815104500d051071710306000c10203544007034201402500b00c1d04503490340c0707005111b18a0759803003402d142501c2c0149021300200c0e428000e0000c0b20a02d408080082c400c58600c40000c0c2e641340f020994444c0011800c00085541d06001c1c80500000d01c5000000c045544511a9109a050042d51900300003584c0d006040301444 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 406955782 1250 406954532 406954543
    0x10c090f1401031505030d0207031506030f030e04240603050108010b061e0d060f080609010902090c0c0118140d05090d032106080303060102070902090d0f0203120406051803030c 78
    0x1402481c002c203150f18161013107407442c010b540204da01400780d5610404080e40001c2e030b440c00c40307215000002520704603a00340011510b46000082403110a02075a0f00820310590311001c104a00510000b251a02c0300a041d5401a0740300b9021740c10168590100251038140c45114010903101c0000e02c006503250b000161103114502c005241080c0407034103000768996840a0b5203070320840070002c101d0b103903c94a030318489a501d44110142481484001801c0d441c06020f03004031158041c0c0000e07410b03215240f0303e810300d030010000b03141190340c0c4111401c14000c0241c81c00f042c250043c4c1c17040301011405184281003042c480c192406200c4100000c810503103858401c104034a403d464031143e54081c40b83c000500b04000c003041a2000c1c00c5c07820100307025070044021801000243c003250071103541c90400344241e005009680d9800030b10980c800c004181d5154103034040038402803d6401c0601d64400da000d041d04a50080000204045408800403c00000c080b0381c10100724000c60500302d00c00503d030381d80c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 406957032 1250 406955782 406955819
    0x6070f0903050712030c12121d0d0509031203040f0201031b020309011206090c03140702010902060d02130b0703080106080f0405061801230f01050a12111302040305010c090f 76
    0x2130301800400c401d0510465864400035032050000c031209032500801009154a81112a000341c5092060300344500a11801030041100c2c802403d84818090300c10b45803600700441494050284040d1488407070043c2c1c004511070741c0b141140013040c81e04c0e40001021201d8015010140c604030001c2ca5400540000c191540f6100c24a816500c0303131400c0350f103100a0010780e41301a43d2603041c42a40d000858268100041502d450b20341c003546a43c1c2d00070104e09840d40f400b00650480010811442d42140700d40041400c00c40360306101402980c2c1d00c1c05129244d0080c10241d0004981c80d0040c0b18030b65103c40010303003050007002d150020741071546859486070300c0500341e0f1b003a951810580009420003900308842107980200300d0540b031840c1c03420b60805000e08451108410349070200114040c40c104c207080e025102e402140000b40602e03a0b4400c80608c5004100d20341c000301003188003488540500041c00510300c40e400106180c1d520300c0002d00400101c1c1c1100d18400754240c81032110602c04590b02426 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 406958282 1250 406957032 406957049
    0x11040b070b060a03020a080a020103240b0d060e04031d011e0c0f05030a0f08090303130b0408132c0903090409030e0307080d080705130306230906070f09030507 70
    0x10b441d6540024411000c1d03600083d00322440e2076000940050201718507103246c3c001e0301d0a00200e2040c1440c10007507410b100304410b5020b0054001d0004000500141800780c1d60200e001075180d803180d504024505044030200c0000c1e0382d020740b02c00301c030350800b006c2d20800c502828040c2c8410074402d09600c1c1e5540c00c1203590108811407400c00d05100c10440c0040c0340580000c10307640e4a402e20030b0020301e021004441d07600810400e00105500300d00001c00c8902c11441d0764000710012000d50340342c6145c1c080c090000d0303804d98414403401c0500101078540350000c0200f103858800c01109031800f64901445020452014403001c02081b0a03200040220340208808880010340103030785150985090100c644416054070901d10003166001e80015040c1c01007035151180740c007594403400100c0b80c912604080320341d100c8a4000820004107a9001142d032440982e20720310000f4840d1000a50b01081100c882d402a40103605000c082a0003031140c01c021407a41c07601c2003020382151615076a540a43c414804c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 406959532 1250 406958282 406958303
    0x9060c0206070c03050d090e040804090e070f08031b01140a11040b030c03040215040f090b060c01090b06090112021c030e1815011d0108190c0201060911040b07 70
    0x455a9420071107082541c00214003c00b56164140b95548072040b40c40700c0003180f65600040b546011131010303d0700c030b00c2e40b15128a01d4207080400d039001400085440c0390b580c0c41900e07004034040b40741803200340140c44294010764542c0a20140403011803a1195000280e0345171181d500c10400c0c1a4401941c02050300c41d0208034070603c401400410310943c0e00c214020a400700612841142240003180594001c94a04600890350b1008035114865841000a5481120410040c1d408207400132441c0010040445e8203141244035101c0c01e546d58446c0c203d4044c10035404202103850001c1206000d0501002d4814440440398086086803c00458280d030350b8074045808070405114140c128031844000c1c0c2105441c0059010b00c4ca800320003598038400d040d0000a00b00800d51103000441843d02020048405100400703006440c0d00c13101402c07185243e1280c928004030203510b070049050076850f0360700001e0814a42441d0600311010485040b108000401040011850010940740c0d0b071604907203181d0303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 406960782 1250 406959532 406959557
    0xf0806010804111f20030f191b0302011b080112030503060a050a0e1501030203160c0203120415140f040510030209030709021801020c0109060f1205090102040305070e04030906 77
    0x4d100c135500d140e02c1c0d0043d0511544002010b584026569108842c0d1014503200b0114100c449899000f403804240400390300340328812071a050400c0d14400c0c01345505100c0021986410052100e030711403042640036070744403030080d526032040d00c2c014a0410030f1454503038003550500c0608054625001c801a04204010020a02655032000803200410000300290740d099502e0324405101d0804540d103841440140c00c80220700c0d402402107038855910b110000e2a0b40d82c650b0070554140c180c811090b038152003030481c2c6400144c80e00300240050070460b02c0111440d03194800041c03100c1c4d0b9400f0742095600c8140a59408512000f054030241c640c02c8480c4088103280000032402030040c0c11031154103119a1000080c40001c6030f00030030758120400c07d9501c040480900582e0707284001c140090004a01000030010f8501c501c04240500c2d18a240c426044601c9a1030311060703a1082d07a0440050354000303030410402404103c1000103050030590189a40b8050700c0152520940344180400c1c44600f01202 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 406962032 1250 406960782 406960789
    0x6010603090302191b0b03060a0b0c0f0109061b0c08030417070519020a0e09060708090a05010603051615050901140702130c03060b1c0b01020c0a0b0a0f080601080411 73
    0x101a00c0d50710204000380201303d800c001c9180754898005101d41d442c0c660010581c0e4120a044910510016100c02e001d20b15014204507158819148820b8a00826144402820007070040c4d1181c07034016900401c1008502c0c110800302c4640e815003000b0f100c00322801e98005003454040c2c0e0384c0030760800d0780d0010110b400c412011076072040d03c10091841c01040800c007100644e0711104900d5500075504d1081d00c6490b043c4104ca0308071700b80c0d41d80340c1aa000030002036280d48070311480d59001d07461100380e40078903900743c1d109400d5904a400407181c9800030b1030514005541e680c50382c1d0040210070070106014101b444007030003034854061103d041203400aa00a084011041115400760380a0241c1d007105034420302c001d004003500b94041d40001d007040d030000b0704102841e080d80d1a000328101d608418030602c00408004081059085041d401404088061075a400f2101d00003010a14485591a00d1035000204400c031000604000d014100c0c05101c8240d078001c02e095405030703000c5071b1446800c0360072000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 406963282 1250 406962032 406962043
    0x21002030901200a03050105100e040b06041e03060c0305040b01030609050304050a060806040e071404230f010608060301020a0e27011220030619020f040e2706010603090302 76
    0x6240380031041510080f6404010010a044a402e07581000380d1390702e5004101800b59a00b20040c0022002503110045140c9a40910b80614009028514140c0d441e100d54140c0e00c0d05400c98030400700011010002e101c0180a12000c00071540390400013864641e4038482c4500060001a080a603200d161200704981001120b000e80b034014029840c06a80f058010140441100c026001d10308201d146071a5000000e0004142e40e60320034a0b20421519101b888000c00c9240d007210307400c200241c081680705e400d6100d903500404c0d940344282c0056041c00c40c06072805001420050080c0e01c100245030f003032948160350030f1135000b044804480140710f10040c440c1d400b04d49965980b409100c00c00010380c0103100c1c00030320300c40c5100745d022804240c103420422221003040d412890f055042500060140c0400c5007020103000b81e80c000c0182410480d600c82a807a400c66007140c060030030080b080c0010806100a411403210449056245080c070020b840340e100c07041031183c0000d05840b0503104e000c0500070f014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 406964532 1250 406963282 406963301
    0x1401093605010212091c020d031a04020c010c0818060c0304020414010f06020d0504080d08040311030706050106030e01020306010c080c2109010f1d010e011106150306060a0501021002030901 83
    0xa541303510b0a0740c214906854140d499183d948a0318412012400034030300d544820944a40150003070301d4a40310258003030b0040c82e9210700d001050b5a040c0c5820340c0d891020381084003280c4000101d5402011018080c9203001c0c01410b1000c0c8401e21050054800194844e0302031040211240c8907111480440c01604c080d003460001050740c0c00001c034a01000002200441e6903603400c80c1c3c81d10075500c8098950b4880e90243d0030454010f220481c20b064080c40c00ba030380143c440d181a038122220031240504581043ca41115020f442d00d004000719a1326000b240c9110705100700031491401c1c400006014035a06200050601ca80851709003203d02c014066207025074030004910b05200c0d01c2d01e458226942c0641412408148000004d200322445444224280811f00d14400c00d495001d1300155124519003030071504208904104240c04081805020300078050307000040101c12945c000c060421b000100b40900400c40038800700000c1c1c0e4000390740c03d03410550000060b41c0b501c80c2040f85026010304207 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 406965782 1250 406964532 406964543
    0x9040f0e0604020306071103070f0f0f030e0420070f02040b0402040b1b010603050a0b1b0f031503011b080a0f020a02061008010b010503160905040f14010936 69
    0x4042940d480c00314034203110718800c900780c0e00d5a136500f180998010810390155140e0342c2c000c1c49141d00081c0309a131000300c01342c02400d0000c620603d50350b81880e40c0094810450000d000344030f650315a8181401036440c0150102408441550000004040e0340145c0c90042c01202a03124a001907458a80c06030a00800103481959225164180301c003040d0b00c00e607945044203543e490340d40307074a00c010321506060383e6006c03010300400b9200392181a000d41d000750000c0d6080c604002c408656041c484000c0200c041540c038040d880380341c18a41f00050703091141145000b40d041c0b171000c0000348040000604490814201080241c540000343c100504003003240d1a4010300c00a908040c164000490602c01e1001c0c6808200690705e455103d4281c43e81860760a01056083c030119590400d02c0c0d001d844203c45626280c6c03410f0341e69000050650341441c00c2203956995842e8400b583c042e515001134050a1703800c038240420001951064947d061070114440c4412421205c60b00d07504415000855468005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 406967032 1250 406965782 406965791
    0x60c15110a0507030801050603060a0e092d1c140d15030305090a0b0a140f09030d050417010203190207050304090203010b0d060603090201140c0a0f140607090f05040209040f 76
    0x70102030a503074040032050f404a00c0c1240002450310303080c02100e10402e0094000000c003032801404101550b4090030541c254016918404204d00401d080e0340240d80041002c0340c1c8000c000c18015080c40390031854500100c4040d0461850b450300b00b80034096542041207030941d5180d403408134000400c11083c41601c0d810603e0f40010070b042c1c0c0300f80030302001c0300100e03440c5d2401a43c902c881001e42c450031042c140410045142c1080341005031002c2d145200d58010b045140c903442e80000707414160740207184408240c01007002c5c00748801078000a0800f880641c021403950034803b403000a00886403c0400c1e1094000030801c0401030248180c034014440c100c015900c95841d803884144d5600410210b104882c9841c20005c4c0e141e20034055404015010303107491103541150284052554841ea8015410703100f43c0c04d150001500350300340312441900500448846910703440245040000140941c0c00f0080c24100912511081d0290401122821030b801a0394180040100d00540f40d11902c81c200c80d49030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 406968282 1250 406967032 406967047
    0x810030602130e06180a02130302040c0807020c0a03030c0b090a05030c0105040201030c0509060702012d0c020301050a1e0903022d0c030102160605130203122101060c1511 75
    0x41d88050300340c0f0000d44081210b070399054180200e00104044603413000d1100804a100a480d0354000c0009100301ca01d4404030a890b41c006c50191068001c02c10002003611041180180d81445800c08000c0708580e030071140303491602c0052041d000c2c07040c058801c8481c480803820700341c020040901c149501c00d003500d4544001e00b0115009000032a0709a0219007492480c5003071510807811511480d0b0010102410440c035a0011200c20194100b2428485125000300840b90b2503541c103901c4082c02caa0f078a28040941d40b06042c02e448000d8001c198075400d080648200303046190500160080008001642c107043d41400c80ca450070105141d601b903601d02600013a20304c000c1c460280500d603503200300d544070f50708d076020301d0301b01d105001c0203038003480c02a10403000068842c4c12041e080001651080090031041d00001c0c03d00c114140300c58515180015855180b14411b28020280c03801d50350031340c1030342d8500b001c050104800381388000c1c00c80e00390304482900c201099010069451280c41d005454610 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 406969532 1250 406968282 406968307
    0xf05070207080d1e030e01150f0914010b0f0a020c10050d051f060c05010e0304060c1a0106170403031d010204080708160b0703140319110702100810030602 68
    0x180c0d000754105400703855150404a8004c540350840c012290f8000c1c0c20350007002a00710020082c0e80c085d0380d21552554106d91a03200884c2600001d8249504212002441d004426044824000203041c0c01503000004000e9a44034809607201c0000d0f0010050340d400d01c0000490900d042e030390720b00c1e40c0500c2c69449105c00c1541305e4003410801d501010204113036110703c4001d1b0b02150300c508480701e891108410512609215443c0d154a8078402e100201d18070a800b0562411030701b050304000e0010707601301c03c0542841410b0001c800700000001c84584254103081c030003402142e510080d0282c2030582d0011400300351096000800b002016400c2a0424185065031400303903006102c1c0390024420280c0100f0203441c04a0041145a0005896103001e454910000c049030840d150981c18014100203030061440e60b1001184900b103503035800700103007085c0c592000441d401c2c68203940750703840207001280040c0c59a2401c0801400b03d810312441a6503640f0710040007502c2c0c3c0d00b0041c13807140080ba001d00002c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 406970782 1250 406969532 406969543
    0x4030509060d1e0b040207020f01180906080102090f0d030e04050423010e010516050306090411030a05010207030210060e0a051012030302030414030702061c0906090b0402010e041a010e040f050702 86
    0x3e81ca10340c01d0065010050400050340200d900c060750009021050303807091b602035034040211010031140c49142565030100c2f201140d00d40c0c1d02c810f440c0d9400140d215028070b0b108000e5a0041e8048402213103002d025240100007180c0520b200d8040c0355102c003c80c00b880700340701c04045006543c540c824804401c04c82010702070403142650984d50341c02c0c10081080c0400e903880c122901d055650354503003142d48030810070200d00030242081d1081d2030001c4034181152414002e0510045c0200300269890640c1e140c0240351050407484813482514020003130080d40600b03040c41d40c02420481001c95140c0f2060450640b5485035480340041d01c40507044101010b8140d005580300d10302444008171010b1070410302a80301d1185000080d4090401c00c070b0806080060120030020001580b030010b40c00105a0740d4000f111045401079603c03021400800c821503038000444550040181c070700b40407001000221001946200307490505118860380b0450b07103501c896001007210100c000f07040c001c174102400c000c0e4551 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 406972032 1250 406970782 406970831
    0xc0f1903050c0a020307020d0c030209101503060b0711011101050a0603050c0f03150711120d0c21090302190827010c0b0c2701020c010c080304030509060d 68
    0x904010004440030580c01c03d503000c1c08201d0b00594038101c1a5400c020318444020b1003110301c02115100800542c41e4800d210344545071542c1e40c1c020990410f580f0100450248070319100b01420000c0911002d0892415100496800440a0768051092006076654404510a01039a41c81c000c10030005180e190011401c0380e000e60196451011207000703200c1c038007108441a981503440a0398600d11200543d1145134800740314501141400c40009031b641c2009c0c004909020300d040301046031003260405100c1d0882c3d0b0361840c1003044145408220740011f0410f240041014a659046800281802480034401186584032101e40b883c0061815070b20701d400c802d1441d0201e451440c071080c980d9940b000c840e61501016101c0f07142e010b60701d944100304058020000c00035903409006102c00e03801c1c03204501681d4013a001c1c800310b11a10140c002842c001084503254100100c503500603022031071240459800503050310704030395039120a10229469100f6101948503c502e0010407844040960b441e41c400b6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 406973282 1250 406972032 406972037
    0xe0604141f120503040b0c150a0b0a12050c0909070504020408010e010510060c0b0601120c020c1c0c14030a050a0b04020405010608040812190c09150302040605030a050c0f19 76
    0x4030b511940a0944110100702c0180542c0c070401060140c14140005407640c070f00d0800440d001124012480030524100307071890008583c0392401c0000624000c0c140360301030700a100008000c44807548441e0b03510001c061030180148c44501c00b007040c60b00e00f40800c401820740908190360312a0b44608a50080051512003070035540f8040c046181c000d42001c0410480d1400c0d0343c0d03a144181e00340c0741c03864550b601034040b50502028580d0300211120601441c144042c6a03000740c440d0020f00b030b0601146503050402610b45500d60500710001500403202102078440c0d291b1100040f01a0f200400e142549090004d8254499000c5040c10000c01c03200c1c032881280300342c50078445666101da0a03506072100f035800600490042c803044640c0081611011707448800110285e60900000d40b071281141c041c060800001a0440b0040c411320341c2004404a410126140851601c0e00d054001003003804050032980b010741c0ca800c040341c10301c190902661564500d0003096980d94052043c080031040c07041e42e50300301 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 406974532 1250 406973282 406973341
    0x4050d0b04022e12090204050f0a06090c0507030e0a080307150608030403022214090a02010e0f010507030c0c03050d05040501021c0203180d0605101e030201090e060414 74
    0x50f48400141410050b880311003820002c1140003080d2600e080d48408610300e80c1d42d492002d00560740e0707401000e00030001d01c1071290301800c03c03955030404d80c0c80c20340000210703609040345462669444000c48818580610302070b14240203180000b0500390266025020324400814904140724218240607000d4401c84c10070880356641d5040f40703480f40600e1201950105240c0e036a44074260741908522455032401c00000346400556940054601058990281030b0f03000d5030f0010115604401c04401d200c4040b10050315090a41000a12920032028002c081000312000c890800401d0301010000d10352100c1a15498004c0030001402c2e0f40061040324010b10540301110504940d500340e010038401d00740e0285141c204603007000740100302e140d04490f0700080080c02c040d020800710311440340645106401e146d0b44a25180c6580c0300f110401c1d0902d800540c0702102080140e8000b0307050030841d082050f41340241e507101c1e40002d004221040d160b1140da8403031420021110b042c951644401c505c0c1c84103d40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 406975782 1250 406974532 406974559
    0xa06020c150601090603090311060705040503010f02041208211509070c020a031403040f0b03010608010f08070e060f0301150807121505180f03070b150102060a09050304050d0b0402 79
    0x6601d008265001804291801d8080c00700920035088850854024241007051112380209a0b2500b002201c0010018030302007014040346c80d081c0038140304c0d20b0300d8040075420142000091550070421110043c4502000150320100d0000ca4242c04500480c02903042151b01d841100801d0b20652021014410b213000d00000302c0302070042d203400400360380107051036010394116950340c0c141c222140e13011822880144000656620035114a41c040d040f41041035489524240c4058120001a00410a03005050200b40148140014042c0c1110310660003001a84c0318140820701d201c0642d0545078143d420848881c100c000b81e10b05c2c003c1111812022210215529503d25068440942c0010f15080d0040c401034072000d034039040789400103007202d440b6440081c0303041410b203060407440e0048459080424440f040c070a80aa403594442180c10742905c000b15140d0000b51107510050003c01c005a581280c001800401c0080d034002c0c20f000303441c52a900203581003819000000700d070100d1080d190400c800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 406977032 1250 406975782 406975813
    0x30b04030809060601050c340803071202070503120f1b0c010807020607020a0f14010603140c0103020f070b0709180b03010e0c01140a020f01020a0309030e03060411060d0e0a06020c 79
    0x1c071904d00b9010080c11a80c0c2070052241e0810340103072881c042e2502203a10b8408c80780c255598020040ca84003000b180d80358102d150088030b2400ca0744540003950800c2030104002d40340491905224446650b0721030b034640c0224050b440d01c2c000c8004c00304c5842d004441c2c0455107240020070903a001c0c001d0300c1d2604030ba600c1d03000403039a9810440c0c000006800c1200c0c58000500211080c0351040e01c10134400e0100c91040e04881c0c2100c449071300c151400e401c0b042c105041403c0c00d00201010f14002c0c41c05501e131040d083c00c131520612942100a0120300600000b40d0242d03c18030186025240350b204d0252100307400200038002d0484217024912a501c0e0082d06c0c81000030000c0d20007030709207040e1a402000c2c81e40080d0451035400a5101c001540207000001007070b10428401081d0140c40e40d180000d00710903d042c0203010300d0301400d24901a501c0801803001046418000e81c0821400701d41e001c0d81c0300240041d000182c45030602502a0b03115041210007001019005800040d500302d08031030b2a1604416003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 406978282 1250 406977032 406977037
    0x21e040302010201050f061c05010b0915010f0f02031b0102070c090b010f05091e01120e011d031c050606070503071505100f15110a03120e01020406020c0415030b0403080906060105 79
    0x4c1c030761003500d44d40000c20640c2d41c2c00c201c18075503002c0c0c000001c4284061010921166080b1040441c3750880000d1268642c0c22121001429090745081d44204400800103540da00c81e011122034183d040b050580d070140000d404032a1007551160a1845a07503440c40148064035140c0c407560b01203450b01230030705a803a2296003500c605c00c100900100f410141803080b0303003140706400a0a030400510025051140c0c0030740c000c5160002205000050b125520710b0640111a40141550000e800c00c02000c19000ba207204071408141c400c541c009429103d00001814502c03070301078002c7c503601000c141c1d001401200710040760456000c03d018882c503950340241507002c0311503029000700d04164080501030100b402420107920001800d01a0030124035000052400d40d90410441c00210343e40d050140e80d0741940600003500104000035401c050030706202035110102562b14500517580c824868104440705031002004641000003146d80e4142030800429003202211143c1c40b034810500421840d5118904 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 406979532 1250 406978282 406978291
    0x512011b0f0905060918090604060c050304020f150d0c0e1c02030a06150b040b03070e010504080a03180306050903031f151809110c190807030c06021e040302010201050f 74
    0x450040c0d203403c2604010180e0010705031150400074500071026002003c0b00060302a00b0620020a00c030719045c60309005030750303400c154082004410f1060000503100c568100c8080002280c0300186032108109071001409100707120003881b800d10200030100c40e007184d001892040180c0384d68041c29901080d490702440d148100940591140e614040452195409101001180302c0c40c400c101d603680c011800c0c10341268020816480b40003052001c3c0c00c1e080840301126120a08099040c0741c609450141c6502d5080805800d202c020781c0301d07101c0300c0403001025000e10351048081203241080e00d42d00da1340343c004803082f07031071402400000d0506a01905032507003240c44c42e440340007050260120440b05001078030302001c0e02c8a4074400110b031410050280301c25040802c000c030b81e10b8a241500c420b1403c405051100c0d00c10b140c051401c1c0218561904031040b090b0107051508403e00c0a00e4904000d1280380c540280143c81d900181d00020000343c01002168000da0080c000e984805c003c545e070200003a80c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 406980782 1250 406979532 406979537
    0xc120e01090806091c0516080406030506120705060702040b100c0b0c190318141b18010311030a051501092702040c0e06030a0605040e120715060512011b0f 68
    0x51010030001030981e01140171950349401402e182080e00c0c40a940c046d54481250400750210341070101c0d40e4144102d82e400364003114944024540c04517041c1c0c481c500d6000d80c070700a2030001907103000d40d1240c0d080b4178900e103406898020314075500b070780040c03101c0c00403a4100c480700c4041b000f04400300c5403003056540142ca04105007018a04d041410380080c8013900a0001540030700d45040003240c030b80041c0c07111185540c0003500d10751001c140465540c10109803014030851442403502d90003c070098100c1d06481c3d200c64100c098074010000a40380040d2100e000b020f5105460f60920340c50a41c1c60524100d0b00c0079001881056120048000d211440fa000c59144144003c00e91000d441d081d0400c61034410a8200341031a19010780104602e03038401c40b06580c0d03c54440741c041003d03040510412020010070070250100800e420145912407196010107494886084d0000d003000c0002d40c0214014140140240038941500301c04501070090200780340b50304846801c403240c25600510490420140c0ea5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 406982032 1250 406980782 406980793
    0x40507050f09040b01120f0b030105070f1209170309011e02251407090902030c090103020a061d09040b0708100f0303030905031303030c0c080a0213050402010c120e0109080609 77
    0x42c41408000c010848207641008a81300034241c1c290031920034150300b491200c0001c00e04000200526080d210b02074542c908001d50700440319040c692001504103003c1e02c40001003030320f4400e814150a102c9003903210040e007010000900210600540c05240311350b0903040590840f03038400350b5810480c080c004161051030320048200190360f041800b400c5025100d000c41481600012800520700760007a00000d9040356107041b0174081d072504000042042d40102c9500a03150304642c0451b52450700e40c45440240804502c1001c040b0740d00c00012800e018020340b054402d450123040c00800c1c0c3d8026036440012940301d01c041890303401400e1540c420f8520034481c150300781e8a1a03400320010301d050712055070f10340030a0092840003072414032840015400f9564400f07907405682490300e44100c10f640400590b521205805006031550034007070b8420396803104005007940c1c4500050302d04054002d401480440c0c3c4422480c8081d802150f03050306a0400e0342c2e007030b1004c3c3d1104c0d201d5545903801c4d00c0081320743c0d128 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 406983282 1250 406982032 406982047
    0x3010911070812070c081b0f071a07210507061505031c170702060711060105031b0103140c03151206160903050304060801170303040c0618030b1302040507050f 70
    0x2d0f00c000c950440c040c2d142c011008032103a1182c010a801a0321580b030100301600400d01301b81f00030491401c10b44a0407000d000e01030b1900003000880c4140d1200c038406202c01007000420301099608542200741100003400c10202e031090b00a0155020080481e00c00382303010411900c03940304d1401d2006a420140c02465001003a51980740d203013210b6020001040484d40c03000350070750400c0c10841e000b10140d800800d8242402c08004c2c00c43c0d1000109034649a001800420407035500180180d08842e401c0480300300140c06000480c080e02c24407100d200a40198400d01c4440c091400095100e41b607003501c1008079502e1401084200c91a140441840340c0c091004641c0160703000c040e0303440d03c00540c14503180084e540daa810f81142c025502070008500c5c180b004001c41e40d03905192170030745200341c4003451071072620f992034021140581c05280100011403035540b07000ca04840000000d0760b0026403240d840e16080f1103103026501494012401241000080349034640210181c83c6581e03401040181482031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 406984532 1250 406983282 406983307
    0x1802070c030b0c070501060b19050a020a02090717090706030c030b210304050a06030903030c09120615080f0307051005070903061503080f03270a03030e0a080f030109110708 76
    0x9010f010703040f4858081003c100019400d124803c010a2051000e0740c0341c0b043da818485109542030b9981d000c0c031030104881d0f4440361340402c030780074200d0341140c1005040e22808002c44100ca108051511810382100506c10340110000d09542141c107035550900107182c1d1071070118283c1d890420000c1d00710b40d50f80140c2c2175400c148240e02908121800803030f42010703900d10002d00c00e6292076010070042941c0e42006000d25074180510f4203400183c2c2000c0c003e483c03030020405021403601c2c0c000380c24160703203d00d001c41204d03411260500515085044401d101c138050199500c9a000c498200e41c6807282c04280f21559085d40200e5120710a1500e8001d4114510307110800648804005000e08000c00c403004000140103001511494a1a10a1b10b80303a280c002001000418503000c0b15913800400d803004031900c0030000302c80c0c121503032524020901e440c40c4c8030701d83e01d00700307010800400c000b00104001c641003d04070b0146040300d0310040103200203000b01017010110310034080c014044810410110001c81c9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 406985782 1250 406984532 406984553
    0x60b040e04050102070203190317061507151a01171635270d120603050706050304030206070e06040303082e090c0206090a110105130b041802070c03 65
    0x5002e40d0015181803900d90001e03081c088820008465040702d6101c440c14560301096203040c5001550b01c0e01e01605101000440004d408101c1d000780c000001512010400107010407540305d0210b6800f0f110503090301c40d6180000c00400341c454001400203810322140711465402c14003c2402c1810142c07030b800c0800b0b0480f00c41820009031061048007a80300c181183d212608810820302004040140c0c2c107280c144a00c01c2074404c2c00001c0c0035010444001800301d03020610154000040c20202c1e80c00900c041100e0241c200d981c0054128000c100000403681c0d00103000f14861442039090358911f5550243c00e8902d41d00000314941c10100901c01400000e015504042d04066802a050400d00105002301d429010741c01d01c4008103203e4180130449000b15001c1e0702442021800642014a041c100c1ca0740e03641c4250070041d00e815005000701c12030303074080c85c21618010340e20b500f1561059100d06100010740c2c030500c03403017807440711507a040c01b8421320074426a0700c425404295900000d01c1c40d1035041940 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 406987032 1250 406985782 406985791
    0x1101180b010b1e040b030610020a02090c130503061602010605030601080a150b120a03030b04020a050f0a051605060709060507080a03050c130e010f05010504150516061d060604060b040e 81
    0x86080580d40f0444900440500018203440c1d0509540389040b40500054481d40340c842030556015000204c0181c3c2c51511460b0f01c100c000003420b488245540c0303d0100e11406601c020b405005d0781090068809241019020782e8045030000d21109584105150b941c41c800d11400490780c200b4021795000940d6a0b100340808070b412400402c451050031b0000e403414510b842e0788044e03030340300701c0c441410560140546040080111030841c10442050006403143c85407842e815607040002070400552405a800d89600c1001c0c0218201c07907440c2481e01c10b0b034031481070b070380c06010034158203001a98901c502c0031641200e0b0301c44030082c106010101d00341c019200261814599202c02e000150040c001442d440380200340d148030304507055143c0f929400001c0c41030f41003581000b204000a210108031101d101d0303070800003442c0c8180d0b24000c1740075803e00c444140c280200f07034604060071686103c0c0e20a44190041d80c6c0c00e07049d140c06407502e004000498079588141504c2c400284010002c5859910035030303901 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 406988282 1250 406987032 406987057
    0xc03030b030a0210121401050112150308041d090d0f0e0a05090702010204090b100c02061804020d0203071214180a0506010305070609080d050403060b060d06061101180b010b 76
    0x2ea0896000540d07114904000d10002403183c07188403c6030025005038005100c401c00071131650f50400000030702522240311291249900d9480c0d06142d48850b40c0c20343c00071a08040080e032165240d1424100102803880d01700300e40c0301b510001c1461b00341c01040c0c8282c0c0b100b42d51100b886000035048180c42d030a1200a82c254403008000001519494081150b44030710301c15800160b80d070b820044c5010845840c0d1080b180110030300c1c4920108290843d884007891901211625252100e10500015081c5e1640900b6005070002c00d400d002041103402035401104240c43c1c0c04a000c118615080032110503218000d800000100894003841e20341d16030102c203804a0040d1010080c05071601841c11070203a00031141a072000c01c007000003c1d2310140c0d22024010003c0900040c0c4c203240001081405140000fa00c66659416544045e55845003102c10300c007074010080c0280fa548810151003940d055840003c15400d1080b0382020030f030ba40c825030752400d0303204030a501a46d013060b404034105c3d00050100981e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 406989532 1250 406988282 406988293
    0x50106080a0b040e060c13120c03060905030c0d02070e010602061b0f1b0a0506060105040b0304060c031b0306090507230c0102070b1302010e060c150a0b04060303030207110d030c03030b03 82
    0x1c01404c28045c1750701c103a008110305903540c2c6090011102002030303a4024011403002501200c0002c5a5001c0201200c2d00001c000c2a1240030b03080150640c40740f001d08814502c901c1c01700312085074011030700e40c08452101d81c2c0440b0a0faa24041a61210000c0f82d04407004529616180b007458a03010261281030416180d80f41002c000342040c0d40c0810100001c080726500122112007005400c00c00d05500c80310a103801420246440a040144d000150000f03211356180c50515503554031039800895400c03402c07c1c0500f002e000c0b03160301800400e03d9000b41e60607913080c100080c00711400b0307010782c410114503801580500710802d001f805140d000840d00784007554081007040081002d610216010300344031000048001928400034100100e00740100b070041c50107201c083d86210b0042000e807881401c0028180003039a0f8511900024a580e50340d0b194043d10b02440401032640c160b002d45030303240c85a0404051025032408100012801d400020000745840c4061741c0003c5c030a400860203100050101c6a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 406990782 1250 406989532 406989551
    0x6010527060d050402040f06061b020102010b09190501080c0a031e0c08030d20250203011109010e030309060906180a0308070b0f0601081305030c070f18050106080a0b04 74
    0x24050b034020001c00070495281e000f8403055181c10b00c42c904414050103001c12820f032415030050440703401c1400484001b040c2c00001c1d802c1da4000e4202c40c1d41440001c0c110522490280e181c0344091000f040000040b92130407001049101000801d000110401452201080d2450307542a1042e101c0d805084202007682809000149010002078007403c00c00f405540c80d05000903081c01150104c001d004180142c19982c00700e0b0f01900c8040f940750600c541901205280400d5101034401c0c02400c00035015842d200f0300100248070500a013103603850903610304100c01409010150360f4010505456807240c401c0007d4025454a8801032842d00003044031101e030348029500045a4500c194004c0e1000360002640307030200940d4030b52850340401c52081d229a10b0502600080c0400c1004180040480c041040001840070030002e851002d007002e1b0450300b075162111418101001c05104481c0c65502d85038115400312114020f07181600c815607a8070020356603a600d207002038140004160f82003036440c40c840 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 406992032 1250 406990782 406990789
    0x1b06070c0f060306150c0c051507050a030509120c13020313060e0c040f1812020322031221110f0a08010608010803090a0311040e0a11031506010527 65
    0x10010002c50f107001800600c1d100c0f04900350041c2c003100d0001c00c0184203042c8005614401410280c1e1000d0307071406596001032544001700d1190002c003514511608401d40205a8014001c0c811044140c45655842401603280d0388e4402980c4842580015a1800210080c280381e02461340045c1d01c9042d0040740e5a00d8071268211501030307542e2415900300c1c82c84d528050900b0f0082c07403008402c11008100d14051001042c6c124050750b2030040000020540b80e180b264070030002d072024500c400081000c006c5003404000f544510511040b1048848500c02c1c4c0b40c1075004050101c2c1041520300000546580c181d05940107044103451a180da40d010b101049000300394201138a1036001c1c0b601c1d02c0480e9410650003802280c030580c0a8500e43d801006034050b0380e20740040903401c41c0e90018413580c081d00c84c48000b41c0030305110b0722280d050340308401b8940c0074480d26690035040c014050301541c10703040442002c24440c0754112012404114200140038140d5600d43c0310f4075420008554148000c3c036241c001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 406993282 1250 406992032 406992059
    0xe04180b040b0a05060a03031b050c13021c02030c0403060b03070e0708060301152106110a02070e0708010609030b0702011409010608010b030f070308180310140601021b06070c 77
    0x7940d076802c0000810440702078502c43c280d0020f17022513441e59114078603a001460304820040c0790f900b4106a110f140c0420408001e050541c0d4802080da04090340806942c2009402c0f594000c5001411140c0c130f005088011710859002e0980784040510f01425601c1d90000303040c0c412442031701071050307401c006002041501a507000b00f40640e00c030300c40750500d40209402d444080265240014010f1020050440780c0140c0c0b911510200030460a10060f6042c00d0b0001c160400510300e01c1c6100280070401164042002020307a400c0b950b11031000d403180c0a08a03070202007401000c020071000d04d010b0011613242a82c2e00e40c82009840003007110200d02404c001000000d9a0000b02c580d121142400505800e0281e1048944158024403c0c01c40b10081c1d59650702880c44082d00704040040c1d00f8525116802e04401506000b03030403074400e001e842c010710000b00401ca001103850b070103520101e48203600c0490418101307202c81d0010801e5415500c00c104071035116002c1103c03400028500040c41c03501d41104c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 406994532 1250 406993282 406993291
    0x60a02040308040317121003050d17072d1713020603061c0c03110112021e03100807030f1109060a0302040203191a0321030118020f03040f021002030a0e04180b 70
    0x110509102e256207046840c01c9140641141842f0890180d00c201035900141198000340c00d00d41259088141d0075103425040781d80307c81c0b000d00c21030090b06443c0a90071040c01207035030f06410249010340e5118031550508031202e86000b5407010080000c0340d001d207030403000c8680600880d01c800a000f8515035a1006110399580110707400455101400707403c0d80c00000141c1c100e0349a03941545001035031080c802c0d030b040c40201590103080d40400400d0204940e00b0029018120060842c1d14494803402d14a0f80100001e03000c03907000208001078072040c100301005501a00014111919890540e4200300181d000200403804041c0c3c1c5032000c0c1c0b8041c0e224003d034845c4112040010700400181c4040c5814404055100c42044c0050404008140b500e6030440341112a1002e035446066104e40c2c220000e48515100c9016a820120911042c884842100c001c0d051080f00d50840d40c412541c01a6220b02600400c5400f1643c40d81310060541802d8100d507549084d00160000c0d800e54965444603403900544 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 406995782 1250 406994532 406994551
    0x5040e040b0601090b090102030423031203011e0806070c06230f15090c031f0602011b0306080a0204020708070f080c0609010b0d030c15020406050903060a0204030804031712 76
    0x200340001942c01c4800080074085082c111881c2c034a0100020703640c0cac0b19a2080d281d0b407020014000e02a01c075150a4031a01d007800a0640b41d0440100c484043e90f80c00c203014082511020009070041915004030103811501d20038050310050f0365000c015900140604000d0b01c09035100c15495071210f450700030600411807800c201c0f0a190030300100020445000404421003194023101d01142d0f907403001c0e0050b0f405140079100766034030f6031641d4140300a160f600c510801a21250400401d0303c58041d001821069090b52401d00070880596007103056508900c03e00b441c580141440c0000350400f0740041071541c3c061803600b0300e415815511070309040c448407015141e403003010401008146050200c55003014120000380050140c4100149030020310803002018048040349030b2080001c00180640f4000101c0c07002c54465039901c8001e09a9802010a40e1007400741c2000a62182401e100340c805581c0c000c61641d0401d811555101c040040003200c40d07100310000d101c0c03143c000c0d60400400d4441c0300f905 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 406997032 1250 406995782 406995803
    0x5071205070b0405030a021201090206160b2401110703020603101a0c06191410050a0b040b0403061104030f150f02090d1e020a031211030a050d050705040e04 69
    0x6003405401c005094106082c021410070080100380d0b400285048540d404466915103d220580c08a005152900009411007c042800c01c034480c03100d0b00c1d0001d02d078001c6d0820007441c1d8610020064500c2d414580080342440321202e00304075441100041d0392881d0000c201d4581c1341e1a900043d00741e40040780c581c0e580454940061008200c025100000031007019585420036444100c165241d100082c00180700035000a019180c1d852a038200507102d800f00741054170907083c00c01040d41004060700035140142002c0500151a15003041203400302c801e007024490070b0a08559400d00502080c0c0d030741e101017400034800440481e450508100041d880b40e8078240c1050442c10042c41900c81524003410765900c10302a240241d29105c6501494039881760b82045410305101c001003011003480030194111101c00800b008000c08040c1149285403d525500310341d404100c08281e6a100d400e0228001440030702985506006607004250001194100181403640b120075440031800102e40c29212040f20 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 406998282 1250 406997032 406997069
    0x31b0f08070f080a030c0308060d081209160503190203031201080c1c0f02150c030d051909050307140118030203071202031303170c0a0c030314040312030c0c0507 71
    0x6030810b90008214100191040140c25100a04548841c90000d000d00a0001c002140b640d80e2031900105990300004013500c40540502c0f20360000400c4454148074800c0c40545401558688000b80407240010000c0c00032a9041c1c05102e01d40700351190032030b0140b2042c049141c1d18845100300d54040d0030080001c0c10240020410811300a00950707002012008540d10710000c11181c501005003a9016a402d408020f868007841c1080c1c0b10702e0100d42aa03000205e2804402c80140c1c03c807900540940c24544800100a03039504100c0e50039080c000c02e20340c0100700840005010840820720049020000103565031080c3c1e0034040086200360442c0185c0000941c00d04202c0c00410202e0b003158180700460030180d890031410311801380740c00040c012944411011644104c2182103c41c03080d90f071011f035000c00302d0500d40704d00d190303130a400114040350f800c2c2d0420714034420307d0302583e0480c0c1d0001c1c140220610300c80000c0d401444228803601c100a6135200d880d020807020071403030000b4040c061001c12820368 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 406999532 1250 406998282 406998299
    0x30405160608040b0604020714030f0d0615050912010e0d0806010314061e1306141507020d080a201b040203090c040c260103061404030801031b0f0807 66
    0x8036003020051050010500000c14003406005502170020780f40107076641040e05015480031080d419000c1c0510001440c4072040c404c12010302030b172560000c4c051208546809008018000c80d81c03084002540034080c07900c1514100d4034100001d0051341c000104290f01a8480d8140703201c6110840c040f54400081c0002542d00d48650034410b94156034030402410540005081403248000d103917803c13220030501c0d000e03d585407850020701132801c0c0d0b0708220311540d5014802600e1a070340c0700c0030703c42d01000742e07000000c00c440022500340300e5001f0440c6040a80039542c4500d01c1c1c00c007104203803c1200711a41014003c803101c410b24660320a000003004000c00007010340150204106025010354018014405600c00000d1410340742542141c011070002c1c07006504a900c0000507500d0600303403807001c212499115402c400c180c1660700031305083c4400c000255844a140c0400c0d18001c00007001c40004002080000c82110101e07c04403101c0380040790b03100c01404000340f150f004070003d40c0191508200d00003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 407000782 1250 406999532 406999573
    0x60204230301090201021507090f1203030c0503010803031f030503071a060406060207090c18120b0f0c090409030201021b0303010e060306060d0602130902070501020a17012105010908030405 83
    0x5400718020302440c1400e90000f0f45448600d000a11f815001e500450700320b600030404817010780000c010302040c150341d030105e4400c55000c54009501003450701042c2c40503248101c0489050714664001140b450304c59010f42c644140308000f541c64131545d10321000c000107d042c40140341070350045210565451040140d9440820054a12803013503150a4003000100d07008190201155010080065058180001910b00220b4080c1c840f4400e180081d010503146440403010110364090040407031707161790304078030401001420f0352403075486481840018114a055040313205114802d1001505121075441500f011500c0303110524116000070005122190449101a41c0f04208030014a914107001010403840003000c6409480c1c142c00060600d0000c40c000c000c4001000011411551400320781043d600030f40000e50071800280c2c42c05480c5015026034907030a4185d940101c41c010000300c06101b50114010388260440701035485201400c00f290017800a148210f00600180c00341d90a00031850b04001c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 407002032 1250 407000782 407000849
    0x215030a1d190213050c0a0305010f050108010302041806050a020702120a0f03080406060e0403111015270f0b0109092322050d110a021302070c03060204 67
    0x503146220500020720006802501441e00c94040c1031924054004143c0d000307074030051003040c113007090244560040b0745d40090a40d07101640d010005662660748500101c40030b07104003400104588014005890300303034085011107106814040650100d9901e24080c0c07102140c00d84e611a070301007114000d60901d5491807001010304030251079200303c43c0d07580d0b03488207411102c050100811100007404102e0241e0100000c1c01c501059401c01d4603040c40d0041c410503001896403058051070300002d1510780c6602030044001c1c1181040c088144c20141c000c0c002e07034001e000c0e00e0342c42c0e200c80440300700101040c80380301441c0c0107426002c91410400c1c00050520b030070640c0406040c61500f10468902d03c19488100c081c942c3d0b0418107c8107444096000d0b001c545000440d0400c00102c01070030342040380000309040319060343c2e103454107051510390015807a24026100a50007800802005481b1b00080d401081e00501c40c404005e50146c40703032985c00c203c0e00250005801002224001b00d006000542c0c0c04814 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 407003282 1250 407002032 407002061
    0x31005010803071e08040305100b031b040f020d0501030609020901060212120402150a020c03010501050d020a0b0f0f07050309130207081e0c160f080a03080c13030215030a 75
    0x140d501d45070510b0350701d214009025180c07050102d504a903d40d0800c4207006030380c0d0085100354855441c1d041540c0c84032001c0301c3c12040c2901c0d02c05140c6180c02c0100d40300c22580d00c900401e002244100c0244805040c0c0c91401d0000d4a600b001506107203110742c0b0659011f10700500000541c3c03095031050200500041c0c0001003503600070082444800c2c0c41074101c07800114802401881030b11640302013210180725003914228884e010a030050303161360008481404020032002404544d98907820b2041201c0188006504001001c40038881c042014006004056030540f100d4a0040c0180743c2c0700c05600119000c50fa141c02c0050003210b1480c10012041c40c0070071802d021894070499544190303461080e00d402c10010030580d001d000d07504108501f555003000c0c03000181c490304180c400908058040034040d030b0341145680340d408509564009101180c3d15403649880c0180e0f00d075000c410810743c010411014103101130200100060701d031a50441c5a030b00f40907000a869042c1041c2c1c49040c3c40e07022111290 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 407004532 1250 407003282 407003291
    0xc060503010b0301150302090904140d030b0609063f1b070303181b0e090a030507230319030c0f09060c02040e0607020f060a14060906030f07140310 65
    0x1040302c400b203d044500390035203101094000d000c00d60107409040401c60307108541d40c0411081c0a040326402c0345514004040c1d5a800544010540446038482d204031380011003403086800c64144000200900304855040c604042c0f00d080c00000905010040c4c8130442c58181500d0680050042c189034016040c00704420607240000f1000032140200c080160801d61502444a040da1040030b04682c1c0e40d810510211070014000e1100300700c00414400c060001441c0d0f00022060480490f03107a078070b10f41c143c0d42c05203018200d413682800b1404500302091001c2c030100e00f4003035880081004000403007504841480210301080040c0407a59662414428411060b41408410742d002600000380e40703043c18181c04090045c0007180040c100280b8421681c803030982800103c2c0d8000440d1021101145c00710303a80e40c0c1d1514549070030307a001101c0d4140702c030b20304001080303561810300c0305039611060107030848030943c04d8541c01c58685400c1da40680003d0601c3d03503480c8075905043c08008186a40b9860612 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 407005782 1250 407004532 407004539
    0x31e010e0d023903070b09100e0604052b050a120c2301181b1e05010c0303020f030a051915090b010201020c070810060e090604151b0206040c06050301 66
    0x4003a96a603007442d0380a03046440c50004940048030703c10111801404540006403101c40003078043e0700c8549854402c140040004131442c3c840c00f00c5400320700380a4101344c01d1510341000e208550b944400b624156003903d0342141c0103a481ea10140b480203000707200504840ca00d03410050f58144204c0b4005040211020707000300410b071a64056001522115003000314107403e010054018401006480003442010030039105105d800d813050605000c920451503166641c03502411081c0c046005018101c0031000c40c100041d40c0608480c05c01c0c107002c2c3c10017500d082e5100030749460300d900440711900400d0b5540c00b4011410800c8861008a001000d8208a80700001e0201e480e481924812502013384039601140142d101b034060321a8540090101d941c100e450b602c5064032629421558119140b420000182ca400e080c0f0490b400380703215078003420725500d890301e510651044400d05001010f4076070f800c901c294505100c40e03144902c171a42c013401c11400c16181000d81180c4c00c2e804001000024030060 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 407007032 1250 407005782 407005813
    0x90f0b03150702120a120518070303050a020a020901171507050d0e0c060304200105070206070b0601090e0a0c1404050108070c1401050c04050f1906030902031e010e0d02 74
    0xc00c01e1041401000105640d094401c0707281c05609600c41c5402c003404180200038a4020a40c030300b10b9510060244610390b140d031008000384455485000e81e542c4450400c0000c20b010360003c043e400d80f94415555603922030340104040d0802030744101110041e40a40740090081880038610f1000210079000b000d0408070070007841801038626460400d0383d107070186100c030703102002030034950140900159268601303810201d01c010340082c80c0d00804003280d00001c00d291320960481e03120b2a03008110508241d015100c0700340b1030b10000e01e00e90601c940900003280c40d4003506c5c2d000f841074105ca8404610748190441c001e0805d070060703850a1001c00140802d0145030b8004808030351000c0d040c40d041744200d100d814110010400d02c48540d416520304803c1c071400741d1500d0010400d48070243d5a55010f508814203220400e0400700c003003402c1d814010402c1c040c1620076001f5410041c00182140c4400141504840000d400b80c69040110381d501c124500d4640700c00e210380784070200c050018110301c50905010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 407008282 1250 407007032 407007043
    0x180c06030c04090c0504080f0d0e0f01030b041406030f0606090c0901030b1315050d0209010905040510150f050306091209030109140105010f05090106091a040e0f040506090712020d060e120301090f0b03 88
    0xa6105408074bc486120740d0740300b94002c828010004005210120440340c00c01c411000a0fa00d460090241c040d9080b212600001c5083c000c5502400c004da2a13982c0e2308003d181a040030000341d04050700d4840c0c02d100c96550220140510341d44001c009a80400d80e690507900c02e1050b403141e03003c0d8402c080c0720b40c05031b503c5001d0503044032010300c00458150780ba490024180211060b400c01c61a1400b107544003ea00242444001e50b4582030546c0815030f252010150f443c201141c180e80a0362043d0915000c0600d1140980355401d4080c0000c1404007079641d4403050800c0702500107a4130781d0b564004000549100291300300420050300e010322030754109440240034a03e18041ea40c0400c500c0705080c0f003c52246411203005000c100c02a10107410b080f1401c0c03030107040545041c0c2e22441014041182c980300414110300b103031641d201c0c08120040c07550a0101c0706120301010f403442580d0301030b00408440c0a100d00d0340645240082281c4d44d605000d400401c4800f40781001912516006d641d00258600085 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 407009532 1250 407008282 407008307
    0xc100509040203090a0206040b0c0d1d040b0f180a0b010c0b0c0f0f03040809090a0e07050f041401060804120305060f01030b0d12020312180c06030c04090c0504080f0d 73
    0x70301580e01d030b480181039403512407040c100a401001c0050001000e074280c00282149d511072600741ca050303060000c0d080350549231012803480300c141035070700100180c41d1070380c011101040c01501c828117020b080000a143c003400d100490303488d240c3d09ea082008403019407050803501c181c2420725030301091254036405a0240d0082c00c802c492075000070045595400c1a05448251800080e010342d0703464140740200722500030081c1c15000d0504440418143d08c610701512040329421001014014036010401000442c0c010a05801c41c2da2046041000e140c050f000e90f0103414203403580012401c2624050380c02801544c0380104042c500014040142c7d240c0c5401e0640201c02d2a001c40c0c1311900400103041c0c00201031004000100008800c0c3d03280c0d80203c00f4000c640030203046980d803580c030000d01180d12600790328420342640007000c0c802032514204003c2d507000b02007400600d080c16100d50742142160128045030020400105040100c0d1104018217490400300310090b0980700c01c02803000d8040c00c006a03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 407010782 1250 407009532 407009539
    0xc171006020a33060602011d491103030f19140702011e020f090907170f04020a060f140c0f010f050a11252a06020c100509 54
    0x1000042100c9052005070408030542e80000300141500310044003c0199204245c050350901001d04824400c103003204101c3c2c00b032000900461010710408280114445200010341900c3d048041c0720812541d40c0c5d1903040841e03070701d008080c1001c450080c10401807114070880c1c99000b001049080031807281c0c20f54016010050151426503581c0c8100003034402d50700c002c420304069204010007294150003440d0503040c03881a007512040c10340c440300164420f90045116000041001c810181441007007141e00c1b040a107802c0880d090b10541c6030101c0341c0d0944451820710407050a000940c58030240602c0207001c9070501002d4038100200280c00107012503140c1c9a910004196a42c001800303200cac40c00e2940c20000200308492080c02c100d40184010b4882c0c914852409000c5101c1c02d00d030000302c03400c1c078444006002c564005000c2d0f000358a40d000b2400ca481d411000007905c0c0c01c01d80b844054030200c0410410203415800e041009141c0b562116030188101d0081e94210011900003045031041a401d6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 407012032 1250 407010782 407010803
    0x140d0f020d0809030d0906030c0c050604020607020109050a0305030d1109030613170c0303090d05070309090207050703081c0c021209061e040f060f03050709120c090c171006020a 78
    0xb420b0110342c80c007407640842c1c1c02d4001c0c8031000040a0303210b040c2c58152400750f2810001c8105036002100da008690000034129440300d00403d000d40380090103001c2440c4149840e405150b100c070042500040340e64800c035844d501c040b5a82d56041c1c03441c012106158950029241400c5220340040e5840501a018011554420007510103010a240011840301c0303251003020340d10104600e450340c1c1c95100f168014900d001e25440f00403624441c1e41110381c0a9007540e40c08441500340300701e00300298400201101c0f68420301c00000000f401c080301070301608d43c903900030111417a0f559070301a040e078410307640403c119001040f45221550542d0184cbd031540c0300503214980c030340011480408088803106d0903a8217044c40414001095912400100152110781d0b0300c10348420099501034060364400c3d140c00c030104494072001d2110440351444448804d002e009240007240d42d4008440c129a0a00c039400d0000340d041000001c541401d00e001c0f60044810b801201626203440c3c402034032483c2d110402410580074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 407013282 1250 407012032 407012059
    0x527070509090a1d030301060c0b0f0115113306030a12030b12010509060106110c0105030402040b030a020904060b040b0307030b2703030901092102150c0d09060501140d0f02 76
    0x640e119034184c462404112950781d612101d01030100c0310400130859030340015000040c04100404041030403030303440030310300010540c0300d10042c0d40110070b0046140180c0301d1038032508070381200c40000a0301107000800d80c0c001401c400c017030401d203040000c007010300943c440c044a500180182c18100c2c8162420701d80028254034075000904e1101421807050415030030001404aa03100101ba0241201c9150b150511030440c880802a21760100c0d02080c0c0c0450002c1c0f00042c003505041d0002c18040c00c00405035140c400c134a60028014a105880c00ea80c05995288010300030f08082c4100100f16208800070100c191440d92101204100102a111852100e551222141e041c1240b045007140100040d00d460303161075184071380201501002503503004140e50a0160b0340400c0220850580c0071980600b40d4014440004030202d480a0028061990100888424681103128480c0298030510002c1410751500c070206514501180b08503110f00d16600c6281c0c0000e141820540c1c202e581a500095480c40e03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 407014388 1106 407013282 407013311
    0x506010f0c030c0303020c03030a090c0b0403050a060902030102120405011a0f0616030509030f0109022b14010605041409070602120f090a0527070509090a 68
    0x101001808003003032040c0d40b4241d05038040e0034050f240c03803e9030951f82d2459004940d154401c5564074864810040404000002082c0a038082c40c202801c549506456030400c02006040ca0342c2d4100100441d10b0a4060790710000b0740034004541880c1600f8280d01038a180382a091200002c211200710f80e1a0851206494581c05000541841d81e40030040c4280c0b2025130307080d0140042401801410b607020810450f04101c1440003040342c400a10501460440080300038444040c070000d4040180c0418112160494000c261156654489010345006009075007041c0d0300182410301c102030030403c143d2868015903207402250b08171680c0da907049882c0c6040c2c40c402e90840b1000c011a0241c02017a0004d40342100004021480361540c8a000800042000d1a2a2440b00350401c26000b481a00308003594043c8090034510b00d0007040c200056000c01c0010141c00840e956801c51034581032 = true := by decide +kernel

theorem cover : BRFrame.Cov 406834532 407014388 := by
  have h0 := BRFrame.cov_init 406834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 406834532 ≤ n) (h2 : n < 407014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
