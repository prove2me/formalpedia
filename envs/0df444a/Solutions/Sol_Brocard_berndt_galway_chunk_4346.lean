-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4346
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:19:37.363321+00:00
-- url     : https://prove2.me/submissions/6ed732d6-40d9-4c47-8fc8-cf15ae8ee1d1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 781474820 ≤ n < 781654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 781476070 1250 781474820 781474849
    0x80714030309071202040b122410210818040e0102030402010e1c0c0f030b160504051207091b1202070809040504030c14010213080c030a06020f1e0901120b 68
    0xc100c130030310301907540740d03000900c1401000c0e140040d080d01400c07405488448000a88001a004d2200d4134409818910038511550510614001045c20140e0020b02c0424086d8440340b104030020180d000304501e000242801c02c90b00c0c00312401c00c005182032009885181c0b046071010f9206004000241c0d810010690705440100c846c400004103403e003c40b0034521145000d0494007203c00302143c14a0442c07100400e0324040e00c000b04082d40c0f64544030040301d0700402c0001c00903400340030130002c40c00c01030346108a880c058010b0b10b603800d80307680000c0121061980103030b1210a40c0340c00c80304490b0300508401c0350083d100406518020454942c2517081c490b4214041c0100d070b0780d10026007032502c41c50892403010b51001aa00c04c1406419106003c0c1d01b120101e89088001d10000155401001400e4424100003030b001e800030603002d40b5440029081a208004c0a800c10000c12541c907682d526403112401a5400c0e06032030344142c100040640c2400301d040200585003002003140740c0d461118078000300c0c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 781477320 1250 781476070 781476089
    0x30c1b050709021315122405060d0f020d09110607111507050d02070f0f030c03081b030a09090b06090f21010903030501210308150d02090408071403030907 68
    0x8407040b44d2007500511080d030042010351141d04850b80c0b003992140c4440444c00120005200e602c0758042209426010841d032000c00d10546441040396003400b1014264000140c1c0c1d0004403000d02c0d40e100d2050764480210070180503902e02009007004044854000c080c1c40036594241440d00c59070300c8900e00b40c0d440c1e1b0800d220b80001c1c0a11000b01c85a14112030b0101d80c0042175640200c0c0484000e580c1d4a914024840c007414201c05c046400c0c0f0100d40c2d5a002c072504007035450380491442c3c072403540d40c0c1e00040710104810454002985c1c03c00c400c10090145101c5981e6110050780740c59100e07412596001102c5218540401c2030144503a04c1540d411820318044880c1d1408254152440c004200d80310040040c075400c210b800c01c14503806921080c101c80c45c09001c9040321400c00085041d1546611009000c101d01d180890603212201c2241e0b10051005007800707000a0440e00050021202120700f2100007000260b014100f0981010861035003500100550a50070709074982c80e00c3d44414010203619 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 781478570 1250 781477320 781477327
    0x8130812041e120f02042f13080303090f010507030c050703081306061205063105070e010b0d0e07080d030c031503060902012a0305071b06030c1b05070902 68
    0x901100c0b01201c4001e18041818004100301803410244425644c40160b203e51f241c00741001b90181810201c209001d04441c288180d0080c06e207048483c2d030800030310f084042e1801d10700841c841508000860050344088014070480d0800c920290030350700010010000c0500705400c000903250840150744c9a903526081020041d070b2041e9040b40040c400350005400542400c0380054040c00c004854240e0700d010b58151000c0390f45401d000344c0d1045000b100c12515007450980400c40d40d01c00c40c40385498510520684031555503980b00e041c5001c000307030030183c8120000079006800c20b85c10b05c960f0306a000e0038400b03030580c640b804001c2c03611643e06001c810300341901d940d220f01c03405101e507120751000c4401c880001c1071540c0301d0400000606030b4080032408a0190112284c038404078546032140210491340140d071607407a960b021616500944821982001003050065180d040300b000c200c0038117002d90f0300203030fa103c1003c1c004003806068120790071621100052140170820100c5c01c2420748010503005030340d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 781479820 1250 781478570 781478609
    0xc1002010e03270901030303020a1106060603010302090606070f081305030a170d06030c0305030703080c070b19090614150103020c190f0506010602070e2508060f030a0813081204 78
    0xc10140a141e1300540c000004004c040c0c1550290182181c1c690700c003150b11040080c12a900d440588400c0c3d448003003480104010310302483c140d54441d00103081c450a002280c0e864944901c000c00c011901440080f840080a0b0102c00441005140843c000e00226406468608215203841d1030180c0070000003500f40c442810a0300460000c40c5c4c02071341c007400d2a6803424041e80703903007018a0403000110444c0108003d1210340c415240c4080d04010145240c0d103800e2401014001410541c00249031241c48890100d44c1c64401c1c440c0d4080b614031031030542d107005a41610950ba013400303941e062500c14894801c0c1000000b82d0302015104203880d1380c5d16010103040041900c9842c0100900c070380b00740340010cd80c207540411a082160300740042240d66888207141e00380319000301c0300c00c41d00d02500b012100d40182d01c600f5185030040c2024121209000459002c81e0401106a209590f8004002560910082280d1100004040041c003a006107800013135507802a101d64801c0c0c2030400050030404a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 781481070 1250 781479820 781479877
    0x70b010b280e010e120f0a060c030204060f05131a0d0b060a09140a050604170111070b040615180911040b0a0b130b04090902130903090504020c0f0607020c1002010e03 73
    0x10718074100b1720b0440701c0c810440c4220030b940d107603c0e2000b180c2c0c00d03040041d1103003c00e0190003030b1000d440382c503190b9610819070410b00f251039400c050244a092401c000d400966455064065001890016061940c5503032282e8020140e503140941c150007040704102013014a0b43c0078040800382c4a9041c0c2c58010071507041e0010307a041c0782d00e030001e99105600084c00644d121045980a500c0c50303048009201203480124140074500401401414100604002600003682c07548040319544040e0411494541c881000c4500c581140703c143c1070041d5141c41d05410310071001880d4005000440e070500c01480e0756030204450110320b00c51078a510030f0100e0000b200800051240c4013520b06610305a440b20b6903001e00c40007130102d00000303a0140211400725003540c0c02c607004080c00c082c1c250322141006440e003002c7c00025485400505036070301074100c20040d144d07410b010581c00381056074010182e20403924100803814002c92108025a803400315400109000401952003c2c607010084412546d20428010b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 781482320 1250 781481070 781481089
    0x21b061e09060a080711120a0e0316030303022d040b0721080412081608060d0f06050403140301080c010815041509150e1605070b010b280e010e 63
    0x560b40118049141080e06a204000d0362042805030b50720304003040341000c0140c442e222070340010a01c040c10003500c0d41c035a02584540041ca400501290440000540743d0b003200e5949800c120000383e00040c034141101c5112002c00d14000d5800c0704038001c0404080d8000e182e2107503220380f644401c808940c1405100441e19030460440c0d15400e138415410000d00300600c0520201c8041342c03030101c01c0200741151841141058881e141d03c1d1080c9840c419915400d40720780c03000411507076211f80300c0c0c5144d80000e080f83c024031a0551040c4030105d0541400d20380a020248002c3d600091044203000401c040b00000550802000c1d0a08100300162111806003400242500921760058184020000706100036548041110580038040004500c5600780b000012081c0c401c401e00140360300041ba920b03500520520701005440c2c2230040c41d003400d03a6512594000240d01c215088000403c4050b0401924400b01911103a40d41365036200d8101a60050890003411a20504100070403200c012140c0740e14040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 781483570 1250 781482320 781482337
    0x5010c0b0a0603020a0b0909073b040606030e01060602030906070b040201030f05130203121306051c0e0d090503011b0806030a0c09150801060501050f0703210c021b061e 74
    0xc42807850300c800c00006c0e0351340840c3d455809040310f00c00107034086e48101c81e030703516448008910b04200c1d0304040321180c100011a1441c003d0440002500c0c0ba143e070340f03116043c000c204a840109144000d150f40c5801c407040c0c0d0b8400c105540042081812a540380b00854840d16031010f84104252154001200180800190403100074508014003010320084464496810b10803022151030318410703442005240581c40320354882203151903041c0010f50041c4086d0a450b80c1d000c00a080500300411590255100c0300d103010a1a000711300c00f522510341c0241c1107400f40c40c1c15002440300e440104902c07103020700020011003c00201c031011401c070f95018070404107010f0700951030b000103688800203000103064501c8010000030300b9110004090806020300801c90b64161511410500c0501d02400b155005041c201e0805c800d40d0b800c981b014116030030142d0480d81c100400182030030b035503501a03d080a0320030003542401c405205442c5940d906412100c102c04642c0940c0880810038000c03500300e0003050503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 781484820 1250 781483570 781483579
    0x5061915020f0a0b01140a0b0316021002120f0c0304110d050c1027081005041a040b040c2103180b030109020918040b070c030e030f1f0605010c0b0a060302 68
    0x420213000540700b0260589052122401e40300c03200382c0410014580c184200018000f06100203030b149886026441010302c0ea07070060350481306000301004d04982c0321240c039560410030b2800b031100d6040b100c10015071220030000c4891031820591601c2001c3c22020364114440c0212001c03090800c1024040307204000d03001b80206020f040285c5000c0c0c0400310150402e03400740e030203142000f400180d0118142c203d42801c4090812000140000c00203008014400c0e100c4c2e0910100c6404181a4440000e00c81c90084448020780d007405c0c60450f1207024254021588181c941c07030034003034000081d0a0001103640c5400c04c000508500704520000c081c880e408245e1390b003008000000d00c2c903011780080401c50800c03506d909000302c0d04444105100400d48000d0142c405040010301101e014128054410f800b904103981d02c6810b0b41e000900e0308031500322103031080c0c02030240080c4040042d03103640c55000900c802408203a08140008000c98081031020304440740c21808079064075415801030380a550040c0c03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 781486070 1250 781484820 781484833
    0x7081b22030b0907090e070f0e100302061204060506010507231018051203070f08060612041a150d02011206120305040f09053303010216020405061915020f 68
    0xa8101342c0304c2560703209654495081880504614001003030a100391114501c05492490030704040c0d00e00074000400054480440714000300c0980d4945015000540c1b00c00382052081c585460704006840000c4c1034941032103000e22081d8000f0b011045000018509903400200c40200c100795649800e0030084049041d42c6008108c10007001c4100151f002e4901840894000e0480d00074405800d1004943c00c8001415100c518042035210301c07607607904001c00601c404e042003104104810b900304c082d101140c959059188064441c404000342c99405540a06441c2041c0602004140440c0e10003200034100540c1549000b45405070b0761102c0040c040110070900c4107074082c0f501030042c4d40180036131042040203500c00141e0b0244d07401418407509201c0103030202c0c6070389001006100d548280c00700070350390440d84147c52151424030107882599502412280a4280340c01448212203010744002c5c080c09400d10040c0086c0d00080c040011070b074041c4d0146000c42c0e40b420049050004082c1e1200c082c0c054031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 781487320 1250 781486070 781486081
    0x60905010e061b280203150432030d0b0108090a05060c0912010905030705100203070e0d0809041a0a080127030c0b04080d060e1302010e01030207021201020307081b22030b 75
    0x1801c6406200750201c0f0a0381010703860020038110201c0d4024009c50591034018006061107500b4000c18120761340f50317541c50072038215180c00c582040303008408a030b6464481100660340600d809400c80b00e8500a4424095144c417101d03120100144070280f0804000340d564040e4503100140c0c8094132440c4000c00c40b403209417400c00e4407640019425640340c412a0603009000c2c00e02d00c01c03039014020a0300d500f0074983c84101800302003c03003100280d4425405010b00001625240070b4850101c1000405104001d5080704000301c035000b0382c020310041d038502160400b4002102d12075050107943c1d58044a15a08a80b800b22190300703008400a01c3c408140003800f00b0024800301901c00040701720300511905454501503501102c0c11958409594140d44a40c00554007070b144030066000c4c1850302601c3c0004640100f080302540c808000303626075000081013000b541c010182500080c155000c08000c6413002141d03451405803c0c036072103080c0700403200401604805140f02000710b42c0140c1540151808 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 781488570 1250 781487320 781487383
    0xf0906060c1e0c010f301a0a0902040513180206040311090a051303111c052d0304150207020909060702061006090b2a07060905010e061b 60
    0x30480290395407043e034001d8900c541c01928602030310141039580fa003100c1c500c1400c1180000840d000a0130524040d00744c3c41059400740544412a14100c640c040300b1400d0b030007480b20b095056071204802600c10301003070141d6030718404501a0403d4684000c5a02d460141c0480018810300030000d40c80f0700c0009002042240ca44001103162400319807000d41661101c03d62000c1c3c91048444505141419035442c00080c0101002c000c100301010803581e51840f09410b210041c0f44041d0f1110100e00003059040035010003290301c85c031115030700e813800c00e401314201e007440c18501010300b0007090948008850785038011a64180c40015800810380380d49400c1481d1050788484007515864018003501001440d11070f500900c61b81291202d030b6070081058079000a0049075040311802181010840c618100d008132401d10071801c602c0c9550282100a103031200103001d1801e1948041e050001103482c500e205da8503c400d840003480c0011070710410320080d00e10241402c0b407845010345216480c40031010620708 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 781489820 1250 781488570 781488613
    0x60318030c1609020301050a050418062c07050a03020d030c050d03020c010c092d0f080102190807020a0623090f1513030c050a0b01230f0f0906060c 65
    0xb004851554503460328000b206901c024001c00c0c1d0000d0850300308104074180750f0702040c9015000343c00154580519501c0b9020782c0d003404016009d61040c0e01007840c0c03920041603401d4802c01c0c00c400528585151a002c54403041c42844060f100c1c1016000b0101414004c1c4000609140c0c8002034075101204810064000c0d04603142031001503103080c44120f010b078000c40c4210161141c46c5000c006803500d0586640c428a50320030f020210320b40c2110001000105154003d018140040000d1b8807902169140c0160a041820700402c00a0620500039041c1c1c0100390030000c0c0c2d4002c034002c83ca01881c40308401c10000402102c54000c0c1c00071081105021020480884501d1500155190780c03026907403000e0315101c150f600c6200c42d1540e101d403400284c001e03800c103440c4503c80c600f543e10380b075590303110090821402d0740100c0403003da400500030b90036a4400741c1c46094100b107400c150f100341d000001c1100801e6000003207008a403940302007071700380e522102907881640d55030013125050885140384d41c1d420b60 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 781491070 1250 781489820 781489843
    0x91201020c06011d0906040602030901061214010516051e0f21011202010e10021e0307021005070b04060b0103020c1009020307060c02150d0227090a0606020309060318030c 75
    0x400b81004402e072592141520780505c000700b000308140d0300c2c2e5446000095102500c3d1207141d40d45c4600014841c00c408400041c0b0364000c2400d03074114004085401d080d1a00286803082040a641440750f034960440c0c2902d105205010090040d05100117400e4124401e15401a803000c00120310311004000d014401908c0b1040d0400341045a6610410200b4001e00c40701c0c002c1c08200705d844c14880e1428180c584000444140c81181c070450b40b02c41d040452880c0c896445807040e000007a91105500b403100d4032019105403481d00528111480c0c517503100c2e001000d00010106600e4880f225001da100303405a0b2121207903102030300c86409884c85640010010190200e02074003568000080d101e0092407034035115600604410341003800c4801c3c00710035902c01200000c20b5a424403544840d048502000b180c05e6034034010081074940303c0e80130041d1003040204900682d5080003c00d201169020080e90074100041c1c50403503c03511101d91585d0003000c40e40034031409100109a880320120001030307444901 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 781492320 1250 781491070 781491089
    0x70504210317061c0c050d080309010b091506071406101a0310051c0f23010504031b03050915040608130308070e04020d140a0c0302040f0b091201020c0601 68
    0x340c0d04015200350b00802100c0440e48001a100700d02d10050882c44010940e912980300300b01e50985800000b800341c00030000030b8414038404000c101c0d03900350034482c1c958091401c40740390382c2a180c029940d12816401034600f82c0a800081480c2d4200109a90030780d462080c8401650203900d06200d03510b48030b8190b0320904145010b116000250081103c040760302801142440d5009141010705001d00c4060200303000a0b40c40800c18040c0120b0610400450498132440c40d225103280003070034584001e0300307580d42c240d416458441030000103904120741a040131036031001808001e4881c01c054070140202502d8075041515a80811000105d11004000780c0e415074032010916150341070684041180c0e070000034003250700c51010030200d83c0662900b20b02440001d10240c0341400758103081d4140d58000701210032001c00c080a2002c0c03820b19000711803d1424510f0218180381c503101a01d4000c030840e1044481c0800c2c00502e0386150b4a9807080103013801d009800943d601e40041041c6a501d040c2480381240c04e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 781493570 1250 781492320 781492337
    0xc0102010b0a12060504080f03010b040e1501201513030f09080307110a15090303020c0d0510050c12130b0105040c0203030a0f06080709051009021e030705042103 71
    0x1881c100039500300780c0d2550f8841d4005a88190341d6280100703c060003c1d50394140501c510b641c50340e10310700254040c205102c1050f8a0b64581841d0b803c00c9140500038903404440005548900d0343e1241c564128811803030304000152880100303032410440c80d68582c541c0204010704205080386071007070043c51244259110b5a10646c1d2070700c115181d0140303020328049034104022032404100038803035444424078002c007108200b651720a100418250b980c032924011880d00d500c10020b250701406070f103442c0741f01603808907070610a41c0d072469210394541c040c20000a6660000c07601d482c4079038040d40c207004100401c4241c207003007405c2c4c403581d00c00c1c1d4414100c80d5560420f0020826003440d000d2800c126446400540c00e45c2c031200e448401422042a09600890b80c400000079440800c000c1c0400401034a80001201d040c4000c404414080d2034000340c99003401003051800604c0414403015200c10040d000c40e07180e884800003104c00d889650f001319540b40200150304000c07650701d40d16080e124400d440741b621 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 781494820 1250 781493570 781493591
    0x308090307090216120315080a140d09050d1e05060108010b060f030129030c12100803030f04170a03020901020d080108070b0a030f140103050d0905241603020c010201 73
    0x41e07208011075080c8807043c2554010000381c1039001c0c80340b140345c5420b000c5178251643e406400030f1a01603000c10410341c00409140140b0200c840d2142c0010600005486010981400504040c00e2442458026076002c0030090070702800c402c4001180d4004000350009034560305005940b11020300829845518001880c100d5181c120101d40c41c4c041183e0200e07040da840c0580c401100312200c070390744200981801d12116480c61017130065101c0c16200311010b44410080101c1c4205c0303200200301c0348110f01c050b0b00c2804130410001c2665445401160602e503d59101e2078881d503141e01c440c45411075010007140410181e9056000340c443d10b0000e90072540d106200103821074030220284624403c80c1c002d000300f03100c0410341d8001030410350384034140803440e1641200c20004482c0c051906652600c0c20030018010000700b4809004500a40d00d085101c007818400000c1c050702d24501801e2842143c01e2280f1040d070302d2801a11440741884003c3d00e81a5042c1c10041d40b5004803030081c42c01546461340d13400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 781496070 1250 781494820 781494839
    0x30115092d1202010c020f010302090301050c2703070e062d011d0a050105031509010e04020a082116062c12040902030709030b1602210a270308090307 66
    0x24400b43d0140e40300c1031225055001c0c070a01c070201c5280d5604060302044001c2d4603072824060310b4054200302740c04950780e5095051101140c06c0080f1030804801911000010f80e80c2c0001d40003054501e100502c2220344c60301d0002803840203954411070320000412888450482c000400c3d0080d100c2d0a032100248086500700140c0320301000b950382584060504424809544100d000d15400084030243c0e000c0550303440002500e402c0260306c95036141c647c401c104411400e04d145407a0050008400070b01050321f01810440302c00c294140c002d80705280209850280342a560003040141e500820101b041d244e00c01185003502204115810103d40c134002c0c51018182c0010b51825148800c00040e820541850740900281d80090700403c104421280d02001040c0c414501038010010b00340ea40d54210344445001e401d00303041041c0c0ba549100200e092100c0552280101c4015049a107007003100004440100d9a0100e40f4191026a5201000021081004810042038181811000c50700c10558424004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 781497320 1250 781496070 781496099
    0x5220518340c0510060e0a0b0402090135090313141302091302030f041203090b130f060c0504051c0210080c040305010504030c030f0311030115092d 65
    0x41030710300750110400e200c8510035024240c003148140196071080898640e034100340c4090303400441504000e1401e00c07164001512818103d810b0594003981030135150800a0310104013420f038940304050030f103110590801440c1c1a80000b140141603c40c59040c55060390342d680d0000c1e8007030b41501418101c003048441c00030000d25001d0300020030100402500b1110788001e0b4103d210000c0d00035501102c6644c40403180d0001e17604c140d8110071000f001d8075080c10008840c0c101d050412050501d00081000803403d010711650307002046010385a4030348460f03d010203510b040c3d0700b0041c020624004110b18881c4c1d000c001403080365402c55101c00402c8010404036008403a5041c000d40c0002003a001c0d9801a001c4c40f0340543c0001501000c2d030506a0300d441d45030950b10f003103604030009400c90070441d003050b8228090100c058070518041080d0b07100c481007200c10f44018040c8190349029800340341103541c407408150f0701030841419040340507040d61120035881e580090803410410810704000c50700066a2000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 781498570 1250 781497320 781497391
    0x507030e120a031a10080f0703020c0a060b1908070501092c040c0f090501030204060e07080606090a080a050f15090d12060305011815020a05220518 65
    0x1030a1500b038104005a00500380040c10080e4000c0e4107803448580c0d6100043c00c0d100c404651540e07411440c2040340341d80003260003030020040c0351042c4a43d0b10001000560201c9240d4008000a1071840d81e00019084515001059140c40084440802c200e17502094010454a01303803180340c200c0d5114074410901041003000e6561080c011141071422410313039410160030500890b40080c0017134640380340103e01d000d650071420145490780d00400841c03c1c60312800d001001d004401d40000d0a01400040c032009024049a201d054085100012940c0d8030700303000014003960301110045040d034500151a054091944161030040d040c8807101c0c41006443c2c148694540c40c050240d1000f00c000581d1b14a0344504410501e0b036580b440440001c030240310b21124035503180080c070031010051400020121a004441306180e005009040006401c08265070038142900401c3e40401c2203000c0780100d08010f030b80710603400818100710005160021844900400b8413000920f14149000030141e05440002c01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 781499820 1250 781498570 781498603
    0xd0618060603273003050108071202030a02100e06070c080606040c090b0d020d0f05040c050f0d0308190c0c0507080118020402130801021305040506041103060d050a050607030507030e 80
    0x3e80200164804c0030800d0126036400041200c00d040582079500b200300b0110f52408280da030401400700e6003040003a0402024407401c40035014040e540465169248100001d001e44220801c49804034014408520140d4000d05950345900702414810b0b4001c80510071040f450248002041c200d040c00d01170710300816080e860f11002d50349011881d00550303005007600340300d15a09020f40c130244c1d04203000300f40c00491a00e0002c01c890038642800d1803952440e500ca540b18034003110502503d5201d00526556158260034508920754440c62112004007035a0410f02940385000c1d20025900d42102e2617505190040080320001c81e26440f09a080b12900701406007640741500e0240014685070300180801d070782040064111b42c1d55a10903a080e6001000c80500d48248034409101d60704240c41a26480740c02107509008064166031004110300c8050612402038811455036000d02404201ea4030f150f139400000c9510b40c1c07502d403000a00034a815150030000031b0070304d074030202042d00000f10180d01c51801d00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 781501070 1250 781499820 781499891
    0x120b04020315210604060c0e040606021e0312010608010e01080105070509061b0f0718021207050f04030525050303120711070e0406060f0e09120d0618060603 69
    0x1000a030902d03085a440300c042c2400f0281c100c82400780300035070240784285800718080b074000340c026043c178860040683c0120b10b804010408a503001074403003181d400000c00c003035482d401d1520703c9003940b01c0d40055200c0048848000520705e81d000144a0480e440b00c01d0500040c0d8892024909807901031ba80f190015030f050204442d6441c101e0700130803101c02029210448169281d1001d810300203682802069078010301001c010b4501c6003142c1d02c4012403282d07802c51810000d05021945004042d105604001c0007258005031444030000f103401441e001030440c6e010318040e00e00044070402c44001702d030f0040301c0914001b81c1800c0010a65421f414008171000c2c095544410032a510340c0c6c1d42840c1d281501c5400e0001030b410f021610524062402400302251b12420007404820120301030b8451401802c0c4d80c0c04000c690340c1c021a01840344890f03c19520f54503940412090050b1581b42c102035589100c002503010090038540c024411201c564405100d4035130752800040000030003840c09a080c1d02c001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 781502320 1250 781501070 781501111
    0xe07021b01080c09030609010e0105090708210f0f0406030c03021218120406030e0615130c0216080c100e13050402131d01140112080a0c0501020a120b040203 69
    0x1010b42d40e90005a10030aa82030210020000780b51040540b10ba1102d83d6449000c1d084610081c0035040d8041c5201004041d101d241415803503540b06451329545120982c404c03420518100c030400c80300921103016005441d0356401e210042607070312602c0341102191070802014456800b0303000b030703c09aa10781e09080314981d8417100c08012180c8005014042d41c0075031600182c0d1038950700d0240001c0c090039500058405042c0f0000c82c03800c6805404400c8030341034820f2079045030761044550080c0904d4902c0100e040e02107018141c0c034208078000035030030b41780c601000440d20000c0002d101403129421a6106106000303141d06560445946491035003205400b01c40300642d004c030780c200039041840509411100b00c4041960001c950080e00d494810600000109880c1542401011245423100352003500c154500484c4d0030740c0860400004205203404030356800c1c0300e800340c0001d00546e900040250354444085500800300352304810002c1e58186801080ad000e82043d1094034460703940e43c2608448000d04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 781503570 1250 781502320 781502327
    0x1110306060c1501080d14190c0303060e040308070201050a110a0309140304030b010e0907050102100e1903051b0307121407080f09090f1905070504080a0506010e07021b01 75
    0x4142e41c0040c0300d90084181040c1c00345202034000c0c003048010b0411110030410050491280304d10140ca0f41300c00703000740d040c5024151140c3c07110899506003440703060388500d8141c01030807560b8058054001d981081006140e042080d141c17140000f9402000583d454240d0941120340c002c0002c0981c920500c1000b10f858000e504c5aa0f03054050a81440e850b01d102c80041d00d541c0c040d03001280c01d1101200100007600034403445c0e5030000c500c000a010800d0a00000070350b28030844034442035964861440c0c4451580078070801d85018030b02c1c0400c02c400d102c50b04002e001030380071202100140c03145140c07550f6401d50100613506210707840781c0112008c2004420440300c5810f0203400300e10a450030498200003501d0000101025000c4000690719200840c08100c005a4000d141e8280041e0300400c211322080d046200b0880041c40e120b0004058031081c1003201c682c02036030040c054038030a08032400240700000403424100c9400c0c0c5010b240b29039400700e040342c5814082c0c1c1c3c10302060902c4400585150700 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 781504820 1250 781503570 781503577
    0x90703020f0a030818041104060507080310030510050612010c020709050705090604061205070c21051e030a0b030312070e042c0c04053108070b01080f0111030606 71
    0x50051084a610b074903911400c0b0f0340d034800c1501c0100c00c00c0c000d090241604082c0a8070340c100386550209420103249c4540078101e4401c3c0d6000908030500000022140120010803070b0143d6000800c0b140e89418020804000388400d507480d900c204254005901220014003801404d0b58555001e4040751b460040281c0c06020090b22102c140002481111103075141c000c043c000034907451b540d0a030641c440000c2341088442c0a0900e400300001e510b24003002c1810f406400b800c07964000c0032400c0340c19412808460764090740c0804810402013545102c012083c00c00518000d6503503410070080301c603001040581e01d100f00c103a1091109400390000f044640640c0642c03e050398003801c0031444044407040320310103039004400420580ea01c0240544080820061261541002c0d40d041025052038502d111801c0107031141c00180c66502101038800428800c00e5072100350388a48142e40381e02d0a841c02800b01602400b03030000b18403843c0b1880690784014066030004200c407940c858910344800c000c0c41090352 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 781506070 1250 781504820 781504849
    0x80601050f060d2d0606081005060901022d0f01020405030c0108100e01061d010309020f041e390c020103050402121005014e05100209010f03020309070302 68
    0x81d502d0054010741e802e00340f000b8a00d6074695580d50407240315400400200d17200798025104006034842000201c58000c0c9200c41550300443d5516128042080100c2c5814402508111501e40f181d04000070590115103004413140d0304429210100d505004440c01c0b07005904ca0035a255002801e07580d0035500421105401000b0191440d5200c1e40311409000300b0042a41300d400003030882c0007000005c081200060207140c600f4031341071000030344540008180380c0c004105240b046070f035130829501021400d8110484604e41c41000e1026070b052a042c0100304ea4808130281c42424003000742080601140c4031100e1041031521344025030704864004400505d8003d00480e0009012a0b1403800381c8420002040380c600d4060006c5041c0d07040502c45900d810945042e0948511281c5050388120b0901074080880c1c0b00c071901d4200385d010060040c03859400d60070b0000e002030098a6007a0320b4000706800803c0c852a0a890701440e140d0744a9085003288001c0f1001c80b07194109c0c030f07814001460084041509174 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 781507320 1250 781506070 781506097
    0x1208040c0914040b070e0a03030503070e0a0803070b0615043f060b030c03070905060f0a090902043c0b060d05060f060c1e100c18080601050f06 63
    0x80d40c40d0014482203a4007000d600e0b610084040811042150001034a0b80c80703d064a414000c003403101000c126800118040101442130104c0000d070101d20400340608410002440c98458940d80c1c01c038a40c89610000095071a10210300014205050040541c2c5000b00840c114a240c070b40362202c001c00326103034803143c10300c0300e08421049101c00e5211f50410000000e071188903d841400d500d8607004803040ba000847c060f801c06101c10606650100d50f0a0440d4110301003c03650f5926400003600d00f200400c41c0380e521076500480441e070a01180d000141d050300c00d031010445c85e1207a150004e0040b1405004038140f00c800d102c3c0c0c0854542038038040c1c0d0310710000d10000c140c28400000040f00b9070004412102c80a035102c00308112868103c440745080b103c2903030404d00d00860225819180c900100350303d4526450854280d0100c0020402d000155007525401c100d80940500300510714822110420b201e07070003010020410000201e0140c4c106c40009040e1400340a0b25014051590406040c01d01074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 781508570 1250 781507320 781507343
    0x5130b0301060801140a1d06090f01120b09010905030f030a180c03290c0a020106090b06091005090d03050a1d01050a030f060b030a0605011403070801060e0301022221120804 76
    0x2c040c1c002641e521b0750f17907051f0b583c8403d0345050414400e000c840180702981074140000100211590482c48000064209040010541d00c1c418018050f00003800c4c010400c1c030000440c08512070181c00598042c04802c541400304107074074003100842d1140840d0203030640354850070420001e0100480e21241480319650040381c2130035194501494541111620b54184000480c0c403125a820311030705016041d541e0781005900d0055021800381d010307003100d0707a00441b03201218003000d6004100341d03000081d0041440ca0440c501e490000c1244c0c215400c6000411405014107215040160524440ca081a580d1030b0520b0b0a588045025100060030800c03811f42e10000030520101c84402184200d2440f030b00032030101c0c58003000401e12035104003e030003080d0051052001c00c036806010750781183c40c20f20348068440a0000040c0c0248038034145c2035030040715110700c02c119100d10100d0600700c4290080071102d0068060200d91640301c4c510008048003180c0d0894070300c40e07008002080d000f03401810351220 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 781509820 1250 781508570 781508579
    0x606010c230c032812021009030e0907082401230307020c0a0e150f0414101707050402030a1d011a041a090a0f0c05130b0301060801140a 60
    0x21848440c0d90214090b000744010307000d1402c0400c0045801900e09640c1c0c1910310708038411641141c00e121004000c401d400c8149041540b080000001d9000c50500403c9000d0f01490050129540901c0490007400102d00140001e40103416461041c00424643c1510224004401c80e081d20404085814062052000191540c00e1803405850303643c030011459907400c00001c0a807030640c852459603c41c0e4007034a401d200079404001c4140e002034001e40030015000802e0300080c1050405008150042d280601402a004c90b00a1040c0180440030144404030703203d1707030800c0007800c00700080a03ca42c084002000303d4242036000f50340c007000d43c9400240c0800001d20440b0714041c200b5001d4240c3c1c2d110b03103000242003021010810f107c0c3c4100ea00304002d001c3d144142002c07889036078000c0e114000030b40c00100030000131b41103e622014040020403903011400c4c0060300d55004204007072008941c613000820011841001ca0381610b215440d02091070f03181400300388000848030041034020248550029 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 781511070 1250 781509820 781509863
    0x619032a15080114030a020a030b04020a0b1603080601110c010e1302070804090c02011b120b06040f08010513020f060c0f120d0f05060f040908040e010828050606010c 73
    0x70104040c035582c0030341d40e5142c10f0241144040e0080c05620a410003102c42c0c006a0b54984810116644071407036103101e41d02d60000984001d6581c1c41400c50703110000e150ac400c2e6254a9036503000380d1213920f4101140d191880116081c1c06a0b60b114202540000c15424042d800350342007203000c80380205508290600c2c0004401a600007420807954000f011405001050003401400400d804500c0200303d9000500c808070710142507005081e0a100d40c041000b2101841a000541c50103c084e00040c0e569a50b05681f113980f606512034080c49500c1c000202d50b44d290b0030010034140340e4000b804240c1c5640d940d001c0010b141e0000010b08658410040c200070502c0c01800301c1d003044c800807411162280c0c0300f00b110340242d8802c01a18901d071854001084059a1160741152071003030309035400601c0420500e8504442c0c0f284c2c0e0400c4036111504000060ba4180c0000c0442d0660184c401c04408030100b002c41a115149841c0014041d810241c0011919480340384480c41d00d6000d5020381480301d01c1943c144 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 781512320 1250 781511070 781511099
    0x50a060f02040f15020715020f0106060801180b0303070321060e041221051909050a1a160311070209090606241b070e010b030619032a 59
    0x40d46069004a410400440554a401c00504000c014298560740080f0000c0d1900194090014507036061555500070a10801010741e00c0070308000204041307030700e590010f482d1240074490458103050b00c002110b0740050501a40000d041c0140080d8100000c50341e0a44184030902c00ca100311035401a0310b01c043ea2801d008400040085c460338100a040c6802e2040200030320000b590180b14003194141281c42c0e10017504500c07000404d500040326124154400f500a055401c006541410104038500b80b1a02088004c1040c1c42000c200c2140101071130600540042290030141c600e0060880c103100da40280c110f258110481401da51400351030707a00142e07824405a480c40b5180c0c1c0114101b2440b42407031201d6440f00745c0c03101d000e41c00c440c0c0b082ea1565201c0c4075826098090659224950b1800d010400c880c42c00b4284109030035401d50303110341484400d60011126244a40a41000500c50124041d01e40060740c0c1c00c20003003151440c0316100640d4a04034002510f102040035240010740944000d150b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 781513570 1250 781512320 781512341
    0xa050a0b0d0b090f04290a0b0619050d0614010f0503070527031006080a111f051c14130219170705040c0c120201020d020f090306070c0b13050a06 64
    0x400032a401c0a0408000c5846102c0401441034140c80351208440502c00ca215030056900c7c101250540d00400810098019400701c1151081c498214809c0242c100c0b000c1d080d86003612100300710300365445d00103101032088480309601048401030070503d1140708070000c562149113420154501f1442588540301c80003c91302040c080420307114500e50070b20f01400900d1650305020b8051112504000c07410f91104074400d0020261089081e040c3d059443d48802e01c070707603403500c0e006000c0c0c016000c001c00740c0280d1103400440d048400489510010b25280c0c4a40c10b04000c08008000c01a903030507914500c84c408402040e640058502c0d070410144540c00c111070701500709900d8022400c096145401c1c41e0220707a0704041d2050742450710340d9020350351296541241d03d80042503070000034131019059009100303081c5d1403082c95000003000b84070306012900801003044190126100355542c0c43c402c030b54648203684001c00a180003404228074000c050f02c00c030030081c0034030140c0c2e2682007250740718821514011f19 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 781514820 1250 781513570 781513591
    0x81021060b0901030c06110c040e0706080a060f210b0415060b030c070204020304021206131208060907030e0313031505090d0e01050706140a0e0c0a050a0b0d0b09 71
    0x1100308001400352020001003520721184a504565883c0c1d130444680c0035007820090707000e0151250784420040c00003123520143c001c01c5003000402085d900c80c0760a000c0d65000c501c10b00082030030941184180b400304e412030030107444880e007440180e240e6159520a10781d052211925104042038120240034011131241c8003403030024601c1d07800b404c11b40b0b256501c06e0000b40c00600401c039480c1800300455450641c101c800503540c2d0b64500c0000e03a120a02b4410383d2944c803c000400081c81026510891624052002420742d1181140100c50b841e100712030407500000114003146040e40260000c00d0311040d150140c2c2e0601080c015081102c01090f4170030303502e00000c1445007a07503986078440c0d2500140400702518500406030710180c15140c840d001c860400034005010014130203242c1c04456001300d042c1b003600007802c00d00c6072140940040f000c0401c0a0040490180c00c92908000740e000711100504100740c0c0c1490101c401d0b802c1e8200e55080b644040e180c007118411b0341d881400030b901c0340d0344510 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 781516070 1250 781514820 781514879
    0x1050601022401052403040b0a0f0216020d0303020f0f040504060605040614090a0512030306030106090b0112050c09101d0901030309050402130302120a200d030810 72
    0xa16003502c002e0700700003000b00c103021944a440114031403415624181c80c81c920100b0205000ca101014031000200e010754084207101c100041d51300c55600a903e400310603c045054460701c00b04030700c03902507520902c0c020b20300d5510041c10034041c901d0005000b402c0060400c3c240e1400b510699100203001d107040440001c1c02e00c141d2500d4807421004d00032914195003000d050082c060034461030320309550740c0b8880104139905565140400300c002342102524201513402c81c50500d540e00c1e017007a11050700c00d500307101010a891794036104520800300140d444900303140200c442c840003410081d0420aa800b01000440c20320340b110100500300700c8c3c2d580c1c0c8441415840120620921121511480c480c0740f014004201003548030010100383c0e04101d60040c0d940461201e90005207290780d00c003d40043c1e500a04a00e8801c0c0881e46c056242c1c05204101d40c0d00d43c2e481200917554101030f104035803010039000d86001081c07040103440e0380410020b07400c5e000c940d25504043c10104285500001c08a00360 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 781517320 1250 781516070 781516081
    0x106030608150403050a050304080903030a0e040b10020601090e0109051b130614060c030c01060e01080f07230a080f0601090b0d0c05010305060a121a0117072112020105 74
    0x2c20070382c814500300804540943c01c003a070703000f4502e203c0c07140050200100407000c1014050044100c441c101d80050450b81ea81241007005004292000c2046100d103182050140e1b807828000c03a54404030640350b01414007a0b00f00301250b0b00810055000c07400da5035961483d50001503040240012000b06108c01c440d4424015081100c2020f16018001034641000001c21450030592502c91102401321a50380c0c403200c058540502e9800f400318000c60942c20400000b5a081c15020f540c0d040e41c250307030240c0f18008805581d543e81d81c030062007a00040f2000800072070000340c62007030384008888010840c10712243e51f44180341c5011240d030740041c6150010b00040041c4403d512039091034203002e841d01004800075880c1d60102c013405100d11818035440f68001350881c0c0d1200c030b04c1c1005e444141403100355a051414800e02c0b51200f09003140310f4946204c00460800d0340c00521041d240045001404160304008104810030702c1841c422485284517220240002c41c250307031080c12505560300024092804 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 781518570 1250 781517320 781517323
    0xc070305061602030414010f030e1516030b03060411060c0d021501052b061b0201140604090807080a0507080705150c130e1b041d07140702010807170106030608 70
    0x21100300b0641d40100b20030805a03424144207008403509003001411104205025005092858010301050094248000d07421141003402c50003408920303003500014241d288241c0c12101c0001026516921910004002039041c10f004208800003400c2c9600300324103002c1007490f04111a01400158100344400d18201c0f440410b464010801116141040740c0c2100c41060318908911044011121150b1480c05122694000144106940c1c1c1d410b0802000328000900030049181030f10360550007003000c1889440c0c240100700c010f5400000071440d005075a524001c4942c80550741c1d00c02e2140510100e008602c00764044c010442c09940904105002c2900034000c00000412606455109000b03455501407a0b80a02d000e4550310690311561751107910324200c6038550b00600b42c0c0b000070001808201d505c074521480c0c6440040c0010030f01c0035100d0343e40c1030f641401c405840400c50780c400c0c0000c002543c482c3c0c1000d80c1008107070804442d03022000d0703008036158400340c010306e001c030383c5440c020000b5020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 781519820 1250 781518570 781518601
    0xa0507031d010503040201050d0e1e06100b040b07110402030f0a0f111c0b030601060302120a050601050a050a031401030501020c0d050c071a190e1e091b0c07030506 72
    0xc02058007051000c00001034042c2c04007a001904101012075000054045076111280e40070307544088401c400c04102d80714034920803e500c0351000d07002c0c090108102d002c4000110041c1d85103a4845800c0c64180005c0b03141e143c00c40740054844078a0203440c812a5104c0c0d10045000e400d44128001451500005440a94191144501d0811710f850541c1c2d042200701c6054550319030710100e44030549880c28203c00007400360074804540c14042c100000a8542c1c00d540100007646030034074031681c5a601c100701081122030480e90340340803504c10000c006220344182e0080c000002a400c0014000c07424014108100c0c0091f0400c035807036980000c0c0c131202510208140300b0742004c00d24000c0e2400407400c079025141e0303c1e180300c0c0707640550303124005122060f9218182c0301e4075900c4492040210344003000041c116036520b0251401076248070002e00c0d0310f01c03488409000016025140b00510b80310741d04541814940c00300c49800055080c000d1501268091001c0c0c0d00840c0688020100d9043c005582010000e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 781521070 1250 781519820 781519847
    0x3180f120210020d0c060e120d02092407030309080d0e2b090905060f0d0525032a1a040503070905040b070c02191d06030105012d05060a050703 63
    0x1030011030b91000083e400b516035404550302c1b08001c15201031300d2841c01d2a05000c45503005090001190343c007012242d6602501f1401000c541c1015221040107080703010010b49441d600c1800c4042100b0b001090194104007503951003800c0c1c040c279042070001541d0441d40307100e04845540d0854007010450b00b2244515003460311035041064010103401101400c40700551081590841e2034800051841e903440703902c904a200301400384006c00c80c80d403805a8a0f44446610350500e0010342c40c402d0b4070008440e1400c010340381e00006c190251034030000400414800d840002202d00c001340000304412030404c2e1b1414440802d10f85c1c3c0b0b6155401c1c0380400d8208800383d0403040840e481c104c10480441c4c1c5444106402c03000d1800e02d210306108034004100b0050324240c1d100342412022000140424500170345a2400940180b4585962141c500f054243ca00c20700c40c0c46d016000c0c07030080301c02c42c800c90b9001031059900c0321a03042440da580c0011801d40c0d04000050740200d40041250070905800c407040f130340f101 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 781522320 1250 781521070 781521073
    0xe09070810062a0507030501020406090e0708060121061a1308011803112415030a02010e1207080d0f140405090f0703020903070801061508100303180f12021002 70
    0x4403d403100001c1000466105030211484018291061040901c60768000d1508000255603540d100c0801601b00e8842d84155640c40201c0e00002e01e60314401c4246a0080605944100180440c1c04462900c5800014400941c9540c1c200001e1031599800c01482c6a40c400c0705002d4485c40d076000c1800200e9050b138400e004030390411103000c100b01003d81298803211351509100076440740140e041c92030240444c129480c3c3c4c41c00320a030810b544140017001c0d446215490490391000c102c62083c107403075001000000340452a00c070301469452800c150004424480c0104440c0c40c10b030b50f10744d01c61402c0700c04211580451641d261003e602d40d0f21031101ca9803d07041c0c9070001c0c80c1500d41000f24143d071400810402d100298a404124024401d40454107807000c0101100e01c05038503401c1c1140281124401d40d019100e41d04c42912080b8080d00c00745114900428140351001d20b90b8800b9141d207421400c60040d0b104c40840003182000d080b07030002c0047c3c0210858142001450710500c0394800c154070410055 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 781523570 1250 781522320 781522337
    0x1061518030b18031309021905070201090e071b110f10081504020f0c06011401030e071701140a0c1209080912010e0a05010b0a0906030203030d020a0e0907081006 71
    0x400d0301802d9058001c2911400307441d92401078010301c1d0440c092001382c42c07802001c0c40b800180c801c0d81030b00544034080e80408581a01200c1031000d96191103400002808100750507403c10070301c0c282840080d403115840c20700c050000c0030348400902c00d51021000b00e4600710f070b150343e42e20385040096000c00380d1030058403203049001c080500504030314402410804002801c810502e05070b00c82d034041d6600150414074007601c0d50039504440e61242005d0064081403103c0c1024000150f20a004408200380c0480141c5071080c1040e6002800341003101d01c2c001d584d074a0310b051024041040900e14800c4c001c5640009402e01090f00c010074070504000d20000103420181703c03e010486c40e800311002a40115600380120400c41c090700d0240c000f0740c7c140032143c0510400785040c88019003000d0210181211804000c9031a0420541200d016000194140c1c0c8180610703550003080f81c0c01480c0702e4440b801c02510f5012040001460180110303407940014016909200d5882c0c1c2040c00a8090051814050710 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 781524820 1250 781523570 781523573
    0x20420070c09110418090c0b032d150607050a1b08070501022d0f01020301090c1412011a091e010813212f0708010903020c0d02120106151803 62
    0x40c08900005c5244d00595079600795001c200243d4000e03001080c12244803a100e02c1e01d00302c102c121044a00d040003050031002c4089404401c2c00c92498810180d034a40805070f84061f205000440d003100404603564442c1a03c490042507504031950b551440a030300f4954103a00741007100b4105480b40e0300c02419944030021000304888403502000c9180c40c050007003014106000031847c5448918076500b8541d500c00000812050503a4001218080e00e0351030354503048600c1042603c0074030510710109101142c0f400148001466405210007222030400018206006040007510310000050f007405040c400a95851803940c200c0505603110040a81b00306400009403216082c140400e6203100700c107114140c1c0148480d01510480c1e00c0e9020303490140c1c000c0185031001e282440e050708030110303072481041d0340000d1102050181d2151198144e0141210290311f8041c021010700c80030040341e202210144028140d1001d01c0707824014110101450807041001d107018144018030715132042c1c0380906040070700 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 781526070 1250 781524820 781524839
    0xa060c030c020607020d200a0e0c0a140c071e060c2001020a0b090c09160e04090609080d1a0607050a0f080c0a030c02041104050d020420070c091104 65
    0x10901d60301555416a101d078244006405102407100c014128072184101240e0901c020820b607404400580304010503948402040f515240101c0d44440c0d009410407c0308090342c4900c5a400c026a1301d03451644c10081c04621080c242541170304800e00c0e9960100d07107210080003000341d480080c20f49051038000f00c10782e40c0703407840070880d545000e031009111900c0c41d000701d902c200001c50310035400c0031240d42c180c1000c3c2106038461505600d07075442000c850002c15075070307074410f204d10000d1207a5440300d00d1195165000c0c00007800b0301c2181654880d0361158100b005c80e031002c1c0140030016001d00e00040340c035510180f092107842d864851500071241800010002800020000c22144e00062105080c00281c50248018441c0f0500b02416010740b41c04003040541180411000d1803088500340300100140c0700000c0280110301ca025400342c40c1030503043c05418943d2000d0301c144200050305032001d2050310301c50350b0f079804214200c95060400c0380800c100388031072084c5031481121099082c40c02d458500c41d007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 781527320 1250 781526070 781526087
    0x605040305030d05060f12010f140c071e1203020c06100b0a080a090c0303110d030506090f04050a14240f0601050d06081507021501030b1602010b06040b07020a060c03 73
    0x43c0c00c00b81d456021680541c1c548181030750740c1400500300011000c03080c0e0340a02074618184210103050400d612460020355038084540f0414080004500700354241d00d5074544507030303e0041c0c4200c05207101e41e41008039207071040528036071609440140e5a94481541545030100081c0001401005139001341700310803451040f11100e030907500c0c00c60403a8070744d40185c200503c0180700c001c20b0035202e51000000c040d005503420b900022440d05070344a050011078154281c9000300c0b10305610541c948002800005810780c0710381c000c0d004804840c3ca5186641d03d410100d4040300f0100b01940c001c2e01c0901c0c480e2000503181a2201b000080c041d0035051002100701c100780d01502241c18000e022510140d009007644c061001410f840c4221050000b18040301d80c0c90035415507101d0018011305078490400d244840b501030480c2d503c582c00d1080340d500d00b29049444c401c081e80c0541195217a401d104120307640d0b5005807024051450b40740780e9641e1a0320401007c1140e1351310150620454914100c0402e8024010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 781528570 1250 781527320 781527337
    0x7170109020a0219060b011413030807140a241e0b06120c03010e06030607020a152d060806071b08070818040f061206091707120207060504030503 64
    0x9070302d9079080342c0164241680c042180440808503401c450502c10325821840b00d5050071b8840c210348000c000d9011400b486100090310b4510f044c107504200103484003000b041114001c4c6404980c4039190303c021030500300210310640e81000301c8240c4200c8280300313030404001c4214202082203e014021003e500341c508088a07041d500d9a5400c08035045d850317100c01c40c2c50501c0c0440808500345013903058010760390000c2c05203d51180c0280000340c80360600181c0a4014640c0da0001e009250076643c5040d032021142c02c04415464a802d030004c41078070000b185407000301030f1190010160041c858104200c038501d900446180d4441418060810303045140c0003203ca0048500c01c607000c0382d03030600326804d01c10b07407000925a01d40020840203001e085111200304007000c1f50f0620407002c071211741c941981d02d18050788040e40d003d07a42e52000034480b43c0c03114aa81e40705022541002786010424000358204000c251081312010300c0c101c02503641030040002a0200f0304040b03040504580780e1590764003421a4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 781529820 1250 781528570 781528589
    0x11422020904030e21160320060f04030501050411090f0f04210c0c06020f03090f0a030503041203030e010c05040603020d1b1205060f0d021903080a05070308071701 72
    0x850203051040d038104140c44009018001e5090707448010110168107070b05c020141d400341c11140000a124141d59a0449400c0320710105c80078071161070110b0741d0340d41644d400d6004004005014182c6407240151000318060000040d4078542410242c10784208107942a20585035031003005414101102401d410031000c50400c50240c1d40d030714003d00584200304102d02c00d042498080040b880c1d1104002441e288540c00311511503a0b1a0303416662001c002c44150819041413044445c6810003140003411700f4801054402803a0380c90700d625046600130340240841302c81c0b902c070010030f15806004421100c0d80d1100204290460400001c0c4140542c1c05038000301500003035118030300b29068021060b0030000020180780300080c200c000e000822560a8280f400e4209400107000d85418030103691038002c050300c0041a10402c1e401c00001304460035002c25141c0540c42c01001141050300174000e4611140c5030295204482c1c28054902d420061030a0b04000a201e090201090041e9455045820094 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 781531070 1250 781529820 781529839
    0x2060c03014a010513050c030705090307030f03090501080c090a1809120509041104050d030f02190b010f08010e1b0f12011424010c0807060203040501142202 69
    0x1140622000d50746590388200c00014440002c08025600807641211021035800e82d00407031450036102034400c102d5094120a00c113100080030310340200000c15202c4002010394040c0c03612551142c600c11005071042e00003900321030080c8030550300306011980148400c038041d402d0070b188800080c88580b04d40a06004400700c0802801c074007000307800844485034070a0000d001d08d10b00714402046500483d8400d4416803d00382200da000056108441c25914042c1000c2140f1000e51001d44080050958210443c800d140000c00c2030801050507003121886101800d0726945085203c1484400c40c2d0080076007a458054840c07010003000072100b950082800e800d0324810b1024000131818188804400c0d00701207081420b400c9103038103500c20680440780040210468884c48029500b548a501d5990312607000080e500d00c043d170083d54903020161140c3d400314075006081d0389000603a0820364007200c0301d030344074103040e80c070615000b01007948880c031048001905007000b880e4030200307032006001034011000038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 781532320 1250 781531070 781531139
    0x1106010302010f0e04090b0601080601050405151b0d02030706110c030706090c0b0d0504021002060c07170d020d0b13020f0409020918340909050910180302060c0301 72
    0xc00ca04d0703c03600c000400410002e00c0b00d003040c40750204210381c954005040d440000e00d0300e6018000b0386066907005003049481c070880403201c0a00390310000300d0820340c103460803001d91181010440606c0f051110342c00740d0f4950415240c9081901c0f0a84500c2e1a07004050001008a10000047d0b40c0416000b02c00400c12400605101220310200d4000220106001070350000305103050f04610300075442900c00440140b8030032002c0742c44810944c0c5220218000b08298408540000a08079194100110940c03900315915425002c90313000040c0084000d4680c05200f615240007004002e041149043c103615103841c050000c88540301700d005059004da80411807500e191a000070040d40c201412440700403504181402850b81c2c01800c001c00c050000038040d00d80190110305c0032900c00040c03620b46010369418a8038403409807200401114251007a007011081596486c000d00c094001c0405010140c03540d5800c0003414030704002c0c01c01210000070001001849000c2a58082d480304041d07180d4815080c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 781533570 1250 781532320 781532327
    0xf0601051e040209040e01050a1d0105040203060103081c0c171e0a091a0c0c1e03250b0c0301061206150302031b04140109080a03020a1b081006080105071106010302010f 74
    0x508081000c2c030f41c6401f0401c510011a0b4ac8040070114450011040c0500000d210500361282202c0003505500114010800519664003814440c0f0f1a0026820407918108140e4201d41c100c0e000040045c03200755000110040000f455a004007206440c1c2512144c58a10580d42d1030000c1c003103151050351071a00c80705000d4007120803640448500c000c01490b0a050320081c04903041602c0c101880c0c099148190000141280381401c105807040103142020110802c041405d416007a14440760306020140c0d40004840d18003ca12a40213440c10030344a5051840080007160341d82c100c0e00c0e02d185409410310215a41c000480c00400c003d00d0b025035079585410281c82d14002c0340c40400044080440d001c07840b805441080042e140c420380c0d41060301a41c4801c0709545014401015000d6000700c0c2c050b13004684881003010503080541c14081003560740b84402894a000074024141c03071a0b0741c3c0b80900600000713000703851700b00c2070782e10346a820784105032541600e03800103100081c14000100011000c0900 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 781534820 1250 781533570 781533581
    0x13031b0605190b0907080114061b0a030e030703030c20150a0e040b0609040527030d052815091d0c120a02010806030109050d020f0601051e04020904 65
    0x1444003041c441800c1145516410400c440d1000c441c55090100c00542400c03c00540c40c0700349920340d2212001d0b4030b0454211176040540542540101042124a2400309030540704250020144001c0c00308007440e0500901207845008000d1107608540740401c003003944050f10011558005400c400c0f1440c69580c440d014070407195041c2e03001015405142c0000700790f28064000d01e8415110140c003100e0920130441200d09080545034408001d020601990038143e000755441102083c3e01d00c01e6114a03d00000801c3e000d400501c410350001546202d261000c2c02096041911198040340500c403091142c3c1184988400b01110142d4814840741c0c0c0c40b03d5064800000c1400c050100107900083c00384028600c00d00c0e5a990280c030440c200c00b1858240145500300c100013400103410005142e900441d460a80908801da1540d00e540d03400010600a020600314080c81e43c00612600d490302800e10709005059004600c0b0360340082710035032012a015207000340800221001640d91400c140050300816 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 781536070 1250 781534820 781534823
    0x9030601060203070b090705010f0e0315190b030a05060718150c20060a03090503070b011d28110706110a0905031605040b060415050909070813031b 65
    0x85a98000204103401000421409020f20050583c9540c0d90880c80c0c0d490070035208e400d0024202c07101940c1020301c5a8541800307454000c050f00c03d050f00756070402a0b80441a1010302c0030f48486101c0380001000c601c10300903558029009052040d14a44406131111001481042481760038089009540100c1000300301800c4c04111300c420031040f2050003008201c942c1c1080750400d41c038414812080940014440c00742800400b070600d0920b10642c1140a003000100440701880280094400240081041c0d4040c0016031180e5480d015041d02c0c030b8010b070a015002c24801149601404001d011130310701078a0a00744980c1c040380d60000e0003068520740c400c014010300494038110464a901c58540014051150540d07680c044090300e800400d910b50160701e02d41207041002410070020341c1440d4120001c14080240082e0420b661101c5400d42d82e040c100f0118000740001551134014500b40501c0c64201c807091070517000924100940c0c0c1408c40e05103c0c05820701ca078030142c01203d140d200d00e1850800703 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 781537320 1250 781536070 781536073
    0x1b11030d051e010608250e1f140421020109030818030105070e010909051003050a0309060f0305010803030609090111070b010e010605031b0a14041d0615040314030903 73
    0x20b2801c50748000c824038110604003482c18003440000b5020b0b01c60000c1714000c0c1e101c0400e0424069000300403079141e1852400d1001441010782c6400c10b00d036980d200620a1504010381940c554a014070300a103103601c83ca105417850041400140700c01c09500c11a101042c0543c1c140602e8800b460006942d408415400100344010010b854140c5290082115214a00541c0244450340ba81c21007075401c1011220010300042540004115100c29508019004003031072005400d281d480307032200c0e41810080d4500390003003109040100002603001c24042c0b80c50030689400c00030707941407081c0c80d5242c0c880506540d02c20520800494070b20318003907105900098105a01540e030b1140c0c1e00d094050500d0920401180c49410310000170014000e00c100c0740304e800c811304524440511405082aa5040b000c0180c0c20041c180784015049014503005002a20741c80c05c04401440000c01e4190320326070014001c40c0104000d040501c5030890b030101b40c6055076030200b0080945003150f0300c0303d0700d140544013009515 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 781538570 1250 781537320 781537331
    0xf180c0e130b09010501050c12030406110406080106020f190f2301060815041a070c1208010e090d0e0d0f0605070c0203060a0c0e060307032a020f011b11030d 69
    0x30038140c1d400b42c608900156401403a6070707a1803005444500440010f11a80c0c2c20450040c00c0e0b856007000150740c4180302e1080041c58005405080c8c0098126810040200e450320005209254041102134070000300780c001000c50200031902c80c4006402d40d4001054041d03500072050800040f924810794680410161800c1c1580d0020014080d155520421100e8003908003942c1040d11070307550722403145400c03203d92100003d16400402c10a0030091007032040141c892440b0000510b100c48048400c0b2156803011255410035103c100340340c0000d850f4491aa02c02c86900340130b280c0100d0b5003484104102c41c550100d894600b44a20201e200c0007005002c50700d41020028110f4008810003200c174020340464201d5030703800007038200700c0f500f144401d0041180b040050140c0c1ca450802142d2245007440c1c08201d840c08a06010303070980204000722a80207102100a131290b904001c3e542000301090028850041d5070340d0031288034040c20001c3e20420a0a00b4180f8a5107801c1003114000c40c7c81c42c004001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 781539820 1250 781538570 781538599
    0x6120f1c120509210717130b0309010501060f082502010902030a060203071b150903030209090406090203060a020a05160c230f09060105270d110a0f180c0e 68
    0x4130781400340359405448601099618101d503410382074401c0311364050300802c002ca10704d480e032031010b030814466001005031100c0c020811181d181d01440c00b5071b40300400440c403541000303000350045274020600760801c401d083c100000f8101599102ca4a00d00c1640010f070341342080c0c001207000d0b01c840d05021303405210340700d00c9004000082c1e00851013140c141e03560a8804143e000c04070704010244e40c018200d000e104003040c80c1d02440d40d010002e42e03840b80c10014580480709000c0b800c4c0f050215411f40d825596901c44c1000e60038144803155010f40701c1c0500310702c0d120403400080c15501440e8020414203030f42e1080d0800b0004510400c03405040c4480201c0f141c11000030740c08102c0c0d008004d185005a020700e03143c00313aa003480340415001e050140c44440c01c1125001501200d0000003011040c10034524401c04807586602403880312240c05049803101c90320f42c12060001e032010b11b5020303101560b001c1c0303c104251110f446500c01c2800103500042100006a4400ca44101079015560f80c800b40600c0c5116 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 781541070 1250 781539820 781539823
    0xf07060203071a0c220914040203062203140408030705072c04150603060204080c1914090c071509060b0103050f2a0403050606120f1c120509 62
    0x50007900c00c05440102d01803003854608507190684449030920700610805410142030710381116100010b4551840d0f0079a946c0b100f00c2640d4035900c52049000e07070031040c030040d800c5c180901d69000d80007403d42259500c0d0b6810582e0540640788000d020402c111514210046c021421500281404011a0f0f1164520300f4030540b50009481802c00c04220001c0300502d5618a088090b000034540781c4620456071152aa5030004c92080c002081096884201000096440c4054005070600100131321400840034280003030001d04071030200c10350f94031200800040c042810001c1010100385c45d40c20245d207500f15045620702900c10b00504905103207400030b04655840c2d108000c42801410305103c501407120054007110f00a4905492100e030110015412000203080410340f0030955403111400030301034002c150b80350030a4004131001c0e0418000d000c42440c003410030b1801b0b1400000a0000b041100413602d0742d0701003443c032030201080400c00190b0306901840144d0410b0043d202c2c240820700c0c000310f166 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 781542320 1250 781541070 781541077
    0x9051002010915050603070f03020d060515030d0807090611060a0b18041b0b071110020304031a06120f0d03050601121d100b03030315190909051b1e01020f07060203 72
    0x10f6000703104003500000c3c480c03540d230020008c507600980030b14901c1020f52110340103844018900300360010b0f81c0d017415100d51400c0010303000400703d40d41e60100343e06094400410048007680a00c00b004000f0341030420048001c40c445400000d05140003d00c2c16070580403d482c42c84070f45030248941401d40802042c019001010803070f8400d40140c10388403585030a480025401042d5000d02012003104010035281003000400d4103020382401201e0405940f962443c107404032020054110603001e00c10f02241d400c1840c0c003221441c9003170025181921000d0000c56460f0b800c032516034100b5440c0c10105001e40d00401a00c2e500b07140050301800030021010681b000303404922821305c03481c400c6a46070403074410310344554650490000c0180d0303c0d5442d00d0814020701c0c44112000c0d944440c0c611042e4104c0a100c02c07c00b4004c04403850041100290f6042aa040c4403841364000740e0f1110030008100c05030b1760070000c950314445000e14083c40000100040b071600c4480d400103d8544103030840854030a030000082c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 781543570 1250 781542320 781542331
    0x309170904140405060403081009090c0e0c070b070c060204090c0f110d17100e0906011d010308070206070c030501050a1509140f150604030c05040e010b010905100201091505 76
    0x240251280441c031000300b6002203901400b103411103404500060b1080c010305410900507500c0c4402640c64104502c00c85803143c0c0c0071280203030118000c1002444244c400b99100703071400122420241a52143c5401d0500180700d40c1c20010452182410410039a050744c0c00f0740201d00040041c8a40d84001604040c0700092250229112210315401182c001a13040c001520301c0da145002c5d006800c82c00f81e0344070000f4250000902186001290107500980240c7c86607154a008029035490041c0c60f00584500000145244100c400188042403500c800c481d42e8035416642c695440d5202d0030039001000070380c0c00050695080105102036100150845004e810024a0410708a5038030f42c1c209046800f0860420740360006034000400e19090488559402624240300c4000c60200400180f01540030b90421540106400c00c24000e5040500c203880c190f24000008102e007114040010f4940d030306511580c0c2c0304007100b000180c20141300307411081000ea8440034103144010400d061601a12007102d5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 781544820 1250 781543570 781543579
    0x91a04051b03100b03100c210c05090f3709060807170f07030804063209030f010f090b0c041a091f0c060e01020a051903091709 56
    0x30344007444040c00002031100c0000d004000d100314400000c1c02400203011803d0749400781c61200c0010780542d01a904126a0540e031f9081e980101e030465600c83e803c2407500c140000d01c0e2604900010b42c1040071200c08210131222486010b14540024030204071551000e880d05600c42549200f2044100d60000d054480c40d110b442c1079038440725404204e0b9900d1094419990141108000010300001e544044c00740000940382e200e0240001b1b64540350aa42c4102d0b00c0e8800020100001540b2000c010702c0d00c440f16000108400080c408149007131805483c0c2514000c0001d200c882c40c1e901002814400c0c044040248180d2080d201000020405400c0c02e642c583d2040c000200c10843d803034225015a402d41e041d4035194104103903418480d0b0068941c05801607810510f454033790750710940031100306406030768081e803104140c80c10070207980c1e0100c10030b141603005000000300391750400203032240030420704500440190480c1c0218090f0100940240072400c01c1d101d600c00802042c0f009141c0d201c02a40c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 781546070 1250 781544820 781544833
    0x23090d031802060d0b0f0f0f13060b0f030411040513140708070905180303090a0b0604020706061502011a0d030c05100e0d08330a03120201061a0a080c030a091a0405 72
    0x14840c20209007c2c140c2d511103900340c80703288180f03003400700da500d01039a00c0d000248650b201d99003080c196100d000c508031004804000c03c02000000310f00529040c1c0180c83c284042d01f410201d1100c441c030b1036813000b0822031a0300005040181c007003040800421200c800c0312002e0b542c0d100314000070700e41610742801c108445640300701e10b5800001228002d22180000700340030f4005840d24294070340003400c0346501607002c00568011490a005000242c403440044061500d0518406404c668407048140c0c403841845100c54025074030100110302064050500200d61056413030b040b401d000100d07107954603507890328051039201000041c1c9445942820740316011161a207070103403d682c0d844181c140030524032100c0d05000c0d00108410000403a6400340507901d01d039840366908070300314202022800041c0e65443c410400030703001c101ca441c5848140b442a518202044030300405045000384040d1070400300001041410a40e584820109908a42070303191011200703800e24800002030303400fa200c0d80f0440 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 781547320 1250 781546070 781546099
    0x60f06050904113c100503010506070f12210902240405120a0c0801060b0307050d0905070b21090307030c14120307080108161e0e010923090d031802060d0b 68
    0x1000e0742c070040b1176651180b43c1580e10b00030401c00b49a020341d104403440c4003041042000981d00d182180c041c10581d44440902d840c80805503031100e800680d141181074140702c0701c0e40140e29081302380300700d00968100310a4144503221210009100300e61040d5041a00448000304a00d40885d01640d0107200310f046c1e001041c0e850951500f039403141d000e1040b4149042000c994640c2c01040281040d45003034401140c0780031261135160409a066105004869000841c04120b0f00e01000990420343e01818051150400d0040e0694078002c081004082c0090700201000f402402425081640c184408030303400b2409005040036590000e4600302d0100c1c90340800450350000102c1c00c400341d0081000041c8c24240360a50004180705000440316400d0ba03148c401140c040348652940b030182078200008180700d01089440313030f00b580180640c4c00c1050099801d02c84180c00101d030750380540ba00c0d17281c08103604480301c03c1402a16911035009610440004141010490b1a00b020100320411181410134039042c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 781548570 1250 781547320 781547329
    0x90f010b0a0f0506031003060213090c1d0402030901020408071d1005010f180f12020306011e0b0a05090d0506100b03062d0a12060f06050904113c 64
    0x14020550895907141d0184190306091001e580d1191b40c00321101440c40e03494864104982c0002c01e03400310203008031024040310b0150f001d041c502c0b60715464000300d211483d507071260201d0174541c2580d02c0b0300d40000110700040025010386010703100308002e82e00c5080c0d0352007458240110400701841d03645140710026000c1c0e0b00780b10201086034410303155056003c46080c2c0c110340140b1080040356188a0103031021691302e800a810b2005840000040200861140101403074400d05910020021204403405030f02e000411103000100c40c03059810035102c2e01030400544040c0141c0e20110f0300b1809141c03840d01070010005d0854000c5140c9420305440640b43c00481259200441d44190811500341c5240342d90000384402003501d212401c14604d50b070b41000002001614160b01c614041c560010109060050720300c2101d40c440141002004528a800c0104c3d009403c002c01c042c06149440c0c000705010340f2140300403003448000c02038903e500951680759140840100700c1c00a01e0004070f10b5107040c0d900780f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 781549820 1250 781548570 781548589
    0x703020a0617011d3607290702100201060302101d0f01020c06070c0515040e09061303050a0e090405030c0f01021305040902031f06050f01031505010503060a0806090f010b 75
    0xb00900020312541c800b0004104030320390b958180b2804d48044007501702418025105c80034800d140018004051400c00041c03203450341701141c914501c1c900702d424200100c1c90003c0714983c0d0f60640b1080360140c0c601600342d00400d05a8800ba4200310880300b03c05407154000d40c4174801c41ca6100030462122245005d101c00c103034044030880c0c00360b48140a000d00d01c0c84c2140107410308500c1070f00345039040ca44413000f054040c40135040904801d10046000d0103912070040328560f102003018024003051a160005a81916607010043c052000016000003114803400c40d2804079580501580c0203403c0525150341c0d0380d8888090009103000d94800000070300418002c88003128601403400801d6420941080000c168401d02241c0c50b104524a60625901c0a0703406000081e0703003200003400700e2919081c04a400c1c040303030340305040602d000024054607811184400c01c1d91000e00c1d02c40e440b55035490100301c6120482c1c10211461180c00d04001c60b4400002d000318420a100e0f00900c01143d418051050984 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 781551070 1250 781549820 781549859
    0x20c101805130b0301020c030a09080f03030604112205100207030305070b060418050109060b0603010302030619061a0301030c270c1205130209060108010b16050703020a061701 77
    0x141410000c010a02c1d000340302c03020260051100040411641000900b2644040c0740c40206030400b01d18030221302c0d003054104c002005008041c000e0720011400a5072a440005c140034450740c0d44d42e4401c00c081e4003c20645100500110481040802d14902c1000c075200500c40e4074460035154810741c0c1140c0c80800d80e9001c0300c1d8141c940c241007072440d81d030b4000140740007800d064109a9a1400104a0b110102c0d4860003030300403000041d000d0000e0400e07800790340c00406400c0c0590410401040103881c0010740642c40102940c00e441c03542030810301640681080d034811440030745004051856180c00034000d42c102d0307104401c02058140e0303c84100b00c000440150700000003010143d055005102038028000c45012440e0128403403c05044240031200103840d41800c001e01d042c1ca503421810011600764000c0400d007000859585010410a114882e128080311b5000e00108104200f200030807001b0080c41d401490003042c1a1160001042c00250310801c82c0d9482c00c01e4000144011185003204125 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 781552320 1250 781551070 781551107
    0xd05061006051903020702060c0d09090b091603020c0a0b1801151401050a05120c070b07020a11010318020409030e10050901020d030507050c12030603010e010605031504140706020c10 80
    0x80fa40200690080d00400307801d0b078100f0f03c00c0041c030050000901c460b22800d82183c507840030013410281e2920848808003c2d690155800f40300340580c2d040080950610950ba038a00542d6030000320030f40606052044034020705c04020081804001480c80098219240b12240204140394200855420b070290522400c0d03d0801800503550303040d4440d0004224a800608000f8600a8810b40c8483c1c401022103100074402004039030f0008009120150b0398003c0b41b244018481d002054450182444601020b241490b50703501d0355030390001c103040c0d2491103150002e0040007a02c1c900d003009868480d0a400f0f00344545c5001214140c024029400d80d03d0b9210103038010500f030052044d00354018107003d40008180314017070040c0304002404210400264080c2c0f1020340d101c0c14648249400c2d9103280543c201c00340d041101c24801600c00041003a8900d4101c1d100000035101e40c10040250b81a51004400900952402040c0c203500040c0c43e20342c201040d11040c50024440108481742d519069804450 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 781553570 1250 781552320 781552357
    0x509180135030301032f01120c0e0306040c06081f0e0c040506070f030207140f0625380601030f0e010227101218020d0506100605 57
    0x6022200640d0520681d100c40724550000124445491504264421103400854841c503001800211104d4504242a03240c44205062039a0001e01821240710a450700c240e0384030603602c1060b104200c03c0ba010345c0080d064411a042c10b0810310f0306282140030b000040780102c408203c05a6480e00340c542602d03207202401c40790a003408008501468098210100b0f400144400b24007580c40380014a081e0344035107000000202c461901138100340e4940c1c071100da07040342c030500142c007600c41e02d21145c1400b104584030340e50b503013100c13003d044005400c40c04c03d4908c0301114a100108940203520100990000034082c00d085c110030440c0c1c04101e6007100e54801c00c59000c01003020340d4000c1d0020b2003a409814000310b03100c2408940582240c1200642c00145410301a052010a400703201103031110342c068426022026105002416030052031001046150f55009c02e9446041d84082c140c810550050070480d103038100e41841541c448082c3c800400200c0d82c0c0000043c1d040c002c10440e1a074407960075503e101d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 781554820 1250 781553570 781553609
    0x1b030e0715080912251704090e010501050102070605040e041b1203030b0405190e0f030316090906050d080a050d02190f02010605011409010314010609080f010c09052e05091801 77
    0x80081210504442c980d074070b5020b1000306c1a24030003610140c14007074400120142d01c0c0300c525007540d8040e409281507407c1a0810310070660320204507001da0f0701c031101d2590306441e18600b5035042d00e80e6140035030b44442d425802203111500101c0039802a030181d80c081c411550800208022188152807455020442002c00f00b503642c07850f00503117450b1075000705582c51400214002c1d41503070300440c0d805000c02160284000a01c1d0048803e03009010710040400c2814108230100340f1008050380083c2c813801c008501d0860035445a4110381c402490080b095440700340401e13072006400b40441808011510640030644044d1052080104680050b51143d44000041c01d100d1181c0d032100315810304258480d01031204000c00a0034450080819a41d44411580f4103844c45042c407200303601c2c000c000e9041814400d4031581c081d0b140d40a41d00101c8034444c0000104070001500303070307102e10850391400701c031515900020b070044040e155030b1106503070941751443c201080f076145c280c09024055495000906004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 781556070 1250 781554820 781554877
    0xc1507090e091e0708161214030c0f0109020907080f040201120b0d0b04020909150f0604020d090b0403080603070308030f0c04030c08031c1b030e0715080912 69
    0x1030300081082c0507109022124542c21050840030b00141806602400c2d040103100b8041044040e0301e4501180205e0841c20325812074400c80300700320085d00411607100c0d4816500c1d814400c07a240e100660045940030203030840c0581c06804100f6040e4880c214140000b5203541c0241d1901784141c20001d400315199445038011740341c812007100560311a5a50346d021500035144d1400e60b8070218000c3d07003880325520702441044401c1800803c0c000da1074100404208446c0000e5071b9842d08a1758810760806e081e51101e001c00c0c0240250308000301d181e400c15008200740103210365400d010314003036501c50610303980f00020306948121600c00289441006c0001580c010051040d940d0040011030419151a40d2a101c2001c0540607410180300c0e80c20006201700029004c0641c40460310002a0030700214600e0300c002110048041406421301d500e40c90f04401010007840345d84060040c40d40d02c3c40c01d04111040003014550215800d529a01c5100201041104503000795032240007440e6002c1c45d20f070b800d1980c09 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 781557320 1250 781556070 781556099
    0x90702030706050411040212040c0b090d0609080f040b090a0803040812090a1e24080f040204060305070b5e06032306100f021f020c150709 61
    0xb03a8010100d0741c5405d2a513134880c0028402100402408401c5090034280799448600d154010b4400355810440a0b40070703101e403401424401c3e00b0140020f8440b040d810850401d00c65058071007a2040c0c00138000c182c00c12990083e0001440680e0351160542c0c40d400f03415603d1080340035400560b0300c41030304071401404031401402e2440380a030511800030366400020707544417200140c4020803d403081d0203000e8044803119100d81401d40700d2525444c0180e00c8005042c0c090701900100c181c01d14003000806548498004400956020080321401d56aa5070f07452195044516606058480c58001c0c0b10b92407404c12165110301c1a03052940c0000035200c401c6141070b03056160182522620b4009000040742401c1140d004101644020600b608040a100c540312005030985c080690500117200c9a0345075030341640001c0c1e00c141403241404072091000ea10f000c10720346507019031807a005a40d811303500ba642c010300030801c0c81d1011039103802c44d50748080780640030466600d80010100e040401c50505401e02d031703 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 781558570 1250 781557320 781557323
    0x3192610091a060a17130c0605070f0b010303020c100518100c0503040810141506030903160f06140c0304080f07060f0519060302011409040b060a09090b0907020307060504 75
    0x10780e02a1851002003000da400018450000c00c0c0054416902c1500d08444158072810a2075113070040710306c5a0701c1481c1c10b24540140310800101207104410800f1002c000802c06411a0f15100725603903078074000b0360345c00351b400149021f1013a0958001e02d043c040c2060b0b603d16003181d0500d20403030f0100c0083c403502c40c003101e00c0e1074100402e1449010106a083c802080a009a10003808815220b183d98038241d486490080c0040e000c104100005050304180045400300d080b070354a50340e40c448144451460103074010032808000726070102c0d800c1003014420041c40f544601c400b8403a000b038100401e01000e40864242c400440104001000a00910000c000d051340682409080c60040d427941000c44060744110000320759500140190149c080503076440030304074940284025400d50340001d0111100ba4103422450101041152640d07496400011200c20090003d94460070760315001055040c05114540b4668509007000f08107040280780345100d5030786034004600d0440c40340d1301d103802420018070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 781559820 1250 781558570 781558601
    0x260a0c17100801050c0a2f03040b040e09030a08011502210702030c12031606090b040b071209020a1701061827020d140319261009 57
    0xda040c40e0300e225641260040c481d100581c0225070824201508540b030140880304206001d11012080ba580300c3d5070420300b103d245d604861030500300e01c10780031480d0300e000300c4105d50300011602007a03180c80d543c09030080f90195031400c00940c135503100a90f1a88200310786040015030070300051201d54001d01c12540381e2403140c4100c0d004c02c0c0e1009120010315003240e091150a060004520b07065141c10029203a1030340081f10030200142183e0601692840b500d070904859407103a031900810700040360b0202083d16000030f001080351410349000c0088250886141021a40a403000c0c01004294821809503035405813004006a01340140340030381095a46030000c656481d007001041d1000060101c116100000e8000b252505100d01d005110412100e0f490071900706084402000d83d480d407000f00040b45c1c001d0354180d01e1041c203035200c40c03e601c100d06404848113a1081000340c03140d4001324204129103500800c8007008107142e040302012100b0b8a0b42141c05e0b406e118103002203402940016884105041e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 781561070 1250 781559820 781559837
    0xf0a17030d0f05090d02060705030a0905010921090b0910110a1403040501032304121e081012030e090601020708060a05101a04030609080906031006260a0c 68
    0x10507003034419400b40007031066110700921150850401140341d0081d0140050182c2e494100d00080007400014030740320b1545d44400401e02480800e50003807903101e4200620400c0410601d0b1409640440c030003050b800608003000000e0b0903991442510001500104058030459030324004540003042900b02c030308540070b8203010700c0c00550a88000904000e200025580311440c0c500054100d5070b200c3c03040603c2d40348016688565100c2080815401940614054040c94200004039215a0355600c00c07841c1c1c1440d44250340080e41c00c0400540320f00712a2250120690f1107030068001c0209680000b000324094640c50103551811544e66a8044410b00c1210b0950703903203401c842c4c50405d0544040d070580d6618024041035524038032400001c0c1c94901c0103036000c0920031f1f4554029101d40e11024102c699104016800c00c052034084410220300101802c1d01c03402c00c102d4a914642507485100c01081098004600001507444504400c00f4a140c45188541c4c5411b040006440948079603410000b222 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 781562320 1250 781561070 781561087
    0xb0d0510051e03010b1905120106030b09060603100c0813050c270702010e0a0f11121b031212130203011407080606030105060a0f020f01110a0305060f0a1703 69
    0x10b51070300c80c1060039141c0809048810002d041c00c650003840914040c0310380c4002c445140104144c000c04075403003941c1310145400d40300449401012a60401040558224140310000a00240c400d0003001c0803425a603892610fa21250102c441035041d440110b48140001528a0300404030211100d0148094038010881c8200260359407804109270080d03402c0c4611036101115003e0300c032039030069040c00200502c50302d80440307030b50740c804080c4028000c107070441017002004503075080c036010644003604904001110082580e1628410b031440c6084400b0341c0040c0b0010716000a1041244813507020a52401c2040c54407406031510041403140c0c0003a00e03840b40f20043c2c03400d101765800e41140d03012095503420043c40043c1fa001016188602c101c07001d0006200c1641c4040846442c15444d0821000d09882410103904009203605440c660794600314409043d124008018406603843c1d56040115940f2002003007a120354070000d81e074029190746814845036286900445803280d400703049a0400250 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 781563570 1250 781562320 781562329
    0x9070b0a2c13060915030b160201151409091b0f0a1a1c05041104020304031b05010c1218170706020705030702011b02010c11011809020a080601090b0d051005 69
    0x58490b4001c03590b07a9200400601c80e06200d40200d5205081c05182024030310b464082007882c0190500ea4411400d0001ca181d141c003d500015040d058009902c800c0b0b81d4405d8404651110301140f80d00426149000499071800850b1a41e210100d1842e0702052000c1c2d0002e10140c0039070b101880360802c495100109500c000c811030400d00400d0304031556540c6142191006002c0b00c04046076031001d04203410300001078040046041d522909840c01600ca42c0c46040465044403400040341e4440300943c0240240001034005007164260b0762130702280703980d103e00c6080c200d555200c22403090074403505d800400036076510070900c01c4c5a80d00d28910300f4100d40791200003c0b6800b007407040300e507070340009454411075800540000201d410b4418100000c0b1140d00040e005541c0000b00078a010010500030301c29038000c0700d0b2018074040351030180c10195207070607406000b5801182c501020943d600c000460700c0d8490301900d81a28064140103043c44103102c8103502416000e05450364060038540c001c41c031900c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 781564820 1250 781563570 781563589
    0x4200c0a060f020901030b090903041413020a0c0b0105010c08070609050715020d080604060e060907020106120f0b010e01061e0e270c09030703151b0809070b0a2c 71
    0x402c03840181e0301c144480c005811031381040701c0c0501890081c02004103880c008010740d41100c211403030500841c1070401c00109403000011004034280c0c4042901660707503070703c00c284d0403009206611841c1540d80b44c80064813003400c10b001c0106400c07400c200800000300f031500301401051282007110740b5142c59110101e0000c1c0d4141d04200181d11400c420550168040e600c242c000c1c400b501c003002620309120303200b4502140206541d024039006000b0416440c0300b540250700509114802c05030a92181c035002c00c0103c0070682c10f551400381342001080f13540030b801c00e09049030300c2c035112095800a2000c0c8400100c4500d0f400c0d10900440f0104010981c40d648144c1c031824010b182d401a440803802c240d02e017120703000742c80c014040c2400e1260f00510745001032910107680e00308481484403030202c06404080e09400f6040540d14500380d814000c1503030000c0c09180141d082d0800da5441d25200e00041c1418000c2002100000e10380340c0000c1c1e501010324000ca10900b900c052400e8960302401301045003443c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 781566070 1250 781564820 781564841
    0x1504080a0204021308190309090b090a021c02041202030c0a0621060f0e01090c0914130902120a050f0109031d060903011401081e060a11070c0e06040b04200c0a06 71
    0x10f92006c100d82c10158440c520a01074540300d8020031909400300c0104045c110007c04c8948501d5001628100000400c0302d030750b40c1404480802c0d5a40c6896102002c401902024202e001e40f0800800780c003903107440c1415401b03503980c1e170703442c1d0160000401c03c58403440400c01c6412500e81c1d07100804511102c401034014050016a260f000319949000070040132152018880410044521810312608000843c21411301c00100c0ea0031301c2c6051289019002004c00e000d00a42c0818403821162012902080c920b2007075000c2c4013075030f840c0d507205900749080c0c0707203e940010300280d0345000359505044881d50602c1101005440c40381030001c102e000c2400c45061058030035902800c04010411102c0400511b02c2e0420218251843c10903900e114130b980785806090440d2280c1c41e292002100b2803480c3c00d07214003d4001501c50186943c5245143c0195000d8a0843c042c3c4d0600e419404241801d0244501c001200c940d400c85100c01006007851079003002d84001106d026482a510114000703006107010308 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 781567320 1250 781566070 781566103
    0x1205090307031b0c09050f01050d170307051b0a120513090c03020d0507030603050f0a030801140d0c0603020702190305030304120203091905100f021015170c1504080a0204021308 78
    0x7c1c1042c410300d10801c081640014030980b0b5284043c00002d6a0411001040e40395030b00c480c1d2680c40d40c4000fa981070254420000d030006999010010300080001c0750000640203400301c4440d103040c0c034006c903a2440394903001d03158042807880c02c100300c0c155a80551947c0406250050401c0280c0700c4180503628151281c0000940710b00701413041c04018861407002100d0704c00104507043c502d6074080d282e0803051250000f150208402c00706540c68185401c0d45043d405103e0594003a2100409002074002c0b02e8241d004900c0b02c01d4902200c5003a4501c0c00030b880e003200c025800c503621991800d180d0040806c203401107010520042d20661034004061013800e03031554240380c101d400d0005020081c541c0c1d200c00404c1007400039141e510203402240c10a24401490300114509003a4500c0c02c1e510042907000c2c0c20390107001d03035104007012301c0400c9154002004403004500380001070b03400e00e0180601c0c000e00c015070700701090440061501f64001c0c8482948841d41c164a0380e5140800b42c1000094601500c44 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 781568570 1250 781567320 781567331
    0x6020303010b0a3005010e130b150621070c0f020d11060f040305010b033f0d0c0809010e0615010908100608251a1c0c1205090307031b0c09 61
    0x204d11481c0201d60160038610700d410301ca0f250407030450200443c0200302500601890000c503650700284012400300f118003401659403008961964000440c0003d021155042c208005c941e28900c14000d05851343d40041204030506080d400300040c1c603d02900455918090740541102a11108045c000c5032840d046c3c0f03691220b145040040c25526448001403007600030300c4100202510000c0d00450790b040298651200580320030b5501c4151100b004140c3c40c505010401d034400b03c0c5950071a03002000d003590307101040d4030703420031441c240e4001862640c41908208005554400c1203888121280300500d000c0d80d05583d5840c0460619004501c200c0740729441d65000d00c003a031820402c65000c0340e103441070034940e542c880d020021004514001c13100c2e04940d810310900951410400c0d2402e1440039400d040c01156034503180c030000c180e0610b240c00406c0c240c0d042003c401c0c1c81c0b07204040c41a00000c000d5460140f00c0d69007100d43c1848861031b404650020449080840c032800412000b4010201001a0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 781569820 1250 781568570 781568657
    0x5120a0b0a03030e04180b1b040915210203100c0507080c060f1b03060906010309140d111212040c080304080d230d15090e0c150406020303010b0a 64
    0xd890003c40e0202a180b0340d0a0450b000a40403901a84d00449400e01411040502030b0700103c24400e0341d00ac04121402d081c090003040000302003400440740d00e45000d603001c25421955001204070305a01030351607000030030014008a103507004103000d90500c0c0744c407901c0c20741c2c0c2d5641c0204a401c02e5804140c543d00c004100072900d0040c09030241c005510302c00c1220390805c010201e1145100c01030855000701004404205c06034000c0d000744a049500105c41c60710813240031401d650b42c58031140000e000541c4007030382d42184000820345400741c80e2014206480c0c91a0076141ca82c1d5200b01400485030b60103680c40000b140c48052000c1c0c0f02038001500506401184400c0090188241d1844407401c14402d480c0c002214603194102e5007402c01e014000310303011007146d01505024216510200c003090400018107a00800030a80d4800000215014104c01d4500303015020203025a000e100056441000140025038415010701441c0c203e40c5002c003104480c20800b00811a0211540c51200d5581d074440507 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 781571070 1250 781569820 781569829
    0xc050c0d03031b0503060a1206060b04120b0106080907050409080408030307051215010903060902010e090907050108130308041e170309010c18090e0a060624030c05120a0b0a03030e 79
    0xc201c98603500d40b160643c104400051f144484500c180e0540920504082d810803145400210040111358956600c070b90307559048001440c44c103c021034441e04404000701d1000d0080741c4d0385015200303050050800360704020a00006120808050340c0c60403081c48000b43c0018200000c6108681030b585490312240f005c0300d00840c1003030103403410303104021100e00035282e81d920082c44011070350080c2010a04ca4414001070b210031101c10160758001550f001003003285100068580103c80703080e41e42c1d00d2141d5480c11615091004010300500161501c000315000c18514a00100c600d400110000c21409480d50384000a480c0302001003030486e404001c20500120a1040802c400340c2400d0a080b03401001c0d4511041d002c040c010000600d0303036101342c00d03101c108c03c10041030015448441004010380340c8a1404c0f01c50903d03124140207104191041500e031740b0038003078003600c200e507600d40380d00f011034030b070303d8500038040003410407054580d11602040c2c00c1d40c60b02ca03810001c0d03010f621620350080c022070900 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 781572320 1250 781571070 781571111
    0x181b291902030a09080a05060a180c03030806030c220b060c1c09080a0b06120f010e03041a0a05040e1e041406071805120106030506040c08010c030c050a0c050c0d0303 73
    0x1031540d030072020086d008542d001c1002035021414140016103003010181d400039914081c02c014240c1c2c0c12080000c4209a04404001e0081e40c00b1401c0342c1c80c003051401007100e020b100b8081440300390407814008030322a0701600a01031068004024501b000d84420080e07152030340202203200381061040202105540040742030018007140e1000e0311030760032103440d0584020000b0340001d00070b0350310f400549031b054414080120f21030030450080c40b204200400f1035550750498003520040581240755504c400814104480c1c0000d840d03181c1500707003032400c1600e04e02c041c00144150181e81c1e610006049588244001d544298820f0441492804014545500c0c00c04018041018400301d90307901840d0680310960302c0c04540d8111255a600c195044c00940540501d50004025105010612007080001c0c5060020b030340c22207000b00304160b294501102510b00301031a81c400701c0c0c010404001a07030301c61490103015a014104a55001c103044012904510303520f0810782c00660b41d10314191410840c43c1d0703031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 781573570 1250 781572320 781572329
    0x20d0f0504120809071707051509090a18062c0606010225030b010807090b01050909040803100b0f0a0201050a05100501050a03060801181b291902030a09 67
    0x104a00c1c03409541e2011888a400310074028070980100040281034104070b50005010294a1450711542c0381c51101d41c0c41c48030b1301406118044c06800d2110900c50b0f14207407041c0030401407604502d6150800000b00500381084444900c801c0318540c640420101d00444520058007540e105290520700441d03c0c15001c0300145000700c0d005001885036507a4002492003c5603070f8134a45a01d002c0b080751441440c590310b90700060485400d040006444c0710f0110b00c50045400042081c08030540800c0111410711848610f02d0f4020010800708d408200884013855210034080b0007d0320190701c0d811403034041e41010050300187c0100285054100d942030145940009120342d062182d0304254690007140055030040d2410818082202c3c0e0f1803e201e50010700061180d503008201070f005022114410304100340f03060380c0040051808004000c6503c4001c800c0b170300d11803081448004500240d446440e035038008c04d202940144180c0030860366400e0748140300d14036a0000e541e0b071400001c0290920595502 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 781574820 1250 781573570 781573601
    0x7030c0b0a0e0d05160507081c0f050d0504050c2d0a0b04090908130b030f1e07030e0f12070b010e04030c0303050402041b0c0501060807060e0f0a18020d 67
    0x1070100b1454400100080d030031081d030a0250311281c81980120f480e648124024005102c0c20f04005881400071586142080c0407000c0401d60002c40041601c1c0f140200c403140000400c200102d540c1010154005500144244196508101200001007880e00000b0301c0b45003540785032845101d424010000d000074102c00f40c0e2507c421900d00441d030001c0b4000c2c0d22038840d40c3c54407400c1071010002500100d034070780240d40100740000f03a21203260b0445900202c62140c10f0390a400b0100d081c000c520b00141064401c0d0361a072403101e41da94441240a492088030740c01203849072201d41e080005040c8268a000d00b00960320300e454003070904100a0520040c0d00151182c00101c05100109910150514155406040c0030a060f02d503440490300601c0241c440050518030400300000c1960300401c4666954014002481202e443d41030f04c1e44ca40c800d41c0b140c1d8003c01c44074420740d0744e1410401000c201610f0001c145403c12340c0e0329040480b0140d00c1c00391a42800754002050340003004a4820205820702001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 781576070 1250 781574820 781574831
    0xa0507020705032805030301030506040611030906160212040b30071b06050903030610081302120f120a0807020a2f1201020d1802090c03070e040207030c0b0a 69
    0x50103e62141512000c201540304c500e5010403a80c1e80c070860118213268007900316950b940e0744c0e007016900c5060944013103030740c9400c001c0c1c3d01244248240a8a024094201c0681829121100443e081c0119010b000e0203600034001c1c1d035607207000741c10042c100403d05012001d513140e00e0440d00c0c0028820002180c480c81ca0302c1c0d010403820040503000b403035200005040c80d1409246c4000e19840e1851400c00c02480e1a085c00c0c10031440240120103540141e005841d1008801041041522a00000c0b181d480c01c01002100c6840035160180c803c0209401c44416155140c130017140709424540b81d01402c032081c000020b4010303802540851281c2d40300f4a20300c05071507003000550780c0540c50712404014600311800c00254030304c16540c00706070410310070009103181041601020364a01030341120420704880b92410f00c03540c4c02c0312070410101d455980c1c01071200c141c5546103945072070341c1d410140411081105032a08482652124030082c00c5260198903030f0389410001d031505402100c4000c044c80c100c01d0416 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 781577320 1250 781576070 781576079
    0xb0d080d060314060c090907090e13110307050f0f19030b061201020408030405010f0210050406060503071212230c06041101030c1202090102030d1406030111130509130203010203040b0a05070207 85
    0x154180c81d107001e82140c409501d5145c01c94101d4441c903042d08642cac4100031003418000111599600304a4048c810403105284288802c109a16100c051003582e4010220034170840942c980b8903107000c0800001000c1003c10502c100581903039403001c1d002100c10f40c0049007806010b290440110040342000e900940c60305081143c800c1c2c40303001d00d201e9503043c00500c194403466640244205c100424042c0020040c502e814107200c0040d10491140500a0044201c0401c0c0c5001c0040059007444d0081c810000322200700c482210800c407a100440141500811040c003501b26000041c9981e1042c00b00800c82d90801e170610043c403020010300c00c0d040c5480c0c155403502c065000041c0c8060700f4860080140c4842941c03005034158456080d081203c6440d000b490b1690603134070340e41d082c02200160020001000c0d03403c05a840c030320824942c03003203684000b882044586800c5951b1075100080c41c0440111351040d50201c1d007a60000d0320b00320750b03120000003000840b10b041c0c4540ca5026500344004d08046152 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 781578570 1250 781577320 781577341
    0x3040608100f150c150f0b04061a0c01020c0f1606111905160902040320150c01110a050910020d0c080c0109121d150901030b0d080d06031406 62
    0x351003072400c0d6194941601c40500c0c090071303007400c0d42504802c09a22007900d03200101c0051410305041d2040510b441000e2410f4185445004240e51350f104914a80c0c0034100380300e10030b43e048900110000d640070004c01c1f031040c0c3c092112940c1a901e800003403804a08407a6585c45004287e000340c0d04008003035510340707420b81000405c20b0841100348040210800541400e8bc1003000c00c5500f00c2c1d0b82101c695000606810983c020300c00c5902a0720480c00700c0c400503200d101411400c40b40c0c940d12001c550001c2240c42030a070001c0c0318500706d80000203161107041d04000103c2c1c000b10340c4103010070004201200d15051035251090012014400390a421051000c00b0704407114041c40680020400300d540d40c3d1090b402d50293d5802d5400c40603103403a079610340c2c0c0002e14014069003110701e0416120903050080c1004c101b0316048002001d031050034480c41d800110b004152203110300ba4484c0e50804040d000c198a00000d110003040d20f50040391003030441c101501d40f4090705660490f1030344044100180b080d003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 781579820 1250 781578570 781578599
    0x109020f0f0918070c03030e0c01091e0905040809100f020613030908120a020d0201060501021f0b0d050610120819021507021c020102070209010302012f0304060810 72
    0x5158040d581c44086260100c0c0c04503912800d0700110a01060500903485e4100103421019440b1799414400b481551882039181e90844800e5404581c2e400800e000741c51108004024203960700141100142d4ac0b060802c2c1138031010369080d110924002420122400e0040762808480524101a489103050404c001e644000c01031007101c00545800305041010320480c1c4103402813448108681504e01640d401540d40d034044a61440513200340c0c400c0060040c0107004050032104144c000d416188812000c070012094404055502d5541c1c0c0c0c644950355545d4081070b01e0b0300030700900c0105003178034140811030b075140480e0300003d621450100300f83c400a0348100448402a10903040f141c90881a584141e141c2282018200a00340c000800c0100c42e0340d000540c0c400358002c0b030011080b5100442c000341c0c00c0b4402d000029400001c0320005101650044080003020070304200c7c400b8120600000e42e100400148082c0c42e000d4200080400c982c0358800041c54101080b03c4405102d2850488005151384 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 781581070 1250 781579820 781579837
    0x50c01020d0f29061605070e0a061a070318090c090905070903020603010b09030106031a090705060c061b0d0606020c0f0109180b030c060301062f030f0f040306140f0109020f 76
    0x50000c0c400384140070402050700201c1c0d002d41290900c7d03494514007280000102c1c1c00500d61842d00000041484c0712109a141510070090102d01c5d00c10310f0340741114101d1a01e08211140005400005400801d920441c0800d96107607440da02c00070f0421180c102904c40c0603100c0420070101d11001e0026035500310442c0c2c1102c00050a5503503807809400801d01401040c0d0020303000c7c100c041d0503451740d866070510b01486000c4001c01d844200f82c544042115500030140c00b0f5900385d00140004608004003002182ca5509589060341010f8500300d0010540d029a008400140c02000310745105050400340707106003003424242180d0340f5007010800742a4114840b4074035070803034541c3c0f1241c01c1074409110000c48118060402903403581c645030088c020201540b0300c1600a2005004050b50000c3e00c612020754916070400385150035103e0940582c01e41120210100d41001080000300003041c42c8100369214076540f400f1901403800c50041900070a0590140134510300401015134a035404d1003c4602d0345 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 781582320 1250 781581070 781581079
    0x2b03060906082505031e0c01051c1d0d03150503060601170a181a0708070801060e01050f0d05220201090515090306090601051c1a0601050c01020d0f29 66
    0x8002c101c0081009960b55100345d415010310003024074104810307400800320004241c2120300e840e010b0b0004666501c90b030340c13000302c4484502c1c010340919503a9421640c00f6100081c682c024048400030310354200007203490180f0200350364900c0c3c0c1ca0a81d4410448100800b01280540b805280103000a400100700c8441c411404810320001005032885510405d24030000359080502186549030450903655021480206403a0303420016100c43c1c032960030988a45056510740006918151007035801082901d006810b111081c00750000d012040f80140403d40304042c030126041c1481d61060300007004003102d03101802c100078141c00160340c2001c004000c950060307442c21840511411100c10718010782074074030b916006400a018011388005180c031705a0303030f003201c610b908007580020310302808007625001080b80080d03010b5800a00c0d1702c8840c0940c40324044c10800d01e8892003119803422a8840b001079051256107000b0890f000e040b81c4600726400e03440011907601016900c058034000e20415020a114 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 781583570 1250 781582320 781582363
    0x110a02040519230f131407050303030405060f01060224062b0203010c03020918090a0515010f0b03040b0a0b0301021c02180d020a060c052b0306090608 66
    0x1840d074404001d20030b1030464034080100300c00349240e001000080e03004030802c1e0041d030b00100c0c01441d070302040c0358085e0000c5417100c82e0000440d81c80b244054244c511501290064520000d4592002e02c001d6105038880e030040d0140d4984805105a0a40183c0210045501502c1407541400030140c0b002d042c48200d5013440c01c0740d0f86400c002541c25000205810301850701e608500c07050307d00780120b9140680300300c000b0b101502d01240224101d0240d43c08895001e42c800f01000c3c4000b5501080940048858007500d4403c0c2140d1141172428581e240030719a401380c40c400401c480710b01a800721002c0c0c6101007000e451410642c82c0c954180b0000343ca404005580e80382000710075175096045800c45501401420360b00410900d00f60002c0d0803000f0b00032260744150320351989030315281e00c07034004440c1d008080c00845400c0400031100d1910307054003101c0764490304400d03d10040891040341d40c081c1d02c80c2885200e804641900070246c407c607a001410342400c040051019003404110700201560411000e40e9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 781584820 1250 781583570 781583581
    0x11419090524070e0405150603090a0f0506040c050418020f01020c03010f0b01032703180906030809040b1915020a0804121a131415090309040c110a020405 68
    0x24509905089a444501c4003240034142c1e02115081d40719014907155a400030500e0800d000641e101254400c1034050803040380c03616840e11801071504100c0510840344003a400359248808500708160541e42130b48280308210420040580000c080d007130940d01171003070030910512899401d40c044802842071241e14503c5106910820035060450002402804003104009090000300b611500150009040c00310f8150407400d10403072010780c101a10380403007098540b51411900b0280861a50b150902110070001d2880c50314061f840295024940741e82e0750341190001c102c1101c2014050f00d000355015805840a1905100342c0c1c41156000f1114640c00614901704070f0803c60301ca80010125100490003140759a40d000e00200c200d44180b8440341c501400c0c05009541c240121946295518144000c0f000944086000c4076209a086e08580c01c01c440610807080c4440300f00d0f014081c0f07600108000405180c54001c0301c0b10f100352400c2c4542c140c2c0b110166a511036166150181c01a9140e101082 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 781586070 1250 781584820 781584823
    0x1e1309020d060507120605011b06110708070c09050a15030b070201020702121e070b04064a06090303030f1f030b09061501050702010e0303040909060203090114190905 73
    0x1c2141d038450020040752914040190500550100403150103182c1000401c1d6540286080240428100c064a807911156612400a400d4010b90b01c55001c2003844003c0000301e00b60050841e9511400f04084403a003000110001c85a004202801a60505e082c0000741c2c003802c4128015039402c160a8075440d95204030680c064411060029040080d8824000f4101808070b01c11800014540c1001405203145e11015500c075030fa40502c61800100b0002000030038021034601140004181d0510031840b0350074034130450843c100d50140d8281c0031070008858458084642401d05407002c0b50114100364000c008617540380030040c0905a10740c8200d0100e14904003c0c40303d01014981591307080328543d203900d801643c0c5030098501d208148102c03030100312180d0085c00c80c1c084010b01a074901d17040c2465a001100e00d0a01510140c3d014001040046421070130750040030195130080700d0142c0e50b420310344800350842da50514421090808582404541103416540c074180b61840728000c80d104101e1305102c0e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 781587320 1250 781586070 781586089
    0x1d010c020f0d0803090111070209070f0c0210020105070306290304020f03060103050307142802180718050303120118020d05010e0f07020a030e06071a040f021e130902 73
    0x1d5901400d10041542009030f070000440c89000a00000e00c1040d00d2185040c1003070191010095002c0c180e04001000544a000020f02c20440b510b4207868171000ca0700414442c1964041c0c680043c0d45907001c010039690107000c0d0200030308008490102c40352203070300359940061080d2008801031100002107000d554a0090110341e00000505482c1a541d59203011581d85d070020400f1038004810741c40d0300070b05100202d180100051500042d08030740320a112400300c0c01c0826203089034848164049a40380c0e00e6001002403290006480b95102c00c0d03d0b052a002041609510603482640b0030084c82010080c10045541115461045c02a86c20304495605d0040c0c00b03202410014145010b000288041c40108440d010707040345607014120b070700c803084101d03250328107004090702051a4a00015850400500405031903005000707411401d1301c0c03004090703502001510709940c070181056001c8103600d8507141500101c03900010001d0013065980100d100168402c04440e48981e8071240320301991507a9010307 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 781588570 1250 781587320 781587349
    0x20d031e060f08070617010504020d1e0507111c080c160f0c0803121602030d05090307031e0c060908040b031f0801020703050327030c060f071d010c02 66
    0xd2054030b450b03000816101001c2e101da9103072485500030000c0c0d954041c00007400b050186581800c090307820842400040d600070040000d80e26612040d0740f000094501c42c68110860502020401d82400c00c0d00800c01c6044080200e002d800800b884500c1d403410300343c40038000c2d0481c14907138182d03510003a01d4552409144003200189000c0c2070404108403400c0c440311112071003000311445054032944c0441da01c0c09600d015104480c0d6600100f04440417003074039030054010b103104032031610105404401c04c0d1207040d0703135000c055400400d1a804241d08080d00d480354143d404008100005e0440000341604845030010706030071754030042c0ca41070001e490304072001b4148900b44942c2d2820310040c00c04100d83c080410307404691210f94013040e6048180200c608254150f520319046844402161302c03106d1410b4201695095621100000c511040c005000c0c64040d40000d041d035880c101020141100005003184204103040d41c441044c0c551582030f0ae5880d1600303190400e444119031000c03c42c1d40c84403041 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 781589820 1250 781588570 781588631
    0x304030b15090c0f090d0213020a120b040c270b0a0c1203020c031804061a070605010e0609070809070f08010f0f0b01050403140a1a07021507020d03 65
    0x10007030020046510303151880e0050354544400d548034164811035016161403010002c404006030822071910f02d581d020f070f060006000880481c142c080840c00c99200c200300d0000302e41d80404690100c0b070b040c4100c01c6003040c00e0b40c090004542034200200080d0807000c16a5022801003c1003610301e500703041e6040034000c0c1e03903011507a5041181002d8810305e8803180850700064203042c0e01e14401d2190090300d4007800d4690046040105e03032208c00200044003000c00e6000b0396210030025a6025000d10038100d402401a059590380356420401c040d948141c001c5949510743c5030500c103091700c603c10710710360114031751420030515103464000504000c4513512101d45019180c80208581c2010b60004011718056030080000302c8649003410142c0311150403440c0420b0b01400200b0201340e10a4120f09030300c00d01d80940d13030002c2183e41c6a03552070603400030782002e20040200b00101c03a501006070030034040802111507018645428001d542d01c1d20382c0291010103444080030040b88081075800c220a540559 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 781591070 1250 781589820 781589843
    0x3050718021c050405060a060b0f0a0315090204240509040509030c0a05031306030b0a15020a05011107140a2a03050709090c1a0d0c171603050601030e0c0405040203030403 75
    0x2601c2c031001c1d010030366064906001e0000071440d258a01c0c8900000c40741c51181c01410003101e07400c00075507500091416024151a1b81d074800c2d917100c40003010320113401901030043e11181040c009003404190719500b180102c0392243c1c0020301a400c01c0995a403114112400f090760b40c0e5643d80c00b07040d8000c0a170b101088d131144500708001c1080100141903245440042c042c0c0c41b0755140422000e840032082030941207800c40c0340c14028044034000c8034143c2251401200c0d8242042e90303915003125038466110358910340124201040241c1c02c0d400e030109500ca90010f098a14284d16040d0500985d400410b40000340d20003d030045080240c1d4000c015a0040290b0b007540d6999500040604100e89048503903090504c00071034594074428000103528100e0a01d00d041861020000d4001c1c210003030b0510510404800c0c42e918101c251015620404500010340c62688002602070144d441c05040c180c14142450000c802d0003000044a440003a0100d5020132151107500120741103200d075800c00f9040202d00b1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 781592320 1250 781591070 781591117
    0x2100519030605040b0303160b07031b080601031b0f21060e0f090a03050409090302010b0a091a030303190b0d050115081603020117061504080a0213060305071802 71
    0x5038041c1d81103c1064505000340c0e0140c4041507260300c41d4200d443d40ca070300341d0751641002c5403807200742c694420018100060310880ca80642c1c8006805501480d0001d540740003000441d5070725001751752400a40c40d0106c0e03001d048005024001c070b044211b0301801c1046101180d003014003c05864280001a1441000080d4807262001129141100c00e062050745590110b510fa01c00010688151501079070303410b062a0a103e160000b802e2440e205808564030340d08a4034581d0b0741d0706081c10080005c044009024644100320520b50055140714921a40091041019035844a4610403e03081d08002c00250300b05c5801c0020080044100064042d40c6418038441d0811181c1541350f065410071070443d690199140703503402c102845030100a000400c40d4904040c0a0748a108181e00418020141030003007129003410b08541d04254814007540e40509514400c1d030030508030398400c0c0101d40a090048030300b551503181d5140194491104190340b02d50031180c20340d0680c0e064400e811103040300b565600c44903 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 781593570 1250 781592320 781592327
    0x10f020106030c1415040602121b072c0c0d0b011412092b0c050a0b0903031b04050a050105070528020925030c02070f0f060207150c02100519 62
    0x342c1c0c5900070030000c589900d01d11704042c2a103046610590007071040340c0340c048080090b46c124800032840c0002441103081c88080c14003610001c1e0941c0b9650000c1d107900035142c0ca21400c1000d18901c51001001709124000784920100c4040c01c9604102181c18110180104c446000d6122243c42d001c02c00310300c4e040040149075000b400303021907408840700f6821200100b542003a0038a04400380c0c0c4914103c2c80fa2590048070303003010890041064400b6000c240e01c581034001802c0351400c195400c00010003170400f4000700301038002c6000c412014109400c14021a039505158020941449808180e9008114003008192094030b848404468800595201c4100c02544408100d01c107000020014451010b2202e50001900765002c0741441c0410315101600100a41c4200304114001c0c0b2101140d400340e00e0071203900a15030824030f580f6003454100d0003820820241c00035600e1158003d42d80000ca6804500c0c41107840e0100c0e900c4000801952085d64a440b030040c0401d070500203d041c00703908541 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 781594820 1250 781593570 781593599
    0x10b1c060b03180d0c0b060406082b09060c06091e03091503091115040b0c031b060606180a0302130c0801050f130b1305101403030304030509010f020106030c 69
    0x381e48400700580c141031103d650701e0390030740402000007689a061240104080d003070100d0700072501520004103e07844038027060412418903201c0401050088809030701c10080c100c00302d89a0f50a180c404540c42c10220010500e58491001601e0151540b06050a101086002c111f0b5000b102024018041d842e18003d401d444840c412564446c4402802248907400b9003e200b01c516486007640542c0000c0000300300c13096905035441102e400c814040481c6411090009110700e14007080195103412031200010f003218482c41000b6842d402c00014001c07241c07100815541c1581c801f20b60410410354031004241c00020960010390b000d03010b4000300d0905100d0798885240000c555995070490781c1c0f500d00780700020018551090300f240103940d041c02102503d0740f08000205005112000100b07101e08900161001034800e030682e034503481750802602503011160007070031109602030f500714a800c0d02d003d846030046242e560305004c600c420004125200b90701c80400b1f10350220304d69041e9a1a0b5040d0010703101c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 781596070 1250 781594820 781594831
    0x120a0c060f0503060a06031805100204050405130206090d1407120b061f0c02010309081809150a0501030e0c12100c020102040b1e040806010e0601030c0c0209010b1c060b03 75
    0xc000c00310070040309100300c0843e40f0a110290015084920b0020200d0083c00d01c0d52901070b69482498524000078000d0000321170003d8071140160711541802c0c2080f0440f94054002c14054031243c0c64400140c4802090365a90704040750110900c4c0d80a00304201191030080300071080c0e002e0007070046000c02e0407080464916002c2c002030070542c1d031a074080c415a082c1c0444900d40c502480c1e030389141040c2c4140b40103405075106140111340c1051599030846960410240e4100b180c900140c5c50900d418006030740c0381c0c044251941d4420380000c44010918452035802a94109606e41c00c9104842008010100410384064400b41c0303012100b10f14161035001070400380b01d10340d08001000718000e1050080da41512019810b25182c142c01403c01181c9210b0b5160312450618103100005207050180000c0740244000740c1081101e10b0b200000600f1102c1407c00081805004a001009030f101c03a128141502d40c92240356664512034040c40c0c9007403844040c4400001d040000201e01c1c0107200c009103000d40f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 781597320 1250 781596070 781596077
    0x4140603060a0b07240b0a2c190b010c0b0a0f0902060c1b18011e08030a02010905010b0612040b0a020d0e0a11010311030a09020a090c031406091014120a0c06 69
    0x3e0810401020585003d0403401d9400300c0f00510070b02107050025512100c035599580308c012803104941051480070760488100500220140701480301c000300f402403422680c42440e003014070841d1507494000d11072001e0110994240e079603000e501c16910560003103409070740080032036442e505122045550f650054410000350503220252002d28145103188101d44829800171a0240e800e06030410945103454841c054422a40840003035040c100f0300042041021690001c60701c0c280314100542594655540d090141034200401c4403182c0180500c150050303400042e05041d13403503009150002c0c0c020124a40080b614052707a000d400a400101c90001c81e22440a251992049000540458828a5100142002c1000042c41034607140e44810b2680c4c1c401407034070604685800b121f808031080da08080f00420341e40d501c0c600105410150581e440303041164007104601d0100d151481e000d43e0f501c1180c4045040022145150307503840480211030b10000110f0700c4030316442c2030011401c9414403411012 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 781598570 1250 781597320 781597373
    0x14150c030103530c0d031a060f04030309080c01201f06030c05043c050708010801150803181507050102030117071511011e0e1204140603060a0b07 64
    0x40c0410710b05441c90713042100013400c0d40402010041e400b400701010740040001e041e03061545556106400380107515854480306886600398900035010030b005807c40700c1141d004105111080ea031094800c82e60b030031401420040c290142c00154913100c240c2c28144590a00340345444414009076001340102c901510182d4a460b50301c500340012208038030345a041041d050411101c44110054803100310082d005503040304041e0583d40301d41240d405807400340010f0401001004100c8007401945c1100c454146110185858510b54541e80d01c40d09010300e0042c41040090302c12552240c4082c400e001000050350341d01c808500d07015000394402d001d80382051a8220000e4880c01c0009981d105445114540a4009603101c8080d100110850003d101c0c964030342d0f070b07020303404020019003c001d03074000e4202207001c4004405107410032181040712a41d01e042031104001242154030070080c124000d4903a0b55594031084e02088100881e07400104030020300003001d00401843c80d4481032030680c80905800d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 781599820 1250 781598570 781598723
    0x3190f020c0f060d09021512160807082e0902090a061b061a042a170c0307180303050d060b040303050703030b0303090a0314150c030103 60
    0x940300025641e030741d00554240320444d2106880e512100041c3c2c001010704011820b80b403e80746060380114814940c034481e41e400e02140c0b80c40c182c01c0c910404403178180002e851901000c000c0440780020032440020b00120143c0e044191448104001480381c034983c1c26076252581c01e01806540555542030141c40756060008441d0311507001290f200301000c0c020071180d4580d0719804061b0001000c250782c002000a0354002c1c5959620500905100403d02010002c3d01000091002c100c2031040e01c00f8055401d40003c048030320301c0515070b0f0100450304035503240e8035410b07030440d00e44035480c0802821465482c008414190400050040c07010040c0c018171000d9202e046061a5016a12009001c0b40061280d100080d019410208880802034103c07030074808114002540e080c901d82c002d0b43c1102c2d0a5080c45800003081c0300154105800700c8480c5220709143c02200424481440b0241031135101c1175101c0c200034910072016a0840d0000d03c0c4c5481c0150700c24861440c04101100c101c0700d00e2116800d5003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 781601070 1250 781599820 781599829
    0x210703231006020d0c1b05040e0105090c040e0c19121a06010c02100c060f02041d09060f01150201020d0c051b0a0b071202280909060803070f0503190f020c 68
    0x224459455548150805c20380d80e5600014001c40040d0b082403048140100b81038503144074152041c03800c000081380b05d042264400f800c2400d4a4070040c00b0310f05001d00030a07903403400900c0d844443c40541c1e00346103090001c484010510f501c2c0c1c100b5545002ca81072040103000d80118a1001220030400d0302820f5241c91005444102105030000e401004465180c942903000f181c0440300c650051a002c00c100c07404070081422030340143c00c00010f80500d405481602c00740b40300c00c1c40e403004020f4014200e6040a912814450f1014416424030030030340d4500c019442d100f90152240842014424000c55900110240280d00000c402c84c3c0305521804003186841000180550f41d50381160300a4a43e03120b540c0c08540070201d4210030303075026400f080800b48550401004143d09481110700040c0741c2c1c100c0400520000f080d07030111540d541041c0e410f2100d018080115424954403140e8242d4481c803d2a103a820340c042c80346222180401d80145027410350700901c807221740800c1036007a181c01c1c0d4138500800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 781602320 1250 781601070 781601083
    0xa05040303090e10090e0a050d031b0503090606270a0b131e0b0d0f05011d0a050c060901090e0f0609101202150c0703060b04050c21070323100602 64
    0xa280281510713034104480c0044d5803000c1a980c0082c41a101c03840b000d601c0d02490724105144aa00081ea0345e0307141c00c440442e450361281e090314280341003451407c024941e40c2d60b61001a04d52407091983d01c24504610040055130b071903a5000503811030544c5010080030004042415500c0d0288001030070140c803c0300c1c24803414440e405008816100c4c108054122030003003001c0d518a61b00604c8207818039010078580e80c07204a803644507000102d80c0321b040c018904200e00c0e40e0b040041950740446480000140302003100d44405d24213840c80c503210203e01004945115982d808240c00ca00920140889060b0b00101903200f002c0c00e46080c004c7e92904030808800d404030380708011200c080e60454600500d080e1004038072030707485251124240707411140890300340580d41d0702c1111100d566005040071411b00c0d000d496880300c4100007181c1001460b00e0201141d00d0f1000503201201e10900010365540d000f81d00c44111500300e1600d040705044048000c44040c1c90640e01880c0a91290100140251000844 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 781603570 1250 781602320 781602331
    0xb13020903150402060c030409061806050102060712060e0f06090c09030c0105131d1503011b08060310020301080d08150102121c05570904020a05040303090e 69
    0x3003690309420281c00d40b02d8080907004136400001045083c0c900b09080000d080501004100020307482e2078818503581c03017804002851034044c20000200240e0780c010640550007500d40c00c0003412104030303204080041400d608009031700080d100a01c4228920b40400701e1060300d066444c4140368648445402c101e00540d40c460354184d11841034034003070b03501c154080c00400e0340caa540c1c1a42540c80304803128500300c140c000da04420101c1410000b81382d092300c00c80c400840c1c1c1540200122000c0b1016001e00280410340c070014821200c0114019840800122004a440c1c0b0821504d958640214940300c0e0070745401407000601000105207114140d03408501c01c0e001c16001004c02185108565016401c50238204402c807442d80044066a00365000e40c500c02c201c600a186641c2c000300ca540c8506021500c00300c5400940c14001c148511009052850310508000c0c482c010041c11403c61010f07482201c848a0b0040e00114072002c081d50800040c1c4192446a140c9109103916012600b0b10500101e94 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 781604820 1250 781603570 781603573
    0x30c040b120603101109061c02030f1006080411060a0c060510060905040b1810080106060509040e06070c0204021305030709090215070f08180919050108032b02090d05010b13020903 79
    0x402c2c82c0e41f801c0c1700109980c45081e540320700c407200440c06290890304225103031014441002c00308819100c0703999114000d4400790501c015241840d031503198001c01b00c0350400703020b0100000d00c8001c1c83e000d04001313030320954050014090740c5444410f4420100c01481590b01041415401283d2460f1601170255941d00103003000514000810303145030b5240b809801c00003d8802e12002081c0c040c0c0a00401d0040d00040e2190350b5100d15030800e000c01c40307039a1110001250440410700694540c0020414508c0340c0484000d610b0f60050301e0407000001080e80700c1030381071042c4880000c801c02c01c0c0e04010061402201d102c541400e2100b039403c414032800c54010b1003100c210f8209000151220041c05550400940100b5000400c5020400000054a8060200319040c1400c0511410390048601500054005d9400c0036801107010200607443d200103000e554a204401109020039410f03605160001800b0400ba90594100315001b07001c100f9100e4014042860150a039040a001320b0300c410f4400380 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 781606070 1250 781604820 781604827
    0x30e12030f04030e060a0504060f1d0d1506091b08010b0406080a1b200d0507030305090f1e0c01020606060409090201030b10050c0c0901030314030c040b1206031011 72
    0x1601e00410200140103c041c400c204d00e10054646400021703040c503001ea6225943d07641e0428001401079402d40c0041c4041204620a1880303d0134603004a400f5107030140c41d10040303120305c0e161844401110060300208c803854644c001402a4090b085074050000e01d15084207201070910084840c41401d00860022010030801003202611a189066010110707080c0000c2d000c4246074048401d0304540311010004511444050103070308441908480c1903030100c000c107070003840003030050503078051500080c2c1855640c100280d5240320900801401f070706904291800100607090440121030223009907a140c0c4900b81000382c51354000540d09000da00003c002500302494459460080e00c0350344001c07810552940c14419064649810940620000d42c83d09504c800018808500e010340080d1031a06c01c400d02da004101194120360100d6440040300c81c0c4640c2c0307a0301d80b020b046451040364000300080000080c0d40d0103a01604000d14042c200c2181903ca00095041d5041c09690178045030480703440042 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 781607320 1250 781606070 781606081
    0x1c0f0c110d08010e0405190b0f180d111513050f070509010308070204091a01210b040206031f031b0510020705091902072009072a0b0703060501030e1203 67
    0x241000e90710a21490465207d4034000d180f0031051940070700c0c00c4450800f06014030109181500741c8a921500754134252202c00070b050012941c40443c001d00d0404e0110b41c00d8442030505c03040c0200103011420f046445400d00340205000d500c103541c103030706503264060703151501100c0f04041240d8003280d03001000b40c00c0303503400d64560100c00d030312540040360301136580c451040001d4801c041402c4400c03240d90300800c256140c00e210800c21200c10506c0150500d280c06664009043d07120b0b242d404c00d0b01907652589030780d1260304400801c10310c1e00020030b000200c182c0000410025074450207406400c1c1030ba01401c05d0784d401c18407a2810820691401513044010309004a05102070503c0d8030100c2400c8440703c000c040400e07031f400c9070300072a0b054031158050203500e10b010820b100181444181030380d00038074070314100c6c90003083c001d6010400f481250004119140700762000c9840c0300c400b90000c00e102c036075007081200603000301424401e4901290801032b110043c0303140804c1044070701001307444aa06d503170b0705c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 781608570 1250 781607320 781607339
    0x3020615060d0c090501120b0a0b07051f050901150e240604090605040b09190c020a0204111308070602030a03020c030c0f0d03050f1006051c0f0c110d0801 68
    0xc0205400070300900080b04000a6801910410b561a0300ea901c06903081000060104402c510140d0009060140c0154141c4034680890300b1a607062210585419240c80e10340c0c00c01d0300c50180001c8520b02103510610303003010780e0302c1320f03000b007124000800c0b45880d40e80c81c0d5030030320441d446805804207095000450000d00401d025161440e0107000c20080c25402d8006070068015801520541d5501c400500850038144941c03460510100c5180b1003901d0544098405203c460213076020f26600e90a150722001d008102070320300390390b0080c810b103d003074a11541388425400c100c2842c82000702f040030005800b00003049280640e001540076501d003000c0f9800642c040d500440c180c25452104100c50380d800721080c1700500d000c07107600010300040b07110340030014140c0c2c2e00a0912103401e03009400f070182484035085100304030398482c1840782c0c4412411000d100300d48529644044039508250117048681030700c3d4005003420700140c035020305002c02802c080759200038040308a0042503e500042c4400303144c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 781609820 1250 781608570 781608601
    0x10c0201080403121e140c0319020c0a2d050319202103270307020a090507090b09090621030705161502070306020315191e03030206 58
    0x20b04220716130300f980c2da00e560101c400b083c01002104440d01d0328000006030368011400842240400c0d1502402c0580806405210151450846c1d00040304000344010254040c0c90112080100381c41c2d0820b2071341400c44040c089003044008001c0c030b1154044a1031010b1902215680d0054010360810f030034520075944001000009005000c0200203407000342d0301940d15030040394843c0c0060304940000c0c8101d00700c03048101201440300c040901c200133481711804002c4600300016110396000401c2150600d045210309c1c400690070001541012031454400e41005004001035502c80c00025a43d86100744070380079401801354000051008160340f49482d82ca00d01d86007031010303d0044510910300c64145568423045080f54a50422107040500b40d58003061840142031181e8080b4503c240340c07500030b44840c41c90000800b22030780800495111403e40001c5840000c0141c540f0741c03440303200e20410303480b24941d00c40c85843d01031001109940b810803400c45000c48cd0316030010805512020b503905030202 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 781611070 1250 781609820 781609823
    0xc08030705071a1e120906041101032c010902011101090807021311070f110108012616030c050418050a06020d1b170c0c030a1409040203010b03011e05010c02010804 72
    0x404e21444c00308107450544403038158800580c8658403044c41421034842000109401440e40003541000b002c20880b403221621100b00b440c001401c4104480311000d038440003804600064460202d04569060540c401c89056000740c8410f02101040d129940c02d0b20107603070000741002018403a40e401030900c90344061070100108802301d40b001d4091010505030308951010350f400c484003284202032200c016405c8017482000e2a0000b0701d98140500c004a0f00c4c42100b01181020700450039a403091401c0c4010b036002c0c10304800c0c256a4503980e0801c1603091043c0c0c01818404c6140c605002c01e0b407034101552451655008001c0c1c00d00d00b59544402000f500f1041e074000000d40c5032000c03d0525900c00d520401c920b402c0740c5401c5036252004406002d8484000d240303220350340040020341090308000081d5031000406e8a0030004841c02e02c059011140217082129400c6400403002244142c441c2001d14140d400717009582c00b1f040380402c0c0b491445015807052354041b9900380b03041d1002d54800c64080394000e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 781612320 1250 781611070 781611119
    0x13020708070f03090e07080601080f040507030b2a03040f0b102c15011e050d1a12281b030c060f11120a020a050102030903070c0803070507 61
    0x14015240d1800301d0341c40380d1007140040c683c40410300c110119501720f0703a0050800c0c5001c0c51585414030010300a07400c0a03095144907580d610001d41000b0b0200200400b41d0380c8503078103650504143e40c5105480311401c81c030505098540c041d021502012070b0540344516040500e0b100b00c0102a241c802c92110702510660902c0c03154440480d60702928005d4041840019802d620982a1910900342007d0003500742c42c8801c0321005a0402c0d40e90014891540d00307441c5550060340b1284074400d64403407180c0d000b80c418040c10a903c001d500c1e000c40441c0386281c1c9040d80c084002d41e914828003521524120f859100b5002131494010b01001e6240e132103241140300300708496024500b207045003030210a0f82d104882800080005001c41c5d81d01c043c40051b100364509000504501c030201003925032500648585102002040d84507034984200961004a03812000071580c2e130600f401b100d070b100d50002805884200ca02030001415480020480798416001006045010300b40854011014008107412501 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 781613570 1250 781612320 781612327
    0x130b0f150906030c1219060602030304380406050103061b0c060c0c24180b0105090402190608160f020d03151d041502040302030a0809030114041407090b13020708 71
    0x10f801e000d40c1e0b450003440c044a5581c405000440e40341b00f039840903040356045400c04d00a100010310450040074030200d448040740b4241852001d41081c2510b440d84040003611ba41044c401071005950146058a006110a00c80380e001076009038407001e41d0320300c5500010052540840031402c0c0c0d90003003455051505e04104e12500503140d40502da6401919010b0001c40000c294201d420a40b041c82c00442c4460f44001c0044c0403601d503102c01c11014481c150242c4880b4000404550301d155102a0300071581101c940000d84445c802040c14004440c2c541c40b4080c203080c1000780714000c18003031034007840036802071520090584007200a4890030448014426025801040c103070f81c2504601c1003aa4046062805858a03091800034041074140300258140304000174030145c1c40c0802ca6945250304103600036513401e0100b020034014034904c020076011144c0c200c24070040002200200744121010402c03138554075200c141c500101c8850842c06a40120668a003107081900c039006480c0e0741d0300a0312002d08 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 781614820 1250 781613570 781613587
    0xa060b0706020705011d0d0f020105100302040b0a0b031f0b0f09100210051603061d0621071d090f0d0c0c0803030106020703033009020609130b0f150906030c 69
    0x1400f1440c4140c4c1e1b00582c01840740d20341581e40c420403090000c0c038244024806400c01d0500b40e0607a10642c000a409a52030340543c84550b00c41d6980c00c001402c0a0202d2035481ca40000c1c9400d907081c0da241c254200e8141c0f1400041d0110802e020796424244920001e071503c214502089400c180b80d40c043e0003580030391032a5030180d0307030f040c4202131290b010341441440c100c0302044020f003150360a810400c201c6103e24070a4100c999030600f22a4048000e407084540c5075111203442d171000c00700390544070240c400d803100416218103c030b64100c0070803a6042d02c902c26495040716aa224040c0101c859a160720540c0b00220003489a203052228a0107982c803d20f8240c0c41e8002a410369000744c102c0b0000d40e00c8075508000301f50b48400d40242d048100d0f0b01400010500c00c028842c440b06180b5040d000315120484d50041d0756642044603440d082c014500300e0041c802e80e490340b01030004101818400c031860100c2f50380e1030501d81040d1461019251516140406090400803076410140c20300d0b00031130b070074480b900c03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 781616070 1250 781614820 781614851
    0xb0f09150a170a091709010e03060c040905060111030f130509041104020901110703120f020d02030906090a05040203090a0b01080114040b150901080303010906060915030f0216030e04050a060b070602070501 90
    0x2010170490700328444d074580d007180014190056017200b8a020780d12042c10444100d28030070681e03058a00c1068081115104e07a401282d0381d406015406c1214000001d502c0405101e4400506015607041000804290fa030300070071485c080c049030050b29400e9440c030303055980d281940c018440b00605040074a20744c1000c00360310749007803902d410031034840d481801c10081c9036810681c203d58a06aa00c020030707503643c204c0002503c0303000e92540c5038001c2c8004503969801d0ba4400c050300c0083c26001d0000c54070303480c0110b86a41c5d04c035582c2300251840d8160700300200d00c20b41c0600590040c0c941d02d82e1450120307121a80d0ba8440601c00402c2d4620300100c0a00020301a980c103140c040c000c0001c070f8000c50303d0307505081c0b00004856055014801b80402020f0030003000c8000a44112180441d04000903209000002d140180c4030304000d00b00010750100c2501d00709900203480d180302c004262000c0140703503184000b41086038828003c00701c00d08001c0c0000b10000f0542d400918074640701d04000b181e440e110510f202c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 781617320 1250 781616070 781616093
    0x232206120b04140303100e0c1603032004060f0c02040b030610080f03090901260d0201020c07051008220605161206050f190b0f09150a170a09 62
    0x220750312540030040c0300078083c45100d5030142d81e000102940c035509003442180c250905520860700004a080001842c0102c1c0300141c500003048401c00c5000c211080c6001402095a2040c2446e0070110013500e240c442000011340d000c1d282e040d00ca0400c0aa030011054409021000e401c90340306458000718517968806110302d9016a4011001e04a02424442000d00f0081d120303100840603402032200382c003d40d8403071004a04617000c2214804004100414030192003c030005112003a104000c00d46034503a90540c01084809000d806a07601e80e80c0320002c0241100b03449640d600000c0207240485d25601c0da050800710070301c003030a114521402c2c0716038600043e1030027166200281440d0314580c061958101c0074481100c440c2d0392042007014103003800035505040b06400b00c1d0080014465815240140703d01c0c81002d03094070242d4540780d008840307940c01c00d50b1240e120b05000b202d81d40910b82c0085645070581d0003002c0c0075101d0b0224001c0c000001006003074010461001140c427541000c02007481806107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 781618570 1250 781617320 781617323
    0xc010e07060513060804110904060f0e06011a040e0601030e03040e07050703080c1201031401020d050c03161b0204090201140d0b040b061608090103061e23220612 71
    0x906071100c000010842400ea0039a01c0704e024071841c00b0803c4001803c3e80c104401290341210070700070710f454030304111000700350b0840d11030b04440c40c00211080da11400075201c0d0484900b1010804c1d040c9005684003154001c52041e00124810f21001c1041503000703810065110041d40c040780e00b060340d01d1411058111094400c24082000007030395100313255002030240e601401c0036490510740105840f418507800310506c400b6104220641240740038403001e4045480c3d008410105000c40e007050b03100b40d60160b00980c1c2c60b00e40081c1c07100d04040b2441c003500906084000d2144a1040c01d6600c0d000d0201600224034100c1c1001001d050114003981e03150701500754130b00c07001d400040c100b80600a000403141800780c01c5200c2c01c001d01c24001d5440d03030a50540b106039405012503440303415400050780540340d581c00c103c060b005424115281e414481d1000c6080360880040098603c0740c0421090840994689680d0000c01400f103819801d00d9032403600c8a2724071003020010302e155548200400d95540d2000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 781619820 1250 781618570 781618577
    0x1918060e1f050703050c0c060a0b060c0f34120c0b180a060e0d0312090501050117010f150b2208030c0705090606030609070e06030c0a020d0915050c010e0706 69
    0x38883d619034184502540014070503411450200c01038219961180e008040107603464a4004000554560503343ca440c8282003045582c0c0c1c00020000d503071148418644d0100d0380b890340c0902810008002c10342425030702205580f001040c28841107884015000760180c03454440460001003c0c104403004042001c10070344c4807004584640c3c208582c614041e0300a6080255000c00d50a030740c1c0c2d4001d4907007400340d45401c0441c0034284000e1000050b203c5610040c10315480c02c00000390107021401c003d200208010003c00c0914282d900c0c60084448141c03000c0c218514007103052203900302420082442d01f4089240e10000181c031801b09a03803005c1a0851907007604040394040780100c00f0010307034002c0e001c201d60300141c03403801d800460307900e000040c001c9104002050101d210207016050b105101074024054035542d180c030009074800e5034000c3e601640103105808405c1d4005120301c03034441c02da440c40003844014800e20181111302c2e822601120105540e6805007006d607901c104180001880d4944 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 781621070 1250 781619820 781619831
    0xc0f080703030c1112030105010c0303060305061017120a08071112040603060b1c09031103070803041103210c010b030f0f0105070c030f031509090b1918060e1f 70
    0x503002840003044c150849444d034007601408081c080400152030540d04e0070300c0c00000208050800300d020702141ea1014045015000c11700c080c0101c0400140281d81c41c3d0704000075580d020058495071061f4500881d4242c00050102d031088a100d00100c0d6080041850802c80d03003c00300c54054141036001500710101c0900140405c10f107500360040300004c020510865003407441002d081c502d1042d0760311460017603595415403d0101030003041d0130b460b0b0038004000c5a865038400d20344003c1b20750095505903800c842c1c0b4148400c9918000600000f060f0166580099007a4107030300031203064200030710744030155407100013508103910b08202619034800320000500719010003c51107421070310080d00010410200000500200c0c2c0c100d020250951150f140025800c1001c816414101c202c41d0400700f0110b06100070503090010600d9003038042c3c0c0b0500342e20600448684040c404840d4100000c00d040700745015004085145d5034800e00780c0d0304040090700c1035000036200052054481c0016001c02e5540e91 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 781622320 1250 781621070 781621091
    0xc1401091b050a0e090a21090f0b0a0e06090315190e030f0a0e0405070314010b03100e040618050a0b07020c1807200a05010b04020306060a0c0f08070303 67
    0xd10200c101c0c600c80c98000250309042c5400714040d5100350140c0c015000129020070000042005a104e4458001c6136010041d0a103041102112003411200740c001070303035000c003c2905201c0000000031074401c088180e18010700c681c0156050301303190001c1c65101d032050003c00520340741030206208c401d6002d8485c0495103001007080740212081445042614900b40344440413120000440c0c14100903d80c07441d40320125180102d131615070b200650f03a000317030600d42400340c01c07609901300c0c14402503285488000c03607889042043c81da010403a2024034000c2d40403c20805001c0700c1003000d4105005034408070f0074003004005030011140320841100c0c2c0c1e600003146041840030f40d0029507000f140501c060004205250300180c0b4004c60101d4528078401c1c031a01041445018503c20400b00101d401501b0714590700d8003440d03032207506404080c4c1d4603500700346410002d45043d100700c038441d0700c0080ae02c0307003004a241011110400340200442d55031803180208004240a0341c090420507220780d034045484c5009 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 781623570 1250 781622320 781622333
    0xc040c020102090108150f092e060305150a090b03030403080304230f0c0f030138061903020c1005010b091e01020604240608030c0c1215070c140109 65
    0x50013440340081c0b070310351401b40e9510281003107405901114092020b44032034041030410201034921100001c5e02c5030074210700800c114000022904542c40401c00c540d91524450100c0c00d60701030349640803160036801d1058030f01c0d5030302808462601508036400d1a40f203588170040b56100391401c0d244606110318a40c1c04413125228401c42e101e034880900014007603111107943c0d03001c80030b2400384180081411812503440943c81490500d04050007040e00b2020b00300100115010900b83d0704031200303840c6140b00e143c18076000301c914a03108038100100200705034a0403802900300200001c3c1600900710600c480354002d0166074040c11002d0318a50707a8907820020425046610040d5508207031612008140740c1e80c000c24202d81c0b0503000b812a102c400c5840340c011195110b1220702d040040c1ca00500801e2042000016000440c503201c03c0740c805100e481c04010034030782507543d031000d02d40c4490070380740525032030100c00c641000c010b0500780c3c9046019039401c1e00110010382c0340f00d0541c0d0b60f100800e050204 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 781624820 1250 781623570 781623587
    0x6021303050c1525050316020307090b090f0a112206081510090803070305041401170403030c12091b1e030b04050c060403050d080906070f110c040c0201020901 70
    0x4110740403401c402e40800140c0c8075008845001498000800302801e0071301071451041440c0340c1c07102c107486d81e0f00a207503005541d15400c090141d008e48103565022500d04d03920311840c00007000c020f000f6030340e41d0b8820004500c4814010030640450762a07120b034183d4216140d0282a00181d101580d1200320340280f400d48620101d13070301117000c0200000c1031140000f0780707152246540c1401d80d5014802c41000900f0307903200d0780d1540f28003168840000c091090550100140017940e211055280021040c2401142c90000b203647c80115070025002040001c3c0c003c2c2e008144030012800e01e514030030030100714241200d500d14400d0b540500b411171040c0c0c0d400c2040007460041c001070b1314107101000d4401407540c041d0046000080c410a118401b08040c8101006001000d01c0010165662075449240c4151901c20308600c94011504010100310030900205425100740d0660303550403940070850000f02c1e0b81041116000d480c85c012140c2c80101e64546000b6000c0805c41500056640d125240006010070b5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 781626070 1250 781624820 781624843
    0xf030a02010f1a040c0e090126010e0c010c06060b040f080c09090d0c050a0b130b010905040f1713230406050306060910120b040611070215030a06030602130305 70
    0x3d241007042c0d1003181c034520340c07000d42400988000030702e2003003401d007038a1102040715101e51150070180001504001100c88030b4400001c0d400400300d683c10b8041090a0766084890740305540c011402807051544101c0d041441c1034000c0c2d030301181d020b40d03c0c0c43d429001d0740242c0154003021080c54050002000c20801c0300640441510042101c0c44c00301d240d03940798030f0903004d03880402000100300014000d040003150761a541040c0540c1e102e0030451103006c8140e040e0101140c64880d0400005154051803142c103208a4000d104c8030950841070350b50201c4286055400003602000b80b00506035139004080003009040781800c001c040700404000c5100d40400d204401e842182082014403050714041281070b0401001e442c030360429141c00000030a94100e40d008584000895041d00c401e10a03200c035460702585c040c10003008056511041070f03021f807041031400b82d0484810342d034403180500c240c8000d42d40300712542800200592a60340328002e0b039110f126104910304c5046028024084144817032200703074 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 781627320 1250 781626070 781626101
    0x4080a020a1d0406021308060a140c120f1314010c0201060b0403150213030519030917061503100c091404060806010e060402130303081e1b1b0f030a0201 67
    0x111a5030221802c15075000700b0042c046500441c844040303001c041c2105014125840684846141c090f403000d00030300311040b045002c0303d64040890700e400c80040441344590980c180c0c3c020107940d9442c01c03030303004c1c032019044e5965820b00e285108041008103002010a03201d99002081044803800000e080d19015005001e106108020400000307158050040303500700143d002607110140312140394100381156002a21500036510280b02c81490800c0b2600c406d4071a40343e00d10929166034800207003901003100382007070754407103000724035460b180740315050400100800b127803250b079940f00c01d042c1555041790700440460450301040c4858004140001d01c000303020380e01041050300d0700c10170f82c1c2d82d064184035200e8812a907a0101e0101d840b140c040700c1e9a1400d00700c0d11529141c0d240740003842d0940403038440780c0c20902413001c1442c0001001c83d5500074038600089540400c410303a2020f40300d511201111080c0d040a2401000c107240600400f0403001e0030b0805140c84003409c00010f829600c5a02c0501085d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 781628570 1250 781627320 781627349
    0x50c0106051c03180e090a060e0619022a101406090103030c0309030501050f0610090506040902090a1d0106110303012105010f05010906050307090b0a03020d0804030804080a020a 78
    0x85614842c9000382a400d8600f10f9248203011070100a01c2e030386a000343c802d4a1000003003000c2000e0000350903e03880c0c41400d04120b07900071507182c1c68807001e043c1d580c12503c143c490590004200d00f60003070845501d812540c2220050783c9403107614051920721102d04503400280e40300045646a04c2002030440291009540c0703807800e000040c3c00000140002020300c400004150241403103690000050755001008100c54104019000080c000813078802e4843c100000c015150940b194000d102114005003102d4180360900203d0b0340603402402c11103800142400e8001002429080000329100d406210540c0c0c40d411b25a00810720020f01d0304040c5a82d00800041181c0342c00e1030080c003072035034040ca0502c0302030315039141c03050141c040740182c0301d8041d0a180010400e00c50660000003101d0382201141e000b031b66a44020419034041400301c992100c298030003040582402090074042340d104d080c00c07601d480e81300e0b6540315280d0000d4001e1607407139001c600c1120440c03d090f5801d6001e001d0440b0720300d40d07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 781629820 1250 781628570 781628599
    0x1201080d12092310020a020307021c0f081804090f0606120c062a0b0609060a06050d020906071407060e1f0c2d1a09100b01021507050c010605 62
    0x7039800f01c00c8900c4162a112070b0345825103410600c86014050040d0760195524200c002009559402c541070a91051501c485101c8819480f404030100865005681d01c100b050320361181c24040c0c00659462115821004600c501075a903071041298091144481d148000d030035081040485100e82c01000a003100008884049410f10041100316a0300f840c1082c111a00c00300320f21014800041e0401500900e80600810400396800a5101e150f05840c02e0713035941e903903104101d0103080910650004c21000c001130030702d00d40c003a0004c003c0340d0400750046140002590700c1281022070f402c0005542d800203503040c8481540040000d4201c0350844d580c2003109840415860038a1401e0701d01300512200b044604104000c540e044034101802400d01d54000117048240c0083c203110450442d03c407103070ba038240b00d4000810b00c2054001e0030070b4402403681418541d07041008100741d9080d981540724a014200720301201c151094450501552482d44a00250a40b5820340e1040e800aa03c2402841ca00301e8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 781631070 1250 781629820 781629833
    0x7210f0c110a031a0a060b0f0f0d062705072c0a0b03010e06041122030209070309140a03080412111207110907080c07060b060408030909070c02090c0f1201080d1209 72
    0x1c091030a041c005550b00c1027100780c801464451032109081082c00c10a00103860004441418104007640c031003040c3e01e070510a25902140c1003152180301060200058810220154042910850f404480c8003850104507002995107600e03a0700c000d18440000005000c80354101d03036442e401030b500384d805024450300c2e0019512030b401a0240442c40e442c031501900039090800341807500858000d0042c1c034041c00c00c41c100401801900c40280e0b48000e00100c5911192400100011482d0301580e95003008d8899a80700ca4014000d12083c0080162a07280d10102c000c4c180038100d03210000c49220740d6100c01a2a141c44074520f610905d622400b0703450f0070042d2950b0001041d59000181042c5160b9502052425200038a80038070026004200480d000c163340200000900a500e0211145100d80e95100d0041715184142c22000350420619000700303c8219003c000303003400f03c8600c140681040c40a400c6450783c0303e800d0303000b8005a841091154002c9420050411414075010b000340440515500d401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 781632320 1250 781631070 781631077
    0x6091d0f03030126010207120503010f050d0c171c031a010203120a02032e1712040938040c03020f070f080f040303030207210f0c110a031a0a060b 64
    0x104a08203805800c007400341300f941100c0d41946c1c00070403078055000303001d07005005401c00d00038094000c5021001140038509810103020580c0e01140c088001410880300c202c10132170328504180300b44140d02d502c4407a01805052400b03d11020340d0001400303e40e120700d120301003095503007403415500304120030440840049100c5a0000591002598030740703d40c0240b109500c4110840c0081c41c201c1007500040800818900b4110381c1c0440b84240c94410440b082c503203540c42094030505640e000c1000700319180c003a03084a4004070038045400c0307e00038810110003d1007072800c0200303000c0e031071038141001c10324080c425940c284200b4178045080c50101100c0703810510804001604c50142c5000039010841504210743c94419502c00b625203507a52441c2c00f601a40010100300c03010752004070814005008409017121b203003900c0d41e95043da401c5a540c103468110000314145c41105910b04c08070640e48600c1c00301002107110f00200c06185000a40340b07401004040d02035040d8a0500c1010080101c0420a6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 781633570 1250 781632320 781632359
    0x703020a0e0402090a1b081503030c010b040e01020a0c150f050403020d110f070e04081306093605090a05340b07080c0708100f050f1902070606091d0f030301 69
    0x300707ca503215010754a4409440b00c40150b4076101c0025006405c1d0810341203465031220540b01404104c4551018a090b40900b43d01413000038210401040803546074031345030024021800d0002051040c900382c02d01034600031181900540e00032900d0fa4445940009402549051030015248150141c0b03981d94554095110b4a00c14202c0840851f043c00070200c1243c110100590f01d80982c035035102c0010b0072020f200c1c880c05100c030024050030202100070700c0031741c1d00d10701082000c0140408110700d48001090060901c0700ea520403225641e0006030200301002e08080c503150b10300180100101d02c11000e140c0344482003001498154104000f61000c8196601d444d4441c0846854071b21090312075192209079408a8502d101b192258100040c0680c0125117038101e0041c180115914075059902c0c52400340c4002242c5c0000710081001800194060004603115090209643d40e031983d140090b112812080541c410320024a241d10682c100a86400369000801841c2590316105083c0303d1228402c0d803 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 781634820 1250 781633570 781633577
    0x708040c120201120c0c02010908030f040b0d0f092a0e04060c020a050a0b1605090102070611032b06060903050a021003090b090f060a1a10020703020a0e0402090a1b 72
    0x180003045a011310445025030400081c204100440540014184c0e681c00a0503404600c2031200414003503404011500e5010070102c4a61505242400901c520b40c000c4007101501c9542e4262484807040d1802624080c034062015250381c4020789950000001c0100126401c1441c1035004110f03005080b245558409c0c0c0010f00040d126000c00e605a082424100b0014030501840071440c082019900090313008580140700740358144030b00c90043e81d10b80300b54403049000d030b840f88404100851040c546c851213081c1000540c0d080203d412481c1500350544100082803038000880c0c0c4c0c101055a100b5800180043e2426141c1d441c0340d9180c1a0300c03007400302c1020740941d45015440000c20700030341100413150380c802c000908918194201a803502e10319080c14001d8040c407000b207600f618440c02015240c1c20701c0d0300103942e002c410204200d08424012448010740c001d445000000da038424a40e01700519001c607207c1c0ba207141610402801c960004d0603003808a180481d0110030308043c2c94410504000c504 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 781636070 1250 781634820 781634849
    0xa020f13060b0a2a0203060f040201050c0111040302030f0703080409201c060602061e10120302070e0a02130504020a0c06020f070302010b0d05030a12020d1a090708040c 74
    0x10844805002030303421541c4640340000701100c0c2070350300450003140614407000000114001c120081403d80741d02c07602942c11f91040d40403450b040c10014110f0340192050500394640420300c1c000c10300351150b00000c02080500401c0802c01e44c103080c44200b40c4103581da40504206400c0d582c81300c8190056004d40c041d0a0343d40c030f00005401141c620658104211490139988413006004418405040e01c400d4050711070030041c0000741540001405c5000d03202900701d403801e010f44e4050004c003c20006000841c4c04140c580b0004640c900351092000c0c2c24000e501a200741c50a0154502071148080d103549841841001038040110311102446c0544804450140c0e0751400801c3c100e52800c110000074042d6407000031200b04001703180700202000c0b03200c2c1c2c009200c00d0308000e04010441c0c6161783e0280c003e80080140725103080c45540380c90ba0500c0800c0005003040110288101207840f6804c0360080765210700400803c034a0001c00c220790120a034500850030389442c0d0b554a01600c002d00c2901d00280e02c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 781637320 1250 781636070 781636099
    0x280b090a0528020618040f060501140a031d0601170c03070302060901030f050f16030509030706022104080406030f0c0e010f0207030b0c030f060d0b040b06150c070f080a020f 76
    0x1507400c503060360b0024243ca0300c5a00b10017404906410110481d84194a0018a101c04132068003950040303e40584500054040078840d207000c1d640044c00c00e100305a985c003843c01100e07101c50200700c020a00140184600c0d814481480c40551211014020952010750746200700d60b4002020030540341d068540a44036041040140c0240614000c5c080d801801d00041160301c20320340d4a014812a44043c0c070703035007118a95100340c0441d40240c0709110550030402c204000b1480700e80050424546080c2160103054a10400541c115016078044a03043c0000804104c2151700d401070b166203140360360040114032a004000780a0a10701980641070007203035861060304034000d00010009503048046a04c95150454180760958022141411161040030110b0307054108031060901150b4007402c03405103a00c65840c0c0846206005090a85c4195101640302d1940c1d24140948649903141005103074540c100f0054192804503504071103100d0b400388586602591351000103800307101c0e099444081c4150b11 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 781638570 1250 781637320 781637383
    0x5272104080d0e1005130311030a020603160e04110703030504050313030303021b010203041716060c02030307031b021203092104210b01060f02280b090a05 68
    0x60303a01c40031003400303124034803074020740c2140e4000300140c821a001d00c0d11401010050368140520b885038006458030020070b000142015400e41e298440c0241201c40900881d800074510f41c1c8100c80c000c55900340036010820381d6400290a0000c40403c903414440542100381025540c000d0000140c20903803034102240500005204484242c0300400c1c1c000680c42e200e00340900603610100d0b101104c080300300c0001c10b10070010310a0700c0c001c81c1d12480502d083c00d940403180045800251070040c8009241001200083c0644168102d451454000e5a1a49070041d0040d04071a21680500d01c0e00308080c40d0b072403a0700e0f40803c3d503665190806d90500d03225101c2c040c4140c1703800341600e039104820024000030752150109001030022074070502c10f0701c030039803003002404c941d9030301c3d414002032000b00d030400140300341030154200000d820000c1c41183c1840c083c400c403014418250700d40240c2c520706614003500074401c018a115511608040003002154429501c0d9903558014200c0d400d01740f5014038034280309038103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 781639820 1250 781638570 781638577
    0xd0513210c1b05043806091002030c060106090314010b0f0409030e0d14120c03040b2514100e0303011406040e0a0b0f010c030c110a030c09052721 64
    0x207000d401004a100300d03000c85007802ea0b207503074540803011054520b12105454510481d8085ca8094031030b504199011042c4004402070700092425800b09001c0580403100030440d4900a0200e5965801710306d10f142000c40480d0144185019180d0600c000f4103900d4545002d0707110320741001c0e6070000c0c100e0084e0a0460711590444a429403242140d5115418000051071a050f02c01d140c0c0240d902000c0041100c21040c8a000030004240d0802d020810000c4a110003801c05004481c0c0440c0b105452301e00003030154480090308031104401c11400c1402d508041141007a2100c0c624020400f600c001310200c4e80d2400144528000ca4031500b0174400303541c64003015179009050a2f0007035122400c5c4a1400f10141900c0d002c3c3c1c134040c00b62007a40c090198490701100400c5505500c820540c0314041d1548200d03403c0313880c038107604039012000010010f2041e02c1408000c2099140018041c103100040c00e6403520640c91089480c8040d100310343e0801d50100701314403590400d2115460380c4481d441007290500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 781641070 1250 781639820 781639829
    0xd080a0c21082d090d0908070602070603090809031006031511030f060d02031005010e1b0304140f0f03030603010f0501050915011b12020d0518090c0d0513210c1b 71
    0x80b0000d01c80b07139490000c0c451144075025185d581146484210059031508184111130045e480792104101c11030280c0e10094455010b80b5080c1d1034586a000480d103803d85080c0e00d4640c0d995107070801c105124585034903048107004080180304004003002018220302010f0003910800c0300c01e42c00319441c2d03500c43c00c0d2451031b2640541a90814410714400000620092142c02072010741c00340010111a03a0000640c03800c1b400c00035013030440e00d81e0384680481404108100407180302c3c51250800200e010840c41c2e10301170103580103550303c1ca00305091500b995009100f035401d00e0305000051005030b40742142c0c00c4c0e0154001c008013204035141d2004031030180c0d0b25980c0f030b0300700c4490048060500809a403520f4501c20f060f002c2324000c900303c00c4216610b01c5040301d03c41c140001903080c0c1c855031511003490b58020000180035810701031615a80c10884200307813084c5c8250403c2146203070130480066000c462402c60060b10040c070454030342010f40a60760b4000000c0090801e8010039030301200b00c26000700580b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 781642320 1250 781641070 781641151
    0x90b030c0a0e04180f060c0206070f0f030e0601080709110301050a06080406020702130504060b1f0c210206100b0705030307140706050c0301081204230d080a0c2108 72
    0x29606003403145c000e54030b01e801900c8541c1450402c1040e01c0c00040e4289c0108803564441c8400c0c050399004952a20324080400101500e420710008010303030070820680a8502a40a48000780c44c00c0c010b441191102104103041110070310041096940342c844000444800d420540c0c80741d1745902c1d2100003071094850080d800404007031140315500c2c59a120901c150303c00d80c4104940d41c80c0340b0800c01803e0500c40c1504140e401d840140084510940800b21202d10407030f20202c925250816400f07a00d1410765088005900000c00c203c002161510072500609000c1081c614107201d0b40c80345074403840001d01c0f50090201c2c905d000c0404210717501c01c41b100103070085410040e40c20401c040c014254020f110710980340c0f2441ca4092100c020b108129400c4a1512048000041c141181c2e00b0300c0001403003020707030b2207c0d00304c408201150f02a00142083c4c01180d990511080003840c29030030006800d503003500c0c00b070f1000101c200e003160005c00b010780052090400241010142c240f141340050200b0010000c0c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 781643570 1250 781642320 781642361
    0x370c08030c0705090105091504020904021b0303061c08041a0c15070e0a14090a090213202a07080a0303140c090102100b06040509041101090b030c0a0e04 67
    0x264007002c200b02c000e88000311504c0050342da039902082464241507500c2c41c2200101000240b052809138000c0407104d5002c2e2000d07007061902c2404072410b034100035100030b03240c2001040101e2403034041030300d91a4580c50114150920034907165180c0c11f0082c1e014501c0c040d400d07582064050103424040c0d443e903129510448680505c444040d0b004408180c5411010401e0383d2556042c0c1d1a00013240e005407092440054185045035040056014026080c02002941c80e4000c5000d6229000325440e0703064031103804280914621280500000214100c4240240601000208411100085012400700c1030604104450901c2c0c0501b410125880b17040c0c588548140d603001c05070107410200c041020005c48880c02e5a0721882c4a850f48100e11103603005070444a00180c00800070b81c04a0301c6800c0c00f0740030301c0c02d00303071107001084c600070b003d440030b40c4d541c2d0524401c0c918540c0c2c4001c124020700945100b10741141050b101c040f034140140381d42d600c28002962550400d50f215540070494495484075074407003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 781644820 1250 781643570 781643587
    0x9041709031e1b0406050f090a110f0304120e30010203150a1e0315021306050322020a062d0e03150405100506130f050603370c0803 58
    0x1500d41c0034000d4240e500c1d4120260310020b02d004e11640e401c4890103031140c40507c00328010045808001080091040d656201d851034a00c500304c040c200180c0307552a00ea40c1e9040c00e04000c030f820121444000c08000d0880324404680d143c1c00245801948511240c8803502030401039400c000b100991134450a46c404010820042030200544041200c15614a01000e40380c1c1da11a0982500e41c80da00c4601c8140042080080c1c2ca94071030000013210440c0c01070515034004000340041c2038942c0031b0030000e4404024418103108544408100c880885036000c1c00000e82d501103400041c5074410301c42031040d040112130140452403100005000443d8004840318041c440142140341c4c040402c9010f480303120101d00f407100203604a0743c0125040700c01801c41c1600e030b0601c280a0000101503580040000c0b803008480c91950003030150903004035a020440346403101c2072525040c64182030b03001c402d4484040400d800d180c220742c075403000c12242d41d0900d080481e04003203400168a511486461100040381039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 781646070 1250 781644820 781644823
    0x807120306090c020a02180718140414090a0b070e09160212070c0e04020d0203010f0f1b0e04020307030e0d02060a050f0f070c03020708070605031509041709031e 71
    0x900b0703140c1c0714904028810b00d180080b680c80002d45d80080d0041503000740900592084840316501400600d0070146080340c0000d41c0342d03400060303400300081300070552203030385180341c103015404036082242280034607403074002c9e50ba6581d65840000a8031251540000c2060306200303404448845101078940611804c01008080c90f400074600764400501840b903170b0035900031604007110b40103500800c80804043c14203080c201c413208003800c00c0380e1091843e0683c000503242030003050481c4d640300030000780c0301d241484004180e03810640d84c01c400c8207401071500c09050700000721160f148402d580041e143d5079040000e400400e90840500440d20618000030040e0343d001070f040344030301c0715480c0500c029181c0c0900c003a4000020f41d03c08602c0c080000000304294410500008005d0003032040301d40b0303260f5035545581810400d03000280000c00000800c4403004c10070903032450788101a10440011315040e114034100704004110fa04a9400000f180b038190f940c10040220706004615608900e035010b5652507 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 781647320 1250 781646070 781646081
    0xb04020f030402100203130905130204050405460c12080a030b180408090d0c06030c110610030b1003080d0b03010c090f120302030f03151302090114030408071203 71
    0x1c9104007608000b0b50742e42c4c1d00c080180e845410300b44080300e60050030066900e010f0b02e001800c00000048d403105200141c2e440d401001e0040e4094005404101e00e03150740f0301c00e21140e503c82d210728500160740f40064000c4200c200304144040408664504043d0f180c1b514007a84151710403c00180300a0406d030030710403640001c01da041c8440e10104890111b20081c0014948a401c0840f400c0c0b500300005008140a04000d004103940101070700d014507401e5841c01d8403075205800c8180040ea86082c12020544c100b03120b00d000350000801020540b402800c2c242500d1064000200505802c0012034101d8000b0303030096010b184d0200d09540c490022003202c4005003212a0100d100790300b000310100303070303a406586d0b140281d6a003070800f40c000604001d403505001c0f0b00c00702d08404600c801c10280380d100700000040c50069460707900d1036035031100c5001089903001200b409880180c0c070400124200c0d030f03000311680701c080c504c54607100d0300d90341c482c1800784140c00f0b80240681984c5800314106801d43d071580c0003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 781648570 1250 781647320 781647323
    0x1f0c1e050a080a1104181401030c171b2b0b190504030905040e1011040302030d050301062a02030115240212090a0803120f0115021f0b04020f0304 64
    0x44030141c0c0d903402c90f1407059601c0b1100154801c2d8040005110603031045c1581c4540413120580801e07040c181c1812100b03081d100742c0c400c1d29100c00208042c03080340d1a10804161042281000381101d0030600340051000300446902440342e12080b004540711060541d041c1043c0c45c09440e00604c0c0c401074240070310401700c02c80300800407002058050310410101d104150065416a4441080d5401e14090000030580e507003a500e442c1c03061034882806c0625038096001e04135100f2000036141d516501c14146400150840c0d0014010240014405168041071888150104034448450308410359400040d5851070070001e5015401e2090070060a03c148000800301c1d9200c820000e80501403840c40488042c0098104005030001140d03241c601c030703104000d041030302c0380180001c4800f0369a0650750b24551044200c002c00341c43c0d09007008084034146017240c0c0180300640208000000300300340251609113401d0241030402400f0043d203040c41066001c40c031034560240c42155240281e030001c17141500220790 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 781649820 1250 781648570 781648577
    0x1a090c040602072709020f060705070317030915060114120411090112030e04060f1508071707051e0d060305061b0702060c0a06020a090302040b01021f0c1e050a 70
    0x40000b401540740e000300043c4c0304450111601070500c84011030140080d10070a030313400041000d4140403640e500b40205030f024407410040c000140b452038524010003482c1049802040c051003005000a0040b035400d4801002c40604000d650f601001a2030080301d400d0400c820204c0841c04149003030340d462805001d41c0c001c058800e0f248540c0d004006c5c00c250700740204201c0c280306940000000e80908051441000003c0010440ca6200d000946e291084c1d03611030070064154864402c00c99410500054101e14a0f241c00b80f000850000c0d100d48103080038042c6010000000b9030401ca82445209500743c0104c11100b0741d5543e84d850f4081d401811080c00305450074001c010118851100d044030000713041a484020301c1c10b102d010f03020000701d500002c81003800360207031103050f0700000c510b4030041101c080e8a032680d0440340e041d801031104450780e81558506541c05a95602d0140030100c04c400c9000001810200705880b0032a0126040754203044800070300306100e0717003245030030340c0000151410311800d55 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 781651070 1250 781649820 781649833
    0x50a0c06020d1a10121e180c0e07090608221412030112060b06071b03110f030c1c050f0d230901031109190f061701091a090c040602 58
    0x400700046007130400008008200e0051341118091204d4112905100d614000d60308002c180b000d03075105480040e210b444811005022003c10401c034051500080c00454170000b582c1d18001401408844180c09080140041840001c020994501c0301c081001400e00f40035000c0541803800c01943c9032001ca070510030740078404900c0b000030321560640c0d040301e9858988410a488540351319004040d00402607170400c2041111402090b540910707150b41450704e0b1110000f0f14a54142403800040409504d4419401e485200f80d4907500080c8030b0040070001c580c2994048800d84802501002200004215008080601320f103443e0100b01c1503030980054071203400c82e02c0715001e203410900c0d140d44207100e502c001b4032400314030354800da100f03255044528038400c9c5800c44120006100c080340b14400d402c0850503d60901c0501d00c203521150003018641400c14404108496480b81401d050003400707041c0b551440010303103500040e521400c107140c01274226007007400d00d100d00030f400781d1150040380094850344 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 781652320 1250 781651070 781651121
    0x1d0105100512010b13081c020d030b0f3102030a1508030a111515010210060f0306090204020409050c03160509090103081b0f01020408240106050a0c06020d 68
    0x41c0e046034071554100d5440700080e82030610302c40c0a500500c030000e0020300c149501180b903100030451003c05441c1e5904800c200314014030000d02c1d0140082240c800c15045c0780e00d00b0540c0d194000f801e0100601280d01c81600721003400010700c0e52221062000040150380752080005140b0345c0210b008103100c0c0f80c1400740070004614070340c02c44203501c2070700010360041000426481c818540c5108580302c1c103090701d40c00820002243c810440950304503140314a1516410f00303e680400200e5841c040342601407085030300e42000480d200d0254400540070584840b10f0300110344d165811034001c2c0a81c040d082059084c001e2850b050741d0400c49982d010b08030001175800c2d40030300403000d41d001c0c490010444896682541c0d503501040c1c0010402c08008541d0181141c8074030000e029a400f41881107000586482c81c0492031407800420709131a00b400c0b15100081d41d242c00d00d50008905440250800c5652541c0d004030446c0e2050856030094691440440c21420242c100d030002101e0441940d075080580529 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 781653570 1250 781652320 781652327
    0x200a08030f0702130b041509050a0b0102030a1409030706030b121903030b030a020306040b100506071203050709090603050607090803030f0a05130b09030a18030807020d0206041d010510 81
    0x1414021030308260306000b0400146858841e22002544200b13011410600090208080da0300880309403098485840082c40710504034807e050313004d81c0c0744074141b0a4144a4001039100d21038a03000c4c00c01c106a40c20a0701d00302e0350502c112408a030000d4112aa125a14100100140380c03041d0b065203c1c0d8804111104980030016050504c1c000080300300003010440c0c1e60a500510306030544903003502400c0b110f10056513050080d144107030b0080303030710010310701e4054011b41303d80416070820f030b00c110010700c05074001c0340d0340001080c0744403c0d03400c00182541700c2c1e80083d21500717101e41c07009415508015002c810400040390300c0340500c2440e21400b502a032034071441c50b141c0c0011980c0a000e145078100040189040781c000f5034103c00c003104410100900e1f61240301e402c0300c040b00c460300180d10008440440710703400841d040080c1c12203500754148070305565914405c0e1180c08006842084403250440a6581e080b086500401c03442503d020041048039030120b009a01f445010f2040d94484140800d0501 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 781654676 1106 781653570 781653577
    0x1021207020610030c0b130803040b3f04080c150105090603070506070b07031d061509130602070f1406161e0e01020a200a0803 56
    0x601600103842c2081c0540310a05007200107408002050080c00c0d400195000b02003205e94135401402105056080c0d41c2001d52030b8007002400046420070407004007a101d07816180340020040809400b03100301c0603250804012444106044044101c2c18166a441841445241d0070000d41014441c60704540d000c3c00116410098014801490881e50701030380b000b41217009055181c244804a0054010804002c05c4880c0000200d03040328025044003664111008150007400c03141c06000b88e03500743c10b072100110503142d408410750904006100902c15110701c291034512003403507611400294010b0100b55034418844918034005040340c01d42c5411604840000d1132507052050303d20a00842450b541c0c03080c00111040301010b4401118069800b1507142810800100c0c2d5000603420040c011700000c00540c14108225801d1070350f42068146c500f802c2c0c64022019440d4508203a9921 = true := by decide +kernel

theorem cover : BRFrame.Cov 781474820 781654676 := by
  have h0 := BRFrame.cov_init 781474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 781474820 ≤ n) (h2 : n < 781654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
