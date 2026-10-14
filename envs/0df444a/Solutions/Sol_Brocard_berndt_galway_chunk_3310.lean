-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3310
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:17:21.905011+00:00
-- url     : https://prove2.me/submissions/661dc73e-df29-4c2c-b2f7-8d171bd01c6c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 595143884 ≤ n < 595323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 595145134 1250 595143884 595143889
    0x70f020616030209090723030114010f0e0d061a010207061d0604030f0506091015050108040c12120206150609010302030604090501060603061d150d060905030f04150c021e 75
    0x46a2004c4c05e402043c16814000d8144d08858584c03005400c1c0d10303842c101c240e2512040803143c0024803405100485a10f00000903500603440707881c3c10700191800f5050b05501002041000c03481c40307012104260340d98403040d070810010324441c0b0120000d2020704081c0d854460700030040704607040007040281c12543c01320f00507070312441140d0045520844a4040e6411400c1041d12030303134100c90405803400f412041109205040c8a80d40c4031906285030038620f6800d01004507030a110040c0205d901500741d035004038441d0f515030007c0d41124454150707402d0003424800000d0030580b01030007090400d207503588011003c0da43c190544481100a2900607201e944060009018001e81c03000074000754607010001c100300b82e00d5004502910800700c1420001121018945000c00088903003103031820740d0400c1481c061038807001d504c0407117005e45400300d020340b4075449503800d507030000e00d202003100030001d010040b90320306201d03464000603241402142326281d80c01042445c00c40044410b4046404861903c459 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 595146384 1250 595145134 595145137
    0x7030e330c060a1407090b190c0609050102071a0603060f06030a0f050705030c0114031b07080a030504020112020c10020c010603170304032a0b0a06080d08060405070f0206160302 78
    0x40a8032000c82e00b40b4100740340c8a00042c002201d00600241c0c0f41000581800d0003007014400310b44500c09420700d40007031480c0d02c1070102e4501203244100401c3c03e1006001c0340303082c040c80a00c103018030001070b59076110345013610407841d05864603002c4001030800c01005a90104189500006100d0300c44141e84c1d0340d10002c0e003003500da40c00040030900501030880510074005034000030381e2015000c40e66440d440f0740041d2000c0380c1d006004d01d1510800c10000d0019442a0703c002c07400742c031510788141004802d80d175140d080e0b003100d81160b001a9880303080005560b44003035280f100e0450094110301d0b026020301605c0e12808105400300318107800080704150b10009510950096400600c1d00a001000080d0750400d94020781e820740001e02c2040f02003040003240390030801081c40c052249209080c035982c404c41c000400410b00d0300455595400003e890b0703020b200c1c420300d1034419540c04401d07103080c00400c4121803000e09910b00300080d844032031034007a400090f05a08034440707141039075806000e684105d020b07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 595147634 1250 595146384 595146397
    0x30219020f0324062209020402120414060f0403080f061207060509031002090607060f0b04050106030209040e030309070b031305010e0a062003070e150f07030e33 71
    0x1407054500250b0420200f0344105802d030340619994000c0e0312280c0070400121038016401011584106006a122480340d01041095202800250401401c601e0004566a04036000ea85420011889070301c0024280041d59201c441d04115605a00b803503200286030380c200801d0003082c07403d81d01c042041503070382c09045002d682e10710f8215420306458040040950f040300e600180a886501550003000040d80285c3e00e41c21005420b06040101c01e0700d03150050003c48c620310007141ea070b60315189655101c6008980c080c0c4102d8030301507a184c99804c00d00c01140c0c40880306402d00d80082c0188095000d0104a0204031480c015180741c4a460b9032081040c0641000002402c2c0e618041603070440d2071010030510f1041c0d000e801c00704882d41c15402220041c0c20000401070441800304000340750309004c1c032448509200d000d01001010b00c0128019106035102c0c6001d11401e400c0460424101036202c66803072140d550544000c0d482c2412030903e025004001503000406409101004e84170079602d0301a203c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 595148884 1250 595147634 595147639
    0x3060f0303160209101d0a02070203030a031a040902060405012f061f1805132012010e070b0c150f060a1d060f0307120c05030613030219020f 62
    0x9a80322542c0041c00e0040590340224041c10403000058410420080c0340c90803100190314400099190b00440880008000e2015050a600384000005a03c08101a064200c0c65132000074000f444520003031280802e4a90840c41b030381c00c0c042100c0058903901306039402c40d0380030f0a00c4607100041d01602c0d4481c0e454192000700261880e10480503241001401d1703070241c07926030035500107800d4002e8484c108100901a00001e8020140313030030340745e0b41a640a283d00090042d141c09038001c003540c2c3c404299604444040d2107072807100a0300101d181c01d8012a112200e00c078020403400d520240646c1d100c44071031044841000300400e10710001034041c413498084004503070000000385400f0b0869684800c0548906008103507201e00894000803c9070940039442c441041c1e80096038800040113100000302c46201c0e010301420f9000204d0f41c1d01000841940c610400716643d10b241070000f41442c2c698010802c144801e198201403003c6500407070800c107500d0601d4035064500c2224000b1880c401c00c0501002e4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 595150134 1250 595148884 595148887
    0x80304051516020601050d02062a0615031b0d0b0f01031203090506040210050c100603050f1f051b040608040c0504110a050c01180f05010e01060b040b03060f0303 71
    0x20060045560606050105903007078441c1c88a4691045000d1007030542c03005a44450014030040c80c010185180040c8000c00c0c00345012040c21407074480204103041d19514456440c51001c1021090045070703440244056141c2c1c138041d40000185d82c40c00c0c84d00c59280000442c9003c245140c840c4682018403076005040081d00341040640082060001d110a03504403040100341e00420740319005040c055038101c3d0041c001519541c00b00000c0850010306041400003c010190301d011040c45041e02c154000600005c2843c5103080c84c40c00c040780c0e080441c400d600100c03041158000706961050001e03c0c0c907240080c0341c4d03850301d104a01000282c913421170222000300d000592154010901c600c42c0344100c0d001c918044e5500c003804190340c980c106103050846c09020103550305100d0b030058200c826200d000031406000d540c0e4214101045c003070041c0c0e481c0032042242d80912100340250104610820000c1000030b03e0b00d050703d41140514024401c02040c00000b00780c05e50f5840010004500008040c1c0c0d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 595151384 1250 595150134 595150141
    0x90102210415110601050406231801090605090604020307081611010f2f03012705070e030d0f02030d1109041e0b030a0203030a080702150106021f05061503130803 71
    0x180403000c3c0d02e110701c50144140000894141401e00490040f1851021526085071980142403403900304000034580040740743c184c1c02400148801003d0007840701c0c850020f48170342403200b4080c440d0001840705000d079004100b0301c03140d9540a082640c0c040b500e07820b51070790b40814500403246084180155400f030740c02c0c1122062040781e1944082c1040101c2040842c8140140c0d108040c4032041030007403a5908028001003000280c0306d1003001904c0ca11600030381c0039001540040080321026100500000c000d003455401504041094400b504003a0130004400380582000964070301c502001181c0a5071a540c180c400c0041030783c26100102e10041081c46140e62802003031800f420b41c88a516000f034100b1003445001c0c2008901408000e8024001e10b2a02c40400b070180c1d003ea00240c41001103104002c2425145142c0380000c0e4003030700a03079000d001040750701040801c00903484015840001d15120921810750758400400385c84400d40e40115449590b020958030140a43c044003074601e28001041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 595152634 1250 595151384 595151387
    0x10b103006090b1c03051305030109080316090e010302100302070b0a0b01090906051305060f1002010510150503060132071a04082205100206070311090102210415 71
    0x9400b039410501007000301e02c2000c010864034804215808000c401d0300345580d400b0078840c000900100c0b02c01c81a090b551550340e00421b00710351080b0401d8450740d50206c14050a009240b2500ba5207042600c2d009034164149410840c0c008010b1000922482841c9000c0e6443c0780a501500d07010350700320031074a03400d140041c81700707014280f84240741c3c0c001139400fa0003080004092150000b2340d10301501075903034406101c001400030100508040c0e80050b20704135404055a5101074584801c8160b400400c82d81041c41841b000c644494000c04800d001d01001a2482d1354008280c0e90b20007024030b01000104148003c0e540303405a401031603402600c010b0006a01c4600d130400a000780c038850501c2c2d403031030300b01441d003003500724016140103000f000e0030040080041c1c403014003803018a4904103408111580c400000d20b84040c00003c002c050b800440411541036094840c003140c0e131208034600c42c0b810b03950200003521080350a102c0440381c0fa229035410710203004407054070041d00c03426500704010288900f0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 595153884 1250 595152634 595152641
    0x70515041127010b0a020c01030504060b12030a080105030c1c1103061e0912160302010605040c0e040b010305161d06040305070e1b041a16060608010b03010b1030 71
    0x2001e038410b8481c0000060440307840340c222964085207502816031440f0304401100a800c0180051741c0131511828400c00c0d0b0380c0c40c2d100c0403051480c240c00459843c80302c2c5801814079907050380644e2282e0041a40c140036920740d11103e5030211340800d9400300030f0004e89844203810040d1070b1240d402d44514070030003010011f281080301c800c80c00446a00f480742e44c0c0c004010b590314078003000c541c507804062110b00e01c0d8002099500f109103100e03000104030300d41c071880400c0c100c4c0e00c804902400902a0340e5580c849041c50301c00c500c18500700f0718050100b0f01c0d101c001c00d44a084280041400c110742e0001842c08200040c04040c01010000c14403a5600da81c0d0408035501d070440c2c05500801c20041011803004009410740c01d11921080c849103042902d880d8200c41070710b603894450210b81004000703820001018a100306900c1e4440d60001640307509040c0340741d084404050b0340e24026031414119024503074031450420480030341481d0940c40f6401040404a400380c0300c01d6840300440c100d076101e00b4811025003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 595155134 1250 595153884 595153939
    0x4021807021e0304030c03030f090801050a0623030c0f060909180d0801120b07030b090a1e09020a051e090412140301180c140409150b0705150411 64
    0xa51082c40d980380503203450340b01d240700040c1001d035260b40030000280564400c81100c0e8490411940a542d1552040d0a4400403a504055035640d0682403101c0e040d5000d05008844e90044804904501100820394a541106440d4130501a5207041815a510340c0c040301c1f040100500401d04071b050070100c00c1c2080d41a4a50f510403400f416002c1d0341118441c0008904880d0108011003907070000da120107502031800360881041586404c0c101c02543c45d092500c40c01151509c600085502101031112000558400042c1050b404c0850080140c1c2d581110403090b04c404456070242c4007103c0c0e01c600114501a0992604428044c003084148485014a200040d4143d200c025221401c0c010810051209010f00668204180301c6195030844a82c081c04001040d810101d01c180100c02d48003000b5042035100803441519841040245064411500010150b8940d96070400881c0e641c0e0036220400112101c004410102c0007070709100981c20556a5040050701210725212040960414581c255 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 595156384 1250 595155134 595155163
    0x6170405010608030a0801030b130c0b0706150e0a060b0f090112060e0c07050607080105011b0201020f0f161a09060c16030605010503011404150c020c19060f0f02060705030402180702 80
    0x403000030700032480718405426040d40711000c42f10301803c1c40100c0105400404060315429950160f403890b88d001c00c4400c44c00360000904440b0103140514580007030740e20503040a4090203040c031680e40702e51101e0040d0742c0c4012090800c1400d161000b07081e90002d01d100d80c000324900d4090414044800100b0300280203460040003510310f00d5940407015141403c0a202e41400140c0800c24103090300b0340c1001c11003210307105105450002d481340c0b10145c5030094003010503031990452003540c2c3c4c0441000407410000c083c8c81500055404842d0541d102c540136410002d8041c010014050020f841c0512160042c540000e6031441d410b5102c2c02e12000610017409814003c0d07182c0fa00000c8012414060301e445103501c4941036008001c0021303000c02410598480d6419440340c0d001c1401d4a55808500d40213138481c42400d48415441d00710020030702064103079000107008889080107019a8042001c50380107845090050741d0307445610100d00100002c003801030740b5480c0038040c0204030354080b4011920f21400c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 595157634 1250 595156384 595156403
    0x30506011217040b0306011205070906050d02070210020d02010c02120703031104170c04050609040b04020609181303090609060518120a06050a0f0e28020d0f0b0a0606170405010608030a080103 84
    0x1da115003007149c009544800100c0c52004080010910440007082c1420841c4005400d00080303034045188251840440b00160b0480042050401c0e824030868549880e1031004000a03041005021707101d01c544035015080646404038000701c0103991040b54028089600361003064a42001d075251241071542d403030351080d03050002040d02032404200c03045c01103400491011145d03c0716400c2000c2a0702007002140c021990b6000b440d0102c010f20f0b1014801e010044e40940d1403100c030305c0d00806000040c0c0101e005e0081c03c84007800702e1944041030342c400c01803c0310941c40030000f00340000d1880000708620482c1c1e20a4180c400f04006854202c180900c540c80828030003044080f2258003030b51310001c500e0403550700032408035243c0d143c0e41e08180758204200c0300340b80f840711030340d000700d1012591a42d0589890301442000c108001ca401c4400e60300095040d0b0401102d401e0020060150350781010720007544040318081001e01000b94008401441000100c2ea03448940c510007404581c0c0074401a50921003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 595158884 1250 595157634 595157657
    0x60106020c150f0a031505060406030b1504080a0b221407060f020d0e1804240203060f12070b0c0d0207080a02030c090406060b0301121407030506011217040b030601 72
    0x4515041d1460600042d03119130074000340c0f020440050500c495104107942e003510700010140c42d800c0c01040644503030354001c14582c2e070350320900a40101443c20807104c4401000b0401c844100400c5801c5090360003100352205448078008807461480200c0c0490260324508004020051500300c8c080304052800c05490801c0d594000940c6c089a43d500c804001d40c22a141e0707101070328861955140500001040030103500900c1c001c9081030002190200e440c0c0c0e02450900c0312100c006e00681710046c01448003035143d4230300034001c5208484201c40250184d1040c8900ccc0002403c240400e101521035100e03056203401400c58a10380c2c4550f48241c90000d400b4905021070a64070100f10108045e030082e0040c1000e00c1a041401401c00e030007030041d1481a40c07000007180034403090000b14000c0140b107a00c4103602c126420400300007810035152807150741c4280c030b0401c0040e201155950450701c3d0301c0400c080c070714203606180280035814400940440b50000740030032100250400355000d45820381e00e90b90b0612 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 595160134 1250 595158884 595158919
    0x50d1d092d0906010b07031b05011e02070201140904091b29070b060a09020a08060901051909021c060e010303020c0a1a030403120f0617071a0a050408060106020c 71
    0x103a0b40c0400c50380214005102000f00130000b041c4903442450448191490880b0494641024038001c44142e510b5220903d00c4021988960368449166201140740118a038006005421000d0004800f40400314401c42255116486030300f10700c0d0040c40207c12448a283c0850407912180103091103000145004280d80e441202c0c0a024505060403403403030201349880d88100440000c0210341d00c04008080494910881d00251130002c81b15210b0b141c05e4203195040200d81c40b0140c0140e8045c0d0024486010704030a500612001c980c02d4105c01130f42daa9102d03c070880c150350f521550242190910400182031700c00c85240e107040300e01075820390314120141d104201d4520303c50300c10214030038000305944400041c0e00c0003d582140c42800c140c203203d0030050701502034070900000014003940c0d44108000302070907100030065000068001d04511b600384440c448125203044c4d0318010301c0c10f020500310946401503003190040c1107482c0407228291783d0b554000395980d81c20403a460299015401c0c42d076005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 595161384 1250 595160134 595160221
    0xc03090b1219060e0402060919080a030e0409050c10020321010f0b07200f04050a140702010b011d0d02030304170c06090d020121022208060103050d1d09 67
    0x1100c0c840f034030b02d6085d1281d40801070300360400321440e540421641d035441d43c03511143c1801c0b8020f000c1c01c40501303030140480c24060484583d141d03002d8010f81c00d184e02030700010004250002100d5040700e0003000001d4442c01240340d0b010345010b80101c10079403c00c0228030b00586030b5041c12541c4e00715013115400c3e211341580e9558017410310010150b0a114101042c000462411883c81c2d480c0500030714003d01d07841c0001004d0380c206071740102d034031551854880180c2c1030074482c0c00d40c0b100c810b000030f00c0400e1038040001d0490928000c0c03070420140c8111300c00c00654803c14600c0c80d05400808683d29107445904045c4c0010041c40c110b030b46031080080321000c034209181651503100c7c005081070658100d13500113648a90204200c81400591107001c110102c107a407001d487c2c2c007807248450810050848820218140150f00709416541c0b21400400000f42c00044501a070005c0349030208009404041003103c411071015445ea01800c14410828a880811940945020483d0300e02d21101d003100d0b4503541c030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 595162634 1250 595161384 595161389
    0x6091803050f0c031e04082514040603022713020901090506120a061508011104050105070819031a041a010e27060405010f060206070c03090b121906 65
    0x308809101403001d0050b1032000d0800ca82c4103c05482c60884140c0300c5038040e00c1701005508031400c022505008804041040e50300030450200034101600c3d0303151000140d03040c1440740000446103130602544944540d04140011640030340000b0f680d2031140070303407000030315242ca0312646108402c0024803104210180e03d10825000341410316a81d00f84487c132400f07040d0007404184c0184c0f04031410501e402c0700300304c00d1960324090b0340000f40032440c0b00540102c020031340c0d20120703c6a041141c0c0b030307950480e0001114110703102400d0a03507542503d441e0446003805002004c03d2050180326104994541540007040c0380c880d07092a22002c0f10a45003080b046600e001002c0b42c0c488028030070030006500602050400c1c2e40010b0080540360380f00042c034580164040c00c042030792004c2c3c40903c219403d0034010140944040100701b80c5490030204000d40d2040000c2c01101049512400e00c0d09140c0141a08000390000c140030740d60703400540080748813051054504c041041c0e600040b851901059100b0300d8117 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 595163884 1250 595162634 595162637
    0xa0b06040b0702040504171b120a02100902030c030a0b0a050601030216121407030507050111250305120708040c080c010c150e010c0f08060306060a03030c1103030d06091803 76
    0x105003242d02400f005085c0188111450340c952a0f0000001000720043d014482d20920103002c0c00c00c60840c05428070305414091100c6070401e1001c03489464012440c8144508603480c006080b41c44ca0000900d45030000d01040c0d094000d601094007480f20007840d03a03214049031102800181c5850b401141240303d0900a00c0401442800d0480001e500c0c000640315020586080da42c0c584064401c0a0346906c244400c07008030780b0020348007080000a004010000100c40f80080c00d01d0f0701b030081665002444a0307402d0079040c07111203170010540200c054440e01c9410716081e0b0176600d80300d82c0c042d091300810f071000c4d106401c00d0840024007072000030380d0048186060b561104070720170940e0783e40f0380c03a2844201040100e48a0030260031600003442550342081e86644d80c103400e00090340002d09051001391007180a9040a81000500c0e01c86000309000c1702d40c0361814842c100700354240300c0942501c0c1d403012076060000061002d842400c0f41c00c40004e0301c0e41031008000640b40550040c4594403407020040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 595165134 1250 595163884 595163887
    0x181c050f090a03020a140a0902040f29030721112208011a1c05030304110105120408031602060907031b090204060c1203230604180b0a0b06040b 63
    0x8000d1180300054596800050b220010321078684c4d00203030110000d81c10003100c0514913100c20315103282000c0090010800c0c200f0451816041402c00c2c8020545030045410440c0b0440003080e54034102208030308582d800d0314400f0303181d08040800034203485001b001010382d5886140c1c24049000f082c0701c1c802e180204405040d241050010748a0b400010a010107284491856000200c14400f03000e6050484199070524001701611800c11043d542001d4104200d04000030009000030740010450350801d4120702000c03503581003100100ca4511404508190042540041c00100b0400401460080f04194000c80100f14203101c03c0344e8841e41120080c01e180e100c603404101148081710202d805130b900d043e5811140352900d50138400e03644103a222600040346589024107110002c8240c8050118526090200c501c403902d09003000898203621035035000446c40800d010f0b50b41d0b40d00064000d111b122510138100c2c40c0741450105190308840d81c48946091040d01c0416140c00c00445090b07800d160581d9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 595166384 1250 595165134 595165147
    0x10801081c030510240f05040f030305032d0f070309020d020909210702011b0305030402040b031606020102190201050103030f2f0a06062909060d05181c05 68
    0xc401804004d071000d900700c400d2500c042030480058690408051811079182c940c4040b03d00020445c502d01000c0104015050001b8810401032825030001c4a0301850b055441c1e49803038200d104d40240a05131543c451048204402903050103845a81c4215030700c000c240c0d5250340d010300071f034182c40d4441d8000354400d1507641e032030005142c803035004c5030004200030486e40b5041350001d0551488005480d07010b20481b012441400b19a40800c1c4a04400107140000e90b940040b0b6502030071600000d44024402d54680d8111101f0703440030480704454a864540105045a80e1040a4000d601022140c490300005410041c80e86005008290403640d26950f54210b071612013104407a07503590035075140d00c007144004502d5107007500d29815903054140e071030280107000e0040c50070100712403440d44004841d4a0074020f0041c1c00b1404d9900382c0c4c100c000e043e680c980d0384000b500086c1c582d2042038442c3e20024039243c180000c0b00c400f00d00b0104107990719021184480400c5502412407003c0c01160b07400908100803c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 595167634 1250 595166384 595166387
    0x209031005181e24010603020319020a030204061d0612071701170120090d020609040c08040203070e090c0f120601031b06050315090702030d021206010801081c 70
    0x400e5118052402200002c00001046800c0c0075601c40e40c041c54401850311440e0403981880720000b0001e000d22400808004044500907030801480340c5420300d54040b0001e40007440301d44c83d0701c0380200344410445d950035180201800035081030090800194041d02c3e00c6c003240078820440900f100700103000701d05210150128842140004002a04003c0c1c044d1b215401510000e160b903018180010f070382d50317120710b1b9500f2650844803400a044d500007521112260540d00700c80480d10101b00c10f4036080800d86640c004110644070300c42e041504180b0305104c681a060f401610240203e20850544411380c3c0d032610b0352985100159500403035a0048030b0389080c58600020081d0250304080c0450552620141324507041c80804d0b802a40c1c40104200c44d4681202c2454a04000e03044c581081811410800c0d80440c1c00340403c070301d42d400703410b000d0007043d24540208180c410590031818155500d10300e84203180041c2a080d101d4502007003040c030010803d460003091600d0b4154104001c2c003000c0050150 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 595168884 1250 595167634 595167641
    0x70b0703050408010203010306050115020a030c1b0e010e060f0a0308040b031308070f030e1005120901060503061801151404090321020403200603041203110c0d0e010302090310 77
    0x104500780682040002480c481c2070002d10b00a5014110004156240116184180c80c6651054007190014031464002940044501c51344a4001e924109460b9824450601c5001e90b5003003842114005000084c101c40131207450f9101c0c0806544a01d442c2000d8405d00c020012107010051122400340410310080d05400d0140d0f9001084000550b0006619151104154403610081d18140035a0b1005401d05030001411170071410701341e4014886a40e0485c0080030390280d840704240d4907200c000410342e021401d40014020300b20003000d0302e1840c02c2068034920f1541102140407155400c2103a915200005014010101c8800b40f4142c02c801c0d51480800c8000c000300d80080b014812a1502809a540550181e05000f01d4400005940e04e0440c1064000c9114040100c0c542d1050140c007601603441e2481a82d800035403000c003000b003040d0140403d4026020048400d0381c2c1c1c04c00400c1c0d01001010004101c007034050076850301c100c2c50031018011000d034818442d605415a0020342c16102d10b185550 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 595170134 1250 595168884 595168897
    0x15040e0f072c1905070c0c0816050409080705010c090806010e0f01060c140118210507150902090403030501030b1302101b0b01090b010816021509100509100c11070b 72
    0x1009040320f14116000003c07240e042c0c03401360002e4070302000c103800c0210411400c030140421100410404600c0c10f00078040400d680191401651503001d040c1c00c0142e01804e49808a520100070320034010360b484014034900c00d92148404c140303d54000060112105040503001d40b068a4100c54075038200f140a40d800340c130700e0904a03003000c0d5515105580c0d550030302c60412507076503100362101c207804c041c1400ca20405060284000b08038030001c40c8400346811404660069034442191001d82c021302054038010001403201a4202c1c420008000805905074001810399104501e00342d882c3d1241000c65042c82c85412000390406201b1078014245405801215001c28144202010304201691000c0f80da40080e4060408261200e05001d0b083da00710304000d62003485044000160813980300e000b9034a00c0841a0715a00c4400c050108071820f6080c0b040048242460b941880f01c0d0401807041d07a9610510403c0304181883c3c41001c9030421300c44c9010000d032082500c024400d482c00e11180401da90f1112 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 595171384 1250 595170134 595170151
    0x30601031e05011e0b03010506091f210201030e0a02090106140409090507240504030b13050f101d06010e0603010e0a0b1012050d0815040e0f072c 64
    0x42a20700024100740254900b40c08070300b4811082c102d510700504141c036507481ca258442c2c0d06140801c0103a0704e8a20325140e11501d6410b107000c0e182081209440031000c9604421401c1d0304202040414000403000116141e00c00c0e6030801101d081483d0280d210b18543c20000d51003c180c0004002c0c9034843c3d000c5003514083c802c078980ca010b507100c0f00300c000c0306d1225208449941112000f003000184e000c542c08c4010342c51001a03059a05440002001881180001800c40021070041a0140419001000e4444d8840c08503017030240081481030b40c40c96a00e0400b91442c4c2840400c40c007102958a180d000c0d000301d0350060180340d00700604a805040c009201c03640542d038820302c240c0c081e031003041140350150040c3c020740c0442c180010751000882080c0c2002050340c080c24900070000e0302c001811428020a0703d800c60194031031500503500403485c0000c442c1d10034140840b10340b00c0c51000c60001c3c0341c0d4031204111599282d4820000b0500754040c404014017020405503d007610f00200c0d440da5200046 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 595172634 1250 595171384 595171433
    0x50603031b1c0302030106140a0203040b0706052505070305090f0d0b0a060e060d06050601030603060e0f0714010206060904050708030a110105060d11040f02040b0d051f0503060103 79
    0x39510021074040c0e040358031000d50790128031500041040c4a0401900d030481c1c1ca003d519541c1006c0000c1d1400d11400008204c41800003145090f062007441564080c1103a20366503035541415062060203040283c0301141c403801240d0206800000014000e140e01c441078840f18140420740d02c0a40da02c0d08a03d81f00d540120240c40e0189140e590702c400340c00360911501400255007400c1c40c94404071101c0d900400504640101800050303a1490f815200c5143d12070000b01d4290340d6800100c0c060007461340010010780c14580c0760404c1c0036000c50700d04580e4030740b001102c03a40b65444949890241509101601507002400800c4107410300c9a902540140614112030209994003101031179503121411a00c00079980703040c010300c0c416080c05032a8003da000c4840094902003500c44070581090001241d101d00d03541c0e0030101c0c418050303030161401000002c10454441e000c01700384a0140000f11422001100240c11490b8003801d00851102558030140050000381c0c00c0d030b510950aa40c9401900c00307000003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 595173884 1250 595172634 595172647
    0x213020403030203250b060909012409110304020603013008030412050712030b0d02040e01050103110901030f02010813140114010503070b030619032f0405071205060303 74
    0x15540018801035200341e0055a40d0404800340100c800b411a40d06041114004804000f007460201d4082e001803045a80714603179103400071400d00500304084840d00884001c2c004070a40c0554100300c0302114840c940500c14414140406580d40c403040390002d51000017800144906840102d56034001c1204228005050007007441c1981e03a84248a011104010001f041000300441b0401c0d024801206050031810000c840e07858060604624198408059842950711141e40d01d0360250780340070380c003e4010048489603580850203400240416140c6507440d0f584001c1900304109046d049a810440200201d40f00d80c0c0110b81c1e005010307145107071071203807500f074a40856007660680c002e98440e0000095034441c400350840001205138840c0b8801d0708501c1c4c00f080000788032000c8980c00310003220507801c80c4566803140b0a601006800180c0701ca18088945102d03441040110800107402c0025600900003460400c0140c4408540a000203610401401c0e00c40e252034005540080b0001c0903a810041c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 595175134 1250 595173884 595173919
    0x21002070807150501051503010b03130203010b060c03040305010b222d021218151012120801081f020310181e140c0a030609020f0903102702 62
    0x24001100903030050b0790744c80100002d180107255503c80303002c0700c0003d40c00c40d031400e83c2c41d000c607000c0108010407001028856208554081d48041040f50008060035102c141c02410644c3d41e400c1404105c860390310300484081d040c0780c030084000318208030b507089500c10105405141c0203031007102d280c2c140d000310302e00c81e280da900c400d418594030420a003070b401038686451041041c0c040d03201410740040712103d14903408480c034021441d0b4003808407104040c005902c4089007189540071650007200e090051103500e1040001040e02900340c2544c554403580705981713038882c40c2c1e214807290a8446240a00c0300a64030344e00c45640280d580200b00200741800c8980d1041c9032401031000d421840c0e004c540c0c03032080f01e0814071060070711180b04a2560040010340100144607880c0704014002200280000c00c1074511180b0a80100001d48006c45081d9102c07448009085850307080034951070301c640610424440310054038860300da100000e40c01a0800c800e9561050340d0102180501aa00300f19005807500303000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 595176384 1250 595175134 595175153
    0xe0f0a1b0f09091109040b241203040510050316030c0e03010c031b0507110622030b040b07021506090c0c01090b0a0e07031104271a010603020901021002070807 70
    0x6005520001c036020783c003858201c2c074030030010010380e120301400c2c410311000ca1030b07006856600290040014030096100b0003149003031016080c0041c0d0208012014400c18000440908112141900c2c1c03002c2c10b40f1213102c10343e201e000450b0310310f000340002103102c8a568441d4100c0000c452860400301110040900440d0a50f2444000315002c40d440d0031541c0340c0084071501003c48000307240b40c00790800301d2956401314a00140788800c0e10820f4041840341c001c1800c0c0d541e8004000341c108064040c0ca41d240340c0056401411201646c0880465001804070b600101f50781078501030301c208001180e5141c8080010686020b482030340244001d00031160482c8003481004a00e031300607180000d00c0d21b40024070b070050f03803c1500000360581001704c0c10400201d019503007460808080f0307008614500d00c41d07012004241d541d00e030030422200165540c0103001200250960034614113140100c0c40c0e03203c100c00d40c1a0300c80c062005006a20450b40d9410607400c96002c3d1480a100311419890003040b620b500011 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 595177634 1250 595176384 595176389
    0xb03100e0c1903200d060f080703050309060703022a030601050603040b07080405030c0708010609050a09080a081f12030e12070303050304080d0c02240411090a0615030f0e0f0a1b0f 79
    0xb140c6e034642c02484802da2051084009200c86002030070000d0440c3d5806890740180e1840e030f0b00400300030511200301802808080b050809844000e8101014800c0751800280c02816150203401480008612801d001d01164407883c1c001001c0050b80c0c40d00c22043b10340141c018025505400140811040480203100d01c0d40100041c0f0b001095150a18058004484c1c0180c03040d600145050380c50400202c1d10010b5a0b040d4246007007441d21540c0b80e00960005e0076503107640c04e00d40514400d0100303204c40f2540401034958026a01d102c5174007015000e106116000f09041a1030b03500050040002034850801181c1c05845140c02506208031081200181c0d400c5c5190350016800c125440c9042c0642c20021140c07440b000301c0240c2240c2800d4541c02c21401401c100f0b0307401a941940000c14072150340d0400001440c040440074090900f5040050091140700007801e41541859510f00c071020001654401d10420720015180c10500d640e1984614a910800c42c624a44620340c00603814003a145031000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 595178884 1250 595177634 595177657
    0x60105162102070f21030f0324030303182102030d0213030506090318090601111b010e0d080d051f060203090a0b160303020903070b03100e0c190320 65
    0x9007042c803c0250140340b5001480e40c01104005d20000c01540c0030740614050701401c00807141a804202240600502402c1c4920724544941e0b21103500642003260045030b0195a003004940501c1180c44424403100801030410703a4503d40342150030300400740b401c51010b46030045910b0519011726100507070f0000c0348440daa490000d00708001f4494184101039104500001852515822500c200080000400d103039004041e5200001c1035a4002d2000e40c102d11400350440d03559a201001c2141061880c1c160180000c0e254458009242416580050718662200245041404d02850500140760052055500092626103441103020640360740d4003030a1154065640c82000805002c1562010f6000d003800c0141000070541c0802228a10082543c1c1440c0243e60703000d4880009191107500d40015412a00c00800d014603500030070b6840c01202c490100102d450b5481a05c00e8403113004880d4205550030a40501c0c1c0440b0307203e94091404060003140d00d440e4903201c40410001a00490382c1d001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 595180134 1250 595178884 595178893
    0x2070b0408040303020106050114041412030711031b3607020a050c0d0b060d03050f0c03030a0c03050f0103150603080307030b0a05040618020304140f071d060105162102 74
    0x11305130b080c058040070305805c1c00c06080742844150300070300ca07115030701c200c200c0c1c4007048480d160180d41d4690510031402d000c1040700e48a20310790a1a403440700d41491000d100c3e11900d00d110203084803009050300e04100042c548110181194650500d101c100c0d03940303143c0980c10390303074420300c0715003c031040d80c0503c1322030b40103040507270756454854900a075410715148100c01140d482c100089100954542c001026035603240161070078078040e5401d0095a0f010303203c03480c000c207040440940000145214122501c81403010b06400302c01501224410b581850301403020f0700c014004101a425101c1c40e48051507800181c1a41e20344800300160002e07900d220000b80c0354154269140303003e20791480a490122010408a464094140000001d080f04000240e40101c001428005036000c05140500b075003040d20b0700c3e1108090980d841e149103020313410400c00e10f403c11001480d005800c65100d6070068603590700c0c201310030300805503003140c418044403101001e20703c0d13108410203014402641c03801c940040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 595181384 1250 595180134 595180139
    0x311121902010c0c02060706020a020a060204170610061b05031e0d0b031618020c0f03070c0e070e0103321506071505060d0b04030504030b0c0a140c0102070b040804 72
    0x3800c3d02d000c4a89541040014160200945e03102da0031a44001c0d0300c404016980c4442c08070683c1416200070300178003a03910100d00025035184041c500804481040300361590360356504810f82901842d0f0080c000011207081c5461502c80b964104501800d0062040f2707400d01c0c4c108410301d0206a003201994106040120b405079008410f8000e4802c800000c4010700800b142460698003103001a100b0030880b1030b104810440c40291950446181c0d03107201041c0c07242a005d0b020751a54a60044c44100d8080e10491030000300c9121100f9000d00a10140c2d444203003403041c07800110068408607a880d0282c050320b0011242c041880d10910b03174400c0d41c019803914103140c03890241c084013074110b08035409a00c04110300c00010704d10400702194081d5a103400145c40e2a090041654040b501800078004404a401d200601d43c000d80540104d038407400da0941650f9079505144101e0041100400120319044805902d03644428054002d40b50700e01c000608001c000d0320703000c0f5202015034040e00c1d141c074002810f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 595182634 1250 595181384 595181387
    0x81e040f06151701020702010e19050301140402030f1b06030402041d010b011803020d0615031a0f070e0d2004090809040c020106050d0b0c091f082203111219 69
    0x10801c030f10480c40e00071403c0011507000604410b80344c450080c4100e108c94030516200002c071400401500c406030082140140c40043ca14080f60240c400740d110b40724000c40211105400124680710556500c0581401210641489038941000d40226401070725520b1501c00c680311300d00c02060070222000082880c0100701d0000d0300400410540001d2130220610900150700c401c24441c246941c05040052058500f105600300755006800c0240f40c40741d03440c80c134030b0282c880c00100c50040c100803c0380021521103e03010344001381e0116245800c00250711260002c50300c090345045c04024085c40c00f40d42c460b000e00c0042d08031000f00310221415140886c041074641031038898041b0900b0280000c010381130070080090103212030100020003a102003000168642d0329001503495804020b400b502100c05100d5003141400034152030680018440c0000842d43e110b0000c408240020849007070180c2c290a4238200c4081541000c03854172446250a40d00d581c40d0480003c0900c162000f51070206844003200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 595183884 1250 595182634 595182659
    0x170a091109010f0e0402030102121906050402070309051002210a080915010b0c15070e100c0803071b0b01080706080a0203070f0f1b060b030c01081e040f0615 69
    0x21481d014058020051202c1412043d2042c20750f81050780c884078a40da82d10010b0f01920070080329449450411044c05840084520340841d00c1c4000c00082c400647c4070008e0008900860070702800140c0c40101c00c001c40c2c200304003002d109080b1803064590010540307604030042c107524109030090540c002080104590700c1021030b904100b040003c1c0c010940080c00e04400f144040c007410845040c001881d4484840420050f10402028400900b051070000006819240c240000c6070007044180c03100d01d140f52140b80900d913910307031040f1b00a00396100c00c034089a019200c0e452040c1300041c011021070106080400e0640205031103c000d00e01c00341060f100070a0094094030104080d401401845034554000252800c45412440c000400741035549003141c8043d05070342004080d91210009200344030303441d0400c2029003c00d40407200c030b042c0040011988868211000c11030318944040d103201190a4481d17468220380a50410032030000030740c5030b00c001c6612500c0341400340501800d007000003409200 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 595185134 1250 595183884 595183913
    0x1020c010806031b0105121303140307090b0306030a021e24220513380904022206060206060904021e040e0d031a09010f15170a09 57
    0x203800c101c00c0c209100841c0c2e0b40c20f18912a4049940300028503075550740308409440712511410101d40c128201225415005c0c0d44045054001030154000344510700c801d841224064405036a41403281860030800e0012070b00007500b101d905014820030080940c1d1082252180c0310100200c0103001850300c0c00708a01241d689255012580081c00045c4036000640c06448012038480e5540d00ca1a0010810034844d0300c3c1c6400c100e901c400c1945810104429035407041c00901022a1400502c03d102c445d255059841c02448040c2c2010b84803504905042507540503400c06c2c40503290002400350810110300f40c50042c200c01038125501c071420095964100302c0c00f0f0700b0203070a0b00e010010381019004186800b24444c1400d8545000c1342144505840d2980b19500c40e648200540c0c00c030040d03128000340030304105940d64080601d440e900700c00610f40315506078102d0b0500401c02480380d15140c2443c6100c112a1008828002c10880e01c510412150300042e20400100301d000501800900d0070288224040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 595186384 1250 595185134 595185137
    0x31f060510080c0a0c060903020604021206150103020f0c12031006080f07031a09010821040819050a06020d091203050708071407050a061b021507080402040219020c01020c01 76
    0x401a078071119040501560406200b1204a039110280f443c1038881c40c02002d4000e060f2072620401030241580481c43d0b80c0618400c80c1c1e08444081c003d40d105640d80b405071180c500203090b040349588690701036030040042c03103201d240c0181007082c1d0007034403404c0c014110b4202500c00d0000041095a04001884030040c002e9400c2002d001c5c2810030412902d040018200b8080c13650301c4402c401001050748000440b0b0600030411251036845a010782c0d04c0d280080c0d416011007030310481e141065035204041e1400c0d00c2c0105c0c0284940b1205d0140a890000b4407030054446024a40c0300001142180c0014a042e03011980040348201852078109001d5016150741c508241c900780612681d5030784404031940090341c5242c030060410424490307442e180302d40c10004001c0d2286028240401c0901d4000200c1580c008041a038038140710f40701a62215090b801032248070100d00d001903810307401980d1032a00203001034001401d220701e50301e00780010b50b084210320300541e0100b00029003d6904110021504c40203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 595187634 1250 595186384 595186399
    0x30a210f0305090a060509030706110901020c180c21040804180c09030602090a0909060b12070303140d06050d110a05011106010506091504030b010f09020315011d031f0605 75
    0x51280c050700c6014400f001412983c0b6940450b0388110300700180d5034114ac11080c00c019180f110b45603003c80750302041e021409805804c801d591985060f02e0405550800e2408100403035842d094103441c0d0b41d11007132001e02018907075110a482d0000d15101648107501c5840010b903505d04050300480e200080041e0101100d0070f14000c0060350b0360100390501240c1c1e00040c0036032511034500c00202107141641040224030315012201080c04042c0d0000c520298003694104002900e042207540c98100d0f900025022400c2403054108160303001c3e004059400092900041c610345900015030801552002039840312200c800009081c1b07454091a4020038090902d86015044944111303161101445170621078507001c225000d49841d01406072120094035610340d03584549918003085401d50038010384c068007088450204080645100300c9004120311203107805c0c05500750307004560030340d00781c561140c02e440f264013210000d4804002c054606450700c50031440c0c401c600d20128003143c4a5078804c0340314441 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 595188884 1250 595187634 595187641
    0x11b050609120c1c02030c01020d06030606050109050d11040615080405010c020d3501031203060b030402060405091f06201605100c05030d090204050a1b0e030a210f0305 74
    0x10006803034442c01c42c10207900c48510b00811045e030440c012020402001e500002c0c0300b10700400c0c1c662200017641e1140d0010004d9075141ca0045030300e918030303001e00c0d5044421070b009003003c1003070300c814500d04c4840140081031060b10781c842c546080c907210040e08003203039004080c0020040207001c0d005e1180c15510007007041032100900102000c12038401103003203c8181c01c040d480e24005c01501907280740c00020b07103a05940d6030700d031414012107848010000245001c401240c102960fa00716806180c00400781802c0078205420401656400741c607509409a291030a002c01d40d8681500ca0000d00840e252210f120350b0306061f128480b10700c1d030806005500038169103402210a1104072055881c00e80e4050360081c0c1130001903403415130040025049200100390090b10298a0300010101c41c800c1d00d00b8469500e5a01150041e02d0030980c005600021140c04d80040500c600410100000004c00300d5290312955155612781074101b24610340108803005501a031250400c0d002c2c1d0904440c1e00d4208203516 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 595190134 1250 595188884 595188907
    0x901200301150e090103030c0b16050d020f07020306180d0e090f1801090f060f02090d020103020d1d011401050607080d0f0f0534021b011b05060912 65
    0x1005001e10707034040d000002c4400782540b0401c2d1155582d03d01520002065849041c003915968a0101c2110316281c0c200001e1144103c0b4440c031081c444098517a6402c0c030450010b540013a40150218554442c000d00600c0b000d070790308000c05805115001900803100c0d100109040c185947c14202000340f1100000604480d1030310072140b503103d1b03118451168651169506681c4403000300c2d20900c5503600b892070520034810000740501090384504801c011480301016500180c0c0200d901c0300e40c0c00f2181d1803071400903500030b80040a20031100d440010b00003000c2810f0854050140c4000322841c2c0d9200104695843e882c42c10700d01400040301e000c2d04000d0760f981e640149106440010722010713180c126100403502c4540200f800e05017a45024880751400194810b0b4041d00340c0541265408020303c5101001c1080724039000c06445a0301401e011a000400300c2200f090400e0340d10b040000101c2021081d4401d0002421140c0c440c10140505040c10522a4a1308241303484481e41c20104001002461 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 595191384 1250 595190134 595190137
    0x20a030609110406080610020a0203100e1504031b15060f080c040b3f01020307120b030c041d0f07080d0806010e09040c18060302150403110108090c1503090120 70
    0x400210f901d11030310407000d40100d027011846d8100940500c505070b4440c142842a0b000a001560310004441001800e00c400140c1c02c4000d0718041c02080310b504c0b1104c80500400301c0004064016441c0880c18484050307018100e403103079032000d84c034611404424000800144692042e001d400c841c18448001e119000580240c407602d041c850000030440b0440a80b030200d00e0101440400340650f110070313628560304502070750085070013600007940f07000e5211801106102d8540104405001050042043d00c00e200091000c0314542480c0421074000303042c01c007c00c1140c400862819006003088510b414141450210103409039000c0c0002c040070400b80b40d034800104070341c03603904032980c4840d5200c07070070110724150140d000002c401c920148144424030803500300f0401c80e4429201131404000600380c4d1805ca009a010040c01c240000e03892003002d61041a030550001c0f21801541c00c014140400560030405800c0540010a800700410412040070701c1080c070f40e18807100f0000c04e49002d01302000c040b07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 595192634 1250 595191384 595191391
    0x11202061209010f020304030c030206060a0305070b0d09120504080d08090a1218030309080c042717070c14040c0e01030e03130338150409020301020a03060911040608 73
    0x881c40007592505094100700c07095840e40c1c000f10350324101410000c050281c40b803c181d01500c90308001c20300c182015000c0c0c104880d00715016183c035030300f07080c80c400307055020150a0710032a0300c0f0881035020805084001c046004142c42d00c1e03540300c2c03920070300504114800304100305001002080180441e400716000700055407001e03d442c001807549505035200003541c5d40c0007410388000e07040423003016007154a02d42521034950031101410341c09001c01c01906d038180312000b04440b84024247c41303000780380411390f80c0d1481070103040c0030200c82c04c00d1004070f600300c02c00590742e040fa0010100240780303202c10030720805203060300c05016103205480064240600640c00314101640c0e19403006c00a1b801b80144c0f032040d00d1441c0b0070071489030780741020100c3ca50702240b05040001c00043d402d00b1420181c0c81204010f016030a4000e0325603607442068140440350500681060b26500f141005035428070003000921282e4600080c024105000f0504451146141150840081005000790754121a4581e0b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 595193884 1250 595192634 595192657
    0x5062404020d24091a0a2c1609060c0b041518080304050f010509060c030712020c06041202010b060d0b0f06070f060b090103030c02011d030609031201120206 69
    0x9403100c0c0e2440700d5008103001205203000341c250075445100014102c43c1031003110340300c100a01c690240722039168144139840d01d42543c050b2032040c041102d03112000042400414807010009031a012440c03140c00303800c0480341c00c14104440c24008111607044503409001d02011b26121031480c1c000c1d600c5846040300640f0181c42c0c5038480000305089100e5421180000e04601c0c2e00d015000501e140588007500269000c0740c880c01095004001c420052040c03920071460b0400400c11354540b11409032040e800a00907070304000039858120280526400140500c51000c0020306051406003440f410ba00d03101340800c0210390600090b040d50741c0e10036017503607851035001500207150810900086c80460745124491b030441004901201440203088031141d14030300803141403101c0c1240c0f804008800c01c007404010081070944061001551103001e10720552030001003000e605454020000f0304d0038404454242d03043d0301c0021903001d01e5020802450040c903a5200304180c1c0102a030011342d407806000b04144 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 595195134 1250 595193884 595193887
    0x8070509071d03010c02030c0105010902130b1c0216020f0415050621010e18060c07030c05190b0601020d11070b0a050409060e0f07021504120309050f0a0506240402 72
    0x8281c2c0d0088042d540d802c0c00010000c0003151017510000c0d490f904101a00e4295510701383c00000c1c4203600c0c2c0211401c03016840e540301202820001070f0500350f04074811560101c08000006045045103100030120303040c0d00800381880002c24410040741c58100c100305401103080641c0c00c0b4a02a10b00059020b9400c2152203907150700f22035556010340041c2d0401c0c0300c10f400040c400046c00c5541075040c180070340300b000d4114152240600140c0c3c0d1380c01c001d55604222000030010007010034410030489900500c144152000b10001e07800710071a401a1a8050350b00c01c1141c0e00380613080d83c041012035003404079800c0c40181400189849178594443d84a00b030007a8800041349600c8030b10a1084070701078800c3c1001003000f81d85408090180d01003c440050b407510199000c110460700025010100c500000038920311543e030f69a596038182101d00c1d180c402e040d1a43d058400160091107400f02d11031a2130010607800c0c513035051151070f000340944080300e02081603540820000c500382c0c0c01200508280c4016 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 595196384 1250 595195134 595195157
    0x30f020c0405010b18010c08041514070501330b09030f120c01140603030d360203070905040312090507050d080a080705030105011d060904050f100807050907 69
    0x1a414888105060341d402440c000c0007113610071070900600303d540c1d24650304c01e00518841006441560b103428000e0104002407200b0820441c50084c1000c10403130b149840c61414102c0c541208030f54021560440e00c0303944a00400311001d1b0100e0100c1c002c8051004025082c000a004002480300680250102d11600041c01d8140b500c0800c622a0501c14040c101c0303950205804109422b500818000340f0603500304051101c1d4241c10200c2c1ca801460018055481c04038003004120041c240000240380c1007807200d040b00c044e0044190f2645524218080701c1e00c4c05101c44c030401d42031014603007020111518010500022903403080c186220111110300c002196034150800a14002a56010703075441007601802004000a1201070803c400441e01c3c2d80507191140802640c540c0000d0080500044159052038164220b00307941e182c5020b0050089131400324030501060540e03170100c9001000105840921640542e01c100301c1c0700038a24030015060485c01d100028000c0c0074050024010040700f03141d031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 595197634 1250 595196384 595196387
    0x1513170f040609150305070e011d09090706140c0a1401140c0a0807080f150406050901030b090f070602151e01080715050c030901050313060e010902041a010c030f 71
    0x8032204000a0340caa2a141c0360b0318280240700003028015220000c428051054907240280240c42c043d00c050780b6402e65120721480111000806500010000c0307a08041c80c02d80307900d1310480d55014624204c0945440303400c107240600f428405c0b0703205807a141420090300c01a801c000c80c8076200c0b04d40c4a170070040300210b01d03d801ca014000070078051402e00309681c01d02035a04140c600504450b402c0f0348401149950755076003903411034422252503c1c0440030b940010303448080301d10041e04440c001000001e5581d00c0c0c001080b206003003600116802e000090501c04910010010910000c110070010541c4c103007800c3d4029142c031551000e5080c899481c00100f10340744103011440c020000d070242203440c150f079104102960307002075114098048041c0201c0d00b404030700c65000c0744c61003001c5c40000d628107139160004581607032000f403905e214914039000c001c00042d0180605403040c1404000814038180714010402181d034641c100c003090411070a8030559690304004010f0310142c05080c02060f07540d04550 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 595198884 1250 595197634 595197637
    0x2040903050f0301060201020a030506030f071811130603111806090d060f1416020c0d23100b0f1e04060b1209060c09090406050a02040b04120302151317 67
    0xc0c000c690302c0000c000440c409505602521054601d039a0520450300d601c002d06494030001c401500c080d400c1600c050101c62024a44016a2010700400141910440300603224035000803e0900b4000c84000007080031a13414001c41d00c5601c05080080d00e0002c00c5900d007440c2c13450b5180c0301401600302144040969843c00461080960040310500a901035082640024042000d07441c142d5070000d00420101d01c10b00c40a20700028540c4c0040c242d69070988100012558401811140e9880da5444440c9100041c00364801c3c080304d1000030410003404441c54419070b02d0005e0400d024040484903841d8036600c205e81480c444810b1140f1400e072610000100e0007600c0aa0000c1c0c0702200c00242034001402501a01c0d8402c1d0400d0041c0d51140d114150361445520071325400c20350105a0300040741c0480c83c40d0707115070340110404034010310b440d55511900b086600164090407074004203070201002d06806204000b08041a01e2940845203404860038070b00783c1d4109409048440041c2103680c0e4080d9800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 595200134 1250 595198884 595198897
    0xc01023702061903110c10021303050f0a03020d0e0a05120f030a05040806060406050904120c0507030305120f100b070203030702090a0c020f0118140327010e0a120204090305 76
    0x2c05056460544001c0382d82502064210003000a140100300300041d0303598801d407400056054050500c1a0320559140003070f400900407048034000d10200080050020018412004038050140550790315504000c0e00b00300c0d0f01101c01d0144011a080b10300c055982e000c0080035114100c0365213003400d0003046800d00e45100f442e49603a03540f000103044102603407c6000790084949450803200503544080600054030102c1c440c1c2ea410215000128000480c049568000f00030f0525001c003c81c045a240d151500401d58030076030101d41c0000c4c1058500c01c001090302d07071098140d0200c130400e0600c4509603060040030300c6901d40211011815030115238082c411150000c1c1c00901080050520381001002001904100317005441a26040001194180a8a0721880b030a44600f680b44c4190344a9000350500c0303424182141c00100710004050010311600c1c462441c2003103d04074051301c0c604c0050320008400000314410881240f00b0031410300c113a9203100b1856415100464000001d01d402d840b24016030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 595201384 1250 595200134 595200139
    0x209090c0d020c0f031c140406050c0f04061706010813022b060f0c08010f0b03040c0506030702100b1207150c14010b040b010311090907111e0c01023702 67
    0x1080c200644d2240000030b03041e134008034005140c0744580060f0200c01c8543d855080c0360f00710400302c00200400c42c1580a00c1d8401d1418405038980709008544003810341c050f4201c41e0104200d880c11080030030b40c01c44480da100741c0070701b0f208116040005005030140300c4220001e220f080000c40c1040c100c3c02c0800b403607240b0780300c00d144140000b40780d181c038101510000e103085000358074042c21030178914841c40615040300c0303815075424015410041c1c0c001032a403000f803094510288000d0b0019440d1180f20003148610703903e9010709142c61000314050301791140000c030b080c420041106415505c600c04188801180c4a040d10b01d0507226003d201030b2100c0030340c80385c00b80c5000c0050340284a0b0b003806411032520703800115810805403030208015011100c00e043d003080c01c12030a11080581d4100141e4158203c0d4840c00c046da501b1805010441c0b81038030300558601003c1224004040800d4100070841e0040c01c2400502031160001200d0b807081c1e89034a20b5101001d200da60700c115141c8030119a4210316401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 595202634 1250 595201384 595201393
    0x16110a03140f0303060109030807240f060506090112090218090307140106030c15091703040501110102070521070c090b010e030708060a0b060910090e0a0209090c0d020c 74
    0x220309000802000c20640701c062801803804414980700d0210403280310f20700503100d020f100d41c290340311080c10740c00c00b410072950595294840452080300100e140110902590045003c00c1d42001d004269402580190300405041c03203030040c0c0381e80015890f0701c010940000040c4d03070b01c450b000003100c080c0d407804900d007441055014409068804002040705a00580d8201d8030b200310845007a08a5010b0720014140001e441000c2c407006050400812a401040c60069002a2078030450303401c03840a0406610203500c0040e040240d07503004500b00b01003808920085040106c161103142c2c03a440110242d40080803d00740d911004d0b01410b050743e003c203810442102d5402d441c1c003e10b0004090421301e113404a1220032210149103400540c03002a40d0061002e442507032120444400a001c0c400c9400d68418400e008032101070303c8001c40f0f142010410368440a40c0791a00702c3c1c07060716810241400d4105401005108515110840b235203230410300e054031590f40c0d00d40160f40e0100a0140f07608240641c081c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 595203884 1250 595202634 595202639
    0x206011205120f0a181401050c0f1606110304030f12020715180b0313140a050a08070b1003082706030a060303020609010c080a02071b0f0608060f01020316110a 70
    0x10318007400c0304040c0c0c0d0321404070030031680d00350360006030446c4103101d03540c020681d0386891944503a0245c00852208022120705842480710b450404100a0f021001c904901e0820041a9031284010700040010710241d80b40904540710f00c8600c07490b82c00040c00303940c0918400e512080c4208880401850a110310446e4600c100d44000c0c02c0c1e90381c9081210b2845d441c1c03c0701054100340081102d019001c1d90380300000702c003c07954070710341d45813102840c04030540110344c007103004a00c0600144104500c00c1c5c100700d03510b080510300a032140c0d8001e0404409160006010320011b52440308494102081416848510540b443c0c000c003000744002c0c19580200d8003000b40700301200d081c0c00c00400c2d00d100c1d809440386640c95031226800ca40c003035201d41c0e000880f04004682d400071180e000780b40150241012080641c2d01000300c1c0b015a0300daa000480914900d0020030140341c0c4201c0c003070b40100c8219401c03002d032034410000030f50703034098400385040c0400d40071102010061200303600140c018019112401e01c59 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 595205134 1250 595203884 595203907
    0x81f12021f050408061e1f0b0c15010812160501020f040b0319050c091908070608160201020f03060f01031b0c06050f010303270905100501170106020601120512 70
    0x100607103d154601d201d01780202d0340c0040000d440c00b4912000c0001845595100707210402020503200c400620803400780030108800d60348100034403640c480500101180d2149408484090328140e0104e10310b5040340b01c1c100501441841220903c60040342d03251100501c50400c50b00900c10529014145280060700040000d500406584030301207095050b00d10b030030b5101c01501030340e6088500642c0300b2010800317032215140500e1400c030020000f421300c2e00c9650f00c550015240c1202c0383c01070f1002c12020410001d0840d8402c0000701000c007648025420291000482642d501015040a02ca008000100462640b00787e01c00301b03200b9030503051340032284c00e50003001d1b0040710051001d0720050300704400030b007030f503601411901d0499a060760342420703156100406400341030380070f50040301c04420b04100040100e980d01446008801c4160b00360005c07071800d00054564280c410004064901c07081c0100032458001c00c04504449400c4084050594145482e41c00c08940340c02c002d00d42000402e6403004d29 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 595206384 1250 595205134 595205137
    0x130506100e010b0307141c0e0a150906020408100203040b0106020c10030209010324150e09040303090f05070303030b13150e09010e010f14011e03121e080403081f12021f05 75
    0x140003000c1c0070000d01da050022161030709c401c0000548800c03e118681072419a03280c1c0800c1f03c4130b004020040c203003611008890b05000420529000840d0003109120906c00da400366103004000900040c44001242408652090783c40c81000042c035038081201c80503030740250460301d0386c403034401150002000e5261911081050a0003800500c07161000100c51170350040c440b600302040001c010119a82c0c5640d4118080e1440844c104c560001c100900700c000b4000f004a500998800c0e100400c00714820424030003c0c400360344c03070841a5824030b00b0f00c440e502e01ca50002e105403621019004100e950320180780c0e024001000f0a03248540c604401800343c030259900c180707502c02c2030a14070510750340e8504054401c0150881000d0b8481d09121040001034018a082101074003607040c40b95110320716400d1810f0f6425820b03070072030106010001b04410168071001150740b01c179884951198140c044241101110124060103c3c040c07880c0d103881003999511107010031101110100300c000b0051558004255 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 595207634 1250 595206384 595206427
    0x9080a03110f07031a0406021605031c020a0c0b060a05060f0306040605010e030601120c0504020d0c120c09030f0203030421050106060206060d08180405130506100e010b030714 77
    0x540109800440b0281e070206030881100c1e00000c42040c100400850003510210103002124030f50707820840348800021002c45000010b0043c409580c450345414600c195804c8400010055984100210541240c204070440c01c12900001c44030416642e6030085107014041d500420380c0310a001c0351400031842c4c6440214462031094905001c0b6664072001981d510079600082945074001070300502400d842c101c00807550034081c0c44844042945c480210341203901419400c03103015102c50f5074201c006d42051408002d000c04100405c4034200d04030004080400a010080c0f07040c3c95038107103000b50354041064030041c00d1010620450f20301c0c0c90b0300c544140c80170072100701c84550900c440022082d00110701640300b500082d00405000e0343c2560b4090882d4040c040000092140f00707040b000d1030711184103e51291500f2200c14151140c1802c2651411070001e110f0303039805c06800d000b03010342c01c1e40c2d2500314110794011550640341e071241e0788103072580061145070380394401022034001c90154440d80042034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 595208884 1250 595207634 595207667
    0xe0907090b03060c04291206032506030b01020a050d08070f020601080714040e1213050a03080f090604080d080a110c0a02061b0111070b010506040317090109080a03 72
    0x80c00d030710030300781920b4000c00c64007181000c40a0004100140c1020800606982482030b902403042e00010995943d8015032400200e08a01008000103410104001e1000020384a4082042204000d43c014240c00318080c2008140d00c40b141401580d00800210203829840000d80c3c6020300b528000529403030086562000050301d4040e01c8000c2c13030000c61400d041c1c0b00f10301c008d0440e4609140b0303020495201d84094540013542e4524944214109011709642e00d0000481560f842c1e502e04111044c0c1d51854010b51300c50000042c0800c0000c818100b00c2c0c0320070410746103890325000c0c0c540004081d80556030102c241401980b458804280c0d0006c140e40c072a00184000704446044a00082810f019102198106034494009230b0054a000400f42c000306101403486410180361003942c40c00e60b103840000a240f810041850801c022000140502504080d02ea1900701451900c955683c19081110680e40920000310f01c00b05901c00d1000c07502a00f0076804441c840c060070314006000d01e540503007140 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 595210134 1250 595208884 595208891
    0x30902122b0813020a32060a02060a050a02070213060305120306030a0312230105040c02030702010f03090515070c031211120a15120c080105130605100e090709 70
    0xc80600c6541d1290709005036581e10103455694003601060001e41c05000d0381e01c030f000e404000910320410320344a9020f881c901c0d080c0c280c05041401025080300481d000500c110402d2003c195000d40c00038919a01c4000300c00042269100c100c00080248560003010b500140704a0f20040040001e4000c242124410811036030100009921020300b80000d80f00c0d03617495008102c10b03c012900c41d281c0e0550b0f0b1411481d000402d8400622139800071541d41c04561035102c13403100100010701d02482075402d501114006907241040980c002440d04114400001c14542e80d0104801070000c100800f600d9544952000c0b01603080c1801c0180c100350700c1403c21000030364181140c5100300c149005000c0500c200f5108035040c0428215503c2d5403000003003e040c5100c2e0348013008120300c81c854075420024030003035591040951007801c00b200c400001d60000c0c0390305d03810003042c8414003140d0228181601c2c1c0091700060f440e2150344107442408010352111900500302010b110301e213540800d0040460f8980310042 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 595211384 1250 595210134 595210183
    0xe19051819022124040b1305010609051206040503030c0309030405030a151506200f011113091a040c0e0415080f01050c030411010908030f030f060f0a05010f03090212 73
    0x12508810001140000354400c82c6004d400c0c0c00d0541004e8000d2034010104d2485d450031180711400c8600c02da0260000501c6404204901d09000d0104010110f00034080c0c403a03480e15444007507881c80043c0949820340700007c0010700c00e81090083d1030241c00b0050590321120028107202481d06d8258000c042c0007803074000e2020310858130a900c0b030102c41d619102d0b031203070703008605400a0101d1602e811000c00d00034010038070380700e06085c800c500599004099803900c8103c103070105515015150400f00115241c036517500d460704803908044240304000c45011540c480351000c00c8461080d00036846801a040c40c40030700c4400c2c0482d88101c252b401d45404c8802110344281c00b40e080c0e95080d2a048000441007011802040c1d00c545d40d900c3c041010b0600e4502c441da500f04040c650707440110f2481c0a558003100340400e00782c0480310b440e000307070701161b500e91700c01c48010008501070168402c0d54180041a50740c0c0b6000350003034001e010030f1500181601126440110b035542c680080b004181c0d01c20031941c200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 595212634 1250 595211384 595211401
    0x60603051005120d05030c070b0f01080114040506060607020a031203050a0c0c1703090f0604060510090e0c2110020403020a0e07050f07150c0e190518190221 69
    0x5081d030034440d400400c4c00c081220000d4465071300140c96200c0100d020498003012a8003a110540a0f070030035408500c1d1981743c081c40302c1c00c450103c650310080c03000400a00000c1103000400e2500900111031280d5281402d20000e81c4221251303000400c240c0c94540b1460307106416620a61107000000000e008000d072090f0219482162090010044003901c001004017024180166030f01001103412182582181403403a0300d005401c540494004e6101c60400200100d516995002000210010700460300c0c030581894661409150040c0101d0060394044130761041803560511041212080c0c40110b55422039180180d80301d03000503401000001d40028140d8040d9011504c01c010300e961307143c102000705107146082d500180c8159503c4503580116043c1c44000d200e800d084900d280c650810700c0f54880140401c4080c0381c0b010400401c1915030030466519140a88814014100110212691461000c80555100380002240c5d2440442c601d1042c240c020b0802c099001101154006551100c0c3c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 595213884 1250 595212634 595212649
    0x1e0c02010903081f090209031e03041e0b07030807180f0603110c0a031103040810061403010902130c020f030313200114070201020307060509012012130302030706060603051005 77
    0x111005203013a042d4082108100039805012820030040039240d00c0c046003030512a00e1020b8943d182c407035810014080003600c548140041c800b6040080b0035050a1512002c048940944400074007444481c20001d04081d100d003070302c00b402d01003042c2c20390522500d4151010b003880080c02a2030119160030209011042440180c4490505050041c02082a243d50071034a404c2c85801081c0f00c0c1c8010300010480d840d081c0581c07035180b9842d00000410310324054849040011030304600e130090345082400005070b21a0f20b21622480c050310340108a40305040d90480c031f004114020b890f00c40c0008814050b0044410a42c0310b082805200d0b01c50000c110608003020607007014803c00c2c00304062440d0703110300817501c402406655005005a03801d01400e074941070140d0701c00300c0e00301010740d40d65a080851451002d04c050150344260002d103081688034004a104441d029000c007d1607005003510208240c401c200303c8070010341c0100c0a1000e2a603900005c2d014081c10f4130603003221000c800300416603050100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 595215134 1250 595213884 595213921
    0x9020f0c0114091e060426040801020d0b0d03021b131404050c1806010315050904050705010305071b0f08071b050913050d0e030c10120605060f04091e0c0201090308 72
    0x21303261580301d61f80c4240c2050303407061000c5c0e41100c04000c0d00d21300445d41c802420043c94800c0c0056511041484140100c078401c0b201d080c4280491060200401c1c0d0000e8408201140140030b0501c0b0902c1c0000160710103206a11460380380e0402411004608500c4501c1d40034510580171a02c606d0014003c0051407107110003425203141a810000e40c0300c1d882500141c2e8001441101244016124404210043c40032074054aa9520103a810809542d05105081e888503940c41c20100085508084191030750701e524014000f804803803066818440001c007290320307159104034000b04c2500000801d10ce405000e00c248c5124030445400641240609003800d40e880c0d41c05000307003284600c2100190390f90807155911940620801078849803a841d07642860003010b00c03a4890741c0c4107e8a04110700242c94468118138010f00050251080502c802d40c10b5900791034000320007090b03486d5648510415925024101e00b9a54241103d42140c3c7e0380652086a021f4040d03541c00340d141c0d80b40c0b41002050034415 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 595216384 1250 595215134 595215193
    0x70311030607170415060b03041703070203091207081504050c0a06050304140106031506030507050d0215030a0f1404020907020a05030d0b060c0a0308010806130c09020f0c011409 78
    0x2088200f4420a4642c00b07541c030070f10641c40c1c1622210320410758421a07005070440e1400010000c1403205000720300364103c901101280e841c61551424480c005d449001ea000183d004600e0b00b0700c14060103038140152405030402008075602c040605062005410040c4c505542d0360103a051820030380d0403c0d4488005844c92a105c652840d204c5541e4550310b035412038102d40c0d00b035503101d00c0400042d8480d43d41c20b0000c1c0c41c1141c00f10b0f28904508065040001a60100d4422008c0320030500068444051005a000001c01401c0e201d50f182d10070380d8003410311141c2a0984074a00000c0751392a03a40d03814528080c41c0290f4070441140d40390703142030381e644090309006089580140303e00c06400035260092400ca01c4c01030110b40c03c048410440700d00e01410300744200e02081007400188030000c0c01f048925808091000400e07060403d41d1520100c52615001d4140941d4001540c0400d18050004503001e401020008018103007001d103150010340d805544031070160040c0a904c0d82c00d810079101e4039603128000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 595217634 1250 595216384 595216397
    0xc03120702031b030f0304030c05010e1b0f0102010b0f0103150f150908060613020d0222030218070503150d210206010506040b0f0903010e030d0e2a1e030a05070311030607 75
    0x1030b5102500c9a0070030302800c503205cbd034071001d400b8841d8200f8005400010300d08d18044614595400030401a50100783c0481d04581c9800081e000c1c580e58200c2c0b0680301c2d1000c0c02c0000346548074103002c2102000e1a0005001c6000c10f00000408240f0b80441c030a0b110816039400ca00d980d140c04900391107580a03941c0036070040490302e1105060800364028884501e000200500d00b6440c2801c418090364404124210200310001c1003096040034224503015210784d4000c082240340c82c60014009010151580c407400450120425140d2a03040c0710300040c0703412904060014120b030400140324080100d0301d40040c050340c4000155030420109441c1542c0603088068280541e1140322186908000441a415929030005100c0703c01c2c18401409000035002000c110428402442458811b000400c0b904c42c011081b91b41036403c1c00f044154880e80c104803003010300c50000c4c041641170090003c1c0000d5142c090307800781d00200100080c0c094103c03807145003100f501c0300265003010b8584008a6460020860 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 595218884 1250 595217634 595217641
    0x30c1a0105030d1d0d1506080111070f0c05090a05100902040803070b1506030c1306050f030106030513051e12040b031b070602070f150603170c03120702031b030f03 72
    0x5211030011404143c44c2c1c02229840041c001118601c1460081e0350008003400301000441843c0034480c050301e079000080c043c00c010300022224034480e2281c060201c5002c0c040110411150b411050010800140814960306000c0301d404000d01050341c4c0c000700020b007014005034030041c500a64046035861409035080542c10b407205813421900500000e01184040700e007041c0c0c0d0303813140d0196000d900c0342001d9035114182d05100030042042d68200000f0300c20240210140020500100e90560342d5500c0c02140649072024802ca5220040e030340108075006500080244107400c40c840f00501c03a888044440c0c05510f51800401c91049009580c0105400c00005d80752000310b441e20101020035a00b914905025034980c1001c031303006803008480e08046400b202040c402c0201300c119410000710390030406c251840daa003095000c4013440c4045810004503100e0207a42c002e10070340303090145030340c0c0e0b000c2d0524010340025240e50108a0025183ca00c1002030070302000c001096520001a030074440b440c50b01d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 595220134 1250 595218884 595218887
    0x1b0d09050d03030f020301140307090b0604091d0f0c100804050733020706030b0616060b0d081207020d020703030f030f2a1b050a08130503060103030c1a0105030d 71
    0x1444242c042c15241d550018044029200840c020080c40c0c403604824254101014246411507000c0303502e417801c040c240d131000d03a10035044800700c0d20803840004e650042c48000a19030b100309280340446006083c040e000c900070100d0b000e4001e03c0121000300c060a0740b103c041e1114030050790301902d150b1103014180004004205000301c41c180309034180490070142c40500184039030021080005030401c1d9002c00c0703556050f015030064000c08540980c189060303050101d542050003080641050b8617404401420386940c59400003407600072111a40c1c4143d140306224400300151852401403240e0502100f5a52000c100329050760741c950755819103452101c6d012006040b0808580d84090707943d0644202d03201901c00c0c1a00041c59020a02c1102d151040b009803180000e50000d810021074165014002140451011003c681c0424480d440300d4480c00401171340d1075503070032164241c17141b170001109150f0499200c0880d01d1180301c018510003000100086044400e04c90950103500001d107081456 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 595221384 1250 595220134 595220149
    0x213090f060c020f16030507090204051e061e0405090f0f0412020c1e0406060504060504120c0509010e0a0b010513050f04150f03021801120201050f0c01111b0d0905 72
    0x41c0b059104681ca0826620350b00340c1003400c60060800c0d02d00c2444c504004100043c441c0c0c4008102c22903003141003516010100b421890350010700340316041f020140c081283e4070321069810b00c02c5a801c15030460811844007030907991040c01920700c9203100302d00290450213101ca1362480790b8904900400d1544882d039410050002d240d1415080d17001d14100343d2034949800b1101800004003a06034111655110b05010480700103410002c1040350800003403021a402c00c08441c2203030030a800911080f076250606080002054100c01c0c8c3c0701c4103002c0001540042401c41c6c500803001c01508012a08000c001076450340308185400030071070400901004240b031b10100c4000010005400403a0042d020041040d11a081c1d411a403814116108203200b541444c03c90f0344459143c0e00007480f503a505040c030b035003c1101030b42d200904005000400155000d012000e0301c1d0114410300090112110002d0420040c3d01700303102d403445d40341040008110040700060811428143d68507041d50541c01c04007400504d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 595222634 1250 595221384 595221401
    0x702010806102a08030a0506040c0c0b0c0a02030405151213050705120f0703030815010203030408040b03070903120302030114100806011232090d02100f090b130213090f06 75
    0x4010f0100e00d007004120903500841c4030300800e4900042c90b1030100200402c927200c203c002d2041004600f40c1c50300051100f204640c01c4a0362802090320340781513040072880c41c8a60341000e83c01000c1d039a02e1010034000308010306107281c0c241c3da1480d00c07036492103520703444244002400380c0107902417441007000b41852509403003904041816902006400755600349040c00701c0e07000b00c00160520081120400340c1c00ca692100350000d202071440c44c00c20341c0310406140224051554100700000220b41d456003d407900070011540039881c0b018272402450b015000350403d2041646d00a1940c60000305841c10180642001041e52107405a41e190400111075025007441c003203a1031070340c690310345a600d940380760500f20802d1044a800c1804091011041e11480040d003031501c258460303444074020a80206000b81000300c0607800181c1140074901810280908a0000c0c0c00c0300d48000900104240139010840094001d48002483c40a42e2403400200e0f01000780c0503104140141608001a8454000660 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 595223884 1250 595222634 595222697
    0x60402090a0f091a060c030427090f051221060d0b0103080306010e1017060f120106091805070308070206040e24030c0319020f0a150305061e01111f02070201080610 72
    0x700c080390041c084c9d003200d400b008144d40d00a0780f0040070342000320410000c0c8038003d815111500385090003580050bc6480d0820a18030030010400150207502c43c50760714051603412400e60142940c0d28146009158002d4644500052001011103030030f00302a0b100740800015030f6900c100c1c0c01e0080c0490514000c010700f03120740c0191030380c0400c8800d650b0000523444448c941c00c00040c00610f82503550b0221801104400c05d180c07180e800680c085a4041100b204407500400202c0d40c0300046d200041d09489903400400100000600340110004c1c40d00b501d00e41e942001d0030384800400888209070f61840104c9109603d64000c00300c0280c07074090000500c42c03140c80542130341180b40781c00c00040c07101c403400d030040040328801c0b4117070a60055060290a07003208081e00c0010840108a10041e209002080748a051141c116030105040204010407011006c903410040311a100c2d80142501941c002c0c0816400203ca43d004a1a50714108070003441d40c0010303807504464110669210a80b500da0520044c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 595225134 1250 595223884 595223939
    0xe070807020f030d0c1b0f03270611060f04050303071404030204020328020315010815040c020d02100608030d0c020f070909060c0f0206060402090a0f091a060c0304 72
    0x2044444100050601007401078008242419170002c01081580b20300b4801083d2285020b0b034201044030074981c3d100d003030b030146003440c203100750203004101400350100001803166802c0303070000340142e102d61a51500c00c108400d6038410340714401c01c14868107055070302030b00680041001c654045d01074212245900604000e007420716503030b41c000904980044074681d034807800c28040d2011000949240051002c2c9102d021425411300c01c0c0f40031041800101c405061040300404654202c450781484803007403100a00611218014010081d221075400440d90050310a002402c142c0c00c0c0c040c01040c0603203801c640107500344032000c0d00c3c0c08003030b009039451481540148180109030075004d001f0007003e02500c41011428040520b005d000b00c60f04114000c0070072005e460040d01e682e50101c2c1164020508440c0543c80e076100000140b600403580d405078175080c2c0500400962142c03250480d01f408490143c0030465001d129041c810340c0d2041c11044421900200014401c2034841d0340682d00070b07841a030190 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 595226384 1250 595225134 595225153
    0x30c021b0a0e0a02090102071205070501030506010c0203011805010c050702090c070204200c07060311160c080a0302161442130f14040e0c0d080307090803040e07080702 74
    0x1d12089803d4903249003140d000a9146040c2d601003049400908100003654881030140d202d47d1b46888583c01410304154880c000318410340c1c41100000740141e0001c0c001c011380e100540210411101c8481e00300e13090350a00058152860180084d1201641c010b4100900d5550f84504007070b10382e100c1102280e01907900c0c00a10b04100c1c68502c420350341d8002568150b55202c0d100c04540c80c0c901e503070b400f520030181003c0b0745801e1002840203842d1100c005a05442141c1440d03c3d00d0340030300300f05402c0010148030f00908101816800074542d400359080003a164116038486250102c3c80c5004142d681c0c200e0f00511024000806581a0904040a00d0503400c48402c4403a201d000da1031603807200890804000c20030040e0401154008001404040c101920f018980340c8408620219509064440c40d40c4110362200c41105018050700e40b01c0003440207121400b2071400c05000e030000e445240000d241c000c804200d003203001040740c0a40d4902d805032081c40e035500804442421004258030114003441840b03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 595227634 1250 595226384 595226399
    0x2403030f0a080403080901060b0405060306130e01060509010e0405060606031f0f061701180209030f0106030602071e0302120c16030c0614130306050c04030b0103080702040606030c021b0a 82
    0x5480742000e0780c0c2e509945810242002442a14090316803001c40c1d03d0440208900d0283c002120700300c44041c0c903000d460340d540380b0007d07a810702600c22485489003007808a90807904190303c44000d44e41c1c210307061100760740c80780c0c4940550102100c00400c0c1ea4446001b040142c68814059a4040c252251201300803404e9400003c803000c1c154030118100050710020300c007140d0040808421000e101100100700d40c50a0380080e000c111080e605a14030350b00040d400c406440502000080c0c020f80300c003e101981ea07a00d0030380300940c8501402c4c0c0300b190700c4100b84800300c041d690001040c41d400d5802014510813004401c441944111103d084501c00c0041e0a02c1d0001072124240043d801a944503004510302000a005c544c02030181d0311190310204150164403002008000950f9000f00c40042e00c1c3d40d410354074644610650f00f0143c07040c2c03510800003041110130030003010810301c01d84003404030719503815069068910120324500036800980b1502201004040b40a0680b10003c040020041c0d54145 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 595228884 1250 595227634 595227637
    0x606060203070308240f03010f020c06040c0f0602070501050904020c240a0903170c090d0c031a010513151a07021f050f09030a080d050f0f2403030f 65
    0x1140560800b00e86081410b80107226590700201500358020f15039100e54046425054041001d482002100d000178842d072000d40c0318880902c5903201c00c5546000030f0282d90f9480c0701c102c604880d1000e030920b010809000b0850b035001161794036002032410300c2c1401d0056a0326040f1104480d04140d081c048450700d54030400604c00611502000b00d04140c0400c034104900305c9000f02542169410502d071500003070352244c2644981c000300e6203841c425407503003030340350b480c5201e40e94000740c0c407048014406040c4041644201c003160710601300b8aa8158081043d0f521030380e401d2040c0750784101840200c40101c10a9000041070010303079020b03084642e03100d04840922880d0b90881003200751000c164001107080841400b0400604551030005481d0689002040351081041210382050013180c86030a9482c100050a00c540c2c2c8000070303907201c0400440f09002094129041e50040b025080403541c5034809002c0f0034004e11246401804107400e6044c100440380c4000c40721601484100a0b05081841000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 595230134 1250 595228884 595228889
    0x903070b131b121407050109090213030f0b070809060c0304030c060b06130e13020330040924080d050c0c060301080c21061b0903100f1808030703050c070606 69
    0x948010811480d41004d0704103032031808050005610441040c86640c1e04003c0440403103c0d000310242c0d0b40e03a1031641c1039207801081d0740010300a0042d1088a0100a076003080180300300c82580d940001503440e05003880c0e483c00142c07a1582a42001c002040c0420711858072181442d000c2c0030081622103014001c5440d6a001c0b90080e01000443c0300c1c1448003401752103032190005042900c603c011b40c03036900000d40311011030035807001c5045c99101001c82014155440c05901241f0100c1c15101d07561409114050080d400ca0b508004500003905148110341c2401407064072070702c500500d0402e81794a002e44159100c40305500d00c81c0310f94681c5d400e49945010003035010380b0040c805840480e0014040c0003009640603041001c48059200300b24004100149090b4082692070b20001160f0b5440190401c520a9080460709809200074034001c1040c9904030380c641901074442001345c40211103030301d00c8503400350f038004028207002c00110b0809882174002a0704071922010b082e1400805640d0041141c01a5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 595231384 1250 595230134 595230149
    0x1061e110d0e0406080a0506010608090a1e02010305010905100b03070e090a020a1701140409030302090405070801060905150f0a031512061d033405010e060903070b131b 74
    0x80301060041c203184c0507803801401c000000388071103420740d9640381c4c0b140703014040c000800c45220000b5201a904100c440b489580110003221a80030702903030b601c107081400d030003039001ca81840000221682a0301c07802d807050024117090b64503607062185800a50744040c0c45641004030311050f02c01259241601031b40240360241c1c00590301c210180300584410f6152190600381030210300100b0002d452040101000e00080b900061060200e1034158028010300c0030041d08036250400f0407622940007076969059405a40714564020340e103000300680d056041d50008500481804043c03841f811000180100301518103000c135440340825081c40d090000c07540000c49180d1071501c030702d05002c524816001b906015214846481515008030351f40d80c400c00240035031050446400ea4000c0001e889184801910001245850405805c0450280a0301c85100700fa90082e41c1c0030031040240002210f240c16440b828807100c95561407070340040c80c0503055094640c0303031900c003100c809900c1c070406500242189 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 595232634 1250 595231384 595231397
    0xf06270a1a03180f0d050a02120a230301080c092703070b01061b031206030605010f03030311091f0e15030901050a200d0f020403080901021501061e110d 67
    0x10f24030080e1907508505810b022608824100840c000001ca480d1007038407283c2c1404c590361011701c0c204a16254040c811071040c04008100201720320390080c881120040107d030113510740000c05440342640c0c44203101d07004c01a8005008400c0354140010702c5a03004107942d84400307100900c00c9900f00000b0403808036651a400000e4800e042041810407280903001c1c07440c10701481d42800c0d0740740303c08a940b00c0d0040e05000b04e044815541e0711b1207400150195030b20140a1000b540d40c8d0400014460082c00120003103800c2440c804600d00701c000c04d4440780350f0010302e82e00c2e540c03203c1000e0684c0320807003201c1e180070030140c9407001c0d410381c881da2a83e0780c043d00548003040d601d15082032441d00b1640b0207804111028105134016024241118034411071540502c3c0d402d81d1101005403460043c030b02070300780b420002c0c0007003000014003281e10040c0803824005e800350f0340703000100034070072a40c07800901031000410714545c031b6030844510441c0000880e0025041000102006580b001d151044500740700c03002880 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 595233884 1250 595232634 595232641
    0x20315040f021002010e0c220c0e0310180b0601021e060402310507031d010204050f011812030c060e0105060a0602011a0603040201031503060b0f06270a1a03 69
    0x10f10034080543c0100510080003030300d000ba058540c942d50050616407052100c0614070000082c074115103682840c1c0c4100400042c01140d0303000d4070780c10310f04021520a02889140c1ca10040786406603009648101c0c60003810a00c2c1c558460f0b040e2000500954114403c288200c18070a01c515412952007286a005101c00e14007031040014400c8484440e032501709814015040c031a032a010303120703289900c1820218107075980080c00c800404400e0f40007480188076020003040d10318194000c1082e60020b841d04055a62180c006403506194102c42200800382000100080013880e03000c08083c602c01d1034044402803444e1662425505902c1240ba0240d54803014071519107001c0011a00070034090000f0700c0000040502d5174403140b45c41e500030340101030001c0003404581c031079404000001c0c0d8810072460340390380741d0612400600e040341506000354000300100480345404001e0ba40341000c10390714880240400000c0503070354817450f0707032542e080741040340c000c149800b59090a441c2e40d0306c981c043ea070b03d038034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 595235134 1250 595233884 595233889
    0xb040302090c040815041704030b0103051b0105040603090303020904090803070f0318030c110603010305060919020a1809020a090c031107121b0c060507050f0106060813020315040f02 80
    0x1401e0500b050b407003000104072000740441d4682c1903070103165940302a0398590810300c1c20840c49030402d245c001c1f0009008030800c011030812505070307070280c2c0c03c50b101101e65010641001d45041d82c0f8a02141d028441000241e21a410181516209141c0503081090030000f180030703903519500443e0010008030410941c41d80c00044502200d001c3d14080c4280507002200b044103643c0d4580190401c120030403408240242445044038009014081d20750360343c0d403414156100c031303419107a1122a01a8100c87e0760912194055100041d80082814860f24170b8000d4a40240c01d0803101425256110f0b1100000760392081030b20300041035030f500d01142011640710b000f03084800010381c400f1000350600410f80410485a480180c01c1c0c21400c010340007000100e2541d1004100c004000c2c46400c0c07000010550fa9803083c060210507201ba411200c4600d0b1141d0030600707881550080c036000400200000b01c1a03480c42d4032401c5000d0000d0250b8103020114551000002021103013502c103030060034000411030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 595236384 1250 595235134 595235149
    0xb03061602100b01050d1a0325140307182904060f150336211e090b03010b220b090d030306052206090b0a051203130b040302 55
    0xb105856082180c101200006056801b803881c3c144840c9036582c10280e01e40061441e13080c0138080c02012603071900d0030819080064922140c811013103050031000011010110450b00340002801800341c4a46c60400040d419076101008c6a002b45d6510780039a40c00c103c0004030360580c0c2850303184403002c107204007605000581301f41e070b44040314619070b440742081611001d42e18017590400e203103004680c2c544000c0c48031509180d049500043e103c500e01e20202c40c16403e2406c4059a44101c400d000003010340c2003081514980d03141c4000c00b0400c40440030440c102d1900c0d21200c0d86034282000b41c030950301d8000200060700b00f60002001c1c1c1c64005070f00c01c1c0500e41c1403012200500e01c07100715240e4509240120041e401102e408a0103503030000c00e040c04050190b080038001d0000900000c030920342d100e8604c0d0b0100f1038040d00200d1036103000000314800b42d10340189484807802402c04a0110710303081c2032124600340505030b110709000a00000c5100d00b8075003030343e000811500411580761811030041100341d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 595237634 1250 595236384 595236403
    0x30c34140708030708040e041a0c091e090f0903131e0f080a080a2c09060f0d080c120a09030501060b070308010302011101060b0f1308070602031c0b03061602 69
    0x50394002d10203800020f038540100c3d01507c850110302241600c86140800019010850300003000210004020051080d50040d00d00c80305e0440720417941160300c2a40e841840c6201070340c2a080f5990100141007864540c030140c3e0043e440e0701c100c82c80c02d017401d43c01c2203900207035402207038200e40300d000c500e024101241c1d0380d040540000348402505514000d8400c1d59559001c000401000d03000c200b018855020301400030200021100440500c503074140000452032250100ea0304c10024100899510f0402c2c003800ca1b040320300641222900004ca80300c0c0c1d00d10b50440401130301c841c8104200448110701100107080d6000c07813a2200c001d01c3e415071030301d542903454940045070310b901c05005480200b40c0c01129141101d40a08081e0300c2c02400c8038445014100035001254181d05c00030300611007450000c01445076000101000c4500e9031103181041d181c1c07a4511079000180d0003440640307083c1c03440380500b00004021103800110350384690017203414010203c4801d81c41170051115001788580600c4040d12 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 595238884 1250 595237634 595237649
    0x21080d090311062806150302040e0a14010b09060c030d0b10020312071101090b0411040f020903100b060c0f0616020c0d08090117010e01050312030c341407 68
    0x100c0d03240c0480d013038080e00491883e030142e1400000019400300d102e80d022002a28005075150000e600000303001c1d000c0c0d072144c81030b05001e110040004120319018841c0b00c3d40000c0010343c9080d1a4a80081c01415400041c09281d1022040050000007101000101744000d841da001080d07054070101000803058950b001c4d5025500100400380011440700001d641c010350b41e0038402401c0540c050f9240c01000c0c8004020000400d50080c00140400900190a0000b0440f401e010240384510884140e0261020043c0c040d800410000c5407580f4030b801c501e020010207450a1b08290406902507d0310a0f0640c940207960048401d1081c00e10400071206848e0580c1d000401c600703000c50000c01c0320701c1c10145000d4285000400d8642c0b1581c4a8540c0c030318120245e6003480307041d50311205040c615120a100c3c0501c43c0c41802a010100d403480c0054074415065440701c10308280c01d5190740d268510084001034410000102540265a00e1450b0200c445008450355158203080c02c601c0c600c1c20b030598000a1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 595240134 1250 595238884 595238893
    0x17010e070608090d1817100b0415090c1b030504442a0a06090803070b0604021c1a0418030c11030712050606040204030c21080d090311 59
    0x24400020b1861032542c0780c5d01e46200c01109003400091068130b5038120764030b201e10303503010503411800015500350350201244003000031814180800c800c80709400464041004542c604000d581d0542c0d0203030403c1e0116083c04000c0c01d1160400e800b41c51049034040f804154042001d20004042c10159910f0700c0d503000c0b1150b40090490241100d98040f1000b0f002403040e618030a41c4039041c1030258542c05044680365200c101803200e090b101102e0310b9058640100c1e100da80004000d88112800300c1183c800d4000385141450580b12101040340c0180010f402ca50200080130551001c43e504c2c503041600c074840010041070f40c0c049081146032420116204a040218011419085483d120b160320f5141c2040c00325140d407481c0c005461064510044c0d4580074085c00064040301d1044c000d4141d921580a9408030350321081004102d00980c0005007900b10709a10500000c105088802c4030040d59030300c503404100065a800c0316a41c000340c0303481ca441d40c40d808914101504043c282680d03003800c1c000341 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 595241384 1250 595240134 595240141
    0x1109040c0302061e0a26041e0302160b0d050a05060319020d0204050106020a2f1017071e08090a0206090a03050a03080f0a05040c09110417010e070608 66
    0x200c220000d5800040c0c030401e0002810440d84d0103440700391480d48220428a900d4602d01034000d4240c40089000600d041508564500400c0c01c10b0340e803901c104c0d441240144a5520a00716680c0d00c40c026000b00c00358899090a15410a55541d12200038102d10300f901d40d541e1480b51544050b600701410b00c501450608091140c26500030a10044514901c038400d05240800d00020b40440e4404002a4001d46800c0022802c10303800302c1c40c0c4da0454025804007030543c0750211407081c80780680c0720245003170100c517540e0f10140c54900c80d01c0050440703a06c0c04981054120103807407d201030990303031100840c64014005158024095400e00240580c0c1080041c40c0340480300b80d41c0301c1080800c02817103a90001083c540c650b54a80c1088065a00407049030302c00105c924014000ba44142ca9402203001c5100001d40302d508540111885158400381d10304480340b13000c0d04840540b040c404101c0140000b804085205a512005110700d01041c40010170245c0e6a101701e00d0400c99541c02100400100380c040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 595242634 1250 595241384 595241393
    0x2120a060b1603030b0105090d060204030201140408071e231005040518041b080c0f0405070e01080a0b061612020303060a1701060b0c0a060b03061e06060c1504110904 73
    0x19042c98a82505000c00c0b29009a0f0040303d4500c16441c0096001d0b441c414944c05206440c2c3c080c2065074400c0c0c8801e1948085001080c0c4113000707600ca10081607114102c14080f0240c0005602d6104d228414880d48480d1185481c040113540d02482d07202d22a4248a021010302d08801400700b102c80d00d051180c0b500d802d000100d80e000c0c40c0b0030082e20350b0038410404039040107a501202c200000115803082282500e494241d41c0b030300d100b0560240704603a0b28a9206441c50b03d40300716170040e5170701d407a051203100c1542c1c010b5552080040100300510356030109100142c840000030720b043d42c070314240c603c4400d40925000d1501d8000050301d108650080c01084007036240c010110003510070031140419400c040d0b9214501400c0319802c00d1400300c078041440d140000c4005105103499114423001d00004801409043e0340d80411130740d42c4007000102c01c0303d03002c1c5590341081907008080a4021403924030185034070703444c0058055402c00b80508040c20001846550042c80c0501202102e07242d01c21f04080c3c45d07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 595243884 1250 595242634 595242667
    0x40b10171207020a03020619030f0606050a0804020103091e020301060f06140f04033305060306190b060a050a18150f0c0204091b09090507032402120a060b 68
    0x107045250001002e409541d1803034021001154000c040c80e40c3d801045c000d481d02143d1245a0f034012070706004ad020071004042c0288405c0d110140c1e6070500f07250005000700c3d0103460241c4160706044c5d075502d002c4041101c005c0058100d0b0010719485880d8106441814210f81480c1d120681e460300051042c0b05e01a88121100c2c440b128150aa1b5210140d09410f116607205561008210111180c0c85084050260809043ea4500000f00001003c1d581180c00150b80d01100d209506403c050002034007001c50007500c0030001c00400c40011420390301c20100b40c00354000d11020000c510b020400500c400c0c2c1c400c2405548501e408807c080352858120040d0350102140b295200b07126445149400c1c85124403940c20380c040c1c00801c1842440004d05103807210310032460101445810f121404644000310340a00030b00c01c2e0380070b401080a0303850740c0c4614105a20140114a080d80c082c5050a040183c0380054202180000514812406e0148000d012522160701507062104240003a0508808220703 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 595245134 1250 595243884 595243903
    0x60e120c1209130c20060f07050d02040f080102032a0a1409040c0c0b22080903011b1e110d0e060408160f0509060901032603040b1017 59
    0x2a066865050100000c3c036031040e01c240002210303103000e04511341903501800b038180c4404001c1c8140030010410304041c0c0c8620301180c1b1036071290f0301c00d801704509502c1140146100d043e0000014103240c2c41c3c4410201c6800300d54030a0803e0303074020041c003003061900b4040401240141c0807a032102662449084d8013801455528820701505035015424945018120741d0a10700c002c00c00c1040d0350300c4407001382218119940682d000d5003903a000624100300345800c0c031403d008464070740840c402c0c1d6658050580e4072034490150035540305c0c1d4403880c00701d0b0740c2103040700c440610b900c51803600c80038450759644813044907601c641005249548c0c8003184401080314100c2009501c0c00c0e0303010242e15408240c06110f507602c015107601c5008801c030800e180c103955030302c1510402001c01d484180c0c1c540c10881030700020f551855202105100410014080c4103c0a00c4030f0360307890800413aa00e010310540e8650300112800d8440425050030072041600728903c9600cd0403502039890340307031801e00c6003040d9262081c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 595246384 1250 595245134 595245163
    0x705060109110325230d0501060e061b0c180f0c0403020609040e0a080307030c02100203072001060b0d0e19030923030709021905070201171f03060e120c 67
    0x503402000d0052065245e0130f03008103032841c0380740b40d414500904200ca07030042c14004100380ca414000314186204a42448802c1001080700741081d6076041c42e40300150034001c0c5101544101e00e180c00c43c0380c03240c8429440030b81d03c0100745052894040180c2900d80c1004002d08d501d0321080009200507070359001a01e4503880181c5002401d444540c0d045480c00c001d8810203441000081b0400c8038a81e45500071103001c2c05954282c0e1b510401c9038202034243d003c20b451038004038290031070341401041c83e41d10350104900c0300c400110703049503034003030000480e400f50321000c102a07140c0d40b02c400401d10800c054201007500c02403c07aa0f100341d079100185100420b00512001d00d4034640c0081e400c107802003030307010071210040517641160365410309400250301ca0715050641c407882001c04c850481c00380c010303038060035010385450030300c0c50300b0003500d582544006200400500020101600b0200303e0981e4078040c503c01c00c0f00050350b005200f8414917115aa800120552004110030b0071104004500c031240c2c1d1448 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 595247634 1250 595246384 595246441
    0x914060a03090212070320010804080405090405120408150705030f010e15130b510a03050a0b0409230102090306240d11010c140307050601091103 64
    0x2d0b02c0000c1c05608202d108403502e200b10351011082c05a605072403500e45807180352220104981c0d10042d1000350742214054071041040c17004100034100701d504154000d10400941d503261000c0c1401c0340e0303981c1198115803103035800a0211002002110b048503080541424000e0447c505200b5456040e441406950741a880f14004503407900d01119a5001c4003c00414130381c0b5440c840c00034640141136400c02c8601c81c01d590000a546049046540000913240c84513200c0c5022180b070040911202c0c103140340303051100131440d0b4080340a1000c09048500c3d6039540200d0706007032000c003400689058407001885249003402c0c110000d200b80295051a025140900c441255010304543c024001c041c3c0183d0103001e2001040050300b41400d010180d09c1d00150180550190076040c04031006c0d85d410000c1184e541a035144800e0740c06904070f50000e600c52211411804180a002c038156000700404031303150b80c095801801404924081c01c2101e90f00d41525a0662901150150b8841c1800720f005054541 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 595248884 1250 595247634 595247651
    0x60e0301050f01081b0a0f03030c020306070507033f02120f060f040506150403120311130306150306231602070b030406021324020106080c010f0c050d0f0914060a03 72
    0x11b4002202c0001d04c20480342c4016280d0300c1c10301070001c41a984049100b03015407400500300e80c0c020030903901555007507035406850088921141c0c1c00300400b0118040d05c1401300b03141e817150a0709210b40031f101d115050b90150301c0fa050b81d018002d48203000781c420036000001070304100050f26580c5d130704402003404031008030311074641101160441600018181c00c0c05000100072092044280000d44080c495030740812007000c648520004a0188c1d030603600500501382401c002041e850340110f4204d500b038501441ea50703562a65010101c900010850128043c0b00d003d0141018017013240550108211990300b908400180009403503600038000c250718008040081001d100c000e5042d1401c1c0d40402124181903911034906c120913401c1030352000600184c581c0112100c61060042108655501e030081400700c0884005488030305282c80700008111119840c0c3c5d000c0f8604004038803a034441c076196495081c020200040622103280c00030f0381c1411003000554030b1741d290b00e4110340c0603541c189000545c00c007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 595250134 1250 595248884 595248889
    0xc100e041e05040809310b06121f050603060604170a060222050f03060402090a0b030105150a080d08011a07080703030f0f14010b07060b0307060e0301050f01081b 71
    0x1d25110500a01d40703420100410040800024000010102c80c000f000044400c003110403004000660103840448444085940c541e58120441c1010010550790420313a43ea00c0115885000f101c480c08500c1b00c618410403000c0350070700d5030809402d003619458614546400410301c2e901c81d52280100344078a81924403404482401402c940580c0614150365130610030701801c251702540c0071000500012454006818a4008007501780000054083c0c012a52541c003040019500200007003056900c81160f142180c0c1c1c07e2240c18802c83c035440000c10411654020702880b022282c000444c3c2c0d42c01600c0e1480700c290070100c41c40c111000ca50401c6071168804000c5000c602403050010041c0602041a40401d6007540000da010b641a82d01003040c8c5003030740c0300802941c0e40c03864202518440000140250604d5400404400f8040c200103d81252101c0100e4501802c95100d0400101c0b0001d8000840c642800b41d65048526280502d40650400140e182c0b20402d0350034665019600f0b1100080d2034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 595251384 1250 595250134 595250171
    0xb030a1109060307080d050421030c060b010e0d060203040501111303262a0d1413080624010203030420130e01020714060f0c0304320c100e04 62
    0x206454030a4801b00243c400024095800c103014121000c3d403846d09103010301302040d0340241030580581e104008080141c131841d0003403041210590400134003080d40da10507242d012104164030321440005070f50b0318250401d00d085440b010030555042c081000019440c04e910607a11050300d8202d00c01d1220b800f500200083d10010324900824400f1010441d5038922120310013031112030f0701c034140e1540300c903104c1a102500c941400700e2003004100c4808100c0c2c010204440941600c20305c0c2000c0040e25134440c4141c62030400111800b078a141c41c0e6002000071071042e00c00d03043ca040300a00055065080550780c8101100c0c00c0b40655001c500b0303071401c0c01070309e07680c0e401003024083d8130000412901303461414442c041d43c030a0740140c501d003102903c035401030b80000449510481010315232007500e4681a40c50302c01c0e40e0000e802600e03142e20010110070103c040c1cac00401c2c1d1030240c411018516007104c0c50345e94105103c60401c684554081549000c0f015002422902e40c103100b00c03000280040440c0141000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 595252634 1250 595251384 595251389
    0x1009063c09030b040b04060c0801030203120903030f07110114040e0402060304050c0405040b090c0a14010f050f040602010b0a080105240a030f140105100f091e0c0806040b030a1109060307 82
    0x443e801e000d02044c010544110390080340647c40500c0950303241d80781a1071000082c071000790907610086480141e58001000361129000041c03c0d649031000703d03000b42c0c0d41138000010a8551150070810320b8442c1da0001644441404170702002c070704041c60546511074016000f00081d002e0180000080c0030082c052200d11841031004000700070a041c281040702c100da40481c1c0314005482900e500340e010345001c406100c11510383c92a00a04d090f000b80044030b4038140107011209001c0705114a00c01400e150004e08042d0801e0781c000102c034010314040084004165101c0d00c201e9144c0400d000c0d565050f0a1001503599140006030802c100d04c1c400300b00344c8942c940c00a803035420901d030103400b040001122000b04403000c0009000d6a141c012400f10030644622640300d01c0d0a1640040040585c0e0760807444401c68a81c514007000c07500241c03220103131034000b50200b0028184904010051400703101d00401e484080d001024450000e0f074850401c6584078409901c2046176400251541d034041000101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 595253884 1250 595252634 595252643
    0x5101b0b010315110d1805060c130603060501120b1504080303190c091a190e10021b04021b0106060f020c04051915051009063c0903 58
    0x586004a08003059094001c2c00215001115108960703900a030a00403640800040d0020340e00d024030710740100c002400360413002c8a460340c1242c0c1207030208906102c0340b403043e454600e825594041040b5406060302198000c5001c3c90b107011014072540e640450711801100a6010018048111600003240c9249032a060075440d000002c020840241c080069070040032040c956400915840c0e54000680343c841048000048004008101d10181810f000103000f401072078103458152001c00c0b40c110603180d8100703800880c3d000103100183d410040c215481c458880c0c03014290003c174801c0b0920403c2c5c5805225481640c02042c824022010001a80340607036441c4000c1015aa603a00c1c040c2c0419146900320025009032083c040c0107041c0b42c002c2512038880644902d0310f0080c8003003464020040403603400080281d00f9404106622640c010b1440185140c664040062514100a16101d0190404060711081d60001000c0740100001d8250410b08914510a05030b080c050484596045a00290 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 595255134 1250 595253884 595253927
    0x1d0a06030c0b040302030105010b0408030307200105010303030b1f0206060103020c03190201050103020a120312091a07050417010608030306101704150608030918060109050901030501022805040510 86
    0x71019103200c001c0085038802d4000b401107170b80cac4220142d0301c3c1c0610b00c11500150000c00014007030600c10200f01310b81800d8520004452031030203940c00d0071100b090304204c02180c0e070381c80810428540450110b00c1d02d21f100040c004440101d00d4000d484010140c811030501d42c01003181e200c2c2810171710070340d01110f202d00d07504002074203030780720003406000284003c0e4014035050401041a0014460071015a6010346403240b1060b0300b210500020042c400040d01c499290440200c814148130102c94002c05d020b6807401d44a6003401308184500c0c1d1040d0404059a240100810100c1030100940344d10040840b20003480450400f030a40b52800c0001c8000869256142040200600c030042040d0031803102104008054403024866030302d101b0200b10b542e09c0744000030406c034850100540707180d0224062618040480d038400224030601001e8000319007030b0b500400c440401242058000e4004003003c03484084039405594007405620941c02050701880990000141e42406094004000708183c00c024 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 595256384 1250 595255134 595255139
    0x19060311040e0411041d0303220b0406050906090a050a120215010906090b090f0a0b0f032a0a05060d020304080f041215060614090a05040c1d0a1d0a06030c 68
    0x1034143d40f02c400718240706500e00b4006031100300d18040175242d1b60b10110300440c07640d01c6112800b055403c10102d000388001d000c83c08032000804082d5401d005a00c42d44012440c1e00703214a81c1c40c01c000b0001d000314240c0d807100001e44046100000c6102030250405840e410412420504a08207035031010740300034841042000150941c00c5510050480e500c0140801900300364408000d9504000c0e00c07407a01026964022501964580d801b0200080c03005180800c552803d074046410015004110004880c45c04001d403140c0e04074123201880c40f50125000c0c40014103020006800d801001c240f101e07100d5000c1b002404002c031312421a8260b41c4002c10b21030b01c0c0c5130381c0c804820300034901500440f020001c01014009101450042c1d000380c41c001e407100c0c92652201d40c03210b030154000d284599030007144c0e8000000e003510789201da02c60340481540c81d150301019152140d41d1700c404030120107004c1d1003070b10000c000030401d160340300d00001c860130020440742e00c0310500303400a001c550b0000341c05030b160344100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 595257634 1250 595256384 595256393
    0x91a0112110303030103110103051911090108060a0e07050307020a020307120210090e0a110f03010b2109060403030c031407030e010629030624130519060311040e04 72
    0x10403000c03803082103a030194020032014141c4074042880010304500102452400c9907000741c00035940f260695140e10341648101d0340e480c5c1510030041444804a03400075010803035580c0306003020350103001602c00a070403a10b0552940000340e001019142001000301c00b080d0814400d200c01d284494004003120103403511011040119541c4040c100d12868480d001c500e100c6001d17400e554100c415a44059140b0b90320f203000c40015050001450341503d0701003242c84615080703100070b94060001400c010351243c110a50048080e2003031050b440c40d082203941000940c00707002610130b50080c0e042c500031a0100303111310103901419082012624100203071040042c10343e803541c48903207030040c424001c0c072840f40d81d2880700488080c001c43c0b0258440b1035803040218030100e070f00151b4015070040e003a5900004003c081074914400da80300421340d1040004c2000003c800b10707120001400040380c40c41d4000003480c01640d13442c0300e02c0c41000c0500d03072200303941040054030105403001841301030303021001e61400703160 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 595258884 1250 595257634 595257659
    0x612040309091404050a08130e090102031006020f0d210f050702070f0302010e04020f0909130b0c0906030a050c1903050603070b07030903080904150b0703091406040306091a01 77
    0x254542d05880c0594205800c1d0f40d512155004640060140040d0074980c0c07030b145c0030303503200d4200713001e408101c0380001442c012070030082481008044d00058690411658003075412081d42d01401c1117520a510032480c2c40d0010400312803080c0c40d8104645c0d828009166048403003240c40800101c1860710384042840e8403280c008600c03440456083c1d88000703486402c691601d4805000107400100f2200d40d0a42600b0140e00628120364034004017814140c10900180b10303130038105c035810541400d0750042c000b000040300c4050307004922010054204110030000c01c010f400002d01440c25a611a008117044810b950308171035009842d420400040301010f5005405408151101030081c0305412001561080d007209840b1403036490741e540b01d012403850f1105001c0e504a401f4159106a03528501440710141170071407002001c001e1441900c44415080240207c3c103954807078511080c1001c43c8079400d589100803035055980c0040001842c03400742c01c00c00020030026058000e807035510000818221010070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 595260134 1250 595258884 595258889
    0xd03030f050903030c1c060302030613030f030506010c030f090b13030b01090b0d02012015010303180f0b071b031a09010209100f020f0a081b01060e0406020304020612040309 76
    0x2409503440d54001250340c1d200c21a60f90170307810014420700013603a0702d001c1510720030380030800c010400580702c4c0c0009040540540f6040300780c10342566100205a04800303441d10b0314003281400c1025103440c10020303140d210500801020400c2000200417040c0c018a014009003c603210015100c9008c501714650b01140307808141c804003540e20001a40704c1c20f83c040e00088a40280c03058400100d00d90064072401d07090704001b0715145400c03c0100542208201c0c0180e0200e002400c1c1c45c855240d4240503021814101544080c40c030300035014004c640788640150116000c1c0c6017081e0b660080c50405141c41035500b14a01c016940041002062008003210301c421900341c452082c0d003d03102c04005500301d118681c12036400410001110a005000318610001303100103006981c0a0049880c07803078240305031082c085800e00004100d0305042410440c0301609055490020081ca50412108281c10342c80140000c01e21500003000408544030786050311511000c54032841110f051925010f4880c2100d070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 595261384 1250 595260134 595260161
    0x14090318040b1c082701030b04050915180601080a0c05030a03080c0703121b0f0507080304140c03030f0c0c01050f0d0b031e0703021503010b0f13050d0303 68
    0x20203444440c5024030034008032941c000c1944954001c01c51401010a04146090764044810701c00d44294038a804200030f07070814060742e4400c01011060024040360b00d40f9507401e000e24500802c00060000004048240e40d044035020740041d80c61460103010320b051000f80a00ca80101c000004000800048140c0d0440c82510607816031381d200c10915541e0019540b000e4001814440400e0309101c81c2c1c0c0003000058000d151006d030410075071800c441039401d11325005c2100b00d05030319090310241e03010107500c6049446141040c50b0161540301c141c1580406071000d869800c454204075192002084005942c403000303820717030783c039040710400e011101d07084844101031078011046013036843d6116400725002d5075034080d9054202404e0300001c0c0014980c00007516014800d0441c00390180c91100c80740d90a11600e58002c00c40c0901b1481840004200701c00300340e4840b08140014880d11441000b51140c0c1c50901240e582c961010412520b40308105038021504000e0071140ca405155054100280c6403c01c03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 595262634 1250 595261384 595261417
    0x9040603050708240a090201170c0702090a0b0310020904090f140712080a0e010201140a1e0c0806150f0a050301080c0d080307050702040902120c1003060305060f070201140903 77
    0x448559011840584c4100d69180040800034890600940c0000209401890040603180d91901040f1809200f0b80700c0086d00d0307401181c00411403614845c40c660200c2040b1051186030442804217039a0146075005c00d042c0b0390080f6000341c0a4503554030034020140c004c0e00c4035810301250b080900c1009042d61a40c441405902800700ba14001d0101310341c80240e0195050345054040c0200b00e40b0460010344160440d500c5801c00c15000c1401101c07607010341c109034400070700141507004044c15004205c060030445402c243d0801912070b000072840740d00280c1520354900032450019210800e21070103000e500c0c5014082034082440e5031240142d4162040301c0308907000f0710008000c0090081240100606040b820400a11710503c50000752801d588007520119104000f80c0c00102c81d00301100217068582e11500c00c03841c55103003070841522000340c503080802c8550b0440d2141034681000600c0b4001c0d035642031010580d124801d6200b50356142c1c40c1e40a48241d0f00780108060385035480300c03814150381c000303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 595263884 1250 595262634 595262653
    0x22b06020d2c030f18090c0903010b0f06030a0b0d1202161d01090c0201090507031b0501110a03080705090d031e0f02060112050a05060108070e16200309040603050708 73
    0x20842ca500040d103520b81c00a5041455180880c0010b078081030403a071011400040f070b12815150b141440380100031000e07046841c2c0f0b0b010b40a01d401c50724404080b81c0315404c18288013501c0c0c1c07501800c60ba0070400c031840100c0d18411000103d40101e2080d44002d1420141d072301d80c103100585c04501c1c0f0594410301d05000034803a6036080351082c0310084041c1260740448513001008285083d0b4041b00c09801280004601e04056444040c11704060350700503101c0036621000c96070100040e0802d0009031500f400c048440104070f000300e9944540c20b000c003e052142e5a80820b802c103028405481040344010a20000c0c1511460010a0070003040d006120311882c00e41c1c01c47d05540180c0c1e6801d8100c9550340104026880c1c042884120540038a003628030780220001c1d034000c151309201c0302d801381c10864004e0203250f107051041c4050703c000070b001d04516103040280030b600c2c560000c243d106155100c8244c14030381441410140c298400d00e1007071a44185045800420810003043c040200d62540b425582c030306a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 595265134 1250 595263884 595263941
    0x8030f0108010524010804020316080609100c12110f07080a03060b0c03090910030f0804150c02061c0f0f060311100806100521041b03022b06020d 64
    0x100d07004e442107809a01500743c020294860b200c2d040d8170074001402c982503a0540300340014108001e4020003155082181003004c45030382088401e0315511052002c0040158140c0010400001d00c40c0040d62039440f40c0410039023352501c15a18000340d0019001e907241e0041c45c0400260b808108424042400c0c078800007040c1e09824103695500151341d01443c50300c2d030090100880b482e4010b1004003000041c034004404546c9014221400b03030322820f103c0d40d847e4100f070a0300c0900303060002101e0802003410250001038a40320103481500c191544004040f044a4115034003a1060720900d1401c5407801a03091980040e0781c204504481c00381741c884441031040030902076460f501c0c00c10300c4d0202d0300305008644c0c10b060060010543d200d4a24009040c402d031107503440702e03502840c200440034071031034000e003c1444000741824032002c2100098500c62172441d40450100d500b00114005040030b200d040d00c44c00c0b001c54407000844d5a12000c1190b0716100508003400401d0f44284603c89085099501c1f04e00c403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 595266384 1250 595265134 595265161
    0x60512070e0604020f040b0705060108060c0415030b010e1201021914120c070c091a1002070e13150207030e030d090909030302090d0c090f0b0901031401060308030f01080105 76
    0x1200120300d00300107691001c2c00e010180d444400308076074407503041200060381d00c004005841c01e0b51103680509210b52504035014500180030f8403446101404020410200320114082d01c1114440c0c1404200000001c00603142821107a10513500038044100301c144100040d03004158403445e02ca411140a800120100c0c2d001051082000000000700488580e40001c028016408640c1d0b0452510b450000e546031000c1503400d070b0203404043c4d00d81e924014100401e00c46541740510584540c5045500c00d030009640c0c407058403840e080c41c18501e01084030b40080030710500126400400c1025207102c00310f50072000b9800700300d00380c0008030f43d41c904820074500801c01d054a032015581c2e1140c414142480d5600030084400d0843c249642044079620b1502c0380d14910b6005400345246508040c5450304140c140d641c02c045a038407641c5401044102030365450659410340b500503424500c0c450a82801600604c04c0ea040070f0561a004010045000c0d14440c401d8160b4800c05d000b48490340340c616180d2880c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 595267634 1250 595266384 595266389
    0x50a020a0507020d05030714070305010506090c03042a08070503100e0604030305060f0a091b0f0c08091813030306050901030c0308090a15030b01031d07030b04060f0f06051207 77
    0xd082004107001528120b420307011241c5c05501a02e1a10380c0554035440100b0707891010064a030448002002030050a115450b800750050b140e0040038980607000c00d50a2100810040ca5018000c01c40c00d00140c107012941d08425000568044054440f01c50559030b200b58800d0501c01d105401e40120201c1d400d0058800a1130701100402007610742e981c042d0058100201021340200d0341f5a040c1c071440d5074080d50080109040000011071078111100b010008416203d504c0c00c3c8614601c840b000d241d4020124039510b90030032091078803a01c4030030024013009010b91805080b07040b49070901940c01d035650180c1c0c2c07100c1d200792420000240d82d0000d01200290174400980724040000303040021840b164001c01506c00000c002502940e125401c100c010200703804400b0011307503103104504d61541c05100d0410138100002484c1c42030b8808103001543d030921800000c00048515020400700011034025001004554009110940403101c80c40300520302807085070700c2603121103070004032343d200030804905 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 595268884 1250 595267634 595267637
    0x204090b0d030f0f030902040c050c060708241201050f1602061005040b0f03060106030506190b040b07050a060504080d0c05120403050a0c060207060204050f030f030901030902010e0303030702060406050a020a 91
    0x20652103c5600340c0301026400c80c01801d25844040c40001a0b42e54400e40ca540302141d12280c6d03d8410680b07000745031031002002c04d01800051814006100440103104422041100c0807825136041800480c4907103840c2d0640c54007943c00e00741800280f2034040c5646200d05c80d66008191600d41c1c030001280d407808280c40081c00441e6095007800b00e0700f065040000c0714180545495650b56104010a1070f280d400d92003000001d0b641c000f845068980809101100280c000c03114140c031b410204c1401e000d00c241d00c03620015420005001003084001d0089802c80390b04124100094a01400c01c00d01c154014014107901030b140c51580300307074140540150f600794040c80c01c1241b01555141c2c2c0555080d030040c4400000e210002d540540091403c3c0001e210306031203002d0141e2958a8001802205100014500e204e900007a5501e1580304c00001a20850b80091a020a0151583c00180c03402c6041504294250100100304041c198002030018041c9100e80d40402960350340c1c3c0b03d650124005c0703405020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 595270134 1250 595268884 595268897
    0x30b0402012c0906181906090c050d0c11070f03030f09030b043903170406050a120b090109051014031005360f060f010b0a0e0301020309010204090b0d03 67
    0xc2d19420904030f07840d4007203006001c1d00104070f480000405840e0f022180c0782e071858088000800d203025140a11002000c00304002d01c030740c0d00242c4020707100c1d00030308400c00308842d9150080032031548180700d0104a0005107081c1c034400b0b9110040707001300300110302084e008200d840411401e050305c94071400c0216038103c262220240c80e03980e074015a07000510800892580e81c5201160701345c0301441c10006102c0b5004c0110000c900e5071a220a0130014a01c2d440301250f0148401c10100e50404100c4009041c5442c181a03400c0b140134a080080c4074400c8907642040040340040f81c81c0415901c40c0b0702410542030041c501c2961040c6824400002d0321030319416030080c0000a05144154004c241c00649e10001d851500c00c1e8442505000e1b118807540ca4081d0801c1c2c1c602a44060703061104196006034140a01207900c0c064491618000046c492080c510600180329424030348220343c107515804001b4020b540c0c0e4103204c15807034042c2d005800303a11a180c3c0340c400420714070328024a400b0f02940e459204d46 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 595271384 1250 595270134 595270217
    0xa0b01171302040b030d23210703020408030f041d01080706030228090e1501050f0904181401060905041a070c0b011814091b041401030b040201 63
    0xe041001e00000100d070440e40f9503d41c58075580e428081d04600120540c3c034101c940c5801c42039036104104003102c202c2012420004074184140e180d03421400030b0a180204180c50311802c008800070310944d407003a0f0340350101250010419004c800100f00b00c580004007020b440900c3d03083c6950f1044207124112240d40401400c202076030003034001d0140c4a45145070800183e00d540c0d102505003103107445207000031301011000c0c40300e01c10182c0c900d5080414011b255030a0309040b40043c18a12500150340066400492110080d6840e40c1040005490b10b0f085010042440c1c03404d20110640f10750310700910b508000001c29081020721455100d00d401110120300d04c101042a1146203802520080030046101c04400c04a01700780c1d680307402041014403e090010305400054122040d5031040640c1d44900b50a00500311000180f10300e080840c5039643e4990317641100002c2c001e003107107003c40c011400024000028044945a82c610a50003a2501700b100c102e062880c1c8a00f201100d0702d9503c2c1c11540000307 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 595272634 1250 595271384 595271401
    0x1109070f080105100c0618210c021903060f05090f0313030b090703050f0a0501060f03080d1505030706030f0606022d0a06020f0d060609051513030c0e0a0b0117 70
    0x1004050819030811031403825294480005860222041100707981120000c03800f006103459817940b2421420041240e69001c4440051600e0f275501006841121140e24101c64808000c01d204000c561041c01004840c04052519002d48012299410790340034161138560140004021100d00c2c7c0e030f5903001c45081d1410740d50741500c46480a8000d540324032810030003200183c000c02040c0c160b007000d880104101b05552a18500b901d0306a001001d001245520800025003c031081c0c41c0d03038400c00400480c03e0002c1c2d060031421410f19900080e803522505800150094156200f625084290b0f4001e100081d1913501c142c0ea81d02190581c4080341c440346020002c0e04801b030781e190b00143e500d0011b4501c220599100d9500782c3e080481104401a4006060305000d01c991080388010300312414001c0c190343c60880064889500300403507100f82c000000d00308010041c503054004c055540891103031181c503100c80380e604543c502181c0e519410b40c0b4001083d101e42d0b000e040c0b05007034201c43c20b000209968640d0f12 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 595273884 1250 595272634 595272649
    0x12022404080c070602072d03110316060917010501150f0c0f081209011427060702030715020405061605010209090c03060f010c0807020f06070602071109070f080105 72
    0x2003964100814042c900003064207004540003011994000c018031781c11710b00302ca070440c043c100002d180c00000c0008204590f400311284800c403900031032049a141c03200700c04681000001030a07034030304800700c10700820040e82200500003a56100080c02c507203000782c00002d9080764020300031040c00f0f0441c58611300304a4800c00d03003142c4203050340c502903003046007550700c585104000080c05c9650744800306070346600d1038140c0c00c01940001c03050020f00020080e046940440364000e00055090358606203110802c0d6070030700ca0001d41044100c100e881c149082e000003034490300080c00c101d075400102c041c80e0601d117100d8000c0d00c2c00e80742d00a0103e850300404250700b40c0c0848002904680554003404200c2042c1c0d03036544440d1060f0425034101e5900e18042c0c0401145000b0103281038144114070350f038400032600d8203041d1502c00d541582c00e0901c504d24100080d5040c0503420000b410f107400045c040b0b0070044c480004540b002e0040d22000d600791261142551400744022654000403006401000765203400301 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 595275134 1250 595273884 595273891
    0x10c1d0102010204140f011106010f03021017070320040b1231060b040c020a020102070605071a0406021b21120a11090a08010b0a14100e03011e09120224 67
    0x5024248c0c4c083e031540241011004d0b80302c44415030b2181310420a500f011500003607814103a20341003030241004030502013900c1c0d001e00340c501056564155005840160007c2180d5030320709116042e2103a5594140120a03405110f0500b40e02180d040030440111114540d61110840280420000420448001501410402c06a4170b494903241d08450a031039034401c4501d205c68950190444101e03500000e841c10045a010600b005000c100c4e0304041400644240203840440e00ca410098480e0b0900c00060302030081e90034840c03070021600d607004003000103c58120a04030001001c0c00301003c09202c3c51030148800d080c2491f21700c100050500c1a03640c0c0b107510402c2c00240243d05100b04100410a2414140c20141013a95914a0b0b40040d2500d60301140c02465000c0c03000d181c88580c030707000c00e8000c00c1718066403040c404644244000342e0b0f003e410000c14070007400d1001e00800680c002440191821a6050381d43c10688665101d0191010903050b140c0f100c940e03840750740524103201e803a50312035004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 595276384 1250 595275134 595275137
    0x6050406030c02150f18061303050d0204050301110c12040e04060509070f090c1403060a0b0304031b080711090f0114010c0c0e070f0f02210c010c1d0102010204140f01 73
    0x861044c03060b103a504039101c1c001c003060002c414013490700d900005101c20724603d0480712035100c0020071403556a0306440c19001945803502a494981882d1000068001c030b8002960550070315440c9c44540d101c80000d465100035a0b800c44030400b2030a0502c40b0244130342d005104c008182c60001a011440390342044d1707084003030001181c0031140d81c0e0809411403001758000802581d01d50b004510344d0b503400182c0740e2460703a8012034580744d802e0000015890090902c0351040013180031000406150041102000e0346440040040c45a01185040480b41d401490201c0e0300144081d028422800d008600500c01c0f103007507010403100e9080001c40b030760f450040600c8904200d010042c010004581040e5100103111807803241c26a030070043c0000c4c004008081c4600100306c058142c00080d0382d0700043e80420030100d4003421170f400030507400c550118072490152003219800c000d862403581d507010001d60301c20b00700c00c41402c10050380c06004a00b80d10540c460704140000030246454a4a08181e1034428080305 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 595277634 1250 595276384 595276393
    0x3040c1215050c090a0806160f02030c0a080a080108031305210f03070203061b0a050f070206211305120a05090a080109030e04020f1e1b01051f06050406030c02 70
    0x5100d2408140c880807600f0044803140400c482280d410a82c48410140034554060500c902d0807144003070b0400843c03481f600402421000c80d1201500034412105410351400640d01c241c0001e040404443d4013003883c43c1c000400480000a580c900071083d03801061520703121512092400701009861903581303000c1e82902a10b400301d810400c608100400421900d0001380d51251400e00425080c680c1c010f008034000d040054950401301402c50859019100c5801c00c1d50712511468003031a0280a0080020f4010780700294600c11002d4034451801e500e07034181001c00d22135442c54804010902e84100003040d644c0a200d0401c480c5c182031000e00016919850002c4c20a6104000202034076115800b00d41e0603550f07100044141644100514144601a01c05503d80b42e00c2c0500c00c8403610034044d8041c0350a203056508a00c0b09001c0085505115001c2c1c1c5000502084520f068000c01094a00500e840e540c2010302c4115000e606500040300e03170340c2d1626414945003d0090f000340040c0c03001d24007107024 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 595278884 1250 595277634 595277663
    0x7030e0c0307060809060906090a06020a2a060b01020102090f130221091203040f0221032205041a01080a0204080601030f0b06040b090c0702030102040f080d0207060503040c12 77
    0x804010030b00c0245015510a8240c1c00c020b201c4505050010340094680c1c1c200904003d4540c4000985c945103a83c403440c0180e64000c00c3c481118103d00380d04512040e402000103011102c0c1e005150459904e001d201c041114061607801a0700f04e00c550450306401001440c104003d07031500301450307079092405640151034408011032000090103072038544101c2452550034040b20020402100d0841c80520b050780e4510304058a505910100500b00284106c40c004224510128025042000c031101142143d4440b0100100140180b43c040030054940c07602d0313480000d261410b0700801010ba6405540d00c03201344141c100440e003a01000300a0404035400f0080007030048002c0010600960051254215503c80780ca0136848e085d00180c02d85100e242804003002c0103690f200c10700c640100144010302e583d01c81c181b0200380a402590300960040e201200005400c0c1070129043c082a0380701d50035070302c4041c0c41f0941650036010540b40603100c4010b1001c180886003400440f17000803030054000e04880034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 595280134 1250 595278884 595278889
    0xe0409150f090507060f1707021e0705030f071a03071b0506101202150c10050f010e07090b16020418110f0301020c19020604030f030908100506060307030e0c 69
    0x40c0103520000311580eaa0b41c0e040240a800e00000001e01018079081910b01e5a0fa400140400158140703c0e14405950003c41c51031402003145550000301503a40329800b520103800544c80d04031360300c01c09000740100682c20030081e81c00309070035007a29082c9000241070310358071000c00101d401c01030070795050100010151008082282c0d902150718400c000404d0640390000050340d15010690290704800742c0c540882005035982e40e0f5155503c030082043ea610340924101c690b1a000d540c038410f400583c540380c1404417100300b0035021410ba80c500c4c2c1c5105136984654804a9115044c4e2080103204007041c0101c1d070044250107407150403940000e20219603014409224030703a640450400329001c984007547c0507403030b05207090320440c1031504034000c60500416000e1141c5820300d2402c488a403201e0740c60510115a1070324103031409940c00c06070803d0310780c40c08d00d0003900c1030b140390054000912441c1c200350141c0f0006c0c0185032141d540030f05280e0031510f68040030740140c4a00c0f8894409400303006c281c1c91132034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 595281384 1250 595280134 595280141
    0x140117040f020319150f0e0a020d03020c1503180a0804060f020c060a11010e0d0c03030906150602030d0b100e01081003080a0509150a02070614090a1401020105090604030e040915 78
    0x1070260844034644031700000d5080450344e090b1010304c440d1b41044182101c2c140086040c3c0c00d802d40542d11841c0166240c40c1c101d08058400701c0d25580040910041051041400c1c0518820122170780c0c446441044148003661301d83c40c1270b1000300454010402030060307a00c5040170210a03031070360040301c50440c0c0681c0012850380013940000c00040558000c6200c11400340101c1131840140d00103482c1800f0020801064520808806002d05803501081e10030000715a009061141c00c160b0041c1d03000c4d40340d0030000e44940c130a00c408400c1e982440604800f5103451014100c40d2906526540140102c0e5401034450600081011200b0f00c900100040440e0307280e0001c14400c011541c8095a6228400400c640090032510025503c0c00900609580320b4002903e1002c2e00c00c541001d900170411050341c200b0510071200130a8121009000000b056008400c02102060090f0024002d03a41c3e41c40c2036a0360b490040fa80900010f0542400c0c1c0d0203801d240d4050801b0354010042d1200500b0350703400580c1038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 595282634 1250 595281384 595281433
    0x302150d0e0307030302030a0c0f020319180303210501050d0f02010c0c0f06090906030b0109091b0801020a08131203151a070203160803041e05030a0c140117040f0203 73
    0x300380c00000b08807030000e0510600007407128500b0300080c0040c0e2b01d00025030700c0c010200c41e1220300b0305058100d0b1040340507a0183c0800300c80c0180000c0701075101c0c035004013140c203416001601050f5040c3c3c807185c50505401414141c0b8005407100c00c082c0320503111080a500c200c80241e0510400c841c0340b0020940240c060405061480c1e05040703403924080006114946c161f00c40b0684900d00841440040c1c001c0c2c05083c11184904004500d8620078101b5036400f0384646031480074100050070014002d001900a480c52101a441c4c14000703035201d002c52101c0c59003144009166000c03107410aa0a40d000c1d07448544400d03006c40404154a480341030408032402e41e88001c81242c04085042000c5140400c13039510801c040e038031040300e41843c188070b15a0324003c2d0300900a480300b1010b1141d00110940c20603030014000101102c1108034941050442c40407503010b80a915940e1516407003065014110008003a0030000070050301d42d03210740316040b01150341030003264180124a80d0903a5100d105003100907 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 595283884 1250 595282634 595282637
    0xa17040e090d11150f091f0c080c120402150d0204080309090916031104022109070b090a0b0f0904020301060f031505010804142814070302150d0e030703 67
    0x8503a650342d600940310007040d00304481194085410442010005054a41c1002d0941604155519403074856800c081544c0c1c40d1808018910031050500700c0c0304d4200c0c40140c04c80c0d44a02d251a121032240485a00c50b0b0360030340212085810100c4e005041c40c3e021080064100b003001800c003500000248141d13401903000100c0c60b13101044140c02407070800c4456800040d504000c28030320700c0004021400542511001d041d018404550564584031601101c10580c48045041c0283e004103103050010402569402018401d030034001c111010030b5401c03070341070000041c01c5000481c5840d03641808c40d0b002d8110710302e81c5001400f000046440e00d001039800381185071202c0080003280c01004040703c0c03560741d0a45d0046102c403030800142e604013000c80d4003d42c224a2a0080e20011010189815202c101e142084c184800d029003403114551040048184a82c441ea02d40d810080d0010341e03200072500020f07601a501e100d940c0f0b01c6001400050412400740c04c0c010540d00c0003500c1060550700320700000d40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 595285134 1250 595283884 595283893
    0xb0f0a0623040506090f010608090c06040e01060e010825020a080a08040311070b04050f0303120c0301090c180b0c10020d141e0a1802031006060e01050301080a17040e09 74
    0x2100c030b10b07041c0205940450f05954030641490304291201d08224180b0500050203001030100702002c100b40f09440400c0009040140d17150340d01c22615171500002d2040303a00184c807018030540103605c240041801206014a00552070b0850b800011904504411140542c0318070003100000440c414060414010b46444410982c54181005082900c4da03400d000c1c01e9800c042001d0100890354015241a0b0320103650007000e405500c00400d255200710504195145400c204000f01c40d188080158180c8004e518140a125410344044c1d9208000041a42c0055040036090001000001c05412000342c4a0201c46022540c1f82d40e10381203070f209807014a1800d071240040c2541140035040c0315008013818445501050b005078030114081005000303d000305d502c4461940d5091a000464810320760010227603008141079009800003400544103800200b0303910910f50a05600507800d0300e04803403c810107008a150f0399502e40321920301030150701040010610010514014040a140c4211070150007403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 595286384 1250 595285134 595285199
    0x806011d0907230904051e030a09090218030102030f0603011a0102120c160e060114090612040633081908070615060210050a060b120606121e060d0b0f0a06 68
    0x124247c0c003440c030000034542e100704a0760820760b5218410208590f2502801038446185454034419020304502d8503070300d0f6002105002181b2074007029240914412002001400071100e00d0481480d440e4034141c0c05a080700d040816070501e50001048034410708000e80d1344c03180611140400d0440f0075003141010384861410084903507042042c200e01d80b9004d100740303814143ca00b0001615807284c0c805240c00308a006d4040f4080103c203030401c2804d040038402010100c3c00883c951094400203080ca01030035a0320000010322404041000e501c8002c1041e407844800d9900e0b140c004450303001032007c0350221764800600c40911b8401e80f0031400b40c0325a6000e8a9509031140460303040d11005460301c103203649810000c020448000c4100d441d002034400c070010140d610200020038501440202c1069554a0390410011080c1c41c4144201c01c682491041803d842c1d0340103000d5000100d440c02841e5424810105102001d105038080e402016018046541c90700c400c20103c0d0304a00340108042c506494065 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 595287634 1250 595286384 595286413
    0x112090f030903030e06032403071a070204050a05090a1b15090e0702070806070e01170c040302030706030e06150f030708030c07050603090a030c0305040905010806011d090723090405 80
    0x17040c0780d0704012a501c070b0a50401081000c02e8140000d011510101d990b101d03901151414003001c1c0c001e00d803142d1040c40001480c5c00d8100c4950008504a228502d000e00042d0001600d02c1203078003030000800240512589a91088089000781d840c0707000d051500b2600080100b03004030905140c060039910159a03915211412210b200040d100f0001e6401203030051208480c0000e203a5170000705443c1a0308070aa1600043c0c0f1148918480c4100c85c945a500b008220010480100301716072095048a4140e60f031010110200c413424840c2d00019002400800c010020f090b1040c40d2258000304500903200181001130310380034556001401d550008550542c00076402c2c86814000c04081e0740051a51500f0071440d926500808002030501000880d0202898818400c0d60058881a40200700c0e650f150031072140d480200b440754049812075803002c104a40e5030841c01a0050860030010034466041249155104440f41c01f0482c651030840440783c1c00355540351906005900410143c180740d0550140d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 595288884 1250 595287634 595287647
    0x507170a030e0a0b07080705071401091202061612060503061f1202220b03160503010c05160f060b040227061207031107020d030201020d0f0501050d020112090f03090303 74
    0x9102e405400403540c450214130740c1310000d51310214500d0941e40c01e03501d040f0142c1d5580565403016115031060f036500c515207041544021000c50184c0c0110a001544c1441203955900c02c071355030107040e600320184c011801c1c01009207000c0e03901842c07008035200d511540421701c1c00c0da08880f104080c041540b0280000e00c0c04c9440040a0084000d0061000d01d440d0040303203983e4032181c240c1c03120800e052040c0421072040d80c00341c40004030043c2520003540031640c055a48151601030103201e03500c0c00b403080c0c86480c010021142008002c0600000030703801d0307032250700300c0000c0706400362074550f03c440d9404216a00c510042c424a03004820a5185c910b0180f1116801c0b0303c4544110300072501080009641d0b0000c143d80ca074400e0592401043d0b42c0a6502e61000c2402071410007034212800400400030540c064014000101c84403500304000c070101d03041c003000e0318820b10480b07400103140c0f002e140255104804c08460141e034100c2c0414030040030303942c50f01e4007404468240e00155442e48144200740c1c0c42038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 595290134 1250 595288884 595288901
    0x130c030f020c07050f0414130b0c25060912030603050c181f080613050f0604022409120706090b12060130060609060504080c100507170a03 61
    0x30086041c1100d040e0b02d00d0f910b05a40c01042d00c29000c120048032640d4443c1c0240203c400c0000140060703090a01c01030040c581c4401c401c503a060040b90000d41140c000c0d030f080c1c0345036900d0b1641c555450040b5a0007030898110044060300d14a071144e4809000c14905100c203410080d43d50f900080b0300340b441c20414100701020242d1881a62480c02029041c0000701c2c1140d088500440e84003045211043d0041d81d130301859200f03907028001c120400c200c900d014000982c001e40100280c440440000000d65184c0340101c5000750f1040d07685034040d84202040c1220a50544040c0c04549460203000c00601c050181004043e160303444498180710b21030307000844500404511000764107080051702942c0e40081c00800c00703410040c010601d00c040c2d008681008140303950081c1c03000c2c490610134808001914803401a0808188210000501203119004890443e80400040e02482c513040081000d082c4014000004000b03080c0810000f0684800031400e031504203018a0360344504540d0090181c85602 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 595291384 1250 595290134 595290161
    0x150106020d111908032502010b0405180a030305150316080d08010614090d060f0606020f03040e0c0d060b0f0c0c220c030f06030f022e14040302130c03 66
    0x10340090361401c039074010f0ba0080c2d100e6001e949960720080045072850301c1920205100126a000035569901907100450145003a5003c0c4056a00c400400c82c1c1c0302e44c0082d8040301a4801410500400c4c8254452504040c0001b44028200b4000b000039240410740705c81e100c903022010808006090007009007000c40c1c00181801c02d4258548079028024084002d9420782003000094814210760300e01da8045403075640701e942080341403452400c50780204101c0c001e1402500c5401201034032514008240d40480d5440491032525a4441c00e40038050b802c150180c02c01142c480345d002c2200c07008100034019031051801c120392034412114801c0d04e050085c8107903034000e0a00031181041c0c5080e00c002d800d407a50304200701150144149004070b0041c84150341012860b458290040104545900e080b1700003802103e8501e40007401d4289501c8058400a5249584042800c070000312806011820003101c0c2c0840c20300c1c2890780d40c1e00860a00340c41c400034007400c0c65581c0d280206d081d0309032062a4148020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 595292634 1250 595291384 595291393
    0x1090507020303130f02040f022205151303050f0d0e040203010612092a1d1e070c060c050a030c1d060715090c05210a020d0302150106020d11 62
    0x1009010b500d074800a041e25058180072a0a041030240250704200c000ba8040c01c104090070030008014000d401459800b06100030180c10310518196200009043d102c00500d00d803054428055074580a0b072010740400c24a000c0706c403002021604c24450500100441e0019060f0390851b00002801c000d511241d99110390b10501c01444501c0e030060390706c104074907406c0c4c000980b080681418a40480312960340640f032000c4401750b14101c82c0c4002c21030110b6407403103c1d80849054200c81c1d004462011500c002c190b50f150281c0100c002521600d042d08010541070204d0010090384481042d240c80d82d9145002c40c2c00014002800d41d40741c45280034407482c500e001613010540d00f8030f0100c1105072204561189101040c088148030080e030181180b44803800d002c1091200a1504014800a0744212403042c448011500740f1110458505040c10900d800a44505805503080195803150b40320154114030800701c20070b050f0100303070130018060318103500280600700100c20f00403c04602c103502c400b00c0381c10 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 595293884 1250 595292634 595292641
    0x30601150807080405011517150f060904020a080a0f020916020a062c0d090608040b06150f03090a050706030603111026011d040506040213060527010905 67
    0x107025a00035005000c0f0f1a1041440e115801e040303014000300001070132001140e0700c00041c1841c001445403060003e503015a1188240001101502c00088813100b0a070f0002e5000220545080d24038103901501c020704031041e19455040551400c0e88482049401001d0248400f0562405040032540f1514940210403603901c80e48000b910344000f034000070401a01c415501164030104c1c6204070340e1907000343c0302501c0080f1500c0100e40c1e0303168420302c500210307110490200f00c162244442601c9960000a8101c607912454207018035004c03552108444500b06104004400e00a4001140240c1c4a0f0004004481b00c0d4140541805c14651103901030500d03140040002a0840000c1c0042c00030031649032403031076030106064807a00c4003090030340141ca0080304100200340e0440c0115060b5201c004041c0f0381404071965840034a10165005001c943c0100009030040c42c0c2001f111080d8203017020040749082c0d27500086582c81458000146904040d0240c601644180109850060004a005000609 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 595295134 1250 595293884 595293887
    0x10050d051b01021906020d050105030303071d030c150909090d20030904060305030c0c031207020405150a12030201051003170d0e060f1603060302060904090c0801060902070203060115 80
    0x504119a40034116076000711095aa0003800b44040205401d82c69440c0d5880c0d41c80e0940096001c20380b001d06082c03410b400401c1a040010969105142031b0700c900d494103110b0f4841c0f005c80c00640c412194544101c440704555030b00c501c05000480117603a105c441d181d000c241c0420011f2440140480502e0303102c4415240425400038140c601ea6103201766400e841001e00c0207003401c610490b99090b402500744000001008000001402d01e000840c09903854840d10344101601e4075060118114030a2080c04103401500e0320b0751000390000f40c00071070410000302c200c0105000d040b180d40000003100580e01500103064083c090f440c0c1c4041c85841014420382580e440c05804d401114140c100054049150420034419a111a1140c2d2481c4103c80c502d28081540540d60001103591681246481802d6440e6a000c0c2c01514280d90b4002c0001e4100541141408018416500d09a40c000c00d030700e0b40001c014400384501e030041d05141c0c0015036a0b1704103006251900c1c1042e0302c08191948920a88040f40303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 595296384 1250 595295134 595295143
    0x3100f1a24040e09150c160308220506340e010c05060a200c1b030106051c0b06061912020d0c0804021f0c020f01230310050d05 56
    0x1041d090840c03441001162030801c510301540d0802c00300c2c0d844800a001c0c2e5100e0000390200d8103040c8001051555980c0812101140115043c914400074510010000030780079100d055444000c04150140e80394021020101c420407481d41500d5a8104a060050441e100da03003e02e030440d88250700c007907803588418001c034020041d0002c060802c0031756031050460740e101d000400034003a0048100c90707541c05c1504003e80200180d6140c00290100d05540b81c1c840810081541c0d20303140c4040261031151504003415114204c0b5058855141d56542c1000c2348035614079503210801c001e252030b060021402450000b1001300003070459480b8520a101c040d04040226480051281c003500d0145040d0a00c0000e4070040d004002d40180341074102140340c0c8060368400d0319241f0590003141c865080841d440d01803103101482c007850100040c11081407801500b02407041f0b400c11401890207020095540e075140c204848040c901604d403150000600c0550600304050340041d18044030058210f80150f501d0079a80c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 595297634 1250 595296384 595296409
    0x50f09011a130b060309150601031e0e10090b0a050901020405030a08071703010611011a0d0803040f06110a180b090103050907050a0620010504030212130503100f1a 72
    0xd0080b01100c0081c0040c6811080122102400d25030b22400c010155036200c4442e030800444103000240050781d90b6200b8021884000d031070225146180190294101c01340c09414000c04030307403080075901410780c8280e120300104640248800541420846002015110080c00b8000c450380184001d002c40d69002c01d58000c01680b04401540c6c4150f0f13464100b0030021401e0120500f120040b00008095030004400d080070001c80000700b01800d40111080c1211078003040c00c07070300040b1008070040003c018000943c0c002e8050a6910b40740b0340350b41d55600030303122400c107051482d00c008240981c580d034102d0f10034140200800c0d0902c840d82c0c1000c8150066000b03c401c178604041d10b80000c03a03c140c000b4003150001d04405440402019195403024041100e503001446050171100d510540808061082074002d942c554041d00003000742e0301110351550404004409440d4405600040725a01040500340c0105007030001b04041d80d0091403001240e0002c144010b002d054816595003039500d038000d03040c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 595298884 1250 595297634 595297639
    0xc0216380909010b0f040620010c0903051e100e0c040e010e0f0105070e0f0103020c01241d060907050c0106030f0b0702010b10270b0d0b010c0b0402062b050f09011a 72
    0x1520340c21032350110440c064071807404a03076500e04215480d85070b03489210581500d01580c2100d51640c400710703060040010016180c2c003035400a030000f01450400b41c0000b820313084481c00f107480108602c0006411206503501e50f52807a036440e0041041c49509025a9044c100c040f0b008000e40d01e0190360140c0f1060b104104c05224421014070504281e01079130540c1c5000192a00802c404150141a440208051184894510880c0e000064131028141520340f1103080c4151086d0244c03500003e1280240001c0c1c4820700f4014181300c5603207995000d10541008500a0082c0e60100b442424852a07200000e00824210390500b5a00c1460f9200c0d0404110009068540105500100c140201080039a02c514020031031a0303040008850a00c00302a0150b085080d0080000e1040d00b001522150f80d071500040402806000182c090700d40b4130041e083c1c03000354103100116055019000854103d0000d003840c1d03070550700c1051141c640c0b04044d03503039444103019008001e201d000d40b1900800311400d865191 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 595300134 1250 595298884 595298897
    0xf0f1a0c072702032a0705031e07081c1d03090402070c1502030a0e090114012d1805010c0c030b0406020f04270501062102091207090c0216380909010b0f0406 69
    0x40200270350300302c400903500164102e171211101184098400030b81081c0b41801d50600c41842c00490f5507c84040c10510700200070b41c60408198203000186d04603400940f00d900014400240341144a0070317880c400d1000d50f02840e40c984d10f200029001010920029000d8002d81c0d00500c401d40c085504020000e07002d0074a04d403112909042492030061460300d00ba00e02c0303032000b009048550881600401c0069606e1621540d0b52110011100402030503000740c039000d4141010000301e00b040c1c8540b500140a0b50015150507010354501805501941c0454200400d911550818130190229443c043d0b00740c0030140b045524101e0020003841c50f0078103a103002040c14901c6944040d00d58100c81d11500003404440250609110740364440c1c20038480c0c0d014107410700125840341440424030b00e44800c1800e01070100c0605144e060a40201c4d60f0034507030007403851030200b03000c1c5d8a05820995010200f04101c80ea9613100071042c0f05491a041e4040581080148024181e0400010540c0d060390494a03120 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 595301384 1250 595300134 595300177
    0xa02090607140109080c07030308160f0809030c07270615181e0f0e1314210c0c030102120c070c0f0f1a0c072702032a070503 55
    0x3d0040c030451000038010440010800001d110210b103031022640242c80740d44955460b20084011003004ac9142c1c40080d40064492002c0c6026422031030300490014101ca042c0019145070616000598001038000b00c03021030144e00d28040c2402c4140c5818240d0800d1060600e06202c420300c1840000041081c04110b0210741100501e0640c40f500a020701c0105c005402941407410702603035040d020b2512101e400400126a04401b055014099a0803034044905042d15881d41c80c11301c1d01c81d008040e00b50080480a0b42c2207100c000c0c069060381500c1c0c89441c0c0c0d454002c184d0518100400d40c110b800380c0d0041c48900d1500303e1852956901120700c943c501c2d968a058034240710784981c160050700c0015050780000c264451241d0303101090303654281c45000340d03160003150010305018114480901e0703030080ca028002c114801c182006a050306204008440c54401c0d0000281d0700200c461001c10b200d43c1402101040e03103440e1aa0701c0020000e0300c203241c074100781c49a070f0b02c0340b20700d054080d90700315030f580030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 595302634 1250 595301384 595301423
    0xa0506092404200706090201112406060c1b10020a200d0807080a020c041a0d03020f01060303030e070b0304080d0b0102101103090c060c0d0806030c12030a080a02090607 74
    0xd10342d004400030380f82c2e5840e6031307514280c0018031900209a000891820140d114440d00181a040b0000a0f408520305d02500018260900100070300c0c0300d0f0000401e1200c41c089000400458111200d00841c405c0d0405c2c02da418441441440c1c5045402c5612250841300800c4c0c008440c407800d400d105500304103104448012407204450103000600759000000c0d00c0d03003407109003030161002c1d0105600740c80c1c007142108200420344028001c880400c8a544190074080c1c9024440042158402d005480904808080d482c1c03c44001390710903004207071190004100504148854009494004180c13821401c064a40306214043c109140306119070303e10070000e0581c000c22400380820560102403200350f00808903402c4a410548501c88140b090384a8600c0d0307031400c80103540411100c0703001402d100000316001c498000002e8103081c0c141c017840483d14942c4e282c040d02820020900001141d40e142d00300300040406e24018a080c100a00c18824016543e592500b110711060b000300400100d082c011a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 595303884 1250 595302634 595302671
    0x41b1413050d0501140c1b01061d100306110a0320040302100903170414040605130902150a23040503070302040902040212160906030506130908120a0506092404 70
    0x41178903542004c6000c000203032030f00100502052140080e1044551030f4801c45a0030383d40795000e40c00502e210400307030f00c002c126680300c000c0d88103182c003074102240c039a60784802040f01c2e5810f040d4911190002225125541c00d0702a000905490001c89000e01382c680d03116480902490200a10544510034018090391041d240030014540042c00301c0512130311029400c904e80d025102d1220011200ca80020682c42c09200d00350071101c0c013a01090090900540030001482c800d00c0890b4048e40c100320f0f4049828200002c2d0000d0b032071948880048103510280c1c640180041c5800a81c0302c141000705004a44020402004590341a200407910080c6e03480054081e0103104c80c0c008500c0304010403ca500c1020007480e12054485498041400361a00d204405a40040b510103411607269104900640342c184d2203054414016140c090601580b00c18080518905032200d039192500c44003440864036190791003e810504098980d030445100c0b5106080380c1280c500180e110340d9031403a240c84241003101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 595305134 1250 595303884 595303901
    0xa06080c0712031a01050909040201050f040806090c03150408191215051f0507020f040e03070c091802031b01090801020d14070c0506040b060f041b1413050d0501 71
    0xa45002c03071503031885004004111841034119120000704510315554019070032909801f00c06031906403280d503542c0065911764403080003a1030841d420000014052401d2201b54051031102016100200d221810949841000f50601d084884c159060200042840c4215078800740c1c00001c0c0443d200b40d8580a1b1595900343c4290b000d800e05210384800c0c04000460000c043d104200c41003d0400600700c0030340f146680303040b05540413071001c000c12030143ca403014070300058180003040460807100480b051b41c1140c200800c201c5036a5000541800180c06501900c1540c4041c18030115200340a500000c3d03450340c001d50000f10703000c084412450b15920443c1280c015100000095540380c000f2031818005102440e09040703905030301408107480a22804622141c1504000200a1511591a1340342101000751043d98051312501c91074a80341c5680c054480c0d80681c0581d1644002e00c90340014100c216210540714140c00c0801c4108000d1400610f21001c0e00c20656108414140600d00f540c010041c24 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 595306384 1250 595305134 595305143
    0xc0613030306051c05010c1b02011206031e0c0501020a03050a0309020f1216080703030c03110114010306052a2704060803040f09092001120608011a030703020a06080c07 74
    0x94200c10a04e034072100300c00f006540302d02d00030407181c109810215454001000d10a040300c00c07041c4a02c02541c410784640c184902c42410020300241c0d01d03035641c801d200c591b62041041014040c407680903c4101580d01b03004007002c0c0060180e004550b82c000f00240300c0c0001d40303418180c2d2414041c0540d2200450b0307004484029203019030ba0503220b820359590790040e00c85c81c68821f0b0a400040b5282c040840c040c021a40c0c19151244c01c142d0996003502c0449070b42500480c0d540d030765400304400900600d0154021401076078001502e051040c052100d240d40c005000c043c441c041040b6420000c4814111543d40007418000400f803d40f41ea06005c00070041c040d0694003038281040840c81c6000407004008541544002034101350f56080d200d002d907802150060629060190310807450100c0851450540701c05241c0f013140b414a50000703004865182e00f04103244c4c0e42d100041c41c1da030b1051000303504088004400503d1224030715400103040481034003841c0200302c003c0005c100700e032224400340d40656030311 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 595307634 1250 595306384 595306399
    0x4050406140f060a1d010506071b0b21070c110616061401060801060816050f0a09080105130f060c020a120809060a050f130c09020c210c061303030605 66
    0xb54400329102019a04a4400d2512180005054445816141254000440c3c01c280d031ba203440d04000300c0d41c0295030160b5a2132526040d0312807955490103400d001e04003040586440380c544154680001236400c8480e001600c00c0014440040d4000750034030016540b00c5408507110f0f0802021940358010941e8901c0e40440442001d420018035400c840d00040301041c0c2071b44107a07a20311045404800038450003011440070008100c00000c4030f800008170ba001c034100585048001180c40010780d0041d40d102c000110008410b000001e02800b0703040c0c00070451204104191503039115100c4030314030010700a01095071403800781c0700c4500034410360b0281600551140c001c0c803c00a0003030400c04007240d01c0d040c68010790001070902041031113058041e403500c000c88040e81d035078400d044a0b14951107034181c0346041050380c00030303100b40f640c001056000704483c0902246041c494042c4c15480103a0356400c0c03108400d1114010303000001070014be211100422600c0c0412250809074000c5c000c035049260000c02 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 595308884 1250 595307634 595307641
    0xf12120304110901060f0e1f02060708072303100e0405070e0108010507050403031b140c03100c1e0c080f0c0f06060109140406080f0a021306140405040614 68
    0x840020314032981c064691901c45903858410000241800d00070800840c0c0c809002d60381d19803007441541c264107030140c0f501a180305c6014050850401c0301a0b0307140180e020b02d040061842d440b800d425003115241c14291100781100c000b80600320103043d000c030645840480011444040e00080200500c0e003501d41c10701c01d003490700f02640c440705c0078020510030885180001840e034905220b80c40c07003201107946480c105800e50b90202c0e0103a01449041e14030503084504a0003040340602c907601641000710082c605c69060505250030909100100d483c1d0382c0c81c08407950322040c0c111702010300780801244016014410b001c004c3e00c55200c03030840a8013180c008100100041803500090011190341011a80c00e000142d010550310001181c9040c00101049007c200240955031608806000140701113160350f12060b21a103400100003145d0131580c081d0b8003040075410240c1072042d00041941c0140078040c242810705c03160000f1003464074003a9070354400250502c01103034040850506004450415800e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 595310134 1250 595308884 595308913
    0xa020c040f061e0f0e090307021f090506120109200409290307060809010f0203130b0f16140f03040c051e0f06030903040f03050a150612020f12 63
    0x141e400340e00c400000f070501405a0034108000102124000f025028140341490390058005001428419152105001c03050069450840e80c0764001030b009180740c003522150f04024421032640e800301d401244108500440c280c04611060305641080d400401c03113480d4a005d00101007003459842040350808500800c81c2580c0350071a900307218010507040340e2a070743d1f41c03400d1183c0504c6088185c2c3c50b42c440c1d039080003070703500071600710b0b610906140c0005060310a407604203080c0c4c2c0c41152102106503295150504021149a19a410080b19411700c90b181c40c0003801e11480d190307a4a0f8500134042e45d010a02d070381500b10421943c1c80400710b1959500c9040500d091041150503000381c3e032160700009201000e40041ca41c0c4c191008a0040201c1e513500c030800e042c008180e001902c90020b5002c10403000c220810741c0c015200065124100500304404941000b01e6280340141c2a0014942001010002e4001181c0943c80c5250110758400c0c11035031013000580982510300b0014014012504000c0421 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 595311384 1250 595310134 595310141
    0x317180303091f050112200a09050924010608131a070e030334020d1211010204063c090627121719021902030c060a020c040f 55
    0x40803049401c030141204001c000044e034509003c0e01100d685034284981c0400d0b0070052803030080c1c0c20600000080c07003034503012a402d8105500300018041d111018070a01403000c20004521780d9070f580455211040c40d102480380c0f00e8062040c54104420000468a41a520a20900d00310350103607401761745005403044240c500c0421100d0201140340c44170220750a0030f000c001ca4055084419000034403c0400c3e9010380514091010b001000601142040c010f032541168240314500030400c85c1d00c50044440f00a000d104988028409139006100802c86180c100040d0544243d10620800f800c510403c40c5144c0b030444845504072800382c6a5241e125960800b000c801620990707600e1601a000d0348100202443ea41301d858000628081000c004c01c40784d103d01e40310024803c45403500d01c403034003452900094021401c40c00310440c0c82503084100580400104c1e41c1005683d200004002242d00069214088480c0c25400b0780c6c000141c64124138424000366240083c010000c01c80c844041d840207004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 595312634 1250 595311384 595311403
    0x80906070c0504203106030509060a060b0706020c0a02180910021201090b0111010905011a09060306010509100302041a040606080907090f0b031e010507030207031718030309 76
    0x103510b03180c40c81e01028140c4c240812121100c0780c0c0b4502d043c1913640108a814450301c0018a2034114440f41d0b03210500108010004100a641c00700302414484603450901901030480c0040318030f491004c1007103461080a80300f91a4003c0001a219011544981e00b45111858020750180500e0001c110313071aa840e6481c1e00500c180c40442d107040c044d81f40c0c5103080344110907420401050080c0108010b040a4200c820030300010725202c891491107032861070030740f24000e4049516944810701448422840d03000c03d00d001c2c0b02100c0c8060103040c801d0100c0c3d2544018041d0ba40615403200000f031001d422400d5140042d42e0191080043c2580c4400c5034440082040b500e42c0708600305000011441d100e180000d028940810103840741da0300d40740b62a0010101000d0402d81544c40b484460456079050024850401c02c1540b1827524001170780b051030841c1c8000300030505251040c0020700100b80d1010040c0281e03418119103a0301e51310f40c05414084c0c0e4030042c4010f00b031403100008004084001003242001e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 595313884 1250 595312634 595312639
    0xd0309060f1d07050f0d1101051605030a080601030c08070e04060b0403030903060c020624010201150b07060c050a05090103050901060b070f0c1d041203110a02160f0302010e0904080906070c05 84
    0xc03600c4a04001d0074105c0ea600c5103070b1110741824941c01007141008507076a000014107101d4940034040880140218144000717803510f400c089000c41085402180070f9604c030409280400c002c8505031400303072403039101070850003c01c4000034107074109031507540c001ca0140c40c0c908500317512240c0e070780f42c000c116104d180800c0f130b0420b06102c01c000c0024000503150340100540c441c4d00702244202c035903040300c0415150fa030328110740d210b02c1031010500018483c00040c3c40c041c0380c0c2079640e030341c1400c00c4130584000000c840c040090401c0f110503402d5211040c0c8001031001d1801141d103880f44411140580768680003c1c0c403408002a66200b009000104001c9080c400c0c00361000711f42d52080e121400c0328048441402141c2c810000400180c820380b0003002050407401c00240c14543c60bd80910180c000c0030583c5c001d644500e034003c0c4c1290440c0c00c000000d10098910010681c15580000c0c002c4010312203a034003480408020600300b008190507240c0350840901010b0f10341800341400040040c06102c0d660 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 595315134 1250 595313884 595313893
    0x20115080f12090906090a090804060c050616050d020f0f181306030203030a05250b010512010e0a03030207020a1d040c09020a021b12070e010303080106110d0309060f1d 74
    0xc00c002e510030f4400c2ca51005040088580d00e10051010035280241010500c61baa10103200001d21000040c0010303009070383d0b13202074003502807400070f2404101401c8030203e580369503100340186038040d00700d0780d0f242c100e0340300545c50b8000800d0100c2c160240034180a806d12000c109110640d841d9540c4144400301244d0a4a490300703642962000ca801074003029405d0b8004202400606000c0c000521500c04a010361310349101c21038005540c0008100000c85040740c00070010041803601d80d00c00c03a0302500d8040201304c000403803942107913105034410f00141816004200e110540d030b070b541c82c0000182407010a581c4802e803104c111254148003240d04507943c20101030003044003400d9201751040000d140e00213081c0d4080a00800c110403654811a590081120100c9100c202c000d005400080c00c0e03907421906207505620340504520416042a005c000d50b009294240020000d00c14222a41c2070a0003d8180704609212004d82010b40c0b80c9074005041c014120803d00c5441e540c000c003110b201090b00e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 595316384 1250 595315134 595315153
    0xe06040b2224060f03030c0206131502100507030e071707180905011b170402041805010e011a06041e171c030c050f16050613050c06030402130b01020115080f 69
    0x12440003080b0301000d40007c1c803414401d001428600010142031342d40c10200e0201c03d50b0350340d0350400d20304142c0c80e8400682007001194034140c803e0054031780094144c01d00740010001d080e02c5a94070713807081c843c8401042d544100e88141e0782d030520100001e01a44084440c0e190b04941504025218600c0c04a4503507203400c121055120800481d0f5030700c0905a90303102084400480c981300303102d001410903039000c0d0740d40c0043d00c85d0101c0c13081582d00e0316115500106030412010410340c21203084030f07140d8400300303403140205c0c00507034800c0200c0d0140c5080003044860a900903100c0d406800381500f281c2c0000306285800814000d00140c030f40294074013509203500c0044042000c074159501800c103200800e200313002c001035504200d406000384d55041d5903006183d1455442c0c19140406c140e80c0c0008200040d0740c9030301481010300452001c5201a603049140d81456404510401d6034405c826150300e658012141480e0310030b40003850b100c0da00801c001410b5440345c0b0040e80b12070000081003841e100c2d56410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 595317634 1250 595316384 595316399
    0xf24030c09020a050306210303070309020a050a0e011503090b040c05120f0d050a050c0a0c03150506130902041418010b031c0503060303040902070f03030e06040b222406 74
    0x200e80780003e56030b40e0310303045480d2401400f040c0700c014481c0581021940d6440c6151500401c0035620840c060303500030410f00100d0050055400385a04070034081d8801007424041210700880303c904690504000c42084542107400320010050314800a00600c4454184403c1c0404210340703800b40c9600b01da045014466481c03600341d482214a03041e0782580c101c80c0740303441064000d0307010b041c1c5681c40d8204140360908020316641051200502140c40c03004880d028418441401c040703000242481204120b00d0905000048600041d00c41d00101d49448481c0032085482c2c1c0e400c94019420286411403a50810310090040c041c2c1e50b000e10750301e039842c3c20b034040000e00e0b000512204041d1108404031100c600742c03400b01d8265000400d82605440204800120101c0c148014032a0a01400380c0c407041d202d640c600201903c4495000a42c46e074080d005000c0425951350b0060b41100360783c1c81c000c00c0c0c0310034070015617807a014008001d000740f2030a400c101403820b90782c007403580c031100c20741d90821802e40c48209 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 595318884 1250 595317634 595317637
    0x160305060918030d0501080106090e030c03091306080604030e0405130c09021b030d0e0115031509141203060f01210b0105090d060f0c1d01030f24030c0902 68
    0x15119400601000868041e624440140850a640380156444d041c410903004064810a900188041e9902d980401440c5070a00c552110850500061440c1c050700d089220340e40d001e8504d6080c42028030340c403041c0d5a120305d03502800060807103200b500c000b441c4c2410080d00e40130550004900490502c000030300d6202d15140c48a032080e038450b911114040c20402c403400250010fa04441100c503075050080c0302000c041024010010341248003141c0d46000c040200d09603041000d00b480ca070f00600724184001083c00494610240c1e81100c00070b800482400c000c000d01c11003081482d80c034061107144285c040301802c010b5205880c1584d040642c0c40360b46004640d4940245041480442c18804030303101140710b0b03000207424210500d07125040041ea1000100141040c0d5070884050717940d4044400c014541c1c0c007450703064040d54248001c03007919071a04074446802c5440054101035a805200303040b0300b120b90050031040000b0f200c4202d9035204416a8180c03201500099a000581c3d0b030700000c140c2c00703d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 595320134 1250 595318884 595318891
    0x1b0a1703090706120b09100807150801060c03020c06041701060b0301060503180a0b0a020403120f09090f090602030903090909120d050c0705011b0e01020c0d020f27160305 75
    0x34a1418a412802c0b1404e030603001d21880301944035800c00c042541c895800901a5500329106415245000d1115240c018142d120b00011302005000c0080342d0781080c60a811180c0504014181d24614501281010140c3c2e030241e50041004c6004101120180340c0c0042c4508038030020401d00d9143e003100c0d50240800d108103030019004000241141064655200e21854800111f422403070a90381d44039003200040f504100e5041c0d000c43c0400900902ca800350031800f206042c6220500003001c402000d0704158022107980744e8032040c105003e41003550007540010780201c0700b10344a0500c00ca04035242c0d4419111301d445080c0844c0440c0c042070b00402c1c481d035150f00300d106661818404030120300c0903203030050183c41c05a40620443c80800c9081c029061041c0700c1960a41c844042e0b141d014281c03c51108040b4115407264000c5000c0e601c0e01d200d401e18003901115018940742503240019040c1d403a6011408090f120144040001130715942c0d828040c030b80c00800744100b0a4034400803011944120b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 595321384 1250 595320134 595320151
    0x20d0f0b150f03010b130b0d0c080a0c05010f020c210604060b1504140d02010e041d0105011403030706020310120c050901051806281e0909030f080a021b0a1703 70
    0x400c1d2441c8a261b090340843e0511344042c0491000740000d40700c1071410941070b403000c1c8030b903000910707c1c4c0104821458207401522003401c0800d000070201500940e214548035489025900c13080c078650064250110081d500ba41c403004541c1c02d860b042c5081c1000c0d0046030159401688000100701a95490800f034030140c4403c03803d0103000c001000c1c02c1205151a24400b40e044c4414054040b041d81c4580c01900000440b009101c900312807148602800c5802c141d0200f4450540d05804c1c8009940c007000312108181c00031405a02c0391607030f00c210000c042c1c0e0303a80400002454008100104000800c6001c1100e00450b601d2031160380e00c00078404603c00e8035100c00e4100c0546000a0006e00e00401040d07240d40082d00c0084100b03032101d000c4251a409908034802105610000304900100b040c2c420010305075400081c400a80c00d0b41d000780101c84038519080500403208001590302c03049a041e00c800d0300740e02000f0080c0c0303181c0100c20b60300c4010000b402d440440c580b0010082030005070b01140d00410f1034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 595322634 1250 595321384 595321399
    0x6050a0302090105040e0f1e090307030e0f0607030809060901051b070f060203090307020306390702031e10060b0d020d0f050c0c06090d0804020d0f0b150f03010b 71
    0x110000c4009522962005061041c14800440c1c070030140510350b403041c010081c0c02802030526116030314400c05000c141441e000003507010040f1151020059800240d40360a100c42a5011080050010000702556075040070740860643c00f49903003c07140c203000710b21150950b211922164101401d0b1503084400c907020320b10702c0004044205010340200382544c0505000000d059090b0303500c0d000d0b6030013980d503481369038400300301c04056280c2481619008003209030034480154002e08240900d00712051695680070b82001da82d003690100340200c1d81000e074010180e40c1d1009558105284000981c10020715078407401103c200b800a151041006888074612441c3c1410800e02c405000ba50011070100034068540201c0c0000744014080c1c24010f4456242040d01c1d0400d681d040303840d141e40140610040c2d40400030020305d183d08100341c0c0342c10030380580b04a500c0c070750385003050764890000340401040d49140300c0400907108243c1060550100040720180c520880001c00c1600380c5d28952905640314a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 595323741 1107 595322634 595322647
    0x2010605030d0e0f0d170a0507060b180c0904090f08120601050f04050607110d0b06030606190e060a0509043023041a070510060605 58
    0x2c00d0725200380e03a2041500000d26210645084a0145407071428100600031495403034000b10b12039207001c0e0340d14035000c82c004040e41d1200c032040d07403030301c1c0b07480c030880d801d4034126100c0c0525950410301d00070345407200301c2400700b940e102201117980701e5a120001c070f00292000801c0d1803400e0041248a44503100d540300c001540d0b5008041504011040044840354840d81c0d041d20140c42090b51029110541442c22050346880d25003c19400350040c200d0004008030b40d141c2c42d00c10310303040d0203031480ba4540000b0700400d03000c03280b011003035250785e41c6050191641126034258064002001119040c3d03540000c50186501075030180e903594140b58445100c83c0940c500807100b00c0d20044100255240060024503101050ba2520700c544c840c891065050509103050700c0c050401c0252002d000740b500c0f8607040f0f0950082e00b003207945005601102c04819994442e503c102c2d8105d40301c1901e00030 = true := by decide +kernel

theorem cover : BRFrame.Cov 595143884 595323741 := by
  have h0 := BRFrame.cov_init 595143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 595143884 ≤ n) (h2 : n < 595323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
