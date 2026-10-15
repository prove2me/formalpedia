-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5322
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:29:09.944152+00:00
-- url     : https://prove2.me/submissions/40b20aa4-1adf-4e8e-abbc-decf3d4abbdf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 957014388 ≤ n < 957194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 957015638 1250 957014388 957014411
    0x5012403050c04080f0a0203010c0e0307060f020a0b0720060c0f0310030c060917160e060406030c120c0b032a0909070c11010e1f020a02131d1c050d 65
    0x12001007840f003100302070001c0c1b11091042c1425558850485007e0002c0000b40b04d0040c1c40004041c0e04a5106180078048403892038000e038100541c4040280001e00c0711000c0000043c1c0004141401c00084040d10455088041d000340d101d1100761100355850204000480075a044100559081a40c440020f100759a580c3c0d6240025440c0c1c1e40300c0c1022a201c00303070400001410400c10524140781e0760242000b00000710318559880d000d0700843d12000c5104000c43c14684030303540428003030f41d8056080c0c03010585a038446801110b08000c2108c82100540002c0380000d41034069030b0003213154039a0100020603000c40245030f20f404e070b001c8004100d02885a00340303985d24020180c0c00b60000342c65404052840303040081100d42d60031603a50512180c2c0010072940e880322020380503100d0b00f1442d4040c03222005941241003420b00e040196001001840f608804845d42d804110450036080c0300030290002204107580b82c1c69442016000652900510002a80140020702c210b0700f07207220001e0340a4000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 957016888 1250 957015638 957015643
    0xd02180103051515060304150902121b0109030f120c05011a120c0112111b0d1b0807080d0b1e101d0d02060f0a02010c020105012403050c0408 62
    0x26072059810303602c5a50300340c1c900424100e0f0310b508040c100e140811118110b80c0030440c113200251009290115442d80400c034000e1580c08010050b50041040f02c101100f001069030300d00c0e50340c505103110036840706005400e6004040c00030449504c0445a0600c0226480e080b02003078400720700d40d060043c11285100082d0080c41848807400d403a0b03010403160741c00c100500c82c0000c501c2c0c41c80101d40c0d2100450300a9603812900d04070071601a010007040801d000c4c0e50340364039400780003403101d46280502d410280f008000328031030720f042e00c1a50b515040101c40c9010b101805025101c05071004a040140ca004070b4000c0b00206404d0710405c0d40400c40c1a08640800d5000c80e0301d000e03000c030f40c2d150200d0076149031500200e80545141549002c5424001d41003125514900c0d81030581d101c1c1d42c5002d4440f04540710003041c5c6021086107c0b14540399810080081e01030000d82c5075210044d480d1a001140f1a1525810700029100001c801c1000710701008080d8000e007406407503001102ca05200004002c4401c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 957018138 1250 957016888 957016891
    0x1204060b01110c1e1801030b130305120406020415030f050606030417031f1203082a1e070803041214030712060803161406060f010804030c08181c020a050d0218 70
    0x2000d045c00603075072540c144035210900280200e1081940899150042a404010307203d541001c004084040d440d680380ca14002d10a07644031048d612610100a0070306605540550500c1c000e5820034800c0f03a0f60074080140e103210407103000380700c14000042d40c000c4840c003001465010035031960702d540c14080254020240d65080d4011f00814000304ea4900c01c041e48081081d40110214859101340b0b1190001c070b46107d0f4488402e41c072445004a0036100070325000480480f645c0101852903560401f90030a0619a0310844040d02c440903400c00c2c64990a119000d45400121061aaa403d540303400750112030072040340f1403640c0300e140c40f07800100304a04140010302d815140055182c0c074031031180c60032030b041e5042910400c155030000b000300700341c1d03880d14030701e00c004808240fa001c00603a5803860161041c241071000a05400d001044048203800f1310104049036038411252520141d81c0e0390f01c100e03403042c1601d80003904140d1208003040366040500c41400800d1008103a10074540d207500100995100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 957019388 1250 957018138 957018169
    0x1b072d03020a0b0316020114010501260a020a091403031b03090406090f1401080a2a03030906030e030a0e060a21050f060102060c0a05030c040b1204060b01110c1e 71
    0x20600c02191070340c0c0c00b02c5e2840c00150009102c044656805142047e205107d21030500c446070031103ea54214112201c004404106003144050a0400c034207002904100300c0c0701d0100f0000030300482c2a41d031152445590300d4000300158a0101d940c0700301c030243c0210000c01216403009100f01509a1740b90301400002d04909000054400d0390882c0c00401d4650114020700072289480c01070000707400c00700b221050590412140307540e001c80340462900d0800740032a8000b501c45101c401004041d8070100c1c2004030750207940c2c280110302c070b0030302125240d00c680c4c0000b40c0032a030000003581307250400d4005030000c0304440c1801c0d81c141011300141000c2070010b00203a252103030744a041028a47d1500d07511034002c2d07001e1008180e0380c54004582c024503c214240f4400340300d40800028101c16510007118050184828050b4482a4504d00c00c003201c242560111074880c24a688242c0c95403040804115400c0c01e0300040c0405c140c41002d002d1107584a12000c0e229451038111040d80351128000a0103580 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 957020638 1250 957019388 957019409
    0x9030c1a0a050c04060e040b0f030d21020307022a15030a0509030906071104110f03100b031b0f0d090c0303110a03050a0e0f0a08031b072d03020a 64
    0x3070321958110880341d009280da40c4075030303042c082805250380c030030300e01c41e11140140c9001448524000016801a4180e441290f0611a1100c0300c0e44081d40200e80d40b411545901c612410124646501e4080e0b02044805070010b82c4280114001841c0800c0306600f9400c0c2a0a000c840c03012401c041502152040030800920600105000043c02c45204550b8080c0c040c001450502021000180292181c100d01500414070940001c00380d07034a07540213102d11410850318540d907800440c140f44454004541951403c40407040c0010b11f020300c2e4040302c2c8601c3c40500c46040d0103140e840d00f03800c5034100fa000c81e81050021300800c403003440e680c0316066645028845c216441c07803941c580101130018580c0d08603500c0d005800f400000030f800c4010f0b0745003050310b41008140301c5198004128492203600040e035004003034140c000340310ba20101c0241015201918986421800103d0487c6d48803018031545503c00b8030650403620003250310101c0b0020107041840020b0140e501c0e0001120304d10984c01c5602d942 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 957021888 1250 957020638 957020641
    0x17010906140d020a05150d1805160b191803051c0924020c220b0910170a1704060318120e030102071b050909120d09030c1a 54
    0x41d680309011400d580d801c8651181d00001c542c0400c500d0806032140500600d6041141ca4208a05209503182c101751042d003080200d00440d452136070713166000000d03121400384c034688610320541c20380200141c1d43d41850381c03864422010304c0c0303005600890b80f181081200c00c2860b00003045800e031421f001103010301d005013218403a03000780000741c602000c2e14405100050703030100080313030030100700714840c10010f0903608407168910400d03410825200c0c8910791101da1074480d03041e0030945280301a17005203041020415154140140039924109a40c491410080c0b0b5004002c0b85441c80c4007841044500b5040e513295080ca0f55400303201e00c60709003101d0a402e801003000c0c442c2170351504c034409e08a425888810700d408100e803034800d0342304014031018040018418504a0940782501101d040070b50210319000100d07a100580c00c0c1c2c2c00d0260050a01c160a0b40c80454103a400008d001036402540a050b07602d090000c01310b080040c10509001c0b1705000801c0880d20120300b0a2000d240600e62004062226 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 957023138 1250 957021888 957021899
    0x11107031e1a1014040207020316080c032d0111070303020301090f022a1f0905152e0f0e07080a1b0503040f020415060215130b060117010906 62
    0x500c10000c42240124200040124060a402594048074581e042090784132a400c00880c1c00392083d80d401031340503c200c0907000400c07041c071101c607021540000b040e240f140421204140d116492000c0c8008142d62014286500500c4140c0750340c1400441d80c00000d41d0000000184401c0d04504e00580200e0f40c04401003021007454010210f4090f9020401c51030310b61300c80320140200328025500000c4414014010520390340400c0114060481751000f503900c220124000e9014108041040300d00d07000d084c0f24041114240c400c601d0007410300003001d5000340000003851211424018000c1c1416002e0b60000a0100c20a50789202070484034080c208146000c10b400f4203046d01c0034203031000191601e0060350340c0d400d22003280c64828641d1316000c2e0b82c0b80c4440c14024054502114041d40c07051a100001c20740da080b200d0400100d40c03544e026a415203045061000405008884400080c0009a5800d0015140c1c0c96540d0b84001c050428412171550000c80c801642d000343c000410065503210144003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 957024388 1250 957023138 957023153
    0x506070809060f01050a090e070f091e05072102160c051e0915040f0204060206071202030906010506030402010c050109063306030905070306180b01081b011107031e 72
    0x18003c1e84220b44003215490000884d1440505103d000c080399603e02503554810010312200004020720324806a000d0380b213056140003000e03003d4180c48514091604c00c8440300850080c0c03840b4250544515188109041c516044005281c4448a8030390b401c01c1012540b9908511441483d401000720400081c113060500240f12460000001c4d200e4820310321100070394842c0311980e845a0703816603d2610032094800300b0050243d041e80322544600118012458a40c0020000d208080748d5580e40404c1c28111020320491000759003441c00b03030b044070006000c43d00707100000755042881071411120b1150181c03203841c21147c40c036a00b00d40c11034035148454140300003a880300202211000014542980407031042c0c14034001c2c3d21070384c41459110030b08403040c4882845000001c6420581c103000135004a03035196544000a03d007210030b007075070704000300340c0c000c000500f00c1c0c10348104002c92100c0300d06040151049803032070703500c0c0380709121360b020201c0020100801e030014009450040520780d0b4041ca050603 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 957025638 1250 957024388 957024391
    0x10e060108090d1d0d050f011d0c0904020f040203040b07031a0a0e040f12090603061508060409083c0a1d03010603080f0a18060c060509030403050607080906 69
    0xa0410030301d8400d00001e010040f070302046002e081d041200301524a010311003401c10411070581e078441c21031220b01060200100307422044050303c0008000231210070018080f03241d5003503482d0049038086928075015081070449581c00900080041a450058200007000e07030348110340c01c950308065030040c80701154060040038101950b66030300c0003482d035028010800c80c000c20300c00c84c542c0a45010128050180040000400701e4002180000e00484030501510900c0e9a2040d640020f1030004e00294141d40504d0303209034074a03655100a420b885000070040030b080030040c01e80b0344000410803034a891540c002c0042c5403c440e0640b01107402e8240300c6540340c102c0e20718041c2034401c608009542036164040700041c070ba605800d031100071000380040800c1c010081500024041034000070300c0c0360b46541c403401030408841940d1780e4102400b0042c100c0303903510300c280c45014041448030200c03200003621504400d601a1420046900707044e62034498600d450010342e1010082100c841c18010070007024017555 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 957026888 1250 957025638 957025651
    0xa0f061d0106031107020f04091a04350a090803130e010504020c070e040f150e060a090b060f1c0c050a090213030f050f0706020c240406180306060e010e 67
    0x7088401d40646500c100792160305c0700280704030091500010307950f481e60b1008450680000d224003014607004a01da000b45419142074805006d0f10141200341c142c3c07040c020210700008246048040c0e0052004199500701074880d009000420070042542417007080506038620b805906441d000d860315030031a80700001a00030b0780c0103500402030540c2ca40f5000a10204032020825411130f1695107040803c040c0e4001c81004280610b0110641503a6026800c0414104000c800b918000d80316644060115014124000c081c00001d0000401a16001c10f4015003517030040c1c007001c000707542549010710032800c00c2c0c02180c20341100b00c424072803410701703803050310292200384400c501d8514042440076030b00803a4400148881c0018410a04115080c48100240b214040c200e035810f03511a04080d403620405020540140e2020603c800aa0711302c0d0203418400e0b500d515003074074103070415a0460f0300c41510803e50078102011680000000e00911030000240543c0d8100301040d41002260f030003101e40036020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 957028138 1250 957026888 957026891
    0x30c02310e010b150f120c040302090604090201080f0601090b0c0102120c0703020a0204020a03141503010507050403031409010348052703010f0b0a081c080a0f061d010603 75
    0xd50381d03680b100c4c00f85421400b64480e4058a07086201300080141c851031842c0c0c01030381085030902c140c031201100a402543d01c201d07502111075a501c0b050100711041031101900040036403011808011408003520740000c010300d0040003098803070000d4079060740704202c03500f142d0b03500042000c00c00900d004030503044242c034420103143c560340b0f4a00030f654000504001e0312641d07001035450031890180c2d00134030681c034002003000315070b1400d8020107242c1100c2c9072480e0300a508042c006030620348070f60120b40a803079054441c00188101403034a02c11540001c00c07030034145680c5400038151003c2612480c0004240440949507000100d03a04001100c511955140300043e50040c1082030b681160555007640071145107040400030a100100a081c8200c0580c1e8240d480c01109050203e42034104440d002c80030344005004039610201e013030303859075046021901648440c040d240b0b05031059040c0e60300a80401c002280d030942000c80501200c0295101024483c4005060034144130314800003801440c446c00d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 957029388 1250 957028138 957028151
    0x801080d020c0d03030c180e0604150b0f030604110c0a12050703090e0901141306050115050702150c01061413151406070b0708010509090601030f030c02310e01 70
    0x1140c0c03c3c12000c40020141602c90446441041c4500501c070b486d10094012491b5055880c0c0d44010b5020f0156401c6001c0d504151070b00c4109410003c40b80212200310390114540b420306042600e864001401d0b03e607100e5124140b248110180c1c10144c83c2e500740e014094082d81001d840c00324101180b1601e02000c1c00380901400c80400e800c0010315007110180c0300c80030010785c0c401c1180c6004006084030700c54103c40c14014003407813180d400740c000340c02803062a041106036240d00084549404056007800003a804002c40c03001801c100300d514900c0208600f099080804080d00142952101e410214111040030354441075450b24240d0384503080b00b1420b007000180c21000c21034801c0303d40b900641f004040c3e036162148444d1100c1080718001030308594054054100101c008004000c2846002d10500c1c0240c04600117410200b015412260b05c4154100800001d40e810341c1da10414a1013684c7c0400502ca0301240da480040182c0c0440b03000103048003880b1120780c0079008840c0900d031441c10580c9000b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 957030638 1250 957029388 957029413
    0x1e020d060f06020c130e0c0904030207050f01020a1502070305040305150402010e011d150f1c140f0403080a0f0207050606030708070315051005030a030903050d32190801080d02 77
    0x41c40d03c07a00003da03200441c6c07228031031620342d01c1d01d00225440c5d82c0188942c0101300a15902242940035650210350100700c0e1008600120b956850240024201d40343c40401c48011b04520b41c001d122440c440c0c2811820300c1e40d0b9440702805e10290042044c101200d00c4100021503034000f81c0921552000d003044400004007800381a0124514001e007030060f40c00360340c03500505642c0300c20348400202814119580d41d007040d00901440d01322010551f003650510b5a2020060038010b0030750f2048804100c483c260b540d07103440031a900390000d4552510640d6812141d01b001040b07000400107140240c0091103641814000e251418025510019598110307210078000241010b92a900907804040b0109958841301601041d0034020351042d0b038141714a8100d03004168001e2807540072a4001c0d02078420070070701c440c010346d2510909442401642417200700380000c1e8094001007005c1a10203141241070000201a45001c0449410300d040495009e0004004150b030401038030013050040d1001d00085c42c0d191 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 957031888 1250 957030638 957030649
    0x70305060a0f0218130f0f060f0602070b031605071a1801060f060e121f0f0212010b160b01290906121f0303110d02060106050d1e020d060f06020c 64
    0x1c2401d111742d22011200140307035a150480c0400303042c50301e000c00400c40c00004180081c4003a101d17800d102d8080480001c1c2d21400807420750229880c5036807061440d5600005c841c0033750004180360080c000c06110403404205013540c1e00780a611000c0c0c2d8500355041c02110041800c08840700d03c0715aa0400708207000499003c860031003103451074200001d10340c413114005480b045143c1c8080500748030b100078450140f603001540c880c030890320080800c664074820020b03406902c039031b03c085041032819100412070161521300404040310381a660f85004400c503510301002003400e038041143c03a100c00412680441320f54480814021210400d28034024401c00481d000307010381c107000c01155810000086c80420000b0f02000c01d51841c000241e42140c89190151030181154204d04c11441001462842c207400092060b0503915142c441c2810320384c0e090712400c050030040300c01132101e035120101d0038541003203070000e4103c26844090104103641441641c4c90101882d500050840d44807c00000312901d84 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 957033138 1250 957031888 957031927
    0x9050f0406050a0b0703030e0a051f09020f060c0f0601141305010807030611041a120f090601260102040b0408060903041d04110d050609160806150f03070305060a0f02 73
    0x130900d01c4d484401030b00b400e0303000b0320013000304502d54000c0c9c2426104100c00400d070780c2e040c4505140e0351120310459903c19011070303420100c020b40150045099003010325083c0d000e0460303001e03180c0864030010f030907039015800d10070b0072303804540007005840382d0b41e032586000b46010040d811010b6003004cc40d0b1608898070740d02d001c18030001d8a1941c0c1d918115020b600c0150850740942038496016010410107490701c040e9611108040d502200a40d021036072020100310300500403400c040050480364204209007840c0c104040380f03090035010500300c17142054028006840148880e040c000d031150310700b00819040c50002031441c03800c0d4200300418801001082c3c001001c4420409618005a85510380045400c06d02d07960300358805040c140450800c01d0000c0e4140c03265214905540d12080b101c5034054480390b035800b03001550b403c003c00045125220610b001c4070a50014498480c43c1c0300300001c282004065082072f10960445400c2141d00c40c1140648900d40d03800c210118944203036840300c058403011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 957034388 1250 957033138 957033149
    0xf050a0f0c1a16030903081c0f06031a070320120703060e04030e01050d06030809040606050406021b18070207090e0d0f030b030709050907030b0903250804090c09050f0406050a 77
    0x80041403044c58890300c3c8040181d5030080c0169551510128071011449080305804005410308200071411061801490102e0360701000680d0f503070f60403000900c411140144000700b00b43ea1030203204020031461490aa01020403410f0316610108900d0030703108408010104002d2508003030040182e04000e14100c4c1e030040d09031030714002100c90040100c034584642d103404140b031401c0103404010300001c0801440c419004031010044a0303900c01c4d0582c2d050250b4070804000d82c00c4a03140080425040d140420070120051503c5244005e010702d0505180d010f03222300b40180d2003c03605008034500c07807240c0c004800e40200101241d08100800918070482c072000e01d8105925960035003580c0e02c0411940b0081d001400c41440140341c104004d030b550704441d2105461880c01d0781d01258107a0401b00458522a090455191481d400c1007900ca240107040d21085030804020800059103060900c0340520700102d42e1359580300b05142c582080821202030240c90f11581c90800c0401140e030b030700c072030150885c1c8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 957035638 1250 957034388 957034417
    0x50d110709060f060f030e070501210c0512100f0501050c010e0a05010c020705010c022b050a030302091e030a12030e100204050a0b0f160f050a0f0c1a 66
    0x41012102500308811503010380e0310030341400008641958450100b0003501c005945007450b14034551320442c240c480076810110b254001c0d5400b030055520403c003c081d0b081480c0c176601c81c1b02c4000b10f140e4040303c0c103005d0285d001034004a411071118410030401c5400041e410741481c0554200568011071002074401c040c10300c400040e01e5800d0740000e400c83c922500042042e5400101d00b401c2480c040d28403000140c0040c00381c58400b080325030046515810300f503005807111401c0c1d82ca00c8805500c80485100782419010420140e0000620800c00c0580d0a44690780158540f200b010034058103144640010034040742e07a5480f80a5074400140300001644c20089108182020030405c0c0e0051807130401c800c40b1030280c40a0100c0034490303030b0001c1017140d5059540241c0e00c1c0e620320314490701340203a40c48400700000400101651210307403485e04600c40d002760501c00080605a0300c1d40d2408500204c00c5030080061341b0101e082c00201c510340401007484040100305105280440b00c014810000b0340c881c0310 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 957036888 1250 957035638 957035657
    0x41a030c16031704030e0108090d050f07020604150327050c091005131b0206130602030924060103060b46050d0b031f0c11030a1101050c07050d 63
    0x15225502d54009482a0206a4030f5810103003001402c00141c50b4403203020030384510204249000001c0c11082e000455603c960030b00b008070840300c105034007941c0c050364000720500000c900d000e6002941140c0d0030b0340b038800144d0318602240140710400640802600914404207150215401041c411544a011180328140d83d0380d0400b182c29141d03041e000582c100c484451500c01e46401540301d00c02c484154110400040a100000c0b681c4910440302010b6100c58400440c00003600c0c0c2e009950480c000206842c005a10207441c91440c90f05001251300005401c024083c1c2542c1600c01e19000e00040c4c42900d2900e82070b25156540c06100d4003810750b1620030454820450054411002c0400d08000b8420307020b481c0d041401805600201030083c140386c40c1030001d030110310700010302d07013901c1480c0c01c0c00300c2903030340f1070200c02d0010305101c2c007202c0610000c800741d41480d00d804d0004242c140340316103c0d03c0e1300d0712412049600b1035000070f02102541c401004101c0200e0000141c04c9182080d80c54140203a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 957038138 1250 957036888 957036893
    0x6030c0e090705280e0310090c030b04080405041e0e12040521012c0609060c030901331e140105120108011a03151602190602041a030c16 60
    0x60020303100d180131401403080c4450388040c0e403008085014030300440850746290648101c2004450041c880244900c4444004000060f41e11515640c080d004802c41418140d4410200b01075941d4032803080740c019010210007034104440e2140d14980a00d800080051201500b005002d500c12030142d248149081e529040321050780e01a000c0c3e4250300718000340841d5500c56441b450300c1d02c080c003c0084d50103900b0314001124000007105442003004800401680d201c1500b040c0459001610006007552201511100003084003a0000807091307681044000d113103079151005090300503420213040f800f948030705034080d0030030034000605403852203060f4403180d11395100503149403007000710007411407203540c0c00042d17102419801a0503050200d10969074420186c0105034546400440d001c5c440c10565000c24418944903007200d0200c420b83c0125010080c04d654522170300c5204500407128150009000d0100d01413103040c1c0910590020541803c60910f0f018070720550150001c410403000d0110721103802d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 957039388 1250 957038138 957038167
    0xd06140a0b1201170304092903030703050d0513050a0f1106090312090a210209060d08071101110106031b270c140703032415051c020f0406030c0e090705 67
    0x70f0040b0347c010446481c6080700403c03400b40341d4111000c092140461808241404400c0320190766160341c0b4a85040b5101520800514010b0158240e03010100700c100b0008204001e108612030050110090090445c5403014144182040d010700419040c00001c01c030b030320000345001861040c0c2107282d4403900e00801148400e402580811440c1c100304a0080c4e0701000b413050310f1000ba001b601e0720079443e513a50b42030000c0300000e010018900f800400c00c80011540d031543c8804103c805140541030f2801c2207a1082c00d607a8541c2040d030b905112030180070100311a1400420040c150500c0103054450b104075992000c1402c07400000c103003615001c142100b00e05c5888140c0d6a880380020040d11200241070040060a03038200c2c410b0b420300e50701604c5041c500070743c2c4002c0448290754560003070b0092602c822241500701e41440c401e45681f004030000d0341e102a00240c600b25100c002ea4588440c030b804401816124600c50301702c1403020a00b00c01100307468041403d98030a1550908a5071181c0c90001c000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 957040638 1250 957039388 957039397
    0x6091208090d03210b0d06020307140d021201080606010203031803090a030b071b020f011101110a03151a0a1d0d050606041116030809030d06140a0b12011703 69
    0x25801940c8485003010540c00c0002d190a44601c4e00054103140908140d04003124480154107500c000040c1c100000196540c0007194042000d1a00c07503440100401c0c040c0c6242c01c0f08402a201c030782c0110b0082c03d42c0c05101d00745401170448200501190401a0020b51240f0014200d5224604084080d002e002800c00807560131100103820a80c1ca56501d08080318110f20a483c100002000b00c011003030066054000f04038800e400415810352000003000650b143c402060010039507540781c150985800c41405c000c0c1c40d118604e601d0200d000ca402070320703c4180d181c091300031403510310386507030141800e41d070180917100c0e400d00745d003400e56030b0f4032807003461000b614040348035294031000074031040e0b04020000c59401d001d420241d5060014a4404900c0081da0040e00302d1200e040100004941c0403d12503400c258221f2004401c2e00c1c44e1014a0400380203460391900814841040343c04107101d00d0400d580002c6c01002880300c0241010340711100e640010106105000e030800e601e41550041600034003c0b030707 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 957041888 1250 957040638 957040657
    0x4701080c180d0503030c13060507120e0103111c05070507030e0439021b031f02040f170c01080f0403081815010504060504090f030c06060e0c0d05090706091208 70
    0x101e07103901d0651000380e007c5d800110050544114840d0005151b4042e03000c1e15960350f4402d041e040c000b401c808080b612802d20001443c10561107880c440c81c1e120100300240402d40c1030481c02403049a070f26079000140c0f08090191010400b0401c15100466403041d00d4801c80d00381110085a15248480003602038026180c603020040c100595504169900510300c049002c003e03025501c44c3d546407928802124603020100b90503802199030b44e200c0240b00821301c4007084450318010f0809440d0441101c065400750885000d0080140450503088000c100f030004000017464803064601d0040c05031080d0303200140000301440a44000315100b4007a02a03c4070303015222100305d61112a4601c1d005103650400c0c483c043c0038920b810702c0400d89003024000c10000c01d401c03a050807001d480945e01116a01010070081c2c0b102561184023092044240c04403d004505120300c0c203868140154035030045482c045c00000e06648483d0082200d680c2001d450030403154440c071000050f0205040203542e512500410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 957043138 1250 957041888 957041893
    0x7050d140c1507030e06040f090b1903080a0e0a14040902033909150111030f0307050703080603150a0b03070e09030403030f02010501080c044701080c180d05 69
    0x85020901821000d040f469000380d941d82d8045907800c0602c6094444c501540d284032002c0c0100384240003c0b82c0104080c04009041001c151290100203d03440c4020341040302e00f00400284040c61681c800350340e0803013840840b184402a0728000c0b259070a035040c071100c980690b03119801041551b070103000518102a20154003a20040c04844550300fa041079084d4103100a551004903460b0b0505a200f0761181c450174214844002e0781c8001520440340c00c0d007022003a44810000001096018000346005a08035150782d5281c4c41c0c58980541005030081a182c065070040c40d1b608604c072058117096030003d00460700040d0f503400220200303007803200e99001311040a4100050046980000005104681c000c0d5a0f060ba211210702c0308a0980c3c10030712501000364820451360400386020350100e005000403081c0444402c4400d07182d503580740800d062010100c8a81d0420240d0140c4604041004803424a0b1050076894231006c1d015131801002c0584010000390a061142a11410018100f25411508 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 957044388 1250 957043138 957043159
    0x101208070b0f22020a090e070915180207050607050a0311030115030507181e03053c15090708030d020304020a06031e0527010f05010807050d140c 64
    0x50203000540785000e5106803904800b580c0d041c0c10200f0301d82c1690081c00807110720300e49031510340a8110000000b004d4003520750b0018207004140300b2034201c00d0030003408102241c509040700098000c06e02c0720940160040004e080064004250b83c0c2c1e0001503810111303103506030741400b100240305804441d1030584002001148140380807024503100245590140f01e56a6820000c41d41000c05980011860401810034440d801c1d1102026038200c819503030388114140c1e00e0302c401e0b18101e003002c0a050010300311104118020000b49240c0c04038500500c5031082c22550160302c9545041c0500700034440c40b00900446c0f0700c50010302c05c58002b8540407044a860310392107102440258410b0303800702d100d0312011310009240ca001e4002c1007010541a82c100f8052103c000c25070003e84002008441d08540307109040900c42c04a5512008140d4102d00006042e414a681c0300100c4006800c00c003100e50010204008560fa0444a00c020715032008850000e0252000d036185007038481e4445aa01003200c41 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 957045638 1250 957044388 957044401
    0x22050a060e0306130b0f070e2e021b01050322030224240a09050c040f240516060203242d01020c030a0b071106101208070b 54
    0x38004581c1c1c81c01103080c1c54068450f00c81e400d42402e000c84c001400c021024000031105124016021341c440c200e81042c0c8020341700344000610400c2c600e0107a641d15201b03250030714054660251034142d59609400140300c211076a46c4141100801c0c020043c1c104580007000440c0c0d00400340c9986500504a02c5140c2d40c0200b620b0069202d56000d2030b6080c50308084039101e8010407850b103a1703502417201135400d05150080111101d9040380d2065240b030704100c20410000310b004607445014424561080030944841c28000c040a120500e83d02a82441c50704001c41100301d0400c02c0c1c200c03000106414400e03600c80f4552009103c000507171401510341440442001400880c01e4240d0040c00c12100c0a111400780d00070802003444000c655100707a28448041c01c212400000c4141602620705004480840b000c00c40003e00c0d00500800c2144c2098125080c0600250004005207140c0d000e440580704900e056880c3c4061000c46200e118003d26a60b10004103029a00b000c40b00c000d500301000d561a031030000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 957046888 1250 957045638 957045647
    0x903010c02010209011b0c03020d1a0a0203011403071a0c1f0504030314091005090304051201020a110a08030604020d06090905011a0406060804020603070306170c0a0510020322050a06 80
    0x701c403564081b0b04120206100b00a030555200221035002e900c84080c14116003c0c05a4101e10b1101251290745a030002c5540f441c0c05a81284107181050016a903907040c00320010908044021079030295004260920603000c100307042c0d0741800001a400c0380c0720360720b4030b2449142140c15840b90810182d104224000041503030000d0344505e0182e03d090181c030940019442812a044071890040d4000d090000a8012640c1040e40c101910034101e030f040c1030300c5070b00040c0bd0360614800c2c8003583c0c0d40020341d462015005034080840380c2041020300444c08c0c4603100d1842c0ea00c401003509115a900068413451a00942d00c10340140045e407404004400c01ca140c8030f8002d014503107031035594030300c08224160507250030701401c000d403902d40d6500540c940b0382d5424032080d0b401c0908204241a10b910010541420b8450b1800520116000800660b10b098061000b2a052901b040d40522030200340c0c0a0459000811168800c0c46628135696034003075071951868030141500283e511000e03170140000c001e03511 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 957048138 1250 957046888 957046897
    0x807080304050d140a0e041109130501090f0b0d0609060207120c02030f0f0706031808032404020921072d0e1308031527130201120e030903010c020102 66
    0x50b03e60021000c005501c203441400342c040540c0000d44581090303203460901da00700c0e042003603132311850341d060408450018900048150240081e25a58801000a860301d030050306078550122404005003080e184c0480d007098140da9015289644901d4000104140c81d81102c42240c1c00029940d0460300c1c51400401c1c0c90032441090384248606c8900d40d0300343c2804174090660002a60017400450314110082c3c010740340a0b0355030390105032098443d1003c100000025031081c0030004140540072003a20420500b001c4100e615070007503105028113461a1503900c4d1800f03c04040814402600f291111214a89001604507401d04d01c040c1125001c1480700d8048440400f154010001c46c03107480b5074400ea20301c3c400700c40414048404c403140340040344081c00117581140228102c2003c0760443d20104620140384074896244100d510102510b000151054603084017440f10302f825041c0340f03500003d1809803210b5050700d0b0760307076991020300270704504200302c590501c00075000740005103503284064000d402 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 957049388 1250 957048138 957048163
    0xf090504030f08012102031501091b0504080c06070f1502131d0f04150501060e1507030e090c092d0d121b08120103060609061d04080708030405 63
    0x18400c5400c14110f0044040c64107030380380a030004110b004646540140d4419103641a6090f000300454000500500301111f4041c00b03001038089108200c50400d2003500d1705005a01c0c003000018003041c0f00c48030010548000002e070444450362110040d0610081030200ca0000a010615242440c0c4051003650040c000003003030342c11031803139490b13540940304604400c034004101c01400c910300284500d004103414070b4105010b40341d40825410340d1201c8000b00d400030780010010441c42100410946043e40700c44502e0400303e0416803e05000b0b507000351014030f004a41610400c689c0000410018501c400c1e520307400c00090221440a4803c07c41c4012500f9400514503403a00042e0355050303d0403c81003075824203600010085138217100c074601b111164400780c9507459160701c000070140420368000150070380c1c04074255400f605501d18a4400212400d5900580500313050200801c0301c16008c080480d2f4a140d80300314074030950b0b5285032401c607134411408014200c05000c020301042c0301e4001422001c040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 957050638 1250 957049388 957049397
    0xd0c08010608150607150b031203090d0516110102031309091505060d0b07031518140903091203070c0e0a0b040213090e120d0b011209050a021005040f09050403 70
    0x115492581000040c1521006400101c10031075580003419602d401d0080143d06d03800020301000c854002420081080d00310040c5d0344000c014003400240c10300450031864583d0800c60320300340a01d400e042c03551182141c09452450400d10703a1900303034000e100300c2d0144020b0481000c1c4113502e03042c98038010480e614055507501c241242001c20354000d881018041d00c0e004028225a090907903030b03440ba850004012104040d250280d250b000071519440101a00103010701e9081c2d002919041400c649070a56030352400b81d4100e0510115480202c1100d5803001e094469503a8140030005443c6584101400108440700e04900052001ca10060780790083d02400b0b41401a014040d04000c2640070301482c0050605040108008078642c0307601c02c0340031084200595001e4400308098807816001440c400c64902c1d00d07040c844081e903902c45488115409403240c00c001c00d500f552561340e40c0d0f01e0211030007405460300c0d2110320310071030185003500c000b00215a51803220300c5d1690707840c0000d844107403070450104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 957051888 1250 957050638 957050641
    0x60916181203140a0804150207020915180408090103020f040e09010c0f02150105041e090602090406050306010f0933050a06050c0a11120613030908030f1801050d0c08010608 76
    0x40c12010845450344c00310b6540b03640c2c58561b5210908030700c0024110405a580c204540340042c5c070364201e014803401c105d40070404841ca0102c2484081409505080e43c039604080410000501c0203007030701c04500e42881c0058907205540c9074500b6902c1142c11130240c403402c1d0f400b002094401500803442840e0340d40c2c0e8024584520340300982e0b880d40410304020304500290018011401c09a1004803204c181c0d1600403060a181000c4070704a81020300c0990351650006410505414180030f814010300c1d05034003d01c055031408081c24281a01b9002d921103d030b80b80c0300c08448031841116041d45204100c007641900c224120303441d8000040620415005980189000811360b00480c191140041c0e01380c00342c80f5043d10b170760340c6002100005d0007259001307100e540983c181039400c00569218003901c07000c503104c40095040140940a003684440c14075882001241c06085a00e010365200f0711708658a0815002d41d480185c03024001e80520398800d91401400441082c1d02400b1181298201c0c1c13a0031103507 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 957053138 1250 957051888 957051917
    0x5060604030b0906010303200d0332060f010e0303070b100f06020f10020306010507060b01021e210a0f0c05120f0306010f030b0109030f020a030203070305030406020c040203060916181203 82
    0x81c1e08c450b8111401d40014401c81c0000703010b40c04c50440c0c121070f441d00f04000113845c0c244c15404a94084448503c00500c010041541401660103027045403d0030314864511640c1c0019550f48101da4004222103007510104a814010150080141401d010221080d580b80c0000a40d18002015001040e100302d0400302c8040e0032901c00c580c09880107941d004d1920840d5201c44010f4042011098110b00c2143c03815512aa076400882c605040364101520081c039007003003a06031920003004d40b00c03540c2c0c1b010001e400724141c010b40724080441d00d074100b6070000485030034560705202958100c0840102d000070b19a09160703a50000f948665000d0301c4401d68071031140011030441d03052040345804110540340a10208020030380c9000c40504c0102100c1c1031544940c08242440c1c000e07802250b050340042000d001040d010300641141f9035040d20110708502d00200002c411b9803000d0081940451401e00d040822440b41c0100400c0315103030919504450358554400f030b03041e40d607100103500040428120000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 957054388 1250 957053138 957053177
    0x105090c0304060e121303060605040605240918010806090a0b34031e02031302060a0507061a01021006030506012c0408120903030709030605060604030b0906010303 72
    0xc4099112040c1180d503169141c10080c100b00d0701c48a8148958080080711444440040981c81d000034a158116071440c0350403c01d840c500d8200d035200394101380c0144003580f2841c8080314500c81c0c2c24541101c0074800007114000344a02c0614942114992080d1284140f02d003115a048139500402ca43d0b1941e2103404442d250098058000c1c441041203010892500f81144154210314881c0e02880019544400740c403845082c050244002c82d07102c100140340c50032455041200032261700d03429483c51030070000310350031032005400c000c2c410007010461080461107401030302d880e180d10180c00c102111030002d1031840d850610240600601c908803194140d0480c0740140d400310b940c0407006291603400d0002c500b01c0c400d0742e03540c01d10b2441105c0c0c8100300198288028103001c0d40c00b90b00d1a07969030040c880b511008100007402d000c031a030700400511451b07a80c0700a0000440750441400100b64a54030001000382c1316980c00035101d0042070301030024210010800ba4101c03440303500c9200e00030410092002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 957055638 1250 957054388 957054391
    0x30d1d152502060c0d140907090510180c0e220b010309260f0307080708070504060509190513020903151608060636150708070501061d0f010509 63
    0x1005030031441c040340d2130f08100c2e4064100d554800e40003140c10301b400e03041c804e141d1008945405081d48080f504000819051103041e802560400001341c0550a01620904180b904841e81d400c1c9907468140090040c030521aa0301030744002003104e081c1c03402c80c20031480c914003060f420b110154642180311140d507000b8032682c0c0313a45038802206600210a0346400c486424003001c05e02500b8000c002c0c00d000b2903000c000a41c4510500c0d2240c04c000c1c00c1c0b540004000b030b200109141d003441810042400126040760a80e4070825040707615002d0b001594182241c1961142d10480e00000e0360f100c02e0002603481d030040c088140d4103504540c0c104482c400d814107503890940707911014600308961303041c076103200d00c039000c1d44058050091417601c140b160b603111024105d0040d941c4c000503071800240c2e081144494104808904580b2030070107040244103c02c980c4120403004081010000c0c149040140a400402c01408108110341e01d1164081001240160895450070b010206000110b07461401030340c01e5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 957056888 1250 957055638 957055711
    0x9170c012a08030c0403060e060f1b0f0a020f0d05180901050f011101020c030301030f1109011a1e0f120901090503030106050c10091b17030d1d15 64
    0xd0781e1604162074400c050b41c4080d00501081d0010407011000c1001d81c000d201d10090020000c000c00d2900141000700300c2c0c40a0407107400c038210a041c000203401c100c000e0310120500d80341455a6004041410391501c3d881c80d042249500891851803095904080940384080c2500b1812440d200d00300100314448100340074043d0310606039280d070509944902005a642420200010f10741190303510301528541017640100d03645d10140640303404100c144d038005402600161200780c010350424026200785101c0110140c0700904c0032030104030842401c4000400c080138601969598900900810741c10b80c0256285006080340d9001302d4000401485820192034100010310706503400d100040780c56900110304c0125034402e941d1028055009482001902c5104110001d81e49641a10024214090364040d168210172a80e68031030168010040380c094041183c130001d100c646006d2603444030404001c41400ba4420384ac68040079886404166000d0f41e07a411680480d44d00c280c04072204409240c604 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 957058138 1250 957056888 957056957
    0xa1212060e0628030b0103051e0303090601060809030708040b0d060602070305030a05090414070806030c0f030601050d1410020c210702120f191b08150709170c01 71
    0x10f0098000e019012441600030145401095a42e40320004501d078203800c145c031140c019002c0d03275880d1001d00c030f18104007a09079401b460562404040b5152120b105200e40b605114800b000600010700034421940d8841e0f103c02c6454440e51600710b094070540001000d0070b0940e2820001141060000501400710f9038003000451601942080807202500a68451600141c4440c071003a0416010465a4414405940c62010318075040381014a0003020418141c040c0049c95081c1c505514081002415102c1c26522110600f402c0e10300000d200941c00412a034130f004180081c481d0590f150000d244695000c0200e86052801c00302c525104050114202e1800004100c03000044c2081a26000160ac00c3c80648d17880601c406e41c418140b0726103e14510119010030628810007415170f41170790f1140400454200814148508107958148003010800c0c20650000000c8005200d900000c1c05401c4160441c0e000d01c04131018250390350b4920410501140e03142e0180903c00403800d1342a01007040f185007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 957059388 1250 957058138 957058159
    0x110607051c051e0901052817150d080d090507141f030914030d02091c1211160b07061a130c0e10270510050a020a1212060e06 55
    0x660206980900c5800c0c1c107124040c46241e200000308040783d4600d002c1f01d4200c1242c1008042e00400c0005121322501c2903d1281c020b004951060189072300c40400142d840c6403a0384180d080c181024040c13040410035403418401210304000780030441400300d40305468031a291200b04c200300007688445000c440990555800041d000c0c0780701e50044055540640f804524500e4181440341c1940d20040d10a0159038001030081068200a0301d0120f0036500304520001d00c004030740e00c000400c8507001004040001c80c140ca801c90500501001c00d0602140f9014109039a030740d101750301d584c0c00481054131094581040f40d8412402c500c031920601c400204010350395409064018003d100540c03000c4108040c2c1c02945c1c82d1901d41c2085000c1c0c800d502d40301c017064103105a298113442d08030081902c40d01d1100aa0810441d2104845241c19001505281da2120840340040f0b107800c100300c3c80907101c480c0807801030400b207402808243c00c40001c10000d0101036200e0410b4907951000b034581c99000010003c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 957060638 1250 957059388 957059437
    0x10c02060a050c0c1516260c0f04060905150702180c0c0105360a03140d1806050a0b0904060504030917150703060302010813110607051c05 61
    0x140182d60000c0c101c0c066a040000b0000030030700e01200300c0c1d4a000340c04175882c00c1c170011101c81c556004400305180307030030950100c2c84041c02600c03450a01c080d000304003001b40031a80c031750001400d4400700d105a5090300d46455a03008028103102c3c00d889018003a2003598038022b42c01c034550007101c0c00b094014040c2c200741440d003070b880c0c20b210300c004001c0f03060f010040c801c10445000030700446020748100c000318184020100307200500190400b00308402c40500f152106288440440c0982c8a01c0d0075003000040e100e108280e503000c5108ac40b6541c680700e80b401401d841056424044043c0e41c5000e03020070800e81c1c2d00c82221208403810107000603401402c4400003400200740380c11284c0c2c4548a490160566550b95504030000810311701d2003182c0381c1202c0d015040301424607440950045440c5014040c41c0c2c910740000c0c02000c0d0140800c1c80f4040004ac4010034010096001700403541c02a120a88d91181400c1c2151118413503401809034080b45031440080c1c42c41501031354614031082141012983c40320 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 957061888 1250 957060638 957060641
    0x90c0b0f03041515270c02070902090307170607030506152b06060507120e011b0c081605040e030a141e07030f031503151104121a010602010c02060a 65
    0x2c070b0210095030322402c0501c4440e0b1340103e003000900800c00084090111025440c42074010200300d00b101610b4079040341e02041c1d0010301501165108440143d8070010100803034109000d0740c00c01e04510038002100b80c1c00380c1000442c2c901c070340001c0ea410422601ca40c8200006c10005855600c1015400c2c0600907000c100c42c0d0603404100710f4501c50907618030281c404071003640c40c103034041c00218a01040711414010600c002c00f903200754514120101100a9001030001c030082b0300008049503004030000f0820619444c070602070507081d0100d441a60501d080c51088030f1050050070f00843c14000b07400e065000c0001601e0f545850340e10f4480c5035403140f5030101707500c0d0170038220000c03040085407240d526a81f2620041c0aa50301941c1d0702111301e1004c000103010340701c4a04c00904440d0307001d801080031031142c140003011080100300119400415403c4c24885018030340240002d05220318600040146c500031a1030301c800c0c1010034440507a80e03418140c0c00c03600c0b12901140541c01c608006860b40c0402d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 957063138 1250 957061888 957061913
    0xb07020f0a030503071b021005030702100203071403130b101403030909010e191404140a02030a030302032e060e03030f030c090d06180507080a02031e03071401090c0b0f0304 76
    0x12443c605111b01c039900042c1490040e4088a004200008240302d2641da05010b05030b12407215000551840c10104801054440c0c440c01034030f1042408070100301000030801110a2090704440031a01d00d0512030b41e89a00c0301098412490300050034000c0c1100703170070084107540c9a254020034880d2503078607101e0311402c042c03001480e0321403030682c0181440c5a21014803907424000c05c0714841104a24152401c41c2034a0380024400030700d541310517441e0006a400103540c400140d03040c5400b40c0c03603498014103541d500400b06601d001154029861a02c2c41c0750301c0c3c24070405c0ba4010343c0d80b00e00d01700000d000c2c15242d1040c030b0742540700340e0b60030400904107007201002442c4030803000e4a01050100c06403550000ca070101359004854a4072218900103100d02000034030080c105039000341801200c5030380001c0d130321204070741591004002043c000b01c0c00c05042c41580e80e0960800701e0b20803810340b64441103000702100903049400c219508404154442d00c0001e80340b01211101c100c0c1e1031601d5941310610011705 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 957064388 1250 957063138 957063167
    0x207050c060d090b061f0f0e041406031b0a17030f0a0e0411390312040309080106051309320c2b0f0b040b07020f0a03050307 55
    0x9800e11011240c49020081100c4001900002918141454840318a00340900365a100d510381c0c008116016000007521038000c0b100e41040c0c070003582814016503034181d0307140d80702e81e00c503142010080c1c03407800079070120b886840c088064426101c01c4005807103540c80201000c1345c00944c80541404411449081041180d10721011030741407601c00004405c0c140e2102c0d07034807400a0704084520805081c40e026118246a0300d40340141044401004007803068295290050900300341d40c24060800750740c02070306c501100d4010541741d4481d4610381c1d0461060b82614210002690108005128030040c802e5806403135008040300d4400c040c081d4420080c000d444001e50b200c64060826030f4840180d9010b400000319001820314081d45141d243c00c0c18840e00b46901801003960109800c1c0e010b208090b450340031210401d00044003550780c00c040d01c2c1c1c0390313804600800200c2c002041c40301b4001400070851040e455030f030807250461b0102c45955144d9180e00001000300f0018800301da0100c0c01240c039110200c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 957065638 1250 957064388 957064393
    0x51908010f0e071824090c0815150408010501090903090e071b060b0a1e05010302030f01030f051f0504120c1709040f14010807380c01090614061909020705 68
    0x20545c03c22403e2010390080c00d07480ba40d078200010850403c0a00450100c1001c0742014921442c048540080d6510002c45542c0300d142c0c5101d5140e640c185c03100c281c1d070107000c004000f0071096848a1014005019170758065022450340c40300001e000c40703000d1549110701c8603942c580c482c0f14645101c1100b0319001d5842103039060346a14440b621601c4094408000f010aa1000552840e030b4115103811400c05401c0541018010010049030102000300715044a81c0401c80520341080d906205041882c0680c51502907226a19011913800d100d400150207580561403441504034000b2066403249482200100400f00c903a0310514000d4500019003200710000d0804038800901a0458084031182d401441401809100502080c6002c02181019200305c003140328284081001d040c800c01404040320010319182051056185050030580c2c4400c100140244070150240c0f410304007400b4107124460303060a802d00041e40c0e501e001803d21020a880484142d20982854515400b0358440001a076462 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 957066888 1250 957065638 957065651
    0x40c0509060f030615040c0e01050412020319030e090c03040f0b0a0e10060f0603020c120a0224070f0206392a030a1b020109051908010f0e0718 63
    0x281c03001c3c0080c5200c0d182c5e1000e601d0001d4820750030402241c02c5803508004000140d8910020741e40c002007110252a00c4001c8803070054070380d1000038a0414490200d60b40702030120103007020180c018809034071450b0b080f24022542c2c1d540025080aa001c12600030b0b0031007081041c044082408030a185400001c6103001080d5104100110f528004040920140c1c655443c3e2040280c040450420f0010700141c0c501503181c02c2000c03401c00d0345c1712965402c040c2c5c21200040c0000b41d2b07a008201d502c0040b880c03543d190210311020f02e41c0000840f802c03601000840c6203110600300941c40411440d120b0004401c4610f501e114005070843c000040d203250005480c044030f990f40d00141c0182c05003464001141c84103a85500e03040342110100032200a04100398000d20903110995004008008a003152038040c0b1906480c07400100e40998455000315001072501c0a001000c5c1c6564a2107000d0b200315000a21107589400707408411159403451009017034000702000d1000c00c012011407860758a4011010406 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 957068138 1250 957066888 957066919
    0x260f15010b160b01180f05250e03010606030212070201090308150a260d080906040b09032701260a0c020313060c0209161d01090906120b0f040c050906 66
    0x11034000382c2042290200281805c04070b6a0307207004955100001c84018400343c01c1502003031029202c6031420b180e000c6020303145001103e1240c0004d220940c0014024000a55201c0b4003400942c021900c40a02421440000c6c0356940140102c12102d580b543e40d400103079071140094401c00d2114100582d11401c0110300240501c0d00256100c600c00030190162141d10682903001d00d0440504442d4061140200c02c00c84076000100d1031607032164004d0300305040350b520f100c9001e08620406a44184103102c10710229140c0105a5502210800030b80303075800c0220303025426103640400c10340b5110410701c0580c00038109400980081d1148401401120309043d0764550074041c0b0403042c2c00c07100004000c01c10100a62409180c2c1c0b0390450b40a200f0141c10a500d124010b00441d00c007074101c0400100d00c1c0480e075050b4400c4440d00000e0801a2041043d1783d214000000340003004070040d030300c07038944401082e101000150075a0051f0f6204280307000e0107191106008074110010651544488440c1c80d5010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 957069388 1250 957068138 957068153
    0x604080105190c08010b030a05071403090f07170304090b030705120c270703051015020c1f080a0c0309060912020d09080c010c0804260f15010b16 64
    0x1941c0d1003998a94000e1a69070742c0030449045020181c10072142400400480c88660100c0303401c50a280004995640c0d07034807083d5001210044009140702001041003600300002c030f8405544810542920980341d84c80d074030401003003100284c1ca0300c2500b0402080088071455481000c1c00300002d02654440b9596000140580c03003040c60002d8190000005856075250240341c482c1500440c0d06030301c4c541c3c402003600c0240d18400410303810a06a42d54046102010100d980b10300400140044070420309031408002d4aa2031049025030285c40714080369070b031400542000e500e01c4078095481156076a114401f00020b418503218543c00d060307489034036502103032017802041071103405031140c14003104030f06800901c5e02e41021940c40810402000520003140082114914903200b480c4c40d04141000e07090126103480703203510001d40000030b0300140980706100d1308480c0c61a030101d000c2c1c6013020300c0c0724140ca403104030b0307030a440100e03a01e0171005214070701d11040a0040c0443c130340c012001c84511640c40b0310 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 957070638 1250 957069388 957069391
    0x9050c1203071a0408030c0c0c12030d1d060f0a1b080402011808030d09170403030e030f011103060915180133030506030a05011e0e03090f0f0604080105 67
    0x2103420008420041c000180c0e600310107201d0348501c54030240703005d855800c0180001b9042c264401c0300090038903169481041580b003210344c02030040005c003280030600c0307680740d00c1a42400d02150800301000307004900c24241c121542a00000344c0340360b541e105440400030750020f1056204070343d183c030240f2400040e060800350318a625107a081e400c0c140307070001402407008948076481c02090107009219104020081d584011180480460206074620740a0001184508840304480c40803a000052541c0045180080080ad400740c0d114844146402400e030355810124611040d410030120710741c1c1c14412542a8000310a0320704032112881d08000804003041540d80740d1860800b80c0c010300c02d107062602c410000078001f4980120b882d90780003482d8030321041c0d03001010038181e6500c00107005d5207082c009510740755800f5000b000b40c03448509240454492040058915520b0700940010428000003110800e141c01460400035072502c00c100030030308603980d800980101c0d0512000441c51401d01031305 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 957071888 1250 957070638 957070669
    0xb0301030803240a03080a05070b0c03041a0f0714040314010506010201050105060414040b0105090a0801090b060a050f2e02031902010b0603010b2d19091809050c 71
    0x241d500c3c1810044001d1128807003011025040d020102001c82e40d56000821080340c5d4480c3c1030a0f1116610101668130f8000e005014100c0c915010030881d03208280742c0103500c60340c441e10680110881d034040c4074081c2c2d00115030302d03690741030000c000c00d41d0746005000c01c400e6035001340f25483c90300e130326951554504d03c82c04010102c2a074540c41801405d603020b0003164050042a1051740c240791400d9810141413070b00c213001c1406a640d41e440c021460b4071403011203410707941c09052600c001e0b50b035901c02402480c40042c1542c40d03194102c081000e515141c8008030448400a1040702100c000e4000c1001140c55103001034000304000d44400d80310a41c0c41c00e00000e108094014640b07800d52a5801d4103000d8800080f28116450080c4801e62644c0d02d0040d64190356083c40e84544555440b4074007010290103010b810420300d00b080b100034140c4072610007044152008001d8010810034110300b5544210103000d4408000d030894450030b05802d180e80400700c03040c001d80859151181c014080741d41074170850030720b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 957073138 1250 957071888 957071903
    0xc081812030702041409030a050c0705061222080301030b0a0e0f0c090a05010b030c0d021303121e1407020307031a01030203060c0a0906050a110d0504080705060301080c0d0c0b030103 80
    0xe802c1540f61520401361070a0030714010b842c0c80d1400204040e02ca105840c40070382070140105810b00c200c80200110710207881c000d40002d94038400c40b00316560203117007181c4070f01000342819102d00f800c21010410300b80f2598060303070301400c0d642190380c0c40e003007420014140c0b5400c43d954455952000d1080028544805100010b40780c0e001a0006100051a0040c440c0e0943d41c14000104140d0004400b103a60000d1032200b41c2c0d407901e0601d00448040e1140100c00480d90200034400300601c620b0200c6400050840e48030f54603425440e4107113054028829200f03070080f84d603030520390854100c118000e00b18135100500340d400c940e40365034980000703803d441410103480c3c4000005104605040007170703513000451f1a0245052280071030008214200600070b850801001090490049000c0c00c00c9142c1c4c1038010064540110108000a003160000e10618286110304200025141030900880e4180c0f0465006130100810900501200c0705060104403105000050000b44811342c00b0051806540305150 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 957074388 1250 957073138 957073147
    0xc012013120206040e04080d060b18010c0201081902070b0f060102060717011401140d09020307051903081b3c06130c08071205010507020d0c08181203 66
    0xd00190100c0c240d00603000d8901203001c0c0c0070259451001350340840344002881d22855031140780c182d05e680110700030b44903c5401c00c02c000c10403120310030190043e03c0c10070100700441c541d10401164817802814020b03012982c0c600c045580d01d400c1f08071100e5403403c0c0440252800300f0300d0303444100c141011151494840d0081d0705010442d83d042c0b124a41100a610f400b10701c031819140b0204400394184188a4140b450303020b0f0300d6159000e803e5000a06080c1d201385600c0720404112400034108548040f80b290069001c040303880e18001d608210034071030a14103404494155030340d505590f4400c807c4544e00607882c9100c15020f403003c2050041100e44007901e07842d500172107070501c0d46415002c1c1d94002000c20404040c02d03018000924141d004c035101202c140780b045207040404841d8895000b000080c0180500411000c02040301c89507250320030700c001c01042e40ca612080740c690b08036896110002d1000004100811041005401c5081000684a0341c0d400000002040141c054007035200e00d400101c3c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 957075638 1250 957074388 957074407
    0x6090509010b0712031a040f05060a05100207050d1506061205060306010302060703031a1905011e05030c131203120e07030b0712110703170c0f0403080c0120 69
    0x11809004144440d41c0504041c411340c0c0d500b003000b9001204d00c1c201585d070410075449000350420149080b030b000e4800c01450b512401d0701c0c03010340400ca684601801c440e05001a0908120030030414102c0c544d406004082d003490708015440710041000e4900c1d0348100300f61903260005203c2d0000901c5a5110071040d034010300e145400361807008001138072a0304580010005a2201c408842c070860f03042c900041c0b00e03107001070701c16010803e240c0915000010004402c49041c00341108000b80e480c240c0b41c0404c6080001100d000f1005032001c01300020748140007040c4600392007030141c094108000e42c10030249480c3c1c0c030b5003a400607004034260009052030540d0040619a0302c510410f940504000d490701c58103507121480c03064405440300381008403002802541c040c0581c49040c3c400d04021000303649103800d0400405000b10a400d00d4604a81d10011442d40ca01400c229290b0043d219000c03810b207450758035103004c29088008039201d40c0d52070784030119110501d069034071010b48800d0406503c4d40781c0e11 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 957076888 1250 957075638 957075649
    0x11031507090603060303052a120a12151a040b0c031b0a03080f18010906050406061d0c030403050903030c010f230a0b031c0207150e101d0307060905 65
    0x3a8007042c1850301d484801c1c40400c1d40001260100c1182009080b11a9522130701280c20b210000e20343c0c40140100c86c004510109480028504904d01d6507900100d4850908004115a444e42c1c40d03114400380b00001700240081036900b10044915980d03081c2c01c2641d20002801c0c142d00c00755004003640c000003103e492180c80e039031008006002c0c5100030480d0106694015040c1080600502c102d85032060000c0c5003800340288003080004280c009014802462902c81c000e8281a5030440760242882030100350b03022807030b24030940c2c01980407540615031250240b48145502c058016010414208044809030314104010603a107c4d43d40b000140079148801440d0441d402c40c18503134038480003c450b80d29200480d204c3c0941000c80d00400250390702503240002d140030400300155119017021000301d20b000e500400e140c400c840301d0304402c1c074280490440c1295003020040900e984880c2d0b03a410740f005280b06031030f030060141100303000d64007001c200e000080c60004107902400001351040340c00d00032030801d0b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 957078138 1250 957076888 957076907
    0x1104080a0b1e06010311192109170901020120130e01080c0f030a0c060908160b18030c03100c18060203071712010b070210020c1c11031507 61
    0x1002c28846070708841c0c900341080c030351015046a0405031200c14104100319010102c885010301341506003040307a0301c00c0d00500400d04424120311040703000032000c02419194003584465560208000c0d03a0022509000d28494003d03c900c5030456681c0c081e1a4907040c8a0001108035207002007042e5128012221103080380c00058000c207007540318010041048000c0010b640180d05400c442c207107030224100d80842c2ca41055071901500c112101180040c0340e40c0c200c3e0109090342e0503003040d10190040703030003030702d010079207078480c4044091042002c1e41c0c01c8100e02d07170300000c4400014103a48c012176154000a00c2c2100d600160390180369200401c075402d5420501c2980300c4a101e10903014003614007a00603480b0301410380e01905071248407511020b030310750210443d88600c0c442030209a4075611044855616044128102c1c000c00003051420040c90000984c0103880a0003440307030010424840c0c608a03071500c8590103c48100c4042e0310001580d8043c813141c0b0408240740302c129810f00c0d1a41005002041 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 957079388 1250 957078138 957078151
    0x60b09090d02061801201b01020702060403030509030f1b181e0c130b04060e030102070f11040f020c1506010503070f030515120a0521090409061104080a0b 68
    0x40e0144404140e00854026440f00960144101d070300d054841c040d003d082c054440541b5110801c8101c3d480e600414090120001e040040302034610b0842e051034201d05c144031011b90310071414001080064403a400815000034003800750359014402c00c139500d14140008000346100c08184100413214201840003903180401900380295508102d05103a14004072404041004003101d030000e080048014101c6406150f020b4094503500d03541c1da044401070b0814040d800c000f8a40c0141154207207814000e5590039501b149401c001169941d81c1c40d19000c09482c4200d4102d51110410340100c8a98070140101c0800c2101401031002002e9401f008498000c003414140a024030a000c80c1a88c0170480b4950350300e05c1c1c14000790315103842100d0750106035280905a0702080d04c4104c8004484041030480d01c6512407000c4403101c0c00200e0b009a0110a1030322606048a000d120035030162406812000105025001c00500c4541e44803011010754083e402504446c0e020120034420820342610441e0b1064 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 957080638 1250 957079388 957079393
    0x30b040908030c030703022b06090218040903111207020f011b03030b150f0c0c0a0602030d0908042c0c090d06091b0603060602010f0b0307150302040b07060b0909 71
    0x9140c0da80391038503070201410070a1000404800110700a000703a040700e44c01c1310901c003d084800d2860509140d4407156180d601c081500380400042d141006000762225102480c900c89584d41c58502404000c08207401c0590801c000010035030300144003031040c2c0300540f1807014480c0d901c40b11030051286003074611080d10b0401003504d000e01e65188e8040c81d02c0318020790518002c200c1e0b0a051002405990380081848491000000e03110f101081c00b0b8000d0511580b26403d0360b004540c1102084025000c030322841c4003581040088041c130054035403001010f68400c00d006420710f40c8070603035280d10b2051510704514071000300c0034802ca2035080300703003180c2c2c400d021010041c034018280c00483c17480314901030001e001c107071a0503621041020320117180c3e0a10700319030541c40e40c0d140d030748a0080240803c0e01c00d10026510300000010039565902501489503006401880d00710310b8841052800311440d0070010405509001c04101540f40c00014144140582c1c00401c40c5520720003045507010000c0e104a1855 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 957081888 1250 957080638 957080651
    0x2010209012304120528050d0e0f01031d0a060c0206090c010e04020703110f0115050a0b03041103030f0a0909060e0f0103080307030e01020d0903020c0d080906090114130501030b04 79
    0x609104407001e03034007191030000fa20700661a00e940f5100026001c07000c00410300b0084004050507121548029001f00c0071a11501684601540c070305c1c15003142d054200f0031340000d2401c1c43d40241c111148082c000e18451007039030b1f2082c1e8503070b04005004004030380d42d03030702e83d4a96460150b04203c0c0d035402c03034882030180820402c02170001e0300c0c8d11100d455280c0681c4c0c0200b20001498007030b04aa5071a00c403500182d80b444881e60300602d0080c00c0e190f42558230800801804922414140924419109040c030794a186807580d4540c817030a0400c080302c0d241d05100c1003010300040900360700030302250354084c0c49000e911030401d000c5900342c80250700240c5006030303000b0410403459042c00314181129005030461f5500d4031121003c8015007118420020b0543c0000ba14907810f4049a01410009019a007500c465642e00800c0124581c0b6140300500018814032885405107403807001084e001c9014104004060380f442c4020516810030940e034000b100c8440420841175815008010004a007142c00700002c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 957083138 1250 957081888 957081947
    0x5031219050412030e2206030c08010b0618120a080c010b040b0102030a0c021c0b04060b0904051e190b0609090705100e0d060e07031505070c0305090a030b070201020901 74
    0x21120442800340c20031100000c4890300e038031000d0a02e66180d01b10504002545203010400010f0407035031001300c4590719080000039842038103101d00c551802c0e0060141d498000c107040603400c5450b400d81c00680c42010040300040301081045040301040c410000c0940300e14240340305508680e0120748850040703007010300e00c06050380c1c04400c03941d03d4000c03402c00c2003e144080c0041251100c0c4001014540c0f05404851000c0c8580c480740280306038031610092188880e03450a00604c0c281c21382300200540d00c03808860703881c0201c04003010303501d120752021110f5044039011700c003043c241d580b82d00b80c1e5954510010f00c000b80c186094035640c0038810b080140416440c4c400443c031300c103c000c0040d80400070301c18044401a50703544000184682c00c44030502c407040441020030b49400c80c512046888050317a08190100e5041805aa44142501c1d00d580071501e0482d14291200c0d48102c04550380103c00728000320001e60343c1352031180144ca183d400181c0380c0101c2c100161096040307054450f0201c100880080c02d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 957084388 1250 957083138 957083159
    0x50f0105092e14010f03350c03070506130b060d210908010f02040e01060e0a050103020d0905010e07060f0c111212070506040308011707090b0a050312190504 69
    0x44600c50201a5480c915020301c0b00d8024009090001d803014154400000c41005100480f81982d004800711810040d16111100c030100d40070b0710b0012101c0014140c0310208080b0341c0508441c0302100c050303d01c1c0811036503402c1d0602c881100d00c0324801e101488588113000c10f04900c194481400e481c6641c0e80c40c000d4035186e40321506c1824030800303049a01c14600c03515200f285060000d10130170000380450581241c1e2070b40607402030700561500b680400f0000401500c550091089014041c1180781c42c54103101c0118065400380032441c501c99120050880018024401c100700ca020001c003030110941003000040030020340c40e1849042140c0444102d01096020020318050074040320404660341c5091a11402c01d4002d42c0c103410900d1010a00c7e400b0b1240c0070030118429446503035070700b18607030301c80c0e01103d0751680d803003d00c2c0c030298402c84081c002e4032071550003403040716002030411251719610000603107410381c100500c20150902040b00c030403400000080d22040300060034500d00741381c10303d4000c54 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 957085638 1250 957084388 957084433
    0xa080301171b0402031f090504050c031f0b041d0a140f07140a12060218040606120507111b040b0406031208060414070e031c1418030a050f010509 64
    0xe10641c1c1c0040420b6040c505800c03090010710017099600306c880d81c2d9041d00c00c014801101e0581e080d00861150706414034000c41c20092a0112003090075410381e140c02203c0c020f041d1520004d410654035140c080491650140381d602010100c0300030300381c10260f86019554a09844006407190740200c544032640300000c241c09041d04e1100e1210403904141000140e44040c50750b0020b80b0403102140d1a10030b0203620b0700101000d00c0c00a40418491203c14180801c13504140300e03e00010341400c803500e41d8008030b6044640c0180680c90160404d546d540080c0703007015000d2840c0d6103001e03245132540d0100d08090040c500c940c031703044608002c0700c0d2540c5c45162100e0072500e00c54007080380140005071240c2c0c45a000b521501c60701c044200c00c51400c1200036298109010b0402e100380700e10040b10354a10080000581c0d0510740366981580790203807a001c2c1aa0f42c00c5044c0000424510800c032000310b403000c000d54902c46004200801c00302d04008465402c40320044c041804540001c50700740748002e100410031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 957086888 1250 957085638 957085693
    0x303010f2907210512010e0a0b10020a02010e041503230d080105030f0718020d021c05071119022701080706110102031510050c0a08030117 61
    0x24800039900010120149841c0c078105401140d000c20300d00140000069042d1034001003580b0050310140843d425115070040306900f1551030801d01c0140101440301c80302c0e41e04050a00c002094010300c060001b50410081c5208a0069105c0440c240c00c2d903a0050011204072000e0b40e0800c04201549091181450700c1d000243c032050807880c00802030300941d100100c100590500341c0310b5110b0600401011316a080c1705a510a104609081c2c1e0380b014041129000c40c0c1400210103280040b28252001a4001b40244e1002e00d5091001c000d80e129101101c90800d07840010010b881d1034440000741104a03141c00e4002660301559030301000700d00d240c0c100c0603a1501190001d4032010404200018210080041c030a032820440000600c0c007800541801510050380b40c40c0c03400311440400324202e01040303640c00302a03000943c400303490f41091603500070600d03941d00d801072604002d4401503152200b45081103c1c185000401042800e649070020402c1c1000800a49040c410710b130281e10250003480441c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 957088138 1250 957086888 957086909
    0xa020c16080a120c060e010207030e040e0c0f180c0406020d0c0804060804060e010c0c0203010f0e0a08030703022803061a0a0e0406050a08100b0f0603010603090c0506070f030905030303010f 83
    0x10030f4120301906040741d940d81e21420500070b4001d00d6a905020b03402200f0100d001c503400d40400703081442c2c1809091428078000005081d00fa01d031400f000000e1250302101a00445220016010120401d2005103d82e2002c3d2501d91f485140940c000e00c0c0c00d60846008080002864030345000800900480d011200e2501e000a041c0d115402c0400c0100380c41071900300d0540c80c24070942c01c1160440340321211030313000702c0080001c03030344c551050300c207940841b0030b42210398014480c080f00040c100d002464000715280703401802c00342d01c1e50034010380c02158200002c0310958080044a150b41c140a1080a801480a4000c85030b20058881c086030280702581001e00c100550040155229070b8000d800401009040500c682d5840c44510f480b0122001840041418042500d0b26030400e500fa240320688061300c501c3c5581e10b41a070481c0203110064041f1502d2122050001d403558500002e09140c60081010310014000d40c0740140c1a0034003548018002e80080c80100085124201520103e800e003406 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 957089388 1250 957088138 957088163
    0x106031416090b010212040e090c30030909011712120a1a13020406090f121205040909030f11010b01020c1e040906050609100509041104090b0a020c16080a 68
    0x11707420140e0200c03070101d100c10040340024040e180301c54114001e0f400c07141541c00028003402404906d80c5164602c1c07080540e4051581e082046541103070080d0f5841d0000d8a051180940019104901c00e0b8064052000c5070800c10344440018000e41040c036480c40c20244c60122104259011120010640a21107030303180154100168520040300100400a151412051300820340340c0003500a402500e0024031482400b003031030342c8051a0401900c4240800c001034401d203658002091003640340a01c2001018480015803445c6070240d60103491107901c3d924000700e00550700421240d42d0411980c0380360306020480c01e6a98001c00d100380c02d0700e400c0d030f5000001d00420f01040c90092a222020b03822a1414030781c0001e21046520150003a6801c40d844142a2100c10209809404502500b80d002c6103031400300700000c600004040c0100e10142000c42d40d40e1a58444002000c0101c0c0c0d04488a9000038101d10b400c2d60510461100d01e541d107408144842c00c01e000c9607514854040010000c141400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 957090638 1250 957089388 957089411
    0x81506090405070206010906050d0203060c160b0411040509031314010306030c0e0a060608150405040f06050f0906071b2901120b0c03040f0b27010603141609 69
    0x908a403894000a0030600250601c1d1030020342d181c009104000219143c480c005c1424a1301038181c012441d00200117103030a4444a00509155004425510341100240c580800242c1840d290714070a5015400000c8503c10541c02d01080c1c0d1401401411a0780040166000c81402030020500342d0b0401e048407901a401d15005074001d243e55040030780f090b1842100060f1003034522a0551003002c000b8070500c07545640d0722003a6148202070b40c0b074031104080031818000c50300b4540d000715803107805115102161451911417a0031600b064900074108600b400421489100c1040025080b81191910006040003801007103500c411a8500520205001c103000070300075540c2021aa00080c80341c0044480e59546641c6076085500540466a030300d8400c0004000e206044c003541d00c5250031000d000807079103035680e408007043c070018001e0401c0c1c0c02c02445400d46680c861400d5668010443c0002415421414042c010490b011010312b481d6200040000c403503e04c0d00c58681c11a42c040304003145a044a6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 957091888 1250 957090638 957090649
    0x5012103030b0310060311030f0307050312040309090203070806090f01140621190f200c0f0d0e09011223010902060316080901060501090612090602030a020705100207030815 76
    0x40e6403c0e50200e0810f00013009000143c469407007c514100c040741c0d071448100c41403030345070b001d2244082c1a075007090214a0141001c049400e0b0f0040c442e151460749141c880c00240100d0704103641140c0040e40c900c0400203070707003000303410245c2004200d09940002e40c5001030000f20300d816040180d005d030300c0c081034050000030558154281e200105414102d20710307025011008090585401082c44c07400c21907051a01c03081c501c80c0500c3c007107150b488026800c03071031402d02c44d650303124a03080042c038421105123003a13084052020800b41121580d03260f1079680d08004102c5080010707000b844c21110155a81c400003442c8a24981031514202c4a080c580d54180810134010050518041c1d04024004100700e1040c103000e1155080240e180c60b11001034880040b09800c0360b0041c010710f80480d079070040038005039004a8840b000704030f006501082c0f4142c150b845100741d03003040e120041d0040c0c01090101c00c11a017444064107ea117603560443c10b09a45480003044898050402c1600c0c0c0101c070b54103150340d19030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 957093138 1250 957091888 957091903
    0x150f03120a031415031b09070c0201021f0e010f110901110a170a08070815060c072d060c0b0109050a02070f0f120c080f03130f060f05012103030b03 65
    0x1190004404e10340301801004038003080700c1151090148021a50444c50f445205a070a040c0180c84440c45543e84281a90b0129a000b41603040d0711810090310b107403544551840c0c40c2c410040071b002c44c2c007410800a0509644550418402301e6003002c20f240e007803c0c040000d4400d040e85c00d18000240040c554500e60030021415005400500a854450641e440600003411114103540d103034072040d41da5850440e40204207440c024495200301030b9000480c42c00300c4c0600341103003610003603802071580c404035a00803140a184208800d42c01401c26030300e810b03d50020800420b298106105117040c81c0da12400503107814007d0359212956407001c01c1c1c2124080d419181c1642c1d2280c0200508503c0341030021a404103000c00302c8050030228000f05006105d9490070300c000350300c0640b103801d100340940c0301c0d2800d8000900c904030203481082c8003404585030324010000c650040b20001909040c20140740140c800581041e04400310f10060000b04101d6101c007621825054600007030090242400241001c1e203 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 957094388 1250 957093138 957093161
    0x1903060807080109230318030f011d0105070e150a020a0206030a1b0f1b020d0b01061e0c020f09060f0a14130b03031b030409020403030503150f03120a03 67
    0x9031990200b400314056000400b85130080c2d5030f40c002c01c540c0701c2c1000a200c00382000109140c2051056001c9441c68850064003a200201661714507494110301908444d02010300f0702c001e49030f450890303400302d40c280311302c03600085107140c149030a11012000c1071151a29050640c024078000401e849410320901c00c14905583c01000103a4070f042500480c0081d0071410740718a6460b0341844a4421b00e4020140c405208403591075446c4000c52618103607020310303010402071381c101884540480008013070910ba14040c20750354454951000401030000c010504000c00301c01400b241c50009005030341c40440c071408185007202ca059141d611100407031030f98019200304907040710741c24202150081ca20704900c40910300588035003101d1441e42049109541c01c2112458140d0400c0000700c40002d4030486105200301180100c91502c0d81e14858807007264442d61003034000840c0407050251984004408691040c02110081070400070840000c1d111078101c80c05503c0c0c050005040c48850740030707800c280a10314 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 957095638 1250 957094388 957094393
    0x906041a09040c0b030a0615170a0f0b031509071409010e18062d0c0d050601140711010f0e0108010b031320100903080304030320070f1707030519030608 67
    0x300071001ea8050700b85070040c0041a4080c8990f42d03292480349d0180446092801c01d086c001d9200e90409000416009900540d150388880401006480c10400780340c40e194502c054180720315103c80c0c000d003040742036040040034090309180302e8516138641668a0545400c2401042c15440d1102107200381d07426032407416014001c94040000406e0a203d41c9080c11200c121043c1a000c1d50034140c59500c641180c0c0c0c162101020700100b400e05400742c1c0100c0d4002c40c181000081202280074203406c1d60000c2e20100e510307911404c0c00410b0341d64428003003441260281080b0340d09010000c00a828040140500c0d0b6103401c0120025a00e5807c869024206642140004121118446448424003204c102050154903545c44056a840c42201c02d00226504640582e00715101d50342d044004d040c8941d44420001e440102c00303105144034200902d03045121b59100c003d45070452604800e12101c1c40c46003400050140404404030f50018101e075183c0d01c036000f881842210006c019030060402e034102c0c00251 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 957096888 1250 957095638 957095641
    0xa03260709030501050117120f12010308071a06010503060d02040617010e010e07080d0302090105130b07061407020703031103040b0c1515010903020f1201050a06050906041a09040c0b03 81
    0xe070304150848180c0703010f034000740a140c0c1c0710f00640c0401e43c424000300003140d0181c03122040f98807040b4042e2402850314010303185480c1503415202d46401080e003041e260b00500041c20320400031a022000b0a000100080145503c1c140e0006080e41c003000b4102401428042c2640d070440da1660301c02e8026011900c1080c40344581c4844240c02083c55128001040d840c003d0781500d0342c003000034030208881c1140003c1100c0e0b0b043c0b4604601039000810401d041c010b0a008100810079101c41000280042c01c010b141c552405040c561b041e6801e9408040c40d0402c2c82062182440d8045600d00907a80c242c01c0003900d044901c03207014034501c29517014803281000402d00c4040d6500c04a2104499901c44403544c0541d05c80340c4040c0c1c14030014001542c0442c015040030401420302c0700d402e8030302d03410003421240c000b145030501ea400c3d240f0440e010540340341d40d0081407000b442d2180c1c000d40c000a06071020412200c803040f070892134800c0790107203d114510440000c0d040100300342e2a41c01519204204079104d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 957098138 1250 957096888 957096901
    0xb0619050619030b0409080304030f021002030c22030b060f03071d0105030f0f07090e0307020d032c210f0d0207150c03090e0c220914090a0326 63
    0xb0120b0a40c05440020306109102520740343c240a56a1420380241c9000d1441e155590151402c60003180c086055010345032700e05482400d280301642c0b0601c000e00805a0b202e40700f184411861102c0004013101c04480070050000c41e5111000c3d5034480c1c4251514000103803400c000925114183e03102e100d100c000c42403500c1810310b035044101d040344c4003a011104c4295050500c280c8544001ca901d044079400444100100030345900721000300d00403c03054070714108190300130581c0c03100024402c0e070210b14228020900000010600c2e02c0004002c2e241104103110400002e01c0402003598510340400e2400d03000d01140c2040c041d0301d01e03500c920740c1180c0b10348800310070280d290500c2d4800c00c0034094146007020303400c501801c031112640c1ea142c0c0d2080c0e906800e00921801c0090081c0030f00314041c030309000303200100300c80002d0300141d0301404102c0302080740360540410580c0c050950710703110640751405001c039200c0c2c001003202d0840ea060a000403100084203004c0c3c00c910840324a031080792180d0302030064 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 957099388 1250 957098138 957098167
    0x3040606050901050109150e040902100c0c05061606020306010203042c010b1620040f0b0901050102120706050406020d06091b0815011202070c300b06190506 69
    0x4540054540350340c203a130baa200540b41d070320341841100f074680d100540d0f0003445880354001e5030400b400100700081001c1e442d00407400c4100b26001010229012038116024081c0c0880c540000b0a0100c1d903c0c4d00e8001c0305902120280c0054000401482e004800b19009a0080c41a01c000d001e510031400b541850b10302140d0b10008821007a03c45d10000e000c00030070401c1c034420440c0c201c00004110400103001a80d00c0068200c9107844410700c48110110f8940d156a51740151f540c815802040403403030b114102c1c10810700c1e02040c5d10079030666100c0d015aa104a465505469400740c21060008180e5100d0074804040c0c45186055100c1e2440d290b00450600c08603440498480001018001241c4607180280c525407802d495a000480c42ca0400302c400707610459101201030642c080140c01c000c03d980e1070718901811a040b01035983c0c1003140304410422022604550f08810344010074061245464030040c1c040c0140c1460b000d107810000c00d040503000780022400911028142950721010400d8105 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 957100638 1250 957099388 957099401
    0x334031805010f050415020106051210060b0703230708040902040306182d0c080703050609062208120408091305040215160b010605031816060e120102030406 69
    0x10040d00821001064651280001a0001002e500e8480c0f81c41d050a400111a10356030741c1000456407520390104003600c0340c00c01c000007860103400808015480401c65000c3d2407054010f07101e003840601821001c40c2e0b001d011a04110102d00c1d264101e01020043e036544da115160000d00301d00c0300050b0024007440264000d1040b24014801040f402c0105203148481820104025001940c00d48009150700310380f80c00c0417082000c1103511745103400c01d95605500700041e90b20115090700320100030000c0c403a0a200705030f40329100c1c0019090380d10b085124200d59a1f104c4012a1410104036683c10400000c4000c444241e041407012810700c5ca064600444070381c2c05a000180910500080300038411141e01580d401a80d000304074042c1409442c0c0c981100780c1002c202c1d54440043c0f880000c001c20500400305010344001d50310140e50b4506036080107001d060b419070010315130340a810401c5290b0300003100d003010740f143d514002c4d045480190008444402c00761051405520000c2400708003d110b03030204 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 957101888 1250 957100638 957100667
    0x15030b07050a030c110d0e0103200301030b0912040311060d02030901050106020c0604050a150c1502071b050d030f0201060b0d150602030c060a020904110c0c090604050702033403 78
    0xd00110030000021150007410783d591401075031000c40e036075a006e03001d041003d13881c24040c074001419032441d403081c0800003000ca80001d0307038880010050050080c41e40c1c5699001c03200d10001c010001031100801080d1040c0d00c0060408542d5000100841d6036040468507088541c400554a03400c003080924001c00c1d0078071541d0098804c606004c0c0c2181016001c1e102210b00040c120103101e480d0082c110701c5802403807980320800c40f001e941140014000300c240d00744174603503600040e00c6504611782038103141013040c0352050421024004100d6503960680740740e1101e905140941640e550030704281c1c05810b9a400150580f140869a1b080419042c0d01881d4920003000030356003150740e9090280d0b00e0303101d04030039400c06400031000100542c541c0c2d002040300b443c0c050f00000306c0b02e20070721000d0700d1034005000300e145030740014246000c030745000708601d908810102c4007004241003000010355644220141d42c00c8241504002e000c100b154070043c00c2c1b140c603243e5922078106131136107801844044080b07082c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 957103138 1250 957101888 957101891
    0x20327010c030c0e10030b040e01091406061e060c0a021c0203100522380a0b01360e070f030e2d0106091a09061315030b07050a03 57
    0x45075807451181d0890301110304090715112031720034120400c5024200898003941c0043c3c80d00090304039800c2c01d2041008450064500c2070039040c00c2c0188500f000d2002d0b1456100303180c50030801c810078010030b443c5140880c0880b481c0c2d6540e0304115110741055191940a5440308644540e45490301c2d0400404407044d108400f550080052529210708460050780c22110208076500204100d107040c3e15000c400e64060180b01c920880384462086464014003e906500c5e0040d4501c0b01440d450015115049840018207211175207420000800342c01c0709100c618003440116170081484000d07030035415122103500102d065941d4071f0f134441c5d89010b2010340b494400254103140038243e003482803013802000004070b03005d00701c06a002111000c0350321400d00020001e907880c0014901a41092089800800070f1130310100701112045191201505002e044a0084940d0002c00a0655501105088440f2120350004003040000a1003083e001150001030100c000c80b41840320781500031020b4510348a56640 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 957104388 1250 957103138 957103151
    0x2d0a0c080d2601030308060315010b0a0908010209030d051b03160b0c0a1d060c1006090b0609010503010513180b040b071d09150d0602040e060a030312020327010c03 72
    0x50110365880480c15510300d03203030140300503c0003d1041d2a19074200000400700c07127182c070349982c00d070002040c00c0e40f00a00b2006e0014124403001d8200c4462001480800000c60411090b42c001c02c0e1070b6107518100608100000400502607a0f400c00d015400748010f0041303e40303503191480c260100c920140c9082d1812842280024140c5420504640d940c11042d940c0c82501604400703004100d0881d00001d5500810070301c503600c81c51404100242e581840d0030804140c05140c041680100c0341144090b5002d4081000b60a1070740c0d80ac4030440c0d04450381624840c80309aa001500c2c0700800d4a100406924111380c51080300b803001d81c450550003a03004100c440c40c40e490340b01e8250742e03844d455414225404d41541160440c0e29040340d09683c0121852116a2000c515000150001c26442801c48a41c1d5020405004443d03140d000d4584c044c800f91490110070b415514090954400134600158481d000000200c501d00d2101d107045a05465801d9024218800d80e5003d000e000d0b060308041c0000e203000c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 957105638 1250 957104388 957104417
    0x20301060b0c030d0203090102070605041101120c021509070e04201008010b1303060501060909060b0921070b1b0606011707111c020312092d0a0c080d 66
    0x81190b4070004442c004614100000b07814202a41001300000e4044d5403d004440100e0000c3c02000c0c4554032424401041c078036a40300151080d005816036903003092404a00f40d6401c1e4000820200588400202d0b540e13594800d40c0091400030340780c0084d2900203120b01070008106040003008070065151280000d1004c0704001e01221101181003a00003442d034500401060003c0c1c0c00511000444016100c18542c0f2500c960042c0c85080e4048800a40410810003040032a88201d1016090070b0714900e01d80203051300001e007001c890355100203403408034002640601c1400c00902006058010290742c54914522038211500d0b80700c0d5850b0303040d00031500081c001e58071500a0f094800c2c42d59001c5429629046812110b1815010703503a0000c1c800c8503506510f0b04812455103900c00c5096004564a01c2101e103e166120001762510b41a23520800b42c0240b000d209814440c2d0100c101e4503250030300b106000240745020241030011f81900c90056001c500c8008c045a02d00c04d03003145444040001a018 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 957106888 1250 957105638 957105659
    0x4260703081b0a3002190f050f03060409020a080c040b191401050d050c04051305040b1b0f03010b0304020406050d080f1810091e050108041203091403030901050708010308071104110c0a02030106 85
    0x10203044005076080128854000271140919002000908000382e0054160702140100049800040041c1c7c440c995a84652426005101041c3e806680d04508901400c03c444100c04540c003440901c1c001c0800411116481941a2154005015424051800d01e041d040d031080d4414064603000c3e03103180b0141a544401c0d4014540155030000043c546645e400d06814500300d08642018a940d008014590b1039266500103107003c0c06082d0440c03075680c141441084119000e81d40107a01404506101202040807442034138140b604a44950391768540700d024a5006102d0103100a0740080340c404440c06c810f900200a2042e651002443c03025440c1c201401d0740e011900b442030600185a6900207000102040700c1e00b92000301508000c0b075071003150344c0e03151050b0110142c064250340c008020020401024050315402c40340600704901c1650464944007160300c10000c0190040000c1850700300c85845075071010482650701e14402d81c541d00c40240ca1501d410100005034407960034000c0205041e2200c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 957108138 1250 957106888 957106907
    0x101a0a02060708150d06060f0504090305030c0c01150e06040e0c0d062a0507050d08010e06040203071103040b040905010b2104260703081b0a300219 65
    0x40340c00030806a641c00008a503011402400f072080f00d007003404114a00d0303c8404421607480c0c41034a02291060421511410000d1b030342d48858030076410b024994010039005000c03a6081003d07e0200c5640c0d501103030b4100c0c054801c25840703205403640b032040003641c0c0b40114101802640b04880c00d1000140c80000703180e80e003212140c1c0301d500007900003c803000220141c0c0030000b080c00900440c10441c2004112078040300c0d40c54101d4010400c002429020450203011000c0e01e640c081c240f42040c0e50504008000410005141601807580000030a0301140070f281c084102c0c034056012a9907450b1604c841e000d40d07070094494410705a00700320011174280612800e0f1070001001c1d424040018022540a1244030000340c0103481c07440d2040f40484004041c2c000c401c8403003130400116030b91404a85402000c20350300a1128141201c0b0034000680115441e04a8102261600d811300c0300381014a20444000c0d809000a1862429031142503020340c4940c001c0c3c0780d0421009048400a0004002624003560 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 957109388 1250 957108138 957108157
    0x3141003110d170a0f0f110d050c392704030909020c01320604230906010f0807181e0221010906081002090402070506101a 54
    0x180005810780c0c14450750500740c4501924410520706034180c50b1807030030381c0218000c0c0d0000d4440c40c100300700306410581000740c02d4480e240542081da41c202e0a5521826140108000c001c4000b801401da410108a0f6909002300c1510a00040b5044814400751240400f00d005400c84045800f03081d9141000c05006003060241c217540440f146d050f0300305c58544004004805100d0505008030300c0241502c090319500c1d0803000001b0341850100340c8600301c41d01c41507a800d4014400d1154941030000d00e00900d40185080c2d60204208403650714001c409500d0410041a0403030000c200288035000180550485140c00700210b8050f0f1200b82d400e0b2180d0203402480c050040c545129400040190722951001c100000c100c3e14500b20031300c1c80303401e030b82c0820300704669001c003108825420901c001e20203005105a4200704001032401da005526030310360603106026194046266601d5803269011141c0706907000054a8061030501d42414000132903004a085030074506414600c5a06818101c0303241c2c41 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 957110638 1250 957109388 957109403
    0x1050406060e12160608060103270f061803080f06030319111f0c0f020606030a0b1905010f031109100e0402030a02040e0f101107121403040303141003 66
    0x400c0c900748524644a42804a5984500800702484c4050700385500d0103090b244d40c40014500f4010001010384090a050f08d40155108040188007044240c0c1710004640c881031108014943d03044c002c0081252007500b10075200c20305100c508069222001d64851038103010b0555040e02c0c2c0c0360070305a8178015104802c1e04d040507100a0400d40d03000d0382103101e12040e41011a400c0800c201d0703014540602038500c11111580313404802d003c0300c0d040100301d0900c40c241d1000704442d26202e000207984841d80b100260400c440100880c0da070084111041102907203130802488996550700010b01c0401003440140d800f80883c00b003400c01e0303140a4001c40d0054100d110840525070421404642451000e40103da041c4a170300c0040b40103031141e018890301032411401400005406400f03460034000340c2101c004411745011031414081a00c141680c80307607130700900981d0200c10050000d8442d013802c010080380fa0380e400b200b00b104050b415000300ca0043c1c44030182c203a1688500d500e14012403c180802003584 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 957111888 1250 957110638 957110657
    0x906031e06021303030f0e030f030319020c0a050c011d0604030809010c1502030105011112040b0306060d06090c0f180b0f1201080123101e210b0105040606 68
    0x9244581649120341c0540c0c001858600c1c0101002c50341841680200d02081c14a209401d4142d0000800a1761f40d0040d0b000d403500e500e40d0340303100b0b481c0c1c80300800d80c20740f40611040300b1644d8043c5506940c5008a4a0100e85c03401901e0708100c0e036114600c070402400510780c107415204074001740c002301406001c00381c5a141800d00716600c4400c250000c000703490400c400c00c0e1581010800c101c0007000c0303201320242c00681e654140f200062460018160000c4a41e0001c0d04c1da84070f641c0c084c821501142d81c280e407250b48075110000001d80354454210820b8595041c502c0c04110184250b11950350041c06890b40180b00340030b407a0035a8045100c40d0b4180e10052807032000c0144244103401018007180603d0f00b00d04d41040740030706064040007a004400c05139940c404803642d100c01e00f000301e280406584e001058078907080c0608591101d850117650f004401c0701c40404800c0c00280701034805000c03800e40304207100c141031400f0305516071a1002501c3d007040c0e80d0000616420188220310548000b0ba03966400e0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 957113138 1250 957111888 957111923
    0xf07060512190906092f0906040902010c0b0907090624140412080903010b0904082b1a0103050124140c060106121a012708160807090603 60
    0x1e4600b400c4503503150398440c110500013455511503222410310a0004469622040c121a5009900000c5000c80d20714940350008180e52120026540960300b103130701040100d400e10040700c0f02d00d400000100a40803180500110680220350700c07040d240200400c11406998032078030400e11401251158107407d0026903075000d00e110303c03110303a44005004003252405c1d039540507103045599680c5040d207808901148074291440c080c05100d402c0d10080f1001c81c5103081584900d03410f0310412094800c000200c10f403c03030030110540e031300b0b8410340c0b1024010861000035150a51b114030308104121300007031a02c00086000310750030840d402c480303403010340f1031842c07406500c030640b80603076240c00140214500340000002034071b08100d00c070f020b801c69a9803014030846c0282c0960a55240e50084002c1c000900e07140c0c9000c0e60300100800d28010100003804450843c03034092030119046811a03100d500030091162204400210004129074002e01100d50703140e40c403c1c60700102c40300d900000b0071b82122001107005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 957114388 1250 957113138 957113161
    0x627060c0f030e120f0105010b12221a060f0102060f1504060b0c03040503101a0906040e070801050907050103200c031209150a15050907020313080f07060512 69
    0xa007621906200e20b410340080c0001c0c08200449460000d103511418604210001c203026150061085c1740b0014104680c44402181248008180e10286250309500e29904e010f40c408164a1030f805c2040d10001c89802c981250902d0350031564a80138a18144442446520000f50240701e00080800701c95140c440c0080300742d030760f602824890744c4151a088045030003240d213030041c428240c104000b142e6a51030300d01454208150221070661203490010b0780e441c1c00310f864520381c008400c1229036001c00d9550034000360052403800b400c0c425900c02c01c8004100c1e500151b2047d0301510b40081107440d0345540310011829940c00d02c0421a03101c07030070800340303a00483c90801f6050210600081e40c2c00e1104140d2032940400e41225444104e40c4980607580c15205c5103801345410001c0224240144500c000310351141181d00c1c410346000d6281a000991240e00c2401035911807000c03e1007602c0e40d241d46d0f00750690b44800d20140080c207802000400038040d4000e008072040060000351440395039440c00280131 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 957115638 1250 957114388 957114413
    0x121503240a090b1e01080a080d0c050403080304050a202409090405010c0306090903051204030e040204030803010e09010c0c08072301020a020f070518130b010627060c 73
    0x21141030b201c0191400244072280c40e28031a9540c0c800c4101001e0700015042c0440c44181c0c0076131030079081043c880c004100c50300100c601030710a182011800580300e080844291055030b002504081002c800c0c0810000041210510039018161081c0402c0b140441010031030a100c5909502150340b8884804100040003180085c00d44240c20fa401c0c00b07201360102e48d00710070803a002c9459941d100841c40080e90544651300c041c20000d4010401c003030481d43c029000d44100c00e05081e00c1e910940015081500c41d00b04d4800c03145c0064415034481c4c3e643d10301810319800a0140c00050380800c00002c000245c148a6131011074219911380505035616121400b00781d11405c0e00b81c0d84944407120404221500400d869039800c40100016034072120110024104900d8101c600140d0300021010400c0350340c0c9002c40c40c078503c10350004580719100d81015003521032010400520160880303000041c0c06401070300d07000141400e14408850f486500ca0b12880d051854080c01010541d070801b8078002c40c1c880c1c1c8008 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 957116888 1250 957115638 957115651
    0x40b0c0a050d0c02030604080c150414161805100306022d0f032208041710090807020d032c03160f06200601060905150403082b0501030506060114040b07060e1212150324 74
    0x581186450786c803918203903441450014508210041c9003590538140100921903003840c903084234188002c089a18182d8071014001050a40c1c2100780004014500340c56454007680c0f00307c07115503459036200c01c03680805c031152030030316640950040c0700c641c0441c038082d0300c06480c0d1203403000e86020503990800903480d80c1c0c09010b400300011200381c5500560f035403105d40703030000c507280c54440c4034a5102c2c105481d04820079003002e03600980103410413035801220880350030f13102d05080c80103910751030280d9005035604603411044240718260000900030740200340368054650581d16481559111021a9618841d921004109001c200504038940007a400c8400030070303c041081c420000c02d03099518050314000e1b0401c3d01e0b070b50409000d03c1081d6800418000c200c07003100000604051402d032841d0164003580501600e5140c550040265560041c0100030007100e0002041c1e840d4410080c2009941d1070480b48072402c40c8400107005181c1c030380001da0b003c0c500326000300c8840038031448000481c6a8405010f8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 957118138 1250 957116888 957116911
    0x6030c06030721060e150f010e0f04090606060221030f041103060703050603011a010903080c120c06060102010b180a0b0303040b0c0a050d0c02030604080c150414161805 74
    0x80a0944545035481902d0079442140800c134141044810000b20702e024004040603440c24043c0041a11905880300303004009003070051038250400301151341900d09c545001c0e4401c0c60003203c0010010b0940c03160b01540c44070b50031616417081c00032984144c514a900c0c0441862410300000d038041429150956002d88560004041d401404001c0303480d1150a0b43c401c0c0200c0d40366010080241000d100b480a6a003000305065014035040c070010381445c040d0f0102a01603140041e194402c0c02c010804012401c2150200507510300314131514030b488d61000c3e40c03c0da0055091071100300342d500d40503040c1e40c01f20b4004003e010903501d586c1204401041c4040100341c1600041c4000200e402911002d00f28010103800582407400041c41d00038180813503420188140308120502d60007581380080e805078050f60000b80c02d0b40e42c0c84010b185603e4040740c400e402915030a12800c000422a01e4018100c241f26000121003204010808644450faa14003c101e8900821b4400501d600c206801850300007041506 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 957119388 1250 957118138 957118157
    0x604080d1104090e0d0315210210170c13091a0a2303070f030305071a27150a0f0e07090203040210030501080c10021504032606030c060307 61
    0x2100254100354018442c141d50380c48110404803040c0488009030300c0c0c40c58204001900e10142e03104020440c01000d0143c0310200803032072302c80c040c4141500c5607a00104000d91419030180c0042c49190140c002400000c0c6040101d03100a41d030a0035030310304d95522164030320200c3c00e1000724801010030b510001c2440703944070b441c0360031610354a0341200a8800001c040c8000c131030900703409144070722000689001c0e90104030204400c04880c1c00709015281d152030865500e60035801c020000d80000f0390b00880389904402441101b288404c5913400d01030400d8910000c00d0b1541c443c59840d500101104452040300000013140d54030581e201c0d0b552548038440c00100f0483d01c0a5140c40c1444a40014103015800400c0c4001e40c601000c40300980c68103803400b0b02156060100842d190391070b4103d03080c0507031640c2c854648113134001c0c40694401c03034051042c40580d203810300b401000c400080c0107030441c06030101248281901c0f204030362486080060000c00441d02c81400b48141c0d42d10060170a402c1011251 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 957120638 1250 957119388 957119411
    0x1d0706021005090c040c0516050610120b060402070201090f090507030f0510210c150905060301120807141c120b03030910020c030a03020706120c0e09221a1302030604080d 75
    0x188d0b074450300ca000f107008020902e450f1503a50f904020a030000c40c0e2024403190040001000050480d50142044c1d401584580f900d2005030754001d0950055621960b00650100303021015610062268120b41d500784221084c24078079030100c4000b0703140c11070a81c069807418029403207810203000e881d4201004103969000070303480304240198103820101e584040c10518460341503101a422010700b80844003949154900740c44021004080c0d50f005040c5030021840c142070001010348036640282d120203441c00d1200a42503a01007500d4100c005002c40c0310101007004034540c5100e12511224080d000710b00e4070713203410308010100b0b03080201642103100d100b80d61440c03520148144c080f928825002061600d00b0018003030581e050404110004078a442540c903000c40d84100c18621060040d00e108200345c4900001c10f240c10484041403d841390139011850070020342c0f544ea02c81e00050303440c0c1402941c99000e00c1d61110101d4a030040d40c543c2c007a0000c100850340d004010028456401000035a045405 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 957121888 1250 957120638 957120667
    0x209040312020c1c020706022806140a2919120302150f150616020301152615090106030b0f18010b1005090102011d0706021005090c040c05 61
    0x9091140f29400045061810959034034034880c004c0210b0028105141c00e11314000c0d900d00051446120f07540d07101c1d90852140100319064040300c0c4d00650184424001244040c40c40d1a003a542c8502642c6860302251800807414041030040b040c41d900c10072500200310410451f480007442c07801020b020b88500040c030315040d90394881c0c890304c80d030058061208034406140c19808014458000c4c0204d0034100104204c01800c01032400a00315059a04c0d0108211400c601030024440250107610f880c801d07410300c4450000c0d0408030340400181400001c0c180d425820041719842c00303810f069001c208076910703800181560f580d00c210140000244555070740c17120300d2000741c01e603520440d0000c418248200342c4400d440c03042a0030043c60086c854a0200000714207a51010820101082408280840d6680c802e4000314041d01e20f0403605404035408001d242d440305000d210380c46c050310034941404070001d0300b401118030503c060340107080385444080500010303096601007001009010480030059a002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 957123138 1250 957121888 957121897
    0xf050d02090d121835100e0c060705031b0f06040f0309060c020f1002030c0102030c090108090d0c06050403090503060a0603060b030a080409020906070c06052d07020904031202 77
    0x40745540c0c5012003c2201900e09a5542114150011510003c0c02000705848070424102001030b40c48503107003420300080c2c02d001820010854280a60540040000095003104100506803005c0c0e5401681d004200706e01403141c030400800c5071300f01b032018403038070f2078040c000c0c3d8803403000300301034541342c89407c0342041c24060300701e404a5402000b0781844c4241540709022034050085e41c2003d01c40440540c0000740703102c000700da41522030070001e01c180040c1c80c070910a540750303060160025900c0e13052500030880d40d5005641c422780085c8200c000207601000012b00940c03040c0e41500c0e0025091805d80310640607000c002d1050f030903c080c146000030291001c00a452041840c0d150001e102d90039468440b0581310640540d9200741d12510404001c69142c5c403c0300e040784d01e92080169289031200208400703006110019051480003c400107281d038201e0010941c0100262800c160140320342203420000404012214114100b4010f840060a00749020303030b04140241454107456075a9480e000a80e4031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 957124388 1250 957123138 957123143
    0x60f19030c0e0a1809030302090d0b0109050c0f030103060c0c020d0b18010c020d111608030a0306050102211305040219030e0d05030f040c050d0b010501020d09060f050d02090d 77
    0x940c0c052595610b54498100d05403200221408451180381198802c41440b1428200ca4440d0b90382c081501014040c0d0304031114401c0107403144da00464170381018054603400340708646010341800b00090401c0c41c02d6048892803c0000020b03070640c0d096444034001044c1aa1850781448408801c0602507915010070308101c0c0d01c12088841146041208006c0c5003110160040030380e8107151a103d408c5070042a00c040500803480c1c100240322000c0c00c0b00340352241d9000e0035040323000000c1010801902c08401813035502c25a841c1488a290390780c0049a03500c1c080003001c9440c003211584820780410220084c2021280d40b010300d02015141c2d00028200c0c0e0140c00b0070800c02d0352503140c1816403605401100140322401000d0040040e0021020b0f180784002444c40f01c0181e0a04001010030000030305140107090b0261001510032902d01d031070840b100303080c010b45015200d00e818100409108602e00d00c2070396415540c50010300144070301500c107504260a401807103034091040d01314039141d81d070382c0701071950 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 957125638 1250 957124388 957124391
    0x1306050a110312042a1703090901060f0f020f0712050c10031505030604020a0b031312053c0a09030f0501021806030108060c0f07060e07030c0506120105060f1903 71
    0x7840d1500c503010100c18140c4010300045900450080041c0c0b0713040340c0484503120143c103003c4c50386100300c6d030461190b90211540000e00100101d100340c0d0000183c5070b2254542c07202401d85850b410142e030348410b43c1c07100d0541da0784061170600100702c1d08540d02001714854012034820140c0c840024031a41c4005003142c3c00a0b6503400d881d0248000c40b111500141740c10f0300503200d1402c2c40c0d00811802076550007500c0340d580c8004045203500d01403d86004030140c000b0710900204412000080059003c03880551051303050007103030145800f80505e03117095486514000000c0fa941051300b024150000d0b011101489a9008004013040540d10000c1545114000040e5100c601d1004407aa903805010018000d041c18001405001000240d454200c00c0c01c10225858203140d0f205d803040c0d4171071442d00401090901d2041f0700040b000060280a0700c0c454500006007649480600c100d5001d2229080210105200104100d041c0310008021210340c446000340f4000004d006101c82114034116040000d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 957126888 1250 957125638 957125641
    0x304110607140f0d1e0813050c06030c041404112713230105220209150903060702060603030a0e0604080d0f02060105040c21060312031409031306050a110312 69
    0x96441911965050403c2581801d040c0d0302050082c03241d10010242207c1c0b022290b444814044204181d4480c02c10003403a0941e00d2618030140b40190b085845542001d4001035504040d03454240640c0c06140e13940d00d02181000b050341c030382545101039040910340c5810000c2b20b9035140d0700d80003042034585003c1c040208448a890f4450040d1500d861200c038811041d001c014000380d6034441a0b107210b1a0303070042c3c0e15040701c42c2d002c80c0c1d0000c0c4103400081d9440701500b420740318084c0924029015a140860640310281d03603100050b078945034215005645600100302da062a0b03801191445030050340074081c00c0c14242c54010b03551424010301c91580114225508001c03c551381040303802c0c09007006560034000c42d00900400b901d034807245951b891080005c10b08060704090107034441da00864101d001c4041c445014074000d4020061071203101c40e50815100080e450450000444400f0800310040c114803600c0c225007150180c1100800c1e000b0005042d03103d0304c401134100040d110103600703041000d0b001d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 957128138 1250 957126888 957126913
    0x40906061e09064820010c03050307020f010501030f0308150a0b0703030f020a03151203090312051621030b060a2a0b0f060d0507051003020d0e0102030601090b0304110607140f 77
    0x174251800c0e842005a14440c3c0d000960399120092030025585030402d591682c544040582c241500540401d50315840c1600002c140540d40c1901c0344401c3c0240c503001701d2521294a095185100314401607000784e0500740c100700860101000f000c94038040e11300043d00b9001494501c081ea4001510f1100107a1913641c5820351610086042000f08203c17681c43e41d10f84801c0ea000303000e20600f0f03c0042c003901c020245048856000742c041f00c040c8241403c0148091010f031615111581415040b00f409000310802c00d00c0050082c03144482410008241034200000d82ca0110f64030b03911100c0c000d20314001002810010003117201c90740400c0e03214030703100c0320035203800e0f1141c00b6840c074020180c501c5500e1000100005c50340124400c0d090750f5059503031a401d41120389042d0080d02ca10000b18a10600e0441d03006800d031419800b541c002c4031f0907a100c1039050398074074454189000a4802400031600100021100d141520041605a1040ca98840b01c0103556100071304080c052000c0c81425013080814080 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 957129388 1250 957128138 957128153
    0x31d03070f08120a021c0306030f14060108072105120f0d1103070e120f030a0305090111041d040303060f060203120a050106091a040906061e090648 65
    0x143c00300180c00703040c01003c0c2d600950303c4402c040c60a010f141e03c802c0c07140805109030080300107503030810300d045402c920500c4c19072a041030360382800b019406610300100e1420004200320003102c510f10070745120b5803001c40e00c10542c80ae901004403040d10541400540110381c64000c2c0c10050049042076455a0030100d0b1902034510403951402100c104100300702c2d80942011014079850350507250070b2640e400c040c80c120310740600d80d10880c103544070104030504150780c5504010f106140d0303400284110b0f03819840030f034080c1c0a1400740b000c28540c2002c2600000c5604100c1c01e9003c0e010380703408503a4980ea51800c84104900744c02140058000090500180320490f038820340001e040d80c0200515072600500500e1441b0ba40640c038448155154000c902014040030368000e8419214100f2000740d5551000e4103e8804e4810280710080c00d220306001700c0d0240c4503a8007200d4176510360300e14802c0044820f512282e400e102c0c0c0300048224001d04002c00c0190071403c00c80e4044441282e446d43d01f075050100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 957130638 1250 957129388 957129403
    0x5040510083f0301091e0e07140f010f080928230c041d010507020609070f060203030f0406090f03050a031103010b1e0d11130605090d031d03070f08 65
    0x25010104031828200142c02c0c044a04442140a002138001c1c1003109101c400014080070640590400d00c040503419004195441200e4503040e4001d01840c010060082d46850700c062507001c01d1515550040040c069403003541d00001000c1a55400c00c3c0d030341102e403000c1c8405460700312100441488201045190308111062800501d5401d0011000040c219694400149014041c648a5030035540c2590040030b52504030310b141009002a00c3c000c1402540c075207045a00c8401807284040010b046c0003002e042100703550041d4091461a07a65040451144e800508111601640d03400003201203904810142c4070ba510940d1440c0c1c1e40c980302d0f02c005060f1421040c000580810400041244d49051400c60b1000c050305074017620b010340c450102c00310318007948075100250f41c1454104040004504010151b0010140142c50034586482c011074581c001c00780c540e500100781025a40120b40115620491074200201c02c00f81e518260000c2420120194440100341c0344900c01404010010700441 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 957131888 1250 957130638 957130723
    0x7080414010b0a03030320030c0c06010b16030f050f03070801050a06090819141912050702030c1908100e19020904110a050612040210030c090504051008 67
    0x90010b420042d0010700c1500781c2d0303c001802c4c940d58684006040621142940c15801014031080c3c9078034140340460320b0350f03000e851100c13154010400086040b0204074240c440e60b000b00951540321059556040c2c41d1410785d0740b01a801d1040c10306c482c84550789494003c5108844503520030510f945440d05200c600342c4588c004e0b0f02031002c940024450040c00185591282c0c020303411748141c4800c0c0381003680010507031402c2420a409070503031042000111001701030006200341050803076940c2440c03045a15000c0d2600003941600025403083d03041c64400300d501006148070b90810401caaa5261a6141c80643e41c00031030358584030240c03401020801d001105024004001b001e0706035003141d0004034027041c020b20090061781c1d2202d25984035190015120080c05014210b10790f02c1940002c03000701110111012842043c203040c0d148001c0340b00f03000342906440e4940301c0c2c803400c60804003000301800004080c4503541c0340d0940b0000301084104810b503201d03069010b92a140e80c503501030310b84256a070300084c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 957133138 1250 957131888 957131891
    0xc0d0e340506030c0703180506270105030f0a02091305100807091a0d05070b03040c030605090c010212090105160c0f090203280207020301090804140301090b04030e0a08060708041401 80
    0xb0064003541a5040702c2015906144c00660103588013582c0380c101c060754200c10b405c000040b542e4003043d100300542b83c00c841c0d2081022444440064011601480100d4611183d964244007041904449401034058408000c20014120b5481c60902c0100d0301c08962400c8003015588007003202d01c03000d01410002e45980d06050241945400100d07041000ca0720304640a02c41ea81991000d101e420b11629001d0b00072100c42c1a66030a2a00704650f0120850109039201407510020521008000903424680c074810b8000d05049011200c514199400c8512264180b1204015500d045129050320260251290900a00a900744107031005600c103183c2025000c0340c4104280514080c00703040c40b1060000e02a11180101200c0d4402c0010f8040d80340000e406600b80781551003041107540140c0280ca40080c0900281b201c803a0400d402d99110300c2d005403200283c200410046880388084503c1060080e00c07184200b5500c10550749000d204803401d100242d8210240020030155070b21041d85555003100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 957134388 1250 957133138 957133141
    0x110f04020c060115090305070806010906051807050a05120c03070e03070815042a05040c17191407120501050406380c0f1002030c0d0e34050603 63
    0x5180d41d9280600802510b010704d940c00d800ca4a03c101d13011405107500c002952005981e902c140c941d41d41f02030040b4110141800008165801c0140005861091604003540c0b2178035500c4003130321258003544400c0d04101c010840d01d000c16002c100c469002d54020704105a0f24a0701c006e0082500f225820801d01c01c0d0800b2000b04018400081c102c2c846d5080780d440714420340c80300e2074000700d081c0f100700c3c1c014114980f4148032009990f1200b003140840d44151010b1150340c0001100701ca108040440382c4031a10503d00201c2c40c44464400341c102c0000ca8042d0024400354940010a515002103804500082044a01c015128407900500340142026141800380030b00b0242c400364030480c4040303014901c9656502c4001011040320010040b140d6800e522651a110141502e031200e0f041103000b4030b82c0c803030107005800d80f80300e0748210384c0304d40c0700002564100f40880351104044e00c030103641200248100000c03559480c40412145c0b8485211400d18052542e25017004640304a04c0c1c1e0240388034500600 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 957135638 1250 957134388 957134407
    0x403020f09040f0803070c0b13120201060807060507020a0b03010e011703040308040b0c01140c0c0f06150607050304030506010902030f10080309040b0a0308030103051e01020c03070b190504110f0402 87
    0x1c80604240e2200049072665240541150b1f188107800b006001ca141c0502400b04000c51089880109030150a0403120108480e00507401c1e40c0c40351013034070f2441c0c6c07207200204117040c440c0c0050b0041510040108040940e0740003500c819030420b03080010300c41c0c108001080410709007004d562071940c0080186013460329649603100140264841c8110300100000c6072007500c2c000390700804205000381000203a074100364140020710303000001b204009100b4280040b0105d0b4000a282d4800c01c90400800e80884003801030bc400d5401912045407144400d0001100103581032003154060044070100584074544801166841c40300502462681c2d401a441800740d50804402c0340c145e1142502d0119100ca01e001c0820519859a4400b42203544003000100400502081d0400487c0e5040350007400f90036031070b040c903080744107590514489a108002c0240040c007810070765540300d114403408002403545039401c4815640101c904a070945a28500890949445d0314011015141a00c0442c07c1c0420712 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 957136888 1250 957135638 957135653
    0x506270105010c260c01230114011701080a0213140c0c0a0c0b0309010b0a0f0509040606091e050108031e07020d020310060e13020d030e03030405150403020f0904 71
    0x41c02424100043c20400c0401d100c24000c80b9110b902440741486152000844100391607001600102095403e005c1c01085414601100c114001007007103d0074110303440d0039050041425002401c80c140502540003094114010201900030101e10001e462809110b01c10001104001c0e9242150185002c148240c0310a8038a19164030030490110300d44c0d90047c01030032a180c458203200c010700340e1031010340100e80190b80c00d01842c01001000000e00c510b07030400c0104050750758280a040c5403524111802c0240345400f00340140c0082c090900000c900c0d881d08444000c0d103d20f640401001641c6106644d02040a80f00307a80c0188036a03c042d60924002d8501c00e0015403080384401110800442c0c03200543d641c0300400034015600034201d03100c00340311004400142440317214428062004400107020100d28200c2c4180c01b503030042001024807001d41c2d040c2c1c0c0c1d512807175807895090700c010b203c0821103450700c1000c0d1101c0d100c0012000d0302c0713034a5441000040f01016520b1401586482c09020005011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 957138138 1250 957136888 957136891
    0x121b0706081e0702010b12160807030f06020f07020a03110117070f11010609060f140409031218051f0f0204050105160f08120106020d080903090d0305041206050627 72
    0x2030710003400b040e19090b5040f80134250805a80d6403040126902100d18000051128601e02c1c00180f95540c40d5510f514103510f541d1544009480000b6800c00c0b50001100c90303000f05080103800100d14203101d4544c01203082c3d603901e50811070354015440f040c0e107415a0068812244203c0c00d4148501c54070701154001d04070380b4809098020310584d4889003030800c60a42003000503000c0954204005035465003032861a4a480c402d2030110342d414501c203581130038580075810760070380c040e29130070606009440b580b4010081004000c0d58032445000c0c500004105020305000d9110006020306034642d070b40200300c1204c220702c002c0c007500e40c810001009940d800200b41c0301080c8607240d0000303c8030642e0a000201c0300310079000810890700080c01080800c1e030702030301a040c0d076059821100e01c41120003081d2604202035508010a510902800f80d4610300715100b40045480381c0b0f02030f0b060507a0b5200b04280700004040449030349849104100203070801e1607800c400c1d00717100449040b821500c03241c0e0118a0ba030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 957139388 1250 957138138 957138181
    0x30204051914060906070519120c080a050906070609080c0d0224190207050a0c06030216230a0c080f0a1208070509030a0b04151e020705121b070608 65
    0x8021032559940d1780da03002681e4080390424103840c0b0320100d000705501d91700810f12045503038518420a40b0100da100b040603c2815034050141803802c0b041d12400d48064000c1483d49501c45010011080000d4280c000c814003184100d40711500c0c0c440074030003141020b803100305080465007c4010240d01c8643d05a80c0394800e404420024055100c0981042c150040e40c000191981c0c000142c080070801c002450070000d0380510b8981c424a500d82030102c090348500c41e61281514110792100c1c000c940d03c1c1c48040c1403252103000e084540300b4100c0241c0d05115542c04181c0b1540300b000803c004015040c8604500a0307125009045078203010340c1d5040e0303001c140c0c940100c2000801c20011710618000d4086030070040d401003c0b9000003440d880c0088098504442c2141c00c01786c0e43e0341880c0c100d001c0307005850302e01c00d64801d420041d88a002c0c0c0b10009400900c41540e5600c10141c09050350f049000c01040f400782500303e00085601a48800c3c0d00d0300b4500e0340940100034402c001c00c20300000d4000d1600f07135100b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 957140638 1250 957139388 957139399
    0x20901050906060712050301030c0b1c0f060906090b0f010302030702060a0b0103180f03021516030207020303090d0b0106032a1d0a060e09010b090102070e04150903030204051914 78
    0x45558010500c0c1380200b080080c51840440c42d441c0d54203800c0400386048a10070303228038040ea9100c1c0000c84007801032081d0314010056030119289207811700e0304464149811568005446030b903030b00c0004d080c4d42d446e606c01d0501c1c542c0c5801121182c00d20b0005031900e450203003420342c03450030602c000039964900100960a035a5031405d4400b02a03120350032450324411042c030880c180407001e08080c0e0284500200480161142a1003101c0304c130358401041d4401c0b130049400c200c00407903841c800c0e8041c2d4000081281e041c0000c000c5c5941d940d46200c030611645000c0e80f9101c4066042110140443e191610b0f07030880f8220802c000810f45070300100c051242c50403442c211044600c1c2c91400200644003554540d400396020340d010810310740c0602c07411006081119000c1a0780d0343d0b10541c0f0070a01c07502c00143d0050300040c0c0240400702005440a400907c5018500c1e1074407010340310601190f2060b0422800650000b5041090340740011007a41d0007000c80125810300792402c0000510080480410350080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 957141888 1250 957140638 957140641
    0x11011407021e1c0822080316090506031509090601030f080f1207030e0c0919021b0102070f0c0e1501031d030c0105042a05010309020a0b340209010509 66
    0x9403002d100f40c0c924140d0340301914000d038000e00005002c0c000200d0b05909000c1003400401005410100ba445540d07410041c5645151030710318410011481150405003409a0994009256115607004510614680d8040b41201d01214200aa81c0002500c01006640058010b0010854000004108991000015035a00750618003070302140206144014000f1074103080004141d01900000d00402c40b0a007912200800d04041004444080c3c5a1818000c10b01d120420b20850b01e13070081c10156034401950b420b10041207001c1c1d007a83c0c412801101c240c40e0081081040141c800403000240081c2080401503203070010030400c42085d8125042d04241d01c40c19100f03441c2c81c40108107050040300009980d86d801c500603150707001c1c080540d03088a2580d850320304450b800c0c140809207810308000044c01001d06d46420011000f4103007903107003a41d00008150002541100c00d50042c943d50950074000f4002000100403505401f0102d030746620a800220900c10042e502c0301700140c15284119040c4589 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 957143138 1250 957141888 957141943
    0x6040309080706080a091509151b1202070309030c06021507080103390f14010c05060f04020316180507050c070302090a090b090f0f0a0b04030f1101020a1101140702 72
    0x4900e00d0007d9045007a00d0800c1080602440c21110005078480d000d05010120512000c6003418407103821a0b00080c8006011208514403a0020001c1c41e000380703807480026860b900c0da031820341c0310381d40070b000903900016001410100040902da0311400ba418940419851511002c411640e03021000d50443c01007000280c0c4070101c0d000360314881824840145c0f445071a0f00c94609021054001c54184070900e01c04400d4540c410028120015030040c040d180d04c0d02c642405445005c0d014104076818000c00150682e03402c1c0c0240064002c000c50040540b10002b9541c12104a40300a0f280201b0020100300a052100001800404495040d00c103030059079a030b410a00000c128444000300304240400074000b440100107141a40c4240d480c040d510850b800144c0c3d0380c1d540c0380c00d0034010320100051000801190007503540c0c0982c1890f605100000784101c0c0c5265007280e1060007600042501d52401405124003440380c111401d405580c0300c0e195040800c4081d5640e55510102d80d80c0c0620000440314 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 957144388 1250 957143138 957143153
    0x5010b031602010e0f01020a1805011b060207060c1707090f0b090307091107021504050307030821041b050102011406040207150614010314040c05190806040506040309080706080a09 79
    0x318039405043e079540c017200c005030078003079031051802da00018641c0080100700034107e00d00c0011104142c4902880b400f50154840c3c104949040c141d4400b40c0c240800000300300035000d0701c04081415035466440b980300c90001c281c0250090010804c1144566040c404066990360100941e02c041030820307190344da441c000a1400805800c40d00000d0304102c1c2203802140304402420b0f400d8401ca804a48410a94008000c5405203200f15907250b800b1000c1000440c080d01c00078228041022103407140a8203543c0d200c180c08c0b400350707821104130750140180110505100f183c0ca001d400c00744020300c00c0ba1403510644000d15401b400d0344d407083c1d900107401001c11048121866003030303070564810b209640e42c50080031400440c28182a01103420070050b03c54410902c4105032055030b0000e543c02d0054188014011004050245c2110900c0d500350041250a4204002886948590000c1020f85410b150040c952103580e8011a290b5001c0b40041c40390b582c00200160740078207007400004030900141070120 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 957145638 1250 957144388 957144401
    0xe15040b1201230f0a0f0e09060c030903040b0f070609050708060a0c05190c020a0611070f1805060f060c0c040b040c0f080a2c0106050f01020a06110d020f0304060f05010b03160201 79
    0x70b54446c5110740020503402032034020384505021000d5035140e80e203000140307040344001c070368090b4944c00400c410700c00c2540c082c024051110300302408504203d8940c0c1d514048410310074058840d907020002c00c01c0030090401005a02c111142020300c11413041c0c0402400314000d1126889a01010002001040c2e00c51440000100d4001304906200f83e0f5a2078080c1000c54881c0c0d80603d41c0c010a4001304a2030401034501c0100c4070350031800f034004062820707031000030180601826405080d8240902490740c0745001340c5500d4096002600e03007000d805080004551048074518092402c0c80d10b0301d82c1050b040081c08060350380c00d0a0420066032500703903980050843c0c44500c034808000b030381c1800c01d05c500d200c00b401c2000d038400000c001040d00c80c0c04100c0320310386d8085000e005a00c50444c041c006882c3d0303006418908008841e80d0304106100c802c9405a03001140c1e20192074801208000a104043c042d0030720400c01c42000f00040c0d41015001e03812440b000300030321000421500d03a5600c8074400d50011 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 957146888 1250 957145638 957145649
    0x8010909033c020d0e2403070f09062309030c060d150f030f0b1909060929060114040807060201020901080a02180d0203160e180c060a0e15040b1201230f0a 68
    0x1b0f5a403458140e03400b0f40942989a6100006403040901280e2070b03000f48103411040c503400c40e00b801c4c0e400da0011400d24552110755225058001e1115501550301c8440140507903255941d400725400d0120114010410441da2040504922002040020810f021140400142c000343c1c01c0e02550365820400080c0c0d05a810708840c150b140840400900c001980600d00a921900703180c8024180c00d400088004640080d812071021a00301051040d0301404118191030707484010366007015135a80245051150952004000d80d4000800110540e489146c1c2c96100750001030443c10103610981401e07030038480c80c1c5d401d4000e444070410303d000e55804021180c0b42690a1001c3c0b071313605031a00550301c41039806a81d0990580c10310b02080c42c90307000c041110f041082000d0710030b85c00c0c40481842200c0c2c1c00020050140c00210032070002c092001c0400003440075000e80042c0d265540b01100a2503c40d03d8140d221084000d025202c81c1412a000302106043d0390048885000b1103032485c0010b00050503d9000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 957148138 1250 957146888 957146959
    0x70e010f0513090201080106030b010c080c060709080d051606020c0109051027020f01031b020f0d2a0c08100504111008010909033c020d0e 61
    0x25000c00380105081580c1d001d8682904082c900e108030400e6840c48940203011401080c010300000e407195000c1c7e514854145080c060304400394032407a80d10340c03194070300b03201c242c000404110280750040500001080c090008140341410307460300404900030707415031103070600e02d41a041e4140b002035015118030300c0c01c5100070807103c00d842c40e0180d51041c06114800e03c942c10110290401b510f40b05903d0400d84c585807054640354510307420003a4035240d91100318141a590050000396a92010842004460507001440650070741005140b80c0442003c03164100580910704030318000c0403000501c0520750403000403202085c140f51888120451390404010740c46030f02601c503500507035900428012400341910f20aa000103105100384900303407041110100d28003500410100c0b400d42d200c002c10074020b180095413070f1802c5e201d02440400c1c00350040c80d0310400b06600802150800d0000380c1c074446030700043c020410f076a98064400341d08145000e1041c06a2340000080c0400d50a626a010005801 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 957149388 1250 957148138 957148141
    0xd05090a0f091b09080c0402070f0b040b0114061c09260d11090603010b0721050a0305071d100306080d0809120414040f0e070f08101e020705070e 64
    0x544100070000000c3c3c040c44904000c283c01c40150090b28400161102c050103080304a180381c06104c0a03500c1503400f1600781c0034140c2080c02248404601d503004500c40d81440016501d040e0184101c80102204140300b001d0400c0b805c02010290703034028049200d10070010850041c9410403199202d1800c11203960700362499a02031809042000803d00c6014004041180c0103101c0c801c441e032070050700903441e0002d00c00c100601091040d50b020f400032520800b0400b10404003505265131a0045501c0e0502140010039002c0741c2c00d4041c09090744c0410603180c6002c41044034014207002d40301c240607950003030441d505400304052194105102030441d0004960f03c0000c903220043c4210801c0383c204e52a4043d801c03502c4d55000f200c00888044036a0040158010100d10301000018550012490541035030b03281001e80f0f5000c1480b210b0014040b21141200c3c040c0b405000030304044d88240340d1501507141018840c40b044007039060803600051200c005071110420b00e001c61429019403c607814141c014030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 957150638 1250 957149388 957149399
    0x27110405040e0a0609060b100c050307020906060c03070804060e06120708090123010614070b0a0f1e09030f02010c0c1b0e0a06060e0a1211130e010510170d05090a0f 72
    0x10402c06011100303542259a49100000403a504914270800a01c2608104440c00143ca40f5401030341d00400d00400003071821500e05011451940808806c40348401e000c1820010f1035003140241020520a4032443d1034a008408180301300d03c8014801030074012035a011403c0c0540941c408501219565000d08a200c030b40440112065002d1041c1c20003d000940303400c24410390740f4150343c000f40d440036290505444c0c807801c5101600b40b41019409550707842d03020300980d600c5030300104404609a580041c841142d420300610b070003046038000065a0505020204107030b40b20081d8180e19802c001c404100c5000b00c415004200007641c4410800800300052004113040c99102100300e400503180c0001800d40c46c01407017101d528511601240c0a2807090a2003c034003034a00429039880010f00001001c042031003000c1c02c0310054090568540c0d580c40130455050b0000d9151006003503030414505240328005049035640045400300001c022002c584903106841c0c0b484108050041c21404069594440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 957151888 1250 957150638 957150641
    0x30e150705130e010509010f0303020613080904020f03040201171012060f1d01050906070504030f050109020310060503010501090b0907321908010501050d0b180127110405040e0a060906 81
    0x20f00030039111b030b9080800040e80c500240d151204403035041d005408540e440725042c0d840f520942c80292450030341081099441e6441d48010302103a1a03050060740c89080c00d0000400084142c5545600c0e550840705005151a48001240c00c48000c001c0352a2014100e14014010304044120b160409003448850030484240107107140a040b0040020003050355401d085969481d800c0d5810030100314100030a00220300c544160003035050091340049003543e03480d80820b18048818a000d42142e91720801800f5500d020700941c4c1c0103104140e4103102c1d0010000000f201814081d102805010a81202c100c2984040100461541e4506000c00ba00101500001110391180740309001c01080c4003540000c1324080d0b01d40905075101a03590074241401400c1d000f0050080d00d00b1706501544440b1403203425171880e805036010b0940c520a222000502c043d5a1180d41003010b21580c0480c108290302404a0139042590300701c500172500420f6454601400380c1c10100c5940011380100d00b07298856080c40302c0c6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 957153138 1250 957151888 957151891
    0x204020d1b0212400603061e080c0f030f0a030806090a09030e06030a06090603150c02061b03182a0d05123006040c030e150705130e 58
    0x15a0241d0703a01c02906040e4050f207101d00051007449100e89100050810425106042d408001d450607180009200f140800e500708641e00c030800003515002c040c060f03a201a60640410f0030b0651f543c0010504081a0b0350300c0e0703441402e5081c007501102046203816a410409680103c010700c0948580d1095405c0040000030201c810500903c241d40110b200c1712040d124100d0b0880d09940c494030340030341040400c10f0640c40035200104180d1103401c007050303443c8030307101d050700a610a00d00305903110684a0702c0020350302603668040c150340000042044404449512000d03600d000741040e81d8a43e2020400c041d91f41c0902401c3c80c00d40300320310211a04001040030354664000e80761440046207283d0041000c03000e00d40074010b01c60b4014110a004405004001d07008840e04130541940350300b02000e250080d1040034020490900a4609014180c10030f81301d00d41144a2525003071040c44c000003162560380b0351161303034000d044119000040c540c9116100713984043c590003040813030556640d01d400c028403d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 957154388 1250 957153138 957153191
    0x1903030e04051323010b151b060c071103100c03020c07080601140105072d060501150e0f03280b0603030310030b15031006150201090803010902070204020d 68
    0x60400800c082d2403d034070081d8801035019030b01443c407000054403007624098450b0700c11020340d201d00204c00941c3d00c07841d01120099409242c2901c40d0b10b602000310354039040300008d26090300700c6c40910a036080c1140c100c1d5140c503040151150b4104105002ca03160101e01c000c021416031074416001c5c1300c141c2c15001400700c0b20002c012501c02c0b036181c8803819101d0100384201000100700314407000740c5501a20103008240d00079000081c444c042456039010a0345403a0101c02d800c00310b11142c1c4100103091041501600040c5050f080c800c02c2100054000344544241d280701f000040903904856804020208200403d20071410300c88240c14050092501c1038141190501c01d5580007a400b41000019203119610a030740d60440c092458403032343d629001c050300744030000d00110b181c85226101002820344131219035030300140c103524011500d2014542800120110790400480d82c010841c50010f07a41524400580103130b80d4085480010000c1c807076012442e0309241001110036102654807480c070900c1c0c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 957155638 1250 957154388 957154391
    0x1503190312020a051b01151e03020a030809030d0c0302030d0207140a053f09060706140714030f04030f11010f060311090108061306020c0a05071e0e01141903030e04 72
    0x218019171900740c4010152403000341c0c51000b000c001c032202c1382c0100450400d0307140b4101c00c0c45803070342c000c40c1000c5600e81064558150002d02005541810420950154243d25064040c2d0003a540d0080d16071080c0d00c0c106038160703004112502030010410391400c203500d40804560030b00304180303880c5d034075050000101d44085040080c94a00c298019030740301e415005070760305907910310f400d000c03800d469800594a8540000041c032010000840d00d200f0381c0402d038a500c05082d514500b03281c0c001c100d920582041030700c0c880705105005001c83c141c1041900103915041078401072961039005c4803030310b004846001c0303d5801c02400c023940c440715a0054040c3c0303015140002c50001c00809021860307c0030310600c11980e1040300000d44400481c1d9007102e210b40f00c0e01000d403a08003500d80c0b40d89452454541030b500741d0084603013000109402c04005070010b0100d02e0a0710420b2030486040c82d02c140501c01c80301031100c81b01844442d0b544483c03034020000810380c180e040c2d03d038036070800409050341c03103c0650046 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 957156888 1250 957155638 957155677
    0x1110f07090c0306050102031b0c1302040806010b0a023403080319180609020316080606090a0506010f11030f04031208070c020603010311011205070e0103051503190312020a05 77
    0x2d846805280e00b501d006800440c43d1010701203956240c40168a8644460301507044012455581c0c40e500341c61806040c0380160715141042c2c58a81040c4060f84502c40402e004c1182d0929182c000c544000b40e4202028040345080300740440160f005c5003443c1450715151503080c04010040150003960107816006908420301a070341035040c003181e001c08003000000c0c01d40034941000804a07000468802d1001d41500c8210048000713034080c0440981000403a40c218100300135460500010b1140e10a490020034060340c00e000c8006002001c00c041c1d440d08001c010100142d03413410400454039901e16014145644903a01d00302a070800c0001400600083c200102107005103209003110315043e900204141c1c44c41c1d1031642c48200143c60254424140059400b1152100103940b01c2e5500c00d14540e252286510146800141100c6001703080381003100e005402603040f030f10300007031840b400c910301d40d03001c003118a59080980381d46008030b9890030014000070309401e03420b03408006000e80c4404107102c0340d540c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 957158138 1250 957156888 957156911
    0x1061d1f081f05060901030b18030d0c1101111617030703090c080d170604150e010504060608040c03080a051308010911100e0411070c030515060d0302070303030b01110f0709 76
    0xf615000d4464580c032226071030051001c244014442a045a10088000351240022030154155000828460000c55848600203103107608030040b2100e0501600003000300d8400100805054020305110900e01e4001000f180104403c6002c400302c41003415481907240d243c2800e0003800b521003214101d511140245001400c0000011260280b040c507844000c085038000c13059030800030f40100f2259106071a1a000103106d0551002c900c00341c4901001040340d503041c0424007080e560300c5c0e440350341085007420030003021445e00d50600d8141c81d84403511664407000018125100e010750080d207025424016070014005c6815802810343d10310130500e803070b82d000f42c00003080980d08180c0c803043c1c0410000300b0865001c1ca425400000b0807042c001001e810140c1e43e884040796800640c00c1100d0030743c404116614002c00851066510250480c0c00b104600c03640e1303030020344400c85480300405160b1213074004022070307026030170040509101c00116180200450f40702e6507a0b03212031090300d44243c40c21501101e03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 957159388 1250 957158138 957158141
    0x51c02030d050a0c08130302130504051209010504051201020702210106061b0320121b4c0f1b020714030109080c06041401061d1f081f 59
    0x50f441064542018001c0c1a495180c101c0e4000e0301c0c054502034506a000c40141e41d0080c90681d0070f0b40d04100020285064600545040c241c8445200c4408090086407401d07a400380c00c4409543d400d8400c0008076a0300c503d054064020040002d620080039520500701c0448551400c0381012950000c0c0b00300c5a4415058034400c00880b01358100951522288020901400d14a03a541c100f1001325000001d544040c6400c001190314000e4040400050203a0410a1607038584000f40f14031011f4545060081c1a00301071241d4002200305a441c034101104505000c1b01c0c008000c05148190003088036860000e4038020800008038a2815143c02c6072a520f418500e00c5401592040e41c00920000c3c0c20441030f040d4031130041c20301c25819901c0b200740c0d5000031b00c81c002070007841003040e004100c030781058a040c0c00c11a00c2c004070300001d03a245c81c000b000381c5a04220a0120881e1164181900d0344800081c4c041c82000c03407620324200c0f0b02c40300e4005a5010b00040c880400c0c01c401800d13500c3c6260703aa01080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 957160638 1250 957159388 957159397
    0x5011d03010e10060f031a04020d0b070c0302120901020604260f0c16050f040e1c0c0212161413090b0618010b04151b030207060f1b0318051c02030d05 66
    0x500001c40e01040403400d0b1f03050014a0f0300705000401388043c41c1c80a940c0d00ca4081022a06130300068040000d040401d81c0400c11a40b403a210900a181800704140000395202d800410160041190388010240761512100480840c0545000c01d40d4503141614100459401001c00464910031010461003c607a000c0d141000e98000600c400503a8043d0010040684020100e4083c5c6004845602601c00d01c000c20701440c1011689500d650b880b044e00410001015410540d401c940050f01200340540401c1000000d0340c40300120f9113448104240454201c035018425507a0640c540140d80042c010040040c0b03104000450703184948444a0a005154060a202d40065254144014442045641c4c64660006075918049214454151300c02e10003d4180c00250f001d60006403041c002d00d640720015015418940c10850240c05c2080e01c1904041c0c00c0d0800a804c101c101a10381205000044010008250040049403450714141100751000c16681c000c17882442004219a0311a0140c826903 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 957161888 1250 957160638 957160643
    0x1270f140d06020c0106210605060105030906040f1a04030e090112030914010509030304090b0405160f0f02160b1b0c010804080c030d02180112060b0405011d03010e10060f03 76
    0x1c2204491960303030780081d400c00740700c40038655250b850104540740b80036980d40b492000054102c505401509159040f0744000c0c1c2514108042081000b00c0204e00042d078a40081d4486007c040000040c03e081500100c104002d00100d02890300344014103030321940d6083d50390350807030316148a6643c4050360500d40709251b04c0280071035024501006490070410074000c0c61101030402e9403074600d541e000641142d20540240102944d62140e000043c14280302d03055100d60503945213982100803582c080c000c601401d00f007108111030480301c082e10a20070b10200e840340c0f40300103444203525290400c1c00125008800080c9441d242291180509100013a5000e0002c1c81a12040d5031307600d641e00c1360343c3c541d40300082d180b0a51108005810400c4054801010a10040c1002c1e4424112120004003445e01039008580101e0800c00240022011501160100c0f10300f400d118a03500c50502e1400004150b210745980e05510740211509010008101103a81d001152410482113856001034030b1601c01a0001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 957163138 1250 957161888 957161899
    0x20c030904050c040828021809010c03142a0406020109110301090b070809030906040f090e120307030c0e030f160e0f0a0207143702030c090601270f14 66
    0x640b103000c000c041812003003240b005410100d036906e41c1c0104141c520104641c0c0071541c42c0c0420008402400e2285000300131480c64140300d407130400c0c0d068050010018000640302c1c2d480403499502590300101702e401d0a008001010303102ca5031030304080c0c02041c086600343c50815a207100481985410b200d00f02c0706075445040740016448460003165905001024103000e844100441102a41e41d80f01074030060aa640386080795074104201982943e81a20b082e400c2580044880c903070115042c8103603079000865150014100040c007400b00c07140e010301e0049980501400801d8081c00c07a0200d54200c00039411030340400443d5440c0316441c005002102c0e00c208914040c00400c20b48030b41034005007103c0f4021b120b02400c108443c11450300300a4080ca02036840b4100080050844001140c40d15084003882c04000d901c5c10381e500480d0300d81d51031100041c4600008000134081360b00903200c240348400d1880e00e2410101d03105070000200c103e94010b000b0300090040c400140140b501c5403d8603c000042c20 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 957164388 1250 957163138 957163153
    0x4270818030a08190507200103060909050607030b0d150605011b03080103170f0a0c142e11031302011d1c060b120106051305040308011a0904020c030904050c0408 71
    0x1364007aa24242c541c401004800c00c805400b2413850074010b18421800c0302c1c09002a031100c000501214130356400030301c0036410901420042040490f03620b900c045141030204003094000005056000c0b0410001d0884400312441d11300705a099201c2c030305887c801c1c0c03903d2210300d10244046403990b82c0705a0040005062400501c0000d07110a41001441010b03103901d410b140c20002c00900540110f184080010b84c1255401c2c18400924120028242c901000c0c25054264800310710801000c084101452203258010b403401c0941548140858103040c1c1d4021f40320300300120740b0b16100020490590014091089a0758088103420341c41514000080041589240341d540d10210741107032620036523070170b070f607610291308a42c9031940b071000c5030b403400000010100e007058200120700307401032550541c541ca880c08020000703801040c1c040c199412548005220740c41c80300a00307118403a00c0e08a6030050b0020440c411841c800102030701594004580511455686840307004660145200720b0410707034043e80 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 957165638 1250 957164388 957164407
    0x80a33050f13080703110307121706010504180b0a03050a03120b1f0807020c030d23030c0703110a0c03060605040c0e060f0703030615050304030f0f090504270818030a08 74
    0x1342803007810404030301681d060101030f464200d1041d09c9a0008804034200144006482c0c1351840000d40c440320900780103050070300f000c0c07940000f88100c41d94494465507621419446640b07103540a402594001c08640000f0b629160041c1050210209844010704080c8403105d1880c184110b222020940040310300b1402c401a2f04956040c4041c0007101540650001c4001a441c20321251b015880c050b1034407080d8103410120790002c8503ca02c5070030000d08051061240c542800c40c205d40e030654143c03401c1000b601080c1c28040c01c0c03400c00e0400400b4240024000030410401f900035404541045400b005445000c10054031403c541041041e8003820801c5100c882c041828040c101c0f00d03009140c005803407a2100c1c007d060b0b07200080c07981c5010410100400003016401080034140950034030380014100d4803200701500025407401203901c11a1180c003140c00c3c4000b60704420540d03040c0400050b03070b89902c41c02c0c058aa5400001c2e464240b810310701900d096400d0018015086179402400c1074030f001ca480 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 957166888 1250 957165638 957165647
    0xe010f030207060212090c030f010603050c060702130626060402220b06070501150501020a08040b0f09030618010c030603020f060307030e10060603060f080a33050f13080703 76
    0x1090483d007541c1c1c280700d50030710b078011002018441c1035100000c0c1501d035044d07001c02d4501480b096041da001d0707060034400c0c40000c90214040308040c07000c4da00a600c5010620005240002144c07440400500c0e084000500d00c0c00e02d21045406603040c0b884c03660401041620b01d844403012030380a504580301d200180550f010140c02c400c0d403a40003050004503550a0320000d6026400076505a450741c0d101d1080c0480308107003c0c80c4d003004000900040c0030303446d035940d6840d0840c0618480d5000f544004216000791106400403107140800c01401d41300c3c980f4000c290209a1801480781c0c610300d40c600140004000d01a100f00401d80340c0007001740b4415020742c000c206142e40001c04000405854085407890110100661001c45401c858040f4800e818008001c080b20300c280d00500e041ba00d0b11008010240f0040b5400103000e801c030414896103c07441d02d03403d818040f03031011041c00702035055003e150040a940118000c0d1059260301049454020b036140320b0a9a610000d0920001040b510000a008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 957168138 1250 957166888 957166897
    0xf03020d060504061d160b0712142106120309011403042d0b0f0106050403060b0a0e0403080a05060102060606031f0e0a060315060f060807090306021204260d0c020a02030a031107060e010f0302 84
    0x7a0101c41c540502100e2f000d200f004030312801d0160348501401d1045c0b40c0b501c0c4140300d650000b1780000b58100135030000024000c0d49103181507840d20034000041070a112401c1060b2141c11030041c1215100d00c00038a00303285a42c102e00c429500015054007003001240c90f00c079070f00d040b14201c1d620242400d00b1612614020a01e04080540c4400e45400000d042030104001901c070f18080e8076403550b00c1c07802c02007a8055600044c50b1904640044e000c001440c2e5600d8103480e044401300101d810301d000e2403140304a40884607080b240d14101d0b45802c02c00d039400c5035001304099030304c500c0d000801462000310030015101c0e60300030304c01040c5062600b800f0843c407402e00d0325882000d07858160440b51341c80d03d40e0012039000400320041c862001040005000c0807400100300c0700040000c1d54803a000640121440d80174030082080c43d030792204000d1781a10b200704042d035a0b243d0010705070f603100310312850b010784004041600b100d9a8020101e00282b410301503081d0220610040e1070340e010100800d042100254407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 957169388 1250 957168138 957168167
    0x80d05070e2b0c0806070f09031e021206040b09010608070503151e09010209010f0806090f0a0e03130807051c0b060a08011503020102070f03020d060504061d160b0712 73
    0x10000703140700480d440103d03240041440d00044c10003420040002000624914103440c1448a41c0100304009840d62008000000c094040f16414200c0d134400146031050b080b03c120024815402440180b0418080880c0162840e030001c102c0b0300d40c1da0700208d40301e552030700c10715505400000c83c4110301041300c0001507020076030b542c03c8030f880c51110008030a009825200e54910340e50204070003482d960030005041071842c0504061005250020008070b050b40001c116034034440340180840c040001d40e0700503040c4503c806080c0c0741ca40e941e8081507400e0f8201442850003c1c8162000007980742131044510615401d010322038644500c0c00e4440c1040303054060611604030004440c006290380084c417504082e00c2c0707116850310701c440c610300009140c040c47d9003040c00c0c1c14170003100402c0140e5a5940300c0b640e803a4003100224465813a820302c20014444051841c40c00101c2040200352044049914820380912040842c1e0b0141c48100031019401803c1004051811007142410018000c040395200300c04c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 957170638 1250 957169388 957169459
    0x20604170c060705190518130e0d05030a060f0803030403051305061207090501020111070f0804051f02010e0a080d15030611280816030204030f080d05070e 68
    0x15140d0890501d4640101e900e40d00240340030601c0741c421740210303440c586003101c28540b40f0700780042d03040d00280340783c2c135801c8180c8541c001c40010408000950441e0344a07098100a0f146d2038041500050041e500844100295500d0149d000c00c0c088844075000d010368400030300440c110ba40c4e030341e03058074a684440090021402c1103400000c055559100426094100d0217400d4210300b049030000c4d10b030394480d4000d6415641048042c142d2071100380e06a40a607078000520030300f20390300390034510050320958121941044078141c029aa2040c002c9010501c040e4541c000c02c012050f1000c0680c5401210b140201454410082c1d076540e0007040d08030301004426050380c2c142d0550740e5070b100404ca898040c1301c0c0c00c1921020403403d071040201300305406030348000140a90120340d00400100204401041816446403d45980030200e20a0341030b1005503600446009501c121400c00749404e800c5001e080044600301000502e00901c40c07168260440d5002e0301592190010720100007401e007594070481c1218 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 957171888 1250 957170638 957170647
    0x18161107050901090b01021e0606240c01060614130b03060619020105061c0b01030314040305120301140415060e0d0c09091221020a110f15090d02060417 67
    0xa41d510b14072980288150a40020034991100000e4104010310345180c6070304030003941200700d4072800b00d10507a0000341100e40620260400880d01ca500c0509580000c010f0400b058104a11005510000c2a51020b13185c0c0360343d40400007124100c901ca1903c0240c1e00015180b41086200300c840003854005400030005800d20301070500a00c0e001d40f030740d4441070040c2c1d10765061040b5420034005400c040c85c0c030035130302c84a0240c1949442540c000103202c003e0411040320320f5806c000301500c0a0310095076000040c0d52482c0b20b01d0494170f0054000380581340c0301240c040e03080368462401c2d200300f6807040403001c1120074485c0350400640d5100b24800d00503410110070401d400018922749030780b0000e811200c000090290040c1490300c51685851941024000300b445080220501142490a0f090b040100580d44403a00305017110380c0a0b0704035010b0440c1c8a00b03004510740c900041460a1000d118400032180780c1d035840318180d681c0904200107000358000c100030601107130102d07040c455090030f052400c9140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 957173138 1250 957171888 957171899
    0x3070201030c140304060614030304062001060f0801020a2c1e0d0b0108060a0905100903050f28050a0c060b06090612071710060c0606080106120218161107 68
    0x407540704585c125541c59a0b40d105002c4c5070360301c4c400200c8040c0d09a00031400d140c10f005002e020182c0004e000c01c4100c000c04a86a1850400d40045025000303e211607803615a561a03500d0203504003980c0c0c2c40101d140951480b00e0712150555040b920481c00c20b200c0141c0440c081031140d41c0b0ba084107402100c1032681000121615403071310030500c05108006a28440d03241041c0f031030801c00098100e11400e13060140e0348000c60000103076122442109440015850300a24040c0c610f4821040c41d090800000700e00b0070407800c0f03921203200c0a031652408174500c460102c101120107105503000c40000c203610320000c001003072281d403000fa220030b0082d02251070000c1c01d80000743c0300c1c2c100454882504040808001c0510b902902060003038606480d091501c1c20508014107181041c0d000d42c1040007180c03402001804020340220f002000d540d4020042c03203413110040ca400c0100c4101c141d0050b08120315003104010034007200b9100d04580c00c8504100d40094204940d0144004054021485400e402040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 957174388 1250 957173138 957173177
    0x402040c030e06090d1206050a3c0914040c0603110f040906050316080307030804020117010e1005090114100c05010212010f05120c04020c010f05130303051803070201030c 75
    0x40d114800003005c1c1516412401000304404c22105030580303050050411440d150740003408150380094940718110520382460241d82c943c0c0024900f0300160400c10098038109050a020a5490701c0344203010300c400e07040b501010104150f4006044c415200c1d82042014401d40c05501c04803018090a803a1540883c103060490f08590420409155180710030016442c041010804000400714110950b6140504503078a81c000c0396409403d021207540000d04581c841d01038440d44548840444100e541c5038241c00c41c28040c2190311482c005140100490310345440c0d9181030407078924200d100d031120903c000b03200c0040c080c4840807017072120305170880001500a001514152026144003080c030f624001c0c103c40c0c403170000c0d4021401103000c1001c14100082c046a000a07040c01a42c001d80d680c054090000c2c01801c40029990740c451516042c4800c0d41d00640d00694410f000b5a030034003076a150720311803215042c090004070005500401c40c01d00154001d400c04400c0d94120300300f20428450702c101901c2c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 957175638 1250 957174388 957174391
    0x1b0601030b150316050105031b03040506040302071d062b1202060a0911040c11070306050f090312040b0702030409060905091507091e0317250206030402040c030e06 72
    0x1d901020702010440c51a0001d0080084402d003140142941c54140f0000c0b04099458015a8100100000055100c05102031f81e0000c8940810f8a169030345054103000303448045c20f940450042c0540d800000d480e281442020440f070710000b4610107161903a0003000001d034540c3c441034807840303071640c0e00c0100c420f02ca58039020158040e4480c1180c01c0914100203050800040c141744e07040d850b04003c0c10100b44d041c2d4154140ca8015640090b0030b002e840429510b8041219800b0340e2881107038004000c10140d904000c0c020000d01000c21841d8840e01866910303030040d44210746880680d100000c0100360f00d00201c98100030b0307500580745096280d91601081d100c5a40000d0700c07407034031041840000d8108200602c1d024038450024000c0b410008401042c4840c3c511690300d1a00344000c041d0340c50300315004d91000860307216200c030030915130701c815010b103940000100030a0017851551a401030010070881c030a06d21350091009285540355400c200050110300c10307580402d5524048610b09503000c200c681e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 957176888 1250 957175638 957175643
    0xf041d06090d0e09190b0a0b0c070e06060c1906020f12090c01111906020f0c0c12060f0a0e100635060a09020616060b0406051e061b060103 61
    0xc0100c0828030b40c0c003030b04200349075907114010301d06030301041131140d10b135450a0904004000d020814282010002d150144581c1220941200000d440f90503070b803001030900e040340d00c551010b06460b500da5080007094007468041e401d0540200e4041c0d0300c000c01480b84c585915108202c0103003891901e8400540c90b400c005250b01c0d60068010500c15540c80030000001108000d2078412300c850300c180c40341da403076012600c4291011f07842204810700b0403010b6010341b9140080140a40d03110100d5050300342d0340d0a82c090b0b846020b60303220091606000c401185070b83c03280e0701c0d4194070303d81d41e2150030745500101400c10100d07031a40513080d92031445840070300504d030041004554543e14003184806264480c002c4041d43e2490301a041e4400806440100f41075a200f031903040000b0300a880360010515610480209012600d9540c2d62001003015940c4460160b4400356010041d4580310070600a1081a600301000010b500f9480000d19141010080420020010004241140c2d2904407483c1803c280c00c00c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 957178138 1250 957176888 957176893
    0x40b07050c040f0b0d0b0705041d1f03081e07080c2d06011203020109081210120302150a1104080a0b0703090206070b220323090f041d0609 61
    0x411942c940750151200484450340b04115000d1188002501070b02076510013001c083d40c220000d0080c0780158195801060114009411120000c00c403000140085849580d0b030315100390074048501b80030841a041da41d0010007a45024a0f240e10254141c4a00c00d40c904681410040b100003e482c4901800c03520160f00000c1c010480d2990b40030f40302031117405100c480c24503042030704a5840d0000641c541101d02900e041e010144240c20300300e0161410620161080e5000941141c008803064003852186154100b0480210b032910380c40b0701420610000980160302c180c000c010a1542455140d800240c0c0000c005404202c030b02d5030100c9500940d0001d401d07a045403d50006014840e07000a5104031984dc1c200241d804c15400143c590007189000303080010640006071440c0040720200001d9040008900000141460000c3c920300d00c071000072801040c80c82c0c14a04414041d0251050ba01000b052403c0c001004402d000041002d981d60690b0311803800c081c544010302c103005103401408203402 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 957179388 1250 957178138 957178153
    0x70e280b0112022d0f27010c030518011e0e0a0803250809043305010516080d02070303060f060f0806100c02030607030f0b030307050d030908040b0705 66
    0xb4110200c034201955800c0c0c010421100001e01e000400b42c540b8500e4040f0610885160440c10350500807550318001000c400900440301d40358441140c129030198400c200040d60b02d4400460f0750074411140200172603400d00036402d500e04410822601507006141040c408548142020489842440d0502c003090300d894140903182000b40356000074200c1c1e280214030703244819000d0121048121440c603004801010600100480b01c01100c6905600410510031030a00031005440d92001442c800d60480d1802e005241010041d4403640440750305071205424540b0300d00c0100d101c0c1e0200c000454a4000401545468846610181080601950300060b40302e05002c6021031109903900304105000c13849652909059122460641c00320b8140c4031141403c1d20141c05840d00b0505d80d20095050080d04100001340c0c2c0e155000440ea103c03c58030a0002420540c1130649a1041d124090702079081140c040c0b0415019812149100b8403540400380340235943c40c0d503030b602e6401031801219150040c20 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 957180638 1250 957179388 957179411
    0xb090406091a041424011203051e09120c0906190801020c030307030b03070e130f0204140709170a062d02040806060a21020f04020c0c1011070e28 64
    0x4070505c2d505041c00104807013a1704600346151450014443e8034058100c0184203020140b10300203464030b1112a00007040340850500c0104500d802a40201d0f008051000c0c80e80002c0318000b030081c40094024003071b45002d882c0c82c0280203035075405500d00441d83d54105800151344209200901403000000301a64807420075800080968100325581803007a0300c06d442c18420101813840c815003282112000301034a189918127080308a0240c10084e500c281fa02090004182400a01038402c09480d9140d089031a2100c0c0341c07031700d030044101519213a40d0288041c1c0780003460550002101100603802000d0040b0f04400c4010f8418045800100c803d030003050070070511000f0040c80781c02000031201d001042d41001c0c8140d41e2400400c80d1075070722107070620342070703042d0344980724908841d0001400c00e565804907080c0d8203503241c1e1060440b90040070100450402c0358861a08100c02c0403e10700641280f500d400c01034a1807040c05000c06014030300301d14032061000075410040c0b9000300405804540003580c0c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 957181888 1250 957180638 957180643
    0x1801050906090405060c1305181017071a160821070c15140106092103050307260a0509300703030902040f0b03100b090406091a0414 58
    0x191007280195106024070002400102d00b01c0e41c031008508289131140b05021803a4032101d903960025070400c100c403001c03040036035003070060070700c600c0000309521403142e0b40e600585c4a010441a90702c569411580c0180050302e40180321413502180343c1480d6007048000d215821588941241c1100d0740540000c0c804207085502801d481002d14039042d41086290140001e810070440240041060980780d660844014a940c081e0900380320f003d45d401c44640c0c41d400040d0100303503240114000c04100c10300a1110350388101c80c045070f444c7c2c9582c4030b1b410b54455040a6a9506621006803000c901d00300030b46550240b5140c1c003170700c80d2000c2d102c08110750504007d8541407a11400002c020000785251800b1203440441d0340b080c0d81e51110390400c1d502d10203800d08400400c480003000350b10034107201201c0a030780419007214403042c4040302582d00511416920904035100700c03040607007000c0e000000401150b22507206160840c0a00d00c8254400c41c048184141004121001c071880c03200d00e00d80f0032804070f08 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 957183138 1250 957181888 957181891
    0x2151b0a122a0f12020310170708120c0319030c110606100513030602030a0b0117060d081b0601090b030c1801051c12090603060b2a07120605071202180d020f18010509 73
    0x503500502000c60421070615200ea0007908400000c2000003123281200504008035201c0c8240400c01102280d45250014050403111410c44001086d41e01d0844403104003140050042000406410b942c02d401c50040c0c031140c1004e03a8006042030745840020120784140003e604c2b0315a5a14001407210a080001d412030144003141d0006606c46800c110580e2201b1401080044c0c10031042500c0c0d00104041c2c180c4a607007800326041c0c6000310800025a99600c1c2c100c151100d0048080c3c8070040c00e140d0a104040030f4514801d01d050001c0070040241c0e0409003400900200c0f402103c2072006c0581e00d9800c00b080007485100005141951b082108603070610a050251418185051400200a0200d50f000c00c81f07801c00e45100804076101001500304000e0400201071034102c41030464950704003900204030885d0f040011455050b10061019064422541c0e180d08007504001100381c05403d00000040b03000701280c01c08404410f8905942c1e41c0c1c80091443c8004a80203481907042805124103840d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 957184388 1250 957183138 957183179
    0xc1e01060e042a0e0f0402041b020c040e0c0a0612020d1107120203030105030a0b1f0b1206041e0b0f0603270d02151b0a122a0f12020310 60
    0x1440307402d204d0040c1000c01c4a4201c003006104130b00355103030342c00018010b101111500b0403c40320790031044541d940104034a000840222010094400801c684545400711040700301d500000c8428203005950080603070f03507580c89003103000500305981c00981c1e000b00c94443d034884030040404203140042221001443c00d65010398405141994075100210b541c6aa10080051094902100145074004420360466041c490701000103c017503941d0340802d401e40e20580410400719940030010b40c4500f098056108001e0070131808400d41300e81d2442c0800200401d2107010b0740851103541034841c0e0754520f005180240c0b289640d003504480021841310300e10401c4100ea2620390441c41007500f0382d135000b007a91000c81c20b0b01001401e0a0b035412030860002505c00842e5013203100003003030086189a105100703040f441140c0038200100e511941c40c1115403109400e80e04400c441200c4020320745881240e401c406007549060810b580c048a42041080e03800403205800e0f82800c00000b000650300d4582c0d001414078 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 957185638 1250 957184388 957184463
    0x702030d02070e27010609090213050907091a09070f020c0d0b22050f06010e07020609100c050d0216060b190303050a1b030e150c1e01060e04 62
    0x1460300c040310300304280080410910101c0303445500141c240070f403031801d04c0da8241c0008002c202d4440390300c14001c2c0b46182c0180e001b100c0f488409050300005105040c001d008841c01049940c1c138003011000505806403e5083d90940031034500c015490b2000303600d0003107120391107081e040944802b00901c5c02c03002c0092184640343c80030400f0003107407003030724041d4108410b0030201c80c0f10364421044812010303420300018007501c40e8200c412220724000c43d105041e96110080d122035510359020890341d500c3d050715840d10705d0304500c45041c809010341d400b00f04c1c0c0d03407000e042c890b08045075903000c8000c81c2c12052324440c400d85048518410401103116080c0c6420007190701022410b0070b601d942c13551040600005042c000d000640d00c0480c0c0c010b00405110450b11880d600008010340780081050795406081e9003d403a600a00d403420420040c1500c02c058107401c000c011071641300c96810011851403800708100e55032083c020403071086142e01544110b00450352804074150031110f240510000d01000c4213070702c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 957186888 1250 957185638 957185653
    0x1c09022719060e01090905070308070c08100b061803120c0106080601060302030709171006090f0509060c091e100512060102070f060c03140a0201060509090c010c140a06020d020702030d02 82
    0xf043c03440500341950860368000900c2203040c5011803901c0480e4102a140e40804600c00d41000368030400b010582d1000c01c1520013006000c5000f074161846254501c2d030000c001d0040e02c100084503900c890f4207903001000c9581410689040c4491a40f05415a8842d42d45519003840702040404c0560b004140724a003c6140d8904980700900c0149940652a851080244402d4025104100c0d940e0789c103c10300c4041240c80da80d500c25400419202801509003401c043c0050105000445c0d80340c0b292081c40019454201c000c0200104e42072200e01c1d5440d001c0d140c400760361480c1c95500010000307582503290f2661303820704807945854141005142074119488076105100f028940700f1014200c41090501c01c201d002c3c20720703050358040300c3e44080c2c180050000c1400a19141e0541080040781c0c02607850004a8484042e21610340306440d14544c00702d600000c1c8000000c01000c802135403c0907003401d444103c80030f65504002d84e805460f140513800c0d00807403940d0075440c0601208118568a00081428 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 957188138 1250 957186888 957186899
    0xd02220f0b1b032107170112020a080a05160e0601120c0509120313060305060d020126010e1006020a050d0e030106050301110a0e03031c0902271906 65
    0x101091400340071107100c070109001940a0704241502d01c00b03200101920740310703072001d004108600c0d09210825180b1012801040c10b1900a070959455400e000410a000340e00340745038980d15001c0c1c0d2604903004400f42c5030000360500706000403100c40317101e4000350019540d00c921452010026403c43c041680d28503040c002c5581c0c00c50321505144041c031201240c1800584000c0e1a28042c50b110740e50000d80402c500d0460200100043c0754258082d10f250350340c0350b1034030700885c1200e000f1140c1a17000311040c03c802e00551300030801000e2280303e44140540600009042d110360300400c1e40200b4241c80542c05000a100442c9090380260040f480240721241044e02c0312956160202c6100b0180300e416030f81d0b0615510290081005424064002d0181c0c0c48282c2c02c100140d4003145001000902d110784407401442c020040b100c048030151102014020030105200c002e01e8068400c0343d202400121941a0038520380a0a01d1405202080300403481d0040140e0084566080b8108032545010001c1c0007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 957189388 1250 957188138 957188159
    0x301141b041508130f120305070903050304030f05070f0e0a05070e09061203090a03050c030f19060203060d0b0f340c0c0e091f06030b0118060b0d0222 66
    0x2c009120701c0c0c240060b48503143e854941e408407410207810114103901c4282400f00ca20640c2d50081c18558042000f0b0f616080101c481c4146400001d206030001c12007040880d50b80080560614050802c2e600c00d1b55594803821464a6541c3c0051a428070792020018840824801c00b07a004034581040d00000c1c0d101c02c000f40704850f00500e1103105d003090503211042044100240c8201c40030140c002c1084c0c40d20b07828180e9540d20643c5145209100d03420072000d503214080b454808103982007004031040801c03652402c01030b42006000036080300d40441c102021030451183e060241d81c01c5c6243c800541080901c4000c00d040d25040c04e15811318000481213414914403d000e440e050310300c0c22140134540e600c0c2401154800f540300c00103c0303504c6005c1c03050300d0070080343e251981d05240c001c90018070740ca4075441303081d1000c0e44406807011142c24010882e43c458200400300c64200c002c000119036407250441c0c2126081804401c1d0100e602151b640140c00c02140f49030034180321400f0300008a4548101000c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 957190638 1250 957189388 957189419
    0xc0521070902040b0d0e0109080d090204060b0f12130204060603060e0a0e1e0102070c03120f03110912010213060906120b03030702060f131d070513150c020301141b04 73
    0x2c007295032681032807840ba10032361251071000d81c44460a035850705007100c0c0780060030030441c0aa100e14a0600009084000c210442c2d5a0031188814a410074080c4100c004180034002c06881001050b09034210041c0c0c4c1d00d200345800303070059850010b100d41c00c0c140032030701901000741804403079481c0c20a400b221020002e00e00c10982d400220701482650000da81d0750180c000c06000a00412012002104104804a80315191100e560720003599680c046002c030143c0701094072500800608001f14021800c00000390010207010100151910781c2006850300c1c60025a80510000303000418140580c42e404480c0c65565001c125050048a103401c000a4582c420400000d00c03400c0c3c00a90b40c2000303200001600c1c80041d244950014491b03403071700d00d06540388490403110202c40c00c03080081c90b100c1c000c2c000c0e00e02040f0301c0c03c005034410341805d00e03c1007015070707550b100401e000382901e200c00140c0d001d005040d5083d515860b05030240c204080422221106a00300340340c494006e01081c4540d240c200c0c1c580c0d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 957191888 1250 957190638 957190657
    0x306050f130605100308130518040b04110a05210c01020a0803010509060d0206030a0b180915090102041e050406050609010206070e06040911180301180303090c0521070902040b 77
    0x7641392241c24010756018219440200803c5020030381d404038800d02100d001c06c07a82c017500c8100c84510981c0d40703050340c80e10859004255000f6000454046401d000071811504006051064003d0b01c80b00007520240c5a040c1265001020082180c404a418081001018801e00003401e02c6116959491450301050140742e001d40100000520f83e90340f40a50340e00c500f50082e0409a813030908080220103050146083d90061003000b200740e04060134901958403034055600a403807000050301060005140103440002c141d9020300000c210780c400e5004001e2402200302e15800b142c0d1800d4140000c0e110b1541c071040c8204801c8c058081c49076004202d1a03808039062419081200b007500008003d4000c1ea0040c440c1240b0b400d51050141034481c0040240d246100348500c03038101c0031350406080e83e82c0c0f0706091413242c112541402c000b034000d800c5280900e2003000b1901c2803940340c0000c2500941a5014602040410b4207800280c41c2c0070710400b00035040b520415031505040c10904d101522401b50701 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 957193138 1250 957191888 957191891
    0x12031512080c0c12030a17011401030b030a0203070f06090801020414100207090f06241425050a020109080d05090f0301241707030b04080309120a090306050f1306 71
    0x285a0640203103e5480c06030b400030a000c0310700e0b21402d007160380c0c2e800013070320340010500c0c02c1300380e40f0b80342d4040c40e03100c1c125034404824081c0c020340c8100440107407504801241c0c25128207104a00140e138188250000350404a604416803450654003d08c06a55a840121641d204210034009451400103c6d86101c206070707003e80d03114440410403460f009090707005c100040d203400c0d403003c03140199800080880f0440c040381900c824029024441c44809610040c0200b010306200d0b400405640d4041c0030300c01c80b054031803e80c00107150114403101840e000c0031601354000b0888803046680205403100a4281c580043c10b402494a1028003240b01d62499681300701c0c44c0d058091020355003500950701d00030303400888401900c5540300d141007840c3c05001d086800b03000d01943c4008248005120701c102d9802000e02e0007030340c903583c5620a89038009028410b00f4010320900d91407421941f801042082046d549100740c0c60301e182480d0044400c043e00401d00c2040c5001440b20760f407207000d044a800f6400c100c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 957194244 1106 957193138 957193147
    0x503031503150a0c080a0c1211091809060915010308070204020705030a02010b01030b01030b090c07020303120118180305070308070203090310020c010c083903041203151208 76
    0x207e0000281e0310038100c11140c0300517000501140400564145480e40c5600458110b02402c076120108000c0c0c1800e201c1c11000c00c220703560b40031001501510300000111810b02a2a006100242048801140490a56685a040301e1003207520404480d80d8400c1000040d01070400f205d141400b09103010a044240d5011340110044018000c4c09258240c3d980301c80c4640c0e5230040300d001d0382c26120500085401c591f040c800c141c040c00341c0b06520030f45a0088103001c2e056507645261103a00c0320308481c2c0c003400690070005840ca0f03640e05060003d09651050f10132841c60103040740b0030341c4c18816031031000d0804400e40d000b00600c10031407000b4800034503681000d4409107400c0d9456689200c54240322030b04031078a442d1101c140482000340000051010b0710500d10341d08142c0d0b00380c0e0207078011680e42039030304d405100e403c0e8014546402d80c6021441c028841d81402c0100c440549005030004 = true := by decide +kernel

theorem cover : BRFrame.Cov 957014388 957194244 := by
  have h0 := BRFrame.cov_init 957014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 957014388 ≤ n) (h2 : n < 957194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
