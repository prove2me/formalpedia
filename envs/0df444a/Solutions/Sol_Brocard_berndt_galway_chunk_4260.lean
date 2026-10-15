-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4260
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:02:34.728016+00:00
-- url     : https://prove2.me/submissions/6ae0b295-9110-4503-a14d-eb42d0892a25

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 766007194 ≤ n < 766187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 766008444 1250 766007194 766007197
    0x1b09010c021002010b03010c05030c070b25020d1b12081b04060f170c040e04050721150509100f0e06010b0c07090903020a0816050a050102190305100b0f0f 68
    0x160b81005135125501000d207818240999124001641405801c0d89015030b040f901c7d60041500c0a40010301da40045031441c01003071951500923102c0385404600d032101d0074010796500c2032403030240c0000703426801d0030b0740013225180d41c030b00019484001d043d851052094100c854581c0034115420124010b05004440800b410040c4010540d5071511207a840250101a08620300c480e0100300c641805000c0280010855044409440c1c1d52201d8401c1740c0c8840c1005482d000c40c039040055840e04000d41800b81c000c0042111034801c1c41581c4221940c51465402016540c0c1950030b845180d01c004d8810101c0040c0303803c00103680303100b01c00c00184101e8041d407003803501d0790aa1010740030140005803003008120a100300000380c11511020b0100300460340c0c00030341c0d84511030000f400f80c0401203a005601c0200e09444984a03170000f04071a001822414480d0003580301e207c0840300c0300502410b50507154005d0003803500c101e1014542c6580246032074200c403402e5100a052280d10602005600c280380301210 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 766009694 1250 766008444 766008469
    0xa0305010b0109060e240f040e160c020a05061605030d09170705030a0305150907020105071d0d120201020910122919151707081b09010c02 61
    0x4001103080400c800016150f001190011002c1205d450710001654844160420303607003000c00b00000802d841c0603196503007406480b4100216040c001400200d4200c804806406400d44060003c058108411709075210201184020b4100307040f01820403083c83c02c940a01040500c07600c0c3c0ac032052030650f840f0350550b0311a2444080c01551000c042d0248001025001500329034144524030b044c1e51916482e9a80c040c2101190403d500d5800054041050a050001800024000c5852405c1400d000ba000c1e00c0111202c0c80002d038421222400200508000c80c802100070300222a017450b00c3d111640c060305080b401c0419507400300030b01e080a0300c03031915603031801e0403c0e62141c4060761840c40a070705132141c517422007419008042038201c03030080d0030001c0001044100d445545005d03441190180008050b4015426241422010825036030400d03240c075400030940d00a106203540344101a07441043c1910180c02030207000000d8100d080c006002440c0503c0d05040400110551758000b90900f4013a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 766010944 1250 766009694 766009703
    0x51c1a0613140f0a050103030203030114040605040203010b03040311060c0a050d2a08070207050f0103020a020a020616062f0a020109050616030e0c0f130603020d0c03171c090503090a03 81
    0xa08005061a10802e02c5404c1003041c6002d00081d499620020741d6800103010700c2000448810b4808501d030381daa406074000b0300d8040e00540d00c0e580e466030f1a240c6c2c3d4008842c250040340401c2d070b00d60f0049030f010402a206141c9408541d0505001c1201141c040e00211000b05905e940c95841c0003910220013564056420070590607041030a021100500f40c0700007601d10415540050004d00c47d5a41d0003481d1511580300386001a00d82c0fa00d507104a01d420b0040d000a504040c000864108080d4203c01070307003009000300c2c0d050080c4100950407101006101000c450700304540820b480e10140d003c0024488107109100120748c550b410b0b151642003641c2500c103400a441403200144106806009145c0b810144102501c43e411640004c01c4800844000d039030301c911642401c0c1d0b1846180e40e8042409190040c000410214040c0703800300425134540025640242d9541c80c00f00d81900d401c085990942d00020b050441010407006040508510348003141c4601007800101c80d04d0700c400303076044000c6014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 766012194 1250 766010944 766010981
    0x603050109060e0f24070c062c060c070f020d06050c090a23040c050c191103070f12021314010f0501090f0b09030a020303040e01051c1a0613 62
    0x4880810f0304d0180c4004a401c01c64001134a103080c03000740000c0700c0485c2d450300d140c5281d442d61081c000b10760b0b44210340c000801003407400304241176a140e00200408041d005a01c4120107000f5085900c1d0f544408880010654500b0002d42c0002004855504441840a84000380740c03d0310b03a40314016a80c040f0f40c8100d08080c041a0000146402240100185102c41c00c24000240703144012078040f8100300218000c940740d1090800d1a40704004880c0c0120104064666040c2504400c94400e0001c1342c0c15100185010414001071601250103030464a0080302d411605191203510b842ea5038041400340d902403541140c102221249024000b2600d400541010f419810034450800b40e190a400060401c04580424011216400d5a040c00c2d10607000341d07140c40c3c658030300c0000c4c03800383c164200039014040481c000503d86800c081240c10b0310011550a96800b014608c10441180300c110050081e2a03142400d0307000c007007007201d0785030030540242018802483e4054000e01303035076645060b100d41e65030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 766013444 1250 766012194 766012211
    0x711090f040203030901080919030c0507091506030903020a1a0a0606080621012316052505101508011a01091502032109190b19060305010906 62
    0x184241000d40c401440c00d003400d86428190042030740da004121009041c02039450105040d11001c10a980411000000303c484100c080c4c50000d04030880342d80111102d2180c3e40002c150700d08540100d101c030628600c5400811842c01c0c104901815044400303030254060b02c0005004520491100c00060710000e80c00e0600d42400d1011600301c5000b40c4c000002c00c40340b5003d11039503079a00401c140710041003000f06075100342c0c40e0720750078018210032040340e42c640240d00c141015004e00d100c1080c4544103840c4030000c1030380c428609562a1013000200c81c81050140d88580e4002c5c00300004401ca40e014000703d400940101d0340c480100c0311186007008030b002e440307001080000c200340103c0c5103444a85c0c0503041401400790001e07000e4041c50084031010f10341b004112494030700c00c1080c4c42c40c001c00060030041007441e0b09010080702070191503404182c020140c600340c1078092503044928040c1e0110725500d031640e4502a00340000e06860f000416a42c5580000021550034002c8007080380c0180000030f000351 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 766014694 1250 766013444 766013449
    0x3032306010f0e0102060c0d0b0d1103190b011211130b041503080d020c0f060705130501080403080a0507090f030602040e06090c2b0f0c080108010204290f0711 70
    0x20b2641078200c02c102c000c80040c9800c1c2d0740800c42c10f8100945a0145449140b47c42145000d440c100104030b030000216003102090140490704150010015420f454803442524a08a003844c1c41c0c01010300703101078003401000181198012030301c0d064040d2800d01c0c44c0d00000740025148504801c00e0100e1141c8800c1140241d1074103203e01c00c984003000400c640300600d0341d07840032403038010804070403102039000c2110101045e051004688207d10002036601c646440c24000c3e0203a004041c100d00c25076114440400d50303501030b80002c3d00440d01600c583c0c1c51035070740e04000006800000c4c46c1c1b6041021382e01000a520604210710300107140300d01005a01d503410700c0380c5041c3c4090000e00240c4180b54040900826a041200300e4500400c04500f044011803010034010040d41148814a001c1d031074800e80c5800c1c1042303a444181c540c003150340d40702002d99170b03044180d0a1740250700442d00742c440c403840700c060f048251100d81e5200b21507840005060491901d8203118a03001064148c444043c4030749068041c0c1b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 766015944 1250 766014694 766014707
    0x3010e0604050f07060c021207150302040e330102071203020601080f0a15050406060b1c053303150403080702210a0815130f15031e0303230601 63
    0x50b000f403001410080d1070714038001c00c00c02c18071030080e025040c81440b1003403005052010102404880c800c102d0000d21400b0300a000b540944180b0003403400c9180072034824006003660b203941101360540c400e04601001e20b0f4148600c41c020034181948540103000a50740c031508051403415000740c001d060760750303d0120b501e8101508035035020226004800c118000501c0d80c0f0840ea0202960f21001030140e65519280c0006c01154001c0b985884c0c000c5110843d41f0103001c0c0300c9500c99000007041c001c81e1500c0000c0c070010741e01540b04140d03854860000b507c41e25017900c24000c005000070b080f1080c02401115000f0000c005031400d6001400e11000c01c00d03a20b404200701d41c003030758004414249540d01d8058162060090f5113152041003104804144502e554000701745901c01c00806800000d6016030710a0018103a44146040740343c00e0243c0000300728042c4400b0004c4030703005000c0c585003031040070300d01c01e1090781114201d0516507180c04041060001c441c0a1900800388510302400c2c2c14108000341c01d4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 766017194 1250 766015944 766015963
    0xe07050d1d031204050705091303020c090114060c010216031e02030a0203041403160905090c12120a11061003170c0723060c0102040603110304050a031d03010e060405 73
    0x7505040490300c5458001007212050300142d001101d80380ca4a00d4214100103003684105c0c0e11400c420107000b85082c07502c20074040030344170b81c0072908410408401e0101d450000d01c901e880d40c0703491102420040c02e20400900140806c0c100041c41d100c0e1020b0041008240d0980c00d800050101d00801600d01800d100414051385500003541001c000d44030080d92489a809084030110701c0c2400b9100c1902d0420008400301d031000d161180c0591550780303000003000d00302c41c210312520400b2607035080d42c10074640d0183c0180101010f400c03c2c1d080c0001e04011603214050940c10045405034104c000030782404441e0080512040c2416a1403840c00e1624104900b01c42c0c20044080330040078041c240c0005400e03040340c41c0002840400005045000702a0308126440d40c0c21040014244e03601c0b5106600a009603146620200058004480c0d1003240e030004450040640d4442440b0601190084800603402d07140740480d0300c1c0040011010a0a48501d480741c0003142d80820240001c204081c04590360 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 766018444 1250 766017194 766017221
    0x131206050c07050c01030b27190e07051c0c0b030604110a0e040518010c08060a0801020906040902030a02070f11010206070f0c260424020c0d06020c070e07050d 70
    0x400b0940d440701500d810019400e00d05056840d801804a078580104101604020f1000ea0a0200540151000b103000c104c4509540035400050701c6204081c40c402e140420320190000c140701420301d41442800c00030303050300d1085c8410001100000881c0c0801d9800a0440000450b85a040c260180025100e85030100c107118442800312800d4154051406402e020040320080b82ca80c85000e46402c0380440304450740501d509015111241b00e0300f04070618040c0c0015a000f08406640e071109a00300d00411762130a0340000100000c20064441e074000c0e40d08100507440062900b047c640e9800c03883c2d0a0400100d508007003480c0c48460715078050002c5503000d40d036410603d0100d0000c200092030100f590b100100a189007100d401500e41c1c25604122154042521403591961205980c00b14407040409040801030304035030544060344003281030fa02009002c0c1081810b00d056a40c1c0c00d02940219042000b035208135007000641411218141c1e01078080c40e10f03481c1c0c8d100305c005a0601940c0c500d00f074105 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 766019694 1250 766018444 766018447
    0x2132402061e04081606110909010e0c0f03090c0301020703080a0b01031e2403061b0306061709190b0a0e0f07510809070911131206050c 60
    0x441440c03503a050690080e4044402656200c045d8072003541103e072964046c040618285201900c0b0301164000c0c0240b060813902041c0036030340c8030307129407103104111030115007a541405000102c00482010f184c00c040201c0036a880c1c450840003181c22600148815000070b0ac400c400d1003458415441680500f2200386800d100b40c54008007502c0360004694001e03000c0c1a40c0707060058001c040c1c1c0e44c00345015844001c1940c0d00541c3c1e4101a409040205198a40709d8044041292040c3c001d208440807a80310f038449180ca07440740e03100024418002000e0b000e0303e01400c0310741742c210030115100c0b00302248101c21503009800c00b02132100c2218425210f2681c2540a6140c019a20800003049000c66490320141c2d00721400d07003040411004c000700728081032010070061202d1815105490000c1c444100072050440c8c1400039403c8803210800d030349104c0940c1101e02c1c10b000406c8160800400022403000345840c0c030401c5400d01212a0781c0d40d20071403903018011a8202080340901500360015085110103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 766020944 1250 766019694 766019731
    0x6030b0108060f0f01120e0a050d0c0c0608040f0204020c011d071a0901170702011b171306020c100e240a05091504030507030e0406080c040213240206 66
    0x43c070303035030080040203100c0c0c102c2619589540c1e1180da00503440d84034185092221950050b002503441000c3c1008a8941c0290200ca02c00a4480c0f02c1558a440d0400c5c20741503014a400750544900e900500155445014100c0000c05600d440c0018800c2910303070400011410840ca40240020084211080030ba0304580c0c4100614140142c446400c441d410fa8425a2641d1510040e580102c080c00c010050f50308060030807032602e030107501095030a614046006680c20742c0351002c85000302c41009800800b100b100201e004548020300d000840c0740f049c900103182034508045a480e05414044601207070fa196006928480340501420403840310030313440031079841c0b0100f04495178440001c0250207003170782e030f003000404c0c0410400443c40a2034600c02c00c019103003418140141640e000800030340129600300c1c0a000241003601c1904100d920001c043c1034400f01c0e180c05c00c00a94402e4101c1410340b0784011022075416540700209a60b4003074071060344510516000040d04002d00200107c040d1a41d82050 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 766022194 1250 766020944 766020949
    0x1a040b0711151504060315060f03080d0506040908031006090806090613050a0b0114011d0f040c030906180213060b16080c150105030106140d11010c080c060106030b010806 75
    0x11420b070489002c50407000c1d81d42c03c41c40391186080c148441d500c41e0030302c82c001091041c4000c40c542c880000010511041f41c64080040c4016410b1100501e01c050800841c81030310030941c420f030f030018001007001c01e05c69142d484403903258006403443d4100d986035032410014190881c07142e10081943d000504010b05c0c010807500d0300c50000410801ea4445070071600710400c4004d109541e00a940315201c041e00d56112030f014141d800ca107413a014003180407c560002c1c80901ca0014411000000f4411001003021005000251841a81080070316455403401c1000030a140203901041941100980c0d8141090040200703c61100c03104071800361034800706010341120300b0212164815000c4008808420714501100103104200304041c0d24000e909003032440034205c8041c0b60407140200d0007030150351388805c20116400d04000e601c0d6445042d2010210014031003520065480d14141440e4000e1016600c81c42c1c06944089119040e5030042001800466014440c2c05046202880d0060091034003801 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 766023444 1250 766022194 766022203
    0x6022503110105040f030309060f02031c0f0e031804151a13180b040635150405150a1404200a0f150f090e0a02071a040b0711 55
    0x10151040300d6201101d035069004104440040c030030840080f00c01da0f62401c0c020b107201003502030100061141f46810503000d20000035600c16020241d040007080c000415414001c0040442d075216140e2508000000c00e081800070b0b20109a007000d04450342c41059040100703e840302c1c40300003008002c04400388109412407609481e002c0e88450b1580e45c07281042030004007018140c1c015400c50407004007030980180d040d081032244900c2036400f481026212801510b405804c0a8100b0b2641500362042c03050341c1c440030340103e09900d41010754005420040b5100c0c1b5040c0e0490b819242c550141e030705020860a2644941e510070b61076141048450340c240f100181c003110180c009802d940f100382c916034410b2064020317264158030050985e41595a038215031042000284240103c00101e45051007007180589000365401e50341d0350780c8403c024105050303840c034003a010300100a92a401e000c6c4100090407500414651007841a4100640c0307070910b0441100500200100208945001d449901270310004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 766024694 1250 766023444 766023449
    0x110f130512060f07053604020a0f032c071a040b0d0c020f0613060e0601050d1b08030301060309331a091003210210050603031201030c060225 62
    0x443c1c1d450325190b01008480d6805400144948401109600564036454021059610111100020f900510b940400040f40249a007110110f41042000c5a4152080d84918207180b50000516072500b6140c40c0c250324400c01e50400d2602d43d108150074401d0311860180341002d0703040c505800b880c1c50708104c5941c4084c000e905104030500c0d103545524803554020300a0020b1138040c0c1088502505c0d10802e201c002428004c010380d17030a840c01003003510381c107130104a003410b0320310207040e81c184180b969445410700503410b400c00c2c1d40d075600c8110100300003000380021402009286d03130105450800c3d041030342d403000c82c801107482130305040c0522448000c000c1c8000320b034101c0b030420005564114000d11585040140c1d0100f5400503880040000b0020082e0482054034000c2c0902c60000300310070203140304580f54504070b00c0580e0008880466219075034000036030081d805001e490619410950024034100c1c207800c200d42d2000006001e00c2140d40c1000005211054020805018500e0781740c2082541c0c044d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 766025944 1250 766024694 766024711
    0x3091603080712030f09030207140a12030c08040e0c040f1d010611010e011407090609030b0f0a180501090201020105131a1e0709150e180a110f13051206 67
    0x32020f04140b501a6002c006049042c0600f03009107606841c000b91200c10501510414800c44500c100d07140c01d0416103402a10300314201528007948030384054908903201703a07088441d40c1c8100800710700c0000d880c0301c3e030380202030101c60701d904c0310308180b0021141c003910b40240d07902400d22280140800c0003172094604445440c200000d50248011006000d884545410f04256007803101c0000d030303005e080038628841e420b9981e034140039035210141290103468600c000340607903441201003501b030301c030180c1c80325000b9008003400650070312203140407100c00780c80c88410b9a0503595440f00c1350070343d40c0a0151681c0100b00c290f00d02e00d60003203a13030b4810541c8408424a48040034040c001000d00c0c45202c0d062840c240d18028200480c900305100a00c01e401601070b500d2550700c078040c18000c0c203010b100c20b0600c1e241d00070121466611030308940100d00400074108803040340c98107200d040b483c0d002d80040520041c414041c0f036279240144089810303200940d10190041402080442121401150303854016090 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 766027194 1250 766025944 766025963
    0x7090e07060c031d040e161e06050a0305091606080f091612140601030c030c090903210902060d06080618070e190510030605060301111818070203030916030807 70
    0x20313102040040504903602c000c903110b01d41d82c020030b2581c0800c204045552030552040c06210203481100c5941c414480c034404510148114880c140c040c0d0401540b041c006000c8030b06603484a0303441800c0800a51241f00801e9a075410300259002e400e8080c0c2c1c0c080400c100600c440315076001e04150b0b918051084c0c1d4482082c4441d88010001d407064000c00400d104001c40d0f4695840c0d0414a807001e426200840d0b0110000e000010034001600408081d190540c4402d4090300302c6032100407044000c206c101c99419903881e00c600050b6a10400b0f80207001d021032000030100d0910324050728028018008604401c1c82c40001c41d101d40380050b858068a9a0b0040800d00d52941d1003062512820030410985d064100030801100c0c0c188450460b00b141d0040509011030780b10401414200d0b085804107400807107040144041500d0000001c0c2070b03412000d46001d116020032031401c0542c00c0150b50b28001a0800010b00c284c1c024104041c08051310b8419074107003e2450b42c1d4440d0510f108110008014080 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 766028444 1250 766027194 766027247
    0x1a030705060d020c06010e0117070b250b010306020a030b0312070f0507080102030106120c05030f060f130f0506010e0a0e04060f060b07050c0103150e01170f07090e07060c03 76
    0xb800d8059070942500c08048a002d03503140e1840d032003651000d0064440017a56001703640c142460005442c402c503002d50410610f08491000500c208002c01d10b1360341340b003065050a80c000160300c1d140880c001c40c0298401070700c841e8010002401d80f4001003041784241e000710107940c048000d16044801056000781500141c1080345001c60500c14254025042ea51011000254040e044418040d84428141040009180e5403031709039034601041e80c2661006403107400090950900b00c00a0240490041110300d0402080ea44074041c0e416000000362125201c405101043d60090700318854a04200d60710b408035420b000c00c20040341401040036054545902c89450083c00075030045000d8143c014030a82c1d647c98605041c0e035100c42d11304000c1d0001c1e00d40001006101000075074841543c0c62015605100e91800e80100c108106550000405005d0410038000203207003004940024400c420000c0b1f10454070365402410300b000360744407405000803d0000000250712070002a41c0034006c40c41161070300c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 766029694 1250 766028444 766028467
    0xc04050a05130b10050c160e1b3f07080a05040c050d08130e0115030e07050405010f0f060c0201050a0c030c060c0210060b0a020c060313050d080108011a03070506 71
    0x2500f8409900302c2403200f81d90742c0349a480700c000c1914188607400c1b41c1d00c4c0401102e150341d44007030601c514086008840301040140304c40d580083c4580c006842d000742070407880c8801080d01e0000e0405010645441501c0d00034441220750034092050001c84445074515105101070007603a4010090240e20390703224002400c005100500001030000507200484295580c42c294280b94441c0510843c07002444400041c406031100d100703416500602d811042504000c4030541c0a41b00b0036203a1a4140100140460a034542c2e20940d4003c160603808200303040e20b800303480d010614060700300604000c1d00058842c0940d8000c000c440b908802464410710b90841801c00315100c00c0e50700001800141401254110a40c1c00035111001c003203104001c00c4900c1d645c00e4819800d1181c0320742003000d81c00600d000d040c2c5180003000703160b200107020308518003031545540340c1c0d017012104038880000c14003031001400850002d2245001c00703064030003030400380003045c4002640d9908501c50580702da03000049650904 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 766030944 1250 766029694 766029701
    0x40509070804140307030309050f06040203210c030307050909090c150a030b0306090309010906210216080d0c03050606120a0507020a050f0a0b070513090b0121060e0c04050a0513 78
    0x610143c042d41d459030401d00c0d00801519181c0001d070307154410600801246007012a4590140754007c00620712210300d601c1480c162980c407003c1d05e090308010b004900703010310144000c511405490b6a903650310080007042002658001d0701c070b1f0045902001d407030100c030b40380c00c598401c0c5280302c030302402c0d1503c0b2189800c40290480040d81a018029130303050208400000015058802098a829072020f40b944030440d18420703145824a03800342440200014005103030f00402000505d603001c4009401151580c0b9242c0c1e002041309404603a403030740210643c95262240c913400200032038134079140a0102085046006000d07114880c0d440d83c8034045800e55008101d0302445581c00410f40d641212805812034594420240030341d491442c01e0002074074544907000310f409002042e036000a03500c1c2044466401480b00c441c4081c10b00c100d10b0320045c60381e0108151034504546100001c1042ca0400707454180e100005005d1410052050005011554a16a4500a40d003043d10740703010f400304d03a00d0290040d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 766032194 1250 766030944 766030973
    0x106021f02040503012906090105030c070303060b120702160803121512070504110703022509020316030606030b01050403062012220b0f04031815030b06040509070804 73
    0x5602c6c1101c1d80f94110011615407040007071040181d1200940c001c280303d520320030240d9450000740100300003016060f403035000c0c01da100c1c000d01d0001031082d22111aa090380d404a00c07101a142054010010001c0c1c0c10040c030101100c0c0c9044070000c0d44c2c0381850b070715602d0141c1c4011600210b070110006121184505104030030502c005c4c9100e009203809500b05469140e28052640140d0502c412030f14070b0a034038012038407956032540c0240250268421800c020070b80d08003504603444076800300018042d250b0b00180d4010390752458025031406a00c28007900320340682d481107003814104084001039a800100f40c40880303410007400700f030820941071060840c0e4444280c20b40c103c000070030b00e07141c03514407190114429001003000f500503030764000a039560301c0c0107404000c2c4504554070000720101c509018680d0814400e040410440a115040c001707120140d410001c20107001c4900880000d074580100c820300b140c150f8041e40341034140004622241c0005015405000c400d90200d070802000c000d12040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 766033444 1250 766032194 766032199
    0x30c020f010c090618060c080c03041e051c150c0327051603080f0903010902091513051605072307050406091b110f0a0f050d080106021f020405 63
    0x340550401d4082c0c15112180039000006909901141ca1a0141d090650545015855003c547c50284c0d90f003850a90081001c0c104c00c2c0802d010015072140d140b00700074017400b15070800100b024103020601502c01c0310280003a48604000840f42c011aa00e649480d01e4034a982e40089018840c00e0000e9002d050003801745c50700303c044441280d00c840801e0302e41e002e50a02ca001603880c218480100d02100301014003020707000030000c100c0344010000c490b000700742d42900036001058024a0ba0009007214800300c5140c814800301812032465480c1c2918001032a40b01010100080d00f008814520450a905524418031100244410600c901e6020b9a95409150f03c0340381441c010510b01c868850030203116031800307181091404150066603000748000384680c85200900306901d078100702c0e1115202c0759909000e000b08281490050000d001d100d030482d00031b075813500e2400c060345089480c0908486d08841000089001840440d50110780a043c0c810751880d41521000c40e0000c50000780b08590006a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 766034694 1250 766033444 766033451
    0x50c1614010b031e0c220b010903020d0b040506070309080316090513020d06050a1508070504050d030203091912030f17130507090b0f06130306022b09080703030c020f01 74
    0x66441341c01301025440341c1346801c241c0314070315242c84c140b011a000707110100000081c2109039182180c0329901c43c03020018145025070b1200d6494000c6502c0500810701607402da00c20604000c00c2c0300082114a420a03541e00d400c2140700701581b12188a40001790032542040301071280c4c01c0c20140300b00480c90281500400c91210004410201c50096100c0000003500c50b09000b400500c629204c5403260071219246114200e60b00d00d00030032242004000c220304180502480b01213a540c8510250013101c52280d001141d65a8001d402c011070762544019045403078018a2007440000040011514600e174581802c504100c05548259012400304104865022440c01004240c02144940e22a4a4000c1080d210102c2d15420a20161600c51001c40c1c1c014443c0021018a4204000101402c2d4420564115940d0300c0340c0d180b10603648600003520210b010504400d8a041042d01c103942e11141640741002451541c1d6208003990140311805028981d031402c10801103070003880020b110030107020081 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 766035944 1250 766034694 766034713
    0x1b08010b1c0605090f090f03090a03111f0c021c24111303230615150c061009090b0601030c020a02040519060602150412050d090c0504050c1614010b03 66
    0x200400d41c021106c95820340b00e105048030030890040101c0d600d00b24050408980c0c5400d50b10b070b9110806440c0205034011030100750000301d03d02030720800009100e444d41c034004617040d42d00400c1050300d225002c9a08104441d848800010142c0e0358010410541381019659a8000030400c4014080750f041141d10f1100040c1007688c0344403841303100040c0d0303104409020100c2c10031882c0020401401003210007990090300800d25009400403014581d5000922450400701d016044100503000151800c40320750040050069821a58400d0005045100420040e030049525480a41d04020380001e06064ad64650740740168802d0040c00c134425000b901c10310060506051600000c1c001400ba04500da1070040041103051000c12202412103409100340500c0e00c9a442d502c51a104800f00c031010b2080810003280d28680ba8003919009501441c590b045407450041800181c0b9801000750021100800c0082480d0800c1d028210391160000141804014070098071401801418901c80d494420315041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 766037194 1250 766035944 766035961
    0x10f210c03150c030e0705040e07090e0105010509090f10020f04050409050606040e0102040317030601050c1009050c0a12030e03030f0d0b18010303120906020f030a1b08010b1c060509 80
    0x3595100c49002c0401c01254540712411811216a45104001900b20f61004c1005240940007041c4440082099074043c90780c030003030b4070200c41ca54135071001d050b515980104000c0c0b0340300030101c4d44444400080c0042c026080c81150b00da115122101c0c1026a000c18540700380040c01c403d407005002d0213082040108102e05020f03907507480480d1640e10071810050700c0b03003a140042c000d0341d0441e5804000d0510764280f000205400c1c0c0c02c0100030604200080c0b10300701640c2e108001c4003040d0b0703818110009003c05103091050811800c1c40406020b07020621b0b0801c50040302d060f508000d04c1d01441c219910607112400a400c0d4420360086018540d000301d1034160080c03140d481015180d2044440c1c0c1c2140448400d150740c000c0c42444041c000c140404045030f02180c0a800038020588600d50040c038045405aa88143ea0030a80da0404546c2c0e44060074083d008606900581d03100302030800100b5585032004200591098a003046420b80295030340c00340c0320a51390002d0703001d480d00030030b040f849207081d080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 766038444 1250 766037194 766037213
    0x151201090c0911090105030408070b040c17150a0207032c010e1f08090a0f2405090714120a1b0e0f040605071b050105070905030105010f210c03 63
    0x30070755850803032020000b50070b84244a86840030000c1c2d940c16003840409001942d01d03410052040d50031b403004000702d5001582c188030541c8035502c02c8404910281c00c00b032180e804c405901d406082c10b54406e01c402072040d10342c04030556000032065405665440245030846103035554894184110043c07402402034540c40840882c80020b0a99130714280210060400c00c815000c641d03d185401c00e10924940320608c140b0741c45501c400030f8001c80d0a00001c694410300b114074040016500c0201c48140c2ca42075512621042c0a1a24440c1040c00b85040c50003500ba00c03100c0f10712581c01c14900442c1010003940b05c1076030007200070003035a0075118103400ca8101181240285002502952301181c8049009502d8240c424003880d1065040141940d03582c0daa8001480301508943c10310102598245941d003920308c007200303110b02ca20300100d80750400041c06008074034a070308038a02c00d9051030018400d0f802c010507000201c1761202504003031480311125001810707202110160881080300b0001c414850001c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 766039694 1250 766038444 766038461
    0xa0501090c0603200f030403091706040b0708070206010e1315051005030f0c0402070c03050a030e0a080a053d090b061008060f040b10110c060307090e151201 69
    0x44060007802c040c05160300c4154141c0d841e07441d00144c28410f28a5200d0039501642d4068424240311003115118481c844207007007a01621000c0782c3c0f012003044100f201200d041ca8001883c0e04003144942020003001e922403d0500a07440586020400504c000342985080f100b80d40d003001400f4092407400d08118080c000481d054001004282d41c0020300d8240010540440607440025114000452041001960080c5000c0e0780600d055540400450410b01003c110b01d84643c641e1442c0300072070428441030b01000c1d481001c030780c1c110088040c0031880210f0400b80d404544050945000c03c41d42170030f225031070b4294100000304020314840f0080c42040c0c1c08011a6802899825055900d12041103104a1468031382e6000407030903c0403402c2e909040c019407012203c000c0001c030703105401401054496140f4240c100000308034115400e46d190003403124260401d001d9840c1403640c039041030041e00a43c550b224030007400484100080c0501801c00302c0811a94000f000460002c11008200b40a00071030b8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 766040944 1250 766039694 766039697
    0x10c030e040c2706080a0b0a210605010f210206120103030801032001141e1314030a11011b0803010303080405161413200705070b0306090a050601020a0501090c06 71
    0x1c48507074003040382140f580c0c00b254040daa0349092070380c640080c81d020b0440902056040141c19034041007041d1340e083c035a289001d140c40c100f000d1014174148402a43c0040e40100400c1c00045800d0103407150a600b00d01680c2c11110040d030580410340701265162040c0c400b1070b60700c0c2d04960000b000300740c0d010951904032030003104440c0d00d01d0b0240c88020030107082c0c802428085010641007600b20305050000e0650111000156030301d800500b26030b40d0050b4000c0e0030204411003061000d110310000e10020030300360b83c8190010209a000340c1c1d038500c44050142c06d8141848520262104041804130840301920341c00110242c5951707582c64007170182c417429a400c8426008880382603600609114518040303e111440b0001c0c07005044003400208550000c4588403142c03200c511003083c1e00300030141c10083c0134001030f03035030345a0041c14080d040400070f4008103010003040051003c0e13503072482411500b10035034030300028558580e01e0060f031500b0340114004080703509111005003030040b849042d0b8102c860740d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 766042194 1250 766040944 766040987
    0x1140111061e0a0606020601060e12010f020a0f0201020f0702040b130204081b030d090b1b030712080601021603060f140a0b09090706020304090c0320030702010605011d010c030e040c 80
    0x4074030205051350a07030b018540c016402003004000c3c0610407500d104520402074030280c0b01410325045182954941c01c4c01a00702600083d46851881e808010090303180307000e100071824a2030035810303502288101d400191040341c440d60441440d5444681206000b0b0300d041c0c00719600c0303543da440a078568106158072281210110900d00031070070041414404000b5950316181c01d80c0c1442000c02c1241c004801c1e0b80020300408010003003443c0100010040c0343d0088203007218250348001d005140b444010041e9045401040c1c3c00b0424540142c548030035285e1001001c9008005c820540380140140440111803481203c2030200d2007006501c014590390b4283d44100702c903601c404925680d105588039090060384204030030080c5020590100034481003920f0f0104003042da179101140800140c000c0703101180c4000082c0405290240716640040600f0300704141c0c4806400760059082c5001d440060501c111342501c40200b500c980100342c03034458010402c00c20100800c8000742000e48401403208410003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 766043444 1250 766042194 766042201
    0x90f1503040b061f05070b04060f1a040509011404081806180f030705060f03040c0b0a0228080a050705160807230319080f040b0a180501050301140111061e 68
    0x541d585010100c0504d912468a0b040881e981d107025000000c2c0144c1e8410340e501d011940e0a08140240d417541c0d090405035151070f2100c1c004000490744082c0c90713800641e140140504480d42c1a84070035078811342029940e601da0b2807460480d101042841a04c5510a400103a803807451034000166180c401d1003940c98140040c100c0c01415500c140da80a41c85c1d1040c0180494034040800f540110361161144030941160755803400d901c03280d9049100b403080941c121600f5656104054a80c0ba00702010030305640f401c1741c40315100c401440c03044010039800c0001c000b4441041c0082001044003a00c101e4503403c94559460840caa2500c2e03a9008141d80542624500300070550084181d0f603407400d0003000b03000000243d1450254501a40000300c03100324041c0502c3c0e0007014050040c100400054120303541e560405070000301004102400790310021074a030414091641d2110943e4150b60740c1200c0d100c0c40b5000c440041c0ea1055610400450510030001040b100e00100c10300420f41d0754031024051042d48 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 766044694 1250 766043444 766043479
    0x9020f041403150c1803030a0e03062404020c01150f290409151706041707030917010f33080a0602031e10051f05090f1503040b06 57
    0x1c0c0007107140d011412000d004600f1001d0404e0007401c003140030500c403851a10700c444c0420f040da040b00c11440045030003499403828604040c000740d0f61000c02e00d403030240b04003840b42c0d00d6152102070324000303030160b039000c510201661025408042d0003d03582d000c04080d165142c40c0000801007500500d00007000d92102d00341010701c1e85010350710107411105036504042c20321140030001c144e0b860f010b01201207403000c001045107100b0703e18003480c400c0001602c40b902d014100041e490402d0241506030000800416001c654400c030740c0d800743e410701c442100d130180c3c1849070180502000c0311042c00aa03c1c00031083d00e21070902d060544840004580880c0e002511040807502a6461041c1c02454000d0705081000456039401903503c4480302c41e41c042061030395040b1005002003114032000900c0036400501592801507c01c103001450b50405423041c14030b84800404a000300c12049000304003000c0d1012856a689a0a000000c600c548032500ca140c14104046455006c2c0c17450303030082d12f114004008a0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 766045944 1250 766044694 766044703
    0x3021b0610090c090909020a030803010b0c06220f0501110a050409050c030105030319020115090b040e0321040c0503060f010e150904150f020a030605120f0c0105030403030609020f041403 82
    0x1155151a4601813400417040058113a02408980c44607650b4400310000b1b05070009507004e00b08485180d80c46120714003580b45441e2014113510110f0b0000d2358166601200011694485d0754007050342c5c80394040c1803416a0142811403450a2070980c041004800705500201400440d400d07100184141c3c0c079242c0c0510b140703200a000c0e194040d0010806036a691160600504048816200008849805e01c2120030700300c50a4110060454940c0c1d041800340c9824051401c086480d080030b1860000a051200c1c0390300d100d061140c1b00049882d0014040c004502809001010003a003521002d01d0300681d0310714281c00034059800b500e090080460314030a40550310303031080240602620000d0300c0d103855004140d020501310118080d151a5410080d82d440e00182040354025280443c0a50415017040301884008400c0e16003940003004114030102d0008010141c500d0a0034050380c5c036111814104c016024640103124224000944030071400c0e07005008004403040d2004520040c040301c4101900c9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 766047194 1250 766045944 766045961
    0x30a02090c0c1608030a020c2b240204050f01030b090a09020a09020703080f0f0403022a04060303030c020106050607051005071701030c0303120509061605120f010609051503070e0103021b061009 85
    0x407140c0314090205403090340c01c1c92009e00d030040c0d02d0900c001200c0d40941d41481c40c01d91400302407907000f280030059414420680f40c0b41400909052050507070b000049000404028400818079448401d14019901c41022081c041c01020405642e80e40c40b42c02c000c0e000b02d40603540400802c80d00300004469294000400340184d42c15130140c4a1340ea0701001105080c2400b0724031107607401d0b140040da40c1c00d583d04e11451004601ca61400b08241c0d4035a4000713030840c3c88070340c0100e01402c1c0030031081c4000b600c04030b01c2e406140c0000c2c1c40051540c03148441180c2903403030140002c08000580d0004802c3c00508030446080f00d02c40e6481400e80030345083c0d884155002941c2c0c00000b907000300e02140c102030306020035006030f210510b8800e04180001c006174002c0002520081344c5444044018415103500400b000d015103815900c07000300425202c1a00703468400144420104043c0320056086680300381c040b07602c002000505184903080714030f0103030740303a65040d1403aa00e4026056800540c030001c60007500366 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 766048444 1250 766047194 766047229
    0x1030c05101d04140a0e010b010e0310090807150629160512070804080d0f050a0c020121020316090f0e06041407110705030a02090c0c1608030a020c 65
    0x82c1600342110050026651481079030080e1500b0000e02c040c8040101240300f904210004103000c01000015401c4607036881c0e40301e04010b45050109c4c06a140003c0d40000d40041c01800500801c03982007605460050b008010024108402c0c4102c0d164510340010341904c114040c030001a02c0d070120612101c400080d001c0741c50700c0040c0000d15103010b02d5045880054001c030140c0b0442741400c03581c01507541c80900c084030482c40c0402c051262080420682030303a101542422002c0680d90f440141c083e0003008607141c00c020006403a901164032500c035042c0d591649814480c0255041e10048029400480c2c0c0c0e109281c1e0310300350540c00c182c82804d0303000c00ca0f40488041c1032028107111100460040040030940c00c280ca0360008031001d101603444501c142201d64034201c4900c10f00150f1030400440b64801c601c42d6104680720030250b0f50300e081881d040329414600136584c2d1200c01840b810901e100d0250309039000900c800040488001c001450354550650a640c202011402007000c5030100502051 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 766049694 1250 766048444 766048457
    0x11041e0b0f070c0f031505101710050c090102030415050d06060f0e1801060c2a050a08010519020a020a061a12071203050c03190f0809010515010e060408010204090501030c0510 77
    0x11b44010555000a4002c00c00a42c2180b140342c60755a2035021042e079210100c055400142d5007040310145105007900004c071030351503525000d0382c080001d50381c1c0118000c05081807101240d0b0240140034108440c50301d0182601406201c1d42c5000142136021040074400c00725107400614002031070300750092100350070440e5035034890340d00784141203941d0140210103c0e10b00040c8444001c03030790000c40c192039200a0b044d055040050411040c0028640c076070740030301c80681c10135041c4034400d0300c8954400b0003103640c03110050311600f8400e400c030314241000c0d0028000c107203048010706508503001003c4880030310903100b000c0d545452111459803114248603400500c00c02c00102000644234900030f12103900180c049a0500d036040a41644040d40f443c1c0b603502003800c540241510036003224500d5804103040008101c2481c00029056018002d512100e0400c900140450525940c130000e45005e480d613103000b15103a903114103608004050030301065039001201d03a0f00013081c1c0340c80340daa0306402820f5035852 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 766050944 1250 766049694 766049723
    0xa0b01021906051009140105121b0d021503150f010c0f0605070c02130203071701060e0d140106080c0a0807030305040e060d0f050303071211041e0b0f070c0f03 70
    0x603801400060000f03420050380c1080040c5c0a0050702070180780d1041c1c50020035840d40344c8030400000d1b41401200507074036040a00620446ca04100c03050b0078010060310441d0751a42641b0005140e54040704505c41000004828800d080c546914074410030481511400c0c0f801c1c0c50303800151803051040303800818071400c107040e0000160254002c60b130402003c0c18404209450340d40007665400f50100704a100135400b00401c034029900131010104108211100e00203541040b8000f020400c60104030744c01110700c94440e10030480c1c1d900310032042d982050f000704007494442000b103489040580906105403e410700105041d8400714808040365410f4030781d03924040c942484030600c2480201300e40d9100d01401c1c1544040b81c03501007041003c1d4401d4024551303d20300007034040d101e0505d1542000105203007000c9410301180034001ca4007500c802d0448035058400c0c410b50302a010032150410060b41074007142885521400c3d40103445d007035100d051b0445100b6254000640407003600d22000e4481288600403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 766052194 1250 766050944 766050953
    0x406052403030414030a0f140c01140a0f2a140f0c011d04020307051c05060907050d090606080703170a0c020d050c0307170d0503040506060f270a0b010219 68
    0x104100c58040c00341d4120310481c3d200d86200d0512088151041c116108c819450070405124001c5080000d081414130440c2e40550003440340030701c0303081c20140180f80c504642410700940310f0401c00484541c0c00b958070340c1c4c980c41d00914a110034100b11003c8051401ca1840b0f48000700b02e5101200c2c204008140b10803450004590980040e08860195a117140d01e5008507116400203600c00d0009441d140c0e0348845102e0500b0020342c0c401d00c810500c919220511207603036512009140c200240d403401588400e030b4014218000d03d14490300601840c50071000207450316010400d1801c0301d014110003480107540c0e0300059024851420340500040b8141408401403600c00c400311156409541240c454002040202c0c1c6130100070b800c868040110241c0002c0039120070007451200c4d1607903107025410350516603552036031908040d081910034011300a1048031a160000015416200c0454580d00a080e8510f680400300e010790768003d0481c00c2803030010707013940005107800c941d004c0117004000c0a041c50300c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 766053444 1250 766052194 766052219
    0x6060d050403050d0921170604021b060a0c031d0a080d240807091413060209061603120e030702010f18061107050f011e03060b0304060524030304 64
    0xb02c083c84000c1c003192425040038801c40703400d00d124160850402a804d800410901e02c2c03244210201700602040304503030300522521030740010043e1005611207140d00d82d600300c00031014064410301e1107064100291018036801c0121700741d4140d202001081c2c6421300c00900e912065041c440300c1e9100c1c0c201310340044c042c10300612134110b100c0e400154004013800100c0114ac020306030000b4902c8072a41c140b000c03210a00c000310043c40c03010002c0100d0106807000100300e0380c00a221408050041f4140818040b16804a504000c1d004080c1ca64035540500b01030800c015000301500043c4808107841da80075414425501034459150081d030400a041d80116062800c203480070f02004000205002155002048000030300091345881034400d40503901c0768601512540024400c4044400c0c0340309030b0360084c0582020809811804e1b05151050101703402612041c1d2001451300300000402051100c44e6201a005400040d40d00b0299005e81842c5121309001c140300039410b0704104002c000d10524143c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 766054694 1250 766053444 766053451
    0x51509060a05090f21250e0613020307082e05040c020115080a05010f110a050c0304120b0a1b0509010e04060e0c071202010e03040b090f0d050c0f0906060d05 69
    0x385042078001c0200040748060440819140d012884820403000310641442010306c0c000102000845924010100d42c0c40c40c4c200340314408035061844041541615a4040c0b81551040701074190359904001d0380c010f10720f0504441d54101c810041224414040b28507440700c04601ca21103100740c809040100300401480d6040c1c01906640d62122440c408081d007040000041540134081c0061918600b00b040c2940c40e1100d040070700c07900c0c103480c1e503c0c0c0c02c0000e4151001d4a480745059603c9503500c4a8091661085030010b0440d134201c92030860400800980b06445004a05002c0c001d0150044090001c00558024500401c90611464280303500ca0340311640c010800501c0420f003c2d9036030404175042d036010b032910070f80050006003079418041c000300381004617011840200504407040c0c82040d01e0b402913000780440c00c603001a64a20319901c4548114446c0e400a0021030041403d2a10365500c1c6070010341640225128021402140b9003910241e104d050f01030b006520700140c0c40206001048000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 766055944 1250 766054694 766054699
    0x60809031204110d02100e120606030616020a05060a2c120309070b120403030c08010e0c0703033209010204030309170a0512070308010b040305030a030c110a0606051509060a0509 78
    0x2404c00c8009661400f00742c8040c865584c40d01251521128180f0a4041a440005400d0741c8034109210340c94a000412650201441d000c083c050700b11048200d0400004070300190035441048244541c0c044075074400c1d03252920701c088001506000100c00d2802c004000100402c40e04213000082e00c5082c00301c015640003091405480381c443d19852000f034142c210999140b28031001c2d00811007016010f2146a102c2c140f80c0c14000e5296140007031420342040700408200015001203071110405002c0e41040350b0302250210b2110110100301e9210640200c40c4419111514201000c1074104406208480560380c0580e108031950b81410710180d40340f80d030050000704a12440c1040d50110320144092002103c00b035560a64550f0b00e820003d000340d5068105040310101044100001400041200c1340f00d072442c2030224108030003000503101c41c801e541c4684a1030003014005400c01050f46e200c44142c0300304840e001507503a4080c803811031500034104580d8200800300442c00e0303124040c02c05001d424200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 766057194 1250 766055944 766055959
    0x21512061809031e04150804020f040509060a0f14070203030402100809030a0c080708042306120415060f080703140c0109052b06090614060a090902060d090c06080903120411 76
    0x206e90058039007004e84d01011000170284000c0c8421460416909801c1260403030b030a00c1581059122141c80390b0005d85050310070340d541e4065040040e515000540c080040030500007a61410b124060348a500c02c40d8103d05c2a1074070110b402405008010f800d015a140200a50600081201c280e8107000c4107881510019402d002840000c0c020344000c001401040b968030820071240301d500080c41e00c40b0390f4954072031001131121900e5620400c03c074a5115401408900d11a0060203070b040080400c0d40106000c1083c0450100c0c0b04000050500220307842066041c0700d00106c201d01e107480e034140c0c81a4500180c00008100040e01e0b141058440308401c1411f150180b140480a40240b6030740000d04450860712a403c0b50140704151082c1600743c41c0c2400c07003c407070746880300000c3c542070040e028041c0400ea843c4c0f031031002c3d5100c080c15a00314215544003004541d0075820311410400d03d80c46002c0008070304000041c8c40303141c0401504c0401400c10f680d201503403100d640d5440f08100304000507410003007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 766058444 1250 766057194 766057199
    0xc10050c01060f030218070c0204050c070c08030c0c1f27080a120206101502121809070f08012102030d170c07050712021512061809031e04 61
    0x1030a1181200803d8201c0f41040c4451075481440300628090000a00c4c0d00604420015001d803c8a260726003294111000a184d40d41e03008126028066014041e1020800c42004a40700c200040200906450801150000c1d10150200560340d0301c0b400ad61481062082064540103019a11109020a140755000c02c41d55004840101150107540015407a0780011100f03010f02c0044030708a05042c5032440a070046107883d05c8504000001840f03150680740d04240844400c51092000ca03203607883c0c10604036614088424504000e00c01c244206100e885900c0100310058024042202002c2d000e0311215256842c000780c1c0307401e548903002c0d0311003c5040d00c0036480050b6020f200c6070001445c0d988601e60424001458002c99840082c805440044100540c1002c5040001d6402c111882032607400020003062001c40e00300780c4c2035035480d0b0028001040701442074140407903152103460300740c442c0c02001c12183d40b0810581c074203681e9100301d41c104201e850500410601980b40c00c594151030700b0700d000c0d07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 766059694 1250 766058444 766058467
    0xa140a0e1e0c0d1407020d23070b0f0105010e01080c071e2f0d02040509031608070302060705070f0b071103040b04061805150d0609090b0708180c1005 66
    0x31411100401042c0000a15004082080c4980e1000344005070f081141880d202030040d40d29417001c181c0304180481054107040700b9850108480c0703180d940c4202136888102c02c0c0b034050321218054070159070b01c81580c2e0010499501c1007241440480051392045d43da038842035041501544891fa05541c02c100903252545c0b125011030000604510981040700340c004200c032210204801c13500104111003e0103407891003039441380070710580d16404950004194860f10745441c41c40c41039040a1400d1108603e026080c4141000036000b42e601a40a6880c20355903910304507128401c04000602c0c1280303058101021505445005500001900f032104260100701412881c42e0881d40c04034280c03110001e4148040d542c0300c0394008640300d54181c54485241003a0008034000d9030800f0741c441ca54800b00394200d40c205240c0100004041a0804100c003e2040c2003403049035504881c994040f918100101d24003102150101c0044141100038220310315108003089140d0002c1002e040c200001400b1800d040c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 766060944 1250 766059694 766059751
    0x1d120d0e030a17060a030335010303031b020a0314030717180f032809031b090b09060307090e01090501020d060e1315050709030807030e0a140a0e 64
    0x161083c1e1502c1e0b0010b001c01c002580d031020001d05003409880c2d0018100b001030781100d014020f608420a028107918110036801c500000151024a40211090000020305402d03510464004031105103240020b00940f03820790355403408082c020005510b40d240104012404405141c203d5500c0ca031041007001141801c0007540700c10740309583d030420156040050108100003c2284802d070001840c1002d40c1c184000b482d540d12b881400c000d00408580310399540340700d0ba40c4c031409503074008665030050744805e5410b50141218010031030305901d01100c0450600d1b1541c4940d204a134024010626103080401d282c001d04446500800da56403207454000c0029000c1c00548150050402c000484600d044401241a20302405401082c00106202d00c041921600050028000c0240108941c1c499920842c1d0b42d446540c009008004041038500c10140d1204201445103011140600340035141c5c03a40310f0218207115502b036480815010200309804043c03175005c2e40055030300103680f10307000701d004d150700d01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 766062194 1250 766060944 766060957
    0x30c0d0c05160b0604050105030f060606210a050702150412030e19050c10050901021e0304030b07050903060108011505013f0f060302181008030a050a02011d120d0e03 73
    0x39501070010401c490510b031146d1801071804500500d450185020403070744030070001e418180205400120038120119681c6452038900700102c03a45c00318602a40020f00500060340d408005010b2110502c840c011754188e0b032406141c001c0080b480340e070305c400307429802850240d0f10003040e4040c4010084c0486107184e402e00410b4000c0380648019580903081080720400c202888040c4a01880401c92690380080c5484d0501c1090802c00c21144110311110714600441c1d100a0400710654108242d0a901a0240c284004103408807800d03a62210340003070036036004036454241c01d00080c3d000c22556125404440284202c400e46102a2520b1000460401c6d4428401c5010030750000d002d8540418500c10070840310700e080400c00c111400d5500140c600c0d80040c030700ba0b024045150100c2c10004444003a107006200000481e5a1a00750b442c000d0000c3c0c1110525101651a1400c000b4201c8180b161000740c42e103580e0090f01071612001d9544600b40c0180e051110401c0d555032240c50300340e07410802000c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 766063444 1250 766062194 766062203
    0x10801052214130507050a0f030b0415020703120c09061d010c05070f08070603090512070212060114011704081603170a09060605030a120e0607020307030f17030c0d0c0516 75
    0x880315441c10b1851170443c2c96070280340103005d2444100082c42d03d20705840240c903400071034082c540e03e440c1070280002040815170700c2414400590201010b8000700148445014040240301d0b0009c100010b5038012140d1203640d0208001d540165008066402007001240d414140b2882d0318205440306441c10000743c02c60010344001242c28003140d5020040c0700b00610140c602130010b8030a82c0d54007911010311955110003803d01064441c215513a02c09541c01984000d8211003843da950241040366044d21640a80812007182c440c500450501308038500c07890300044007501c0c002000d9608850340210f04020340070400e85a200600d0716000710031a5000365401440813680c0003003070070a0021110190700840c40fa0b2b10444e20b031400900b01024071124400242404031201ca20600807500340d104164000b907050051040200401c441c1512480b1014000c100f400b2940c018103031041d0007480161120072203004180700138400040141c020f14131002c0e01c2e02d00941046100064004117061a0b5000ca4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 766064694 1250 766063444 766063471
    0x3090302330a2a0c11010309080c0a0b070f170709170c0f180604090c08120403140307170903120f030a0b010f05040902070c05060a0f0806010801052214 67
    0x1000d040c1845418008915190100b24094540e11000d400309460030070040844400445c248150b078000d0380300215890b0414007050fa560440c080498803170703401b0b0764116400d040e050041100c0c58481c25a882c112115500e4032040c0d0080d400250051107401071000082007078401d00411403140301041d0015495841e1300030318a0000a80c2040926000c000f481c0c2d01031440c80407800c5044020019590300300400b82c070001010320356801d10340c41e221030942101c4410302c90050084808600c03003006004076405180400682c0c07602601607500c0780700f16800070b410007200707038260701004440800411085000a04807215030b031000d204400c15030800c410a40300c906010040100000580c001c2d100641401d10701011045110300014003e80514040c4110b03055020a120040118001000c1c000d44002050103481c0e0141e40801459500403500950004a0400105281c0e5000d41035150503604002e01b881750056240301111790310392000260780d20b86500d0b88802100c070100300007168054429910a0b6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 766065944 1250 766064694 766064711
    0x11d06070905031906050a0f06061701090510170a06051006120c0f0c02040f0f050601180501080c0d14070f0f090509010b0f190302070b010603090302330a 68
    0x41c14030340302544124041d8100c1031404011140012000038016030041e0002115202c2059050003400340308182d06c80a0300d4801d000c2010b542144001c07036600791202250f4416a26618500c003918815910943c411143c60010301c2807207843c40c4c010741c0061904080312540d2445031900000c3e65801d550a050034040c40c94103018265204000fa4030b41c00d1010400d01c042c0842d40da0007041c406001e4840e508008922403003008554a68002c1c600600040000740640060071030b1a000902098841c05d01080d03507504440701d030602151010046410503110288682d031240039500e81e0383c0c0400682445036950b2581c90000804444545005400c540e8810b00d000e01d07089800b40030700b0511402d9105000100030108455540c20400d10b0551f821b4110303440d111683c140d034040c540d00607501130204030080441c241040d2540341e03010b4080c0c1130040e410103c071330b662418283d003211a1003a01070700580250b280b90342c4500514049000f5202c6480700c118a0031358a02a031074024000340d800c2d03030f4100d807076070a01d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 766067194 1250 766065944 766065947
    0xc310335030a050c0702090601030506150d05060103060522090c050405070f140405150f04080303090d0e0411030406112704050a0b0315040804050904050d0935011d0607 74
    0x98030344c00900065403d01d0f050564000407503440004009078105a02c85001600da5140d0788650f5244a0b03002030410381360280c2d0715080700076080865006002a00d40000010f1601e06031244041c1002e040109410f801e4254584501030401c0e1181502c00c00d040e840700041a46031031140c0c0e07105400070b40e40e41010b1401500c0c020910550728400460600f401d11042c046aa61080305000e0502444022603441841403d149164003859020f806540008410400d000c4400f03d64200b00d600f065072100d45642d076010420003102c1e40c6007050211b05038180b00140002d00d030359004101d414880200035080407200c90b05070070200c10001c00c220550b0b0941115115070b040600a0716084080c980051040151007004280d84011000c40b0071405400c82000c41d041c8031140003250054000940100d43c5858181002c0355600c040741c40c043d00184c0d0101001903401c6401002c2c50401040841040b13005d050380790305269112141d079291085550703a2080c50700030100407241045200160000d84518a0013040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 766068444 1250 766067194 766067201
    0x3080c0405120a3503090115080d180f050616150f0e030408060c13080d0c030f030605091303260f010f2114060c310335030a 55
    0x1609880000804079400d0504604000710003004918500e840340c3c1c0e0010004c2c05401410100341081185000202e00010042915240f03140309484509483c20824034508bc3e0298500c5452081240c880080c407861822a00800040b4141c0c07904200d001d03401c4c0c031600030035180c44803480e4130a5034840104004400034095404404100701c05142040e244c800e100ea2180002000130310300c5040007a4162021000710481800f9140c5001140d560441c0c4907000b402e07040700303084190013140c040c0315480c148070310034000e0b982902d80184c0582e1442e1954202c00b2680c03060100100c0512118000c10f441a442c0c4000644200c2e03e840002101c60030082e008503600315060300000864502100107000d840048009180780d0451100c001100550703a0a024501e18010f031840003240c0121003d02c000e00c0450380c0506141c04014010074680c80243c0c6d0340e0b2807015000c030703072a6100c1c0848107001c201007200c10b088402e4000400301500c0382c1d0482c80086890030f08543e41604d42c010008400d00001511a20 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 766069694 1250 766068444 766068473
    0x80d020a02030d050919121e020a18021e030a0c09080607200615030d02011a06030a02090a0f0e130b0609060301180c05030d1b03080c0405120a 63
    0x10340248516030700480c0d21540382d0700b541c3c410301400040382c010985a0f580158211115a5910a516070321014007515900c5845410b0b1901c07400c0c2254801245001d1a090110744e5001300100c0b1010302d0811072180c686000e0721034810f03180e420310403300b9012403491031701400b90b5910640381d030b00d1401c0408a8100c1d41490f40306410030030fa1510030301400c42c0010f90303103030071202d0340c1812540480b10f01d00c419490038a1244e504524062401444050513504404002000c030482c1030340c0342e50713940c00c200301e00b01c03a0480c21045450501520450b290b0030250025900495000750140c64100d4110110703100d0300385507000d4510301c55000d004001404810f0b620759040400e10566403040045c03611020003100018101602c00c0b82c25101084c40c954096200340c44034403c4042d100f500804178280b80f0080708562044e180240034565500c43c60710b220b03a00b0810b19803d914000d1801482584040301d50850041c0040c0382001c0411002c10650340703820000048544d00700042110303170b03d00d1400c901c01540d1303031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 766070944 1250 766069694 766069697
    0x21030f03020d0f150b040f1403070f150e1002032a06090303010f1e0510030f0606050909150d0b1b1b010e0d0f030905010f091101021504030c06091b0807080d 69
    0x6e10050002d4464500c0882c00c849090aa4910b500710450010f81401441c1d03000030b1049200810003d80e511000812070b0042c0a5511103441602100040c00540c007520081440182c108102e101c2650260b070304000155180240c8480300c03141d6110800d8500001075441c07014513440800100200461002100041c00d000c050a655000102d50450b9140300785001e001d210748860003e13800941e20980c0030007010007001d0014401d42da90b03400090300c00ea009002c200d00622803800001c9500a468141210350100500030312480c014a450320948544064919007040c140014500d0900300090003074000380d104140c041d46e000d09801d0607a821540704410300341e144e0300403c1ca08403a0715008091407070204002c2c2000f24403c1041d00d8117500600707944074107901e403910780782d03a81040c0300f591000d2123041c12080c0c08139840172407000215200320804940050014060070180c8000130b600c2c2d00b04404280c843d441d00d03050b080300b801c911001c4100e00d810004036540000e0042080800802164420500c113 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 766072194 1250 766070944 766070947
    0x8010203010e01230a0303080c070b07030203010f12020307170a0501020703181d01180b0d06021905030c0301140a150c030e0d0b0c16050d0203030106020721030f03020d0f150b 77
    0x104d011a01c40d204070310000e024071042c4030008a458620314100c4003001da0010450300a8500064050000d40003030003102c0703500e809640c01140009081c01c0607810350382c009004088281c40d01040d04009039402014130041d01072160490002007090000d410818402c0e00d895540348041004100126900d40c030000c0041c40d9101c120750040c074000003542c159400d00111640703409000500f04040e25400514540000310000070506101903580074218280c100d042c40f00003a01c02110440f454041070340c45a01e400d004000410060341c0c000e021800410380506a07c0205a0b0780302c410920301401060383e004100c01040301c0d410154481880740103484120307041c13018140507444030800024010101d0126010000703108201240c00080080c1c903079440b000b01c0381c012040d064001e4503034000303204030b10141c421614041040d0905003295522840d290319902c0340c0b85940d440c100d0328150030841420603da8204208003d40f000d900950b41d2940c0d0340440441e20b409a0006413070658900c0e4840741d0300c800e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 766073444 1250 766072194 766072259
    0x1206091e12030e0f07080a060c0905130c03140f0901110423030c0a0b0c06010f060522030605240301270804091505040f0b0102101508010203010e01 65
    0x658100c60680580c1e460300048904401c50345070f150000802c0800306622914000107001c0c0720004966000c40d00c5454103028218065034207071608820340c000e4540c0030a101c0c0c80d00c0c02c990f200e40d01841803c0c1c40b07840d0206520050280c01d59281c4802d54181c88400168010012088802d0140082c228819131000b40360500d0b0502c60707050307000d0241c406d15006c02544201c10303050740d080184840c02e0b81300030182925a48d4070300e121080d980c0003040030720041c0200e500000b04a207114408104644131529003a240c5440b141c00203000500360f00700344020014050011000c01e1481c0f003120700c2120301d1042c401004072821581d00400c150520320034400ea040840c1c5440300320400911079081c68804402e8514103203540b42c0301d07955005a4000d098500c0ca0400041d007111505080c00c2c04403401900e040040c1206004000144c2c0c40d20344801d4096801107071143c0100d0b4160348128001d2104032082d243d02d60700c81e42d0080c2682d10a900c82c54a4005840060100e118503101c180314101522284010036070703 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 766074694 1250 766073444 766073453
    0x1b130b04080f060f06040f0b0402033102090406240602030d140c0d0b010c14010203040c0617010b090a0f03060c180e0c0906120f010e090a050c04090c1206091e 70
    0x1074001c1085005585603a44000e207c01290840b26200380024410754407407404003009a086120700003201c219400e001440020001c040cad08002045401900141a0703030740d00c1d00c40e10040e00c2c40a59488000114464141c400e548103a086000f91106501455413102010580410340382c40300c4220010034056010321039500340100458854070060040450050120030041c0e5122041c020701034400c1c108010411102401903000758440c4e4030500e02d08080d1030700d44a0848400700308ac50700d81000d0010b040188030b00c240440240c840d05070010042c90080c0e80f103c0c50a24144580d071b20840310719886070040065036401030035203200c088000920b20120752a0004240d400c06015000d001c2c0ea210004a0301070940707030f05044a208010000403c1d40c0c500b0b0443d80085494030901c950316071401c80300c001c0303032040501040030045c07550468001c00c188150001008020501544116003041c1300520020740402081c031a40e010381c0c041c450002d0407809030301301051000c4444c0343c1d4500080c0b09880200c0040d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 766075944 1250 766074694 766074721
    0x90604121107090c020f030403030903021801060203071b050613090c0f12020d060314100e0f1e2d01050702010605010c2003060c1c020304020102061b130b04080f06 72
    0x12002400c010a00c40134909050341040f18003a00c0e407010707003c0090040305154000d480301d03084910a17140800c0311003000c0c1800c41c5c04502802164010b0b00200450310104045c04203d4490700360100e0701220580d9180002155980304600e800b0b511101c4c030104101c413502911800c4041c10207400c0108109052040c000c0585000e114002c0e205940071480c061401c0072903001c0c2010303640c00a02c04201c0701a410310f0342e903aa680c0054007107a49050200d0b2007200305d404180c0e091507000c0f9a00611242800c40c442c48007400307030a14424094411b214018600b58001c0c40d1051701c1c1390f80601806540807042c0c80e002e0039248020220415681001800c001d166841280841090b41044441c034455039085203020032080103020701640b507c65a03040c802480992801488255a1648440110313440160070200ba80401c640180c0035030420b400080b0903d0704024500140d01d0340c0103a480c5011010811003030903001d070340c100211041c800b0509010011080003c81c90019002d001800b0303d140081444015 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 766077194 1250 766075944 766075949
    0x16090e070e0d0602160f0506150f040b0312030a05041a04020112020a0e040c08090c150406080601021024060c20010203090301052a0c060601140d05090604121107 71
    0x282d050581c10109000d015819901498500c0340400c0c0300403414100b1410005504109507480d0054038042908090740031034224588401074804a43ca210650402c0300800000001d01e4050041088001c1d0180c1880c0046100d41c0c82c0c003100080904060070007a0a808144080d1001e0022540c02c1c800941e8008040200545e0b03804800340e0ba515030070100316920303051a00744c075820504101d28204030542060340144521040c80c111600ea40c2c1032007c100140c10229030b07080d982c1408201c14019148a44882940010180100c42500440d01e01c00021200d41e40b10150005401841440000c02c21001c2d2100404580c540101104c196445010085019865601200d210034a082000f17034002d2041d40d082100c02402007115141078112040701c3c8400d840000c010b60529507004044000358004e0720125002c010080001c0d035200001074902400481151f41c2040d0207012851240710180103861254402c103000d880c0d0707400c040c5000006000407070040c905000c02080c10071000ca2000400104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 766078444 1250 766077194 766077199
    0xc060f090d0609050f1f06060c02060705030f0f030708060d050309120c03070801021c060609090908040e0a09200f0105130b0f04080705030105012601110316090e070e 73
    0x1240401c5280c11001000c0f600703002005806210034050200c1d07404503007038880003108586071000600c6058000125101c030b014403c046802c107038407039002d410140d014205691245040b2481d1050520384010540c00100850315141030000400012550009103942c0244081e9058024492a40e81e007130f807a0b010380d000072800b1703002c19027038019201c804110b160b5a000000d010740740307641d4640c440c030382c042c2d480b0125a60b86001a03000003020b03040684540421503801d551800f044c1405d00608101a12060400340c501c03010520010030001008180d4600604000400140039480c610381060440c510390701000210b9800040c0c0011070301d4602106007240001d182540d55454081d07180c141441041e04206850784d00400c00e00801c1c0d800100402c29100d03071a00f222115555001050300f41c0c2c009004040d05414484c00e0070f200c83ea110128851410200350002c03a0001d40300b44800030701d070000c03148031030001224032440c012185c00040107030161900110542a51400003000340c2031030b400d00070260 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 766079694 1250 766078444 766078459
    0x80309032209142701270b011505070305221d0a090818060d0903030e191106030403050702090705040f14030a140703060608030a03051e0a020d0209041404050c060f09 73
    0x841c0100e003035202c400032001c4a04007440d500001c2c0d1a4040c518500c0f0421140c0d0340e20f080c0007140d0840704a01c1007440340b062b07507030700c5103800c14aa030100c510b81c000040c069041460540200c0c1c54002e00d445c5000a800d00d00d2094150a840f40840c203a41107019220132b54503880e00c003030b00d00420400c07800c07502c1c1341210214410001d020342d801b160017882340c84592101c1d10305d0032210074101949030b000120310b02a4402110150b102c01503840c0301c0014510802800070342007804501060170604041e43e4054001e0420714100200c0e5008185202022a804400140000341c02d112803040c45070030001070000120440414101301c40485d9480007917035409041c401d510444041c00320000c001d941c0c007a6601100c11711074640d0710810a83e807a04001c2c00c10020070306040020b14941b08894110400940c41c601c0703004103440f4174003500025071140380920b407260303000c1140c0c1c080343d1642d000303403e040c207813008503541a4505403c2040c10b10308512002d1344604400c014000e82200c0c42d005454440c0000c40741f40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 766080944 1250 766079694 766079761
    0x1030b0a060305091612030e010f0206060108040804030602120901060b0f120a0b030a080c0c0f01020a03080a1b0801090f02070c0b0c100603060c030e0f03040308030903220914 77
    0x1482d09040e603504150611600c3c5d404204120641040560076119071100007044110b0401514000310910101006a01400004031a58410f803500c40d0098001c54205180545035290709041e071b400319211228400107030b014448040300912400c8010114a1442e604083d10aa80000948148080400f965041d0004100e1250555100480201e402021204880c0140c80e0081e460f411581001c002405100b0b26000780d41400099084813400507405048030314010750b0705a0380503001401c0850750350360300c03500420400b03007211985100c110140c485544543c0743c101444140c0b42c0080500841c54014041d0703800140780f1a5070783c026503072104503c50700d852580c000c41c2e142c002030f6150004000c0c00d103000081401302a903c81010a241c1e9a42030042448404d0015a100e02d0211000d5099104110410116005101554201c5190b0044c1e0f0326140400c4c064511048401c6030003030044000b48402c002c1e10f00107102c0c1c0f6845c090401c0c00700c4403902e40040c44110100c5060301c04900c815117110003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 766082194 1250 766080944 766080961
    0x3090109140a0b070f05010f0603021003020c011d0a02130207120c030e0409060b011d06030a1112090f15091b03030c0d0302030117010905100222120c0501030b0a060305 74
    0xb00010303145400040351a00524148190b144568400541d07140d4603000c40c890310070082d4001c04090301d4000d0250030700708815200440003584041c0004625550321001010200203452043d007210340d005004200d590140d00410072400300e020500e0310902d01c1003054000050080c288812421490708022085015038103050f1401c0c25120142c1340e100d0301d0315140b4000c00086c2da210301140304007070382e0f0714101d07180f9164882e044110362040d0541c001c2082c00042e011a0480d00601c16029890780542c0c2400a07016030500000800d90313128500743c10880b81c500041c40c080048083c04001c0660b0103004c0e00f05003540d503071100092a601d64980c01c16403a891001e8401f002101c4810f40c02c14116424140c901c0c4009009410a000e0705900801e410707200310108505008507070307040303030428040c0010210550b0040000d6004020100c1c929a0009802820001034510100240103481e000c01c04d4110a1428820030085070704554149448c0240d58a22921156514001d50343c090a0020b56074551181 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 766083444 1250 766082194 766082209
    0x11812080606040e010305150a022d04050a08150603151f0305031b0c010c021302030402030c10030f05010e251b03031b02012003060a0302060d0516020309010914 71
    0x1110007850213101c000070401c00002800c1c440d0f0072912a0344402d5844050b903c1040e4842c40441c0c42102d079004840c140c1c019001380034030910000c10740e00d09140980d00d402081c00e05c942a07005441c41d03044111420444d4100000140e404201213014003a01c0f01340c0e07010b103c0e140340c026000c2c0303518407442402d20840c00682c511120103150420101ea1321044860903200110007040a181018022004c6000341035004d1600001c902d40c2c02004111900d1580d01980025000103005a9061192082e501099120742901c05440000c0d9a00031071008030441541c0c0a40c0d2040c2d00c01c05442c41611304003c482d07000910106411554400e0f2104404e014020407684c00c040284040015041c030044181015096030084521900c898850910800b040e03201b64204e40c080065500c0c00f5520101700d080464040f002103a200c00005d207500180e94403500462110780010722030304d0070141d481d4140312060b00c850380b01d40325140041c802103103801031640000701003464906c225510380740461f014a6081d50380c0b09 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 766084694 1250 766083444 766083449
    0x110a080f1f060b0717090402190e040606090e0901021201080618190305181909140601020d0507140a0606030506060a0513230c071a0601140702240c01181208060604 72
    0x7e1042d51601542c003007100d010240c0c2d1304d103807010415150070f0b0300743e50505024102c12603901c0d0f240c44200914094051110500052402083d95800c00442c2e130b0208140502501034080a0000d02c3c5510b40b403c07041014415580c0209035130b034044030300594243da003650890000c660510705940c03201c0c0e121039101100301285a045900c000c44a25012030b04500720350605c1191007414040c0001901da40b4030501d01007090760101e00681100103c48001c6010f14000d100851044035051b41c10000c6020f483d0504003198030445900d6150103041043c020204059908008106d0700162a83e14107400686081c0030390941381c0d40740c1d40712002c0c43d04ea85c009a00102c0380f400510315919103450b12100250203a84500400c031a00c45101580101c4019040b403164411036060f19011780d000504091041f40307070404a000c03648100581f088401000c402110001c4c10000403068603224200c0c00d0165080d646100320b0351210b144100328110201d014009051031451040c10040b0a0340c403840049120751007682c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 766085944 1250 766084694 766084699
    0xd030e0405070f0e0a0e0402091801021305011e02100f0207020411070c06110607120f0216060b150306040e2107050c120604110a080f1f060b071709 65
    0x1d42002880da40140420740b51003515900e00009620700b500f00504000d0034040c4240400407103001a00604040700715541044158211129041465280c203080ea48081c08613080c821241208002551300040507108550b41c0082c200c8031002c44480095407225400c0f14081b2071f03920b403404250f802c156a8103d50000d034002d4814014219101d0030080381c3e522001d02100d4031903116800148040c0320303c40d802c1d81c98a428028125036180c04038110780889400040c0c2120b9565a505001524003505c001d2406541e5812816410401e50810301d0858844012041c040e044542c020055880b4040869910030130845000940240e0043c2480c600451003000070b4400541440c81c41001a5075005000300c14810000c031f91450804c40e00b800254545015111520340c81030000ca80060550030180e1460b09c400f5000d002456655020303649045c20b0401010001d030404140c000d142400c1140608541c888100203002c490f140c4044d0400310302c12404081c00180d1207900d10b032928001601200c0031580700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 766087194 1250 766085944 766085951
    0x2150f010b0315190914010509041a044107120807080706050705120604060302010827030406051b010504020a060507061e2c0316020a1e05090a0b06090d030e04 70
    0x25005c1c0c8500078044801101036842d1442c1c000181807406284d1540709991041264200ba202c60741213055002d4003620407941103c980008100b0510180b400b007801c0d9420f1030040c010003802c120341d2000c4a074140f54401c01908408810b01c1103201c1e401c54010050360010a142d994020790070804107038001c1042c02040342e17007004180005554000301424800f24481e0704428291540c00400c012141c0c0e5102c001d000c90003950000d110000c0c01141800990309400400d043d24418414460841c0d2080d0801408100045042c200c2844161717074401d040703203c90300200f0050605800040421605200d00c10030054005a000c0c00c00080d50400e26500b5404d844280700c090044c80104013400c00203008141d03000c3c01440382440d181c0c003030507004240c0c141c01c8007a6103808041103540030b0880c611001680c104618850016085c2981450202c8442c0c101015402d01d5040c4420000c1e20b2001615443c8000d00b4826840c4180e5a074404a540700c4204407034134a00100e80b850140c03803103c0d207906150f6000b440d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 766088444 1250 766087194 766087199
    0x41101110a201302031e0a0e0a061b0206091c050408030d1a030a020d02040203060a03051c030c020f070b1317060a06170c0f03120a02150f010b031519 66
    0x10340e002d4508031602c0884960220320b070354032060b604900086814561400d04d122040f040041c419840c51b0b08441e000b40b0116842100d01002d910348080c810302155410f41e52100442d130f0846c40242000c2c010210700c0a002c99003002c0d604944c2d122030ba010070341000061403064030301181c081c5044034002d1402a043e240c503800b03103800c800c00400011741c10b99000141c1e550303801e07214a004944a00c03c180c3c02401646440096021701000b50002000c13180c205030b50440c003002041e000c00130304984d03402c03200354581c8111082c0e03001021703104100501410b550115100c0d005440b00491503100361400401455203a940c030515a20000b19590710000680c150f1700b112074202d95001c96100c2c8103100002060150907a1400c5410040100d1002131442c2d8000d030400304081e28120191480414008007107a40c0445817110011555000401120250740016102c2c41e105c41000c40090740302400c8000c0000d80d40c5002c0da5401580b10003001c4990400003036000c07401e603a445400c50b26050030b01c950810b0702641c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 766089694 1250 766088444 766088483
    0x40b010521190b0904030c05070f0b1c05061c030e0d0b0735100e090a03030501120f0b06030f0102030c04051905010219080702060a1d0405041101110a 66
    0xd0241c0700081410510204520310304100c2c05083c01d4401c0c0079003007007001e81e04e40c2c400b1500450881d030300b1035917405414000122075103070400380c034040c6c40c414000380d50b030301c2c0d4008008203113401d504003260803281070000b080703c4c039610f5140200302d0150007440c0045821262400704c48200b102d00550781d10030079402c400414800c203220040d02c503a4135500d0b4400d804a00c00e11000254114213802664013800c02c1408c124980810300094004041c00c907488049519140c4102075024122189034980e0300281030b80090503414003881d4014100f00040782842081c60b11261092030203820003816481420b0041a807a45041141c640c9514002000310344030308090b4014180c1d54401d1041510803401e079150000360ec0c4140c40c6603c2101d005800802c0c454085000c0c003520101e40351410303210710505104110158484034000c003001d45c9a0743e6134001d0007105042d42c081b94291072001d1805103140004002c0054110040d0240e040c609007441020915840d1865107001c08204000303100c400c010303a02d248041c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 766090944 1250 766089694 766089757
    0x61806090201020c04050f4312020310120203030c060a0b01030c0215040605101e050114120103023001050103020307061d0904061805101802010905040b0105 69
    0x1580700341c0c04d80740f071060300c0401c21084d01c4003075980849902d81395000c41c0110008031840c10110759146641106028070814a1464811480180000e1000680c020708895803106404580c480042c03011070a5040812341103209848900692043c00100040c3d0010f540e020004c0c0c940c032030f48001c00c44d001c920f4408149009003a26041141c042400c009900c043c3c540081007a150040004015501c103940326180c540207014080c114422045c070400001c84d4022030892906074904110940031829494a0001409078800d01100c045115052040107640d040c82c030074450449070120703111207101c19049010510603040140050100c8500080c2c0c0d0303c50b0720103402141c12607000700c0c01d41e2105603952130f05549020340c0175002c0e490007005544507403061030203400d43c80d04a4024040015150350b0b100c0001d09080c03a00342c040d140355110755029043d2480a000b03142500e031220420039601c8a4560000e800d070000e40c0105407043d600caa00020003640329505482c031580540340100000c1e00a11001c8401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 766092194 1250 766090944 766090961
    0x103020d06091e0b03010b030303060d0f0b0f1b031905041b0801060503120a051204030e09090f10020c0c010804141225020a050d0c180b0109050d0201020a020d061806 73
    0xd604100f0b5140d13003840c061082c105821000b401640c42c540c0c03000700300071104061800446802680c0e0364410007260310070714035600c03034030000200c10200d0604ca65a2502e92540100c0c0c100420400c100301302644c50701c143c46a42c101844140450280c5a42c60104411010360324030002c900400c40c070009500805412140888070300350103444c01d0f24000d40f000020780c81001401c5002c150104450814000d076401c6080d40305000e40b03072000c20102c0c100d00203942031320140e644007200e510000003016000750a00142110400007030342103103032255440359076071100159180d0714180314104c00000e05000f8031111080b00d101420b0155520102c3c0c00703010440da60040d000d502d503150042c504840301d540e4603040d03418140350018000e140703552401003040141000440c08035607054141c20300184420904090302a61040d40d200841e41c0340a00b4001403140c51190702c82441003900c0c0380c881001d82d801007088102290141e5078081c04490794201900640a0707a0150600564240c840000b4402240c2c40840c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 766093444 1250 766092194 766092251
    0x301051005091006052502030604030509011701060f0f021e030a020607090b0708070201050909070815091905040c0e0c03060117071d03151003060c1d0103020d0609 72
    0x500d9281d03c1440d040f400030500806012501c1003051824054182c00842440e103510414680001c180e540800e09182040d60f080f00413a4020803e18669078101007140460216000ca1048a40c5001001440d071540e190404041c03001c2c41c42c003050002d1007031084000c0b6000c1d9160880c42d080305140e0b220b03560f81c404c01c5a4001800b5020100d0b0b5041c0c03281150004945030316881c2800c0c1007842c0c031140e61030b44c46044100c1c1440340802105419031508040d8a1103141c06445413012071a00c2c482d01c490310f031001001e861158942008000444949100560744815100000a80c1d1b594034500350a0440c102d80141d02d0b480d40580c10003611484600007180b0034071003a81c541130300030480005000c6500060740c40f800401c50f4400e2035100c2052003100e141030b4250040444150200c24200454014415100c40000500703002d001d05c14040c95011340426442d5616016040302c0c40c0898241c2c1280904d0222410076400041010711403041d500140007030003410104003d100200d4410a144640300140d218 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 766094694 1250 766093444 766093459
    0x60e12040f08120313080f161a13020901150e06071103120403030807030c051b0c030f0d140706141f0501140f0c010f020307180f0b09060c0c0301051005 67
    0xf01e0003400c900540b8090301d0340c586180d603081d0f0240d59184241d0080c4003100c00d1180e0511800101107038012035920300c140146000ca07041107801c00013a404001c0140300c014a02004000d82005843e040219811603003101c810250182d0a02000c4903d2500c0c040607590040f400301e480f1042c170a1820b03440489072000c4084030703489076080482c00d10302c5c0510711003e0040f400e00e1000a2505d40241c00c141252030082c58681d2030603c4402c680350600e0101e0705841c02582c0820000f20803820204880410300108900600310a0501c0b9001040c4041c054007070202c00301c001c507840301005a80e0304051071000c6506105413440c50b003286400150509081c20000c0c00da00100002a154020080c094009583d0300d41503140c041900211403550f41311306d410301c00542d0303074440012904103070f803001d54040d40c01c43d5603440340c084035a400210138055a4220bc1c906c07002c5040101304a40c101e1044aa030040300791042521640ca15141e94140400c291046030103501303100030040408001388011007500c0c0c080700e404 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 766095944 1250 766094694 766094713
    0x40503180f060415110106090e0c04051005010f031103070807080a062427171617030702120d11030327030c031602120307050a060e12040f08 62
    0x81c100d60018074250000b604000a03c200310801d00c490f084291207040c40841142561401400c482e0103034030100c4425640c41c03071072009140a02110324007500c12241400b1030304080e108071744945050720685040c800405030002d54030707001e5049494030309440d0038803e440740b90481014103072200c05c641110009a80d980000c0900100e440b40380156000d1031022a61f032000c040d2602d40108100101c7ca0500c41680e040c0c0000c0c124a40c0c007040b400303564200210480c6e281400b01c1a40c52480034082c002c6800c4030050252202101702034000300e58041040c04c2441d40a0a8280e06611800901035007100b880c18408a0722200001d08041c5080e0f26034030300603545140310a994803808103507042c009412501e5201d0780621100380140026070f81100580c1d03d414280103445146030b01c01400e045030f400b0200f58000a51800c140ca11014015a502070340c81c028040c0d0310300d5140c0031441c10003405203036100c8a001210104010400c0154920f0588139030300c644030700c1ca441d0624030307500c126201445040200d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 766097194 1250 766095944 766095949
    0x1020d0f0905030414180103060c122a0507050601090e0d1b020913050609010b09070e1503100f06020a06060909030e090a110d0504020a050406270b0904030e0f04020f121008030304050318 82
    0x45941c05c411180404541c11070301078450021071140402280dc2003402e03c1a0000f19006000316402486e9032440081d110700d864038aa414056005004410311140b612105220b0402c4800c5802c007550480d1040d0290351100c1007407404082040c1c0180c0540700b0030303040044100056004e600c90400031104005561303911002250402c0c40e40203065045488080c203055200c0400c00515002400e40c0307076186140751607145100d00301c17085500100060788162045410f0141c2403040b0000f40c800f001044c09005407a4501606100380400401e00500300d079000200680040c0c0d20014154019170005a86c900b0105100c402802c0107443c1a071007800c1c4500d000455240510460049038a500141003586220180e403440da00021010031200307070344400d2074803040e03981c58a0300c84c400c40c4240c8803049054008010b01201080d6424828060341c81041030500000028050313034209844d0010b20007250761200300d80c03088103905c1d5100ca64248408000d101c10000c012000d049000042c004032444410b04104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 766098444 1250 766097194 766097201
    0x4060b0f0f04020d02190c0c1508070e0f0603011e0b120c0d0b030a21080c09040b01171810060e04020f2101020d0f0905030414180103060c12 62
    0x403040d520000a0808400604140c0c010300144108a18010300f000505c0282ca207502d48800488800100045a00020442c1440100000d44074000050740e91000c0709101402c005e0002c3c2111040c0b100b80e0070003071400e580d00410001d138680003a000303545950f0745070300e02c90b1160800320f511b44850016000100d868a252802c0d0341f4000444401e003604d60301c1c1c220b07001889a10241d051150700d40c5a8012015584081110a200a1084000b6507140c14401d94800c0d0021000e45580c080041c0e007014003d991000c041555021a0304440c000b41d4103c0c50b00042c0c078104008007c140a14084030304100003940c0f0b1503900a00340e4520015100c0c09070020a0403c1164402d0080e40c6c48446184d01050140c00c10810752221020090038002c0101c080403103141400c50b01c110280e030641c1d0000f81d5445001e4480c042c50074042e50f5160305000c07003d030135035405032a030007240101c0c01d071071800f000201800da50382003400c4034a210354400c203407403540c4030706145002d802c0c0d640c01d8001040002c1d1402050050034030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 766099694 1250 766098444 766098469
    0xc1d030f1203060a030b0f040b06010c020a0501050c0109140d0318200d150e16050a09020a05040b0310080622061a06120a061401140c010f020a0804060b 67
    0x90900c80481c41d031031124640000d00a550411000c140100c0010381c0940090700662070a4510302c404e1502d8900110110802030140341080240040200180c90f0305004400303440d400d00301103442c1c905031081d0f540104265440a050f80004000300080302c200803034904050306a9582c14080d040359140e8084040b045228010102c14020010583c01c481010200c5000403004102483c205919110f500d03a01600001840506640e004410500c80082007841c0c00c0b1412140140c1e4910326000c0010750007241841001c0b44030760001903036201903205004490140c84000f141548a00b0304056903180c50b05a40106012403154101242d140a84144a602c0342050150000c4800030683d41d94000742c200c0c85071891554824140c00d81c515600c0c00050034101c0030340c441c0c0e060744d883c109624201b61a0554040604840000342411450340e01090600040d240c0303500d4280d07681c2d40d5042c42c0d401801801680c0e804103101182c540c0d0308a41c444038040c0100d000b01d80912401c85000c04110368064403e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 766100944 1250 766099694 766099723
    0x40e0c1e0f0d050d032c01020a170105010f0c0c050901080a05010c1734030f06090204030809010f020c03100e0c010e0307290f0403030f0c05100504050c040c1d03 71
    0x4541004d145d12a4002172891001c3c00141d10100020713450010b042c002410052000342d40108000280390751040340220580750303c02031a18603514020010700341400c0e41581c0d03003c0040c6041424140002d25054400030403002c1c4c202c214660f03680005031f4454141003800c9815508100041c5c80103440703075098034440c408081c0c40301d4140e12501040c40084448030740d20b03021002d1500120464001d001c13800c0c48500e509850128500e81090008001c81358103400c01a0349910501050020032013a0707054030044e15003130030411020300f06107406a1030640f40c0d06029915208004007544140d9090700b0091110980d8021201c00305100c17001502c140c2d240312030040d015400f4a00800050b0322098907000040f9511015551809900322104a660300000e03200e40240000a010070816600c1030030b03a0008106464007810215966070381d00e45406842802c1c3c02c0e04c3e9200e501050a00406110746040c0c807000a10070814551000009080c00c00710040844000010b525849003d05000c04c2e141c8107a102d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 766102194 1250 766100944 766100953
    0x21020309120307020f070e09070b0705032a010504030302070b01080606010c03050307031401080d090e0f0f0a0f0f0914120304171c0b0415030b06040e0c1e0f0d05 71
    0x49032107000041d04020040d0302180b140340d02c50700f60f8a0081c03040c1006052040400074651a1180c0c196150001300d500440800303404002c00b402003078000c0180d440892408400700d10036180c0c000c9404070b14103590340d00e91280d480d01c41848101a01036000b00202c903c1580c20a04d00d0b0ba841d11110388446d81114030a0201302103100c10340000b44114019a804481801d0000d10210038403413003090100c09030026100307070740641d0030580d2443e044000403008020455240110b89400c8000000d4084050011600ca44640010413005801600040e01d107100704001002003207030080101c0d0251400c4041980c0161034400b00d10031405001c0741d01e0300d072598100c07645880c6883d40e0f910101c0842d48000711890084051200061640c118808456428400100800c4d4140700c04100001c5603030007601d01e00001d4400d0f90800010350076044c4250300200448000441d2000c43d40e14600700403800a1030341c0d00001c0c07245080d44003202d00c004031741402401d1f20512480c84c001c1041c44407418800308007070480c1d4070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 766103444 1250 766102194 766102213
    0x406050a050603074401080c03121617031b0306010c0206160506010f170610091e020316031802030a0f050c03030d0b0907021f0911060a21020309 64
    0x303180c001e10b00c0e006841d42030103140b11840c2d06030b480d11480e01050302106000140c44185910341707040340d015041690103882103200301c000003a980c000060b2000c684110104101001c03100601407004050380006404440110180507402598000c88a2007069400c841c00520005c100005803403040074103848003a4165426001c00c0501d4102118000c4c80803040032200c8000780c0184900341c02801b9030215841882d0525055440c4001c2e1140291400d6002030200700c0b0b161003808440b0115a0112000501c0760320020340700d80c1540303c0b00c000c8000c0c14000401d102c1003d240125007044100345580800c00d07801400ca001400c070001d035501a6159001142c45004500c07000203510b410ba114000715150220810b0100e41150000d001c6100002c0d81d50b5290701c940c3c01e1030ba01e4960f01511074805403000c1c1e44400c500d40401d03480f0301c1010091036990020b03902040b101041c1c082c6281e400920390b03074a85286c0c000c01400c18242e40c02501881c2ea81040c4415524201c3c0203483c018441e05020380404103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 766104694 1250 766103444 766103447
    0x41d0103120c060216030806010912050312190e1b0a03020a03140721061109030d0f11010213210b0103110d02060d09030f0f080105130b030d020604020406050a05060307 74
    0x24020041a56404c0e400c000c400040f201c4107a8043c000c07403081d1034865440c41e1180015252001030703840303241030342c0e201980b0400080c4044120369401641844403032964175803007100c003503900e90b44c1601d5822901e403080240d103904000039960900381c0c00b041c0311400c8002d20303018042c000310075110094000d040b286050002408050000b0311101c0c80f00c04858581c0d94421610f00e417520616104450b80031800c080da000c0c000c460082c82c040c001c10002c95480e00920a01080d580c505c548415020030204503020301c1c80d18450003144c1c2c02e034072000b8000d40d1a00c071815014451503c2030f00c80c0805541c02d0441d10381110b10740b440702242280e0464000300340c42e0318644804002d46004402c280d80b2500b48102000146d07034a801a01000c20013183c00240c0384560303d005029409140035510a00c8214120507031610b6004d242e550542d0019200c02482c42c0d10248010702821620304c00f540e01d40161034030300c2c0e0031550002e4400c0c483d500885050081a503282d09000d01642ca43c042c003038020760104000381d1060f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 766105944 1250 766104694 766104707
    0x6080d0210020c150f090106060c150506040b03070905090f0622110909030a03050609060d03031112040312060902040509060607140d050c0c03150115021f02041d010312 74
    0x20703e06000d0f00d00d000b06000580940030340441d100c40ca040151018400000d07805d206200c0601a03e040c07022854645860340c2a4040040907607601c0c080c0c54500091083e00d139070b006031005002c0581180c01e40c40e181d0442c0c5000e040105c41c8107101e4416403070340d100003550004015024205014100d07809c00203604060060101c400010780300b40b41510b81c80c007090340700c500c03190340b00311812000703107460701e0703032032400400b6100c02400291240c080b0b50107110540c1da5aa80a00302641c0c9401c0000c4e884a416800c101c41c1d0042d001a006142c5c1c40000700408e146d049104401c0000004a0811029844100b10380c201d010b24004c1a411180003400142d560401d03400500c825070060034002c0050700e0000c6034614000020303000c4000071341c0c0451000d406c001c003040f20380031085040b00545201a0419513240d4040814850301800d83e060030f2150400500038403105d02d620384400d02c240c5042e00c940424501940c030911418100c11a40c49022140c4100050402d059951040d8080040c1a4214007100d15 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 766107194 1250 766105944 766105957
    0xb0c060a180209070905060403080d0b0a141002010e0118021f080c0c1e011e0504080901030209180106030903080105060a0225080f06040201090b04080a02040207060603060e0c0406080d021002 84
    0xe00c1107115000c030346c503610100038000440c80740c2081c0da074840b0300c12510400d540d010098a8050a5019010b0020f101c0113020480b914405484105081555a8049003d0690134000c0c0d885940303825401151420310303003002404940295004400c0e2801d078840c45801c091442d00c5180068501404a80c02d209107400400c42c1a0801e82101c1f404c4090410507510403031800380c0c2100503903646103140d01020a40301c0c3c0364201021413100f04950302d461f85402c80380303104101405042590000d4001c07401e03550f010701c40f0126a203048410720b6035a11401d028004200c924010b03004119880e0000549242440031200145c2e0554041d1007482581e503880103582e00804411b4200702c40d64440460349210402402c0c43c05c0440b00020046400d10b0300015103803592641140b85003000401044c40588000110b04410544c1502d005a0350030403410280028820342d08000c003414108403041c3c81e0888001122181e00344205d07420030541d9615a0b09030b030388411f005489809038011020214a00d136040c1e024150 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 766108444 1250 766107194 766107197
    0xf060f2703150603061b021e03070f0c060201050a020c1011222102030a030503150d0503031504021603120608010e0616140702120a050303010b0c060a18020907 70
    0x5915880c1d50382c00064420000300868900c1d81e4040c02c00c11703c21640a0001403074580c20101102007404040252201030310061205201000480700d00c8055040045890003a08880001c0c0c0b01d6003d0f180507039415085102e00c40040d0f090502040b54103810b403003101c118050400040940d048007104035806012000080d081206083c44010a9410483c801d075a6281049880c0312560b4200401e50200c4046645800c2d03000d400505441c00580b800510505d0140c2c05041058581c0e4400402070090200f00c40e046da04034000c040d01008001c00040030b180105c1249101d03414420011003800308a0207042041c09043c002d9282c5a0302081c01141800f41c48441d80b00c010032200c0d10f412040c0e0035289421100200c90740070714100954890a182e001d0348040182c6800c810741030050b042d01e03d4031300940398040c0c8a4940b82d9130306080c1000400811b0101035010341500d0700c969560032402156007003014000308900991001601d0701030f0912649040215a4080b2500c00c00ca64017071000e07014004000a0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 766109694 1250 766108444 766108517
    0x6030109060f0603230d050c0a05031c050a091509080d0501031a0109021c1a0a08100e06090a030e032407030f1b0e03070b130f060f 58
    0x40403603064001e1080a030301000000c1001c42c40c51628014180284030391581c148081411091400c2020176921080d0300da5147c21602c580241c40c071a800c1142c1000003c00c00d11001078401821030352100b010f4180310029108002079540c0341c40d004140c1d44203c0e40101481c0d095041d5412891140d44040c0300d5030f008804113030400040030800400c0b140280c00a641c3c040300040c16a131010f440d504c8240c050b040080d015030401003003400c2e000184407071281440485441c0c0411404140703a680568881e410014068030400766a228104c4d01ca0030004448000a4100180c1d01c282c503200103001d81c06410480020b20106e802034500310303119419145090b526020b5203d90400022441044141148480f01460000e080c21032000d0200d55a5049042c440d900301740d440701c0c1141804210342030000e4682410680c4240e0500005d04000c015080018111030209180740840e0884503140d060740d11003640902c0a50310b44605450600f0071030508000a0240d6180000c0d48410400300708500b0059500b10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 766110944 1250 766109694 766109711
    0x10504021f0e09040809030f16090b0d081801021b060d0c03110417060f0f1504020d360f030c0f0209090d020607090518040507080f0a0c080c1305060301 67
    0xd880d00209441c1a90780c0700c1c006c211036069180500c031003802e20004100401c0300c20407550040c10440c07110312424074515501c118200403130f03c2d9452a000016400b0034106d03612074090035010312149a4000d41c0380103100d018901d40b07901c090b0b802e000403000310051200e030510034802c40c400d01031301000300c05000305034549403c03407407042c0d403480544080d02c104009201080b03c1004600e1900358000d04c4040d241070f1090600c80f520b1441104d0641110034030f610ba41c03406440c1004900640f01d10003403000000d280c83c603e041134800d50100e50b8249610b20002c0e01d0f480c04460800e00064285410280c45182c000d41c0100019004841680c1d80034800c00e007000412090350002080c0040842d100c174a150440311084446940c1803240c44c0c0c2c09034840c20540151400c020120300c103c94803501a03035851021074042018008104025002403040c0d00840310350b01030007440c554480b4620b070000c5900e080000303004a011200030a07008002c1c200034041c0301c0c0c0219110842d0b806000040c1c006a010f540e00d1802 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 766112194 1250 766110944 766110949
    0x50a030b13080a0f02010506061207030504020102150907080f1519060b04060806010e1008061c0605040503120a0b01050f07081207090f0b04181515030c0809010504021f0e 75
    0x10f041070301c1c281d0b140c2250400407030501130709441008000328422101080750f10341e2140e042502ca0f801901d80d2a00007110f645605c01070746001003042e40c0015402d6035800308070750f02600080a0b800d89030170740261410380740000704a541da1a8591807140d8450922000616401d04c00c04e24001413580242011403081d96560080c1070581c099040400022051420003110b075070004860340003003c0985214020105450005000c114080d02652241203003c6031019400d1483c000701c1038075608200b0410460400f8544581d40c2d5006400302c4101d445864009510414188a03a9009001c1038440a00e0850030102d0b0341280d078401348c000c0307811000911841824090083c105885114540c03100e111041c00e20020884100c09944a002c2410040200740124404440c205104591010b40030407068802945500c0002040d000b8983c030b21300b00e40145010fa98590415030700c0e94155100d09002ea11504c00c81c2d4282d038011100a900813003286030b0004411a800c0030110886102e1a20209241c1507200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 766113444 1250 766112194 766112197
    0xd0615090c09050a12021f0507080408150612071a0f0307030b0f150717071707020112060b09010f05130603020c011103100e0604020f0c150105030304050a030b1308 72
    0xd42400180c8408043c001803c00041c14801780c20340149845000038103a0010340c0a03ca07912100800c020a410131414a038091019204000da005540903121034807400302556901c040d0740507118540c0c064001c21002e040082d03040389441c6d0701002504440d4240207203000c5815030001445c9071b5400800c880d0b0303d200542b80c00707140950f04c15075000c5403001c4100d04121407154070b2079160344200c80120205451002c020120340c945940b1248440540548444809050060b184003402604001080320380e2407504c00c0007400c005100f40c0b1000c0c045d030420070000088840394000c40f0b040110400c42030311150700413807020b4440c0041e40340440c80c006200d1900b0751808041cad4042008207402140c1e10040071428010004a5200703112030606501d01030a5103c0001d1083c031943c4411484840411601d03221030f01200c4042c80d041e440035566032242452507541d080c07500207101c14403141390000308092601104850440310300803c41042c030b41c155115090300c031002600803921f8a594122810000b0b10400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 766114694 1250 766113444 766113461
    0x112031d062b05090309010c060e010e0604140c060d021b07060905030717060105010c06270203010b0a0303020d05090f0d050a0b0a1b030b0105120a05090c0d020d061509 74
    0x40754007944400041c0094011100b03410303581c042d82810200f200074000001550340012003440c014021441a080440040a401c000d101581d401e00b4607490042030700096050045c1d1088003245c6030130030a080555210311b01048007582c005070800150143e12401d401805410241c540d6210012450410580c0b610110381d000700f02056212404109a250501040d0300806820780c0c920160040c07242802e4a403501400317441e046c000c0781d001c00c0d0b0620005a00c000180c0c5036601030301b0300005051220b0074410300c442c5d1040f0720a600b0404111494180417915100b100d40c9278004041144c2000c50540f00c6400481000f60042c200c034410b0740c490f64903843c086070128001c00252400c22500d0600070340070704000f04000811800e008585052000b1540e01da841c180e800d203000078900c110030780102c038a44a13515026140540740d605000202036180d11080c0240c5002c0110741c00002020300340000703c185160065480611071000c8404105942c010804515802c101081216240d28442c022210480c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 766115944 1250 766114694 766114717
    0x70c060807120f1d07050a032a0f030c0603021305040e10050f04061506020304030602071a0412030507090b070b270723210709060612050601080112031d06 68
    0x3060528a06500c084a0000b43c0e154240540000d07424000807420147e1280310040900304000c00c0400c240a004180282894491011400203665010f410340c0d018801c0c0400d9400c0400b000b0001a03441c060310803185510440d9151403802da00e040c007000002c0c860116038070b5040c000e000607150702c0c4030b40d4450240f0a41c1e40c42c14002140c1000d00b080d00498149034940d00d4148001c410a0010070340000070343e41280d03403140780560f5840301860500c8401c224402c40c3d40076450420240000c02c0f150720300e540c8040340303581c1c0c0c10403c40e502c031001122180c1c3c46101d002d280e5070301000221701089407111480da22544102d20810f185603610b425940740c0c012110b10448980100c41e00b4404a240f5110102c410075000240c2c440d031030280c20002e900f4017608040928421801c0308820703680e2030180f0444006100e51002040300b10340d80d50014090148030410120150303d031000090702d9600075a0194181c0b0007502410b10425a0f955041d9000000764040000002000508140b155200c0f0010700201d0040c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 766117194 1250 766115944 766115951
    0x1101020f0d110a12050907051002030a02161401051e0a11010b090c030c070f14070305060c0705120a0e0402042c060f100513090b030f03070c060807120f 67
    0x165598821600c0260103500e1124040004020a60348491500700d448140c4d8400151501c5014440307180c8812940700c03d800954008400380010740110140039280000c0d000d680e011283c110f00300801c07031410702804150021344100c0070000e500c58400390590103c82c00540503c0382030034801c000e07a43c00455905d000160045440d481040007030040c0c0d402d609090356a070300a41400c08a40856000003440ca40c01203d0105241c07090283c802001906a50000c01780090003004507003545d120b403900d000c1900c031486054041070b11000c11b80103c404d2039030408003500c400007040d1103268480d03100460788020007041200042c0d59070740e144020300081100030048030713081d800c54050548540c0d03040001c1c90342c60100001c004050705c0362200000d95a40444000369004401d0006480794014556400c29008401c800860300e62500c1d4803d001400046048404c0702c0c1003c99000c2c2d4a20460400603c0361800d11400c010f09409180c440d034220016017090f034503041c0340c0c14a4404613031900501c0702c801c2e83c8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 766118444 1250 766117194 766117207
    0xa031b050f070b0705250608191a040c020a0209060108090f0328051e090a030b240a0303140d02090d050a02090a02090f300a03080708090c101101020f 66
    0x45c10071070800440405c800c1c003500e80510303190010044035035209050601903124002940340f50701041030207410703e44640030000d132a6203c4000e141c010078003000c40d000318034005075034500500000790f020906a0050044850340c0d5040c0044550700409491031200b40f00300392141c09020000d00282c00300346580c45500030101456030030442121500d01daa10240403080069075200041e194030002031b840318600c40d6548200042c0131410381411fa40c0003906008040c001c0c007208581a101c039050306040744c0007144a480d061800c2040c2c140c1680301c01008100341303114031445015024003816101d02900760050400c00d02c1d40106102c6c2c0440c5c1d10131a45900442502401c518091b400c1603000b0800b02c004500345a0840081051007080c2c0021611811444058224a18403440303910a9089110781c12205210740d03880c510343c0d441d250b80044011800d01c8002030b10007489000780502c2407c5081c0203016522008080c0b090b108000d00d0410100903032000b00f40c0e030051090004100c01150116119917a00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 766119694 1250 766118444 766118453
    0xc0c0f120d020a1b050d112407210516030c0c1e0e0c090d05030d060e0f060316030308041a10090509070f031b0f0b03180a031b050f070b07 61
    0x20700700380c01100660b62100c148410384450308407002143d40800d06540b050358032000038011842400004100301024050f440d003081c8c02d800a4038015109541c5505602e4921500200e000f0504622000052051207000712155000603034207045400380c18194a00c04e0543c5801c0046540c91300910300c00c2c441140b05981c000c2241f4410002401d00902c00314503810316001c500703114450026001d01c10710b407042c542001e0100c00c7c0b04440c0310f601a88410042190358941403650428112030000d81c030510100000c80d5410302081c81c400d520341c071220855040742587d500b920002c402801c2a140c40704a501840034244c04041582c3c05056460414181245003518120030394900800003009070304404010022500f01c9130840c0e0960b94000d8242ea05e603518001c00c4000d100695000417508061280c0c001080110400114000c4000c1446031002041d1039081ba5600e940c45500100001c4100d4015181440c000b149010242c1c42034003660003240204500324904003042c0c000c0010b01000155210400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 766120944 1250 766119694 766119713
    0x8090d2307030206040b0a02120a031e06030b0a052a0d0605010504030803010e0601020f0a150b060c0a080a0c051006080d0c030f030213050d120305010b0c0c0f120d020a 74
    0x302100c0d0300404055003180c2c0803030414082c0744244107003844003013400420365000303000017030400645050407611000f03a42e000a0240c030b010091001415104000d06030507850070300406050b660080510f0406440780850100180780050080c41c10441312803c0b0384440054400f00390000c3c440d0900d49441c0d1807444081c00445000364449414408100405c00c00680c460054904403000140d400031a65113030300041c1d0a0080440c8103002030700419030304070304000c04900c15120000522100f000201d402d00140640c6102c1c900b40101c5035032191a07942c000405007070041c000150305180c504045296540c3d03440c9410800c50400e40d0325501c0b080e051060110402013061080b20760718042e0b1200e4243d1b00c0c003802c920509899a410150006024203c4042c031038040c10043c403001e440080c141d5100e00b081510f0031a80074450000074181400010704541d20010740d41003650031400340c61522800c0301000a07803d5220899030704000035034146094001f00f0711840a4008003900640348510b80c6241590300c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 766122194 1250 766120944 766121003
    0x70f05040b13080607020a0b0a0b0406030b01091401050609011d130e0609010e19030e031f0c0f02030c100f15121106042103031b230705150408090d 65
    0x45601c0451f811002c00c50b03181280740c1021151000065494040f0081070203803d00390000303411020755100010317250549600050034050359648840d183e988a004103d890301c225403a080c001512690031007004c00c45c501e440111403a00904920000c0c800310448001e56402d030100f60040c1d08901d04000240ca828001d5900700074050000c4e188088800c91685151042c644000e401c10000d61200003071394900300b10011113a091182010308000705c1d01501c0020341104031400300040c01c9586814201800001901c07800c41c005400383c04989840c41c0c0b01c000401c12811441850b0fa1070b489001c03080440540090064170584420102c003401600300108004401400d1a0080c4020071040020074488030f4424a01100d410b9002d002d41c2c40c50a0071000f40038a104081e481c0841d0b03085030786031550403c281501c456000210f80720079034012040200f9a01580c2005440c980054419a549400c0c100c4500d61291091407210b040000303c1020480b4056560421200c400c05413148001f03105131813102580 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 766123444 1250 766122194 766122197
    0x20c03010f150504090c180e0313140904050714030a1202030903060c0403020919090203101505061908040804150e010305090a0f0335060423070f05040b13080607 71
    0x3c2e0041b640d401800d04802c4c46070041c4101d005520030840c40c1e55800900c2c80d0140d60049a03100e5180c440c0542010410b88902281c080c0610300d110030700d091890701203120b00d4010003e0030703c203490b0090907101c1220305041176505025804404000480c0d0740e40c00c1c100b0300d240f40d00079174591610405061500601510242130900d0072b02c0100b0050b60b070748840942c003000411131041e6403414805d1400c058260210300a6040c010b0980041510a039940061691604540c40741e96081d070324018851035100d001c0058440e10500307120010014046c0800d950014402c03802e907442d007555803070105540d0299011800000c2c2d031807002d4401c19070b8140601034010f0700b202c0181031194119a1688142c2c102c688d001000e020600c190564400000c2c9412036901c41145944102e080c812507104071461400c07a680d510591400544d040d000007459030005100c44010410170070f5884050081d68120854914031081000400021408034480c20181007101403500c518002c0b0f038240310015049c0140100080c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 766124694 1250 766123444 766123451
    0x6011206260127060b04090204020705060406110a0504050d022202030130020906040b04020a0206010512010e0604141e0a03020f06060102100905030f1b0106090515060a020c03010f150504 82
    0x1a1040c101030711080000d134010f000066842588000c6009480c0342d020107907010348041902c0c42446000b0541e18803443c8110802c12450000703c0e0f103250540103100507800001c5c1c1c2031109024504080071070400c140d0005100448400c0d0241940001c901c501130a244029004001000034041001703024002c0b24101340800c0840c0001c07a4482c480501402010b481518803801148554489038400303044001c02404c2550b495018000107076440400380320751401130042c000410070180043c030403040011a4040a0840c41c0c1340d58855a07414030f41c84d00e043c2460300130034410620810b4100f211190b428002c8003d00f00303101c03003800c001c8d0620754403400d1031030690000c00400209070f0340481e50104490400c0800501441c0c40d040c2280f450055a4040e52070010006800101c0303180d014028100c40c010070001d03c40d182c0c0b42c0c21881c0c00e41d103040e00c007010f1864000e0321000a80c50003101511080d8503500c102e6070f00a40100010742990302c1c41041c0700100c0d0b40c0c0e10301007030b6401468240e0400707850107590030b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 766125944 1250 766124694 766124741
    0x409140712082a0d020102120f0c2b061215050c09060705070f06171302031506040905062703040e13080c03030c04090c0e09060112062601 61
    0xc0c86501c143c03501c18000d2186800c4003500000c0030100010704480a2040390041041250b000e4002d600424a803220b00c400783c40003900f0814100700441c426031111484c241803801d0004d030254030504886441c4075524a5065803824000d00344507400c0102812600306080c3c0030a8144900130062034500c0018043c10f2408200307041d2044411142014000d6900c50b558403158209681000100d81002e1811070959100042c0150f001c88050403055400d01ea13820716407285001c3d0001d904040e50000e4264101c178020000b50203401506030f5010703402410200c2c184015a03151424100220741510f003101d03651400808001922800004460288008600d014181031a4030b1000c000141031003540145a95000204002d580649403a42170f1f0b041101d4603401c180d0000f90719900180101180f0ba85090b80d03400909100350380000b1444000b5100d4801070300c3d920011940c0844c0f20031500080c80d240d03032000914103a800589001080284c40c3e00b03006401d018105800e448402081e104000901e03103e2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 766127194 1250 766125944 766125953
    0x705120906060f030c0f100c0507030803091608070501050307050903061915030f0807050a0507080606040b150d0902031c020a02040c110d2604060c080708011d0a02090409140712 78
    0x6c440344814100c42680e1410909217040321480c002900081041c0a07500c0c0c0002040740c0c20010b140104d0807681541e9a080d001d208890f00e1009a1007420209c0d8071a003820060365028800035038001d8510310b0b04502c0d0115560201e483d08609807881151984400002e4001c101544151004c1174001161201183d02d5500c0c0c5285890403114007030704418000a07070201304102042202c40455100d02950001c07070f6102c0d01070762181d000701c5200340500d052541124081c40c0c2940800b9115002c11200c40c20400580b0920006100383c2070300302d070588216240c00c4140904e80500418100c1d0b00d40c0101070444991052000351158520360205009042c51102001000407650216140c52841d0010240c1c640c2400300c2c40c00000d010b031142941c1a04e40033700c0180078068122007480b03841d039200c980d21920340d0141120711560074400c0c0c12440d0003551074003d0280d44103c00d1500705d00c0c203000140c00c140014001500b00c030306e519011110000c00c02c1d029030351040f017448210003c01900c40030340d80694407a20b4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 766128444 1250 766127194 766127209
    0x5070611130501051605070608040b0105060a2c030613060e030a020316030207270e0c010219020a0504020a031b0905060313051e0d02100605060d02030705120906060f030c 75
    0xc1d0b1070602502090504d410041107400403045034103d03040b00d081503590480503100010680d01070f680ca454210000c1154206034003203a41c000820f5503012407c10286009400c0c5da04a4a0030041c0802001034000c00390b41c007002254003d4107400040255142a4607140c402c03144032051001e290f8005000040c50b40d60040190350b640d00c905001c0e5000b418052904070704068098000d100c010461744048a00d003060b1b01001c0342c10b40710400c420060715504030380340c0d41d50b10f9a519a0074016400480361086000150b4080d03100c851001e4142452582c403a400542aa0041c41402c3c002070b82c0c031134442c0085114000030301d481c000340e4200301d0403040c104400304500b07201c010088561304283c0d4218108106041019101405660408140d00700700ca621003034641207000c0590005206403031a02030104010b22030601201c0c0014160740c07404103138000c0030020390001404d52040c40f0040c0001007048042c0c00f40b907403103080102c0241c1072500d00301c42004010100002c12034002d901807501144503459030070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 766129694 1250 766128444 766128449
    0xa151a0a060507021c030c02150c0606060f070501050a0207022103030703090f0503032509060e0411040b1810090e270d020a1a0601021b0a03020a03030507061113 71
    0x18040c3e030b40e524180041101d00e000d51382d004152060706074541007403607400354045a2181c801c881c01981d1400c1d001d440380f924000d15141844580200011030046d01c1c004000300003125a81a2441c00c1c40c4160300c1d82d03403c440d011070340d0411042c0c00142240851800a40c480f907110703030708e960030086142c0310006641d0301d01000302a001456520345000c400c0c0810070400700d0b07000d503208040f684c1d40c0c40c0c01144000b12640582c6c07440c0c88103200d100c1501c103450091070088242c64095a42c404c8004a0004001c050704c03144c480400b9022042101041c40c103000002843c0346a4440f0301c02c045501c43c0c07814020600200c0503d80c040040030003040c44041850182650091800c0a60342c2103503021407010040726a10708440855441220320002003a600800d0460009001d1b0514502400710a02c001c000c003e03045a0150050b0070405038203d01281b907407420b43c0081001307080c414039261a5408900392101c0c540080c0c0c0441d40105004c804c0144c030740144000780450181040c10600e0a40d11041c200c101c50 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 766130944 1250 766129694 766129697
    0x1020c06010e090c091f0503010c050a05070206090a0b040602100501050105180f060a090504180209160c120306032a090c18090e0d03020a090509090f0a151a0a06 71
    0x80003191240703d0412018894990042c42001a420815000e101ca0f0140c4003140c0c0b00014116000030302890103118044245081e51070b010301e403e0201c00f044803aa413214904030381c031080074440d10681d40c0f2000d42c9080905800500c0560715410032001a1805407a8041081560b051400500c06a644001a1071200e003041408107009505040090340688640c0b0780f058005c035010072646080340d03004c901030341110800c1c1d90801c590b00310040c082d180b40c058180c01035049103071240840c0c0300c400c044c68460381c182c803146046038405200c4e559a000068114075030500090311080e0a0090104866054014211f001028011030f09440c22520343c8180da8400d414070107540e045d1170301e401c41c01454401b00d81e414180f0b440d40030301c7e03e82e19908018218a144004103201d1401280c3d0701601174800c03111503005544480c0c100030701d440100001060000c1154015000d0b01c0041034220104120301c0c3d114501c2542d4410300d600c00c50204104030f801050b9290000c2d114800c12400903200d50a1420640d0040e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 766132194 1250 766130944 766130969
    0x20301031a07030f0515010f0903050c090414150a0c020606030a080d15080a06060f0e0c0703090902211b1c02070807050c0102070e010b0313031404091b0201020c0601 73
    0xb28070050300240080741041030180d04140421030740c0d0480c4911002c0b1404240c84980b0240c1c0c5604003210403481a000050055001640469441c540401c0303046e4081e10514100d2400b01d2146002d5040070300d07010001403010301003c140f0070028030340d0040149040503803006082034070b450000242d45400d410f2000e880480001340440d90408543c1205040700403440b60300c540030b0355540449640b0050744005a43c07091902002041c4080010800c500b01c40108400c40030b40c0c1c0760000c0d201825440803100b101441000480001d030301c1c6c0d290006c0c1034104038131003400d111240100780101c50708100914401200748101c100e0220014040c080c2d0f8000c041101140080c084407088100092043c1c00d0b010705078038004121036040000004000719544402e900b621141644c030410f602241100b8050122105024030000e05021400d048444201e80286413141d0085002101c20b142039200d900410078a0b81c581104406001d14403c1c18280c059161008501d0041034100140c0c45142c1070007041d180c1d084 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 766133444 1250 766132194 766132201
    0x70305040503160302030c060c0301060c031d0a03061a1210150f030507030309050a0506040b030a06090f02180f03031e040b03070302030f090a0c260111070213020301031a 75
    0xc0401c103460100416a0012100500906000e0751b02e810031804410144200b030700143d800d1460038290b0341294066280e44524400540e02510444034010006600c05400030704074100d40d80b10004400110b014a10024225422503100c646034075050031101e0062010324040a02c0f440001903c0040380f810356030006000c484c000211403140c8950f4085541500c94080200a010300801d02c1021207110f80c5580e8007080d6220181701a91105d48209944820140f1080041c6101c1e0402076500160282c000983c3c103032140000da00b00d4842040428880ea03003c50fa04180304a2030180902183e411a4032600b0340001c500003995034405c0c02d81c1c090041d418092548a10000e600c05c0d900030700304000200b5200c2c03503c000010001e42084642e075201c21402c0000c40c20403500412240345881d00202c92a40380307400e119006100711000480c20385801d646803005e650b004170a110300500b0000300e04425a031002c440c010095003d0b03080364000001881040104005540e0398440d4a41d12541c5020401686c1c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 766134694 1250 766133444 766133453
    0xf0402241e0706020c01020c1b0d060f150603060612090b3c0a2427090c060f051305040c21050603060c0f1606020f041203141207030504 60
    0x840b4070081980340049100d480c514419000b0b002084001403ca0b03504c44c2d5031150b115014450949121303000301c900240304001c241280c00010700c1010100c0c011848100100303148109090365400000000d9540c1414091140e20803c0d610030341c0c966030403d018448254580d038420b0040684030105204221589490205191918040c26645200113804840484180350300c0c0c0e000c101c44170500f041c036240d42c010b01c9210140010082108800076424010704280f03081e6a01d40e03084040140c552070032014001500304c940244e684007846041c558805030b1070140090241d01d1409894400d0000902802640d08101003584080b40d80880307020030145020721044c0d851a43c2d100d031300b640341c08200b8803844280c52590003d500034042502104c5007a59140e400b60f00358000c40c2801030b00044100800c01c1c181d1030104040320001e0041200501c2c0c0680701e9040601544594800d0705c0d1911a0405601455003040498016034505500c26141403420110740d100ca010040c240713014165194003103410310 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 766135944 1250 766134694 766134697
    0xe150901140403030507170307051903061205010e10020906190903170c1c02251e0905070311160609061e110a091a120f0402241e 57
    0x1081d10500040c1d80e607440e414000c025521002056490000c00c3c00d0b40c124205803042120b03c01c10181e80c0303050510701c07001d0b400708000030130f200c41204040e2030b90008125445d090400d50f011500c1a070000a01005c10030110303003411640207104001038414446448141c0382c5030102d03404809284218a821003042c10180c1e2240d110380c0003e415041008422203400381000018402c049070542180c00c081d080c5140e50341c20004490840005805c84040c001d004e20a141c0030045400640c280d03424440e48554170340c007401c400c00880c2480c05465000412a1034000c0c07090070342212a9180034004c1c0d038500080d4000c10b109069041d142e903c4540d8140e424031103a9401151415480041807010720b4845a00c81c000c1c1d80451441e001e0a490f00e41048003102001301145d4500040b0b480d040d646600e0076580d0b0310b043c040d4050700d01c200d4a003009083e5a01108050780c070b20540440320740c8191401c250040c86000413606a6846040c480c00b407074640310b6080031043e5005400c16130b256000c0c00e10305c42801d4205 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 766137194 1250 766135944 766135967
    0xa1509030e090a201b0d2715020604030f0504030f1403091003020d0f06030b07050a2604030906020a0521040e0901050f22110d0b090f0d0e150901 64
    0x307651040e25a0401d041c6001000c5e03400002a000401c07030300c030141c02615110b0700c1c1a0000410390410f84807000c2c1952008101c03d054004041c01540ba40c2c9003501020b61103180c0314080146c0005042004058102d0a0960442150b10b0700c030781443d05503603908440200c00c150280075800c0c48050000c4440c020000c6410210010b065000b0b40d0100f98000380107500654640d140c0e5500303207010b54070100d541d80300382400c49800c80e20a181c80d8450802c1622646e01a4186508200301ca0b0484c0100741548540d40308456041c2d140c10440f40740504000b031115109401501c11074214001c0701011540000d650680a800c003080ea1480520108150a0f5032045c2c2c2e200150710700d00803040161400041d800346102d21025207082c3c002d40c1d140da2042c1001440200e21034244e101000c0702c107000c900005144103900c00c0103050104240f52985800072107503000c485002d481d901407090800003420034801451007100505040d046048624005031001c002140201c81400300071411040c540e00c6503032041d00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 766138444 1250 766137194 766137221
    0x70201180506210903090d0b04020f0901120b0f160305090c0a0e090601090b010f030506040b0d06091103010b28090227061801080a1506020a1509030e090a 68
    0x181c841041c000300703504188690b026420f18081c88001005500b000c800c607200010001e00c40b006100303850340c41c0c03c941c003006013050b81c1018001a241c00c1d40e8030b42e05d1030f403400707004015040030070b40090349031102c0f24240c020510000c4460f44400d10258650101010616241500300400d06903a6421342e14500103100400702c0e8402c0310b0340e1000603018078400302d035030081c500c0005450030741c0c7c1ca4540c218240c44054910900040e04001c4030175605c0e100358030240d0401c40042c0003007104003c2078000703000c03e0300014059400c4c80c0d44800702000c10a40b00705d20444030700241d0090080c40c100700c0c0012403002c64400c8000103581e90a0036030301602d505691150140c801c0d8036046481d00b9039824680807002c07501000312034001030260071011900c3c24038191001e1000103c00c55000d454003400464000348003038050303107a20f40c640d00700081e11452080c0c0c08000d030800341c1c0100141021410200c21b45c0c2641d80e00060168504114000401d900c9200c034080d0100903203035507045843e04d40c0b040c001444061503921 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 766139694 1250 766138444 766138447
    0x1e030603010e010f02130b0a02030415020c030312070e04060f0909020607080304050f160803040504020c0a022d0904020d08031e0c03010e010e090607110f060f1e04030203070201180506 81
    0x3401c0313480c0d02038075120364400c10415070603032100010b9055218050a00b40980d0040c04200803a4201c0c0c0b11080c005039192040e140f82145c0840401e28603080168845451a402020040703035036800542e1648015049409018941c41c00740b02c0080c2c1c0c0402c3c001ca0b40c00c0b540b28a10302c8190340b1a0003c9031141d55124149d00d503640351600301103440e2151880c0c81c0340c1c54000c0c0302d4a160340445040c3d0020581d02903001a41c80c251400007000000c1d802090034044c01c0c010842c0c180c000d41d444d202c051103800e2002c40f81c0000051140c1e6400240f60b1103508141c401c0392440e052102685684610554035980410034560703e07158540848011001b20741425500340c2290100415481c903c4090340c121821141015120390300c0d82104108914121480b140f260300c48000640c42e07920504081c01c0d104e0547d8280c035107080c4482252410984115804070700140c825081c0400140300d000007109a5080c0d0ac0d0b246210704041c3d900175100e11032600b004c2d0400c0807100135541c501041c00d04a4001b09030040145 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 766140944 1250 766139694 766139711
    0x1140a03020f0301090917030412230c0c030105060a030b0606180a030305041406071e0204060b0a02030319090f060f271b06021e0705090712060b1e030603010e01 71
    0x5d000b4208220301211894003900d0780d8120b0840c64002c0d02d025690104007010000302b01c141c02c0303920080c10984100908014241b00d19210501001041940001e20140400e040984103050a540f00a08480e000301000c030001c10104444101840d082181111100d9a41901d000720301800d05107030000591040100c076002041540220080084821401b107078003800c04144104170880c041e030300000d032590031401c03c000c80011038540982423841c401480003442c25100c0d0f402e403080360000b0241c100540d2000082c403582c01005d0703640c15104200700c0c43c14000b240340c55545240041805000612040d01d442d043c80c03c1c041075411031812190000c9403684000c14646d80c004e58248108015180700c0c441e4140585400c8407540390300255150780d002068910307464041078418041004000041d8000c1a0004c580b95481c0500310b0701411142e920010620000c90119040354100e0780702ca05601420801e0440d602c20501c0910401d0014400040d200d588100100b805080072100d240515480c00048 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 766142194 1250 766140944 766140959
    0x110a060209040e33010b030106110a05010f1a0301020c1c0927141006180f15120c0c0f0203030705100204090b030604110907020f0f1e0a0201140a03020f0301 69
    0x400f03103120104e16408a44100c03010b01070302441c080c050700400100400040c02014019240c00e0240348070841150711012454603500d0031200c1c40c40764200d500d621075440c08004100c50440300c0000008500071440c00c407501c00a130340e0381c0d05a01000c1842c12840c011000d1824000c00300328004044ce1650b2011070909004040c2040a000d010100c0d0280352203501c0c0720120442401c2c61189486000400100d81007900c20369004184103400134184022030300100344040482c4d41440103001c03a80c545031103410b8828020342400e0020032004030052500d000c411b5410791140f0b0640b2038580007107107102e00e8411400030a045200b040d1b4094454450502e850030f2025280c0c1c02001101e4500320304000078088070381055102d400c2910701510303d1a410b1140034062521004441d0807050a0040311103214103424854104075044c040701c40749170048010700d060710103210500c40071007448030003400d1189059070010304004a91320408805071408183c400e820b5029038100c515052000d40300a882e07607520b210 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 766143444 1250 766142194 766142233
    0x1020a0e09130b01032301090b070f05032e08150601090501020f071e0807030305030601170106171906030f05281401022b0606110a060209040e 63
    0x34040e0241c201800003903002940c1c8440b00100590003007042480f6440c5444c0d8502c280701d080301d0f5029264080240841d101000d200760100e20f84641111403c0d8030701444040e006d20142441401407040401c2005030960340c20a50011207842c0d0380a1640303505003078900e00000500340c1c05c50201da1040c800c940c20100c1c0c0a170364091155100b607075040c210300c1d112001261a505200320301001c690003410144840c1c001c514440c4e034240411940c5d00c1c5500c0c4e89500341c078908035265000380c01281000040c45030075640008007035042816007004104a51618a0091102a450100094001820021960618130300001da140046e0151090080580300d061188022582c00340407141440341402c07814600039a48010314440d02c036000000d0b46e0003c0c0d600e40c9540490001c01c4004155820060350701148074001510700d0540195117000348001c45400c2800c219040c0341c1211060142d00b18814980700000202c18000e20784c01400581c586040c080481c6c041c1511a90f0300c0c0f407d0081440d07995054007603c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 766144694 1250 766143444 766143467
    0x2301081b1c0c031a1014160c0608070801090614060901020c0a0b090307090e0c121906091a0105060a05090d080304080c2a09061801030803090c01021207030c1401020a 73
    0x540307400d41c00a800c2c208030303105e40c0075042580400c050042c0d0822440b4914080c18004200e10944211036409035540301851032540c110130007082280e020303c09556800440640508911081040038609040406d0f07004c1c0c40218400313100f6000001d0041c0d039a4400e200d1880e07041000390090b10100e0303c4004070b0080360000ba03541c0b802442a6807000816006034060302c4e0520a00308050b02403960b10f134042c449024580b1070b03449090700c2000030441407102c45800d100c0980340280c80000d40b4200c0c41c60203400b2000602141d0b00242c0e58600140450703980c2c00e0484040b2030560402c0d50b622100000411502d14190310041d143c0e40000c4100024000004003d206d506120b43c240c446190361800e0001a80c0001c10002e109000c0ca6580224181030102074642c01c4000280000742107000c81401400341c0c04247c008845084010040c040301c20010088245045c0c82400903114501804c18441080d005070b010240030401c000203948103210f4076403075803402d08400c0c5e00290354408841030007034112303600030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 766145944 1250 766144694 766144721
    0x6090501060e19050f01091505030a0b040b0f09060f04020d0b24040303031d010f0c02010f060b0d051302030f0a020a0b070201020303071103090a2301081b1c0c03 71
    0x1242c1d1031041c0b400b000d0244040d040242410010b9007030800b8401c3e014441c10a01d81402240500802e404020b1400d802940c1c6e02660f4490b62450040001c10503034078214a4240603c1c00c000903c0b0702544d441ca100e0012403004c1d81d204c60103544003000901c101c1c1001001a4010744001810031040d8500d8210b0040d5030025901c00d0b5948010084805540390210182041d800c5c0900c030910010b03101e17800103006001c081c80341000c500c40c1c0403001801c48503035007440c4640395622601c003292290203004e00c5c20181002c0c0d508010261034070b070140c0028805ca09403032074040d545034005030401f00c4106e91802100c1c1c0180c21200340309070706400c40390b8809401070160310452003c3d200190780da00b540708503590150706a010794190707190a075017522140d090340c4040705540014000f10890f601c42c050400004c0008028094031490f030b650340d440300681c1c150619030411900d54204040d8804d0300d070301c1c00c60b1140c81c65649a55810341c003a59481c40341c0e0855441003403908003009107510f40c0c1c1c11341042c1110f1485 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 766147194 1250 766145944 766145957
    0x14090703111204020f030f07090c030207200301111e1e030f10090603020d0b1003240b0328110627030d08010504090f050106080d110304030b06220609050106 69
    0x101d004042e0707075414001f208405940051428414045141c0140b21409124140035040c41b05030ba031740814004d10b072280c0403004404090f400e5207900d000d010300c04114054003415440c1820004030f0342c0d4445807810f038990311b184c4002000003641c04070506420704031b214048581d4403800d00741c0c04007079188000e8629803498140c5042c00301c1c036489644114801c5944c0280740e03040720308150390b6800c1c06040041c10710b0145802203100002240840c4084200d20464401008003011800c59250480310200c01c02c070b010798403600e45649400420026404c02d2501821000c0d806925440d19010900c901d180e51900b15001080c46002903290410007400303001c034406404602d400c1e050604d40e03604a14814003000407a401e00401613824540d03c04424240221603040c05190103465280c00d50f0900e42c0002042d07880070a82404190344810540e00c03000029000d5480e01d40b540e01c0d07258010360045d01c100d100d5021482d020025454031198400802400c00e4180701a5540b251220300074582440f850380441d00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 766148444 1250 766147194 766147219
    0x30d030203010b0a21060602030d0c320d0c0906031a130b030c0409050f0d081006030506060405040e06270a08030405191209050a1409070311120402 65
    0xa000703480c16560b008850741c0c10000c10550465414000426181115001d424a5010016a801258085c050035001150740d1141d8968120498252000e00410001d8107004c07042d000d0340c2e810100282c0c1802a403105010005144410140d100e40308400302403524000ca03045826030092948000c03074800c0e80301089550514240d0500b800601c0c800980d010308040d00380c00c81c41d8070550084c882c0210150031110383c1c01480021400316001a04240c2d426400841c3e104007000d020841080203030480d10f00301d04541010594a6410ba01a015000034580c403034001400540700da00035a00140b400038000e01c0b000e003009151a40b9188103840e03002c042041c66401c502c480792507403051000c01c6000002040040714030340302d041e580c0e04064030486203801908010940400460943d0301490b000f44a08544440c0347d100141461515900c030798022000110200148000040341c0c0c070320443e0903640080780b50340e41041140100011442c01d0114000840c00c0600c040b1100ea5061040d882510260b207500c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 766149694 1250 766148444 766148447
    0x121602010c1706040e03040b07060506150f16020409081b060708090703030e04020906190f0305150d1704080106090b0301020909041509020319030e01081522140105030d 74
    0x240d2070b00300500303600301e068045151030401794010300c18002d244059a007001c0c1c0700d000359111707503000002c01e45070551901d00f842158504010520050228501458a4005d08401030051405031282103100360154031030210a6440b50303040710ba08690b000c02c0301540c410a8501d9a01000300b5036205140074401c240004000301e006402aa020700c60b0a4002d000040c03a696040360001c11040704c00782c105809014000d1140c54100203018580d900340504030030307a880c03403100400d042c02d400980c204044c01c05090000d00c0c0c00b0190020381c0d5a000703a800822209840c1403040d43c400070403516410454001500048510040d031060301681c401040c180f01e10200c0b141058240d00614240e40ea00c010b4150200340040c00411030484a0b801c0440c001c40d060301c464001904101e5030b14480401908a05400020994080359a0602e0902401c02c10b0319400c4c442501080c44a00d0340c40320b8014001c3d500c60360350141000c0c0b00303440041d003a1032013840341600f03118181d454040207218041c000c0c41011603190b6604d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 766150944 1250 766149694 766149707
    0x140c1003020c0610030201080115031103070306081b011202210f090114010e1f1521051b0306040b040e0a14030a02100b01030f0e070311030c0102060a020c03121602010c 74
    0x4c0c2e40582da523040c0d03030b42400d80f605403501c50b440449060540d01c201c0041c0034030001010f948100b007180c600180113850000e00c07600708010501c200b010800e0360300d240c040310b03a04500c2081a613000380b9801038542c442c0c4002c050603201c440e11808200280b9800302b2444884180d1118403c4074480000c1c0428640c10303410040c0c012081c05208410000d00b00010694000100e905001d03041074101c41d40c0c21540c83c60341246115524003030000251002a507201c049000a80c1180240c0c0141780402403850220441d400a85042c03000440f107503000004240c0c135130b8031074204860b4007000030700c100540ca00c50340900d99a076a010504642d640c503400c200044004011055440441050700a07010b0fa000c0354588500402840d0a5a4181992000c04000c01c400a00c2400c2080b16042c000380b0040323045040070180d00c0c0b12200c050340309602403111848541da000ca21a83c0185404e00050788400c8041c400e20701310f0098505030359219107000300300700320b0f010800f08584601b85a42c000700000c400c0d508080710070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 766152194 1250 766150944 766150949
    0x250804052206170a1202070b04060c20061b031e0705011b09090504020d06020a0f1d1516050d050301151b0807141903030b030601050a03140c1003020c0610 68
    0x40d904105010fa002c60000325502045e0341543c41a10002a02d550030fa4116400c117401410024289681070020410040404c8030030010390200c01d0500d0300e1139000207005100b03542c0c0c00f03a4008154a21005405d000b04150799070f007480725241c440440350040302900c0702e802c6590203841b150300380025080c10340580a1a0917082849650380161a810300b2488009028080d20032030700900e194518401081310f0b0300c040d100101d13990741e465406840e0000c0c0184820190420314440001290039804c2c1d40d91a00040300c0f035091042040f42e103807e03801030442c3c00c0000c0da035000ba1071409854034000b115940000198140d803680700e030b650b000c0c4500e4442205c0311841d081d0a01030950541c800c00c00030485100180a246104d6201040e4401074000b0342800c0c001c030004829101d22000240908040d003500480000102c2940240710315850907001072982c0781c40f448090b11549112107014072589092014200c009030181c549511810061001002540500f00020301401080041580303124010206000c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 766153444 1250 766152194 766152239
    0x80102090310090b0f13060207030f020c032b12180c060806030c0d06090c060207080c03060411012003031006030608011406120c04061811250804052206 67
    0x2465540080e01813000001421b40032410580c600110001091030004025283c8039581d51760404607200c40c080d1410214420b580e00c00d0b0451590340011520b480c101101ca081d03003081110b03658062480c1968038001d80c000d0304c41e2444c20044511040c0100700b0b90000840c4c4070760820b00710195a00800c0320301203c02e860a582c150003000b0300710b01d10310b80400d48400c03441c040c00380020141c2c0142e4840395031071000c2e4002d0000d80c000c80030030002003900307100c2140800000e40260119103041d540d40740050f41000c22240c140000f1f10580003407918165500302c0701c00e00c00c1c01141d9880c1040d12101c2200d00562041d0340010b410184003192100c410b000388003042a44d411045404d4030b07200200201030301000b00c021003e2203102621642c99031503000d24002423040441607414180000c100b9800c0c0d54501d541d00045140c00c001c4e018140032120b0b01c882c4182c0140080303030000c4115140031017051045074032003544004001441005500300d02e03172414642841d0310342042002d60350f100707503102c11038070403000d0f80d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 766154694 1250 766153444 766153463
    0x60f18040c14100f18090504051e0d020307141608010501050f0f060306040c210b03060a0212010b030a0204090e030a12060828141b0301050c19030e01020408010209031009 75
    0x30005d0081e40c10303607400301e0160840007045865064007011500200c4003511198000340ca00d014072442422912502128036000e0300c018032680074041d583c2d00c01d0b02402000d56501d060945c0350f140301401042008180600349004150752040060702800f400e000d4244211200d030900c1513a0324004441194040e009082542190750b0141000018003850b01c155083c00700c40550400300401006645503880c1c6800000a0341d00104002d06207400c40003003642444a20400040d05d0040c900c0c5c444504481510005c01e40c1ca5540c0d20425002c0d001d01e50102c021982442c10728040084040040c000072101583d5522081001c0210b007401d0b0b030094802d010b035640201401c01c0700604400d010b0314041e05209003142004107150794a913800390004035842c400c1c0e000a2210580c0c43c030f05440110ba600c0d0b04130020300c214200b00c070070801c0a00c515058450013940c500e0b00c100c040e0f4043e07000381d820303480c4400c000c5440396035484e01d0a010b07521008400d8800d000d15403465042130752070b02c11007000942000160 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 766155944 1250 766154694 766154717
    0xf130602090a1809032c0d05030c010f09022805060901111b180613020a02010e061614040b0910110d05040e0105010c0506060f18040c1410 61
    0x2000303610001840390401d2501c1e1022403d180e00b0448010b10b14040d403000203010107a414020214004940180c0d69101120a00d0b0070f96810840121802d24040722103220704600c6142039491849424049400b550801c0034510707402a060348000c04440c02910745000c000d8941d17030b41c1210480711081110810529030018011814140b000d80710310b80c0f060500c41404001210954540780c03940c2c05081104009107244c1c072031400c00410b00c11408000001d0100701d801d161001a00c4a00030714034003a4599070110748900307018400d402202d24040200c050f6111420020380b26451800ca1448101c0803800d50718440c0414441c440445040760302610700942040420410040c00c3c051403802041001001c1c80240148501032000039416207a68450136681c618141044481d000140d0001341400455003440300420070102e01b01e98028002c0712028214542c4000051400c0800640a9947c4101c030301008204400c5c0c9080320b060701e0b070380d9070183d01108188080225210b13055090780001881000389 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 766157194 1250 766155944 766155953
    0x1305010206092a041506090501050c07090f0902120d030b0f1e03030403080d020711011d01033b010501150f1d04050a090b0105090c070809040e0604030f080f13 70
    0x202d04150f03081c2c03410401c40c210f0410019040c2c451032410085018001007041060030307000750142c0c006000a003000d41c10500e031103544070344510880c460b1005d4292a2103030840c40c1070311640f000010a500422401116000c074011070361311544415a40082032070b00044240c03a291200741e04423030381c10040c01d14020703180c01c4014804803916032200c2c5415100c00e10001c00060922001380ca03c0aa01c0c040041c0c8079220f50410582d4100d05000d01414404890351004070340c140410b103a40a65800c0c00c0210b401c4803080d29142c1400604202c40d0b40410601e040c450090f1152400c4d0311010042500030301403a40c0310107000018049006041000c140c442507003080c0300d070054940b111f0701c5018161300ea003810030400109059800c1103c0f29804955030b1040c01d0104401d00103500d000d00070584041c907070b46c030f400c44405071039100f1218094445040421203200995690b0400f2840c6d014800a07683c1d20304041c580548146050300b00305001c01e003c2800610000784104a103880303800e40100c491068240703a00c8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 766158444 1250 766157194 766157233
    0x190306020702121e0d0c080301140a03120f080a0209010503040210180e0402030607030b130902030f120306030d0318020d030c0c06052a15100f080102130501020609 72
    0xc1c12608000c89803110415440280301002c07100841d00390b80440040d07103194003420055a85020810701c480c6164050100700000d05581c1515201c0c00c0c140a8940f940b0005071510005520040220a156a4000e00740c7e13070001200c0760004040d25503a0441c2c4035002d0340c500780d00601401c240011401d100140251a0000b058a05140b0a007000d80d02401d40260b0300c01003554540018107420400c03002e100c2107040401c58558802114a01081a1800c0c00d0006036020b00704103a9040031a100c0c2d11200640da07081c4018001c6a030b201c4111102e12040100c0306400d80c2040b100a0b01c24042c42c02002e501c1c038081d000303c0000e49020004901d21102c180c1c204074800e12800429020802c06e95401e100049542c001e02010340400c0c0c40381602c480007410007240441c41c1d50600e1450000f00764800c2000d076000508030030b0000b8041e088111582e604120211950942d074000e03899060408000030700000198002d00d81007032a00502d0921a4403000103a0756107100799028201940292600c1042008405 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 766159694 1250 766158444 766158457
    0x1d0a08060a022a0c0112020c0a080901090e1003020f0d120c1a15030606100e1509060403060c0306050f22020f1c05060f060304140a080d020306030c19030602 69
    0x6802100d0714040500003002400a43c016900b070388114010945580c101c61452201c01081200b035140210341e452164503003c004c1001000100c0c0801d1100c2268090050300c400b0b0310403010070346090310701410502d0300c0040a10081e401152000125192420041030405080381c00100d8a06900755209044503100603d803001e468110040300c000492141040300c19008080380031400004a0030002014100b00025110328400c41e003099241c6419600a510b540b51420b045840c2da1000c401c80740c0801b0076104050784941d0013071000502208000702c0350700080c50701d00265000c0006a4403141402000410f0407011980409607484c0d004500480c3d10301c09a0120b0006409401c000e02d15408a4183c0c00104070404000362800420000088034480d00d5030010084402904081000000c00e403180b002420150450004882e0300400c44010080c21034070036030180900317990b0900000702c90002c0d0800d448082c4a801500b0080c1404c1ca02108003002d03019000003000b80300303403a60350b80070001d41c00344 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 766160944 1250 766159694 766159717
    0x61407050a080703020d0e030610050f0604090606090801150b091306050613140418020111010902060723070501270f090e060a020c0613080702030d1d0a08060a02 71
    0x2185510025401102508003c0c3c4280c0007000d51301403240d005020508051042402a8000c00030007001380e10340442c201c1128030a03600d0b82c00071640040070883e10321032904011504c5041500001d501030340700d1003403c01c5072078100c000c0003e00030005120354021018401d0004422003400004454075080c40038441c00c0305d8001c0c0018007150f84070045071041d040380750a07000800c0c49000c02c2043c44010781205030305030821202000203282c04c40c0105825251200c02038100140301c1440c03044040300f54481a4060380081585803150032519144c003500700b42d0303003025281007581040070341c0000300050703001d05a4a0584400070035030b508410b048044112030360030381446402101c0c00900302d0902000003000d841381c1040803c00b240050300040c0f4003078010341200003552042003d22a024804203490350401600000003154803401d0920441c180a004c402030b500d404bc2e03e109030346154214980541e0034105945c1000f01c0404c00040090501c103a02c100c0380c4540240b00007403880c40c002e500410140c15007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 766162194 1250 766160944 766160953
    0x703090507060201021908010308070308130f11040c02010b03060a1e0f0b0306091203060402092701031b03020a140a170703021507050a02040507030b0d1b08060106140705 75
    0x280c495a1820003298400c8016035800500d0040864400c3c50b01e8400d4000d6081c2032031b440d455540e88013071034455094003500304640d405c0030504892150044100309500040380d40480c00080c10070200141d111707424944500e00c1c1c940d6501419006014401c0c45103c014050420760f80ca528941002d0319440d842c5820000e0310320800c0035101303501c0c4100031849181400005182080209041c6420f0005c1c1201d5100d5200301101d818003110700d0200c991022017500e0150f103810040000c90080c000000803140b18500d146803850600144400c518101c03030098004002a025040c41412240290700001c2d4006600d60070a0001f0201c00e5902081034801030081c4020300d0b41d038180358500e14000301010f403050304070103410010340c604280d112000c0c96401401d00c0c40c0020a5403400d40c2c603060780c50028080c90321980000c50f43ca009a00428075030101800d00888a0058600b82001d08481442d420404d883e01c08041060314000600c0c906803041e64590b0415580390310300c510800c0c5c1020f075046030799209 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 766163444 1250 766162194 766162211
    0x1704020a080d17011a030c0c07030803011202030c060c120c070f0e09060705160201231305041404021c0809060f0405011b0b0109020d0f05131707020d020105030703 72
    0x400040706000701030383da0b40c0307110604089203d2001d20103074084010030440c0542e20f100750454a0880b600604010781a642d80c0c0900b5070060f042103c0e40c0d1014220020200c0005800c0304802744411810740b0031004c0c0e900f100c015404020080c000c180f840241c03544208107050401e0140f4006104820907201211741c821394403000c1200560f0350f6000240b502042c101806041c2e001002a61b4100810f410f1031424980740e080300c42400301513040c001c0e0402440a02c90541c209103000614a001620100c45070780d40c9510f22640c101040e90f105a5000718940f1440c60150185c41c040a4012503004010703a1007a884040484802802c40b1003e841140b0308101b500259078600c0c0040c0800b001030704841d505e5520f000d001520404c09007081684c0400022100e20002d243e200c01c103419140010001a1034404583d5208000c11a82003580c3d4078038500300512840300f009203400b00d1a41d04c900c1c0301e4a4405203c180303500240c01807403402500301100040b135000560090001c1c40c0d003c00c0c41c1c84d00080118 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 766164694 1250 766163444 766163459
    0x4060b1806040e0f100209012c0108041a091b06040f03110a080102070b1803030402011707050c011a030c1503040f02040f14011a0403080d0e010207050322090c1704020a 74
    0x4810551744c1803010750008101100d541c0084980e1005508003c03640a40b08a01c0c000501d039401000710541042140b0340090100000e511050114103d07944105c42d10386000c81c00140c0d10800d41049210304800b00c0341d00c10440c6410340450b42901c01c28070103d0180e45c6150f5980100075008807820790700c600c02c92808280c09900348054001d25000c0c075800a4103003009042d40b0780000c0c4048501509401c100100409070f43c201d511a40c407410901e201da8955503e81000303c0d5940150300101c200c80d4201014505140300241c3d205500304411801d88004029a1081213410003000380f800a43d00d1060000401191002005120041c0003810200300907202003000d9044404d16200c03075219500c21801401403295240d0784900349400480042c0c030703050a5454061f524050201c6aa00c030f07030f0311104280d004c02420340581c1c82d0b40340d0080450b07440360700407010340000040f80701c10410038000d0303460b00103080f08250280498020f80c584a010041e0001c10b030042129400403c1680c1100c0010350024103075 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 766165944 1250 766164694 766164703
    0x80f0a02060d11030c0702091312082a0310051f0807050412060203042117100509042103110703080a1b050406171608070c051504060b1806040e0f 64
    0x1510381c050030551b00c2c20284100158034402070a114103011503c0030202c00903091003602e50304051780d0b045c01403142d541c002021001110000780c3d0b004801e044600e0b82040890300c4041c50040c441492041425510782c0305014282c04004104d1403882101e4011174040343c01010100d4102d22286809480d054507507800801822000c0f40840d2000c3c0e00008001c140001034015500d81d080090050000420342c0900904681c0700300400d443c000110804241c9000e00025080c000b0200505803204620b0103080054554103207202100281d807000080d002858401d1191607000f41c840421a424007005460441e60484020806020b26a8400d20312004d00d1010300001c142e074185a8450303541e941005d400030701051081c0001314074445140d09104030141c1b4080c030b9202482c114500324401d41e44040040b02c083e0a441c0001e04207001d00200000700c0701040040502c03a5018203c28404414800107101da01c8284814070000d60b0391560100310f032450300ba08070035541c8482804881080c0c43e40d80206081 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 766167194 1250 766165944 766165951
    0xc09170f1903030509011a0f0f12010510060e150a020a0c1e0e10031101050f0a020604140303100611030c03130603061e030f230f07080f0a02060d1103 66
    0x4580107100780340c04040e0b140c05070359400016a4001d00508806d0b581c24148064103078069032164031002c40003041911505a22242603c0c014200305c107002903455600d00038641039885902c0011014400b280391401100001101c1c80f024200d0b40c8042a018070380e0b1040d800510240045000700e003a4407020440031010440a41100e420406060021500d8803c511a065012624113004e900c10000c0c40502c02d1101401c4981200307c501280c1c1c4a100129002c1c400c41494034501400894000020380c2c2c0052024429131003070702000d200c00410105540c0c1d034081100c04081e420703c2c0113018003006d4812810709801c42d200d042104e091a440f164100c2c2913400840300382070b00c500a441e003040390603031501562001700f805801c0504001cdc03c0c00000d00e1282d02d0740c00058a41c92a0070703c000100b020312152040e04101e00380d600d031440d80e6803503031361501c851010110143e94803c41102044e401c0300030620398103081000c0020084085c5036400d101c1c464008013403000600380d031050b52503410140030005510 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 766168444 1250 766167194 766167223
    0xa06120312050105010c0c03021903140304090c0c050c10110f01051b04050913080918160504300501020c06070f030b010e0906210307150c09170f 64
    0x24040e200d0407000d011039005034010341c100702410f528007001c01d20480900003602e405441c040008048240d030346108a6059100400148054010030842940880a4000c1c0e0380925000d01840382c0610040f00d0300d400500c0040e04540064000c15140e140264540409a105040a401c01c0540c0e288990078040c1000103140e059440d142044138550598039035042c858030882405040a080102260001c4001000e8948001a0701481028400c40c1d04c00c1e2260114010030560502481901c4142070040a6403920003540300040640800c90181055900b658501005002d000c00115289484031014012100c1801710026040e800b01d0002c0c0000c00310480f207a401400d680c28800801072007010b0131700c801800c152070003c2910060303074050140c11240c081295040c81ca500d582001407525028005542980b1400e141a04507602e8040098036440b4003c5014152960250845c0820b0741d401034001c074005010f102050044514032030303030303950304210600071a9202108160420719000846200c01c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 766169694 1250 766168444 766168457
    0x423090c01020c0910030803090c060f040608101a07081b01060321090608060f040903030c1205040510180c0e01030605010b1306050d020d15050306060108070507020105030a061203 79
    0x3005941c04004103100504280e84a138458904540c0304042c2c1562404000c100140010100c6d416030700c100000c030003415000b00801da071021141e44007031041d40b08c1c5c4190b0001c501d009002401c007080d41110101125461070084061401a008a4980780d104540480c1c54610500100c03481c44401d41d012440a002c000000404d2421400c1c010b640c072580e829220076402998030320190701c40e40701e03000320222002070030a0603081d2656400034400741c403141c1646401901c2c100c1c554051507415004451400d81c641c0312603012602005249007075400c01c03280030b0450740c0322400c80c017000d45403903025042d03a003c1c2542d03c48030000700b60742d40030b0404000d0707101e07903031041d1584014014040284143d0780106010003c091900a01f10b0016500c0c10031071080405010b00816a120485941c0e01121819004500e0410100c00d00300340d50802d5004500616000c0d11450300041c2c81035020744900303800340501d902c40d50700307013842d55004403074540c03005018229090b01c8200c000f80d040d1004529081c103d1290300e48070b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 766170944 1250 766169694 766169713
    0xa1e060e03091203030702210d02030a0c1d0604030b0c0906070308040515010e070c02010915110c01050a1413170d0809060c0702131107140606040603080405042309 72
    0x90403d8103010201030b0f00304000384400d454001030800c1c9071480c218031690f006c55403890320107400d000340104100143d000008008010030907500400c03040074036450b211150080f03074a092041c1e51105001c4c5030807031003c100600216940101042e071142c0345030341180c5001c14041c0414200d4101d054102c010805000901c030402c80300740100d900000c24010354200c0c96241814050300c1960240c14101407010b07603940103041d644a000220701400040d440103481121409008201e1a000b0713030303004010f000d0003868151a600c250700303c0d4550b031269641d0981e2110b12a10607501c0e5405984e0082c801e5000c1900080c40b4070300369211810f528117100185c060016044000f0384400d00041264500d60003e10400114214090a445003d0780540b0360000380700c01c103010342004080b555441520103c020850380c00300700c05001c2c44007040d5200e600351000c3e0749804050005a500c9400b0040c10f00c0d90601042c050750801d94460300c0044c3d140b05c030290014010b40c00c091203804040c3c68a000c02e80103124803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 766172194 1250 766170944 766170949
    0x30c04030c0f14010c0c03030305130803090c0306060901030c060f02010b04050f0106031508030316020106050d0b1e0603030d0b010e0405040606051c05250f060503100503010e0a1e060e0309 83
    0x840050310021708040c0d0300030344079a8a200415102d40802010f159440011420b01c08000c282c4201c983d52101c4155602d0801c111540d0b5610000e0000780d109106071800a03020342004100981200da0254040e8130700d0b0b00700581500c0790301d00540d81004566a900050241d0795450044501036110400301216079410050000d080d502c140c0b4a400314129150f004100d00f040c0007007280c0c0d01c031a42003909405070401c160200e01400255100e1039001d00c0d40442075013405015080075001d03401c08900d852411001d40341440e802d40c000c2b2101b81d4550014842c03103402078000d8120714031400d0145003207800d03054800001811290143c0342900d015665502c24490350070414004111fa44000305c103403040240950f0760550721002c1303170300107281d0100d4510400c1ca0811000425401343c840404848081500c2c2c0c0320050072604121020318681410b40d50014440c02e061044441d5000d6030340c0030700458072454650345841c0c2401034001507940003026641e004600a072080035116940d580c09103582e445072108 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 766173444 1250 766172194 766172219
    0x305040f14010c020405060a0f03140115080d0e04230103140c0607080d0605030a0b160809031614070b0c010e012904090b0a0e0115080d05030c04030c0f 67
    0x100006445042601c14850381c2c02440012503181d046901052691303034040400c40d04002c0d03502203036a50301805000f008004440321400f42c600180c0c80204107902005280751206c1e461486004415081700c2e590800c424403500081098903c0940b003c29020140111600f484098030608068100304400502c20040c961b826107070030328038403c018841d0032480c0c000a625840745da0300040507201c0000f00500f540419411140003090300409660b291800341c10042950403003242c4011010180029462105e4001c016950194544400550400210781485400c00c4606001a245400d810000b4200410201310701c00140c10040100e58403103203103c20090940b925100c049078142d046c070444010f1200f05220300d521000d4001c043c2182e0300c1e00c20004c100101700c1d00c400640860089020410b00030a2a0881850110454000c020083d422a017620314404180a59103c030f400c9040e0041c0180c2c1714202558106400e0010b052501d40c1d6aa241c049000f440e50000c2c0c5601020441048000c0d042507 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 766174694 1250 766173444 766173449
    0x4020a05010908100b0d05010e070e01080105100b0a0909060b120a051302100905151c050c180f19061e09090c030b0a080f0d031503141203040305040f 66
    0x2d180c001281011010b940b5498007401d2034124641d61034681c2400da44c0c0341c181d01c0300990030000030460351142d80c0580d5140c0450b0300030020080c0c49031307000150003013052044610a10007101031000075400c0802d00304841e401020242c0802c1021000030400d050701d44508802400c3c90720700d6546c0d4031009001c4400c1e0311001411a41040d00d081d08000c00019030013180028950704580d00031526074501c00a403028a00c90f000355411499805140030000f0030b14000b4040ea40240305100000c0c00340e000d20b60181c0350101c0343c004030000b042c8407041c800c1d40d8540745030707070fa80700300400242e14a00c10101040d040399009500200004203414200001c6401210003410190f203e41e80303c2c5040c89104000c0c0140700a44100e952003a683c1c1004000789102c1d40c0150908880204800071071b07990b440c0c41310355a1070290340e9000303035004049134021150700078801e1140102e5a800000c0100b031440e128105c0a0210413903a01d400e014196a001840f8070b07201c02144128800d03241c20b901c513424003080031003004854 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 766175944 1250 766174694 766174697
    0xc0b060d14010b010e011d0f010c051009031d03070311061e19090f0303120f050702011b0c1a0702010e1f05060d150b011b050c1003141b12010e04020a0501 68
    0x1440c18040c0c0c0602400d240c250228141c7c0c818010707200340c2300125203032014440d0140c810f015100002d00e05401a4100b01c03011800303070b034a8010b44814800c103541e0f442801c0700d8081d4560f00101c800c10003e403040c400c0803001c0c00c0c000c20032801c00c5041c0c40741ca007580c032644000404000000910203030a11041c2c0b02e05208006a290807001e0034100540c0400c0c0f42d0282c0400781c240f042040341030a200e5600d405c0b07500021000f44051265003482d02d0b029011300b052116210700310040c000c01c00c40440c410382c030800d0565000b05080c844400c00c10350760340d40700310060b00c288115502c90300c48600c408030030803840c40d4a607a4032504644002c4004111403c540c4043c0034140308010900c002004142100503003075680e43c0602c40003450350072803030040c2c9848182119900d10565000c510400b400004100403550410940324401071100d214002c8003240d0008148880c02a402c0001c1050301c0f0007000030344080c04441d01d0365483d00000090300310f04400240e01420040c0c803050100710460501c9010000149000e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 766177194 1250 766175944 766175957
    0x160503090a031b1215240e16020609100e01061a0c011109130f140703060e060301110a050a18030f1406090705120709050106020102040e160c0b060d14010b010e01 71
    0x4c940c1c507001d1082080005840b0f85440340503005244421241624002610701618180280e071000340f14100d840440f00c100000001c0b81d10345000f50300100b034080c8141c032544040c01008502040b010020207412005d40d41541d42e540020400f0001080004c003134194444800c1d840b0b54611310518251050a00d0a1b51658400d100a800c540c841010041100889800115001d03030210720103030040902d14030114a40402c0b1051204494140e4884c1d01554220602c15401ea43c1e05014142030714000602000820400c100c1c3c649072600c50300141c8806040d40ca00803c00308103801d600c801d00c010a400c1651215a061ba201c1c040100345c0292801001290015119a10b0580403181c1c58402500c105030245401d151000751a5400380209805400ca40c1c2c03040100303586403400207001350458000c5804d020380c0c0b0300102d8503121941440032501d0465076200341804400fa61100710340d5102500c610b402030401680d600c009482c034018618105080c80001a03e16401c000060444a5407180241030010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 766178444 1250 766177194 766177229
    0x312070210110321090d0c0807060504171305120a03080103080f0702030105090715050c030d110d0c080702190c05040203041a100f0504020f160503090a031b 69
    0x4070104114586003090074003030104581d442265085108480305046aa0311802c85030324903c11a410f464058803010084600c900a03100055420603000d00015121002c14800c16000498a0f00a55445032103000104584582c10355100e8050f08003080001601c14204018006410b00350484400f4074a00e07001080c6049207a207000d0007006060102070500703280081d889403040001c00450307050543c090020003075881c100760302d192140c05d1401002a8207007880310451081d8491010744070301c0020b01000d946407402c030217001c1c8014001e0b8404d480303068609203c0c40002722070501c00c1c0050007510b070312005105d150004000382081143c1e00c5940e400e8618410305004141410b070540140c407019600180e030fa88490900e0b0146030030000c002d00e00c0444000c200620a001300d25038204445c0e5180c14810400d4a610800c0140e00400100180043c0c00340009155030461400e104043d50081054a14000228011856410040c0c01c1075650105501d04a601000e08000120041080c910701092056 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 766179694 1250 766178444 766178449
    0x40b160e09070c052107120201060e1812120906070906050715111303060b0114030420060f090901170a0312060914091605150f0c03030a02040503120702 67
    0xc2e1036141049108030707045040003002c000790400c00c000c0ea021410b00004001d00103005910661044580c111501021900e0500500804090b41c48201d01e603103640c0c3d08c00554007100c03131a24400480c3c0e442501054040b480d0f00d00001e048481c144518074003d480c2181c5440d290140140070502048220001004165881019982075940c8840703d002c404003005500c001070586814100002e10000422035400e810101c0e0035000c0381d115040511811000f000195904c1c854405041040501080018000342e40b0480c019021040710100c3c19001c902c6d0000324519800441d010203454000240001461404080d298010444c40380c10f680340c0b0041c0c0280d940c030380c003800b070303004050108801f1180d11200081d0041c0010388500038040003845010841300030921001d84142d1014016600c15203600d80f9110718040907200050000080c0b0281d44d540201705901c00e5801d007095010030b0105804250041c0000c44c0552140d21000d611607051000305070801c3d05054400d0140d903820010000140c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 766180944 1250 766179694 766179709
    0x131101110d030c0302040806010f05031002090901090c050d0507050a02010e19030f021014040b06010816050a021203090a0209010b07150c0e0d050105190603030903060504080c06040b160e 82
    0x11079864041030545448500350040e00581d0091442401400008a03180c0e841504000460b4000c804030780c1c010860b070162108a00c40e000001d904041c1420050250b05090b8000fa0705008851610714030708600c00501508650094411303030001240050341c400c01035824082c00d40a0400b08002e0088c07051180c0c0300b0410350440c4240201840400442211094028800104511640d0b481404501c1043d006030504800844080705c03006040408a10745510403c1d4a900c00c03055003000039400040c0350030a803401e80042c880c10085118000500041003942d0029501a510701c4d00144000c1e01c10b40f0402c103260a05170404500300c4004d01000d400b00702c00d110600703900b12254800085c55021007104030344240c0903841464020600341e0a9500301b020550095100d14078801d000003000c441000160300b9141640b10243c0062540d5405102251407940580d4015100c2ca40b818034001c400040305041c54411a0195944e0303a00d1400c02481d2030440105940d05a002e00e440900c1c3d03603c2c14000b44c0903 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 766182194 1250 766180944 766180963
    0x10e030d05040212060109020a021603050d03050c13080a060507030c0516031b051e0712081605120a020c091e041401020d06090609141b1213110111 65
    0x86071950003040940d1114103000d008102c0e0310068a031590707121001203000c0d601c05221000144662550903444140d035a000805403540200500b80624100d00224050310000c0c0424540000030841c01d1100350011044000800405010340424205410410b0441c0da00a00308000d0504040a50110650002c21180407400544402506880b903007070071a012003864041500371040100c820081c0700c00015080c0700300c0652034501c10281d2151030303665203844091040b00d0b0b070407105050440005102030060104020903900f1038a99004a4480034503002046440d003000c603400040114a1a03418081c0c48800c5e03105540c402061300300216412221220741803215040b030400300101e0204445480c02d00c4461051344001c1d910ba11000385040c0c0107000901c1902c05103403800b0b5002800349828001c2410310942c0340550002507490748e40404080085c00c0400140c41b90800161701d008507090b074032034042e004051b01c03040305130003d01c0c000a50320810101281801448400003c241c0c10001d00543e6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 766183444 1250 766182194 766182217
    0x10c0c1a07050702100915030501080d0c08031803130b07291503340915090504021305150a12020d060b0f0301050f09060117070506130909150b03010e03 67
    0x318074880682203505802507040003d00107901b87c96100802e9060700840e040c0c0d00500706680400d140070700d06962200c121100101454001d00000d6100c00f01c001d959140b402002e0b09a0745444800101070f01c81048941040782903900110f041ca06002c0200100c0b99a001520440e81d00046d0140e42d80301c00041c0144a800c40e54000340301e1500c2602e05008030b50aa0701e540d400306015444da0100070003100036800743c1040032000b440d00020f0003005402040301c0542142801e4600780d0902e46054023070a0f0040c400c0e07802001107403402a0f00002446454860702d0b02d400c4031000c2c050480208445100a50f011180c100b100340c0414025176241d8a03107880c12603110800142250401020030014009040403682c594a01005c102d0811130a900203132041ba8000142c1d00310342e803101400c0071050107160802190f6446000c082c0302c02d05014000b80024034902c450381842c5560b8141c49003c1d1000114110784101040d0385245c0c035039145000da00b16204c0118000d20112240303840c1c66039680920010102e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 766184694 1250 766183444 766183459
    0x1103040b180f041503200d0b130b01080105010f090207080306010c030e03010207060e01050a02030915090313062616051c0c080403091409060103021b010c0c1a07050702 74
    0x503080d92080b0798610351140150003403100c5400400702090194842c03105482e02e8521400480007520804418101c2000040c800e02008a0744d4903401d95032500100031080c00e4882994180100b8080c4079141d001b8201c0d240003042030b40c1005d0310340c60403000d1640000d403058014001c05001998640a030b039031200080c6889102c603062804c04480103003036150455015440010300c0c00c02d2201c5c40e0001500740c941c0d44001d0005480320038224049200458200070550080c5618101409a5110300341c2c000140900f12030138504c102134020f088502c940c1c040004584045031314000004003201ca2003030000c80780861700c06480c0070380b0082c130031003a40320320113081181c005110400310f45c1400c1175240341c1720b5543d0200a001c862030300c007802c1404150740650218200b50400100c40c40c0004407504109405031112032103454450064000c0e401400b6074002200000d1022846101e092140384000c2d40b860740c64000110306418880c41745510502100d03c0207a80d2000c001e1035035000011150030960645012 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 766185944 1250 766184694 766184737
    0x150e01210b1203130b04052202090315070221031b1e131712070212061911090604051021021903050702060a200c0a031103040b 56
    0x100141901052282c2c8400822580100c141e40080500b00c220550380300f071184661100c1e03d0500c1030083d0b10072280e1008410000304540d100b03072a035002080000b200c01506000c81d0f000000d080c44150710401d004045118104440701d42c0c100b10310300c64440c0046041a50380d032000c1524100d40b20050000218002c40102c8a01030f00c1c1300b81c11500309490400d00a00302d1040003056200e035038021144070f51600e40c800da010600c170350460305898070722031840c004010002c0070340c6184031180c00581c01070740e001e01d401680c000100800d10035144110800310016680e141000d0a4508450b4032071a001030880b8144048100380d10f4400484042d10f2044a4002d01c0300c010541c02c40c0d46040c468040d8900d0240481049100003442c4c0140102408145413100b42c0310341e902c002c40448904840e094010313400341022a1a0140380c0e841407000c0410706001c0c0b00a03a558141c2c0400690008003d00c0969100740341d90001d2580c8081c4203035080f1900005035182c0751801655455600480b10564055007804016 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 766187050 1106 766185944 766186007
    0x60106050c1902060702030f070e07090e1f030c0b070309152f0a080324030619060e07111018060504020f0d050304150e01 54
    0x400b01d804003020207110781e50007201c040e60400401c00c500e2015803801d00401c068141d090001f01030072854146072201000c0000c0c601800c111502c58203116644405140c0358104513200428034541d081141d00203401c238500c0d030004024000c4000005001c611000140004a001b52a071002d030607a14290701d54600e01c1944000e000590703009403040c10140781d11041000121141c8180f15940545005900e000c51132202620468404000c0108007074503e061010740c80e0070741d00400448210760340429550f050181c04071403a00440001c0d00781591141e1710000040901c00b42000742402c003240050011044002e00220318003a910313138540814900e011311100142c02c2082c42c8071412080c0c54a00040a01500803031788566061401c03d00c43d46c46504800405000c0e0000d141d50b0791520001d000f680841c0d00990060013039016142c02e04d80c0c0c01600e02c001e13100f110500223a2400c140150b = true := by decide +kernel

theorem cover : BRFrame.Cov 766007194 766187050 := by
  have h0 := BRFrame.cov_init 766007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 766007194 ≤ n) (h2 : n < 766187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
