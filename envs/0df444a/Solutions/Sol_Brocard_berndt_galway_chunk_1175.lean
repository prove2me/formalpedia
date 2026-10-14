-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1175
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:36:31.879388+00:00
-- url     : https://prove2.me/submissions/bf2e9b0e-6b07-4fdf-96f6-1079a2d3077c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 211151079 ≤ n < 211330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 211152329 1250 211151079 211151153
    0x6020319110a050a05030a1205010b03040b0c07050d0e100203071713120f030e03060c03010905060406031a0105030f0712141207060207020a09090807020d06062c0609040203030403 79
    0x3c1c0e5801d8031345901c0014007d6805078459110001000b52140c204601d504010f8903861600c8080c0007c0c04100076180800c17080e00b010800c039013402c0d600500b283d0b40c0f41550240a41540044050103108000400543e00294004812070b02e82660103016005e4a010114160303441d50400b1107820700c40790f01480041001000781c034250701c4a600070300824022841c03034a401030040f00d4000c05640690014024003004417001001e0300e055a0300d0100101d880e99034040424010b14643e4000307400300600103448868600301d01c075041c0c1659826401e42d1002891460000d94a4000d407144180d181441945000400c90782201440810510001c4e103481500c5444202029004078000b5500103900254040451900607000001000e4400d000c3c42401da160300c07442303041c0c000d640e00a401040e041544104210031684440090b0021401800601302501c0a2404661350b010301c2050003034020f000320760740b40b4001c1141c45c0b18a500038019480c0c5815503079014034040d480391841c01c200e030245039807174000341003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 211153579 1250 211152329 211152343
    0x901081b040503030408100f0b060d0b042a031a0d0206070602040e011e060e01090e040512030109150519150e031902011e050d1509050403020c030706020319110a05 72
    0x1810010054250b03512254001c231504d070300a04900a180c104214403503101c0030180c409505100000207401c050f180c0204000d42065141801c000f186085409400050b600884813180b1040d9020030030115501940580a400140140e078404602440c0800501d001d50084ca90740b482076602500781a40c8900440d0028421b812000502041000400c1a074201200040017481580b90160310803c104002811813810340c00b0f1210451008400501844002c101481170525808a1242e40e90794400e9490000c050601c1125011080c1490002d500d1400c2c1020402040004042448003847c003015005441d0b580b40c510814061100340e000700c281d50074022541203400c0e1400054200582e4400140a0269007917042000b90608800c040c0e00f0b68041d0540300d865110b90350001e42140b86800d400d00c010078075403290188600700360030441010ba0106040950440640444044a482e03c20036612030145114100440d00420300760040365105043c03083c0341c55110000c3c0c5400c2c03009074440c83e00b40b400c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 211154829 1250 211153579 211153589
    0xd0b040603060912050406050301090905010209120c04111215011101051e0703021606020d150f03140619090c05030a0506090d111c03060f09061a0901081b0405030304 73
    0x41d0307510126050210003004c6040c010760b1460100d00d02410150b000c0c080b4041801415074491303a5903903403000c00000754101c480d1a54000c0148202501c002112603440710600c43c0381d4000c5040c00c40d69051008840142c40003a0000c00303909920303039544090100c54035400c0305a94100b202d09402100307220000c1c442c40d07006040100012564400d0010206030f0007070090300803030816204007c422882c0340364400c10002940d03c5040580e4911141c02d00b1006403001100d020070400040500142c0c0c0740c052000403003100d00c9010000d00039115840c0194480c0307000c80c1d0300c440350344810f06000c003403074000d500104285102c0c4628200c4942c030780f004240f5001c1e00b0103085031142c0c0b060050010b90300c010030503200c01008514069203400e154119041e140c0c445c0b4954003a07110040c40c69803001038040e402c03070f8000d00340d04070089002d0395882d420280548010307c039201036103890b158401c2c600e54043d001c8800084060b11407094030380703400300300f0305071071070315000e403000100d014030011807150b03070500041c40202 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 211156079 1250 211154829 211154831
    0x9021804050705090628080f0f0c0f0409020c01110403020a060c0602070804060509010207091b05070507120503041e0608150301061e1a0c1c0203071b080d0c0503030105060d0b04060306 81
    0x5a2104080004c140c5001b40d070000d0080403810044120040103115503c103031081d8884800d0784404000030002d01800403500c0e040c00c404207011880c810399030f02800c80614948001d00000300c0d0340d401410288034500001c0d411484600c001c0c0041400b80d0303803080516104000041c903084107622802000e0300103420000000c0d00006800900b5a81001008040e040101c02040500b14202200d4405454281c80d24240f050200300d050500809005210081000b07003081007442099150480d102d0b0b015000d40915404840d80c0c1046448181205500752034035915800c402d91076903401490502e002201440c0e0540d20f450340403c0c0e40c0d12401082d24111003541011520724284a118403078184a054511200c0380c090143c090b04074000500000b00550402c80b440903a01c042d541282180321700d144c090041750301d805041d142098003100d40340c110742c480001e485520011042c11100d82c00341c100041d00c20b0380b09100502091a2240003040039034580c0b000080d19499000204050360543e071300c25a003803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 211157329 1250 211156079 211156117
    0x2030402010806040b0a0501120b190e0f06012109020d0b01050a0614160f0b0403021c02160312180305071410090303030518060a0c0306090218040507050906 69
    0x650b0080c410300d40000086130240060007500d03011601020b0140300d128104502010a600506c0340c07a03104410300c450141600f54510440980780d880c070310f03040c481c0005800440000408071b03101d03080298000d010503525045a002c056200240d2004a0150060502e903900c6208005a03141c483e4000d21a1048020140b00d42c500030410821903000c1d4403100c18807032050401001006000c04591a020303032190714a94106850602004030b0300400e00042c40d400b5084280402c2c90b800148004010705202511005500b01682c100e813500741c0c2441900c01c2c60303000c480610014000c101d89c0d4680c070810303143c40c2032180b00074103514058006503031003914540c1104005112240403e00001401d010980d050100c106800ca8001d03c400040d01c03000d0200340e83d54012943d1500480d01104401c4543c00445105062a07024100101140201480440c2c50070000060000c041d000340c402c840c01c1c96040500030011a020f00000d844002e02600030800108a9075096503901809462030342008201c080c21 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 211158579 1250 211157329 211157333
    0x601110607080603160b07060510050907020c030c040b03060601030c05160312051f030b040c09240f1a090d06110a030b0925020a081b1e030a11030903060a020304 71
    0x60600b00c0180110792854404244440391b41c075004c6460305680a43c001031140d8802680c244400000c2d040705902002c8203041c02041580040c2041c8544821020384105002480070001101e04014840f6015000603001a80ca98081c0d4009201d8880c6820058500010210362a42e06c90050074210302041c08890f03c1d50b0403805c140b140701e0780004a60076060484c4130500800b42c014600340300c0180040c0f030f0f4000040c200301800705400c00401c542c172420300a410034458404030b03a000c0d0130005130040c4094180020591000c000460807140d05100040300310f80070103005100e0b6800404c42507000b807101d041c1200024034500c55004103d80b18881d0588508a00e600141600d03d41d000f8144141c1a070010f00c0f940601090003051010050002d03014030b0903200e4426400c0000d00c1c00040d0515001003031900282202d4036007030082c160050261460084c0c00f00b80c80072000031021100d251a882030000c0c0185500505004882c080754a013145d051058020000c4e10b0f00c502100d480d403100342c0100c18801 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 211159829 1250 211158579 211158583
    0xa020105010e33040f0501210b0c0c0a020d050102031008070f0b0c01180501050109060909080a2f07090c020307121d120601030516030c0605030601110607080603 71
    0x102400c0d892822250074200009480c4a071400d03030ba002c000d4000d082ca08500350503c44071890100307200c094014800304881c00c82c9980104800d2042d500c0141c1044d02c02e03400080305a25015207158000100e0615444000e4024202d4201c000e100766248a11036070340b00540e40b4030000f0505c80784104000360b0380c0e1401580c40016515070382e01c0708909601c0040b050040140d07203480e100544140c0c1100d151a402907418082c09006400301c1542c03207601c070700c1d0362800b8090107401460503552200303020302000e40c1d05e403e960704440c02c0d0304c4d02601e082010b2028800711889200e0800013843c11035000c8140880c900041101c00c0c81c0c0808166103a071085008102801d894002c80740d006a00340080c500b01840c6494802c000b242c1c4203070400400100d02c0341c482c0540c0054203c01c000b0300c2c0180001000360240c5200c0b1782d558100380400c4e94584034040582000c60313000410b1400344e0b81e10200000902d460584255942d4001901407418001050f002c1014000104110f40c401d000790b1381c038000ca508104007454 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 211161079 1250 211159829 211159831
    0xf06010902030a09052d0f0a030302030a0b130903030b01050403020108010b0c03070b1807060503040308070807120e06010f051909020f09100c020a090c170408070c030302070e090118030309060b10050a020105 91
    0x140341d50051f800d90014003002292241000343c242c1000350b640d46e9201e50860084c04140100b40c2d004d0030304d201c1000010b0059010285140c402c1d2800c11600d20080015600780c09240f00080c000380c2504010701000700e114002c4d0005694000482c0d0401c0000e41d40c0c8c3c0403c00c1c040b07510703020490118103020340f10384080000341c005102030f041c01461b5040030b0b18020000800204410280155400811812440341ea014401c02c440240300f007100fa0b040084c41782e21480203105481c124203640d640400c05141141c00c00c01d813040c007003800d020568541420b010113904110079101c50107200f44003012060302c880524020740086a078400340040d8282c4104030b030381c802c5608189041032a02400105007600a180c0d10030080300c1c902100310b20707130b82c604d4070312920f20035060010030001000750b0002c1015000140c04041d50344103001c5900300c0d0341c1c60f1005070895403040c000c00b03055450310807007502180c0039134000c12302640a0303a00401d81c66000c03008280c02001014003500001c60009600c1c18466082c4986 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 211162329 1250 211161079 211161163
    0x8040606060903120305060d12090e010f1419090f02030919020a0504180501060e010e010b07020d1211010617190b1512010513140f06010902030a0905 66
    0x1401007a0640d10791300e10501e0040410400d040c3d86e040800c042e076907807400019407641e00000f01c904130305070300c54014210b90b500d2041c0400084407500110704200300c40002030540d9010710128603105030700401c00c000c0d03218940f445981015200380124149507140125028070028040141c3e9034107250010524110781400000c1e56144a08403075070041c0c0d80d115820048907030449011825180c602c41c4807d4040e0308885c010201d619005000030340341802017200d81200c05150215600703a80c0c1c1e84441c03011b4803d030800254010318940c7c49a0000302c1c1040300f411000d105140078101e2080009915007100d1040c1c0143e1402c071003402d4440e298040801050207041034020b07a2811341483c0d40d0f1040c5440d88040c0040c10703030b039007820410300f400d8480600d00b10000900f200240482e0801540850140750f41e51000d40c0e01044640c0664516070740000d22890f904420001003000303a00c0d101051009400c0a40540b1000d600d403510b04001c503038100f10650300e0302c100800080011204418075007030444110b0003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 211163579 1250 211162329 211162337
    0xf031f090902010c060b011403040c0608060109030305120a0e0d080105030105240f0d05030d0605031207080904090804080d1205010e01060c1709150a0311030c0901030f06050904030804060606 84
    0x910042c1d9124003154181c85d4032003c003250808001c00165a001e0410b05c80300e0321018007008206c140404528110201c6400e519008455200c0c50300440e0100403902015000c034004004d88001e131203c406205520074803e40000542e44070900900d810901c159882c8000940c50f20300620540c40c0030700c5141d400100381c100303120702d181c904000c002900361900d2001e031042d0750390024414507844902c100000964813206482d0b8850070b60381c104000703042d00e000d110b019201c3c103074500f01040744c1d09044030092600120071074102050b01003007101400c0f1350b65081310140740134000010f11100401c03041034005e80701e0320341c0c015007910b09c00300d0000ca400507849101c0400c01100100003440d00b1002c40240700d504400c1c00464000f614650341840d120f441042038000c5401400c2c40d00980420000c1c0010120a0b60180082080d180d20307a045400705071511010180d04101d50280c07503010390710260f641140d60320041602d90380c03100011010f01003114241d01041a80c800c02081100520450000d0181818 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 211164829 1250 211163579 211163591
    0x8160801021801120b120d020c0102010903301518060b042c01060c030e0f1e03011d0309011709030403030305040519030e18060d06050c0f031f09 64
    0x1203512009001c449a0301d060010184201c0e00525007500604070550303003d001d4210302001106c445903034100c050030010046c0144c0301d84a40a610601803200f0440c1c01da03941c09081d1349614003c0390041007800d0034141120f038804041d03030105041d0007030868644076001000c3c1800d181450000c0c0d00c40f00c011513038002600d415814045c0d8001101541d05580d800500480d1144081c1c51984c109207401190410b4404608000500e035a030110182e141c852183da1000248501d400610120188140c440e5030b02540e42410030100b00402040b000c01c4a030001c00200b100809084844555140d40f408000e080c4c0000580d0040b558000391031641d5000c501880106c1c602d05221103684a0040d03000c002c04050312000071409005040000102c40f8400403401c0d1103031503140c42d001c0c140307400c0740c04d642d40102e4641000401440c01c241d0000d104000c044d12011103500e507691402e009000c01803040c5400c020030b010096a060009001e14400c000c07030b0300701310b188603807a01034400502c3c9141d1011034131a003040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 211166079 1250 211164829 211164847
    0xc031905060a0b2101050a1a10030c03090812061807080730050402040b061e0708040e011409181903120c0509090a2d14010816080102 59
    0x60442c0d220700d0007040014440707111400142c00081c01844040301c03541441180601071410342c0064062140d03d182000034544e104030440032404088111944240d58511080596010703400003264a4600c0c90700140c00d00b416600c40800d9042031036401e00f03683c602c0e0100440f908210900c01548411005803c06030700c0c200c40b0040c030741c84004000808001c1da0308103640c03110384880c09089132890354402c02c60f020b00320301c1c10000040c20101d030180c0c4294202903200c170103420b00e08201c89034003494804094541030405482070003a40040c0d011207814404100c001180f440d02002035010f0030503043c40800d540003a408200308014080c103080c205102c82d0030b280b160040d000400d0740ca0303803400d401d06400500da01d050035141c0e40561413101d030349142030240c50011180e010b4000d0598210450300c412198840c04582000c4a90f02d0b00d80b40d4092540400224642d50419580810b1080b810400f145642d492060700305809000e0703000705a070740d1242d18103104801c8008072540c00b900d8040c0003182003003515 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 211167329 1250 211166079 211166083
    0x10b0312160c0b0408010b040b01030b0604030303200a11010c020705010903110112020408030c01150602120c0a120302030603010b04050606041215021908010b0304080304060e0a12020c031905 84
    0x5440005040030701d0300c9070302040018801040c0001c06907180840d40325640e03800c580d800b070805940901d114500d00381c42015158000d10840102090180009042c01e0540d0703030603001003254040115041c0c043c4810440c000b500c850042108414a030f8a800481003c50304950075118824a6041950045401802543d0703120b400b05044a0700080c00705414695400140d903802921034110840c1070002901181c50000040140500c14503c0c00820490740d08c024141d0b424a40c5003c0c03480140c0040d000788ad0301e2a440c0c009800131440b00c3e010365813803401503030703075032040341d0580c15248003294010080080e5880d00f8800d83c805c44005940a11140c42d00304002400c03880386000381611030703101c00409001d100d901e244007841407043c228219500c9000481403548904403607034540000e0070071800480e40c00e4528003624011940700c0311481c2180c03500d5a40744050011504d095409210740e40028004c15820301c0b62a4400b14203401400c86006da02c41450304150743c542c0b50102d02c4210150b090001000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 211168579 1250 211167329 211167337
    0x31011090d0201030e100e07050d1713090c09230f01030e0307021816050a02101a19030b1315050403030b0312190804020d0b0a02040504061205010b0312 67
    0x411a001c0300c0c11800c1d4030068004005511100c036192040311a8944c0104c4c103544500d00b0707040000f084685450b42c81c0b00f000400858940018102000c81b4024501d9102c4040600700382c2e4a0b907a40010b03426158403c0304c044032298024600007508800b010010444020a0340000d05034040d0a004a02c1900c001308400120f901c940354101580c0344c1194910b12418000d540d079450b402000c50b5600a00c20801d44000541a203d54a0100340000c128113118080d9044803170510054010b050300071a0000c681d00241242c96401003000c4120b200190261741da001c0d984404280310210001c07442c2181422032507505c1c000d05002c41c4078010184030000c07600b20308800c2c03d4030150b09004602603031540b800314080c2c0340940d00981c2600c2a035101c0716411941da8013a1246101c030b00c055007003603160355030300310b420600a45000e50003440d000d80b802e0200c0c154910307095000302d03140805894a6555400f00d400c035002544911081140e4007900002c0103028041c0c0d002d111000c9000300908402c08111201c0f41c45 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 211169829 1250 211168579 211168597
    0x806061602090403051303030309060c03050603060414030415120b030714040e070e040812090a0803011203090506030a200304110d0501110f2a070b0a02010e01090809031011 76
    0x1d02d400018040511400c21195812501c2c920091520f0307a03494050b002d4042c0b6141215002e04000040c0e064620a101d454400c590040040100b529981c446042c10350f1f050015103030078002040040f41a40c0c0e4110104c41921081c0d894400941c62490810111400c55003403507c280c00c0302d134082081545a504c40303000030f141250f000800c2c09081410b80d240c03602940c031615402e50f450080006101c0740c24050802034510750b441010580d20600425165840801c00170401a000d000503c41c1035100d01c1800001846410004000754907040019040d405c00c960b8007590a4490007141d030072080044071450303551001080e071800c0d401c05558103508090b0100c550f0b40202da0b20400c03a0240802500403520801d500162a555a03000c00340c0c161490b800201da12181082040c00d0542d10110090482a00d03024040586250b41c140011980701d5401112205d04640d20f40b5403044055900380700d00c0400310311401310f440e0740712600011716003465164880701c030402d850240d034040c9038000202120201d0b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 211171079 1250 211169829 211169839
    0x60102070b0427090501090b0a0b01020d0c081b060a060803130522140a06050108090a02060a260411060a021002030604020f120417090112050403051b07060806061602 73
    0xa08400b140d0f420400c0110f2441d41450420f5102014810194064031b00039004100c4580189c0d200e2802409444c10a0301040c0140c1c000308806036142e21522148218901c204120391602c07402003a000c0e801c81c1718001c050b171036802c4082849201c24542c4038090040020300c01460500a040c503000e907200031903110705c60040418000c1e0306030301d0100c52003009032300521800401500c0c08620415601c41411510003510516010f808603040d80540c1c0343c80d20440310f4000601d101c01740741e404d2002d160030003004542404280c2e0560070116241000d842407900002106081c28942418108211541044114040c6404202c002c0740d4075404a61451501c1d25000050307640d072241e9000c60002c0c46180c5c40701d002c070800410a00044044040c2d0035014a01843c0b94401221441e0b44000f403501c9a004c201d404210444ca026415039030580003e40e005009041c5541000c03495103500310504042d05020703000303400450052000e0340c5c014490a8102100307568103420000c0300161482809408000039200d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 211172329 1250 211171079 211171109
    0x11116181b0e0411040e130602090a030602030a061208040b0c0313060f1d061b030f030f041407050904140109020a090e060c0313020909190b040b060102070b04 70
    0x44515904038866400c48410448424903074810014104000310034800e00c11070a080c0c0d400c00704045201581c060f0b4451000305215512100c0308200e183d100c0030000c48540e5020b000b1200555130b0741141741e000f54007448003d81e0740d2030425480c1085940d55000104c098100101400115100c00c05130750641e210003c0f403e59440e8000d446da4510701642c100000c20b40e5507414082103040d4041e201403485140740e103442184000066400200b4407040a90700d80160382803140381440300d900110010360b0715030081980c2c0342c40b94118003c1c2290780704580c024070b541440401e0000300320300b1803241004c0c01407040140600d182018001400a2405080540190881c44001901100070f60000409503402489445010b0740c5440400113081d9052101600340100e00015070858007250840344102076801101914580541c20800220303000b40c8541404d220340c41034011024028801249068014a542e100e503103400d180078120840d00a21240c11900710307001c04c005000d1060281c078190303076180c5079030810 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 211173579 1250 211172329 211172369
    0x40302120d091707080a080702120114060103110c0a060902130e03070f11090106030f270201141308010212130302060601080c0d050a050f0115050304060b0114030405010b011116 78
    0x1e0519141c0220845d8000c4022000810240d0702c0203021280c4240c40540c101494404124203c8a0010151910f854048000f88456109511800045420385031050505600e1809245880c00d10582207a1443d514102d0206500c3d0012080000141e03116060081e0380b0090025522805030b9000141003e003d408100200b00000341407900e09103010381200219a91404003e028007460003011001a160a03400841032101403110341964003003851405002d001039004403403901d501006c647c10100103101c0144e00d158061703078940043c04040c002503120011000e0070048044d0240c8441d1803c603200a4a400107074000c00d20a48c081c400742003140d100d917282c0d040344807144183d07040711403c1440d213010411300302c2c140c2d8400c1380100040c0c0840f082d10381c3c854007000c130a801c1e11600640030a60910000d800142950810085a00181f4008100618007202070015400507501140c40d0794403407021421959005604c5410110a540200024406404850145d1060380030720901c0d04c07045000306203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 211174829 1250 211173579 211173583
    0x9050a0f05040b161805120c03070b0a0201112b061203020105040c0e04021f0c0804031a0703111b010b0a0f0f0f030b01060807030f020f040302120d0917 67
    0x620340000c0202884580b5103440c0c600c102100c101e606103400e06144001d502114890301c030181e01e4058844100c07a2041c1020200003100005c0a104030b101e1194046040b1aa00c0910a40008181244509480e580e410304040c0c00e540c102400c910f030b0f0500034064081c084800704403048c4070001e2228020310820340704000070041d0005412181c1c1d8400c1c0414003d04155056010314480d50207190500c4005842d020161003000007943d010b5400442440c00c20b0414600b9031304a050300c806030502005c01001c0e0b9032512600d0300708d648203031522264000001c0e0002d020801041c0d01400301e241c00c002203070304522090040e0041400b0454504444e801040c02040700358000343c20804020003500c503aa980306402d4540e07000d28015a01d1020f000500007c05180030355824041c0c950100c40c1400d140e0034400110741c051070040c8034404140d2560520794015900d44002c003004080300c5119070343c450440c014000743d82c1110030050882d6100c483c0c001c0c1c0d01c541c045008826581130320170340c0c2081488080168 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 211176079 1250 211174829 211174841
    0x30103031110110d051003030509061303050604080a020118051f02270109091a010309081b16080304140603060604080102030a0605040f0b010212090604032102010e0307030909050a 79
    0x40d00141c41d0105003021107030400d01130712041d50342e001c0c01c0c04184c0d664603040842c60b50034800140400e03814040e1406034035052020307003200550398114514090341c136210380c1c0c43c1050a440c15100820b00040a041007070782030141d2411140c15801440d60b000081d03442503034070804214100a080310103485081194001d40460b07084180c40000d03240c40001240010f400130701d900d0101e80c007254040200284118a9004910301079111a030200c1c40720010400550142c1202e503c2140c450504008005003074210030350300704011003034100030141110400c01d01100156286c01c80d0070341e07a000b480304008048042d4600030b02514180c41e0113490392114000304190380240d030080b485950012040200c0c10324141d00c00070445034200c505118014041a0280480b0707190b594050040c4c016400441c0c040740600b0044c0301e0700c00d01a049a1902e80e0760340b81c50b410320078101d840408280c07442c5131801289509008a940c81c1030303580099440c02c85030f03a074041c7c804045441101c00c4c054848000401c0c10303030307164454 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 211177329 1250 211176079 211176103
    0xb0118020906070804060e0913150902030a060903030c0507170c0a020a030602090f0d05101116050a12020706050d0b15030708060111060c12180708070e01060509060301030311 77
    0xd43e840300c41601d403c076600d40080c0505d0000441c000f80b181100e00d0480381c0140500ca003104d21180c061a2912442c01046102030300d20702d95600e40c05800300584040042c001d10501544c80000c450001d480c0060607981c80103a41d104100d0140700200100b00e031101411450214108030f947d6503c41c01144a04100400c840a54002011030000042c00510f8009092044049416030310900d032140030803c43d80300c1054058403e920040341102c500025601111941942000040c1400015070520f01150940311040307800d0303080300b5403010030441d000c41400030202c03150001c2c240c61810844e00a041c0c0c010030328030104e015124007140110351221752800104100d049031403642c0e4034100e08043d008000039510140080c0d01085c1d14400c0c41808541c03d4020f003003100c101c625010065050940744040a01002c402045e107040c1c42011040401110000345294400790010700d141441081c10840141c2c004010700908110881595a544003102c2c192940350501c1d121207040241c1c440e180034849d500f0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 211178579 1250 211177329 211177339
    0xe030f031315020303010f0509130209100305070509040b040f08120c1b010b010503190209060706140a050405070501050703030905010518280b041e1109060d0b01180209 74
    0x10400380c0d040540710300c20548180385003000c0715222841e400c0f81d5a200900c51162025030600041c01280f5001c0c201070380118940c240306c01002d0540d00040d0107c2425104d06680c000d21140800800505011440c000d020403156002c0c689030070b84071011400c10080000309000d0b03032140d018080080c00025a1102c040c07182e5400d1075440c1404007504158408000130280200c6a43c016420000500807a0105881a91140c0c210303100c2d11143d1141e203060b042c140000e55002e004c24150f80c0c4688025240203030103400042012910b503428070302d800d203001c0c01a0420710b05240801010a000041e090110380c000c2ca8002d0f0741e03c0715814205c00410480000502a5081a0a0141c540301d051101510000003c00381c411103880507840c183c07415803c1c145265001c508070b04102c045250700e54044c0c1e1040c09070590507420200c03004080007080031010f041b102e8400c20ba0f280c0b440d40c07c01415003079001c50269080501307841ca588407058180c80510501c1802e2580f540c07511110b032403d4058551541010b44 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 211179829 1250 211178579 211178587
    0xd03090806100320030a06020a0203041e050405010f1a03130623010b040f290409020304330e0c18090111030708070c0503070b0f040c080d02030a0e030f03 68
    0xb08041100c1402d21040d603814800c0780d0b4040500c503180c115150b40c0f000050091410700c5803565031202a40025281c4010b5000510000a501d1104100f901240841c048a200c000e8140010007007140d0060300141c03c807210611080c850050000c000f8051002c00c0010503440b80d4850303000301303020003034582d0062400b030910030014071405000840000c150001d071a105400e80c0c9036040014a405640716240c4c4074803c242003044000a0500801e1010402c0140040c1411030951400030b10307405a0720410302036034000b003080203001c2060f04107104029180741001c2c1403442c100c41d505036502d00000c040d00213503035038144e081c00407000c0001281046028004502d101125005000c002d40100d829910365402c0c506507004048012084a00c10201a10380c03600301d480d06803040322070f8802804110340520007003080e000400c201c0b8403502e200d052010800003141c130f007a00e031002800185600c2210030741e000e12a101c480a402005885081c0b409141940244041400207440c02030512901160307400009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 211181079 1250 211179829 211179841
    0x7150204031101020d020c01020c09090a0501060e09060604140105060a0315080a03031515110a060515010e0301091709040902100c02030d02070b0301030b07020f06010902041e050a050d03090806 85
    0x200c0d041d5401e0000741c080d1707000c80c0c40684042e40c4401c034030001103005800903003500c1200d10b010034020740c001d03002c54103c89605001c1d84d2401d0841d01c0a4004446c0c0110701c40802111050400040c4d0f4000c500b03850621050307a41201c500c60100044c050240700c0d00c00401c0e4011010702c680d0190300c400c00c0c2c1d510340100e120760b075020054461515070010350010b402d080d681649124410401030440351412108940c513440c0240841d43c05030b05820a6503140210070784900480c0c400d004507401101031901300b0380032064007800984030508002401c3c0c040d03410207a050b804150102403840002845070880c0c1c1d5155001030000c0d004000408000350700c108a4001d5030305a82d4461413200c0b00500c25403c448807080800c80c141e03a01c2c000b0388540d09481c681040140700040b09030021580240f003e004681c440001d1021540c00e10341e098001c1c480140d4007080c100842903810001c0004018990040500c880c100310201e0281100760080c2406450001c096800f0584a60100d2006294140170b480d0182081 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 211182329 1250 211181079 211181093
    0x30316020a0609060c120203011a071a010806010e130c1806080a060510050901030b070e0105040509070e100e030723130605130b0105030a090204060803070311010e010219050715020403 81
    0xc500b100042c0f5010605c0003201511f208482c1a0f41d4078940358624410856038190322540585012107540445c403403030603480d055020740c185c0a040e14038081d0040350b041010722626050028005104440303e0181d00020a911503029800d42e00d005004141440000c0324220192513654003008041c030078a5004030510407203504c060b0051041c03440c0410080d580b0010465128000e01002c0c2ca151700800104911034003500d907401125006051060070150b07568006010944101ca000c0045624001e00b20391925200c2140c078a017520710f041c41606c103015203001c01c0d525182c0d4014103101d0000040001c40c82c1c1c418800d1804490380040038911301243d134514610103490b540c401d550180085402801c10f1801600a24460751010794400f0f04683e12410b00e88082d0000d50400c0c0d80107030b540e0001203050039007400100341213030080d10b5001000f025a01420b00311142c1590b401c3d41030344140544980000d001d0b640f003110150600c1c0c0243c841045082c44818030200480b1591120f1000400008000c20 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 211183579 1250 211182329 211182341
    0x803090c04110a144003030f120908030a021206010306080c090a020d0501060228020d0206031b0307030b090603010e07030f060204050603040c0303020c0d02063708011505040602030316020a060906 86
    0x3c42019103207001100d92151250610700000b0f011502000c88088c1e000d116420f1148181d0751440302040d500131039101e140c1d5950041c2c40b049181500040c100031001c90441c0050341000c0700b8a82045a14039103406291a500e14503007140c8204207a4010460854840c0c06071b48030300c558684208100d507921840a9070710003809002030110751000c0c00e042c013611800c1020171030040e006012082c42740066400c00c030150303100608001d00f000c0003804124400c120342015508c1503a1540300000d05c600c202c2e04001d51008000e1070380744030382c1c1070201840900030b0100d21035040f25030208030700b0140070080c500311001c0c0c015038018a403c094040100018000d1400181049034029000d072a6400108014480703402c16802c03020f900001c0c204079400d0300d4030030f24036044c61080c0c0070032110720700c074003854000066090823444a2001500f41c0c030040c001074917110449002501c1c1400c2c818a0146001b00c06512800018005484518524001280c4500a0100120300d95014008012000f200d203048030003051 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 211184829 1250 211183579 211183657
    0x9030a05060f07080109021810021005010303050a0314060f0103020318010c0f120c0804031809060311090c0406080f06010c050d091a04030305070224070803090c04110a14 75
    0xb4604c40005021398007882101d0f51018411441a800c503400014000c40640304003038401140321361041400d801001b440740b203000c2d5110341c0d03c99680d40002c400060a843c1400740d030000400c1c04a0605c00c0a507120312400106120030300b00580c80c4e6070341078544c171413884540201340c1c0301d942442c20217407845a10510003d602e010985035070300038400c501e40c03100494a2072561440841c9851000c14082405030b0010b03000e543e102500c411000f42c43d02001004d81d0701c44e82c410ac0b4044c220f040f40c01d280d850f00082c540d078416145400c040c18240382c200001d00f0828003600090001d4032020215865900c40c03a103e500141c0c015007140d040704c0c079503200100100020701c51043e441d401c6100c0c0518001c500011601126010343d9150b080c01d50b02e03020051a00402d080c40040c0081642d90601500c041c2406408414042c0100f80d440c2e203000f119581c248183c05002178400c1e1303d4000504411203000c011b40d030481800e450513920b1040c81c860704011900c1101c07081200007203010010041c02c0c1a2251a064141d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 211186079 1250 211184829 211184837
    0x8010303080a0c1d06040b040b030613020c0d0e030705060a1106092d100c09030302010b030604020616020f031c0e03030a0206040818061315110303070509030a05060f07 74
    0xd9107450814007250f06281100300003900f00c85015052104620700080d00f0b070380042510f4a0507644510800c2e0f2544150b00004214101000700201d03443c1ca11070022001718059000d516010000d1089611003842004c0d01e010320015100500c90b03032718204080000742c00040d2001e40e88009508bc0078010352040c1c4d05c050074601c105070000f010700d02d012900135a02c0380c541c0c02884034031034030410030b100c42003529510864521450429540700440c1d8086c0c41001d2243ea01c03a40d404904504000342943c0306065942c1c025403029044c000143c940d2400c940c5810691034441c0303052641d5100050700540e03904d80b4258544101c1c40b19040000030003078200d81152094807001c543c0c2807100d080c541c9901644005a0258202000150201c0c1c00e810081c1440c81000c044020780044000000301581c20041c2450000f240410042c00303041985002180c041d13805003404000c3e0f2500b03080e21580ca01c401810001004000b0842c0e5496847c10400c08030313803950150641e4100c0c50850000485c02c40f0481c1c5840000e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 211187329 1250 211186079 211186081
    0x2a100801050f100f0f0c0506010605030906070206062407050d080a0b01140d0510030f03021e06040f080a0210020721080f040b1009020c0609070b0f09150f04060801030308 75
    0xb03103000c502141c20103c107a01d401e0420540150240c5001c08a201603109000d0341500341b00024000784499806003c0f43e844d581d031281401c50849242280042020302950f200030b090003520f03540c1c5d9103840c0152014034803850074081c03052148091401400001860b51040d05000120641c20604840c03180010240c108404100b5000442e80c0b01c65560a81e00280f00810046020003079641156622038942d1180c001e419a40b91340308000d54414000c2900180c00c101031a5050307040c4240d10030020341c2c40100900340f604064440300b009845005009007c2800000c00c800d407540280210712802103000703804c5403101c10302d04091000c00c0011528011100d0000c1c0e0413440b043c010410076000d803880d00d208d600d281e0b42d10b03500c152408070301402d4140c0b903042e691000111111180014000c03512070b1000703400242070414880d03107401e02e25000758010071400e01c01c11480c1c0098105a45141c001140c80451040040d6661209442801c2010303d44107000580421000d03084504c890407248255078003646 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 211188579 1250 211187329 211187359
    0x1203040f0506180c010e1c0c030b0f070e040b0f0910050a0305030d1104210f02040504111806150f04120b010317040b0a111515010e030a03022a10080105 67
    0x1021404186c1c1951000070040e02c50084800305a24901c0607104029001c0030540340d4a5101500e807003268400c4902d210f500030048420b60105004003030034420740f024007004136004000360b0300d4071884010034055090080041c000c0e4890202c88001014064006900180c5034140b0584940c48405034402d52814100701824a0b400c2070704503400c845001c0e0074000a450389a50344038800103103160544000c9150015100503a440d03204450289100744032540785103460f1811300c1050140000780000303803142c00d41001501d031600c81c04141c420064440196547d80070b9030000c071050140341c1125401c0c1d019070822078200441e101c049030680340941120301196612000071045403055000304102e00c041031003000801802032200002c00d50200e8150b404580300c0251108414508640e0b041d0102d082c1d058880c029600106211541a82900505600c4186807000f9513526803590080044820494209100c803095140f010f120020040c260002c0e49190300008220050078003c2c688120070b21508602 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 211189829 1250 211188579 211188587
    0xb10020f011b0f050a030e0303150909010c021209010212040b070b0a02040305030a0c05010209040f0c1b050a0f030908010e0102030a110c06070e040b090109020c010c0207081203040f0506180c01 85
    0x401529540c0d10850100c0803114104d41603004503d0481c01d1645034000c80c50101000e101031440380c3c1100e40c50005241c03018003080100e050140c003041599242554024405134040b8812000d8560700e19116a43c49011740100d00d4598030701c80446501c0c42c08100071410101840003404c519000301000e061b1500d070000710900301c0c4610300c4010155803040090214040c090021080300d036004000040c1072501880c04942034400d401c403ca540349507154101c60f04240c10010f11040c2b40e80c00d6031a40548201580e841e5656202104003a00119104c6e40c3d03d420548124030503005026074030001e200c0072340c4458800e4040d40041c0d0b40c400c845410101018000c80140050321103c0304804014401504e642c0303415510f1440d205017041d00b194554006410980701c40100c0c03402011040c0d80140d80304004a00d00703007168150405001150041e07070040100b5200050852510242025856a692180c1c584800c500031042001003080c050344040044c66501ca581141443d203041741520421004c03100115 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 211191079 1250 211189829 211189871
    0x807020304031b15020a05010c020307020108151f1701060e010206070807020715050702101e0813020405150a0e010807060c02040906022205030102030103030c0b0403030b10020f01 79
    0x44010380c03040c002000454109104806211a0900000900740c0c07281c1001d05442050756a11340964080302c1250100102485010509256407000d1401d00b0401c0d8002401808068900074030080005115500c9581d040c00c4600e0103a00016414810000a1005480042c1000c44140250000000094814000d41c000c40003900140d000d48400c1e0b54105007030340e40f080054001c508600c60410702041245002d150071352246425101d4544564040c410081c1074070034000240200244202001202d407403600b00d075400c100a901303125a0994071000381d15904510103402a502900340000d00ac40c1c0c503140a924105484117071010701c03810307844510181d5203200a205024855011400400200e8800c0c03a01a0000d44000d102180324503e0392a03050580e0481d80940c840c0380381440644a03a00c6c0030007400d000030002580294255031446d1005041030b43d9801025190a03809000141011320035840f281103044000c0403941c0540000000968a000464110f5030325860310300c41ca13404452400820f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 211192329 1250 211191079 211191091
    0xb030610170c06030a1505100929041811030f0703050a0b0102030a031a031b010f1d010807050d0e010e1513031803060216030306320607020d06020d05060108 69
    0x143c1e03c0d40d15803120803001000000f10a090740b60343c0c82c070701007082d6640d1803041070006044d07950300ca8101d050200c00c1c450000c0301103030030786c02c900d00403849035074050300c3c1090b40c080312031444c000c3c0d8503400b4104480015044c5400c0c49410704000008200c02d6811024110b0300903029603808204c0b940d07070145114204c801d5121a0380c05a8805c0c8540034000e4801d4000c07021441e4080114400d0030000f03400303e85454051385403c41c070402c0807a00c800071942e001c0300c101044183d61410300600c040a00712504541703000c02d04103040012000008410034040c20807100e12a0142a08104081d0321003901402095101c04102c0503024062400d41603650010840f030007254102011020040c0640c1d054811445498150361f400780b0b07046002021400d00e102a0292101c0042102402c0c0e20074a130081c111040c5030040b0b90081840c01c0c001d098070032400305110282c0803814403039013111008d00c00540a400f807007100a5000c001c0c3c00c13010041190503005060500d4080d901031085440305401581e80c10011996 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 211193579 1250 211192329 211192339
    0x80105040203100e06180f0105040e060f011a0c1c12091a06011b0c050907080c09040906020c0f1e150a0b060403060c05090315150d0203010b030610170c 67
    0x10134841309008031251900008000e04079283c0c5002d0395000164041e04491000301151484010040d6040500480180200c180060220351608a00951040906000e00c3d00300103252602100c0c2d03425020100c0305610000390460f1060b00c10300c4d41026201c1d0006441300002004e550728010440b0b254001c24280c590301000c1c050760044144959002904001d050604102c0c6205038201142c40c2c0c0402024039a0041c000b1941041c01c20046c003030070b100080c05010405c101a0704101d8410b041d03c080c1c0d40581811280172510000d9800c14102070f0142c03001480090149102a581038000022580343c00018039280b0a03410242812a54440c86906c0526072a10400030000302800b01742d90090540310740050040342401c1c1c80b5202c1d41c00701d454401010001c1080025420003500d810403c2d44408582440300d0002072401664424031201004400ea0280128011403c1195005c3d000b1401905019080b2415840c210980303038521901c42c414200e82842c61182401c403144003003600024440f0240c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 211194829 1250 211193579 211193611
    0xf270e071e0c0308130b040b0a110a05180a150e010207050a0602032b0f0603030e2b0f1b03020a0e090303010b030901021b0309100207050307050d260703080105040203 73
    0x1000e43d04c5200c001c108440224142030b540e40019803000c8102d006134000c503110b064038a013a88495048540740e0300700040c083d400703200c1642801c3d84041220001e00c1206c2030b1041400c1c012002c035030028403507000502416000410703882c01c1544014141032003032090342241c00107503842c02400285001806002e0068004102207011101c5401440079510820900d04c0020b11100101c08201c07406603100c940c010b520b9043c00c1042c544d00c20780c8e022a0300d00c00c803803212040c00e0940c11500ca07400b4907400c00d40013140c40c221420500c01007800c0c0d1700c420381d01300062000380f1180300c1c09803101f402240070072031080c0c0d5000d81c04180802020b6040c0e10541c2041c005500c0c5074203000401c2000c0d040281011090b64080088101c402c540b80351800e045954400116200d002110800c81d0582c80340a910045600039903041049a50005219085503c00c0c0d42c600c01c0040d6605090803031072300c802e03c49811404120358904001002c90014080740d4000c0d0303034075006a62290204402c0c2d00c02698052500700b0202 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 211196079 1250 211194829 211194833
    0x30103080414031c0f0e040b030607030f0905060108010902030d05070c05220c03050402011b05120307030b0a0303020d0206010e1314030c0a060b0418030f270e071e0c 73
    0xb0525041964014101c80140d11a032440303a0101c0c0784000c0220002d1126070320400495000317002c03401c02180c12542444619900700203c0e68544c40140707400e080580b2145030780009201e5a0002040c01c0e0040281c07180c075a11004114060504007100301c1c000c0c81840a0907072070501c00c5054a142660040300b400b403261801c403c0120801420882004000f40c00c4402e481318260392081e80c001460079100443c50745401c1c000900110003a103038488082d580803000030001080454031200040014003160740325110501e0490040c405000000e4011707030a44404002e0613000a001c0d4444207443c5c1c2111407580e22180003c0b241d61055404909030880c855000000641860300000b850014208070790600009503041c91a20b00150300503203d4940c0c0700031550007420207010b10300104607004d450f1301100c4243c0d5030052899506d030125404101d5490205184003c07441c25405644032000d650750025030300d56600c1d50b04210b05448a00200e032041e9000c1c0c1c02c2c03180c26100f189044001b030301c4411685600d5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 211197329 1250 211196079 211196099
    0x1509010903030c020a090504050f0607110a020402030a090b010806010317040f06053109060b07030e12010204080105010905060f10050a0c03030b03060127060e280515030d050301030804 81
    0xf00d00101e80c010f00440c03021a4109892280511a90144000b02042c0c40740804250510b900982000b080150707400a0046086002500d21000b5605071030041c0d0380e40e1100c081e04020084284002d184031301e440000100c8a0740007074114140c3c1d0180ca41e0614881c041c0c2c55600261040d8400e180385200d4141080040714050405060702d445003003403034000b480205111003140c140100c0041d200c0e0a2008051014540c41c0c0324140251010241d411b240c0080358034040c2448040900711807044c0354103140d0080324a030a4060360000c0544100070302c40d0307503120700c03c4070301a08007124000d00500c0f6800460300f40e40b411404d215103940386610388600d440740c0c502c0100c0d99032407620415001c2c1601d41c06180080d4804100c418001e16811200d200001c4545070303000c00c0c1110134078060161904080e001c2c040f90912210b400d420080b1280018031141030040c0003021070054446a59206290208104528601c1d15007406000e2003103041c0c5001904400c42502d01e40001c0c0400f0b00948018070080c0101c001c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 211198579 1250 211197329 211197347
    0x170105090a0b040e0109210302180f0117040c03030815012123090105010b0a090920120f01050409030206040b070e061b0c040608030d20070809150901090303 69
    0x2c040e00c00b18240300110065800d50700c0c1e00c10101d03440c00c60019120480c404c0b0840701c0000021614041d841c103c403451130040400044807d0510803020001209000c0c0e0194955003124031070b82da180c0d5003a00d003a051174402d0030756900c001d030040340c003060001b203040d00c0d0250101030350038050b180c020000d02c0301c3c081d849808000c008509029503450981c107c0d04c03103164001d0061503d942d04119803d20b0100a003900703482d03060703100d145442d00502c000d0034090b0300401442d081d0307400c5060010b502032240510900001c02403d442c403103840c00080c01d00b103500500b41d0651003440c1c0a900d19070580d9031002400100c8030304000280c0141c12010100340024014211203400c10180e140c001d10400403000081c000c1e901044400301e11340ca1a4407500c604090a1080a048210465040189900d00800d142e02c921480f070b00d86980c170f1b035100c1c00c82d40c0f040c0c04018041c440a220b03030300c0240c40740114640702c41c00f0b82c018008503101e50301c100d80342c02d2480342603400c0380c040442c181c0d80c85020520b595015580001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 211199829 1250 211198579 211198601
    0x90b130504060e1005091006030b071809060b0a020f120a0c0203120c0d0e1819060e10050f1c0213020d0f0f05060a150f0c020604080607170105090a 65
    0xd22014a514080f40810a000400701c0d8000700103400d0408511840c6008a04040003009508140d400c1020403100c0d00c001c0d6214840303051420440140003403400c103541082e08840c5216140001c0445c2c10040031300035040098a54013200d00407141080d030301e9035a559090031385044070800c01891400e00d00c00c500100c10b0340d00c09800ca030040c01206001e000c0613000b580d0740784256804441d00456440d804100141c60220541d4001200700f00c2c060660304035200200503e907600d6810703069a641c03c0540e400350004001901080c03589040581c100c1120404900c1901d104071040c14a0318a549801880710090886034182046052041d03400d0220304200b0142d08444545e080c410010001687d0160149a03d0000e000040e80c019401d48002150409031031a40507030100c0308140a0030001124025840003941803820300b04455050032200042c00c0754000b9000840454000303400000081c9040c020320780da03103811000184200002e03140210910402c1d500803078400c0851230801c00c3d984101c007004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 211201079 1250 211199829 211199831
    0x90201050c030703030c090e06013504240204050f040b010c0507030303090c0605030f0f150a03080703020c0d03020c0904060b09130308011706010317120702030d0501090b13050406 79
    0xc01189107060543e040044180c0210361581d9019007070540c0502e100780544030070f01110550b03040403800205408008200d8902c01718058042101000051030318522403411856420800c0c50705140c035980e950b901808040c410781a08144034600012802920240c5001401540c40411403000b003001910140324082d0502c0580020342d00030403014444c0d400914040c4d103010819940a181c20a04001642c1c00303403040190034403d0250350480021150780050340800c40c00229181c0ca2100f2103038006420010794440d0030090000100040c0d117000d0540c0714040d40039a001041c60000380440c0001c030040c0100182c20030b18524600e840c00f0742220f608140a04000101080c466011800000082c0c0b860146544444094410558045150782c050b055810400385c1c98110031030850341d0350f00d06000c001c11610341c1410309181d2600100c282c0e1051134000e4400001414040c1c00a07480358854070103400404d041c80000f00b00d0003424001c00c480444d0141000814040c001c50395001008050070869180f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 211202329 1250 211201079 211201087
    0xc08070f05031801020c04020a120f020c0316050d0c05060a0504050c100e0f03010b010c02132004033f0c1202031812070b070302100c03092603060409020105 69
    0x4100d0800290940f40d0451039440c01410102c0c002a18140709a41c56901c0f403030040014500f42c83e4010b81001c0610114080071429182c00d0660f200640500f0394441c0c21440003065a000e810b00360781ca545070045c02181a2010048410780843c6c07164035001018000354404404903070328401c95803000d54001e0146055900c0c410010000801040300c0030f4440c0005140c2c181001514030b00f2202c00d48888508500800c0441441e0001800c040c000c0301010707100d210040100751941d91070740c215188502e01c0142c2c000800c08640d590894981290109031091828070140d1101000f003010b039160b44c003012038020200d003114000f02150786015103048004000c0e941c8204c60005e03008444e000d50000c10394024644494000e050349102c0101c074101d9038411981001102c071650408203804e4151200100a2030f919007080c102685040100c807041100180303010301a540c00c07a0704d5486040200d01c43e500b00d82d0b14102141107248800030b6240f125409000c200003150b05450300d50301440d00c0600c181442410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 211203579 1250 211202329 211202333
    0x604021005070c031208181f15050612010807060912150b03070609140a051f050f0313060e01051e0603070302030109080307030c0207140609040b03010c0201061a09010c08070f 77
    0x2e072070000e40c1715000700303c568052000c010071000350041d0101182d00144040c0361030b03041d080e410944d41f9103d8541682d1383c40b00615001c021109070b1000e44400340503156115070741d4600c03c6c0d41220034401c4003042e010307100011034107600c248000000c468086100e03010a0600d40c4442c0040880c04c071a1b60b1145a41d0301c035411141e01d040c0081c100400145c0c845882a51400d83e46803607010003144150321402d80c0c40000e101d150389660f4802000c10907445031051070804e10030141d40c0340c859140051700c4202c2c007004001710320b01900301e0a4980c5210b141e090111301c00d03841080b420b84d0015120b0b204000c0d045042c002200d00745100c0285d10803c020102c4500030b50b01e801090840300415002c0c0c451031000420081d17032a0300f50140c1040a40c0500c0141407032440d02140480c004100c1c0207640c8034040003e803001d07035075540390031070550008002e008100301c2c030300034101900900784ca1046004184031080c42d01d80c0440028191015000181c44052900034140c1c1c40920a40c014a800c030350b03004c07180301b803600 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 211204829 1250 211203579 211203593
    0x9020f07021e03010b040c02120a092d0902040b030414010618050906010e01051e040b0a14040606050f0a0c15230c1905030a0608100b0a080604021005070c03 69
    0x440080c4850070740c0b052000c0145030035203001203803890007642882c4107040030745e5001800700c140c00c4030082da050b1146a06081200d0340200c40d40941c0412612803040640550f241040c81061085179803440d5040b582d4071140380581c0258419082958000d0000401052843d14950328460080d4000a03105450720a0641c0170b698801c110030b8810364520422415200c2040a0f6000d440f0701440049107614000000d46407404143c82100f440407a4080400766458a81190b028150020207040c00c0a03241c10038002c80c02c1000e5640761107107080080000d450390003101200d66a004c41c034511880c00d02003510944403044020801c444111340d0303034a10586095075100e0408050121201030304494006815a46071400241c07005060701c408000c00e00c0d06003459010302c02000e20506000d6260b03926594144002d209a1740308141d03501442c2540c2c0711000c00c1340e0100000281c22030340040c0c8251942400380e51480704803030080d001000c2500a620302400b60028150b540d119040312030102c1e4482e56002 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 211206079 1250 211204829 211204849
    0xe0d0c080303131e0f021c170a0201140601200a06060b09010206070201020f04030f0f02040f020301170f0628020c0c0f010302070c060e010909050f01030507170709020f0702 76
    0x8010410b2462900300065507101a5208039459104c11019001d525050406010040001e1088a032000c0e510209200002c800b0881604401c0d50750000384049420300165010042840065180180d03001d0382c454405a080e00403007040c0d60701c100f44035010b040b945600d01a040325248610550031010001030040c061080601021480262a101c0420001e0f00c4c088000d0450425a40103100916076040b07400d00742c40469821181c045615040ca040c8400d000381007074030194102c0c1c02c0c014100e101c913200c1c0d0001c41c100e90045010044007281c0205a0707031228201106161650000c00229011150f413002061001400c0380c0580307040c00c0d454110034103d83c0321010b894141d81051041c5041c91a01c0302c143c501080007030038250b1405206035640004010f042c040e40d4240074039000c2c6c0700e0f0564810344601c0081d1100748030070440c6040030113030030000c15000d200442c1c40f0b01c28040003090154411000c068118545402003c1d03840c10585102e000c0d4101c24110078401509004000c0503a035140001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 211207329 1250 211206079 211206091
    0xe040203092b03150e060616121d0d020a09111c0504021903050c04050c0d020a170606040e010902030402030a02090a09140c0a0b03040203071d250e0d0c080303 70
    0x40002c16601103029041c3d8030b03411201881d1a82a540401501042da2185503100008441d12652482c4901200794200400c2102070004035009a0081c110b0390040c11004a00e008001d1100c02c3c070520008203c440203104000a40224a059080000f0070942d048018454a00c1070141d0030403090004415401c02004003000086031030301c040c4025400c001404020880307000030030441041c01e42c1c88041c2d9607007403018064003daa4850010b080303010914103499034000241e80955460b41000d00c0180700114401140e81e1031000d00000c0307407803450014210750072540140713415485a0b20b8004d0000003034100400590b014040c228001d00140e942284d0755108111407400003d02c030307049003850031485841401c5116558080700700400c85584207980030048a101c001c507207030780c0d595501c0030034145191540030860b800c010b030209010001400404610854040d10f100004800058032020000b402c1c3c0c030749801050610150003290304055030701901642c0181034150b03100d42d841500c24510707030003114a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 211208579 1250 211207329 211207393
    0x30f0e0f030a1205131101030f060f05030606120c01080c0d0207121101090305031302010c0506010303020a0b150d020d0303091202010507020106061103090103180605091605010f0e04020309 83
    0x1120703101c3d04a8444403803911140010021031414007140030402255000107003244280128480c8942c0c0700e500180c2c000707031100c101402280d9030350418000301c0d4000d003c2c0da80b10307014050001d8064105417440350020788900004110304400040107407420200503086100101c410000020310341000d00041c0070440c401c140007012800f407900010080030403012848107990509811a0109501005407608942c04803060505c3c2891440141da052503030090060242c000c4034000428541c000c00d5034651903006041030041e40d9100d40c0002001d81c60102a154007078603201c180c001600b000d44c0c0c02050580304e410b0029410040fa02c8001c042a0090050380041c2c1d110300800103a0390f42801040300621680c1000b000c0a00311403803990712405500309884c101661000c14222020200100304002d07500040204520700384602001e40b15070000307800d0782014440080010f080d5202d01c002c94900303e140d42d02d60310300a200c00b04000180d8005030940c146486056240342e8811500d421040043e240905 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 211209829 1250 211208579 211208587
    0xd090308060108131505060102010e011a03070b030118021602030102270307060503010902090a15170c0f1608090a06020a02041d0601061101140a1a12030a030f0e0f03 73
    0x4001001d03d440104001d2244014040c00000944000c0c00c1c81802d03c1e110102048954902c00102e004284110b02540d042d0b0034024203a2100c006106d8229410701c050f400c0d500d51b561106101c883d507200a210302039036207911560660b862445a03028141c01a10404041c4c00c009454001071309903005a0b600c904602400c80220f81030a0b00124080500310042d005442d0340380c43c0c25000b41103400148900c101d1290002b84a031826981c0420b01400703011301e0b02a504100303034007440007024101c940c0b9003050fa00c8040d4000c00d140602140035108054282110545481c5010101c04103036000b02c41b045403c40340c24002d006255907403401c000d0142c410355005105000150040100781c42008100e1700c2e4091240c04104090b1502090503030548606003020070881482c181074500610300340403c0160003c1503818010755941513000708660070b030071340c03010525482040200984260031a1102c5119442003241c0c1d400c0394040c2d04942740304d8008210004041c01c690041d90b0034041d40020107030035500005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 211211079 1250 211209829 211209841
    0x150f020301031a04030306050d1a090609031b0c09040c0e0a0b0904030e040e07090e120a02060403141c0c0e01020c061b0a170702101404061116061d03010b060301090b01050d090308 79
    0x1c514a500114500041600c1c3c104000d84640300d0fc100480840041030650307000e08501c100b000b000c5a516006001c0b880c0a24050901c0340300d018a0f400f03071141c1c5000c102d02003803004c803207805a07204a0400a2800410f40c4407035500361002a802c001280d001600c030414a07150a500b8060b8000078a108030b404651040106180c90801e191450703250b1410005101c244071881d030000d034460b0702a9041c1003500410040c00d0410b41c40340a1030100d10401509228040360812264001d800c201c0403645860300044491001640c9580b2009034490300944103012545001d44c0010f183e140001610060b02d4803030341180c80351111404c8069480c4648000050064110b081402c000040c0701031a00c0c290005030488114282c03c0e10480c0f1403c400c00651511301c0c2c92480b0180078481c4040c055045403448030b44e8841d40540f40a0212240086280d0b01c05045451810180507081c078110717000703262a01d96820300ca4104000d09002e61840d040001c14031a54004a60030321031003172075901940300e00965180030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 211212329 1250 211211079 211211123
    0xc030c0d050a0803130b090a03080a0524040b03250506120604020d06120c050306011a030c0a030902131a0f030c130b0607150f020301031a04030306050d 67
    0x500014028003822205401240000c580080ca150744416810780e661103600c2074022101440c0d0303001d0528000481408200f01c03000403182e21651003030302c03408101e42d00c544442088400c1291414226140d9080b480c403214406034400c0000c0000034000102c806901e0042454802d04908401402a01a0300010505410b4204400800003150504e142c4030b100e1451001e143e40140ca028051138001c00e00c00d4001d034242c0c200d00040e1000d058004071a144a0034401e004642d203100b5140031780076520000c10b080f0141300d0050100d401c0c00141616544854542d4041e42d40882001020555038007926401603880b000940b40c088407000b00801c4090320459551440840300e011148107086102c81005591404544000f049808540d501c03110302d000e044820261540f043e1a1b58481000a10001000410b4540c203c40050412080080501c0240400201c0c0b200303000c09000295a42c0d5294991404900d000703038080e200b4600480c0e41c1c1e541d600480c96400d40e240040310484520307001d82d6514000c0e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 211213579 1250 211212329 211212343
    0x30c142a0607050709020a0504180c110316080c070905010b1902031606020304020d060507110f07050607170c0a080909060a0e0a0207050c090403051215060a08150d050c03 75
    0x8651032450620341d9a03d941d40da1000e4400c00b44d0007a00401c154a0f41c0c0e000b075041c0c4005002008501c603070b1000e44030b00b040062203031003c8040810381c00241c03a03da0f80720020554400c80341c410140c00030022580c0301c2c40d800350000c1c440d04601e4440c3d40c1d80803131419910701409000b0444140c1880e01e8854145048036030903025040c3c20110f500501183c1401038888466a102d103421902c01640e03a00d444c00482c4c1404201400504410308000510803080c0d40064484402040075054a440101c60202c5640340c2c1c4091240c1d5900c58810302c00117011a882e50740d11200021001c203068130b8070318012100c50030400e00e44000d4400c00c070301060030840380c1800d00c031003640180d0480b0301e04021800d041d50302c0c902c0c610160010030b1080e400308004080000c02c02004811290080990704940740901c0c0c014243d41c032880c26180d04201d200f01050907110704402c880f0403103130018261820208062011076540d2001410380f00c03c00d892200228154071006511111540101d003e4405650300f10f05040c40c100d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 211214829 1250 211213579 211213663
    0x1060801270308060103020a05120c1824130e09061e090607210513050d0507050619110a020a03030501080a020f0d24060911030f04030c14 61
    0x1a56100040043e61003541250300c05001d007001a220b0582000440e05da004a00190140321a505e09020059030b5035405001d00b0040b0714040300300e690788c1c407040c000ca0030310114403070503010544024a5050b54842010341050244030349040c101030364506010590314019109401720740c03c02c405220144441880b0381c5240c1c00c0007891442c95041ca07601107995640b005110504201060110380d580ca102030f041001a200201401e100c2070909184025244142d000110f44ca8425101c0d075103803090140c8290b64140c0d03040400b070403113540c2e030070440111b1118503d0810700c06036a07646c0101c034800156024010a101c40c0c0e0042818403028580030b0308642c2c040c0c0002040b68410010140107981e0100b2010b54901c054828040b6012180707060700d60a400700d181c8295a00c07101c42030030100302c500e912201c220380400d0030504c00410306c451000490700c400e03260707103d01101c094001801b0034010000e0000380c601c0f42d030a0340b15002d52a40307440d04000540c6461034190901080e032000380043c070311503003080324 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 211216079 1250 211214829 211214891
    0x3030f1403011d09011e0f06090c09210c12020307060207050609060705010f050c0d0c03051306050403140a090603050f010e0106121814010c08010503120906070501060801 75
    0xd41004004188809620104140004000c0001316648000e4000100b5aa0041449000a0040c400d0b050103050008107a03030240e40350a100041c800014020850f0f01c0c0c4203603c40391030082c2000c846060400d5403144104028440d2400c480003c0d103014050341c02040c004030105803620306881003500301025940a5011540700f0b1300c0900581c2d661200b120003250040341d00f83d43d039203203d00c2d0580c05005440c0301c5007255481c001c01c0021604409009280782040391800f0082903001d041c081d0129030045e29a24211070200300c4080009502c0da0086810a000741001d06001c002d60b00d030a00d07183c0c0f00e420342d02e0016203000700c10802d10b9014007940b90404881009140e842d07042845400b000001440717400c04101e601184d40981b0801c0c1e51140c06811114605407031458441c0c149260b030005216011000c945c64440d56026452240007070074181d81c4001e000d00290120780003108042d404c0300500d603038000c03810004440090824815000282044000402e4003d23820700400c005004a6000105030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 211217329 1250 211216079 211216081
    0x3010f031b150c020f0904120225030201030b01030e061f0603090f03081b04030b180a1a060301141e0c071104110702030a1b080d02070e1f03030f1403 66
    0x402a010a4002409000e00c1d00701c0303c4104a0001641070001c0c240b100b07410036400c405200600c840b013004220168a80d03000c68080c00e00003400107421056003240a00d0b1807116560a0005602c40c0e001aa00c40c3d805140c0415140980001c0c83d0405e402951551180500b001d8601480346043c0d144c5801460700341400c10500245495403c0c0b0240240340043c20048140d00060740804411102c0b01c80041c889c00c0d090300e450310b03407616514402e4181c50b0349040a8800703018095802e8002020284070351300001d41c110b1504a0340c0621207041c0080d00035581075482380c0c030340d400032403030403803d203101d40152a9100d1898000d00b414456040d005400d4070000c00e0100b20900100381c02e44414008680d0070fa0340014990342c13044080245010f0504001e5050181a40000c14882484500c0480120070104902000d60f120300040d13840704482682805030f000039400300010000c24540e9a80440c0c480011443c418a40b003a4004490807a001140810f040c000480b800d581d01940008407220610790301403039 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 211218579 1250 211217329 211217339
    0xd031a010207050d02090a060308030108240c090d051905031806160b06130509030712020c01091a070203150907050103021303060e010b10030b0f091611030405030303010f031b 77
    0xc44c81040130380540481400b0461048a0741e10103001550844045a00d0796120140117849842d0360351240714034115680d4040561074512102ca0050102d005a540343c00b80e1241804210044460f041d1510b028608044a082294890070040107104101850351a41512010035a5000c408a43c078080d0005103d080100034090525110b010741100016050307640d041c0c00180381c407140b04080c122480c2000306001401d0000806041e03e80d10030700300c2500c00f8404d41d60403640c03078584111080c00148206420081e151049011075008072071014a10318207a41074002c24034290100a45c01d00755184902002102130040c402d11000c1d0401b440d0940c644032001c0c00404000b000d600001e00303060741d02c00010707e0007030003581b11b034a004001800340b038280c085030030026006007070420425001d4282d00d4400c1d0154500520303414031545c11185001e0880000c1101282c7c0c1e0780450003520403070b00c0304210101d07641e50100042c0d8000c0210125034911a401c41c03515040a01d04d41400d100a04000c1d1001d00c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 211219829 1250 211218579 211218589
    0x4060f050a1706180718090210020f100e070e0c070b090a03050708090121060527040b090f01090606140d210504092a050307020c090a0e0d031a01020705 67
    0x7404c580028003602d42011040c61590400d00541c1c0314000e041403100f081c06c0c3c1c40400d46c01c03a00c0d5460084038040409c1d20252801d907110103004070a80e029800086d10780090050690210f01c00e410041d04541d00e0b0342d00c6442c1080145d03001c0d101d400101c40302284150400c850114259030000140014019107000303960050080d008071076000340001320225540041d81d2240910030040c03054144284040803039410108010841401828007d402526002c246600b100503480c0e1000d10f9901130180f40c0c1c1d40c0f6101c810b0b81310006404991240610100030906810901401c032a070b038054407000415502d400648041800e085201a008140c0740c41d840c0b02013502904410b00504a002d0040540c43c1c0c00d40b01210703184103a80061001c1c602d40f0300150740d4a2020306c4c0201010709400b1405255080000c019520b60100700c50590050b804079086014034103012664a41050582a0205d40c0c09032603084141080d41515001001941c2d0b8921082c00010003096034020580a0000d0a0340c0741c01c040101d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 211221079 1250 211219829 211219831
    0x80609061b091e2707080c0c0a030306090c0306180c090302031006060206060f060307030b0102010b040603111302040b0a030c0e0d0303231603270f03090e0705040608070c0204060f050a1706 83
    0x105005400d00020040310748981241d82607080c28007507456400c0c00344ac01400030711079805900e5400749006404405540240708480640d034546094030762429200c00d00101030290030300d4483c10800d80181c00001600c003000305079003075100d09101113070380f40c1440c000038a030440c002e00f4540724004490000c1880c0d11b81b8012aa04444946008140306406000507405040c0030204260440c0c07600a000041c00362030a40c040c4c00c03490131a00020241079000703808080e03000743d0249883d0100200104100f2900070360110501e4441e40c20107030383e5030740500002403c0384003000c03055001c6500c3e4440c0c496684020300e04003180c83c2c243c928007215828090941821484d1407100c00003410b5403070b030349141c40311a03cac0311000340691100c201411342c010600d01028503c0d0700301c2040b004100c580c000072400300c603031311005031080d405c0b55580c604061402604507003901e4050040024031015929036409610350380600005002c448004041c079520300360030b0113129605544040342883c42d90800a0400c14045851 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 211222329 1250 211221079 211221091
    0x24140a0e030705060a02030703031506051207030f021314090f1602070504022208070812070813030803160201090506010303050702181906080609061b091e27 69
    0x2420030341000e501191411070190002c5900400c00304480591030f5001004114080c465a010321500000424a8403100564020a0080744060000507402e00f0660596a0b00c050185000315080c01a00c200004990101c0300d1880c203850054070a104080c60141403201d4054191440190b6141803035440c81c03000c4029091074007058a0383c8042c00880e20030094800075100040c002c44d030b56010180c0c2c1e4100c507084410300035201c03002050000780305480030410008981c814401381607910411103c61407a540084d03011a40110f00780120203429404205070805544a58080d540d01c0c1440c40d80030040012201c039842c11603041c12916400600c0200d02d990441e40e05003003054031882c0903c00920084e122961842d90000c0740030400c201c950301455002c404038640982084000e440320307403c5886140460703481d130703040e44084007040ca803190303125842d45e03500c01c01d94046003427000312400260b0800d14450307503140455800141104605e0903182406045900aa040e5100c4011071000210014002c00c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 211223579 1250 211222329 211222337
    0x1103190e030702040219031d0a0803190f060801050a2f190c0209011505090907091205150a0506030607080907090c020a2d0f0203010e03030124140a 65
    0x500300d00303090800668075215402801951901003400d030002c02d042840c0c2c220800603050a20240c102910246011080da1305030300640421403458590343c840340d0000c1c6c01c80405900030413010a10301000e109400a1600900b030200307125150100b0582500c101130200318045240540c038950701c074244001803007150ba825140c070b46011007280c2c894000340100085100220a001180121103611a540c010340d01d10840c0d1002c52a6201c6410660138010f5810f4000402e00c01c1100c1806490b0058600d54480401d18240b10050b45030032820000000682003107a00d50b01c842d030041050429030044561003171100400b00a00e00d842e10000e0350320324015100b04103104010021800030b40d421300000e00502100f40091040400c620b0001759101d145540548400a6607000036041c0401d4541801d101242d020040388983c100d0380761000844980d4008a074150340c1c502415603c1e175414405940286a030003c1511801c441510215100c0340c210300c031008118901c0da14400b10100c4600386c071540007091034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 211224829 1250 211223579 211223591
    0x180506070209060a0e0c03070f02010908090405090c030f15010801110703050703090815010608091c05090604091a030708030c030a080606130b0d0c0c02030a12051c020d110319 77
    0x408076002c03100580124100300040030030004481e46c0d480040d8001e28059450190303401420030204e00f200c803010780040000e002001844643e240503040a81c000c04028180e645403401c0d000042e107010500051032042d500b1044035105c800158001103401014a0740c002e1180104c68040001d940c4154907000b000d00c10081140b2092502c03844003100600201c81c03c48443c51603444e0440200701c8240328840c00507501400080321031101140303000003841140308400d800c08420304142c0d480d030440c0c005a03800c0341003440002149031050052a03011030070508141e1214110700d05040c10882d2a0f08102e02d107500400c0101644800002222543e420500d81350026844000006005114600c007017000944407400208180b44c030140200114220403008100e08201724205540b42c111400010b54180c110040c0c0034049803004401c5040941c4501d405858041c2003800c10405105445104030090b40c081107003d5a104940314080089500c40c0c1002e00f1858000c040802910404403200c440c3c0c3e481e03c1c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 211226079 1250 211224829 211224841
    0xa030b07090f06051e28020a0818030601060216050d1e062c030f030709030203060106051e0301050d0210020c040618060902032202150c030307180506070209 69
    0x4000380340907100500b40d0440c0300c0e507988001800340d0050280c020041d0f0044600900040c25207088881c4503c50380f044282c646001600d4155001c01c0d6030480e0b0650003040039050003e00504004c001c40d03001111000080001c2d030301494517103e030580010040d98007003d4005a40490661018211407080721404804007051821071000600d1000a002c60300310201c4600c02c2068a4001c01d0703081d481a003007610800c0341c90844104101e002032103000716402c01c000341301e000c05103000196440205418424030300c0ba43c0c0d0b8042803801e2026171100c03000a401248081d01c651200c02000f504598000c4100d045504010005590040c04100207110303403202d04c40304658034020302031906500f8005108210041d80e5080280c015445003510340d00146c0381c06000b00304d020399442a640113500340001d01e06280e19110040200411000c02641d10511050b56888010a404014840c0c80485005192281085c2d00064000c2c91182d0700c0c1c0c4003155821206100075154141901d00950b012140c0d620307940c40300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 211227329 1250 211226079 211226087
    0x2060613110d0203191b0509130b0a030302060f10060e0f12010c0c03030b041103040b1302040603061b020a02010e010315080105070302090a09060609030b1801050403030b0f010e0a030b07 82
    0xb420003455100c3c008820484290040400c030748150850060500482840f07101c548640005003000e0000305900340441031aa08014150300d191101c40000000d00b00342040003d4543d5540c1e500840060744540d080001210034984901d420007620400c1c07a20300c508001015010310403202d8207500402c2062600c1c003403565a104010791484901008102c491070f03a0350010030561501c43c3c02d41c0400e007030030800c0030103007031030b00c2204071045050310a03d00316203803a9900201450082e0209210039007181c82803025070344504c00e0100446c0318000000c0d10484450034822109c2c0703241d0703454096400411404c40543d811070000308143d2400d203000104002e03140345001400105070428006586071400f0000582d826174024058500c0840300410380540d501c10544c1515524001c0348e0010304d20a80400018080b5201c4940107540035922921000302141100e00312082210184c1c0040d80750011701d40c041c1800d4403010711005c000e28204403c250080007203111041d003880010826049103000a1540c0d1003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 211228579 1250 211227329 211227337
    0x3042901090c0c0614071103070b060d030210020d05071106060d02060c19080a1815030b0126010509090c06070f0303060b0412050c2205040303020f1b0c010206061311 73
    0x80102c4c20080308203d00030044120b50119852400b0559045000301041b1700001940c085952020f084c4074241d8401d0f040c45480420018110f09510454001015040081c0060700c1002c032940400038203803501c40d2004001c104425075440160300040d003032240307607121100121601c58065403501c2d40c0340300c41c5240520b03052608004a04004c0030355081020400e50400600c00c50b4282e0381c91040c0e0409250445030300300124070560421180410341d15020a01035081b2491440050504036004810310030400304d00303440c000c5004404030303c1c1c00044c80507142008541e50800800e00044c1600001500465541d02c59060040d040c4d107001c034440e0080511a8025001501101c0c01c0141c0710396854101501ca0024108100c907a8050350000c039016050804001c2c0600f0b00b41802030403603801e0b045444000344005032040c0c08244e001c0080d00700042d20000205408003212612068410184010600f8042d0250219045400100c1449001d548083d80c03076400c0c2c170501d880002c80b400601c200c038a007441 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 211229829 1250 211228579 211228583
    0xa12090801090605090c04020301120b0604060905190606030e0a0b040f120c0b01050d020919110307050405041b2a02030610050102060f0105090a1805070b03042901090c0c 75
    0xb0802581c1c0c0200070094214901a900040c2124540d5183e0004c100c00d0340424002c1014101212088d90042a90b8445054000344050400035400303031685252002d40d88129403013801192034883c01c13010504a403080000800080c80c0400400304050074503619242c00010282c444410040442d007404030384181c2010142d80090401c000c0500100060214204031109948130030b003010000400b410400c802404490f4014410062943c4841341200100750707010404800c0b0f03030755041c00e03000001103d00550054183d929016100d518290820068554144074040030710215814850541d81200c1555102c0c001200d40c08911b603150401050400b95040000e9494420007050022140400c0c0e9140141c81081c2d095503400d036034070b14600034510428031459070841ea0240c0012001503660303128810100701c41800d1501400192541843e0007000c0d0020900150004240000c2042800d040c7c2c0c20320b21503443c03035071241e40001e9000c00307004014402c5403501c54960440d030810a205801065400d6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 211231079 1250 211229829 211229831
    0x1a0a08070b1309060806011a0913022104050717070b1603050f0f1b1507050310030507080d0e10020706081302060d0b040b0103020705030d1805030712020715020a12090801 75
    0x40e0b940d02401c6c1e56413020b2048140340c18051001514126484003191541e03800a000c9101124002349600029401200701e40c0045640000d03481d440b01c14841058000d0380564002d000030781c14100c80c150f05900410040a981d88500720800444081c007054900b1030078184210b0243c0e49403414203031058400d50030600c0c81c00da000200810802242009440c2e0000ca031800034079407034420782855640f8030380c10594101a080c0b907000150a28404c600455200700c06621811800707036641d407040d19000040c3c1004050b0f4121000b0285500e030b002c00d01003104001240c0d001000600b403c0041c0d00e441c01e0b40103280400c03248900140d02130045118030401b0940c0a44519664122458104003d1000da030720580b0640c10040103040540c801e0013510203154200c0061454441d200c449800149503000b0302c4c090115111009001181007400070f001030b9802446a0880502884c6000381031100d01e0b0014840300102d151800609940011001c03034881d0b000d1511a03860310600002d43d003402c85540078a20359 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 211232329 1250 211231079 211231091
    0x8070f151505010804110d02130c02011e1413030302190203071202010605210a02030d020a0c08150a05100b13030308060d0b16050f04091a0a08070b1309 67
    0x1030600e0791085030100000026842095120001110018070030313140500300400ca8598880603144c141c0c3c14054603480201582c5511001340f002000350f450481358540942d641700300340b015076007081703034002840c004a450801c022800d025007500080009003001e10560046211402014002d604030381010380354041b002c0300000e11741002560b80c2d00100c0200e4415000f2072020000c01e00500078402501c10080c00c070b0703181d000e80a91010340110280d813003001034410300c030b91a000343e1014000200000d482d44d01510300103525060114140c400c60384484031692001d1400e0404500105405422142500e8082119115060003802c116480c4c1c00040c0680c1000800d41012400301e600c030022a8441d4483c1d0405a03036980c100316425040c410083c0400e4608800904400314075000e0100d00c10361814010705191600103a0754281c0c10503002000e44690b134160f200c030380101f120050903002c0341c03c503030340110b040c1406803e503118000ca00c51000c48bc10085202487e000c4c0b55483d01c00030784119801049a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 211233579 1250 211232329 211232363
    0xc03080928050f1204060c030215040c1e12060c030e15011a07050c1017010902070308090f101e0203040506070906020a0309050d060204081506040f06030b0408070f 72
    0x600503071900b100d041c070501014040641001c2214a0360607120b010803800e0602c2d0207010340701c2c1c18251f01c04504600402591203013031440202454003450080d01c00c0010300c1d04000c01d5814000c20211001103901e051041081001121002190201e40c0400701140c40513501c2c0056001e002c88101c520894081c010110b40002d4450305214101c0d412200c4078801d4002480c01c0030814805d400b07001e0541d41041514441c40e09000c51138040340c240c240303404100c4104032002440c00380000c1c0c2081c9051500001d807030701070640c0310905580001128018005049036501074079540d01c18480d40340c507070603200c0c0e07482c0e00f103094560820802e1b4044082b0075590f03032529240c0242c0340c01080760410301081400001060700d500c0052a0700d116a80b60300c0d03c089a03424142001a00116030700c044039501e40811000c61548401e025046101c610035040856500b0103004220964110f080c980110320303e07280c0b0400100d00030b6540382c2d81050f04003400e903036a065a030030002200940050f0280508000280d15a2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 211234829 1250 211233579 211233643
    0x40306140601080a0b131104210302120301050f0409050f0f160806101806120506042f1216030c0e060a140402160c060e150a0c030809 59
    0x8800c0c902680c0320190b568607441d141c0101d5503c510003e030000e104a0305046d06542c40da000241c010914401e090401d540e60030064501440c09140c124020300b03201018081640410407640000f00f44c201480c110f40c18034000c10728010b01c00f0742041c4034030385585200042c40020b210304104900034030240c139007022055142658800d03e180c070310300499145110002d03498a021800780c0c002d103548a9210115890004014400903a418411007529690500060100c02c25060007040034882c5020f84920b02e000c3c103042c840e070901140c00070b000607140f482016565003e4024440344c203404551080c0400c0f62441c4082c40d26180c0c07070007143e170729246005c00700600805400d1a41210200c10440c2c0f8581c0e0f441303080c03202e900160b03c25100c601844070038030501454581c02411b01040c0b400340070724109002e03071207400f40110140c1c007200204200750401c43e40c60402011503d01c444000b14018035014608400070b10b18072001201071700b000755800200309041428000b07001e0341c202d41e022811741000c1d110005a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 211236079 1250 211234829 211234831
    0x50d0906061706060301020309030a0f030b180708060118091808040803040305120702061602061c020a0e03010e030307050a050712031d06090615040204030c0e041a10180204030614 79
    0xd400340324180c0042c0417031905000f01d9104841a01c055420055450743c203840e554002a15403041c95100c9654800c2626403103480306040044031007139000e50070000f40280a255010b0106810055001b8401403200014a0180120380b2008400125103040c410512610400e1220003003040500180010358001c5c004003900917240035000b502c00038001c0d101003804511030044d0094205106100c07004901e000d12412102c0d680c0040c14540c584801203e0740c2034402c0ea22030000f4031640c2c2c040750326100780da4480000b14090f80254000c010b144840500385030399000042800b0100312000580300c0202c4c1c444c00550b001d840d0712000440d6070449401e40076024242e8905039001005950780314070401300f80003d10070b004941d060040c001035144e04080224810600c862107030441d4080100100051071003080000500142c1c40e0103c20b07080c50f240c260b60b45103d905490300c9245081c0140800345240c08290000c0f180004c100010b0f00482d403641c7c1d0082e0140b5130001c0e0843d8038101c0d4880c0b44d0003120b40d0705 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 211237329 1250 211236079 211236119
    0x302040605061315032c0c10050d0b04110c0a06050a06150e22060f09090507180902090103060207061410120609060507021f061401050d090606 63
    0xa100302901d440034090540100407039000b42840c662010411034905150118412207580b03004500994049a4044042c403110600ca04603441d45c0b6160085510521642d003074250121507621040c499130100400034020004010074031030380c0b120080c50641d61580290260401d40e2101a100e61400703451903120740c2c2c1c09406403850340c203210024041c0080d61180d4810344141c140e1510000c41400421900170b2120707103440d40c00642e10313401000860700202d80d841e103180b1801008125241850600e4264002030f52040a004d41803881c003600150021903010705903440b0b03442c2462141a0800c12102130501a0740c0039401500480000c003d11000b81c0042c84030500801d01440503034510000d101024804454190039100469002d2080c0174480c8000c402040c01035030081103180e0103445034011148248c2e243c10159100003076000f1600e0170002d200e401001200c0080141c01d20b42501c6c54503440010818074100080021810301e40c000385d500c01c0d00c006400100402ca0151160062441e4845070440 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 211238579 1250 211237329 211237331
    0x170d031e2a0206071e0f110a0204060f0501030b060a0e1e090a0204080c0f09010603110c060705040810020406080105120a06111b1f020306030f012a020d230d1104030204 74
    0x1000f2203500950700e81c01c175448890f50301c8a10030558564111400381030b41c465413926000b50000c0c400540d032607019860144c407264032070701d0400740780c100050300711411245054024030b01448140d00482d0400407031404581c058030744040209000a045904040c0c405285901c091003c0500100d02196405082502c40f1a07003150f040b107045008100300f1540f0284403a41c80580c2c0c1d001444290320130341219100d20003e208090804516000b902e09000303088544400007540400e0030080c85008015190102008410852405050400003455031805020340d6000c1e5001d2480041c0308101003100b249141d401102c2080040c07010210b0b416907902601d6000c541603440c2d580c0704694100410341d480001c1c3e107000c220318545d0340100e03030f01c020b50001014558140074140c20048000c8082c0514414a000380d00000c150414000f90401a5400c11409204542c802c117107003001f294105541400b0109107030400794642d0b0000c5541c0c0001e20942c03260801c5581081e04403074120a0840181c41968030840c1c0c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 211239829 1250 211238579 211238597
    0x51305090c370804170c060c0c0c03070e040507050d1205030403050d0e012f16020102030418021c0c0e01120608010c0207050307080303090d030b0102010209040204170d031e2a020607 80
    0x3101c006c0c00340d507402c1c2116800c03210115a81c0c0140e54010420844541d040c0e540c48201580001d0a00710320f98052144d4980031010041040f0050120380007a00048030284403e4046841c1c1d490380240228490052020000110781414050f80030f588902c1d032034600901140854040f07143c064222458868800c3c44820144400540c3c51040f4166161203074180d07038200040d00e11816202054241301343d041d0b000801c03000c51003400c1c90001515543c0070110250b03590100140c0c20341034a44100101c41c6181c500240110b14a03481101210000001d01c0e0400320150440900710050245034441c0e0883c2d86461688a0b140d9004100300c400c0710802c0342a5041c541c1d6644605450b40700845458585400202c0b031007010301d000fa1700482c11044184001030030229600013040882e80035030402c00c041e1101c11710030308070b00c642000200216201458240045950328041c8000f000d1007828075103149841d030740300c94920240c0207a03400482102109940101000345000b9455071811b44041c5e001440c0c42c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 211241079 1250 211239829 211239863
    0x306060312070b040213050c120907050d02010f090b030108010c0216030c05130e060c071104090b010506070204020c100e0601060f05030c0309010f050106051305090c370804 76
    0x4921038407603100c10144940b4010030369036280c0c00d4160080040382c1c4265030350255000c00f0311501c03d45108070310031006240d0714600018040c40c0c41000a0901c1510350001d40207104946500202240099080c2071007090059030780c0003941d10140742c0d0172450b500d070f8001c0000180d05205400c007401c0700f42950240c80f01210b02c0312402010802c9400041d10510b21040d0030002811700b9074440c0d03006005040e00103104c00d090310034a8180901501d001c6244040890f24209021644000c02c1043c2d8040710200310240b12980c42c041c03441030500c91544950f0001c1400b6042d134a1300d40499005120315000e841d02440a002144010045900d10301d4541c4a004004101c150055000c8900c01d81d454807554110f94030b00041c0b0010b41d10041004c005c5540300d07410000b400516016a602801e01d50712460b0312842007a82c154600b440f66840184074031100414882c80e207000744121003220711030700051314809500300c80c05190182000d000300060789125080d911a56405070100e030003184201108802d2011071 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 211242329 1250 211241079 211241083
    0x61f0203090f060f121314070312030e0c0f060c0105160315080a020f131d011a0d060b010e0306010e010e0a0501030803072a0303090605010801020705030708090a18090203060603 78
    0x18013660790003074003041960361074002c107040a5489001881081c1980d0f0b2190741d8440582000c019500d25a442808184208a00070001404a1b003491608001400d0030381d8107035907a620424a00c130701411a146090300d464441e00d08039030901001d0002807260703052040603490100f0101020b00300280c030381012521440c211f070440b103003107070343c5031004000d400a10380070000c00b10a82205503a10101c0f90f050002d401e2003a02405240700c030800b68900c42d0040558801e0309542044103801c501641071441040140e69024a009610380c11810001d110029030b8010f85039100034003c21541441400000103840f110174428505848818050007100d49501c1010410b0365801e020042c10302c107007070000031141445000c80a03020149280c0c0e440100343d150038805410000f100d4160006500e030170401c0180f1007680159070040c0100d0000314540a00c41c0c0343e0640764069504018003104001840701c0003680d59840c1c250150400c081e000c81c0907411410100700030300048408038064020030001561f94600 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 211243579 1250 211242329 211242337
    0x302040308031b070611071a010617040c090e07180501060503060105090a0f091a030f07031502040b04060f0305070801260f031321080a08061f0203090f06 68
    0x4400703545819a150005221815100010018080d8400303101a40c0442c401d409150516081d11189640e11040c078204803084641110021203000c10705001080425444003440034920540e14142045441304d181c80164400340303501c045030b01828141c0c550b2100b07402251a10894a80c112644107140010210700d0646209110342e4000ca4014000941194041c000520700c0c4580100140c92403900c0303412040340c24000f508100718103079484c0381e000701606080780e03c403031031210480042a6541000c403029544d80da41d40030003800302e04d80305152084d840760798059602400d20b0b190756075102e03038540d075005050001030400440040e041c140492041c0d8095164603040e41d411441c80c5da6003108000703040340715002d494036118403403040c140c0e44501201c0900c05010039040420200c008a40790200c0b403108500b010104203ea403031814002d00000300c080b030032103441a1441c00c0c000d10795550748000a2010441414020440400019680b40a6070110040c40500c3d0220b5254032206c0d49003007480101c2c02 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 211244829 1250 211243579 211243583
    0x203030a03051009061503050601021009050c01110c03031818011806150801051215180d110303130c0302030604051516050403060908070213051014030a020108041b14040c03020403 79
    0x31b2000503224510312035040242c1c000b02c1030048400d0180607264003001c6415505041da2a90400b1501d905c0035a80000d81800741c0a03c00c0c020071f004d0400c00002620ae01c2806007000c50f0114041a80e0030039110810200d1420380c52240ca085651b0351031008c801121101300c07000e000d45261220101e800e00c5001c0150b02401c109a44042c0755078200001d20042c0e030040380e4081c03d075201d0381036401c2107440b0640209108400780c00113000c038000c074034642e5468045801504414403442d610b241000c1d80002060307940c4500c6110a10030341250b1410880d442845a810194050148100f00018000b0000304c20001481ca5030362864a0782d0f9640c41c2455101402e00401d002030307410002040491010782202c040c80780a291030500d41000781c1e0000b9a004500302c5100041c640343c108008024082c02c80440c002d041315880000f4040c0042d0010b515000c48400007814810200e012070207105006030000c031690140580519240d456442812045038842d800700e00c19420b088815582510074001d48003126 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 211246079 1250 211244829 211244849
    0x308041e05060402010804150c050705120a051c2901020705040b0315090f1f06060516230105070201020405091003171e070f02030114040209010b0906070203030a0305100906 76
    0x603c46900448000c48090000d03908003220038540309080840d4495a0041c3c1903548805079140090300c0d006091602d0401c01c0102081c01307115003014150000200d400c840b500641d0014565400c2c400400244002454420200b585911403000c446d8411001d80d101c030800d03000c5036196540c841c104020ba845030005580c1603046409110082c41207140d04c04e4005421005580c001c18040d0202890320a415007451103911002c180d00c400840d0307510801c405440c56280c458540014049242001d003410b807002030991078580e20000d400d601c500740742c040d204212070080c0048c2c206850024042d401030b01030380d4400c001c6a40450b50049506160008803944100e8040351a085505c01045030b4200d600c800303100c0340c0c0d41141c494001f40003500800c0520304c150f6000c00d155000b070050600b181e010000151311140e51000340000b50340c80c24442411600141c4180b42c1ea0781203503010414a0045041c001d41510001ca0404070f100c0d01a00500c1c030640840200103541a611381e5648260b03011441824114 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 211247329 1250 211246079 211246081
    0x50310030611120f0103030e0d110d0b040b010602032d0c060109050108070e0412050a1407050a03030c020307050c04050604020f070f031704150b1203130f08030f03060d020f0d0308041e0506 83
    0x341c180118095103272400361400b40c2200e4143d00100e03c1916050700b0483d04009070f90200002c208408444a025101500c001d41c20301044501414416032410003580c500a8600501c000c502d10010807640072445100c10f80d40b55594840710380025120a000381c6a5074003403c1000b0411a444140030751080d50045182080c1780d1450346c06448551094403144c007001850344140c0c582c14421001004c0c250312a00042c2819512420003d080300c00308ce2460f4215082006000c2c040780c4000796822a8000803240000c41d82c941c2c4001034020307c5401c25825407201e000c541c04062003104450300078814005e840340d9132004c0d83c8450f003e000d820101c1d4014103614012003a880081c1141d03101c00c3c91668060800008010b41040c1e45117103401003071901180c800c618909100840800b000b030300c028800034006500b090b1144112104501000300180c2c000e8844005480565542c00a03000f40b414010307142076941074050500600d522004ca4050720442a008401e204032414409000e140a4000001e00b8103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 211248579 1250 211247329 211247357
    0xb0c1b0a2a05040b190e04110108040b0f0c0c071202090f0c0304111c060b01030606020313090f1121070e0603040204090615080a0506060411030106050310030611120f010303 76
    0xf0614581900e4100505201c2e0810b4501c1940005c03000e0103c070022802d084c50310b442c20510b10110b03100524100310304da400b400700007075910103d00e411000080f1204007558441c2000a00c6000e0a20900e86500c00c00720005588069403060910042c0203079001502d85d03945a0140b4209101910000c80d010030800008001c41c20740c2884140c4800c2c004c19a0041552040d0352000146503a101500c1701f95070f8040b80c4a0942e01441410010a1030340081c604002d00381e00c512640222074400c2074038454a40d003070700581d00c045034082c07844400008004ca0312001050b40d1101c07032042c425246d103801d60031180407a80300b074010f11b0405107045004150b10714580c0c4903400c1c0409000101c00441c1d0305500d07600080405c00c04110317940042c2102900811a00903a403c01c20300e4000090111030081f0300d030101910080c001d0b6011241901d520f41801355580c0c81d082d160400e201c51507403000e4040b901d441e5004007942841e50060681040c03003082502c8585a03200b22881f0032600b80300081c0801d00034404514 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 211249829 1250 211248579 211248581
    0x20a09051002011803050306030633030c060a09080f01020f0708070f140105070306050f090115210605041d100b120106080304050405070206040308040b0c1b0a2a0504 73
    0x100c030403100d2002113403181c2485074156040d2142002180030032004000c100e00c5040c104030076640004100d4210280d40b00700000e043c03440726407181c1400481c43c44680c0c55003944080107140100b800181880b0b95810402c24010085501801203600d140648500c5481082e01402601c01100f11512500c0c83c2507220342e50318840340e0000108981c511320707658560010801109184e407070042c1e440300129440c035000100030110748039a027020f8443c0c2610035207419030740c0b0740170800341c150354280200c00028102c04030103440980c0104c081800e80e0303110030041588800d403030304a00b08440c820b8409010708052140004e4110645000b074070201e60200082072130b1800a500050b00c0310030302a010340c1d501780340d10a50500b503594a40181205030f00000e81040785040500c40c1c00d6020b290f5101030000b904103030740c00a040385c1d80a0009002c58014001040a00c165001181c0c109002c0041d89017103508180c000b039883d41400300301555125054805600f8024241584022926200c0f0140a06c6414202084 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 211251079 1250 211249829 211249849
    0x2070e070905120705040608070b04030b1b0703030c0e1002101a0607050106080d0e060f1c022b020c0c061c0207050304090f091707060f0c0c050709020a0905 69
    0x3004006544074005500d0b00c41e030b1410340c818940741c0082c00c2d48a00f440180026106151f0143c019503000c0402000010000300c10784e01542d5200c1c00940d01600c07804810322095004902c2c8850101000038502c0c10550150702112065001da2200f0710014040b9081100302451240c9200c05038000080b44800041603900400320500741c2920b400302e41c055540407901c542c200a004840d07903035403140140b105400c00c1102840da0092890040413001d01c070720201d00d060140b010a06030a9102081059a2000c0c110354081009084403045454005010120030108821441141e103d98051500342000741c0c44d000300c6100b5408240140400310b4840284601070740903c500c0b84000c0c0b200044030120322514001840000c0c0039800458640303040000b8081190010b90300125028602012a00069111944000151445098079803280c1c043d08003100035181410100909a00c0d20780c591007101d412910310b0000328018001c8512450721130010004920620502c0000f1070042c0200b04500c3c5000d41c00d030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 211252329 1250 211251079 211251091
    0x201030903180b070302070b0a17091216021003090c1511010f02030f1302090c0f130801020c0c0f03060402100507060c0c023c040902060403050a06061502070e 70
    0x8010300c0d5180c20500b920509030750000c140c65540091400c0600d0750400c00507010700340c0915a9841c01e170b40c5260251200d06040310b03c45988034082d0000300840c4051082140c907406041120b55170344540006031000003c50802280319180d40594000e0081c0300744542c94203a07500480b03c801d610b04204508003220041c856850401007151104481800c081c05038400c070b20a00c10b4090380707a0600c40410900c900c4001d10705101c2a03a0322802401503a502800150031940e55016156905000007403420b01e0310860200a505010085000840c84415030080007842c04002c196411151810100700801d49410300c215419401701c00820058034010003c05200d21032814241c0ca0031160766507940990300900c84c0c04010800b00c041034010b5061082d00b802030f900c0c0403d02e038415100c002041900d03a40c003e00400040c40101001d21059440c1d41c1c1c03210925580040c4003544403070b503e00c0c203150707182010102152618101a00010110103115404980d6407054018108482c2440c0031740d542b0340801040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 211253579 1250 211252329 211252337
    0x5090a03110301090203100e06070f0c1704080d020606040f0e060a1d0607020a03020d2a0204060b040f090e03070203030d050c1608090102010e0c01020c1207090c1107051c0201030903 80
    0x8213000580e01040015004210000041840100c50b07a90314148180102400300380701d02a001043c109500580703102c0c0159008441c0d0342e405095011110060040b6003003401d940c85007184400045030000f45541c1300305000c9800b44100004444510b09032000c8012515059004001144003007403590880c034000c4183e200c0c3c02111025141c29030f45004000d658450140c3c02414264080c19410f01c0b41d801c0125103810006841150403001c1352450100071b0f000d0501c4480c240001c0c00719525074000b50300801c0741001c0e040c2c4031500c4146a11501d040d5208452065280000c45100c5c0180803043d0b41c44030f90007d01031800d155400c541074016000042c80344107450020440020500c141e00030004450740038080140c0c4440380900003a00711039011602e9485540070980d009156031b8001000200c08400765454400644070352421807604070746802c0307907904e1410091007501c45580241840000101e41007221407247c0d070369040c40815406084504840352007641c004000d54029009540b49030310a00e4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 211254829 1250 211253579 211253591
    0xf02030a080c12040c150c0b1305070e0a06060801170705090a0902030706030c031406090c090a08030a050306100c02011407150504051f0b09041b0f03060c090605090a03110301 77
    0x2801d043c090204581c111480011030400380700e0324a4200605415208a0078030420744c1a59488030307404584014001e5030001c0e065452881040402e00049005040240d107210140c01c0818458001d041035009040003e00d505000040d07071900010608100c0c01c009001c1c0a2007820141800010341c0020130b071800035502c8101c03800043e1020002e110003804299000582900c08250080c15a0300041184054590388414007401c1d56039040b802da00840010741003035581200b54089582440e256018a000f4000400d03884292500038004500c1090100c80c000c1410100310000e0b03402c850f04c20f10181c00140c003003500c215080e00450040203014001d8000e04a40399011501c2410303600c0884c1c0440c0d513600110340341000d40621000320303400c82d855079805012190710700000c1a0301010040010b000031010701d440725000141514079101405512071041c10f45034584c20040301518211520600003001da80340064900d03c92019500f410200074403410703a142c5982c0300c120841003c40076140e45035681e85 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 211256079 1250 211254829 211254847
    0x30c0304060203190c020a05091f09090b1308091009030f0c0302090612030316090f1403060a0612020409150c09090b030a030c14120a0c050d0f02030a080c 68
    0x80034000a10741c6500450303984078280e102404050740b124052051201c01c9440c90016580c1500f600203171041624480d48980c0e401c180140700c1000785500c0305a030704500c480071034480d55a400142155010b0324440000e07440720f60203805003031a1440c003e003002809100d48113040c079060b09220000c041c0f41c40c004500175240c2d02c8100506c182000101d0700401224020411810800d40c5198464411146401c1d4004050551030f142d03c401040c80d1011801610b40d4901540140642c801800110a041c65825180d1030100c00c001c9804025510922030384000581c1a0043e000741400d445034044144040c40d019420322018007601c0f04100c500c1400e08540500f40c554910030701c21402c12654914006510382078211003180c0d09840283d000c3d4100c9a03042000ca038000c6107881e941d0394060070107500c074000d40628505241c4000e80c0e80340c0c0000000b0f1480305441c0c3c0a9419014a2701450a94150000c0004180c40c0c0e015491a01000340c0c00521400c1909805800182c0d030100d0703400c0600746010142 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 211257329 1250 211256079 211256083
    0x70e09010b03070e04020f07081c0c020d030b040203040c0521030d0f0e0604080f0309010f02180f030f0d180e01030614010603050609010e04030302070b0c1e04031211030c 75
    0x240c110301c0c0215004410400790980c003c0d400041502d0130f0750210f181410412540500388103102001c0c2051500041880c410b000c03c04220520b042d40010802c0a000600c00094031040701d000030170000380c200304c481c058a140a00c212402280d2050813103813a1803505050110203205030f00b92618a601024070034500ba0803d02c0140094034100720b0000305180003410010455900c40c01401880c0d020804110002d19410201c800f00542d01528a40342c0e940c100d50107001d0003d851204181d0350000c1824119507443c04900600c6810455924040c11414024565104544010410a0b502030410145002d00440078105070069044886815949501001c881240281d000f107a00b10f0313403081d240005400d01c06102d8007411451505110f6420300c074000404408060003001410b03c0050701280405009074115030b4420340c010060300c0d40789411450758030380e82c106580407080c40e00e0f8150103540c8400e40008490640390f0000e44604040b040903000c80301072211081601d41c0d48010002e645900c502 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 211258579 1250 211257329 211257331
    0x2104180c180807060f110706051b01021309111806090d0b0c040504061a030601120603060513020f0102010204030302150a0e03040807081506181009060b030103060608150f070e09 78
    0x29001060040d181204c024007116035151004c04000080f03924810100011850100701c0d02985401074444054804c500015498401038140d50341c4001940010320585081180c1150443c00c010404c02800602e40c0360548202507001c00043d190301030b5126a850000d003d80b02441019000700a18545507880305000136003542c0086200001003810001e61516026090141c44c2a0b00014000700c8005480040c3d400040e011030305100050008914210413548550011a0044401d000e0b9040c452580d140e0781c0503201c4168000c60041d00d0400d82ca5005000311412241e0503401050310000d00007060080c100050812862951540302d450400807081002e8805461004080c111052401449514017011510460742cad1100360b40801c01e141c0da840d0701210681d0b2030504481100da82d131101c008107407581a0401c041007407810501040c448040400b0754180d034424401000025210003505a84a0380340c80411081158000080c400302110701c1d0040e0031908a007000d5801108076400a003103004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 211259829 1250 211258579 211258589
    0x6090e0c15090a09090b060301060807031203110d051509090d080c0c01020a170105090105060304030305071e0504080c0613030221010f0b030616021b150a022104180c18 74
    0x1486085c82018410725018a6404c030600710000c0040034648403840343c40700d03154403014090760141c07405200b10034000d406c08030804542e4480c25940c0c0301055800c8008050688014401804106d0004131500b8818400d5000d14207007070040c42c01008401040700c07c00c0000b001d05d100c2110900000902c031000340003801d8400c03590307285d104038042c8000c4650040c54059002a1040221100401c802d843e44411290410781500c1c02042ca50f40b50f0700d050b1a541c125407044e0b100610303112202c1990a600202900c15074284000740c1c0d52402c0503104101c0640101325030042d002151800400041c90141034292a1420044d1503000c121003030152142111684100c110003541c42e04d0000b00d040c40c1c2031080d542e000c019110307101c1100c0c01c15880259034403804482c41c2541211525174a000b555050481c80852070041c0200d40e13564a0030500030b44800c41d01c10300c02c4c00100c0c03a40001c0d002042c0701081e07400361440d41d0f00c500c0881d054142a403025001c409002410310004103410000311500b0240680900 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 211261079 1250 211259829 211259831
    0xf0a080937061b1208040807050a05060109060603140703090203070902040909060c0c050c0111010605030a060e010e0303040f0f063207170a0e0705030a12020106090e0c15090a09 78
    0x1c2d14164024044840301c008404a140358a000e4400180d581803c0800e403110343e182280182d80c940c5014038046c85a03d8025104d440741180c042d003007000015589058400c400c0040c01016900c08066080e0380c10004590740003440040002c28843c407030b0744000e0580780024121001d0340d9990314036600700e0340207030441c181d0300340c462051205200050080c5120041c8529226051410a4848640328402141014100010031a0640856000b5000b601c05400020255505442e041c50004003c120780e00107494154200554041c81c610f020058a1003141c10084640480c5070303035a9a0066045140c03000c03070300b69580e181140301c5203441f0354510354003806000c240d00c0d0285e903414420100c140300400b5501044280540030780b0310551414096003040c541200411100a0b84060f03500700702181c2c10072605481540b0307100b014071082e04900c80036100c0c10340007000301c90b803162854030954150501c0d4020395441004490700d607050a0b165020a50003850b01d0b41d0801060f1000581c2c0b05200d680602051 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 211262329 1250 211261079 211261189
    0x120201090609051305190e060907050d0b0703020322030c1511090f0604050301021909060e0a15110d0f2a240203010303030507020f0a0809 61
    0x5580080c40000649103506003000301500c3c11000a600410040c41c4480d0030303484901080003942034002e50310000c030f4012818003142110b5442a6a2132404481e080c1c0d180c81010400221410000c0318080301607003100041d0b00342d90b5141026000395101510480c50720f002003843c3d40e0007946690300d000c2c01d20310a07600e12102e00003030f040002401e403a811000c0c6041d498880c40c43c4105000400321130401e50103807004034508441100003042405a5880301d030f09540002080541c50143c0c40700d81c800c00000e038843e82001610b581c000c5822036419620a6000180c1d03507824000140c220304a40100487c9103405130b0444805c400d41c0b0300b0070381e03003060050100d222500d80c2c07180030381c01906500150740c030400500d0060a0329441c25100711148039002d002c888030700c482038110302c2405103100300702040c00303006550380e5a50313141c000d00400b0b04440c244018000d03544080c0c8400ba000c140e2494541e0000941070410040b142045045406400c508102460703540394041c010381020030698881120322060301c50 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 211263579 1250 211262329 211262333
    0x807030c0203061518090c040c050705010507030b0306010906030f06050603190516080613020d0f0b152d09070c020a0e01050102120406020303040b04111c03020f0c0904140a0c12 78
    0x3140d03030121924680490700d40300f04616040000359a920746142124085a989c1d164541680c86c1d108520000e030442d4240b5081040f6250190411440440e040d4102d441c0d1381c2c2e95800308021568140001059084e0f170100480c04109290001a040720303004003039404104d00820f0341a003405001d9000c803000e41144610303020b06103442e58180300920f0a00054240351074401b12506403c0c12050f002807040044881900600415005000c11940d00a0000030303a030416070001203160f030841c00c410303100b0902c280140025550001000680400c08004c001c003a44072a802c0004040000f0322007000c12800f00011400f503501c0a43d44001821807a06080b0f41d5410030300020700380704407410400503c5400b04020041c20358000b08580c4c0c01504846204a0343d182d515159640c000b15009503644401e10600c0040910107118031900c0d00c1d48643c00310741c0710010b584602c9071113080707079810141c0c0050000001408100c807106603100002c4014292415505c280d51a032000f20400d401c1045a04044104401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 211264829 1250 211263579 211263589
    0x50c0408030c0f0d0c0b01090c111204030c050d150504260d0b030705010f050c010209040606020105190e030414060903030c281e02010309080a0203070b0a05060d0807030c02030615 79
    0x18500803443d040e40001406e8948080480040c031965514035550500200761900c1038101c4e2550f00c03003000640e107c0320202208160b83c1d4019003c151000b81c1261400101407a000412800d066400104600380701c8003403c07541c005103c010000d4175490306896000c0c400c171085280c0c1881c0c0ba44034101032512400c21064400171500c42c414003501a520105090050b0783e000040403001c02030074a0400c0c1e86190441c1c4450182c065449201d804ca4108140800c1c2c0d43c0d0103402061003045d03904421a1308081d01000c41007079a032020728601541c1c00c1080184428080c81c171120310240406810980f5280382030000c2490b43d8400c0f01d9480c025001115200f540340711002e404040b56101d042146451803940e11580e140b001e248108800088005802200710790294203e02c40701504261a80e07210407203000d002c1d4484e407210030100c80d503000050008114a8047c400c290080c407004d4101c0f014810b060761100100e0703001142c160148512124a0f200690302040002d204002c84004203203c0f08681040c04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 211266079 1250 211264829 211264843
    0xc1505070b0c0a05120919150507020106050f0f01021204090b010f0e0315040f060c030506040c110a060b0109171f0504030c03050a1101020c0c10020d050d050c0408030c0f 75
    0x104034078804129141050f0342c8613040e6a40c02624003140005519081081440c1c5480e030784900100c60010300400c0103000071914500a00c4903080400d103c0c82d56070210407400c1ba0558020190b000503601c0440c196070801c42e5500031400c0c5c0c1030048451748101c041000c426900940c3c4041c1407152a102c0115440d40e000e4182e001d40c500c1801d040c0c0d03440c0c000c200000e4a8401c00c031145100301284400103400d100d610010413041d0740e0000300802801012003c01005480112180307405507040508200b0348a00c10003804080c3e20110b405460341c0146a51400090484200b115040280c4410f021a05402560016400c4824440103000308103901903a840c1f40c000d5075952590301c2d4035100c10800825001015000c80580c14a4026682d10080d2020b490030410300420013003540c40440c034001179075800100038140041c11602d59240c0c601080f012686c4081c5100d5540000d2000d10ac0341281a01d69007002d5041006481e0f41810581c961200d28a150818850800c85038007000403188c09807400d00c50301c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 211267329 1250 211266079 211266091
    0xe0303100501110d05160309030f060504050c10050423130204090b01080903091201020c01060e01170601080d050c0c06030910112b02091c0c080118030c0c1505070b 72
    0xe8520301d21303018000340840c01014601d903020380e814000300f0200b44c0b040b50038401540d407001c215115007455082290007840c04440460f0544194003509100389084a14814403d0703050703445501e42820283d0502181104020141070060b0124403044255502c0d4203604d0340410a00300161524a454200c00541d41c607842503a0500c00408140112150040100d44140c0f10641d44280c0441c5064440340c02071280140c1c128141d46040740219010000009036412a003944120419001c0c449201c00e44450080c41580020760240c0c109003181c070b0185000e4600c0030782e8602034840c20580e420100d030700c613801151200c140350420720040014040034030900c90070b000091003550514940802d81500340f01c00b5a114480608252503c1c0c440701c85580403604054005005800c210100940c1ca11001d40c40e04d8088130038040300400415004414403136070031008891090b84108a50740d4900343c0d15400700c44400d03107006d4401280800e1142c0d6442c0c0c4000a81c140d56200e5980d00740908012a00d00340103859 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 211268579 1250 211267329 211267333
    0x30b0408190507021f090e010810060e0609010512070f06080708090d14071e06060303081e0114010210060b0406031503080403060509030c1203060a080c03060406020d0e030310050111 80
    0x40d1000d62140340100000700800c0c6800c40c40c41700d401070140c40803c890362010600303000820001c2062500429a03409141081e0b00603c5031035203c01600c07031100011035a1a4100e6501030042003246800341c200e914840d020415107403896201c40c00b280b68161540c005102113005d10007440b410542c000c500340e502500180c041d00e048008000001d0210320102c040100c40800401c20006000150b01c0c00c400d428540c4940110230300c810701e008009041d061005401149082000846c00342c503040740d0746485016a494000320303a080805c0607011080c41c1003010f04506c6056030031160f4046910850003c1e1030640705554407140381042c001c0c1030b0b450b044011401101800820000030307a008050b5001d890b440344010686075207449500307140d4054810301d03030b11170b100d1851108044660800218001d400680300d00ca200f83e107541344aa907d1458410f040d8240d800070b00010042085903001c0c004100b05e10b04040780300c26601c4844c074507640050b03851513055400010100030541e08101405a41486200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 211269829 1250 211268579 211268587
    0x34020d0e0613030602030603030405030115080111040e07120f1518061a0a02030c0709050708011203081302030705190503100e0304030312020708031f0b0313020105070c030b04081905 80
    0x6403080c00000b09200040c07210f9004004a1490360301407083e80e000d88000f8008001d904605020070300c2610303c81c80352505035440c0205010071428044200d0b802e40d0b4801c00700c0e80040e200c00744125840354070310206008981d0b407502503003400c401600856041d400480c01e1070b04030f94200312540a80b0460850b00340c0b5002e181c18410810815044d40042d080741741c00d0002c3d40c4800900100f641540b103054400009402340c0c52010400c101c0c07a0340103e004080664032111541c4e01d41038901440b04101102030702196809001034407032003015500c8210188003030250344025030740d00041100910800b41c1450410170405050040342020426091880c0b01000306004590b800f910445d281e100314003010303041003071006080c80c02a0003501151601c552100d05640d5916040c4580402d4012500140320200740300e0000090040c1d4030402c0d42d004d044c0c01c0c00c2e0282c00d1002507005480035404504101c0b540d541c02d040010200b026131440502c104c0c0190740099071602c0c220001e0241800b10b1440406100042c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 211271079 1250 211269829 211269847
    0xf05010b03060124080c040b071b0602070b0f0d0e07060e0f1f18080d0906021507090603090c0902030f0412020615060c0c0411090a0902040b0334020d0e06 68
    0x302d5102010907845c00d00714203130f0302c2d08045440c251245420926981e0400681e020400508070701200c41c003907034003d803001059210f000072a103910561240050515040c019040c0d000c18030001020312090f40e000001e6100c4038034214900301030b0341e580588040744408110a0700c0c4d0515107480340c000a4219005a161400410b030350310048003082c640000c1101c0317002840003c0c008011130002038000d07102110784000300c00400424080c0ea0f400b03801d0060103404c1c0b1020700410906c1415000e4801074445003c1c0f03d080c004d089000340f540080036503030082c074504c00250400482c07000b1809030341e800650301034920382402c100c084640340d042d01504540c080000c200038030f070300e40c4580c01140400300c038040d035514048403c2c546042840411143d000d07151404144507519280c006152101c02601c40c04896965440f2940490040e442200d400d450304000146825141c00094000050040102d0b000340e41e84511003480c82011311000000342e070080c90403524080d002610401000c1e8100c2c3c0891505070341e6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 211272329 1250 211271079 211271129
    0x3071403130308180a0b04110d030206150d0b04050304060318050d030513120c03090914060d0501090503030f0a0510180c030b181006080c071106070f05010b030601 72
    0x1c0c0405020411000e01148119290312650410050700608551410310a81007071205a039003a501111100100007039000d80341404c3e000c0030070300707a0580c02801390390740c07032202909200c0e0001011980c0407003003070001c50005200c80c07401409140104011612a8100306007d002c64561410960004c240341d900d503000030780300140c074182c20410340c90301103080c0d00c41a0101c881110340d02c070010100610707840740c140c2042d0f22034250210280030307540b000216a9217009030000c50b260303002881081200070000401c6800c0c00028030280c0b0b4420310002404480329210f41d030443d003054460406003100d9005010320520700c0c0c020b03da08040f040004040d0f06281c04011000d14a0580e40d4802d80e81d20380c80d40b1078a890080e4415050b2100152024140302222040420028000c407124030846009800204001c0e01c9040c49170700c101050100d580c90645a51504103001020b804034540c04101001f00700e000403011402c00e14182d00c100008110a6090300c109801d1841c143c01c06c1d08408040c8184030a50403007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 211273579 1250 211272329 211272361
    0x9150d08071b090507020d05031b0705030d060b03040317011809020a0b040b090405090d0804031404081009030f030903140c070302060c0c091609090c02030d0c0503071403 75
    0x40451a507550750300915010392240031100c919880c2c112a0400000d103007115421043c400c0d81e0550949481103885201550f0900048c0c4000d42006200b01011603c0d00c0e01100070400280580c044030f017031142e0541d0301019101c0580040442c280084144810036402c40d40511924000c0080c0000a6062811000d4103d1106c050025119291542c00d815510f40c021034601420b20b02400643e00d640306e50b6036503190341c030a1041c680036505d0000021030801011461100071001d42e5540c104d01d0b1110b44080b41c21000188801d07656410030040000d09010070000140e1400c1300303071800301301c88403141009000d280c0388816550515051140060009500180c10311680104034106074444080313101d0700740381c08600c0c1c0000b50016000268000c000100158542c6804401c503015a00d56541000c454558150401c884012500040e014403410310160020300c0c0c40c17030340d502c1141c0c10004440011303001c0d600700203008d0010800000c180a44207a00ca00700c00c001070003100c400751450030101d00130400c1c1c41c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 211274829 1250 211273579 211273583
    0xb030114011407120e010e090405030d020a1101090f030305151003020a0903020d3c020d030e0303030a050106030c050a05160524070215070c0f1506080105010509150d 73
    0x14052080303110540c412001d40304403c0d000220060504c0042c10040e09240c000540c05000c1034000072000440d2070a00007da02c12513100010714100700300b29413064041d400030000101804561034168642c0700092180c100668018040c2d0181a1490b05010b000c840c0050300503181101480150740403515040b403541702061139842c00607500d0070740c404100c80324000350300001d51084042c000c00041c429801c4030348050400740700394940c0b0444c402c0b00d60070f45070700d900112001510408800e000546442401c20441d82d00038203003400c1803d070340400241103074811101d07030b104140d030b80b0014040343da03040c4500d100e54052401c3c4140303800161030b0054a1030080310340169400900c04415000c0260a009007041201425824510000540454400c0078000c580c01750042c0b0035019110061040800c0250203031500d5103c010003480fa079112580182c4c0c141c402a40d440e00704134004620301101d81b282800900410000250b50750411040000b55500030340340d2200e06800d981e00014681d10045102a0342d0f07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 211276079 1250 211274829 211274837
    0x5151c1103160b040503010c0801081504020301090b0906041202060601020c04021e1b010b040203040206040e040501110a020309041a0612070903150204140415050609060d05010617010b03011401 85
    0x200305000a150000750360051055107620940011480500e4014000362801240203002000002c8000c64461a00f4030401d0600da1158041c8c1c800107a8500308542c22500140001c145c038899901e58000f41c5c8001d650702c0149510000412080c00054002d010080660b88003610460900c440000e54560300148200c1c81998002079000306051300110300301c50212041609900e600707880404441142d01d0054814255003040247d00711482c082c4205c9206c0c0780e0003003500381060b00b461400d088034075000300119500d642c2d0301211149400c210026144d142115401540c4d074020100038407080d00c80130142c40c800070031405001a10765503094291071f01d4820349401a501ca90340c0310011905104558005809100694003ca903890a29001403082d100d45010010507800d50b0030621049600509211940a1402400f40414030302440105600400101901d0a107024091036504440003a4000d50228404044440b02076043c0703601c0c0360061403121945819581740004150b542c1e40b010408030f0400c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 211277329 1250 211276079 211276103
    0x1060507021e09220b040507030c090b06040614130f0504110304050a08070f0c0303020601260c01121113030c232b0b06130603031d040b09070305151c 66
    0x80400c1444d032a40c0350750042002841402c081c00c181d921084c0314001598084100003010503111400d001d68810100041e04040c50320f40341200c02c40e02895000014082e010040000711401102c254890014002c2c9107015400903203450104070881d030964403030072128401030007004003040c400f0481411a07500141241d40d10105464a44802444210010a1004445008020700d980002d549069951400144074070010400001c40b0302e8084429202d01d541c13025543c100365511480299041521040022070720210134044008140c001d03d108240c2c00082480410a001c810500c400003030007500041c90020380d2606a5000c1c1da449400104d0050543c4212120b1007180600007070b03680b101c1801d0040701040903181c400c00796002520440e00c100c03011440c0c4c030301034001d0748180400c40340d00d070301c0e09050524410007960407042e040d01c851750310582e43d4041412175290b400446201d120b10303580020325403a003062281030300805500c1280c000c0450300482c150048144440c9010560080300140791 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 211278579 1250 211277329 211277371
    0x80304110402040f06030e0d090503060403031109061b21030c0304030e09070c050105070809150a02070c03050a0c0e1302040209031f060602060105040c020d1805040501060507021e09 80
    0x40d00c100d1340400300700302110000040f0194594089566500c0940984900172080e500442c0c1058142c01130950580041000c2000203000c1c1c1c1c00f10740040c40214072030341450720010005010783c0003810141e801c1c892104100d0000001806804000c91543c000820540003015840d40e039404020200e180d10782001000c40c05150040c4500610254001c198110500d02a0402481190441001c961960802011841082c01a800341d84100384000c01071024240c44c0d25020725004010b05494040e503400c00008021801008044014501560041c901d80c01c440c503080c44070345901c6d84121601e040c408244955048180c41590365503030101c40141e10b410071000000d081c840b502e9065440040d0700e07a010320424106810040c121519a0240c444580e81c030010701060f1080c0300400390050700201c0860b01460b000300110003c1e0308070154840066a1503402190460714281c20050102e80e022810300c4c02c41c42d08001c00e0500030804080c0c41c0e681c4441901044000c1009801a1303003065034220100b007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 211279829 1250 211278579 211278581
    0xb1b0102120103060207120306050609010f20071509120b0702010f06080d110c090f100e270102191202090303031312051905091815120a0803041104 65
    0xc480003205070780780c1c40d030b503500d1602000950050030101c1e808240c0c04490707072115000344180011a040038010030f00d04a03040b4011207400350280e462130140186400c4400d240d4698111107a0f81c016000c2c024031149007421000001c031090102c0300c40c10004021000c2c0000c01100c880d079060158021440b010383e0b12902c070103130f001d001c0060003040c0c010300c1c0440015042c440000d000d02d50196035110022070407a07002040307494401402c00782da08030545101213090404129000c41d4000981c00b401025203454212140c1813403000d4840703441c0c0813803c81011000c5080d24101c44001e0301540001c500c0c0a000d0703040c0c07021540c84c5000304030501051004040c2e00041d01e4044031540b0701c1c020b05883e80d928240f680030800c08600b0209545922484569010389800b4400711850200b01058a40116051542c03c03150303944440c6407560442e00c0c1d40010038032072400003021303400750350142404100c0b18041e0060005c3d84110364014242548110042c8011401ca0030440c0d401a4215040000482041c0301041c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 211281079 1250 211279829 211279837
    0xf06020906030901060f121109070309170301030b1e04120516080310050406080303010b030408120a0c11010218010c050a08040308120a020708040b09030709060b04060809070b1b0102 80
    0x290704071000004100b4880010b511800541e0107613111100c42075155110078040b8010708000401c2038454041d0140246844624182e00405901d00032408008580d101c484206030000100f03601c40c0c0201c010300030014180c079041d900000703eaa1218818001501071520880c1c094009805806010980032503a4801c1040301c440003007840300f1003510b14031071400403041ea0046408213000d2140100201e21850240100800c44d0149001141144d00f4103409244551015200321444070081041c94080c00d05a4016841160380400001340d20b118048090300c001c0701c0102c000c2c42c5920400c10f03080701c109481ca2100c5481c0c803e02c0c2c18802c92609140182c6400325008010302804400f080000401061000400e101c0e441c900551200361074031913104003039000700701c2d00519042c401c1c0414480308940d400034221144000342110503040c0e0310a44e0004603507123900851001d40000074140022070b003100074103400414110051981b2440c140c00302c0742c18000c050000c00c44030032480c101d11030094250151 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 211282329 1250 211281079 211281097
    0x201050304110a12060f060b2b05101401140a03090311060907051002070806060405060607060c0909140f07050f22060f171b071e0c0e070504030f0602 66
    0x2503e2001d8a54440048840707038a44100c80e101e0030640f200b1012105409018200d801d9426900d0802d03054514a500305012505c01d4103001188006580d0082540d0040380d0051a03900d890020440c2048000c01c41284160701440c1444010352401003020340c4041100c416114528000484525600e011240c08481808200c02d034420441880302400c0e010800b002198011070f800c0302070b441700c01c0099880d0049807250615a030004800034600341071981000ba1b021030014a02480c01015070359000443e1400048040000d621b14003d0161440603c00d8500c400e0354103027036018600e00404101c6a503403005010104029000c03900c030080e80fa4060540b035000000340d00314400c8401c84a00c8010300c941c10f01c240b100080f210b0400c00000d900402c04448148642c0030310074502c0d5240e80c4110007100300c07840700d48a034150810003d000b1400c505500c1c10400a03207404685024224140300001c1d814541150003d410000b0a20654940060456003229448039007228001e03964104800207000e00060 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 211283579 1250 211282329 211282339
    0x7030503070b0f0609040b0109020f071506050a1202030303161404030302010b0102060a1b0e0a05040c02100b0301020301060507060515091312020d0e040e01180803090c0108070507020105030411 85
    0x11020041001c00c0180701d0000b103c2402c10603641d60042205001c0c0aa40c060f004c4201580140320100795a0024040407003890310407458403043c0d9071140c009007078800c811264659201c0040c005031030501442c00050204924244685040d500000e8580c40050300280b0f01034041c3e600c01001c0c50154107891010702e1050075043c0c49980da428040d010f00780441d50103005010314000540092000e101c0d440701d403080442805200045850b01740c0708200c40c2a24550b0041070914002011340e1a40208050840c0303e901a20310035001c0c852032000d989001580c54808e0b401440180700159000b425101d1079500000b0100d02078450b900003401212900401c10f401868000030070845601c918085000940309103880311030310301c00c120304a03200e0511603602d070000780c2420b07d82101c1c0e16182e0843c1040020030740000402c01d400c141e1100120b55035043c1250003c002008110f10004240260010650f080c203106200d0b20f0705600040483c400c80704001d0602402202003818817031440088030318040054a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 211284829 1250 211283579 211283587
    0x4060308070506010e070c020d02010e060c01020d1d150c0d0507050702091e060d0804183218031611130e0c0108042f040b0301021303060e07030503 65
    0x40c46035040e4000d90701969544941c0e0000a42c0c1d190301c0a07001d100705400e80d161103ea020a038200800b060a00c60240c1c1002600c080075003203980c0d00002050419044000183d0310f100c4002d020042d00d103040328400ca00a003c140090030400081041a083d41824445400383d0751121285595070040d50300030072105103004100400309070080c5c01405000e008640e1030902b5030b00c40c45601d204181440700c90329052010f03408103c2d036080028100085912aa007014100750701d031104460314910001c1c8400d08a902c40e0b0780503500f000442402c5130b0b4446030b4651511882c07201c45200a200101810a2107506544a0101c1c00d42100b401510b80964121400c0000c0d00ca240c10151144100c510b20b50384171312a903081411301400c56100380340d40052004050703c40c08100342e0042d24500d000030030546541443c1c0803220a03204841c68203080c0d00d070b0000f03000814005500c0501c0200d89803d10340074044d0b881005071a180c0f05108880004980e0321000c04104000c403510a1400c02d00e01c2c2c0c2c00140710b40310200b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 211286079 1250 211284829 211284833
    0xf0c0807030810140d08090d08130e160203030105150f0d0609050a02070c1404060302100503010e01140d060b06041806030204150501140c0106240801090e0c010e0f040603 75
    0xc6801600351000d440300040d103581640446049030b410240c5c2c801d04810341680000c084001804051000514030790500d601d54440741c24940c403030000d43c18860003200051040413000c080840d008402c3e00035200345003103010000713996440180162480f641e100c1c10f042ca9054510000c4030b111944194074140c0b1170395005014405401a0302038000c80c00d0a10740050340c400500e100352002035400c0356403038030302c0c40c94100c07080c024403615048150429203461022016071948945c00c0400f0f8481d5480e0b80c0d0b03075031600c05824134144040c0c000c2110070b566604140c7d107940c1e5440048110710b410260015010f55102c0004401d031085501c911103006050000c0e14245603590310110407240241d41c28000112003040740b820300700150140074080750122035408605003021014000030000c0100014980c0d480d44230550441244142d908240000340035080003880d8009006401000c40c080c05011070040028a035448480b40c465107410040b55440314001540c42c203052110184004d441041007035103038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 211287329 1250 211286079 211286087
    0xb18060c0409150314010f2d0513060e060118090c0302060a1818061a040605031009090b061003050403053702010e0d0c020a03120509090c0301080c0603090601060f0c080703 76
    0x1c800c3d41c00f500e13108901c444a515040c6d6800c0c5441410308c42c0c03103022044241c0b000240000b03001c24030843c290100300d02c00031361b06204104000703070840e009103525803500ba03484c24036504218401d401d0904000c841170029038034000c8213007a290704032401602c0f04513644040341c0c051a20040c0020520354001c0c00501d42d80501130141c1c015642102c18040b5580340d021140d80415410802d101c411400c01c410860b10744500055a0004803201c41265600e41c0c640500090b100d2010f001c0d40c924002c80144180f900e07001d0f6003015030b819542404e001ea443c068a024105009000d0001e2000c0300e000012206101c0f0f4024611681002c103408480401d10214028000c0088044618061191101c0c94895a004080b4844c00550080880305c00b5802e640c3c90446010f0b046041c18140002840419802d5540500c010700c102d0491a885480f50301d401c40b6a40b030404040840e0340280c2c002c105124500d174021035064190307440c5082003c814942c0d03610844503204008009801a8000b1a28800b00360744 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 211288579 1250 211287329 211287341
    0x6030c030a140c0d08091507060c030c08090606010e060c03160507030203060c12060105090409060518010f0216121107080303040303050c0415030e190b18060c040915031401 76
    0xc41003103421010f50b000c14400604140600a05003000a002e0340241d4a03005c4c0d1050448005d0000290400b2050707a2208240c6980718002408280c4940c540c0c900160322202141d4003400007001003a40d400e10b0400070707000c0c83c7c4d4044024012140016035a40010081048894441d0075012240c0c900301141001070319603d280c0800ca1013406140042189641c090017514100f03800081030400d182c8520b401522258085c021441d0803a40b9a8480c0c07011446500c52507124042040584801d41038120125085813a10341690700c2e05441802134917692a050b0002c030b02507030743c81f03a80b040000100140c02c4d01c030500485100401c910075050045100700000c006140514030075201401345460300310307a400300c50003a0701981c41c0e0400e0440342d4000403440b0f03400c204260f041060a4801026242660070348400a80005449011400d1706005848248288040d00c1080b072a000c0d160a042100e44987c5602ca02d1003a80091601c407441c20b20000002c400001c000c40d4403642c0e85c9420303461758500c1c9000e080c07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 211289829 1250 211288579 211288613
    0x153a0b1c08040314060601201c020d1121070507050303030c0703030606140a0c030e03010608150a050f06150f0a030c1b02061903110a02030c0601270506030c030a 71
    0x151101c4d4a01041000240c000d0040605840d00001e001c20002400b4542503003510101451090789250600020141c0001504042d194003900070420403010180583d81c0d0f041a07c441c541c4102ca10802c8440000c4005400c0580c2008280c0d6a03a2503003003c520308100d0b90440b9070b00d400300000303105c0d0000b0610002d082d0079102e51005e00c0215602d00c1c06540c0030400f02c05404600508100044059101d280c0c007450043c428100f041c00003414034046030031035009800410703a56003c0c580034048404003014066001c80b036884140200d1904000c2419240006003009002d608813542a079001d40262041c1c1e21aa01054003a6880c2c0030b4241c0002c014080400182e808161031112903403021155503010005d01790003070001ba10f02111000c42c496000d0140407a081095664156400f5000f07403940140540ca0321507000b5900c811a0354513080c240701060340560340c01c80800b83c1902005810700d448056884424100250b1a683c42c000b19062441007064203074036018402055080005512024414032 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 211291079 1250 211289829 211289843
    0x10050c070317010b160503070b040c08120936071d030d0c030e040e030f04030c0609080d0302160b0f160e01020615030a02153a0b1c080403 61
    0x5070401402d0616004280079460750348070704010720511410b00d4590322600c0d9102e4412249000d60070344412250820507102114111020241000407045c20051204000017084d000c0b850408813900062a004902e0720503101c5000c0c9001000841c90580394209154240009103006864002c5005114050b83c0311440400302801c0c10070381d0b06080019040c0b0344200a0f8031109018a403e480c155800501480e003243d01545403c804604001d0a201811030011080c90321500c031030030340c9041c00800d070080c1c01060402810b04030070886954005200c1d07040402078200107a40354001c03c00700b9140040b10a018002c1d002c5401406580040001c4c21841640c0700c43d03c0d4490010405012644251003010030340c0144c0c4034a010400d25010060280661040181194210701aa0740890491841c07801900212440464910030401350300f0030704000707404c2d60000d103284118002814000142008040074030346a80e2202c0c07103003a0302c442c84450b007a001100000c404107403031458600c031580d0050100320359030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 211292329 1250 211291079 211291097
    0x13080a061109010c06050907050d03080f01150203120910020a050717090f041a040504032003040612020315130c0e090402090c030403022404120c031b0510050c0703 72
    0x11400680c282c80a41c03030165104801105103440d07003c06468058a0340910b07004014002170381d6130301c00940c110b0f018480c3d100c400301407030f101c4140261004164088031340b40d104601c55418455020045455106081e640044543c880351a014900300b42074240c0002c85100040204990350800c1c0a41066481031040d06643c1e814103482c00014065620510742007003c2d41d46201c201d14007034100000b045001c085101c0300410543c006416208155010f40124000b508401c51421701e43e9080c48008032031074015071401d4602100105805114203115490a601102140603807410742c84101480d0360003460341c501140480342c075000420801d84d40308046440c000e40c0398114207255090610a603001058800ca50780c0780c64024040e980024001c0f41140a00389074840c1030a5040046a2808103c00a0109601d01450700610011442c4603980c14040451a180c001940c80440c2000007051854440c4540d1071519040c0d141c083c03071074030300441c00d4101000c2248071507080c000b80207000d000340c2d140828 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 211293579 1250 211292329 211292351
    0x80703030e0907180902090f130902031905060a0203070c050a03020d030f0e0c060a021207060b01030509010b0f010f0908010f02030906010f060801030b06061c0f0506011d090c13080a06 81
    0x359071441602640c91002120b08001707001c07a941c042c0c410440007400e51141500b2407400161800c003052030340150b4994a0751404190305080107000708601000e443e03045580f05036102e081c0e80b004002e00d443c034140d030000b00162503d841180100201503100e401c8403401815440d02070344134005141d00c10000380c980620640c5c1103d150107030196001545000d400501c05590a00105501005149045d4816000d40c1044824a100100ba00c01d00611000501d40941400141542c0010b000341d0941d03818210081b2142d0f8820f1400d042180c000d007014041480d0100060301c920306541d0004403a5407030300d10344082c000c00c2c039002135208030149802c3d1095681c95002d800c406500c0740c02094001400140140001150030000342e0300304100602d80307810705100c60301070802c0342e09440d41c81201684900041c205c10100c0c3c0a82600817009003050803048903041e8552486c1240c018400f8070541d40100440c03800c003840c4040342c0f0000020f04001d1021512031803126503c6074800d1044601e28900303140400c4c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 211294829 1250 211293579 211293587
    0x603141507090b042606010303020a02040b0603190f1b05030f01150203070b0705160f1109060303090d0f0f0c03110103020a051218030a020c0414010501050301120507080703030e0907 80
    0x140c40d41040d02a013883e0418080007170100240003000d94400c00010000b0740d01e1804c10a0303078000c42c441d50040070080f4040c410301007500d01c51a00076014805c1030080c42007142c600703101168110900900040e880810174030782400342c5248a4503000c2007410740701510a2650140c001d61240101090081d40c90f41e0382c501d15468407083c203855030010b070410302085000900c2e180009420400030716143e810200c1084140d00b4000301c0c0c103412074041c3c81e041c10380c004200f8243c03079401c02c030b280403560030b501d42c40c201000c02d8481c4102c201692062101d915040d0403c12256007008002c3d411440361019040c1c10300d00694601c08030b0100707583d54103080706031340801d6100e0f00884521004d5070392414201001034141c01c4410601510a00d038240002c4014a006042040a89000c0a15500804000c4520b00610040b1856100b030a0000380000c001403241c1e90700306080f40c1c1155001d0000c404000c1e01c0342000f6003410416000741081d8041c860001083c503038040c0075001242021100b1030360340e48820005603 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 211296079 1250 211294829 211294847
    0x130203072301050c0703020619020c220e01021209010917030403050904090f0f080d0c1103160201090f0b03010302040c0c02030c090603100204080109060e0615060306040603141507 79
    0x1c02480c51441e00d2524a520400203000e85910041c11943e045450354006034141d08101e0710b1544421000021917000c40d410400f4844407041030703039601407402c280c211145072a4105281181c40c95280e006a41c1d0070002503044504908500212400e14200a0100c40c06084400320554003100000820b108200d00034007280d000d564941c50707040c81d080707202c01404082c00c5092015141035024140950208412010400509216805880da942c451440c10740880b6915103144d01080405c08540517030003400821100d41440600b00341c2c104041074801242c802c4815004903000c4180c1c41d01c0000d1408460002d14143c0e0300c2164180942601c50354201c0e003030f402c00b0b400030b540744d03000c54002c00301c509244181070b8011307a025003618600203001d02048240c0c1d0142c0d010b80701684d035480d07010003030061a108028210560354082c01140c28a414064204008402214410382002001c61142d603140c0c2e1200c80115803025000700300d00c4844a000781c81e8142040341300b036031058540024100602c941018 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 211297329 1250 211296079 211296119
    0x509030a0503150d02060a020a02120a0506012303030403051f050c031603022a0f060f15010c0c0b0304020411091018090e0d0f020c0f0f0409060513020307 68
    0x18116a2102112480030059081c4280c0002d000c0b51003030050b1b184c01c4011f201c0c01c2c400f03400501c0e854207184140441403148026401719500202c0b480c0c03000500101d0282e04441c1c01c401c50305e800f0303498910351b5070300200031415144d03046c8000a0000100400411090f074520140007628400c04c84001412050f100e00b00c4078080c0c501c07810400109002c01c40c58084101c0e50180c41c0050038848030504d08841c8055582840c480ba1074842e010344982c00c2c0800008220101110243c04541820003035000303144d00140042c40000081e0500203656440b40320609045604000301d5035a10340d544561204560050350240d005505012200760b032694080c0407241403c070090000c0b180004002d2044035041010310030b0030303030300c003211440003c146003640107030072417a4150b401401d028401d4a8015103001070800d2800c09541200129142e1940c50080c040c0500109a508a192040103400540184000d10700188200c0c5840e0501c07003601d21081c1d034085018400e80486503459245c04208030402003c3c290 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 211298579 1250 211297329 211297337
    0x16020f01060f0e07020109021306091118090c07060c03020c16050105090409060f150503100e0706050f070606060e01020c0d0f14030c0706080a0605090402010807180807090c030509030a 81
    0x41083c040550303101680320f1001d20000415444a50014100880405c0c1070320200391140003d0144046600c240315880010006040c64000c2ca0759081c00e9101140d01b005100d91890000506030900ea40c048503145603219a040101c09000d40c00a0000d410050034107166102d0442c2103007040000f0210a810b89030141c5509040c88203850800c4082d05aa01041303944075100c18540c0c5200070140501007121003500c2000004500f410b090502d0000300d0018118058200301c0b101100120118940f0309803002890804d070307602000d1310450b0301442241001400140342c2a00000c0701a8000c600d000c80717603804d03401d488102d0348840c108032001c40387c03007400b602d5000c01b00384d003200141d02800d0a429a00707034002602c0c02d2018201010b070501009501403404101807a042045c508203d109040250904446014107820a600001c0454200505000038090034440f04100c20f42d030f01081c0c900a00840d4212a2741940380d04842020f40742100442011a0030a00810002d14002c01a55011a030743c0d5a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 211299829 1250 211298579 211298609
    0x105090f01090c02030d151a070b01091a210c010314010e040c030c0e01031a07021e0118080d050f01240e130504020a05030705030c131416020f0106 65
    0x140d20300c0202000c003c3e000961204005103500c026450060701980748459040c45103180c68035000605803c02001d41c1c80c2e4688041208500044001007480c4c151410303410001100c03402d17000c0b03843e4240607030003d1035401705001568000c00d040781509071821080000581d5200104240103405071001c90700308481c080110b40040c00322030304203086903601a000c0ca46000c0e1040d941e8035001c455800c1034012240043d0841d0048c0140320501141080030890b4010b001c4240c40e10301002034540c02040500d444c1c041c3c240c0c88514150b8025040149040050000700c0c4804005240409440d80a8034098848500b04800584441e01044200c1d040f43c2c030508544129281f540546001d15540010034400d01410301342403069500c426035a40607000300d0460004041c01c1500421010124a9104030700c40d602c0b8240901ca15100455240e100140a941e15100050019070603406003050309803071003842c1c0341c4100b000300b52020008004850300e055020f548003031241036000d509030380c407034022240d003210040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 211301079 1250 211299829 211299839
    0x30d021c06090e030403060b1f050a020607020307110d060e0708031c0603030905090a020705011109041503020a06050d09020907020c0a0e0c120403020102160809010e0402040e0a020913020d0609050105090f01 91
    0x23400c0400948002041c031184e400c4052400e0060070301604e4854001900841c541d80c841e0b0f0100281794018500740001c2d81420b0081e0380c0d01c600c1d40b020b00859400741210308194010450240c009032272310307103029027619071305522402401e60301d40100c5041ca18402c00340e00e070740d22443c00c24400d0f50140c0e034056940000c19420001401444040a8004000309600b0003020010407820b110340c2000049107003109070340e450b49400f000180c0383d166a0069000c0c84586c000c000581ea80d89080d402c507002c03400c101c2d0b10740e181d841080008281d00f07a806504042c0342410028400c2d800700d1003030a106c408a45100303007a920361031240190070045411816411081110841202d404080d45621a00c24030000d4505075402c80710700596040c3c5041150103501c0891455220f68020039407810b03023071098800310300727140c07a2610703500c0702e030701c1c06040c00d980329900040b50b0701e0a4581401e2440700c402c0103c400c1d961195600c1030100100f103944a0201041d24090002c41c007440d229842e24001c01440040071140c1e4281 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 211302329 1250 211301079 211301081
    0x81005010f050c0a0302013911120d0203042604051c05010c0905010f03180f020604121b0b18040507031806060e01060810030f05030d021c06090e03040306 68
    0x4400c070005201c014008032540400030420100c80d94420350001c107441d5807580040050450710b40903001815a0701058110080c1601c2d40407003221300034038000c101c84400114103414942c10300540c1041e0003000401c14201c4216400440c00b035441005080b89034000099400e0061314580464506200d04200c200410302e8014981541075245c600404204521a541c0720300311004826802c002c58090f034010819580c0044d10351004a400d4241400740c49000120301c1c2221001510040c0144c9030305480105540790003040d80c0180102c011450a520160700b800c514010420b4640e40c3c100f0f01001c00864415100010b580c0d0008140019068182c906c40410019140007025981055542c050302903030120842100d4041e50f000781c50000b1980e042000c40c10592074160030150511110340d00344031109040c2002c980841c2d0f0441050022900e20380340c424154890106486600b034000300703000980094034a102c10794402c0340c102c2000840d80d107541d038000365401a8103100940d0410310003040071500b5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 211303579 1250 211302329 211302347
    0x3060302100f0e09010e150a080a15020706050c03040c0801060510030b030c04050a0b03010509060f18010b0a14100c0c2c150915220e0f0d02010c08100501 68
    0x503d090040703504030803a0214040041c00d9100116800b480d10038848082c805040000c5180820b44091a51500300a4040c0e944c12000e14001c00c1d8514031b214054641c40103505442c001c0798451010b0005050800042c0c1d4070307420a80c1d081c3c961420b60b440029480d181441031004541c000351500c00c80080c03205080e0000e100040c2c0140c0c243c0940c0b400341d8400e0b03845101c1d4a10859052400240c5201e00b4810716007103942c01088440950700107070030b02560711400c0114552103444000d01400c0c4111848400703014104506050750001480b00d0046650101000300b00c0030403006855400074218100004c4501c0090000b0141607100c04007400d0008071450403680c4c5c00f0401443c0007418041190700c0503003550200300c0e50311642c500401541d155074901401076039000405085099a0341041d0070005a6529420075901080c10b883c1440f0f8901000b140c020440300c80c4c4460694188002c01c0125031b0b02d940c005260301c00154070b0848011502c41c02850142d004068003c406d42144e81080c0c010b444d5040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 211304829 1250 211303579 211303607
    0x50d03051014011809360204020307050c06010b19020c011d12060a0203090d080408180a080607030606020c03010e071a090a180c030c120908091e0a05010306030210 72
    0x805581644d00381880c640c846030091168041c00100007004112000c2d896411000c2c0480714014144040402c091001c6412141030b01100c0059603034407901e01c15200e5104492010486018200c0006100c0c0316000140c10401c4220b40da06400b0800558100c0e01ca503001020b090200b008824901c24243c0d0f0848055080314011381004c80b070480c4410006e1821004079000082c640d000000c0040640d003e216000d00d100060402c6030f56400c00381c1c0d0322a810f0181c01455120040c400160041c940d07500d00c0c1c11001880c204090303801508013541c00a010340707001d00a4101501c52441c0c0713440345080520541100740e0a120192140740c0c20012405402e000b00d1a159800c40d80920517a0001d0b43c800324404020300300300865209090024500100f6520058250000e05260484102c0780c182c004080d012421100100000c8207003140c9480405406035500b90b40d000200002100d114002640c00d00301000030880b60200400e91301d00044003500d000303000c0250090410600f07401c03100e00422100c08806 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 211306079 1250 211304829 211304837
    0x10b01030c0c0b0a110f09030c0a050108010909080714030309061f0506130b0c030a020c040c0c0f05070e1009200708180612010303030f0b06040b0d14010909050d0305101401 76
    0x41006065217503903005044081c44030400051001c0c0725207001c1001d00711206040d00c2c1da4100615080010305180c00501c81d440c0d141d51521032800410500004454a01303a00c00c0856000740841c04240f5940d403c121041d0507140700b41004a52180440180c070584030000c41a181801403d00d4203011098001064080c50094004e1000c1914241d5101504050744820000d6840d654501c000034544480c2228185c004c0d498129411181540541c5000c88640c1103101c02034914041d01c0c2943c9043d44603031000c1c650042e2601881001d40c44180c01200321802c2042c140400c012600a089141c04410220500580c0421138680000e800c0006441c0d291100200841c0b62200b00c400300310650301a1340c0d13500200c1c040c1801842015010320410407907542050003000740202680101b0b030301d40b103680078016107810041104842000d003a00300600007203003040008211b503941e400000c050440b8400c201e030607005114801204038072911490303110314005851491410f10b01031002c098000c069075058100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 211307329 1250 211306079 211306091
    0x406150320030c0411090a150f0e0d2411040e070e03120c0a061107202805090c03360319030b01020c030304090c0e03070308030702010b01030c0c0b0a 66
    0x2640c0c135885403000c008030382c10a0560399503c0d40100240540350b900b12107100c4107015500b1131000c0c1d00081065400d034581c00c2c200c02540c056000202200b00c0100d001300311031543e40c8440844101c5801409600fa200328043c800302020495503401c03401079008110b001800c12000442d803520070010049188405026a0006d18061807415110b030701c22521441d041d88600310007004c0155521514000e20f106c002c08904001d1995500000c2d16100d1050404030707880e0b00040c050560701c0c50307a1403c08000d808000811411000c00b030204501441c13046034410440394000800201d440e4048078810004070000e00d4003c2800d213a80703d080401c4003454030305004d100d141001e54003070400050498031210184109940e02c003d400034140c40b21504402d045410020711903140b92000019201034610a100105441203c05822694045d80e10a803580c54852034100200340240301c0c0095008110503802030111400b0750005400f901c02c1c6c0c81c2c0300000248030b10207240110b0000d10318181c12400b43d240210390 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 211308579 1250 211307329 211307353
    0x609170303191103040605070206060a05010806090c16141002070b0f04030504170f0715020714040b03190b01091116020d0b01091508010e070e0a0e06040308040615032003 75
    0x603d42007154200c1b86507507100309011030507404100035680102d08403003800381c050510300000c1814101400260040d11120f000c10b840c01122010f1301e1980248002d032606a81d140c0c00c244c0302e040d82c2031880c030b48180a81540740e14100f0040c001c484209410031102d420b19212501c02c800311000060054041000510000c83c1440080390881500080e08004061311641d0300764207401c00c951035020300c1c40c081d001400c45108940100303094003103410350f00141d8a041d00d2074012901410300e401086a01d4010a0004044680d14010300d1407450302510030700005a889484003000c90391502c100c1da82d1545d06015042d011216908046c00e5540b02400c0320081c0380096840318080407080e0400d00308503071980c040900404050b268000181102402440480c1c500b0384005e807126464000d414035001084001214018650813425082c1d08032401c90b080c0380303014103000b0211001610215105800c03c01900c203032100d0058000184c0303030040000c5080c1c40a14416002c03440c081c0d180300b9003500a004c46011 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 211309829 1250 211308579 211308611
    0x316031a07050f0f0d020310030b0f091c02070f0929030709180c090506030c0303090a171903050301050f0d0b0a0c09090e030c060606031303180e0709060917030319 72
    0x4024150090059181800c601c2c00700600300006100c2115055807100b0043310b03440000b4824100d400403030300c0b100302d20602c0e03008a0500070b198000710443c4140c1c1d01c0c00a00324109a005050001a02410322402c0f148016109055036450746000d0b4107030702c410403c1c000701c5156400b0b80060360700c220241426102d15901c0d03110440e80356000d480b1590f0b48401300241818107206440407886c08902070341c649400c0c00c001a0100c1282d01820160500c0811141010001000b610310085007488441007091481c1c40c0041c0070b6031003401a2030103007146001c105c540741030242640c64010362100d042d6509a13074005100000b0803601030b0400401c194a031001408004521900c0f00e0150100c014540e2101c05080a601e0014081c00544c003600742001004501c00038102881407056143c6840d0402c012418040c01141301c0c103800c02c07c1019180420301c1011071300011000308581d2035489030f00040d9a541a448007002010519400030b40003000001c01102080284065140703801c0c400080c010f02d03200d40c1c12 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 211311079 1250 211309829 211309831
    0x714091009051906120b13020616060203100501090b0a030e01020d06060305010816050901090902010e1c14031c02070c0b0307020d030e010b130506010309020316031a07050f0f0d0203 80
    0x700850038910f0382000e0700040e030700443d0050401c284c3c840c40e4001a55407001d82a860051004848100444c070803011503031038504840780501e0203000c1d403041c1c019505001009600c07e80c0c0700301700340b140000c00145c2c3d940550380840c00c07103c0c16502203082002c40e600c00e5015069162201042c0e55080180012020462084201404403a80d002035298103103d40c951505400740d5007000140050746040086540d82c0e40000c2c1900c84800d800b0070072503201e10041c3d884c1c07080a4003565100340b24421818814400400c0d2415070340c007405492000824182d20740d030700c0788501c800280480444030b0620302241069001080c1c003030702c40c8500115a50380d650031501c4030341084c1c62010058020003c00c1e420f0701d40c140030360040203031040000c1003603000cc0c40003d400c040c080c14400804684a900103201a80203510015103030350040c0681d84259505a02c9036a0100d4a000441d0586940482c40150b04960390360103200d80c506403200c618200000e09800d42c3d41c5c00400d005031340701c2c0c4108044000e0f529140055 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 211312329 1250 211311079 211311091
    0x105070501140109020c07140d1515030b0702191e0c0b0a0519031109040507051902010b12010b09010e040c150f120209220902091303090602071409100905 68
    0x42e2500b00381d0250f24181800c82c0e00004c402040302040c034185da40c0740e0517000c29880c1e11201c0704101581c0f152000c0090001e158248c04a80c004800000610040d40b0073786104a04941c01d89801001c5120040a004154117015000905503d01c0d0144000314002030403c2c03901030b000038010f4654444402c680c1da8402042c100c0095800f060750304203140c007640201410384450805003d01c40444940000b280503104905115944030808150441e0142d02207400d9050142e030011400c40e040315010740602030f40340115005410160b0600b03413001040c4180f442101c0010708010013a413800380b5142401c200030f80207a030540c0501138002030415071a8200040181c0035100d81e070380d59402c0b9030090301009003588040b0b510750041200d5000c90740e409000080c6122024034864510300c0c45d81c04500148041c1070025081010380007802500c0001045070010390f40300e6a5030b080e1445c0c440c2401c82c0c80703100c07030b10450702501d02110300c2d0350380340c030344150364940c0883c05144252400355905507413002d0307600940360 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 211313579 1250 211312329 211312331
    0x901051620030607120b0105090301090b01050108011403030708180604030c0501090e091f022704050108120a0804021912060c020706020705040b0d0227060a05010503060105070501140109 82
    0x41c8000201e05003480c1140c034004502900542c0391000004e03110b80d40e903c9600e00c2595032502c0040d0260f0040041d02c0d19080d02500800000c4410b141401c0007050a000325404508110b0002a0f03803a8001e403500700700a07004c2c001d1828181a550307100519003000e404000ea080d802080c10100da1600800f810045010b030f00f8512500c0c4c079242c005006119580c002050810300b0008000b0115000142415081410031741c00d02d4000011590400034068500e400e00c981d1407440ba4503101c800944900c00115404480400c20750b6a1901907543d900310b0200c00001030b81080c0004900f15014014144d8020b002901010007185038400140d092035941d0828907034918816450700601c0050312a40c18915410300040070b503a42458000380d9078440905c1261710a5403502201815601c2e60004015643d03406416071100c00320050450803103010300b14003004cc413508440040d00703034079187c7c0c42c0c80c045503810f03100d0a1642e15030300011501c1e68840d40f41511503640322000c8c0c000c283c050701d070024000e01c08240 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 211314829 1250 211313579 211313603
    0x1f02070f08030a11090105090108190507020706021c080c160204090b150108010e130503040806071e03180201080a0e060408091009050a050111070b04030503040e090d0c060209010516 80
    0x448074111341c542060710000038418080f0965603600617086501d031910900700000c4c03a0303480c1d0121a21041002d071000c80464241814441111340001c1c5540c2541d1013174081d50300001c40d144102c00ba00d58030020100000300c442003c0365400c0170080003032028007040040c82048126a0700030400b580d032a12001c44c1d840c081c08042000740d01068030700401c01c940034600140c4035490100140d84020019006401203910030800c0405c1040801c122002446000142e42082c41c104502400520050701507012040c101c980340106a8424807424032441c03d100303240044410160011525558002d082990003503540e801c0190300e40041041d24400da02c510f000542c0c43d03030305401380070610700340b11004414000c12800038003160303641c001a07505407002131a088074101001020b10789801820380c0721441813640014048140240407004000f0346041380340c2480c19407103240b400b581d40d0050350000310000300e0b42d200b1600001c1d016001000b0181c4149440c034100b1800700205164034001c000110340700180f4807 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 211316079 1250 211314829 211314841
    0x1502030307080a020315060309010b09010815070908070e130f050a0c08120403060f0b090405060901060b030f1302060d0c09170a350703050a0201050c04081f02070f0803 74
    0x803030030a51082d503e800a40c11800c103808041035801401241c02d1090304040009024803100b5405058492030003000c5080559549140c42d03100e440a001c98412402c1c1100090744550291a01000300c40f0b01800a1488502c0c2803040d00d03417018050b20314000c1742c0a840d071401c0800c04518108090f01d0084001e04007145051800c800f1220b21503201d104203400c00161200c4012401c01a01c1c2220781268022803080940720085005140000600381c3c00030400e802d00081c0b10700040d10740d00c1880e07010000c11119448030000c02c52408203c46000b100b00d4403500148085120125048400d440502541e00300440c0c2000042507039640d0a0020010340405030410401e40c0544422080502d03880240c48010529110790144a160380e00c42241c5204075451480c42c441a030919501000a01d00295100d00d01c03482d005101e507104843c600010b42c01c1c00041803041c2c0101049500300c500c03000062501004600040142c03a00305090078181d65400d01524020401c24401c2c40e002d28416070300f1559078038050f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 211317329 1250 211316079 211316087
    0x80d060311091b160c080613031106040c06050705100203130c0504020712050711030102160219050901090c11011b020f03070206030f0a1b0509040e120d02090105041502030307 77
    0x1c1c004954500d000f4109506440389504a076005509421403100c120802e0815042106140d40512828821601000071101000c1181c10102e4466561210054005028143e4030881541c0162202c1c8010720300b0000140108000c202c8a88180706403029400300b1240842280c00450710040040340c8030890304200400304040c100a818100c80c2141450600d442e00120f01c20103104410a000c0c0004813801880070410a0719910a001002035641783c46000801c64801084801240034080004d6412411250b03c2c191109588010b410100903070700c2c0440e20005440100c440c0b405116000740f4036403610200b8000e8504140da440b07001c200b4500b0305100280f41800b00c03c0c80001d19001885224016507401c42202e40280006070a41041d403613006540b0014001c00d590080f07101c00c02945030701c0f01d60b0030101803c540c0e84221804c100710b20606040603141d40744286030002805080140051280f025030252000c101c0625156042a4940c031102c4206100700c40d4400142e440801004685944 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 211318579 1250 211317329 211317331
    0x41803031d0105090c040915050a020703110a03022d01061403070b0415200102030a0f0b0604030206090d0501061e0f05010e030307021201290a051c0b04080d06031109 73
    0x1c403800030030003480d2038148a80c85808000c65184241c2d19808104140720320818107498a11f89050300700041d00b894a1140c0003980405800c5010a0410b01003000170040440c0b403081c40358140d00a03120903500c2030801840d001d1101c144520b01c00940c00e0100303c180c800d2150001030003915900c96100c200c820101440c0c180f06034040391031858104818014801c040d05e0b81503075411641450700d500007004100c0304c4010b10a200189d85c030b40c4048108000c20344141c00050b0324281c041c00c200310240e1282c0c2404501c2c800e42c04080d40000d0308000b00714041c100456044491070103000002040c0ba210780c1a442582d80030740d04003042003040e9005022401c0b0710205030300280f40908002d01c07084650b20119442e030040b5003010340b240300e40c6410038490704002c0d00140c800c04207000034038110100480c042d20541c42070131602401200c8920b4003140c40d04000401c00c20407490080800e8180c0015507072882c090100501c100c030b481c8801d210030040d204090007000080e5104800d900701c1c43d5200000e109201c2c0d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 211319829 1250 211318579 211318631
    0x172b0e0303041a062106040210030509070513060302061209010513020d030503091e1516080f04081c0605090601090308041e080f030301052112030604180303 69
    0x800038000094044070303220790f000080300c24a181d640c1d1001300081c9006801c40d410406011401148142c1a00c0070440612486c4201c918610360006d4200c00c2702250000c54295501e941b1019041c03256141000c14100401e0240e1004070f085501d13070b4003013540340d005002020742c1e842c1c070f0348103011881c0000c0c020383d5800001241d41300351000d01a0009007611800d040c0c0038050040010210f682510b0a021410307842e0200340c2d505180c001c40c940c1103984e82c4400045601100032907400704000c03a034401c10001c030b415010303542c0c905240c640c2100c10034080790281c0111100c5108005410000701095400c0403400c2d50440b000511510b0642070280c0020014031150400240c10f4090002500d440c09807802c0c0d0b1240307020b0341031942080014281c05160ba03002980940700c0c0e4080092440700000040d03060390300540309601a07100000000b407604084030000030b80380c0c000809891030b07413000f8005035078030440003400400d9101200c3c04c10034100e04c003d0000d8001944446600c280254048442d0514903 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 211321079 1250 211319829 211319833
    0x3040303080f060907030b04021303081314030604120c1203050a0507050a020a03120e120309010c020f030d09031709010f050106050702010c020d0f0c060801050a0918172b0e 76
    0xf1400d140080c84051000b040e0f1400d1541d5208080f4950f1159815901c403d4a04480c0d000f005071a41000d03448d9800407403401100b04c41c3d50001140802c00d0303c2d01c040c2c260030040c0091840313456545d030703400d070035600071741c41200300000c41c180000450f40068038940d4005403a1000101401d05844103020380e00010204014844108a041c0c509a070010f8941000741c0c04d407502c2d04c00b034001032941f40c0c003505012090f44c01e2840b625070b11103c5035016400a50244403404003c21506a2110341640c0303c25582460031640e80041c041408841c90503080031010074480e00e0201e1946850b00000501c20310f0941d0f698055a56482c513441d1014910700c12280074000c40c1c1003050402c0640d600007800c1418801d0000e0207500341c04281c03020080d8100e1204801580a16400311b083d85070f0b200204240702c00d02c11640300710b206400028130303022a4443d04000c0c1d030720381103840882c2c900340e1544580e01180c0e042e4084959010001110351202c010b02c2d00e0325100c01c04254080c0c4109204918050750410b04130f050f026 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 211322329 1250 211321079 211321081
    0x130b09010c030c020411040801051501020127060f02070501021c0510090f060e040b16090b0706150504020d2301150c030215010e040b0f0f0a0905030c010207030203040303080f 77
    0x29a030058010780d440e503854904415202800e20115002d46008120b13840c440358007007401300300c122046d08107a2040f0710f0301640c841f080c41900012426201006a2050072070101452040d10b402088100304000d8044c2c0f4020584050382c0740c1d42d1003284c1c00321409840076580442d0b0f034081da00710080c0f0042002120542484a81414000c504c26082d151041c01400741c0c0d00c12070000e584500e500070800400552100d0800c614041c00d10340030814044444242d018840d488191020f40034041001c107840e034000d03000e8144221a594030380204120404a003e16510250000d51540c07140024425403501031000b0928000c0d03159801e115040d2080c840158980440043c05401c50404c1c0c00c1440e10502d180600c0e2003001f03414240e040103480003980841446120003c6240152010742c079008030b200311140500703540d84038201c0500000980f201d4401e1144403001c20756101c0103400031f10865003d0800e8914114854100b60300320b80c032440e01280540c101207010030034160091815035000c44118046045 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 211323579 1250 211322329 211322347
    0x1030b0a06050109150c080a0806030d020102070f0f1112010608190812060a09060b0a0e030118020f03031606051503120703030203071e030506090a021204140307080f130b 75
    0x300b003428080c0116580c0301d203c0141d20301d40f152000083c4113421007c010b44c4c1e41d00c803210042c0070360b0040321454080d2156090744560300d403052003242e90399500440c1500c41e080090342c80b0004000c1041064505400c0041c0184a80d42d4810b81581802d50903c0000b074201c0c940314000e803c000400c030903420481c1002c04d84d01d002c0b030380da80700300d580051320f005101401d60b4484000a84422060300300703000301d80c6040c0c40401c41303011510040590000c541c80f0704206031a807800305400d80c0c41e0b400c01c03000410f846036819401270800140300140c2da20700a060b41d00308891002e019140c3d035049001604c40540b10000d108114081c0001d4540720007040e030140058000c3e1705800000d42c4100a00202010b070300000040f07881d449207540031a00912900d04030744508c44400000d001d004155182c40c42082038602048000c0c28030700c00c459000303400d210b210a80e81e98070340b203081c4035601c600032100782d034001000035034001081c3c034000302105032220007aa5120070040e8101d0b690401c103504820301a440030800c0c022 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 211324829 1250 211323579 211323587
    0x70c200616081c0209041118040509030c12070c05010905060f03070c0213090605062b0503122a03040c0e06040e0105090d03110316080406090b010e01030b0a060501 72
    0x1692a280d80146903800e1807a00e00306560348540d04261001a000450403910200650001d0051072001c40d07040c0004081e00144426900c10307451140c4050525004094480c241780e040243d01c03404060590781072000c0c4080060500d20140f05c00380782860001203138010890740100c8007018184c20719003102c80e542080e0220303d0500c610100c02e010100080001504544148112840903501505045036200c080750364402500170300e00b00b2540b0a0416000995505245181c0240d5540c2400203004084070007000c0c140101241500f074404e40030420000c00031501c2c03000c9080c010252444803602c01c40c400b0494101264215108070008103041080c040130498080c1d1520584902000d0f48005071070780d800082c010044900044665404c200812003001000309003000f0014003034a040c410301500c4890000719100448030307035005541e0b402411f0304a40c8601891703944144074400000e401c4400e52a0545258400d9204c24079881681c0c0061080140b1401c08036040926240148041070070b16001034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 211326079 1250 211324829 211324837
    0x10506030613180b0906072d2a050d0e09060f19060909060501020c102015220b0c2a03040515040305060a15080303070c2006 55
    0x2030321030448002d00e00d01254069200b00c143e8006031007420480d8405203001602084c04450075131143c0611000214640d01884e20808202090343c41c00320349104c400000c00c55025001c0d441c0d020400226520311116804c0840340742002510b81c95001031001e80c1c50598600038140303000104000c150014140345448560000c0c1e0410400c950019200110f5400705e400003000c03100d4640e580ca42d03401700280480c0c000a0300000c3c0d5550f4041800309a0b221001a0381e07400300400707820f41048403140c0700c000345c62150080488900106000d4416507840f20441441e20354100340102640190b58180440200b0103100314422840c11842201001d010b03866a038003260b80100303444e40c00080000d40a1210104040d440d002500206d000110044407001c5a65203400501800f0700524000001c00d0714004c0c1002600c0c12258004010a002e0740d41e05c180350050600420840c3c4a0b48807014080b8203030300244080c40c0700c4c0c101540c030116024031350308220301031441e6492003a030304141352800d41045840750f50490b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 211327329 1250 211326079 211326091
    0xb0402040b040207050312010e01080c012a0c060905010206061518010203090310060e060102030408030a0509040f021c0b0604060c03050912070303090e1005090103060f0b10030605150301050603 85
    0x14280c4a00010802a12600c4c000503c103020000d01498894400641141698a14291400145c0e00d803a80d4907620302c514842d41e40451114039000707034200d103c8038402d65401c6480011200b0840c80341d407080200304144d040039011580e145000d016550f0304000440e40a0401ca807100ca03814504a4260054450305d081800286000f060324405a4000c02c21201d1404000e4216141440c8203001c45c001070000b8042c00b0355902e01b080109110758400002d48058403d140003940c60626450130980c1ca960110040c0b503040780e1100d40b000b49102e411303c060702c5400c0c404441d41d1100a10292010212201c1c850b805104080c288800e00071150b01060a5650341d91508010342d07119400c40006051580c0c1d190a4100d9100e06080030080640c0b141c1603070111903d40c5101401ea4840e00e10803910007240d03016040d080b050703550041000c500160092006a060740d02c001810f0f64411011401c29034443c01d0000202e51101e00c01c2015041c0500c5000c0e520410300b1041e0304650414000800512029210f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 211328579 1250 211327329 211327331
    0x30501050f3a03030605030f030a1115040303020307020d031e020706020d060305073b0a020c100c09050315011a13060e0909060403020c01050a141803010c020a0b040204 74
    0x42c1201c1d07140100442c901c4940c0c941148082c11401d031440304952584000460010741031900c00a080d040005450060000000145051a0074001c0c00c8582500e4030350703864114400c0d20801e90502e101081d80c180540d000b550b01680d80d01d41500c000c1c0c03401d00e050804800705842e181c0c1130803031035503042103501c0001a03110016907540c0b99401c100740a406118482e060180c9081c400000300640022000122982c41083d10806090400001c2042e5200300344202d04414a00480b650005400c0300d0592210005c1001030034800803080740c5203001c0c10f031300d068035526995940500795140c01104201c000c0004800400002d100c00c0c940303041c00344040c4a8a0100c840b40011250300c206524262070308580f0043c4103545e840c1e92102d005202d24080c40206015407048004148941004030b24944101d4240d0000c01e01e151214004480551100c12135000b080b64120030400e2007645203004100d01c0c10303400004454510090201400c40d1603a24094040d0341c003004d04600001c40060b60580d000340c040798 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 211329829 1250 211328579 211328599
    0x8070f02160e0103020922080306040f1d0f071a031003050a0321020306010203190e10050d1a03210409020a170c340c0e010312030501050f 61
    0x2805920341400c0408800ca04501040082516601014141e048034000c88042c8200d4a60040c18004202e0303164101140340908090003010868103c002e6070041000b42000440c0e1103440d114070700720f03055030304c00f40b02d070b41040030043c0e0160b4030402c010344500491501070030740c040c50108a034aa203000c42c100d070030402c81d020002810b0b904001c2c45520007190000251801d0040d0b51034014018040000d0709464401c001001c2003071031542d442600c0c42880180c00451134410102c0c0e0b10709200110841c0241040203a1054207039944641c681c4104a03003098507596220782e40c01c1c100605407403407103690715140c0c41c00324078868040d81c00041c0c010344802c00c201248a44040143c801c404c0d88556088150b4190000450401d411307807101a201c0c6c218150a0a518940c94840c544d41c024402c54080b989800001802203840d1400c03491070424640007003240c03495040441e52008625000d540c030282c0d030041103034010418880004003e0280160600e0208010340c149030000d00b411800c03401c11405111004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 211330935 1106 211329829 211329857
    0xf0d0c020a091401210f020f0f04020406050408010506090402010f27060e030f060702060106051303020d0807050f0a0302030f1c111c140a0c0207030b0f0103031d010807 74
    0x14140c800f1001150200024488103801465000b102740303404405076509c0740b000700010311840d03c13869121440c002d0801d0841c1c4005140c030b4010300e040710401c00141e0b4484062044a00b00b4101000405202c10800d403185810f08070348100c000f0710440100e201600a4191110074108504550080c444d4113440b0342c503180140c4480703001d03911a20040c054240100003912502c032501c7c11161b41140c0e2500003e20f01100b204068884810004030807050017001d002c080c01c030300f50403002000d0172090360340c0c005c0d503d00c01c5144400c854003002c01c4c164281700d0385242d22042c05100710000e002940200318008141d500481d01c4165080980f484c80100320194040c40d045c1408480802015070f07130700000c010140644428040c110b0140d003c0c0031001448250440d4040c00080c180c256841d8103610700640f80910102c0d0581071041c440c400c0303c2140c4e0340002c07101d03800a00362a01854601da04 = true := by decide +kernel

theorem cover : BRFrame.Cov 211151079 211330935 := by
  have h0 := BRFrame.cov_init 211151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 211151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 211151079 ≤ n) (h2 : n < 211330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
