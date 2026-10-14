-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3746
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:33:31.298131+00:00
-- url     : https://prove2.me/submissions/f709055d-f471-4448-b8f0-ee6fa94f2193

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 673561151 ≤ n < 673741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 673562401 1250 673561151 673561171
    0x2030f010608091b130203011410021b090402040621170a0516050a140307060e1504080a0306030204060b1803070b0d150503070b0703020708070305030d1a0904060203 73
    0x40c0e88594040d590407500343c403080c0b400da001c1402c400e95400002c0d541d213180c4900914a2402407807144000042c0ea000360021f001c0503028101c9020642010a0300342d01c2d80140340042d08403400f013140d18000f9200b40e02c542c6849010124040780c2507403981d5200c200502101c8000c00407440c68005480110b025194040f9040300d45030790302003424400e0b0000d0710640d95050f03441c00d241058103146000341c80e1240074281d605010b03034103100700000c11183c283c60b40740078204080d60700d40c4a04e0511a003212104d684541c1d0b036403c15010017042c07903961a101d540c0554020320303850f2116503a600450080201c2c0d000250070603e0800085501c807003a0001d08200156240400c004400c4c3c6010300d510307029540f064240506092100c10421070307181c2c1140d44400d000503000d98040c0c0d59240041c0c81c116139a4400210000000b94070740c02c0c1503051101034013428421009001c400d20310f5446603901c3c8031380002c02c80078503528485414444582e0107006102c0100401820f22801c00d4105a00203510960f101928 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 673563651 1250 673562401 673562431
    0x90606170309180a1d010b01031103040b010e04030c0c3002010c0b1306020f090a060f08040321020706240518040f050d0201060305070f032a0512010203 67
    0x103a0400004a42261001400b8002c014041c071204031810800a0301c100301d1240c4442c094050200c040703103585200b00d0032800205144420750005411605401c90f50781695104000700008160050080d604440b0b800c58042d504c1d039582d040448800d245040e0080285000f0790000807403070312044c0456684d4002d0703121041968030001050200404015009000c0ba200d0060140401d43d858103240e4800d00c240300040c4220030542c2d512003240d015410024020030042509100c40c20000d00500142c42c860400100c01e40075000098200100240014100003104c01d102805c1d000b0440b40044100400009544421641ca0504081c051040d441041c001000c410200050161004c0c1c004869019200c001c21070440d41e400c40c1850310060003501c0019000c041840000c0d030400254502d03444035800040d5036419480d1003030600c80e2550041c0540c000070300c024400301ea003c8c1961031550144618a044801c1c0c0c200d08108a041c041d0310841d400351120128140515041d0003c502c50f850328110500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 673564901 1250 673563651 673563689
    0x20d0609032309100e0a1e0605070b070e040e030c01050109050a0e10020906040909030f120c2c1801140405150f0d1b081009080405090703020d02070c03060b03150a1806090606 77
    0x142707401072800140c000c0d03940a0204003414000d00c4443c42905000c0c1003c20b4400300340381098038503880945003a0076603545000401501110b0312607260031a180003420f120fa6190404220f6480c0700329145510aa5800101601c1582d141411100101030303840c2c0501100142d0f04010b080c455006124402142c0c1101210384803004a01c40e4034102800c6444031614400043c00320000b600a41001d07034000902504410700c43d0380c4105401d804842200300b00c0000d5814900ba850482c6541446180540d041c2800d00c020b01d441018040a08842a034603070f02d145086100181c0c40350081030000d0a100c410310840802103a460030303650161a8008100d0340011010405901164605000503010100a001c1440249014103400303420400904d40541414510070040c000c81e44042c0c0102c401802d8507000f0820058903002c0c9204006086001e000601d0f074031404c10300d42c4a00240111401540c640b0140c0f0a0741d0034449081c00d00340c001c407003000015400e04d44000245103c8c00341402007030011142c48 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 673566151 1250 673564901 673564907
    0x819060515100c02030703050f0d0f0306211a01090e0d1d21010e031b01140c03191503020f091303080a09020d0609032309100e0a1e06 59
    0x800850241069074802c100c2202102e070504034207001c0703030b00d400b51901c008041042003081903010241d000181c4182d000300d00c0b01400c651a403424050526007052070820100d4540224a40c07602d005020540030311300c42e0f1600401910034001c1c894442d04001d4008201101550b10032a0041c1c645000c542840341440f0041e100305400007140f5540a8142c04c4501507820319040b400b56a021200c140c00d41034040054480c01d4840000e502c1d2001d92010400100d07034407584210484074042c0c030000308040c1821160140c99007a00501403400c040e0f001010851102098040c14401d00166008220141d100c042c403055803403481c402a032141d82240d020100c00d02d4818a05070244540b4020701c0900549603070240c0c2d43d0350b0000c2c0429481e698a4a210015072030b25007601c0340c0240b040800140203007592601500707804403021160840019800f87d142a2350000c002c0310101c503811100c58424a0a00e03a0440d80e1004039000160415040000002c0f512003105d00c414805840100142606031152011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 673567401 1250 673566151 673566181
    0x290c211303080714060f0a142208160c170303270a0209010e071403070c0b1003020a030f050606031603141507021b030c0d120908190605 60
    0x1410485036444810000682c125000b0000c2e030b4031494100d0203404c00d28240e11300300345040321882a604d000c2c00c00c010481095100303441100c0e01c60007228480d410030790301d009070500015282384d030020401c4624000b8091154281c41192078400101904d002c07044c5800070a4090341d108106c400c3d04200c40d2004599008804d03030388a405140c540d007034144028244580b04401448042c105405041103050140c1c1b030ba101f03090f018061183c1c6030181800d141e280284105443c40000480d040140700f446400c41c3d11400c600c07041da0f006080440302da1601c80c241368080d48540d000a500501e02480007040000380560140b00f5402a401d95625540d8141816210f81e03841340450751484a100c814000540440c66100319840e01c2403c03100000780c0600784541117001510b8100c01b40c1d1001808140101c8041c000041c074510640140940b02c1d10b0b070f40480c080c021030b91001400139818a600780381031b41c41405640c000300000821a82456120420011101d201050940321a42040c0005555a11603606 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 673568651 1250 673567401 673567417
    0xf05010509190b21070f050405010c06060504020d271110021c0e040c0203090a03080c0313091505010c02180601030905060406150608070207290c21 65
    0x3030340c1c0c6400800e070100038200c50200450945100782c840c001c1800403020004c1c0041201ca46035681d01d003070304540c5801c8020001840042007100080720380f10303e280e001094030304480c820300b0b000d08200303802c0c600071001d00700a8100c07070340151010440a400841c10b0700205684080320507003480d100f80541883c003407801c0181c4090303d00490030760481c01d00e041004030020b070700c0400e1040c2d840982009446114a81d03070048414001500511480302525151240003030081c800e000451800400f28041555214544800340c4040008240c42103648010300c12541500c05002882400540300d5811000400e00720300c00d40d043c0b002212004c18154020400130b01110340060000039014051036031a0301d85840100039604043e21905e807640002d108011a41c040c070310561012601c000b500300c83c4450101e040d448441082410400d00c070f145074004c00c461003950900c0520a2445000c405060540802c50304004184040000c0450740c1c0701d008907c82404240e0500452159000d20050f80d80030b01030584 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 673569901 1250 673568651 673568657
    0xf08030406050a1101090b06040f02120a02181203040608100b07021905040624022404030e060408010506100f3501030b0106260c130308130504060f0501 67
    0x2060256038000c0e0042d220741c0f0024a803100404403402052401d64001c2407007216071000c40d00612155180a004070004030350305280450a0031405000f1001036100030340b00c041403a500207244442110031103140c40c3d106001900802546441c01c0031290750341e0080c400d210001d0003010100303141e00c0c5c908051070200d5440d400c829080010f25002c1001007020000180181204d22000185c503031100d02075500204030a003c0e002e0b0142a207410300b5802022402d00c1c00441d0450343c00382d65800c00a400342000c40c080f8070448003180e030310b91409032061512010807542c000c44c04a00003403124030540000348240c1003910a86d002600000c0140d60b6803c0c040c1208001c0340b0580c0b440301201d4441020428140700e00e24146d00404da500070401681182038100760b1b0542c0700c500050051725000039450b603c0746100708001002c4180c8500c07200303e40303002034507268a0f814000f42074107101040d1501040913681150030150f44051440b0740c070034504414031440b80503c0c144540050f4000f0790036202007c4ac2c2042e1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 673571151 1250 673569901 673569907
    0x60804110109030c0b360a0b0322060e01020711040e0a080d0b060d06030b220b2806170c011e1b06150e0a0b0310051008120a090f0803 59
    0x842c001615400190140c005440d16011035010032a0030746d44c10505521552988030201102420300c542c0c54001d82204022480400c01e210303a0540090500540202000942a0341c2a0306c0c50603002800c0d90320070000c2c846d80085081e00c00d02040e4020070201038422601000101000414682c8440240c00e0150443d4018002c1011500380c40c0c000300d100f0a00103205502e880c0050512404582c0139130420380381c0000036000c02040704c01e11480c00f489600c0043d00794100f400d00d0395503010200c200400010a04183c43d2070301c1000c12414110b03490740000840244600da0b102c10246070403080c1251041803511031607007118607550207100e0304249000010880c4c1c03080d03500282e0580304a4500600c1070510810522044046030b40b40c40b0f02080c0c01040101c54541c0c40c1340070007091040358003421080c403041ca0100b40c1d480c0c0d030342d00068400c045000c2c404027142d1669403e08205a00415502c0700c10507004011915041809200c020039400115440c1c000c410707510364080c400c0c440007a00600070907074070070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 673572401 1250 673571151 673571159
    0x1180506040c0c02190e011211221a09090a110409030e12030f0a0503090106051e0910180905150108061f0b0d05070215070903020108130507060804110109030c 70
    0xb00060845030f03205c04203011a5989026009243c48242d1003250b01085456488007000b1007010114002442115030b0000c4400340745800e0001004032449060031035451603a19182521513030210108040107101309001e14040721050b40310354840800b01c0390304014103802d000c00d02d014803071a0400f91700b40c2e550000340c7c0800814403a001e6090b008040140c44180018000c007101a0020b103060000c0356078082d2a810560b00040c00d403042038002034412a8070a071209105407489161b40520b210480d000c0241d071715500c0d001d4280d9421a00402900c03402da162404041d2455008410424842d008959075110308201c00c40713000c8000c0c0662001a0030100108240600800310b98251141c51404240000c2e80c0301c21110b40f550101140d00e9443da1181c0c10000c2d00c2d80c051004e00d41411313041501d0f410500d03040100812903041c074000241806226000310b4080d40c001c5150f602d00550180403503410703c0c0c55080c0900402c0e0111400c803030180e001c0c0302040c0c7c554420402201100d50000c058941d075410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 673573651 1250 673572401 673572409
    0x9040501061d0f040f181b1a1803030a03060e0112080301030209040809091617160c031701120c0b040803030c09040f0501180c03050105030d05070503070b01180506040c0c02 76
    0x4000c40f80b075402515540c607211496070511444298202103501c0704581e160620740302010b115411414000b401084070300b04400240142c84501c41c40c2c40b81c81496540344026000c04802c1c6524030040c1e05484040382d641c0c125034140e40701406961007412103001903030741e90500510360b2000d02c03001440307203900340f0042005041a00e07041e9005446900f0180c100440760700416402c9070b04840c4940c0c901714000403140510b0b0000c0240345022404c030030084051801003421900d03011140840030810040640180c00c1c544101c1e041c000c1c0003480261146030356910b01220394042c10081c02582c802c03140c1100083c610480104850450761410007a60440c0c0d19900c0f0741e00c00740c0000420326046070301d0b0a04144e000849100303c038040c00e060030b4a00b0110100a400b8421207000300d52881c28145010300500030750750300140845101107139107450342d41c2e030056240550550003030410080660198400104180c0c00403441c049402c1e81c6201c041002e0756503d4100015100700c68002c402040e0313010070400160070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 673574901 1250 673573651 673573669
    0x6030207030207090f060e0604020309070e07020f030403140705030708060103030c080903010f1e020a0813080f0412060c0503130611090d06240b0a0804051606020309040501061d 78
    0x10207401640c0c0e0302c2c4c0d901c110090540d850141c8104a69030b5641050048030302c03030702045030400710075202142135140116100fa0ba030b02d6180140c000f500c0c4800001011580b08200040e08002d8040c2070701d0320760355603140091404a00c3d94071000c660090110109040c2400203c041c1182d1265000300030b1640b964809981c2d105000a068450190400c1030701400d842c00d0040c00305415102c00d0000b95003120710322000b0f001208403489401c1034010413940d10542d610035045c43d00029902d00707401e4807c10340c0c5440c8006200e4141c0100c3e03c02c3c0041000a640301c10f903217451208500030b0b03106114200710f90a04660621085552801102c0745540001c00725085621240510098101c058606020000010b44d0000d0b8114200c625544a03035140e043e6241c08003070507514481c0140c0d07a04c2e00600f0640400007138001c03048150f041051020018090105c2042600966449150a04111616070100940742e51000b844540034070300780b030f00020f0715611500803048181d80785070311450840c00c84810020448 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 673576151 1250 673574901 673574903
    0xf030213030c03050d0e1e01030b0315040b040b060328051011071110050304030f020a0f080405310207020a0902300c0f091210200c0706030207 63
    0x40c111140c04030000d007541c40014007039400b4100034100340b034001c0b0300101b8148246044a000f030780001d541c00b4002c0207845840440b12001d08003c221402c402c00801c0c603080504550f0b6001c114008280030500520300d05650246000d2110034005a640ca81410f0b502c102c40342c03000c0d40d407920301c1c000c00c1c440c01f40e24242482060300c96800c1d603001c00c1c9084400c0b401d03154002001201c5040c001881c008101400d80b4581000078140d814051420b400c1d0006015800300070b00280a1082c48a0380703c5146100740044801c256025151603408403e50400c40c1d860703085070003554041c2c3c030058822203400700d80141e80080c10302940280b94440b130303012000c03201179040b01801f20b0304100d00d6940410310b021140007070811a0403c000e803421119880d00047ea0664140400701d100782040300600c031042d42084101e8001401d034100b929610500203022601e080c5090182c20702c135014440240b258190150011540060101034010ba00216102201c00074412030f04003492a61103403404008240c0280c000e04119 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 673577401 1250 673576151 673576177
    0x405030a08041e08131d010302010806180405060411180c0c0f0708010506041104030804060c0f020402180a061d0d050705120c010306121121030a020709110a0f0302 72
    0x10300f211618807010000309000480b401c40010034820042002c5020a20080502070040c4040000103c0250030000741030201074100034407900004d00540300c00d02050240d001c03101359a03446141600301161240e800707407005c840040a4911800d2546400d081c80c10b032184054907150582d868031001c056440c0c0c011004d0b11668081c0b03200241540400f44001001007032007134000301d02468000c0c104011140e0860050401003000d1005002040040042c0d03010356100d410490300ea56058185140600c1c100350000b50300c2400011000e00d082400b99588015000503254400030340e4643c0070641d84e503603000b02c007a15010305c8405040e106181007500c3d202d08a0003402920040d0303845101255a42c10f89105100721755119544004036540d15101c1c1c00c0050641d06903012a03040650345407078902020075807051085945454202184249200c86540051810200c9030b6400b007401011351909000e01c00c4c1c0315600d2a148419040444920480320f21280650f205108640341c0c0720300342d000390490107843e008 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 673578651 1250 673577401 673577423
    0x30c050a141027030b1503060903030c0901033c02090102030d021b060117070806010e0103060c0e04061e0f030b180a050a0b15011805150d090c1d0405030a0804 70
    0x5034103c1441e03a42c0c0507501400241d10382e480c28262082c3c0910306246094042d074481d8040009500b004000c0d40d0300a404808040c0d5140300030001203004d409540e03240301c4031120003040d251800c80c50400030306030441d0410010400410300c40d01441203001315541140903810030800030317684042a60081c03081100c0e41014809042417084840c1c5045401d0708101c0c013207403280302e040c2840c1004002d9500200300e400c0040c081d540c108204102102c9042c0710003030100f42c440c6852101b49008a0b0300c92450700c809001006025912080c2c5204868192400001c400890502081103010110b007039080d642c114a00d091503888603011064989034000c0d4882080c051150880c0c00980306002c4442c0440c01103101e03074814180b03002402d045010b240c0070681841040b25801102480e111075820446008888070025500b940038521000d2140750704048105141003002010403400f0741c0c007034096802200382c0314500c00940140000d402010342c1c004d0a90760090210160641c400c44e5100e501512425840c1c4d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 673579901 1250 673578651 673578707
    0xc0e031219120906022101050f092505090a0801050108030f07020a0e1e060f03060a0f0204081606020c010f1d01090914060102061e0103110303070c030c050a1410 71
    0xc0300d40c0f40004468082c0c0010300462084010300345022404803486410302d2651519002400c0903500c0c010207402078000d9400100504588981d4030450b40d484d2890b0090344c40e500c84001c00c60350054544500ca8807680c98040340508051040c1d0f81659006d000461801200c1c92030084550440781e0308a90242060340042040e203140302110b805511044241c42c03d00c01c000303400c10050726000f804980600c0d4156104203555600190040c0c1100301071800203080c800030201107000c0d01c503d81010782c0500c07a000e03500c05042d2044d003000040f15820390a45110390f190400440f43d554022050400241310002405a0100100d00100da8400141000c660300c5642da0705440030f617000e50744002103d030300b058100121940c042c07154640c000c041c000030b10100c000004d1003108035001030001070700e410010490744006071000c10840d0315441d00301241140103035880c0760841860034a4060640201d141d03050004505c04100014940440010824425072880c0c0c4c03000c131203599800d28129902c03044c0b943d01c2c107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 673581151 1250 673579901 673579937
    0xd02331f08030a080a050603060a0f0204120b04020a09021c020904090b070e0a050319080d0603140601090c1b080a030902040501080c04061401200c0901090c0e031219 73
    0x200052401c08080c544070344840344083c140359001040110803c0c2824100401c1303680c003290081c0d000b0b2020200081c560a81d102d458000e0241d900900708092402001c83c0034000c20500540c459031085442030441070310f80f9a80004c0e8015120500340e071074501400200d000926801822681c24003400006000c8200d80710310700009005e541c0e038408220381010360381300c50802c05c0c03018000d40301c107074010b0401006103600104c4481781c141c0081c041c0e80b07010601145506d51500448011742d0000c0107090103851142c0010740380d00080c030400055130714040700d04004074000c010a1703414441281211a600825441d6030780c25500035190038081554840c0204010380d15485030f00d01800c2c04400428900c15180c081c001142d01a400141011200d100c00c55030903a4030000c1c8612940c8100081008030701521744e40391401d10701003461680b080c094030001c200406580d1001030400c00543d1600d40c6950030105154482406100b8119030b5042008250781e003400600c02507840310300f18502202801c0c080180c0c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 673582401 1250 673581151 673581211
    0x1122020a050405010f030c020d030b041404060c090e040803011a1225030902130209130e01050601080c070c1a07020604080a0b0f0f0a050a0b030f0d0233 67
    0x3240c081080420103104a5034004070226031071030641420440144841710295481d04140c600408154031820049088d40321038002c44840034002464030401d0400e8039004018240c14207440300020641000001c0040c40446c0080c02203801090031851a42060003683e190001c87c203042c402401e080182c5030011440300c2289220351091510b0711506000060b0402a42500381c9068080508109940300503903550303440800e801522203c0141d8560420f0041040780104110840ea100d1404400300801c02043d008076101e40000d0361980c402d55500310b46030003640110364001d0190740c0b03414800d1040508103e00c0f502800340706001c0c41c1c00c0c00e0703a55001550701c3c0c3c445d0300f284500c2e4001c2d130030a00400c25130075615508071010f006040c1032031804000314020711000400011f00c15072510b000c940c03526119807016260500140690b00010445030b99550381e05060898a0014410010012040d00306400440302d03c076102200d40510000001c2000ca407605d001c1c10303000a40844802195403581c041c0c0030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 673583651 1250 673582401 673582417
    0x6070c030f120f030204050109050d03032003100501030606080a0e0106350a0312050a02070609080a090501050a09140a081e28030c0c0503060907031707112202 70
    0x40440b5144007000280540c0d0000f04043c1490300500040c04940c0c4c1041c510b102740d5409035040b00303c40c081803c04038003030000803161040e40c400046003c0074418440d03000f50f104158000302401000da0b10b07001101161494811f00002401210105090b0b14103900102c076801d2180001040c49038507140c032591656290020107422020720000c008840c0c07035040000384a01d01030009404240c4103610081c003403101079040030032000e0b5508005150066160f054500c0e80350020700030081200d03541750040859010415200200350907003400101988924101c82c609006a52202c0d50580360103c0900c5480a03030400c4d50b4840304810010400710010000400b41d10100b8108140d09560180d6040c1081c80103e03400380488600c465054510130188014441e140d23040c90482c0222016080800f50520980c220307a0313140c09400300b40700607100d000660320162030248450040700c27062011280386611030588010f1809240500c0078042d443c0c43c90790600c0c01001040d1048481009000d503400f241d000d100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 673584901 1250 673583651 673583663
    0xb13051c0203070c090e06130516060e011e1d0f04050705030601181d0601120c0201060f062f0a0803042103090c051210050109060e2406070c030f 64
    0x10f0b0307242440390442d501030050842c0c6504002c0d407010304840715121400144500d00900b2550070700002c20000b0001c0d246004034040103481c503543c84640c01040c4440a001c0b0a000801f003228032aa040e400e5003200e51190029118032820380202c41403c04114200c080071a8403601070b0b4404107694859000d0544984500d5940c01c0c0d5a25206002401c00208140c0a0143d07140341501805a8046038801d1601e4000c0d009449803136035282401200c40812080305c045030181408840800c958054000d9415114a0110016240d0325004100d84030800340c4a0303c104884200c0003010300c80038810b0303900b001d50b14004c00d070b4005042c2034503647c10940c010342d0120390031100f14a0000b81c8511018a100f00a86a49824072800c180b0b9254815103a113540929480b903c4424900114480100700d0010110101034050080c0d69580f000c2c43c00804a030703c07508110013850000034180d00c03820804c4820f40c070480c003542c001d4106031030148500b030b4020050844020940502c04400300e64890211500c1c240306103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 673586151 1250 673584901 673584907
    0xb040b09190507170705070609150e0f0309031908071a090c040516030e0705031002030f090705011b0804051e03010e0c1e0409080a0f030e0304030b13051c0203 70
    0x5140d903086800003492082003058425694404203c20030900360807185d585401500da200a041c440d0042190f140014000e44800f240480314034980d40000848140e0b46050300c203070076038920400d40c981c850034038104d0b0725802410003c40c98040310038222904901580f403007410704101d82c0d034001021001003003150042c9000c4040000b40c100400207103000c40c0080c0c1d403d2110342003241a0701c101e1080c1d64248400c0c50b07110b4205488200f41002068000c0100904841c07216402ca4003c400030f5005031841091746038100001845400d000a840302100e6041c0d4950101600d00703403d04502c0300f00e80070200c4a020040000040c02e41e10081c45178100b51131180928006284102051308558401415181e5600030500d881c82030b81d05c2800d5600c4400315008a9110302c001c9400203002040e61010040041c10045a0b401f807092303000f42d03d615808091b840802200d80f0b0301c64600e03500d010300d1000900b2140b041000940c0742540c41a0381820611a8007260840c030b240400c007018502500c0808030060b4004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 673587401 1250 673586151 673586191
    0xc040207050715030606090b0306120d0e090c3103020303120108010c1e031802041a0102060106050403050d030b060c060408220b0a0c080408150f15010903060b040b09 73
    0x40c0f40c01214107240c038182000307003918201014280c01054410540000800b00001d1040e8aa02c43d907892110700050130740b1000d820030b880240002c502064200d0203010607000041d503020442c030458090005140e03004c501d40c404190034989040ea4421009a03000c0398410020050310100f000d0a070071309500c0a80b26081d81403c001c1c0382120075007902c080030004030741c00c0d00318041e00340c0780e000f1101c00c0381d8a0046480003003410454a24550310b40000e402030700d0006c0007520501444903d004d0380d80c090b402d0b42e00d140d0f40d800c03046401c0d0155000181407a00000c0c04014aa402580081029800034003180c0c10725050b0701d1b219080000440d029650070f1000130f202110262224070300200d4451554204c1d032658240f5610001d00d003d135484401c24400754028120600400b441074030000c090720000c40b40e001c1c804801e00800d00c00183e403803900150245010584000d1080319440341954180d60701c541c0585035894081c09040e51011031904641d49446040c419180d00004074452165112501002a44 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 673588651 1250 673587401 673587419
    0x405011e020c3003160f0f05060703090b060d021011071a03040303060e0403170726010905070309032703201003060e07080c04090c030207141216021801080105090705011806050c0c0402070507 84
    0x1000303240b1b1303101c1c543f01d940c0384005030744810030b1000018003440c0045e8031422101c540c030700d4101950000d511407150214090654005200214440d610030707903003805510741e41d0240c101c4030711040c1c6000b40401c1880b110150803229540b00e040c1e01505624041c0d049005000210800b0812841038510030300b812001440751110a01076190440340c5440c0030420303428207481c0244403850b03007012070102a41114200480c050305405d058040d50b0000200d0007048240208440140900715682c1e002e0011038822140990003031080d003045458460008410707968080307040310a5140107244149100e402d110219001d40c09200d4117071002000c1e280166227807030300e0800a421140e01000c40ba0076074810000e500c02c030b04280c0c0565040545134800700e00c0074201032002500b241c804262640c044403030500001440d00301504158010602c21054440a035142d100446005030b030800803441d00da01e10102000003038803e60080c00340d81e03a4030003520a901c2e0206d000030140d90020a0544113540504070500c20307603003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 673589901 1250 673588651 673588673
    0xc030d0203090a0b010b090102100b030109300c1208060301090c230306102903040c050f0306090706120b03071203090603020405011e020c3003160f0f0506070309 71
    0x5030385800c1b40c203003600c8200007569508280e2600c00b44507210380906503191425040351076010350000959041d9080710501d0034a00c20741d02d030b41d00b05401c2c4000519003514043c0f06403203041c1ea00510840c0d1441c01211381915481c034041d00c01d0382c2540d41c0d02c08000100349000c10b804054201e40c01c40010541000e084440800258402148250090070034440d1544001420a040f90190420b10044100110070302c0c1403000c800c1204029020008104410409808924016070380100c6040aa11082c3c2e811700d60f0b10754003141c40b420030798040c600500401d40184000c1c0005036140c000490500124400b090900703485602c0001e07140d003000c1c00703901095008030014000e82080d28045003018078240c0004c1c058408000b030303480500f9256181114640c424011108a0040500500c2030302007881c01511049009236254040745a50a5101710303802d002000702da04c0300c52071030010f83c1700503440c1d20b0301c421100d07000004554640c029015807000840c04c0c01070500c10509600c000900589078103061001c01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 673591151 1250 673589901 673589909
    0x108040203100e0606270412020a080406020312090331081504020906010c0b152b02010207050406050f13020c060405030315091323030708090a09061a0c030d0203090a0b01 75
    0xc01d08000804407001e0046c0681d48150040c040607c032800f0075a0503414480c24440142410354009804244070380c0010040c49400039807610301c0301903683c9411140d180d0252540c99144000300084180a4500c0305440b80745051480706100001c50b0348400c0c55181520b8031755202810720241d0b04100a41c503007100b110b94000d4080c00c041c1e46880d155030711800b14a400900401d281080c003602910f00781c4070f002213108005000c014408000c0c04018501c01400150f24007240184541e26000c1501d041c02d004075021698007400c0c0c3e82002500c54100400540c40d4000d884141c1e80c2440080c000140400501b4010360055014550340e060001d9140b400c421001849805055005c00f800408880305c04a5881590015402ca081a420390074204c03803000615015200b81c03201107801c00074003c501004085c802002c0b03804c0c5041940d2243d000054898a100b14112032039035048050350000c28500602c605044030041e40d02e4585480320041c2280c00c280c0381003206900460300d440c20001e0070042c0314090 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 673592401 1250 673591151 673591189
    0x1209070519060804050a080a030e10150b0c0102070501060f06180b07061a1002030c1b0919110f0306120714130e10091a150108040203100e0606 63
    0x2403142040c110190840342c810003040200c0c0340001000d0090510500060715071003402585d03600b0710780b031004014000e407d982c03140070300441c49040d4620200307214408200020301801e10701d141c905081819190030549c115041c554003004000f0024000384550406440b1111455a0950801e01d005102e0042004001c0410741c030400140301410101040c1d8101d19806840440d20324154803112590242c10b4940507000b0140d0007401021a030040301604410070f488049592404061f01076240c1c0c40c5074807060542000322000450008010716516440d42421407501203100cad080b4000c080480c3e8401c0141c0c815819000c414010a0316100da005420000d40400411940b81009441d010b0f141c2d10100a600ca2121003406406d922101e40045c1c030080c448100b529421095419a00041c0c0002e11040b900407010038040c00710244603405090040424441085040d210800191a10080500160b90520406403044440c0c1014081c2008840ca050040c040c1403c150090240c0c10881500d01141 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 673593651 1250 673592401 673592419
    0x312071b06020711130c0f020304050d0308090f100c0306081f050603120d020d0507020f03040e040606080316020f010e090402040515090c041409040302031210090212090705 76
    0x90024014848449a0401c01c01680c0320482e140840d03040f401041090740145400540f054141c40550002101c4007183e1145900e038511400100d0b00c0b4800d0780201644602c41c8000500070a10484c80981c0c130484c03541c100d9125600e07140f90246842c51090f80b0000b426150886006d00c1c944c035001c0d40d0010249040204941901e8500c040ba80140108042c0961a03590b00002d00a0390100902030445046000480c2d8030384e41400c004000e0b41c095180010000d0400b40401c3e071140c400036240c8400d00140002e18145406c1524200b001c1130060810f403281c9860740004900c8003002d000410b0003506640200300403400901c14092540040340016051002118116542e51138600d1805d900507030440d00007869540320101458448075805441d901b00760403c0c2080082e2000300e00400645942046403114141400b0030000310500450340200160230074003486682d5902c821803180c00407a0401c08051841c6c032609002c0803038200400e00d480d090240d100303111403000107105080152138261900c0340 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 673594901 1250 673593651 673593677
    0xa060f0815010e0d0305041d01063005090c09101203050c01110a1706041a042319061205030f030901091a0411030109110f060c0708031207 61
    0x45000060031020000300c002450706540c2c1c0310715403140700c2d204000d02100c0790080c01e0400410360b8120b070142c3ca00d0a14121080d40094200d0b0707192904880c1c25036130ba0340001c210001c81480f105c80c40c00e01e40e0028824900c0851151005008a40c800c0301d68600504102d0440002c1003150500601910100107881c00c051100d142e88481382c41c561505400c1040e566055403400900400150198510030800882c880360341a9011452556254028440c01290b40390541008207c4036103428032030300f03183c49021a00c41c90401c2d4104405140120b400980d11111103c0070540d001d4045448420092626903c04581503861099501900081c50400c44250307099403040da40c0c0c80f58210982840002100141c1104400d4210b1004d09902021180d10340c0b485000b40b85021038255411540d1480c1003580710190706051107452801604620490350203100081032094441428241c0b980210742046000101c0c10100801001032800400856075028440707410080401c01514100402c490584644 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 673596151 1250 673594901 673594907
    0x807020a090e15040309050f03071509030210110718020715050a150b0d1e06080313151d12060c120c04030312270309180b031506040213030b01050a060f 67
    0x5402d0395070036205209410201030029152a65590090505181d4be0300707001c04041d804003a100840c0c1c0b081d04d00d098603145518082d40d0a407a60590000f44d5400341008000d1041c80b14001c24512750000001841e009107521401940088904490300c0542c888060281c0300b43ca42c03185806103110100b4094040381001d1000d60b81f4403d490881c00e400c0c1e2200a8a500c44c04610015182200356070010040f19a442c14072075140c2d0440140441c1070038012b007001030034104401c4000c081941907540d2180902c804d0300c41601c007103a944400c41d0407102268820b04a03950810915004061220f1040c0c4c540c20ba96948c0c1915110080c80b01d890b00341c041c0401c000080d0444c82e07040104035554408940d000c0719035003014860030000c1702c4440d00d08ac400d80c4041416000458030066502c0c55108a500c403c10419420a1301c0c0d07411a081d81551014800c001303003007400d20944c1e8001900900251805141d4142819411056081900c01d40300034801001145041a2060003d026030f0803c540ea8030042c100203 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 673597401 1250 673596151 673596167
    0xc010203070219080a0f0b100e1603020906220b04030b040b0912030708090c370e16080726060a05090106030f110c06060d0807020a090e150403 63
    0xf80903641e40c0312001800d8940f242128080d00c41e40e41112801c0340c082c100580c000107041001d84449000401203030380700c64400810015111280b003546440d4640144404080b03055640c09030803d64240980062a69050002c00404041c020030b0300e101851340c0005401e00445501c030410b134800402003040007600c10b550f03280d80103030003da10015030b0360b9100503d42000c00f0341042601c3c0c00d00c0001008200c580050b0742c02d004030044c004540d0f80755010383c00c0c031030f1190b120202071006210b84070800d41500c448040e050142c03643c0103280901d00d85c0c1d401b1b01c104100d82c140c5004000c00c84a42d801d51416074071100c1950f00c4151407412490403940703075407070407001b0303100a036044158090500055820f03110f00308190001e100140900a103036945010040091a84414404a80d41080c015a00444c092030544d00600800009001107484160030031a8004000c0c3c1c00710f60b410740134010907016907030b4030226000504d1051400304407010030100142c207240d0350307040148510050703600740700c0403940c40300803 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 673598651 1250 673597401 673597403
    0xc100608120c030d0c030203041b0f0b0714030c030702031908030a0c1b08040501020114010b0f030712060803035104050a1a100e04110405041404140c01020307 70
    0x5469841c10b140405a04511550140940050404c5601e03800581d03d17600851007280070381c1c00324010980c00c0c40342c5d02c0c4071400b038030640040401394841405102c02c000700400d03106101d0199018207480f07a1078814210b4000c18180075140e0800f2030341c20150704050210b010290000b6032807800c0342c01c0c0c03a5540e2500340030103007014101c3c40d5035407218142d85003d18140c0300b520741c07840782401c8417005c0751a20402903070082c041c1c5801542424800000083c0c50009641614000c450717a03030600020b0070301414107400c014808010440d861030180003c40e1980f082d24050308402d40a5660703403424009003076040c41b4500c07012005e28810440c03150849881040704612240c11071010700034170440061229030350240d44569900074904410712510700c0442d408010000c1d0040d0901c00b0000c014801c10403075078174020b06100441d85d4100d5440e168946588200299102d095400c8d09290322203001c5011030f080302d180134035141e500d8018001801042c4402c41442100c0200070f10004000c00300003910381c05003443c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 673599901 1250 673598651 673598683
    0x40e0f0a030e010908060f040c0b0928170109121d0d0623040204061d01062d02030a02010b040c0c020603430e0109030803040203160b0c100608 63
    0x84540b04980c414801c407002845410102c5019051000c00382c0c8100c8020b640869240090080008480f1020b109840200d5001491041040e64030010f0650900600080f0b0038401c12000f0003046d2040321030180e10040300c4400c00020984528507142510494003076030f4800340214907100c030f03007190407604085804e06405c0d100c4030f280c0c0342c6600d006400f400b04000000c040a1510f01c03800c1040e40d8118007648210f0084a06111960390307044003280d01c10010811000000c40d82c00140100c07402003918200129180d080781e244d4480d40c510f240c0740301103450180380050300001005d12091303909025802c3d007284101d800f00321807821400058034962642c000280152804000103002c1e5019010b40e4101520610401c00351000380080c03180320071204084900b00cc0c40004114400a109d03606011403104103841c0c030701802c0e003580c85001080d00024012a0300d03201d07412060300584c0080e50501e00407d011030169440f041004061410101420030005410385004010024810001980300301400000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 673601151 1250 673599901 673599917
    0x302100b03010b300106060f0314060d120c082703060f0a0b1f090e070e0306360105090d020102120f09210702040b040b01230403020a03050705040e0f0a03 68
    0xc0c2c00b9130b4542071002001ca2165182100001d070040e041b403014500f45200395000c0000e4035040c1c12090100500781c4d000ac1d048407030a001440040c2601d290382c030122149040050040d607566030340c3d1101c2e078440754103201c055000c0c03201c0d444d96020304501c50604140c103d02800c1946400c040c0d00300c0c444002000341c5405a1034500d980c00c0c42d141c1d4412002494640c0a05108079400301d603010780450f545d0b02c1400190340721303240002c0510b44240224440d0020040c060141c03500c0d51690400110202c144014900045000b0b8143c040070030310400c4203894081001141c5482c008000c035050200421059003964010090340b003003502c510300c3c000d43c0004001c040704060384883c004980752910900c4012604d21601d02d0002d80c0300894800b42203080d108841c01e0096810250520081d122060141030200d42c0c2084c0300141c1a03031140e0a000c6105d50785265074100f42d139940002d40000e040c0e034419180ba410210090146040034000d00c0d1000380c1d250000d06110a01d00e06040d81c4200d4281e001e01000515 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 673602401 1250 673601151 673601209
    0x60911040203070f26010b0304050d02030705100203070314090708100b03191b030b16090506090d080c0a03050c0607020105100e0a06030803010905070f0f091404060f030302100b03010b 81
    0x18540760174200c000c01950070960361310b8035148180e5074425541940d0030721450381003403001e52002049412155110703000e8941101c0b110751400c041e40014101c04141a16070045104100c0c0d8640c40500ca280e204004080141c80c150040d4142905185540561401c00d100c6c48001d450000c0c0e140918001c24608800d080318504000144a80d40c440d155a111244070b000405e01000f44821401144032194541503060007042c1034541d050340c0d2007869045601882420018508090282015406040c09500c0c060f580b018203414903440b000210007050000c140424408010071005601401ea1700080005040c0081c000c1c441c0710a40c8110040301e4007041c001460745040e90049001150301222950710703543c460082d100902800c80d194000661070100c00030300140f041c0284e0a103025292104001d10b824404610b0050752500c0c2481d402940b6180001818000c03407000c500214080e50181107280400705805060712183c0044901c41e03030502c040140156260648010b0010320000f44290f01144 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 673603651 1250 673602401 673602437
    0x503010b1c1404030908010605030d0c0303020d061e03030314101a2104030206130b0628030506060a080307110603072c030f120406110f0703060911040203070f 70
    0x5500b0210300302102c2800b840201508000d19500b915010750003400b0b41c50b21101496a944c0e600c446180000e4500b20821300030034041d5004151101c42070034003040c0c00d40c9852210805003c165440001d051315a0020000e1640c1445098a0402c02c0041c04103281054a210611081d46005000f141c561400700c2c070481c54a100125009003d05061000c15030314040346170f580002080710154054083e000004129505c40d0880c4100554054104039050300c4440520040c09030800f000c100f0798020f04081416041c0710a6403000841c4628000c04662801c803062040307070403c5601031821030b4000d200c1c540014074024a503040c0020103641a45c3c595581540440301090303000303088101c1d246050608441001030b0400390b01d05280550403611300101d1400c2c055071f0742034080785030402240180800d01c40b8a20407003250245000c04c0007120380d074000d10020309051994550003101c0d02542c80200d00c0030070401614240f400c1e44126070031400d5203003201c005000191303014000000c200c11a0600300f80e4a007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 673604901 1250 673603651 673603661
    0x20070b07090f14041d100513020315161e050304061103150f03070e01030f02041d01050a0f02070203030d050a18050105061206040f260a050d06060503010b1c 69
    0x201125071034400da44200b050b01100080d02500e0256041129400c400304152107100b030304181880040c1b50001410790040000d01014104601d40c1d104614182e025030303420491140022840b0030002003a0500f60a050315101456441c1d0080c05400c02c1c1410402e600c06200c0302c10011181041035984c0c3d0b85203045d400a00d21800890b00d00326010040c002070f0f100d840c7c100101660140d03650341c0c441380640b00f010b968441d00d00c00d000020b0300e40401400021900001161960320241011620410070000000050300380c00d60600180c0d5200c2c208545d028250003840c20003c100442180ba121b40c0348c02090700c9125103008120174513100c0d0007264120400e42d0100d00d00e440340c2c0b5105072002c0c0b414030341103000e40000d582e454803445c0011900c0308180c1c03011940380d000d6030b4040c41c1d80d25802c4580e81c84410100004510040500c4100102c40a01c40014020004076049944103541d070888a002d983c12540590042c0c8104101800144402103040040350502842e400629421010300d08034140a00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 673606151 1250 673604901 673604909
    0xa120302090d02043b0a0f06090204090b040521030a051017030a17010608010e07051201060e180c0a0c0203120d140702010506010206150118060206070320070b0709 72
    0x180303055041c26070004041441d13410b081c03650500000010301d0320901300350784d17404100030380d0315402804502d000201015081c12261748503001c08121041103800260494002d00c0080e207c03640314030208010031905001d03a00e4101c2ca9002d200f243c2d91890540c010b018080280405807240c0c3c0e800203c1c3e410200a0300b9240100300003000728104442600104d40c40781c000307000346000706000e006130301c0a102d82200814140d441300c0c0d461100c00d80c607005441150b0355025180c5418800100b20104103100038014017406031107281c4406103100031003014407481c1c1404800003203480070418240042d4040302800c4451001135468003140450482c0002030400741e80f05101c800608002030400000390080d042052030b00c030400c003001003650303400e0400d90a03500d04550300d0380141c0041d40001c140c4c844030341d400983c00c50185041c2040b0f5035003400c2002c1c02d604581000015900803401c000c141c6074180180344540000d19800e42440702505480e54440c002c3d05001002440325070005481c040c0705501c0341d8014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 673607401 1250 673606151 673606159
    0x62916020d050d03020a020c04060b0a18080604120806061602150d1b0f020706020703020904080c060414060105120a0f0809030a08040f1520010b12011d0a120302090d02 74
    0x2d03d01c00502600031740c00107081e0740140c0a50321079200315190520440084031030511020b0b141ca00b039210122341900c03800a005080c0300300030501047c1c00104100352480350b489460420402c8404803030180000030000c1ca4188102030405c0b141c0c103541c42c00700035041c0c05d070b5050301c4d55404900d00c102e2070500c90064200004850786491000844c40c0c449110354203104099888058405c101504104e85912890092001603441624104010305148000d1980280600c01c0c060030281c0c410009030414030203460980700100c241d000c82c03518120601040340105001c40f2064510b41c181040540c81e65441e400141c544045451400c090002500449607210402400e80d81c03182c0c00c2d850000f0164205008001a5035a11207011031084c0d005040c03450100840e48030300c0c0384918020783d074200c02c40d80b426215a46d035407502d20818a40d143c00c1e40d152280c0349010000310b034403111200951a1034030a00e0b80e0940c44e5000300e41c0140442e602025851200440703241c00340e41c038903a1b0408149104407080000b500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 673608651 1250 673607401 673607413
    0x40e010c0e13050408030f040201090b1c0b1e06070614040515010603061a090a050913021305063003030a06240519020705090a062916020d05 62
    0x280d80c800c400701e45001d0129880502c0404090510045071012940108040303002c03c00b0407114504080c04541c400d10500d0480d120603164846035582c0d802c01c20700c046040c1002c48170311180850301e0180004200d8207545402c0210309800540800c0c105412840703005a50004511080c8403094100c0003050b0036010740742241e41441c1c07a0080d5211902120782500d8003a01001003120340c882d0040390100c541484a21070b0050122400003000c0e80100301090303200c4c16103400014507880e4400da052203074544002d040380320f80c1c09005005020710040c9082850f030346000200a241e6480c0c02d0403c0514000fa00340e195107020800e40350070301c00c82c90b0841400354440482040f0222886401c414190340030711007000d07080791020104030903011401d007490012070740522500010901c03091380c208010070507104440d0b61346d40e5030011841594090341c40c1100c4a840e9441404681e02000c160100c003a01d100c41d80c6072110128400c00100d009003898010809011a04c034000d56484038441c240144d040420707200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 673609901 1250 673608651 673608671
    0x50a0306240809010c02150c070b0a0b04230c1c02070f0c120b04021302130803090102060f0c1213050607181d0a020d06080d0e03070f0b1602040e01 65
    0x9000d08406034400002d00960000f404828040c0500c1488000c1500100304207954140201400c0d8001085602c0c400018403044e000300b198400c205000301003103400003034000740b54020300041c1c0309001110510031510700d1100d100c0f840021445e40c2e02041501040751a8000e001d89003031313045403981d0035281c424008036405091040084490350441d2164900c000e031955507804034048050030f2203001d0b0039003810000040150624883d00d40d515050000d0051410442c040d01040c1c100b45900246019440404e178003d46503010480286c0100c0c0400302120750749414158075500c0c1c411039421440709200800070584408070640e50021840d40081036443da07117031660009085c0b40520141c10550714000d140001c06610f84040d0101c010300590b424100307560b4000c400070103940208051070350b07150b0302c0f00c0014400c40f0a1008031040307907003580e0701d40b00daa6120f0100340c0750580c140c0200305552244242040a005000100d500e0031400e011032026640850001400500d100c615100e25542403001c0b141c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 673611151 1250 673609901 673609949
    0xa09080c0d03060f14040902030c0409031e0203031303050703020a0c060e040f02090d0f0f020603040c08060105040b1c03180b0a02061302090714071b0806090c060a050a0306 76
    0x207803480c141503408011066445141510780d14507480ba40d4428a0040241c00241c2400e8011440c81400a4101c801e100a03881c040360031a1040001500020038903210341c0000c0c9182100b603546a07aa0744020350445c101641c002c114982c401c8002010300500241c8007041600070b00c817454a45030042070207104950f90302005801d41c4540c20f03269100d90300e071402c01c0750300c1c194601c00e4824001c00544840c00c0c00709555100680c004100e102550031403240c10003240142c2d0740c1002580700354403032a60001e09034a02003500e81713080010307042039116504100300101e650701d40d01034039a01c500399058020220b040c541010380300c09929034a40c4040110407140800d5072543d1400626031151690308550103542d0b5101c030040c45a540b00c900075440040340002c1207a0070320410032000030550350502d05240c41e90565400507482d000700d590041140c4202010410803809001c4258002200b01c040c1c02c041d403500d00040d031140710364070f80e42c0c00380310300841e00040e6640f01e0307400b92014060801c240713500c00d203030303920300c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 673612401 1250 673611151 673611163
    0xc011b060f060501021c0503070c050c040c020c030f060c07240504210c111002071e0303030c080601082403010f060f06140f0714150403021c050306090a09080c 70
    0x110f8098494041c428192103401b14820401080b25074a1030b00390f07280c0100494960007095400d40d064411828a84000c2e60340d40b02d402a9212580c0042842d50740003800d0509006071074000c41c60a4100d01c0c204200780c0007440854800e980d100c91080c5040c4007100404100310071780100e5224051a290810080004103680c5d00c2d10030644c01f1130b03d0168100c042c011500000d18540060200342580710f103201d282000300039131400448600640714500d4a800c3d850381c016441d40040c0e0301c41c1c0d0210341c0803c03c0c0340e058860040c00700000c6c5082c43d403528100c000685040d001130005950b00c1d10038032032014454810100c40040741c100400a015050440d0700a102503c014020413120b4040028005841401a82da5010307464050190b14208046201c00e05090380103040d0079102aa52049040600d560520804810007210b8800c65424206400c0c02881e00d05091058072001455030703603a10410360007a054a620000407603844641d5507411450380c025120000008201d1803020070640c85080f400700d02 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 673613651 1250 673612401 673612409
    0x60405100609020f042303121305010c050d08041e39140301020d0219030506041505240a050a12061d18070807031a090c011b060f06 58
    0x2090007495100c118110032845406800d400341c400800007000802d0950140c2e1843c14150400d10300203060900100e41800d6922071016104100001d0510300c404a001c00381003e00307403c3c607083e0011103241d9aaa503850007103140f00001c0c0561076001a04000160b0f100c08503a6880300700b204034400003403800101154245401e66100d44058400c1e03588100c1e1050404207620a960510701c1c00344c070380780c580250005034400f09509035408000107140c0c072180f400103203101110303203082c12450220002d0040449402404044c03140c0e003056100241c03441a0100b103010b40e4030441d03142c1a4101c1041a0700b075070703200c0d100481204000c00b140c0c660341960440084d0100c0301d580e03111100030541300e40600c002c98100e40510800790300b0080405510010440c0780960280c1c1300d4118041000611041030b141c55003c0d445495154040d21088c420800b10301c0010350300710000424400c0718180320340900e0f16080c07064052410001400c02c88040c1c1e407800b0000fa1061034000c02d04010002082e10100060b107031a000e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 673614901 1250 673613651 673613683
    0x90f02031c0912050a03080c0d180203060601030504020a151112071a06090103080f1c0c0f0302030c1602182a0304050d050a210609151503050c0c060405 67
    0x210004a078038180f50010300c5954404060110303280583c1e0103882e4094090400303000207505100301d0100079483c0c400e540700d04c620709000c41120102c0b441018039001c00102002c0c105400c20042c840141c803610260702c15250221004800c11050010440c1c0e5420f40141c0040b02d840340c48070800304804102d00425009001701c6014190710070f030362842035203103805135843c98100e0389040c010030115141074040d001c207188445c40306141001646030031681004401c040c2120950fa40c01c0c0e83c61841d0030407c0191249080e013025801d43c94111840d1480e8000e4001c41103403a1018404a81190f60b0f0500d6180340b005050000c49031414508e507404080c22820909420701c40c0f41072190103c01041509070781c800d507400001050340f8041c0b00c200300c505400c40c0d0b0b01801406904115120f0100b80c1c01401290902c0103200007810360303d01003040040c3c4000802c04000c03500100004c0c401d09542e458028601c030250700f00800d4a0b1101490720005100c1c120a10f1600c1c016042844100b01001c03820b064040c1502d4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 673616151 1250 673614901 673614917
    0x70203010915050129090409230f010c020718060e04062f090d1b031b0b040f0b1c05040807050d09141c080c0307120302040308030406090f02031c 64
    0x300b02410541c031702c0e01d000000c44000410b004011071904018000560044c10204011a0985e100d24801103d00383c080e0898480101c0d07114900010440c5d00010340700398000740721080740741c10080e44541e0640180c5000d0610001c2d1141002c03c0c0b900294018010030720440c0c458606810700000904662605150b040008400203078000411494040741d0303102044528642442d440401619091005c2c007180c0829102e54440310204001d00d000004500803080019200c144104026101c44242c001c0d0004417802d110502108072940408020b40d404a010b450b9202e030308a100e400041e50030a01c0310040390910040000300505070014082141c865000c944198420784803d43d240038450203003858038140310120074a00c0c503001c141140023981d0039529400221450302c501303d141e0300c0106182199070000807410101b20000140700307050750041c54110b08007400e566590065100c050800391545484180e01e85c103000649003103007941c0d40e008040340d40440000211580101502e11640003050002c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 673617401 1250 673616151 673616159
    0x90a0b0705160e01090e12161e0c032d030302040e07090e06011d03070807031a0103050606060c030d05070e1e06030f072616020d080103080904020702030109150501 72
    0x3210615080d10003114003c0e905070300b030861450003000d240c9150b150318482e10100054006041e40140303140d84451100203021038541c240300b08408040880c401200b003030705000d9004103400c41490000e40b0b0f4001c007a08000c0c4c0303180f030031360741c1101d8074010507024280e1000c104401c041e015070041085038035030000d503105030b643d400c000d403007040d103c0c843c9000b90380c1c3c1c003400102c080d80705182c803030a0302e458084400c540c0030003080460328241250300141c00c607034010b40c0c082c07050045143d010007020080042000f215030440e69810744546010740118060320005c215582d40160600030b03242c0e0000544c000f004240b0b801c2c80d0042500f10085c290314098004101130f400d150340b5400b4020342081d405407209140d91625003034100158002002c010070402010914a041101c1d04200b00a4190345864034015080c840c50140349480d80303100308001e40d131003461521552a0031000b101d0440350481c481580311a14040420003031701c1881002940341d440c0c68403407010800d035004212850b56014030108079a0380c039 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 673618651 1250 673617401 673617433
    0x406030c020c0d060b241206060705190201050f030a05060a080a050a0b06010905061b120306010c0b040302161707060f1b080d18060c0201051302010311090a0b0705 72
    0xc1c1c04120341c003c042188080c0c0820490741041341c515002902410011040c0041c10584944140b01c440e140440002e9034a245003070b984410f5041681164183d162002c640d03562582c5403d126440c851041d14080006c043d0780c0035200b5907c2c010110142a40d60b441d125101d04002c00f0200e40141c1304007102d1034040f48442000840711b580f19403000080c02c003408541c890a030012001042c190410021010105440d103c8001400e1140301000d42c507284007406900c1e0a080c4020031078101c900076020320401880360b9011080800e041d4001d1803100c2e01b9203a07810100d0a22110107602c1c404442c490b0301c0080d50401c4c00c4000400d0b4032468083c1d41c00e0030b40b100000c456040045500000180300c55081020246214401900c0c4a20a980745894094040c0e1a041038401c054076a540c0e00d4240503d940a01005006806807041c0f544001c2000d840e0051034075030914100200a8101036864883c000008030b150101c4440036001024140003030f039103203801042c66000300c0b81140ea9010b0300c0080c20720084 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 673619901 1250 673618651 673618663
    0x30b0f06030f160b031b04060206040b13120e0d05010203070f0908012c010921080f0702030d0c09080a05071d010e0109111e0d0b09190b03150c0406030c02 68
    0x12010340441c040341c03130804200c1040e00040e16180110781d408800814500d1100000c1c002095240c001d06a01c0c6098140180d400c14001c21201e0410300c1c00c070700a000543c0140c00100e01c1031050429019080300f0300042580ca510308100242a90b20000501100c107401520b90f04841c04546da840f01800c0c0c850b941e0a00740c6d00007040341c4541c958540c03110074039040381c02c9040d0408555a0000541e40515071612503855981f90384c0302494895003001c1181066102e80345076409141f0814680c03840c109030000a40d203210302048050b00c02c3d610981d180c4c0c01442900550028010481102c02501c45800c1c883e48070146840b400641103d001c3c1c20160801e03d000d46c003070481e43c1c200c1c0703000203e82c40c11030520017508440b00c09075140341040100740800c507100420010001c0e08041800c1d02c0d15103c41e0300d0b40c12908900a41c40c0b043c042103007006140d841010304201480b1400c4008190901500e02203840d14481e400c10888550500c000c02c401e4441e143d02520032140640c5d400e00c840814183e059031101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 673621151 1250 673619901 673619923
    0x150d0f06180e011a1014041d0106020a0b0c0a14040306020306040b0901140d0201050f0a080103060e010612060222090902040b010801080a02120c04090302070e0a02280207030b0f06030f 81
    0x14080e4224002d80d24004541040f01705990411080d4080e428024041c0d6600c01e030810003001d0b81c000f0100c0180f001d072464060142405000626180314142c0b0b0382d1614900051802190010029070151060300c00c0e0f5020f003031107403031220994490740c0303a1400001039013007102c4a500903403600468000505d801700249040b5140a064006590030840c14080c10b210035800503414020200540c0016140c404014180040d155803a0252035040d031501100ba25891388c0a000300d41e04081741401551452803d800c002c507404600180e4481392013100240c4100d4820000804505042c400144040150007080c072044c801c490800032035010038015174007140300b80504000341e0b1100e4120001420284c0c0b001170b101c2d040c8400c54a451780c00c2030001e030a99805101c1100180c11074401000711401405156800000c0ca14040d41808040181169500c000c2c50040381085100204400300e14008d00c400009036410200540e034602d400d0600c1800480c064905900912500442a003d000301044003d011 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 673622401 1250 673621151 673621181
    0x40905150606070b151801140f04110f07020406030b0903040906090212060108181605130204080613080c0a11031b010f0c0611070302010504050d030506150d0f06180e01 74
    0x1900c0e1100c007805400118008550801072101ca02034030b40b61006e803618000c14030b0030002c0c40115a4002801100155052080d00031401e04030040d00c0f00c2d418106440075002d5041d0119102d074030500000f005008141c2c00503040c0445107045c411821400700003081a140b000c03500340401030f5502d006134100d05c035119460341101d800001007203032980328131140c0e0742042001c080d000850001000183c10305404090000317209182a00410140c103007401d0755103003600a4a030031410301b403038030603e292500b400030200b04c14058034409400c2041189003d03a881c0c1822042141e07a2030405180c03c0c80c02a000010700c501c00c0c0319101e00010444820032450416840607910b0003006400a541a01d01c050022000c65109840c0d040d2091004a2400a012524001c2e4008501c0f41040d05109051a0402181d602010b040c5402c02a1a8491503596a1403504414a442d41d8a801c0c074000d800402603840d4244055083c2100010b0300d60384d06031103888882d0120010000c2645412140d400c87d0320b00d00c148008 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 673623651 1250 673622401 673622423
    0xa02030301051003090c0b0c0c0a050a060c03110d020a0c0b090102120f120408250309030213110a110c04060f090506060f19090e2e0504090515060607 66
    0x1c42c10040c00c0801c400520303080c0814170808aa6800b184120550408044040302080d08240c0301c07001c10a8100581017a6010400c150400b80800d050460a0042c00d0520052440c04820140310740148050300707800c201503c1814000c504e00030348135403180b0300581b02505244804100c6030920f030308680641c04140c004180d0284501d0080101380c00240106489250502501014002c1da115992281d03104171412551060243c40003a159554500c400c511b030380170701c000e590000744c000100100b6240c044400307050705c0d130384105040050442c451404005030b40c0429650389464201d10484410a4440281d40c101809403044c8400c50341180b251080d035134070b44181045140e0055008a4102e0740c06800d1500d8550800704850f415444a020030384021290396485120590201082000d01000b200b00141d030309024084400346401c880c4810030401d880c5490715006811031350b482e0300802c4003034000d000a22003070500540352010083d005039a8002080041c813545400b80c229103580d5400702540360 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 673624901 1250 673623651 673623659
    0x10807020606010c0311030a03020d1104030f060f020912060a05010e060d171210170703030503060118081e102f121303020d02010e0c0103090816050106080f030a02030301 75
    0x48010341c13903209809001400e000c0c0b102d41403040c030080002d481191401b50381c80f81141503041c1200e52101090400c050203208c2807000076200c2d20350314052504441d000c1007001000405000038800d1040682d07000c10a0014004001d0010601c1c2d413085075603007401c111582ea45c648524039001d0490344580d0201081c090040010060f070642a0300103000110a42020103071000a060344c041906d100784901c14102042207041041e01d9414400a1100040e202041c60369401914078080030f0301040c18000715000d21104400d0502e00400205404422500a0250103d450034189000c1c00c0940050080b0202280000b04602905505225042c0c0b034410716071001070b181e240301e50501031107540c0c0300d4104540d02900a00e1035403a402448000007882541c2411701c0d0203850600701100d50015641000301044100001050b159a110400c0c00c001c41d010740c2034900100c8a119030b0000d0030742e0003040015081444415400f0700155000d072001ca4841d40f8800303404030781c0c5e40200b9205500503402000140 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 673626151 1250 673624901 673624907
    0x412080714070f0624090903020a1e15051009061503091a0a0f0b041a10020703050118050f0a050a1e1e1b1d090c090f040b0601080702060601 62
    0x103060040440f94903141e903a030382d2203054130600a00d1154540810b00c1004c21441c48040520042c03e00c00030400c00201c50360380c0039444000c503007400b0b020000b00209100d0301200142e003d01240d0b91145076820042c00c10303180440101005d581140d8406ca00070320102e04d22402e40300d09010782d480310f0300e00413141e500070408801401c02082c04645040707960f801e0300e6002400d400780383c0c02070340010004a00043c2c2000404201e40100742c5541c40345080541c0003000300c0c11070442001001d019188401981c1490710203910380b0308a40e00040ca10b40c6405c0b00c141025482c0021100414450000d4030340107244924804c0e6502c000b284094100d40041d0213584c0042c14130f0011101d003c0c1c42e01400713210781c44103031900c42c081c1070500c8494941d000030504000801c0350320b03425480c080c20103564901700c09060900210000b6030111f21304038100c9611000c581111010449104a51030080c85c0030710307034035202e05c0081180e00182c404590061000001c00c0381907000da20300d1449040c0985c020708241e61010011 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 673627401 1250 673626151 673626157
    0x31115040605090a0f03020309040f06060503150109080307030e0316030203100c0201150b0c0607090602070302010e03030403080f04150e011e090b580b0603040303050412080714 78
    0x107804240b00d00c2080c1c00005917404c20b04d40c10b40d8004d4001e192a4880c80c0180003c1c0c1e5140f412000420345495410b0004a4101007500c2e0807200b50184203051030400001079030458005e4000511510021035008100b503401501d00b41580419401e64103103000002e0340c0c01c146401404000c1d41030704128191005008184c0c018a810074a80c800401c0544030007064040f02002c58025800e407440010f0400e0015408010700c942001079403078075072003142ca403030402500d44035503000003410481e1016690f1816a0b081096501071508003401d207507240000310028200754014452515958450401c1003003441c042d00301c3c49004503068541540c941d032421055001c40d40100e2524060041c0302c000410840c8003000601810070148d184071260b588040c500582c20350350301d46040900754901c03064407012800c1c04a4100c0c204da00c00c1000079941d0841520402030310301c0a407001c0c1c0140000c0b04100506078103402c61400361780038100e44101c02400c0d403802c580000003210381d54041400e0403103800c05030b0250001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 673628651 1250 673627401 673627411
    0x4060212160312271208060102060a09061b030902090a0606140d0e0a050c150316030b1c05010504031202031b0c0a020406031a010b04030b0c030709120c03031115040605 74
    0x141070f944001e0313440d00c0f1380306a030340102d01501140700d60041008054040f01002003506142c11300d8a00400001c0d27503820000d11094280d03450300a4541041407903048600041b107500c10b40f00107100300d039030018000c10400e58140d10440b0100c0200d559a01c1c5d40c410302e07080d01c0301f60703a40b0f01d0f100024081807090b90b03205050340c0d11801d41e00e094101d407000050041c4c008091190f4042c010201d010001c00054410810380d54000300d6040081c4103d201e403802c9141e00000550a01040800ba62030008601d00108855405c500c4004d43c110000c001c81035000500c035910948400e0040720703480c2c40e040200d0004a813100210080356010201880303c16018200041c5d1060855240800c568003090a44519038000c4600044210700c41007400d140f401041c0c05040070704155410300d4619101c95a070080090b00e0b100881c4000404a041c07507106203021340141c100f6221100360b000301450040d4440250384802c1e80020114040c081e642040481c41c0c501d6000e40682140c2d00d6100d40d01d581004000c0a08 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 673629901 1250 673628651 673628687
    0xf010611030d1d0604060905010b01020c010e04180f03021c0806011b05070f09090b0c0309030a0c0c05330c030403020919111b0303040b040b0a0e030f040602121603 72
    0x400283e81d00003005824415171048030081504400ba01d0b0086c2502c2071400075074155040210b007003072107036840080701032044000c0f86c0214450b2001040d982c2c41d002c5040d40a42001c1c0750001403818540c001138420700c0500c002c0c04010443c03011000440300b0303100036504d10f40040c2520b0f5143e8941e5010148407078000d070243c0c096820340ea55408502c1c0091190703502c075036400d60b104d22809003031100d80a038642d4001c0b02d0302540ca1031882d181256a07107921403600301d0014001042003030024007200a84510107828040c1c40c009407494400d070b280d2581000c2e0881024848061f40002e1010b6209a0540b04d181203490002e6041606690810040240080904c00c5546110203403030301c060000d01650f42c0c840076559550350754003004000d04609210b8018544c88d03583c02041800f00249051001c581d1081d00442c00322401d44814002801504486403160741c103200104204803100b43d648000c10441c2d42503000c443c44035000c0b094002082c040d070a81080b030071010140c40400320b40182d00c90105000940 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 673631151 1250 673629901 673629941
    0x1081b0a090e01060e011e05070209090304051503090c0a0303022d030d050121050d05090d0c06030608101e0c05040b0304081c0203040b1504230f010611030d 69
    0x10b011007a5003d9110700300160704a0780441203542c0220590380c3d8013103052403080301e00c80b50301030251043c8034280d0000c3c000d1a040300041c011500c14000e031005004e004061000154180201d050381d50400e0350024598041c80d500d6141e03525000c1c061004aa60640140522440585880c540c050051014200a480e800d5401c0681d4400b070004003080c4044040004243d41000c000072952204003d0100180e070351035401c140030440001d5200740450852421030350343c64407040443c90142e464800101040c0d100c0f04041840d6406800c08821340704824121150f28600141d0101079514101d01c2500045812090b46011050b40d0080e11b924003c904005142070741d03880d04048558811a0140c4014001143c440c480f40000b81134491002c007860410350443c00c00381c071841080072015100b2040081100507500f040d4460b600500c4202250801c0017041c0e141400d0300c3c15070800c1c00c4900300080f540741e600110f61306d4018803504018160504c0218240079000701071b00018407060010300300c900281 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 673632401 1250 673631151 673631159
    0x410301141008060606030702071a07021207230d020f0d0b04060501050907050f09010c0606051210050c0c211c0e07080c0d03030902150a020604050c01081b0a09 70
    0x4424924041c00c909a15407a00d249042e01e0542041400342030607108010420600c55551360014880c0299281d40c0c2e154000c0090200010b9440e1194000080d0030074103501c012030048102080b96070440f41c1c940e42e00d40c42c00c0c0314090310901315055003030074540c090911501c50000d410417030041003610401418860000501c3d48454000356000c0740c08642803038075400107001c41e08003008081d07040a00360070102e0030030181c400c00200a02410926034100100030007040d09104064000c04001c15003c0e010413010001580f0460f00d90005030000c403103540c00e000108003c5401031040b1014030400f000584501c000020300e100d046030440d000b0280024082c00108442d08031040c0045c07906034406000502c1b41ea046004909000482d4803900341900200712046c4241c4500100c441299490301c0c0000f1f280f840c5100260741c2d81c07415060288040c1004c15a030f103800d074000804c40d00032400b030700c01c5070f00aa40d0768004560809044030041c1840035050681c9901c4942040a44140001400e00780030b95503c03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 673633651 1250 673632401 673632431
    0xb0a060906270e090d030b22050a0b1003020406020c0603010b1204212703080d0f090f06020702091302010f14070512130b030609060f0102070801020d06410301 70
    0x402d84e000c0b409900300140e9158034581502c242e4015900036a40c400e00d02e14141e0549411010210f1442c08081d00d410015001103d154480350218200524070300c030132840001c004009400500802001d40f18001c2001070314584003041d28100c80c203000c11203252501e403076201c00701d0321400b074421520788500a41c6519603038007428441d801c142850356400b04810704214190000502240c0d002c011804440007840841e88a100703d60506001080100d608480f00f400940100100f13800509052031680013001084907980061002e41d000700c584c1c00076034031080340c81d040c4140b17078000c0240821940400302070f840780100341101c41d8420311000141444010b4840b28104114805600546480003500b4820121a0140310000e400d41440c082d05601e2302d900410213803100603240c180310741120321001600e0f07072081040401a0001d03500964440b40d519902801414090107204111250b00d840810940d188004840c000441d00000d220b14401c2c0d80d400f0658030f001400c2c0d0640654a4888103d08a04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 673634901 1250 673633651 673633679
    0xf02060901350109090302060103060b193c090b061204050622050703260f1801030b09060922050309100309150203070216090b0a06090627 61
    0xd072030002c1005800751140000e011560580220034040e151a000a000c01d83c0003550a054a502450014210303903140c00140c11100d1600910100c0030403e17201044034140302d0880041e0094800b92505c242340880e911052035402c07050f914030481c00703904041002002c1e54100b04481400680711628000c108500e4040c0b25200f100c0980d8950310184c14020150200034001c0c40105c080d8070094000403441e544c2a40300c100510018010810b840c09280029054400700c070a000007c00e4050355130a090500300c0000e4002c4001e0b00442e81100d0213031001c1d54024081c502c00c8a0340104000180d40d501400c00115450103001449680c030b2400041d4081c04100950001a0340a00c00139078444a021080012001e12920380c4410107013001c1042001038118000c0c1c1503844861030000d0380f00d5a424000300c1c940030304401240044002c3c100005010411030f400005065026119074035016160311050b10741040078491507000943c44000c008002200941c201d403503a00728224402e5403541c510350504414 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 673636151 1250 673634901 673634957
    0x110d14030903060c090a0608190204032411030a0f090203030c1515010507020d0501091a06040c180504020c070801090305190f0e0108040224040603060e040f02060901 73
    0x50300025030900145020002e2941c000e10100160b40b61001c200c0104480542034401c1d201031102030004240c00c2c00c400c1d4202640c154000380c2c110f40312956403d250840311a1981c680030f40a07034510400714414001e00a9050903901c00458601c1e42d294908204000c01c1744901803014566100e25400040e43c0074002083c2103550500140445440c0c170044140e000d201810820340340310742c600711809503600002640c1e042d5030100e41c1c1c56401015414400e02600502070000c1c00e420303aa850502c0c608428000460182c081550300308140c6030700041c2a14400090348801d01c000209440800240c174164000704002e982500c03d4400043e51070768121300b90303000e0740012000709001040c03400802564803800485941549020f094803003500d5809000d008100900b103041011400000c0c0540d01c03546e007903018803508101c0100c802c080c1321101000c4c1e6007050060b000024140300f0700040100d40d003040a03000341c2e00112580120390b40d95007049099841140164180320444060800350a40c911a40c01c200b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 673637401 1250 673636151 673636153
    0x30a0605070912020d230304080d030c030b01080f1305030d020316020303151c0f031710030213020304030201060e0108030a080f01060c150f0f1a03030f07110d14 71
    0x150a000c5405807486000d604010303c21540075400c5000b5a44207403007a103a50b0b4100710700c07043c030300198890b844845110110f10303020361200140005000300009201019a141a80c04100020410104034240c1e44900f1200340040d2144003c0f4507000c0c400b00b08a0f811105500c6082e0000d001a51041c0c00c68201c2542c0e140c0c0198007204024800c923000c030110f8007040f00f07840914650301d0800203030002104d100c28110f004030340b0425540c0d80322181c0500103203035907001404840d581c030144c0b81c000c0482241d00b44404a54103464082031050707128040580035668010040032158968040c444c1c002d4200070001e03021503480300400200d000d16130305464081c05403280607650390100c4c601c0207000ca11000d40003411140b550b50040120540c4502c1d18042680c0c0111042c141240da0200b0201909a02008214083c0340c04444200c600340c560001481100c4044c03080e41e8404d0010070181c80703014000d480c0c20445030400005000a43c0d003042042c134150014602050300d4459100c00c0c240e441c6003001c07144c0d2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 673638651 1250 673637401 673637411
    0x30c031b0c1806190e2e121505010e0c09130f020904290f19080d030507082206090b0a090b0121020105030912030112050c0301060b0415090e0903190503060901050d02010c02030a06 79
    0x180001814540350002c0004409e01040d4908584071041040082103951030103800310b0407415a0351000d9608100c0b4540a006100d1502d114150400940c0040a0729100703a2a01080c41590b417440600704120b81e61086628204106250510403d04040040590b0203009071240111a00000c00c40401400803000217044001d100720b8060203d46000d051001403080c10020403505056004c0c0e42c0c88043c0f07081006003000022490b044d00500300d4190000d04085840b001c1020040555001c0e40910340607296031039041e6619005219507100c841d02d40410240700708285070255004000070b54221203044200c3c1e1280b8008440550160070a070050604007150b590b529060103c00c02c5014081c44048000300166072a15050040728401c41c81031140103c07003000008a003902070200400140203401c5415280e01d492522151660710444948440720344007008882d0386441002030fa032191401074010503c903401c2c2010081d07518500c2d0b40c100e0402510041000060702c050080c4202144108008a1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 673639901 1250 673638651 673638653
    0xc21050d0f140d05040b0c12060f0105120a0c030c08190908040929012f070b0c0a0c21020402030402060408032109030c031b0c1806190e2e12 62
    0x480a0b8003428404581c034060011102410743c8e180701035000b100840703881c90b0315282c80c00180d07003500491140c1c400c0c2c0c0041e241040509801600645001d031100e030340c01c1006801003503080e00c035084103445101d60381145e8803a0701c1860f5510780c8008000383c0103d454505181c0d5541c030768410340f80030880260310003500c82c0ea403600e0ba115410b0420440780782400c003041a40d0001d02c0c4070041501d40c001000c0b003a103400c00000790f440002c0c881c00018060b5a041d4590f240c0e024507105a23030354410001190503c00304d42d40000c0ba003101c6d400102481d82288900c20041185808200103500089c000f40da00031010000000c50000400082880708102c0b83c03140d040c070140303074528031f00076400420013415034000b08600006040c0c0401165202e20010100102d0000412042881d0155200320107402c41c0f910300841c0440a8100c01c01c0b4802c80c41140c0d80c2c041c0412421208103840b1300d40c4140002c500c1030b400496040300b00c10807051140d2501792092410501443c8046035409070903030200780d4201c1d80c030340c03294 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 673641151 1250 673639901 673639913
    0x220b0c0d0609020406080a05072003040509090d0f27060c020301050106110c0603151002100e070303050f03070324060e09070806120f0105040c21050d0f140d0504 71
    0x220080c5000300b421810a441c0450282541d00f0040c003010b0300960f140002a0218081d03ca9103050072008a00d1588090b0003c0c00d9030381e01c1c0d101d0301455108030b1030304000400540f000250610054040da07140c1ca490214403405a405d050140a20195103103206101c05605888915420040800b650f0300b40164007907006150840c3d4040c0c0048080010701c4e201d002400c040065001414902552620b40ea0364468001400310145c40020380e030b216080b90314a000315540091607482110307009000b0010b0441c20108540d030b07161180301c0240800d0007444103d541c040350002640c3d00c604107080c0444d158103a141722400440c14020790403210b80310164282300543d40a001c0100c0e42e07501380ea600c0300038104410090500c0000070b0626201d082004038034140d210040c000880340d035500c00300a0220b0305140ca4603200b4494240602c0c80501807025010521080d648160048250040d014042500030880101c50284580021106200000c1a026100c1c6c0150300240324103540c001d00003c890401d45040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 673642401 1250 673641151 673641161
    0xd020d08040804090c0503011e060e060903010f020708090a092a050903010606020d02010e070308120402060d090c0603050c091027120201080c070b0708060d05250f0e220b0c0d 77
    0x78103a01740802c9270901c01150030801001c00e04400f200c00030b40301d40024000a0240c50195441c0703080e54004510f8000300300140d4040e02e00b041b02100c00c0d0081c00c1d00d40c0201c004581600440040d441c80f9407a40840b90b8021501c420114100c2d031500924010540f8003003825100e080c0e0100006030b011481220200381d0a21410f01c4100240001e420700300d1854a0700400c0c0e0084803103101e00b0030f4542000c1340855070341c00115084600300140034004002141424003503d078803480b441002c281050300080d0851445000c603040114004c14460020b10148021902c916085020b80b5a201c5500e80c0c0b41c010412965081e03000f00310540c100c200c10b401c64400101401d0b405003104003811400d01602c0c000420030910154848131520300820203581c2c190000b0018480c0c01c0020780310f4044c85030a03e07110038140c00710700347c0d03c401541644c04441c1c0d55140e060708801a2b2140a42100807900481e03142000320182980324017400040c94445444c07a2990062800700391590035010900190482c2030b10864012 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 673643651 1250 673642401 673642439
    0x405060103120f050d0b010306051305041b0518070e1203030108011107021003090204090c1211121b030c03030406020d03060506071e06061a04030605090d020d08040804090c050301 79
    0x100503000400f000601a8003c12485501040d180d083c4100180d11a6000138014103000f081146071a40d451204401010300340c405680d590302800d011096030041c12512804c440000c0c25028100b0350049480c2074804001d01000104203e4580b400c0507a41c0e11400b03120054100d01c05503540754500141d6a0844110b040301ca001c242050089402595908604130040d4280e81008109082071b0720000b002014681701c000c01032000c40e4000329096200c02d648403022841103001501542d0702c0d500f0014550b031400b401901d0340d0b001110903000c42100404240034040c0141c1183d850b480700d00c0010382180c015400050059200420118a090b40f40c02440000e000607513403207140c8425501c074070360030a5295902c10701840c0c2400c012010805035034401d000030b2041d9010160581c1c818400c01e04554810300c1306a491a0805c00400c1d800d03040410b02d10030003c0642c0080c00381c000e8692050741c010000800640b0b05000910001500e10601c3c068005110330704d595070340d5690f0400c015083c40701c8007005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 673644901 1250 673643651 673643657
    0x3011d150901032a03081210051c110301020a0305090d110a1e142413110d080d0605130c09060305090c1906080603060c0a0f030902030105040506010312 67
    0xc4410200d0300c0d6000442e06680c3c00440000804400120180300c50302e00b02c1c890061505131407000024000c0e4800581110103509140b09000d44855891000d00a068014980e00402c00c524480d000b01d68601804908c0c0c1c40f0b040b800500d400718034000790898021b40700000200344c5550820407810b5051100c14540c8040b41000c03c01c1034498000696209180030780144580000080050001007048801c40b040d5030080c492040d05a208250503110910300320030741c0e444440340b0305c414071203010030100368440c421410101808950030348445403421102803210380c129800d8070505000c500410020720740201e940341c000c03031100d2902d018028030b05031007190079406524000030000e01d84d030f10101440031144d01f4a4086066150701500c5810034640c500c01d0340d0712405510320956104c500c08125002c40d485070700d60b00c3ca1695280305241e00e804040b0303015582124104440f007841c5000d036005040d40f0807203140008002421f84e01081c01c40d601560280e4075a80490010410001a00705104004940386 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 673646151 1250 673644901 673644931
    0x24080f0f030d020310080307150606020d0c08071b03060504020114090f1009080d02011a040c0504030803130c0905090d0216050d020607080a0c03020d02071202121203011d 75
    0x64080e40e101d010302401d4082c1c140d000070208010499a10048001d04004d0b41030b02d981e003103149400c0321481a000c0308420007600741803000a01c00c1c0003042c18443e20340130341c0311a149009980d86003401540320040494484485210075801e12016540c480b001c0c44c49104001845c0c1030600001d004540005920301d8003590400040381c0d1500e072091584400101952081801c0040440503551080c1c9500b040002d846803008144400e54150440c400c3c8804950060f25608a16811700046c0d034400f445200205001f08004c100051401005543c8030040c03010410008007503940702d20700c0c0c80c0d455212100d45030b100d13000d200e1303920024007100c00011103d0005115034070541d040d001a103c201d00c1094815604c0010910a64603110101e407002907004900f140d843c3e0004d24050282c01c8246010740040c07040e000040151030002400c10295506c0c0c1002c081c40c0443c55003001200142504069002e01519230600b020070074020185007c0c1a8100c9140401025282110030081c030050040d0351b194001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 673647401 1250 673646151 673646173
    0xf0f0f270b120102031e0f01030206030c0a0c06150603051e01140d0501150e07020307050606040f0b030a0320010b0d0b091c0f03051f05120124080f 65
    0x8550340d000804408141001e510000925203040011856031550001080007242c80382004d4241303039682e4034500c450464643d400400101c1e142400000d400600800115544401c04806031500b2101407511416038100c03540c0320300a6848441c03201094070a07010081c40241d4050081d560700811010640d10070784a0120002003014040c03046410712400040844407680302c442e0111215034016000380302c0740e20342c5850b101d2404154441c62400d06204000704d40414408412074030110380060050070701c0d0300e603031003004020058440013495007641c449004569860a1080c0b40703002c0d010b510f40801e550740300c80307012214a40703038160201e16900d007442e5441e6566410901d2000b240d0003d0320400c0076030300c81d641d0918012852407407880341c5022030030010040380d2004003010b074030724240c6e0b091000c0c0c0c403031180c1d4012306001400c00c014440d982400c00d01180c01c0c84a82803007a2945207002185200d14070340308021080c80c200f64414500248601804000020440c058402c41c440005224140c40707 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 673648651 1250 673647401 673647449
    0x60d02030703150204090e160e070507030806010e1e09010b0f070803060103110c0304081002030106020c0112061d0402030c010903020603041b031406040c06080907120c0f0f0f 77
    0x181c0c0030082015a0f090780348030000095905031800b80103543c00804c140340c1108145503550074501e00c400b80301074007030501180d10384646207103c1c0910016141d6a042c201180e41c1901c0c90b1500a200fa810410a000c01403070650f520082e07010004000f0400070003813003800d001d100258030160441014a04104501c1415a81d001e003101d504642044440c1d4807038031140012005080d103400544d0940d400411030710700600c3c0c04401041140c0500c001c640580c40c01443c0381069000904ca2100540c203e402080e80030b501984010703500d00d44982000403520f454000020244c0140640144220005d4080204505007001820b0240c10242410061035140d5400681c031440003c000a010800040a5144824240000f100a55800306c0350381070560203c0a0581d40301c00485090b2120b103c80040042c2c402d0243e5001d81c0500707001000707030044c0da0400740d0500c902c07401550201c070701c030802c50800905101e0004910001d050605034034204203180040c080d08442881e0481c00700509003541850981d00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 673649901 1250 673648651 673648663
    0x140c0307060e0307030611180f15090f090106020a020a0f0f0b070303140c07020108150108071107030615030b0106020d0917030c01050c0301150504080303042a03030801030308060d0203 81
    0x9401d02c0c010124001c180c01180c1021071660000f482d40741011082c2070b0800204000c2c1480d003030031510340040c0045000802003244040c0403802d42100b811a5003924552644006012101c0060f00c40800718441c0008034038014000d0b030103540141c014107100300452810000c03801c0102414429240401e040006c03103070451201d03108001c00301c1030015098007010f0280d00b00641081c5140860001841d00540c052065400108203c0c00505031000069510141c2c11407803107205010303511462243d98286096070301c10024004141d15218590000001607218058412030314480303200c41d10042c0c03031880c020407244811303046541035402c4034040d02c04491b40701c0100411194118107105040110380d80181c21072169080450b415424101080b9810103030700001d5040300d10110210010b1000340c0d4040301c6500603401078440c141c004002040210748a91701384100640d40615500340314002e03208004140d040d41e48110081400da0300108241900011382c10740c4881d058824091448140e80005c2d21a1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 673651151 1250 673649901 673649909
    0x609061d040e07030807030e0f0409051b010c140d1707271d1503010c09120812040302010f050a1e0c0207080a0c03060e150a0b06071a04140c0307 64
    0x40c0d64060b045400c12042181600668100805c180e8403d810f040050208200400003402001c0004c00f40e80f440c14030780301e400d1800da0014040e100050006111265104401c41c50904119042010b00d0201c1d403c1103480350465100002843c54503082a000307042107584050b80084007181c1404c001d082134009100800000d44854040009814641d21242400c1d070b503001700c08049040c0514010f030000f1406c1c40d41c000d440d4500c2c44a0f45080f040c00b01400e0b2042d41c0c0c03400e40003414030841002801e80000181010510588a46080000c00b105c05142418110340c107400507034480700300c1401d05400c1c0c801c00e42c201801d0a030030300402a28180090318400c1c6120f244c502d0550303c0d2000d0880e50f2007480392101800203001960b45041c00d40c1407600560306d49000c2074030020b1030903c0d8290000d0707000414181c40000101126420740e2000c900d0030003002603040150b089a0700304010342c00200b00c031046841e4901255100c50032030800d424002c0e00001ca2584032070a540c4082c1c0542c1403a41c6c0020703080121 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 673652401 1250 673651151 673651159
    0x509030f030604110a030510360204080118140d090e0703090204060602150a0515120102041a03090105090a050316060e0a060219090501090e060f190609061d 69
    0x980340c84010a0041008044011042e0300200345d645815905030030040c02024005205002151503001e0302d04c514681d1008502c0d004511101045607143d5900310b0b42910b90030102c018103103640c80c88201d082d2642d185100421502c0c0070110070810000c41c09a000507803a1400a001c0b00044800c00340000100c0d003d40104d52901c80f0010700b2052207508621403480d405401032280c40d0751f0300d00c082c0d901c10511000c03c4450828a0004018041c20b2158a11602d480542d480c82407419609014214101c4e06913040155000c10010402200d00c03083d007048200040540d07541d921302071550f142101c40190603007105400800347c070004a10000103a42c600301c50a2004c03420310f1058500800141800f090783c1031140140030202c41401041c0d805010134082c04151120750210500085030740c4038403406500c2c04036203880c00070b0110004181850390300c00b0001d0218103c2a01d141700061000e01a4040c03115501c403038103c11300105920048020040515043c90780c422200483c5020340c1e261481106030003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 673653651 1250 673652401 673652407
    0x2030a022824050313051e193f08011d1501080c2502040501061b0b191a130603020108131e050105060f06190f02030d060806190509030f 60
    0x2401707010482080c00790b40d12800b2203807490451001c20350703503e00001d011051406090070051106035440b10b0310018550111052110000c0101c803005c03165400001c401c030f240d58031403541034010400d0038000c00d007442c60780740d030441366150500300d00320380758009070741d000308909a400d03c01c3d24001c0080d00d2025400900b00600346944140d0188904d0007002b10b00c40301446500c000031560210080c04c8048a40241c5c1c050150760307260142980c200148460b0100c0980c0c0200c10400454100fa90154000203103000c0c01c440b085024136030105540c8c6130012030302102d0201c0c3c0848818a40320300c0000001d118088144010380c41c40d00041c00220004061207401180501280104130041d404982442d0784074145500341103580c20810b000300002c40b4494000d26601480344402c2c90644191004288480d51400c030031900d4880480e0f41c401d80c0903880055100030b010301903151a45001c5d24000e004080c005220502d0420b01d46005410013004540b581ca14110500a000340d0200403184090103012403a95 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 673654901 1250 673653651 673653661
    0x120c0322050a121d04091103011113120302071502100c050a0909291302030f04060e03071e210513090b010f0819090b09010c020c03100902030a0228240503 68
    0x461f20360310801c55506500c2e00c040703010070b05107203000b070154075403025503510500340c0381da90203840d4429171a80500907a2020380c4c2000500d98400440502c07000c2407058a00d10882c13441c920080d12146402280401d4000c02c9006c02d40e68072040c510300a00292800340f14103010341030460f00000302c41000f01d0a4918400f03c0e181140c0318030b14040d8058408d14403c5503039280c04040407000031010381d0f04541c29401c0541f8074504510000588200c180c001e82c0b03d4030500000c0c0e540e07031074070280074504a0342d80000004803412081002e41c12003111501e520751640d285400405032403135141c0b50300710851462500c51304010990303000701160405405810040165220b1444a00032650310110036100c0c00d04049000c02000154000103000e80f0104000b803100741d007900b409070780b5445641d501d41c0d00350f8412030903100d4031500d60300500615030021382521000001500812107807200e240c030b10310150280e0010924140e000d442040700610703e602d801403415200c0e0304160b00c070b9115401c04104000780800030503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 673656151 1250 673654901 673654913
    0x7110105011a091801060306150203030910020913050115111504020118080604120f0c150507050906130510050c030708030a060803070b0702060c120c0322050a121d0409 74
    0x14125a100340c400c13020075a5110001800390180c0c0c0a1140c260000d180702c00c882c10b0000058a010352540400b81c1018520032010b2710080d04111501907010402c0d00c00020003038454450f070760280c01c07c8104c2143c101c00050300070b0701c0c940320010f04290a6200710300400102880c006556000b0360309207400c691402d001400c03020100c04581020300035008490070b10080181c0050f10f14004a00c60311132680a01e19101b0503031b00d03c40c200d40060100c0f03030861803084c400c040503444564001003e040c00c40c1442030350004150140c200d840300900e080c2d03091300d091020740380c100203e520000700b61800d0f616000c040c03480035440303016480c80202200300110202d07542070a41d400002c041c0c46c1d502d045948582070350508490032a802d942000160084002040002140d0340c100c0707501c00010040c1e040103483d0002c00030000d42c0000d220a07040100d000d0302c1c250816961402c200024092401081c03100f400f402c21803032564030707035080600f4892003416103105c0c41d000b2081c0103810003044400041d05061b60a0017 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 673657401 1250 673656151 673656169
    0x4061d0a020703031418070e07050d0b1c14010e120d0506220f060f050604050d1703100303020d050918150a080708061509042a0e07110105011a09 64
    0x280e04083c05081084000e0021448103440d898413131085404840e80e882c40000340c64030642d038109c0000c0e410410040c0018494110207007420f0041d0448843c6000300300703d05050300041300111000e1700100110005104240550000e05404402901c40d043c4e852032107442621501444459082d26030002030b40540da1840c0d01d84d08107c005081c000604c12800c502c1d40107203907003441c0076000f40c60000701042c45a0b04140440c165030019018074130309401d1504010803140d20306000c845942d10100310029002904000d5401254040b1526000a08524002e400c003941680e49004005042c0080b00e00350b0b65050104042c0d060160f003102003900d9a600710080444403e00311500403501010006914000003018811501c480040c2c0d2290785038900345080007a6100780855000c0f40d480049800f08540b000c1c42c1c8051800c1c401c40c030240b4400031003d064082c41c0c0741c0c400494100d4030000c01c0b00580d005880c4105406002c030007080258144180c240c10710203031641c01480381c50013040c0050710703417102011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 673658651 1250 673657401 673657421
    0x1d0a140411041505010824030d050715020703120207060209033304020d08030718090209010801120c0306110c1504170a080a0b1c060b04061d0a02070303 67
    0x2044545018200180a4010020128015403401c0c1d048880380020a24031401d4401c1650360502d2074888171724118905100c1081c08171202c12954020120381c1e030410551034101c030030381c0340d90740c440d03d603800d04c0b03000301c00a05140310426004001c0d14000030342c86000549240000c55005031100c00a06100c0000c3c0140c450050300b40c80356074000c070440160004000746100124034071800c0000c001502d016214815200290000e401c000e510740001c030754801860b4031052510b04504000005540d40741c036010540d0100c003000e0b41c0012301d0501564080f4007036014008090400c41d44c0752059403000e10348280362201620704c65458200030170400010003140c100c030722031800715418200445100031558009940440c1e60444030030f40150000588025180240e0750f585514400c0ea0740c80b40f040c409040c8600350540d204110740e2001042001c4480d44040403401150b000030744074010400c0c84121000c640003c41c1248031003034505a140a071b8400b460b88a07204034000340c1c45034045d1034168090700e1041a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 673659901 1250 673658651 673658681
    0xf03120e0d0b04120c0519020d0b0403171308090904240b032107060c021e0f0706140a1808060910051006140325120e0102041d0a 57
    0x107200c8244826204200d000d43e020304c0780d05400c0400c80000765000524208028119008082e00d101074010407206501d01c240040d2003c0d21800c8643e0350071a110320101e034110045820780e00c1c0c0c84044181060107a60281e11146044034070900c944945505025140d1010320580c1a000080c0c20045241a00040307800e52540c5070303152004540e00c20000e4030320790016a0081c80b900140002c942c0414042040032200c0c00400c03407a0203170646400c000b500340f07409200b0540c4540f04d062039682041d82c0f802d2511180c4100a0001131070403409103810100e05900000802002100c191580d0b80c4000849451750391034113081001e441d0510100d05021401c6d4001c1205004060400034084008122242414481c480420942e901c0c8240040c4109890150200003180c201003e080c80c400b650040d07800000020314080c61000c2ea5100c641c094004c13545580000710514030513903103d20680500d008071101480250304042c24540160003a02118140010b00701034040483c01e1582d06521004000308000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 673661151 1250 673659901 673659919
    0x303030703060e09060103020904021c1205091e03032512020a02010f080f0412020c0306010f06020717030a1419050333060904180506011e0f03120e 65
    0x10300078006003598400d100d0305100020010362914004504141a07a0f03000304807a038652102d1702444105988448020f04c0d420007101c0640c003190360052419401e40c0329655182e580c201e40820b00194046c1040d403001e0810180c0324492a0740d0303010040c0e5100011114035940e403180c00e8803c11034024031103138009d0a4158101c001c00c4c116540840ea2510840c000c0c0c0300e614403421014070444410700211011190146048040f40010b0f500c04041d180b0244c15104030340c10950a000001d04004080e80401e0844401010820460760140003d800a010440a00d254824050040382d00c0f84640c5ca00a8108000b18070001c0502d801003003a0346043d1a11095074020804240005d455540141d9120707089401001c94100c0c61a40d16000442442d440b40c5240001078006050140e10340260340c92591150701c0c1c404000c9090300e1308500c020070a0158000307141c01e5141c601c180070f58180e020100403440803450010300c8420058640f40c1d00304c907400341480c032a440e10500c0c108d4280c51080c0c04658050920 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 673662401 1250 673661151 673661161
    0x90c0a08070e010b030c091311120601120b060921030316022e1a06070f02040506040204150507020307030c0b03070315121b05030303071d010807120515030303 70
    0x81c03500542e8010340b84070a4030b9880c0c3c41c07420340c540000c0b80c1880c0700039010448031400d410403403070f060708c11405070102064003903c4a041c1041c50700516500610107806d142000760035a481800740043c03036101d02d010440010154041025071084400c154020b140188081c0724480e21a0b42c1c001c0908060426a500c03800c11600300c010326100705880500622452481012a60075403140c070f03100240500c211a0841410980300001d001d010a00030100003604004d00c0080c1c4178140200292803041812500c2101248100700c210740d005080540036500c14001801441042d8400a0960a0781c3c20714984030401840049e244c00e6654100a2280500610001300158120007460045440d600e06121440e0894400c154010070380c8900f10144a8560804010803c8100f001c00c0841e0103040e42d0480b1038581d40440d18640c41507840600041072400034412208542140030170848007442e2689044c24180b0004180d280c201580840c0709648102141da1244440c06520b05400044c05a070340781e02d00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 673663651 1250 673662401 673662403
    0x402180403020609060610120509101d1510120f020d0c0303020d0c112e0c0c0b0909010e0603030c1b180105030a0f08040f0b030114010c02030a0b090c0a08 68
    0x4152044a034171702c42e50000c504140703080f01c8520b000e00480d648494445045940f850003810b0050701d500098022501319512a000c0703070250622075640074112090b00c100303068038a40740280c000300e8a14030383c4902c01030200c0f00240040c40422500d2800144c030400d0320302d0405240b0010b464500a501000350107a00e410014910070f0001201e009401b6a001c1d190303001ea040e52021000c50001b850103130103020015030f0b807801501c0700c40806a0307102c0b181411000e9145e45698124260004004910b005111204001710304203528064103448409070f04050134880818401101802610030141e100300000344113031006c1050340c0b070703109400c001c0314056070402c0c940d40c280035200440280180590f40c0140c050000e4076010724100d8001400a040e03001d200e84504207000301c0b0400803525001c0030400014030b00300c581c0d4424081c003080003000c3d5a0b5450721060602070340041100c507060103108883e480140c1e40c04a042c404003904010302e88219551b0b05401c034204204441034035130028848001240b2220 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 673664901 1250 673663651 673663663
    0x6090d030513081501050402030415050705070b0901050907060c1e14030a0f0f0f1e0302040e091b0d05030307140405041802120a020a0603150504020a031a0a0f030803040218040302 79
    0x100c0913503800c2080c4d07250350a000c2644030447d0040c20b1482c8036a0441d070505000e0b48000d41c00080307480d22034100031b102d035901851140300342d914407010fa441d0024000040c0040c0200d500070075640c107052417a88055035815508030140180f040d802d800d900404824480d03145104d0032482c1850341903039520401424003900b245549984000055406054050b40f540551113098000e103032900c80c43c0c102d8564400e040fa01b2030f650b10400c800c05400340000518000c82c89446401003503a0005442c050303010840300060000703501d1503a0b1084a40329001c101054000c4101d0f60400002c0ca00b00c9160102c5140b5543c1c944075507030085030000e1a15003160300c0c100c001c4d286400018400c490034640702840840310360741c804500c10040e41c407032807888081158501961010f40f01c01d100740d00f5059101d03034410001d012604005a4503020907115030600030000d0160100710711440044a02c420f445060035622110759407103000003020702000002040130f6560b46d2680b41c08140606081c1ca00d135140c20300c2c0c002d495003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 673666151 1250 673664901 673664923
    0xc0609010b06090d020d1b0e070f0f051b0c0604080c0a0f0803030f0a090b011203180609060309030e03030310031401090f0609020409022e0203040506090d03051308 72
    0x946800c41c991401d1620500301e0304080001071060030225025001c10a00c4440018101c6102c03c3c264013a04800000504600c000c0c900c0420085452804840203000d03041d14080180400001030b820f08211074009055485440050f140130104203c044282d502c0e058000f840c15500610100e80011520400916034481c10000d80c3d015a001c0d6403219210f10180003030003000320079002400060080592095000e40c480d00b098400311351901184c4500104490a07045400516100e00f0070100341070700f00c02d41e040e01c0e240c03040742512064034002c0c0c01080311186004000c00c15481e000c50406040c03103114030320b60054004003502e540381410b0401212101440c0700440312241d5030081c1081240c0180300700b000854101c0302092410840e540c2d10b40080010480483e40310703a0318085080940c840301c500b40d1000d41641d900802c21441e0805520740307160030410010842d80200303c140800d40340d110075200400b00c00c0c0c030b405014451a01d0203803582e0050900d0b411120b40d0280700080c0041002403540d6401c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 673667401 1250 673666151 673666153
    0x30108010b060c06040204020913020703020c2e0f0c1e03020d020d091a1603020d020c0a18020f0906030c0d050c040b1806041703040e0105180a020f0904020c0609 71
    0xd03040550602c0310501502188001c0c1e40c1206000401506194005180f1103000400b20002101c800704e620381282c1044c1c10580050340158406c40503410407104108403101c0005004845140960040d1100071800005004201c07103000840d949502071190900791682c804034445039440c2100c07034404410781501c8254014811180d2400f04c103400803e51507103900f00f550b6240d02003810134400c1c2008600404828050003000c0202600da01002400e9044491083c3e010f0941514001d0001340392000f007400d460b1040800e2141044041e507400c2d40322854600815000d602c5810701c2011220500403c0140c0303030031080020030420340203a80b00c01031400c040c251004000a4460104003165401a0b005041207244100001c0d600f05003c0c81c2e1000b46c1400c000c20040ca070688a030401e40c0700c1c401078007948007a50b0002c03905010125003081c041e40503000545040d28080060a000450404041d000c40350141d40001d0039034060600c1c80c01c1300c41c04000a4400d66485007900d02a035038480c412a120061 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 673668651 1250 673667401 673667411
    0x6080606030132181504151202030304150315080706051602042a030c0302030f061309080f12010503010c02031c0b1011010509010c0909020f13030b0907150507141e0303010801 77
    0x185d41780a2060440000480c074a2090040c102101c80003082c0703255105030703490701c01403100144800c114160007103c58030b15500401d101d004900036400d000700c550041d942e19001240123000140d800419546900031416448010b5422030000c41c00401c4c075018a4082c1000300e03601e4079104082d2030088034070054196000c0000642d0044110120300050381c0c8450180101408648503103400301d04010008950540001c2d44405540d5654003a407003180c2800d0024001315038950360b01780000c241c42c014181a0000d000c81603000000949070b2081c4183c15004c844529900c09400d070313669000c074001080181910340c4c1248040340242c000301c1c00c109192040c0d8201400030325009410f000e2406200f84076120701e4001800c1c200d1620194101310350315200303074405001f141c03101906d01d5a002c2c011030141d07601041c9400c1064005080c4443c0ba00800300c144194080010b17a144e20400300c074000d94028203201c2101120f0f5040700e05005100300308105a19008031410401c1070040001d504a61170b010003000303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 673669901 1250 673668651 673668691
    0x31406070903030c0f1a0a050a150503060a0915050708160338040203130201080c0a0e040f06031407050109060f2f0312010608060603013218 62
    0x2820741024000140060640030301c4000051520781c5c2c005019208120000107a0000016032503004002c65200d000180c6603418000e0285080c0f140c040000c0d464580318890904200c08240d4403100600403440030390382c1d100c048060100c090440c0040d10700070030f41070095040c5000f00803e1510306840b0b00030600c582c2101c41562a02911402e19900c0340410522401e50301100c00c200132492204c2105410200f002000c3c41565032031004500c01c10074060105000038035800014020b03840104030703801c480800c00c004950541c1007148605104c1c81120003041c80e2500301295406002507500c002d014000894507035021440204a40c01610700a030303111142250f90b044101c894000300122400400c1100c0c91703411145c0064590003001c04c1042c580c10310f03c01c01c0f09502d1865988000107141700ca00120006000c01e070350101d031507500308004540160031541002ea411700c480d0200c00101e200090914400308201c40005440600b0010040c200072820742401802e400c1000221185240929400c610032 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 673671151 1250 673669901 673669907
    0x30306030c0905130201030b042c0f0c011407150903030e0105060906010e0409020a03020d121101110409090507030b011206050610050a180e070e030c01030b150a0909050103140607 79
    0xb4400e042941381e240c003184080d0019002002d815a1883d002510f40440d080900b5500802e02c60b05d8030885908141c1c01000d1404d035052003001d80b03512402e5040340740104e4060307034054590045c40150804903640d480c0545030020500340c420380d60307150550401d10f409080c10b416611000d00b0201201c024055a5600800c01c280840115283c034042100740b0b403010203d04250344010702540c80038000c5580151030340c000030500e40280e40203c0b880042d000300c0c0002d55500078290340f40740036031000a001e403410111146446007c0e0b0300494801c103581c1c1901c04c003881400c2040100454010130080388c0c03542c4039031b9140c00e500080041a42c4050915011800f0b60501e01024440c20200c0d50350349050404076a0211540c0b001c50002c150065005803000c20400e00d904006405481c2c551a06d0036105500c86c141401d12a80a80c4681030614001c440c240d81e807601d51001c40b030b04d83c6091156903900ca00d403400307031050507083c1c00c4800c003070f17240100100c100701c4800549262000240e0403160340b43c0d2003810032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 673672401 1250 673671151 673671161
    0x5070204150b0a0c11060f09010906090e01030201050a021e160807120605100b03070309110108040c0611070f0b040305062a2520011d060711030604030306030c09 71
    0x16504240c00f004000d003003d1040c01c088a52900c65045040007600c6500092516001041e54040304000015100007668000203504020002424100b4070341e4508108446803150520005e81130140000d180b550503417081c0310b9544501e0000c181c14080c0040c13000c0d0960b8070042d0021500d42e40040320b03004610103000081c48022524125603c42e5030144640d0b0340006800c014040c0f500003565a840801c00700f100a025501c2002d10742c3d8000740f00303102421709260301c180801b0940d0502024505000114003c11405020380b0301608200c007100700b07040403907460319607a03a01c25908007102c03070340c08150040c0e400010002c0700d01a508840403621009280012610b003610402b01c9401031014041340303046010058501000c0310301040103200d15880ea40000744d50300034030448040b0f00b18114412507028a207801001c41d20286001090034242c58a010006c81c0d407030120a1103003001151100401985d20520b1924020180c00c2e900b007030030305240240240c01d250004507244c4041d20b1000c9100a101e10407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 673673651 1250 673672401 673672409
    0x5040f020127051002030c07090e0c0103050105060a1d0a08010203190605010203071707021302120705360406031b0614071e02032e05100b0a1e0507020415 68
    0xc1d00c0c0001c1c0740401304040851800c8244040d80014000391860030310038483c083c0107121800300403c0d1a4030b8214864100208820580c2c181860703d80148810b440300c609075803c00c80d103414582c0d03040201294014035089d049910a41c4507524800201d28068190007450262641c1c1800c1844140348001c1c910588000d80603083c0160310a0003140c0100360000103030002c41c0b40250b54140b0302442034000c02c04882407000200000340d0005006905c02c03101c2450241c3c40b401503d4020305100500322845070b480300d50156014560401842c0080d910f40001e02e0a043c20801001040110340c0c034908a24840145042c01d850740128110014406018011420b02c40850000c4a803074a2011f81e500c0011400000400103400c0301a608200143c5041000c1c01d8408001036140e1102c13016480c1510011003581000c04c1d8150401082c040503214400d00181940d0000c52100c0d02d4a00f010740131500d0354211400d6160001d0300b08804c2c1540e54000000b0712550b402943c080c031007a560101609000880d03445 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 673674901 1250 673673651 673673717
    0x31e10051b0f130f1d0708060109120302030c031809010e0106140c100e160b0f030a0b01020f010212070f03090b1b0d09060b040e06010602151003020405040f0201 71
    0xe02c5010008100104107020700400c0340503920f42c6402403c1d6408649401000c0e40c1020f403e8480040c01203114450f901c007803603181c02481c1d450700380c0008007030008920071540c031348014045030741c10140207205450b5800d4002c01100d4a40d41844840b1060400b00c0d44000d003c0c10882001284010002f00c00c103042c0c41182d02c030702e1005200c1484200940c0e018103000036950155014161080b4120b00401d0400d00a020041c00100a141c0705400c0c520340c070343e0204602850070000070b20032115043c20b0701d0340a0340f801c00010b841c00c2d03c003006034140520500481c1c959440052806030300703008224218028a0240d0b070710001070070901c009600301e8000001c081d101204420000d0316a500c80c40c80703518a19119482c003801d140c0e40c0c110602c20348034068800c03100642c54070740d69099400c02e44039202a8241c2540200295490b20a02944400c0911562507945140f080040c40e0751590011140c02180d001d8000c01036441e09003003240c1c030340e140040c0072400100c1c000010304400518541007606c1070203940d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 673676151 1250 673674901 673674907
    0x11030303010321140705060405010b0a060c0b0714030a050703050a0b091f05060d02120c0906070b060f0603040305180a0807120203070e0712150b0a0c02031e10051b 72
    0x111024802c40c0c0f5205100081204c030b07500040036800040c010740150f41c0b04900420503030920f032a01c20b09680c81019940d0040300380540405c10250301c96441c1700103d40102c01101c0e00c1c2c940c2d10044504240c0340a01c460065000410b00c0750341c1803142d102c0d0780301c1d0040f60f50410494844806140564030305030b112aa001284002140403014a00b14600984c095407002501003640c80010070b02981091a1080c3e03040d90101e10194214200c02210b5440581100341d5840c01f0f40901c000340309030080c0480a00360849000000b10640c03142400495000e600030415a181d15141c03500034103d6110a00e84880310560198000190030000820030070b0760f200f440506441410001103810344a03211005070307810300c90100002402d0000d141164083c01e200d03540c030030100c44035040100a58440503880c0050103005001001840d10200607a00300200741c1c40e04010b41c10722800006d00e401c0b007020b030724107544008000720f1a0400b000201a02d122040d8401401142d51b161103c41071182064070300120446c0030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 673677401 1250 673676151 673676183
    0x61f112803080f060f19150c0c08070b04031b080106120201020c090405100c05070c090b090c030106171503121c0504021018030507140a092a0306030f0b0103110303030103 75
    0x103a01c403106d011810132020070800d40d02d086018190014400010201e00c11200040601070a00003400107044200002c1803502d142c024140803030b00c91448098107554540011210508400740104010401100280162901c4885102103030201c1d80c000ca000d1710603055408030600b4800318041c070594020010345500054460240042c0400001c0030342005420001c2900140303100c1c004034081d01005500142d003112a50501c02c280314090904801144140010000740350701040c002464005800d0b000480c0c1c41d6a21030f4003c59070424846ea5250154805460f040340e0b0f95000b41041c1060000c00b007200540b841c2651080351030503200a9044510740640c0c020039030044000d880c100c2904540c1128844d0303262141400c00c503040e00004038a6a448a0841643c80d240212102030300c242c610030051592000015071201c20359100c10100402d441d980240070a0003035126200958106007001e580840e13500c0d003995420b0703003400110340100c5941c01d84a828103002081e43e068070382c010a40f803410481 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 673678651 1250 673677401 673677409
    0x6010c0f29250311160b060303250c032102010b0f13230108030403061a01021903030e010204080f070b0a0f0810030218040506061f112803080f060f 65
    0x20b207000d00d410305840d40e4001d030b48400084014030b032008180c5001078504426280c40b4040160242506200e940148540c112030316200c040d42503801118841602c06d081c103481d0801304604103500140207040941030080d4060500d5480c10790b020000d500030041e8030039035001c005102065480e400c0c1c0240140303140000c030b03915551022444070800d400010078200e03606e00101440100360448440c81d08085410820062580104005410460040020704600500003075858aa44004400c1e07484048da0900925000360301c07103454240150300a40d61591107101103540d590140400c80d015208154000860b021110f050b1244c0d8021507a031301e66104030310003040721a10b030041c2c02e602c0f280c9403203d400030040c1d98141183c0c49600d080368082d0302529040c14141c0c00c0c804001e0044e80a00d4200400042000c000440344c48031915a0403c0d52801c2141124585007a1440200001d91004503518502c507090b07130309d0300700300c41c078800d81da12003007592100c1504481070302c11341d9200d400450f1100c0d05080703032034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 673679901 1250 673678651 673678711
    0x90a0605060415080d030c031a100c0210200f0309150c030d06180b0105220816081204060509010c0521031b0306150306010c0f29 57
    0x41e0060000c100010310348022110198294450303010b59020081003031105805000720031809840c3d0804000706858030110844c03210009074154490039904030000326050007068440c00c031540162880580b44000c00d07002e40b07207002044400b22078520490310780a0300680040c90307500100000d800f0318100700810b800d100422180701c40c400c15004050003001c0c50a4000c0004d41100503515501207036140c03030540622104282c1d01e8103a42e20b141015801d85d21a6040000c6a640b030030020b0440c00042d405480e5100e45082d02c1d0004869805100f0050b0300401c5040c4501c4261000b44007503880c0c001844024400520440c404c0d0400710b40140409a003a41c010311054181034001c100762442003500d1522004407910b5090100c072025004403c2c84120060100b40514001546401a156003480c0700002c0e407203984500d40c1095824000001001648903402c00705849502648880310070300c0c28941380020b281d402558003003180800500400e80d01031035180300c0c05020758006004400d640000706040c10b034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 673681151 1250 673679901 673679911
    0x903070b06061e0901080a09050a030e0f04020301030f0605060d0b0402150f0a08072010050a14090307060506090c030a09320607020a2d080a0206091203090a0605 71
    0x381d09001e483c806a06031081c00c840c2c10f1854a480b40e884030800c001402c1c41d40054211440346281021100c0004c000069502c40c003901810f04c1600c0c521107000044400780064107050b0001e001100000c10021040550804984100c43c20300044d66a035003071001c40d402483c070142000a220000c540542130520854003402d4040c0306851a1040281000301a5881a010740000034050000c00402c1c40d4083c5e06201c454207200c1c000c0000d0311803020003507a214014505194429640c2000c524015120780c03290b0146003561101c0446883c1c5424869200d400219040e5074060508000402501e04032019922031581116968199207e03104140010440900d08680307144a01d400c868517aa0511180c4111b84c0301e0346182540420500100c504210010b0b01001c10349d84507004440c002440004441080709404030341488164100341030791000100e1100141c00b15000140210400707502040961003541071808131900f00754ae10211081c10b100c200c0c2d00449941281c2400f1b000941903811080d048 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 673682401 1250 673681151 673681159
    0x60f0b131b03111e270102150903040b220602070608060402130b030402040b0307270c0507410d09060e0f22092f0405090a0f0c080709050903070b06 65
    0x25031080c1101d5100c2d0500a52000c5c1d07010340c034030001207581e0400c01140d1034401402d03030030703494205400400c0c1e8a000f20701031916050004a40d100303843c1011b0a4082140b002110306c10142c5035101000303512242d06008050010f00d01e140000c0003403c060003285c51407210a4854120075140644003540ca40000c2c004070b034402e8480422144c250b40400020002d0200000383c142c00c8a010039000c440c540d80c904010340c105082180f8242181d4012060b680b6540c0c006000e6040c03001c8021050184d119041c0220181401540e0031410704d0840303c101d00d48103548081100e883e201540d074251440d01711441100005040402c00401c0c41c2000c003501d0403211070181054421a5962034481001030940445038080d903520f1000b1010b0280d40303c1444004010310525036208998940f021454018020b102405162580b000c1848602c1c2080b15440060700002c42204010007447c4c00340a942a40c0310340138507841100b0300400d812110f482131f40d004501c03a2000b5880d1084a6480704103015005100940c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 673683651 1250 673682401 673682407
    0x1c1701170f0a0c180b1026010302030703020609011206060e0f03030c10021303020402030c34060c17090d030b040b010915020109080c01060f0e040201020604060f0b131b03111e 77
    0x5079440da0560f88215403005c0e221130030040ca401c98030400b1f0b86048613440314102008030041000d0388010807a503064a4054034441da0300c507903a00050b02c0034020400d003054120715007040050613550114a902c8040000c503109a4100444810545e880c0030b400861051703a0802003a0040c8040c00d58024003121084e240c2940401d95650000b80132600f0444144c031507400b0008811362a0030b40d4000c818070403402040a03002c4001a5039001d00801c00e400401003900d90b13150080324040c2d000350484088420100c541c2d912a2402d10882c035100c0d0f840f45810b801203400c010700c2c50300c18079080c000c20181c00010394901e0303c014940540c1c2e010100d80e07100f8120565603982c0d25030010410038001000b012020317000100b1072610700140003040c0401e9900c41c420395401102408010707a80814020340007a04203401245010509500780c00912020340303115408100810402003510294100782071401c078900001c00d018000542c141c003520704040e40c40e00c40c0704003000a0140741c0e12084079840401240e140c1c80381 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 673684901 1250 673683651 673683671
    0x50a0c02041805060109050108060f010306020a05130303050c0d09152102040605070c090903080f0a060e1609050909030a050a02030f070807050c010c051c1701170f0a0c18 75
    0x40c0408860b80240c0e030a800600040c80541100e0140c3c03801005c3e844001c10543c0b411070940103e14106000052401d5000130300f804d80c0320f206030191407444411101a60000b607032440c0141c03540d408000d1130031881c0a6036450040c0301d401901010100c0e5080c66100d809060407250880d07680c2c0c2d001ea03d030380101480940032032409a480c07010348041d11403901c401d66111082d00303122042400035840704485030301b8109a1000a03a100c4032854001086c804215440d80342d4150487c082c00171508000c1c070074000c15080203400301008904900d40c0400f41c851500300c5464005010b00c146007140c01000c95070003007188552840c0302c1d100a0000d02c0552046e02e05024030400d140d1840da1203020152048003010440c8014400e0900c900b041e85242400c01d6003030043c00e50340f0f00781c452000c2070aa01b002d80c03400f800002524091118692460000c1e650001c0a40e1203071440102c501055003500c0781d520584c400d102400700002004040e413038100c4c180d510a107241c0090314460540342e88812003600c0d22017503a04 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 673686151 1250 673684901 673684931
    0xa0c06120f05090a0309080a0c0e060607020904050d0f0e09040f14060910050106030b220207020301090602121b072d03390f0f050303090c03060105060703050a0c0204 73
    0x603001c0d1a02a014110610302411700a006c40110b80020506800c008004000103411001d074408469141c900300e10290b0394140082ca20380035490020f50440d101c00c00300002c0010100750000320842c0c40d168901401000d80c0121404404444002d800c08120004140031440008003400c00900c81c3c0c0c0040091400900183e040500c1036484d12141d622100071b60202821600900740506580e180c20031062400c1800030b0050f1640120f062a091030024030b4249102107038040381c04258000d0000e002c914080d1030814000d600a4040206108001001c04d8a49101602411108240f00b02c0d0030306107a869103600703000700903030100c2c2e081041408102d804c051951014142c0803a00a455403004e881c05030705c0c0545003001c01d8106c1078068450310304150107904045070301c003400d9400901914605c0701d1403400244031900008041d02601c0f000c0200160b1800000e801006140d05505031882c590780c410a101c250302070568000d0102e94203210f8058801d208084c1103030702d40d00080010602c0540b14000b1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 673687401 1250 673686151 673686161
    0xc0703030216140918071a070203060c1606020901360602010506370e0106030b01030b0d110d020405011509140a2c0a020406110a0c06120f 61
    0x44026030040190080d41c00d142c26030040007400340c40d6010005900c0000000c204c0c003002464080051160041c44c0e601800c208110341c0600300103020000310301c0160309261902d4100c1d4408038428845d0304005690f4101d000300f079800080d5010019000402c0a584000194200d00e00d1141048220a6102d01c07181c098020355541c81040c055181c1b0301c03001c02d4804c1840d56013070340044007968109028040c6948507182031490091088030a090510612600800c0303d0303000364a01c2d01e110401c044045030b81100d03031107228121000c03520104a402c032940015400d4485015016900020482c03210011803014295250700300c40003007070000114510b90014040360801e800549503000c20000804021b0341016801c0c000e01a2a0941244d803404200040c40c0c1101e84d0050b03032814058159007070403110950440c00c542e6010380003003450302c0c03900248c010300035003152182c00700056603a02c040752005008101e02881d20f40090702c41e61003505258068130744105021545403a660348164503e103114843c415 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 673688651 1250 673687401 673687403
    0x708040306050402031501050a12051c02070e07090b0708070807020904050106091d121c0e0102030a0501051e090606130f030201081e0609040201050d0507080a05010f0e0a110c0703 79
    0xba0303400e0500525103030419822501000c0b81e01b180050043d03550705da04030740c01c45d203d015034880d0310286898018100301c44243da00045d5446040652541c070703008101c03135043e00c450b0481c0401a82d0f82c2c0310115840a0359100e000d206c600c0c00c00a08000c01c1c0300c40003c2501900421031140340444039808203113032075022202621941d543e540b0a02c0102e0017400b90300500c52804040a10031810500c5d0300f41c80d94000d00d012181090700103080c80c000c0701411480c82e040c02a24004001b0207828002c114080c0d40119003802c480c030303d09000810b9a02c0c110511424028502d07060700d040c1d40400c418440074100140c0400e601480c280300c1408440c50603001280a004100c000960303052842c4005130007000080d281d00c4510f6544a424031440d04d007804101d40c002c0084a0000075a1540d000584241c4074055078550254144001c01980a1700260301c3c9015643c9584200180eaa072075035000d403c80f4040c0280c410302041600819a040c20039000402c482c0f004105040c038007000c0d0030100d460f00340d00d030788 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 673689901 1250 673688651 673688663
    0x212130501050a0c021542061c09021311070501060504270f0b1501020715020d05090a080a1a06192601050903181801170307080403 58
    0x1495010098203008050b04000400828094410350090207034503482807010028090320325400040700340e91118400301510000300149404650742c80d91a0b14035a000c4c0f2080b00010320b4010b8110704c2414500111600c032a11042182d8180219900d06004ae141d050416a888030200300c0c104e100721468882c3c820040d4049048903650615845d00b01e00f990b52a502840c400c40c60300580d844860141240f40f000351041c0c2200304107502c0070307140104000640502c06010506920704201899068102c0510303010400d07021101c41503546c40041400300c0d041595180140c000114410005016201900b0502c00080c03600b800d1580b00e000c021b14000c4164020f4aa038030442c8040104002c900050030b80290041d51210150b440398610404001802d10801018440800101c0c81c1070344007040036094905007400034071150034071100741036030b981180c664180c0b413100603080350b1084c0c17500d0310140d0351050307001155281a0b0710740b00303c42d04003001040596071907000170030410f40003600601c020310255200b10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 673691151 1250 673689901 673689931
    0x705041a0a050406050d080307050c1c18081213121a070804020916050715051f0305061612050403230702090612031318051608010312030212 62
    0x4041041c85505580124041c51801e0710510003034a46040048615400400c655030380d4880c10070841d0140f0a0300344440740d60044401454072011030f225401920801681c030721a50380e2201f031046494450503c500f0190394083c0010002500014018200b640d4604100f0780b500c50796141e010321072403081135044507510500c4440008906051203040e40100040c0750003120b500c1c1681c00305565440140c2802813464142d0a0110014481d0080760100c80d442540409a607090746640790207054192a1034004240c1301c055041c81c05d07a440c880e40101c1e034116000340707165115251030138503401806188408020030030007400310980460040500480c400d5031040c0fa0791440300401c421101c0c1d83d40c20079007008030802c01440542d60700c900c85604901c04941c40700d0400c10401c0101d20358807500748070b001103076000c200c0001c05c8421008601643c2d03114031001d120321342c0c030540c0801c201500034500c44040768502005202140c200440c0d030106c554241401841c10b480070980f0041c08400700c401048044d0f845d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 673692401 1250 673691151 673691201
    0x803041511190204020d140901390203070503040b030105040b0d0f020411090d0c0e090102030906010611030f0f071b140114040b0c06091b010e010c05070504 69
    0x420622200c0c0c00c09460289281d441c9615031607203410100c1a480e0542c0400d4081405542e91603044500c0041806401c01a01001c041100e01c210b0302150038080319441e00c608002e40241858184402d0886d011440a694007100b904c080150608850031085100500800d0f001400401c0200003411420441c65100c0d858003040100340c0b042c440400b030140c070076a02d030280020f290f81c03c005405030741124003180e00d909800601046006a80b0310981c00806460750300c0a008100001c01e040e542c00c0c001101c02c0781d031154038581c240c3c4001d6414400d5036001030300402541c0d110711503c00c00c4403103090640e4944104049a80c0e455000400b51441e20b05001030007a04210300081928181e0720912011822245468090404500c403007064a050180c1314108616030005a402c540281c20341d01500d6499040000e5200e903100001c9135002c03064400c403814420130303119030640d242e140081652190b4115072020300454a1b0248440103c65911171043d0202d21030380d030307030041018801c41d84070210102000c1e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 673693651 1250 673692401 673692419
    0x1e090503120c0301170304050a1701090c1811040509070f0e031501061803120c0606090f0212010e160e0d023f0303040303020f0f12182b020c0a080304 66
    0x404017003071841c1c0d10400003000f4076152014488121640c0c4030034144640858a500b03809058006001000c4400068003c00c83c40f010301a800b0f41056185810016241105c4905040f4450780c01100c4c0d00100100010b4503c911514800c90340c100e0501e019050b04110501191404e41c40007805c85215526100500180390700040920780014040c00f5151000d02c1e548904000800c4010b200c4100708040c1003010034031a4a4100c48028010f2b000c08101b800d100c68460710003508540000c070003c4140c00300002d172010610086901032180198602c00a98900c0016500400c0031000b05821600c480c1c0b242c130250344c41207021040011004c0d1032809074291010104441e0138010305010804294242164020500105903a07200c0d0341410011703941c00f42244a02c3d050300507401400c84020380042c1301c8500c0c00c48000101e00481c2101c0c4a04a0b4600c100782494403140341089007030425050200d11585500380307000d55810382e04980145d401c913441d1000030400360490781d0031510ba1580300050410915803 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 673694901 1250 673693651 673693679
    0x20f030c0d060b0d050307050705101106011404060e07030606080702160b13082a06070f170c0102070818030f070905071209050d121e090503120c0301 66
    0x50224090140300a0020004040e1070310380402400305550742c0c04a6402c0c1d10f90503140300c0520741210449403220307000e142c01a45c62038a030007000d024401002d68401c1240c041d01e1001d4940c143c82c009010240e0910410182541131f04403400e9010351034800010b0443c402c91501c0c2d020b1003003a580845c2a604021000e403400070081c5c000740455101001c0345e041d801180000c20140c8400ca03100550340d243c106110340c6280c201c0d800000c42030041154241220300b0015298000160310039141e102c4004160400402c0d00551002501e00c0401900280004696440d00b11507812150ac4540c249408071700e0b55806ca8001c014121500e040020390385100695042025030b012804400421110706403807115074665641e40304036001c0a0f11034001c142e015005100325000190343d203a0410501d00740d4100b1940e66590b60f0b40000208602c2c01c01c1030074550349801581d1038510500015443da02150300d048005120035501601c00b07000a0100d0310081d0601103c0d90300540004010680700d504240840c3e131000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 673696151 1250 673694901 673694929
    0xe040603030c0b220201140d020c06040b0106080103150b01021204080c010e030c0d02150415090905070816050702010909090321060503060c1602090a051f03020a14010207030f05060402 81
    0x7200c00e80d090700c044c0d4003000b4150321075080c60b0030613211707142110501150244a403032054980c00841c0404072020300040c2a031045004607603002850f40c3e19441599030380f50a0001134242400b00c4140c40701d04040707800681d506039061040303442940440e00007541c20740040e0042c0d40b80c0e13005090040003541e8031203100350030b43e88200c000c5c002e14400c1710009940821b62950080c018244511840c2e915000007003a10001c00480d107001c0f0100450900007030081030340c0d00403114014541404920754038800c4800030f100300300080700003000d0300b081c1906448613000354004034100b140742c030000719a1043c24040d100d4450702c01e80303aa41503900e008090780c040400710600007444501d03184040045903000503180350001001d074882c0d50750719440701a50004481100c8080e40100c5520300740702034030440d40e204170701c1905030542da41179240704607500c103060410030f01c0065031000741d200003845180c003040b0703400402c1c42c0c0500450390441d9032036555001803c145030040d26507801040400065040010310703d0021 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 673697401 1250 673696151 673696171
    0x8060a060603020418090c0803040f1505160813210c1a040e060f030a05060403030e160315060f090906060f05130506030f0f010504020f0f010804120e040603030c0b 72
    0xd800c10580c5d07035400c4445034411400e41c4e11482c5001c01d11000c0134548010380840390079242da958444144c0701224040f40300e207007074074080801544219803180d0280c820071098100a00c0d4039103c60340b00c0a04a0f04040300c8401030340180280003a1a075003000720a101c2800840031300b032010035141002c90342000b040e4403103142880002884071128207090121800d603842e05411004070740b55880030601c0100d10369041c980511500700010107000300002c072184200c0c1310750340074440b03c04182d0403d80c0b150b041d504030400140c0108010f0002a10703884101c0400d200500307000403c0c0d962009030310f41415190381300468090340c3d04c1d0b98a080c00804c4c0a1000a4805003902c0341c440762410022500402d80310001641c3e49582e00041080d9580920001c1900010340c0c00301ca01c0d41c01d00082d850300800c0c0940c1c08034407801500f8164601070400302c00440c6a0036058554070015501d0f52901c0c60030680490100c810485d0181e002095542c03a0700c2410061070203070b5a01c50910b0f006260010303070034130050104418 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 673698651 1250 673697401 673697407
    0x10806060d240207120e1e0a03030e063a2007050f06010b09030709050c090d0c030c03120314060f0f06042313020f03060108090a050708060a06060302 66
    0x1061800782c078035540c90108600384014050590112000b40102c403c010702c50b00c1240c4103840c81c583e2108843d00484070460b0101d1441c80004407102006604d9805075402085c4400c040000c0381c0101c5140f10000800342080c0c0c81c0c209682d40503600c91180300030344ea00b1800005c441d2880a51490440d2100c83c1d04503c00f080010103a601100c1c50030200005801480d40008404080200c24419120b00707444030310480300a561030340c042179101c5e00451401030092190719400904a107803406250f00520342c4001181ca484e50310300a00002000c400c1c015103050320215400030004000c104040021402a100d8413150240d0b0071004040c0e540c00d1400030044079081091040c2a0303510703c030209510b08200c0388807840b000e8080100d10340e4011544588020b520500304c03c100d911082c4c0c1c0b128100902101c01104034103050a00f44100e010b183d802c103101c2e150510010321254003c10b41d0b980c11040c5241142c1e60030f4441e13603a03145001d905420045c1a41c00480a001c120f200c0c5000304000b9212700c2c00c041d41 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 673699901 1250 673698651 673698653
    0x60f090f0a02101e0809010c0201050c0d0902030f0f150105010f20010b030318120706090b0a0c140a0201091205030708032e0501081302131a18010806060d 68
    0x980d40c1d200c101c020b4454842d0609903451039000f45000c042c2409051114018001c89180183c201300088900d642a942845030031007d0903c107100301d612500b05a40300d54100b912900052006000e03900040760103116510202c031040c1400c02141c41050702c420001c000e10304003c088450719443c1a4800c9041c000c140c0e0000b04c000b50042d000e02030790f2001d82003038652101364682e02400340c03400110b840d0305408001884003021040020002c0b00300c000752040010701600d010400e90760b52451040d01c7c00a001c030f050500600300c80c0402490306486030300d024040417823261291040e1034141000340c102c4e644011403050855801c0f4100c0002001e0855450290242d00d4650355141d1107642c0d001003071380c10000002648561496041001c0c03448050310141c0840d00e04014031941b00140c00f8040c00f1807803180000702601d2610380c0104055a0141c00a00408110074860300a8480001c1d03880072410b0100000705903465005403161520748900e4580c0095240c00000307400c00c2d10103001c480c050fa0380520300304 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 673701151 1250 673699901 673699903
    0x140705060703090501060504150306111204030e0d02060409050406060504020301080a080c01111911071401030f0906051f05040e0d11030405040207031d120613060e0f060f090f 77
    0x3a074030054604000c10800c0740744c034180b80100a42d800495015103030140408001d206c3e000b000c020f6030705c40c50703003009012150342400009000d00054150782c400f4060000d80020311403614400f1040014102410000040c1e002610350f8000b40c1100d007000d0f540e90100f00c18414980104070003004207690071807a55040c0b4150b607031141307400c43c0301170124000040e04401c100000d5010865032605192015100c00e030050105100100c02c0c4102000108405210300c0c0034400420351004451280c1c80d503080b60a820300054000e80384588003072001c156507a04075000710f130031806100e100ccc0c000c02403484004403034020b00044100c1135070480d60245140000c00c030088140006e1800005800703060200640040700c1f069861803259070480d941007400481d10004140e08290798112204002a0a800f400072603018031803a03600f0040312a41d50790040c000300c0c0c40422503c1c00304000a006420100340b5641c45500340d8075001c0031074980c01107640214100300341d40101d0400c080d001080c02c806440440640304410f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 673702401 1250 673701151 673701163
    0x418030210020f0d09060506030f0f031e0c0f03090a080c062d0703090f1202010206010b0d021e1e2701030b09070c031b0b0a0f0207080f03010501140705 67
    0x1e450207590004000d001002c10100b0350f04100050001800304952624003880544170603181580030f4480d103042141402008600d00c682c015450001714204421080e4500039200584145001200200700865240400b0700c41001418040f50085942c0c0d05000188007102500350b00801c21a040407428541569441041310684644c84075113910018051051542c04142002600380701e50000400c4030405800c944401c2c1101d00031002420400d9444046501c0b60303c0006c0000e0042e00b0020050201104030005040501d1080400504055000071601c00d01e01c2c0c126200003039610003142e0704940c00b1405c01408104030446000c03c1c03d00503108500c0054451006003000e001d030b032100c074204160b40300b50f100101426000b482c620541c1090b020107480c00c002c5036400d0340060f0300034828841640c481140441060340c840c040417261b99401c0c000d64001c0c6424030a03603100039002c10061010a03004000380840300031400f03489a0f00e51504001500e03241e15222400d0381018207020000201d0004580 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 673703651 1250 673702401 673702423
    0xb0709050d0602090406210605010b030405030304150e0706080103260f0d23060301051f0e0c0c0d020607030b0307120809010c05012322240f0203040204180302 70
    0x201580b2500300000040c050086608601c28000e40140b0070203508407c1384404554a025140402441e62a24a612854031088601420300e40c0200049000200085246401c4a0705224001060501500c0342c504211280d0701079800620b01e60014014003006d038118192a10100001c28070041c0d00000d1611f02c1c2c01000b05001651070040b84803075001140303401982c0e19144034031108408011083d1030380c000c03800503540c80d4041d610304800142c01c80030003110f100d85103c06c2c10340c40072102c0c5010382d14146100001d03e140d1040b1410300081050342d0040104c80321140030307a005014285841140101284e6a0f15182c1d4480c3d070044000300100c4200504052242e900000415036a940c40d100503565000c26003001841c941c42d045440c1c3d107601d00c1c5081021f004800707003c0c0100c035490f00c03540ea129070b100380542e4480c41344021020000040c0b82d00e9500c658140c2d038100184003040c3d8804200115030825909010180c2c00104000441c6414456a5074400054103880c200d042d05480c001d503200700c5c00803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 673704901 1250 673703651 673703663
    0x9010315080606130b03030f0a030e0c2409060c24060904121809021c06050907032a021c030213061b05060a0212061e010810050405040f0b0709050d 65
    0x103d2a00a8200c0b604a288a140080d00f100e03901e240d00c003041b081c294042c244010020380b81c001000c101d0340011440b0245808018204001c080e01c1020045040c0045c0311050dc80100c100440300c3e842d1030f904043d11001c039602c4042c00030050744411000340c0d04410502801401c00403c01c1100701d980d1540e0164221303410852002030081a8001556059540840d12884e800d191400003903070141e540081900b0312120507038802010024080000ba034a4038060143c3c0045258001200a44268800d04820300140c89003242c484030a51004101100101c4000040e04070f000c03400e40210310b0015000003180075103021403070402c100590b002c2201c0c80780030382c0042100903450405411020f4406282c115000010f0702d517941010b18503240254405950002c61603c07a10001d0b17107526215030180080c0d01d0624001686800380001140c80400081c5008220000b0200205081c0c5403841890320031845868040220951410325429221004040e5800c100030880e080c481130b11818151001ca40d4056 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 673706151 1250 673704901 673704919
    0x170d110f0a0f0e1201050a0b030f1005062206150509010c06110d0212090d09050a0902030717010303050306040f1b08090a1a011d1e04060b06040b09010315080606 71
    0x14008488456007019402c1d130107009121420702c0e903036040d40141c0c01078903e11810080c2c05403446c01d058660040a2000c021500250031f01c02c4050ba540d0042640a64020082807000801101003148a44003a5034420002d56410302408808010458542c01d522507046c23013803c0c00c600d500024403401c407143c0d00401e000d4a50392000e540307801c0710702501c8140e411040250b40b1620030240300c0a00d054115070b40c0f00288682031781c0f411007a001d460441d095440c0504842c1e501c0c5e0070301002a010703500c09000740c0200001058554000c180e41600c0b0340c0a9442076848a03503030b0802e84200810b4510103070645a400d0301e008071007400b5040c2004030003441601c0d03042642190f600e4105490808024030000b50501d0304003041617401418070f41c29241650600b224020402400d00c02a008086c0e003100e0480d040e030a90300383c030000001d6802e690703a8028030401c00411402c0c0320b5400b2800035089540101070504000c140e048a66070140203a00700c7c92854845a002580780450315a03071164043d084034011040c0ca = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 673707401 1250 673706151 673706177
    0x70f060905060c0a090b030c190c021e0f090606031305011103180708030c032b0905061503031201030303020a0210060b0403140114150d170d110f0a 65
    0x5600305020254018094940603e040d0078140002c2d88102c004800040c4040c002280440c02c01065a00034203000c94200c0c284465004060500c04265600c142072041c0c3d010000016074070100404804c0e0075140144620188800c01e00c80f80704203280fa40ea1060700e0900400495483c0d80081c0d83e0702c4036181c1d642341071424031420714500421080300910684d02000003000655440b10a144101d1800c410444402036035a0b200e030b540300d01405800501e01d810421100044541c000e1204001a0a0f4441010325054409052044270020503049034680c000f0802c0000d0302240c0800b200d0183c900fa0051031502803490007980b210a81400300606055000c10980541882004005840c00306020104038150302c980104056403c54441120300c1f45030140c00a0403d1818013a0008146114200d42e001d910355031203034920400c038803106a810920301035000000c00c10040c0c4040c0d1209080203802e9541c521004a0f40075166104031440395140104911250014050121020f0508916000b0152415 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 673708651 1250 673707401 673707413
    0x2060a030b0904060506031e0624120c1908030f0708041e0312030204060804030e01120612151503110f090a0e0d08010501050d0906060e07020a0b0903030c070f 70
    0x80c12640c02d8100044008110400030954055401520204c048031554601021402a4503120080303200d000d0f0020710100d80f03c1c886102d00503400d0b50003030030840207420a00c1e000c00e2520b500540c60440716400080e900901d400c2c01542980c0481c0c180d0918842d03c0e0600e112186e903485442c042e0380601e440042c4240601c02c2241c1503801a21500105903041d0418a040d0404900345000a54850001c0b005c03004d0111700074030840381210740b142c0b25103d8580ea10384081d243c0d03090350f03444517050001042d20074161900d1881284007900c0e807410034018002203824841d200b6807070700150380446840d020860044440e41c052100469a100035895800e406403404541c009940d408a150400c11910902a4100e03198221444007504141140c8010946000488520200703124107400300f01c0400890150f040300e60007002c0302d0780c06030340c0114420341d544c03890414010b000c880ca000140c01c044200d10030445c0a03001c003608039050360000d50071400e0076400c00403a03100c0d818004025500f07a030384840805c01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 673709901 1250 673708651 673708661
    0xd0b09071d0303030709030b060f180901141302011d09011211032404060230090a0206190302042408070801050f01030e1504080415031406040b010c1b150c03020a02060a03 75
    0x40701410703044be24544034100306075040c2c00f44c0e5543d406500700511104040d107103982c414030a4070b040f030b4210060075280e0015210900c48144d05015400111411400b40c0c80307820b2854002c00741c092107000e03031200600700407a500d1a100d00b102d1082d00103070084c40e004482e00d0300764203500c103980402c0c0549881c0c2d860207000078410120743c0301c6000b468258808ad0031324403841620b82e1600c0001c080c1c00d0342d61401415915801108802503200a05002e186040310034040c00344130b40611410300600e420b89540244402c9503008040d584941c03207044410081741e500c440040e802c4101401c0c1030205505120003c3e12514280320344904241c3d076014203001d000c104100c206695044200b03807051a080c5820035441c0b41d807280c00b504881da01100b03100294644288600150034603000740ca465076440d0b003001c000251095000c0c860400041e25099030211b04001041400840894626100035140c1000801c20080040c105800e02144102240c0402e4002c203444084a50485085a84800020041c0c0c0109 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 673711151 1250 673709901 673709929
    0x402100c05160609050f0d060b06161101020f030c120706021c0c02070b0a0806060f071505040501050a05090d0309031b0f06060b1309020d0b09071d0303030709030b06 73
    0x720603503502c4000c40580340290002e540741d40c0d640c0c01c1c01075282c0051155181055050a4003c449850282c02083c9541d01a0942039070007000207203416070030495001c0b00b008020701a503100761400405803840da01001406668041280070750308186101900076103030305890450051400c3d0009121040015907812203c10140e4010358006651036191450000c1507003440050140c0710300b8601241c0307074207a141611203a540d00e40d11040c80d035a41d40d05008840d085480410078641050020100048003d0350006507074150b10740014540c6001d003041400e4801c050121800e042c605810301405003000706580c800d02c8880d08010a002c84585011101e0f0000c0c1a00c607000d01e11442c84c14003c0005503081e08076040e000f0351090000c01c0d01c0300c08621881c420840d030034050001c060020003400841740c020f0816032184201c005503203600d850105480240440310f4000240c00042007481545030009a03c09140042e00150708514110202030500c140ca40400b414000c00032000480507074541c0300b00b003801 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 673712401 1250 673711151 673711153
    0x2030a0c0905070837060b040303080a05010e010308030112020a0e07090f0807262d010e0607020d0c111c0317060a060311070209010b0426060402100c05 67
    0x15950300e481c11802000c05458401c0021444004110346505100b0074008450f80c40d6209018011440b80d021152000b035600508050389030a000540c101c00e14004d8402940130b51251802c514040b100c1c48101c9030143c00c04050742c0034220042c404212901d00740d90542d1542c40c42440e004100e0300024904101c070b5070250056480d000b040044599100c20f210085401c201d8014038180d0f140d00800f40c032a015030140b58045400344181c11030500500301440506400001514241d40340c03411208000d1008052a44000703101d01c40456800009100e000d0441030100050000da08000380000e46900d0000354000c1000003144601080c81444010825594030092200c0050281e070b00c88007080c030010500540210302e1100c003002c2f40d000141c0c4c08609c10880144400c1905042c4034080d40107011100c40e48683d00350500002e001601c400f00b4050281071041422a1034525282c441d140f0400311843d25001d9100e0707d85211951040040d03542e4205904456540c40c188880c082200d241040607409001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 673713651 1250 673712401 673712423
    0x40207060905010b0103180b0f060d0606062105132d06050402010e010206010602151e0709050a05030c2b080a0507110a081e0316080d18020a030303050402030a 70
    0x8022056005901d210000c0c0c86c1442409040e4015030086a0b2284024100302401d4000074401e034a8410013552100008000c01140d8003681c82c1c2c1402c0720030a0b00a00b0124814410110003102c00688010115400b180c00303004030f180c103070031214100140140092243c1a1104003401810030320300c00003030500d04070500306440d040908003100030344411f0b1800d0303000ca81c050310480300c00d502c04183e0700e0690340950018990300d58191302a90012b100105560307100e0141d03ca10030130407507164140b039015980659400c843c0c203040500b04419507820f90f2142d4440d030300c802d251b030800e502c03960161a030078500c00d08001341e04015411b440ca009464404004e00821002840114040d0003402811203540207403924040e0440300c40c140290f802c41c60185041540c00f005041d4000700490710944182c4151400f5a41840040b0304070b00007192418004a602d200046003c90080708544590250303c801132408070f002600300d8003c84e01c4038580d800027404058480c0c00003005e43d2001c1001e0103a9a90000d26888 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 673714901 1250 673713651 673713653
    0xe04020d140f010e07020a140109020d1b0605130501030b0310090c0812042d0305030c01060e0a0b01090b0a020309090c070b090607020d031a030a03030c14070b0708060402070609 78
    0x15245200b10b070000041c85441c0004542c600c3c0701400c03d84545055002042d0580c4a030b110070600c0950103441d000d0a41d2511440c40041e151807401101e007030710840d0380d040c2020551030841103079402500300741c00708002801450031900c14241c514048813001e0a0002d02416030b4030210303051011405038a1485402c184031681009803940f040710403203555409407901200143d5810200c0e00c918407400303c85918a00102c249601102d0026450b42e401126030078800d503590b41d070941980c0080d80240c085954400081014040d100ca460b03500c01c4400b0400c1045144030400604294001d02038243c3e0389034045034003050382d402041122580a0020f212006c00d10703242203031154603441100b00322064a506400300e80a400c0008016009041580103400c0060320f420040340113000041c4d01c540720813400c3c825000c040c0c6091000c8041240039036004651031002d0000075081071820300d514800300004204000125500c0c0002c00e80000d42841d1001064803980d001601034014010b000e4603045c034140c0b90384 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 673716151 1250 673714901 673714931
    0x10c0f1208090d050f0901080901020c06090f011d030f13081903030e0114041101050d020f0406180e0c0a0509120601030303201602120609060403230a0e04020d 70
    0xd2003041c0c0c400031240c601000039811104e500424084800c1914180300412456000d4001d19500c10f40d21400103081c00303455805545040ca043c1c589800c2c0f038212640042201c036082c005c0810b50690003c0e0340121070341c601c4600d6641e1082012504501c3c0380803406601c00b036010780e00c900052085804540c0b5000c0c803400c00c84040c2061400450101c0c1c5019a45030140300180181c2204280400c0000748a541d582c503400314201020700d04030304000c810452a04503203001d101030080d807400d14410f030303031118200304014101900003480344a030741c03070810b03010007a040304003200700d50140130140015102c8200c010240c40a0145082c11a489144441c003260704180c005261812280a540c00348048031a201c1d98651103805000f451500100030070032841018002d480ba44000c2d803010b00221001028802e016040a41c140c4542ca21900400180030030b1507440440c0c0d010b40c1a90984020382000e00c0d43c000c2005200d404071842c280f2039014030922182d0b966905440c0810082d00c403d000755000c003400f503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 673717401 1250 673716151 673716167
    0x30201061511071d06010f030e0304090605090a02040312110106050d03020a060b09100e151504031505190e070b030106030b030609030903060103030810031a070e040911010c0f12 78
    0x602c058400d1140000d1600d1010b065040c030780c1a212044c0c1025110380c2c00440c3c41000c01c401c034501f45504c0742100050350404000400c01003000010000d0706c6801d001c10018444000350003848890300501c001d1020601008044080d0585810f0250b09500c001501300d0152280c0e0b800300da400b1100e0510704080c550007041410800703105400400881c0550000c101e010101901c9001c030301c51f05148144400d894507400030b44c000c500f1440d810041d46560300050201c59180341019105280481c04004014204040d00c040c2c607440f4009015925240b0310707801c68a20500452080e064031510201c40d100303c140001c1014014112032a540c941e10f0341c00240141069843c070900912591000800041d800310503a42040002400750130180d1030740e00c04a8013144007a094080310b6001041c000b0015243c01154400812111000515460189005441c0c281c00201503030041e030a240801000039400403502c01c40a009080001d070403d1b803414551541001d20b80700600140032011388540303061b0032841c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 673718651 1250 673717401 673717427
    0x3101a09040f05040c15030b0402030106170108030f03130f050d030605030f0c0303030a0b030316111011060412031503110a23060706020c01140121050304120302010615 74
    0x7051048141c114108400c941080b24058001030000d82c06000c2c070402c01c0c03c100800c454519000c02c180c1404000207049a2003a44003002040c1504548002c010140380d40c0b5004001c2c140c003540c10108442d410101030b100c01408400030400066481003002510a64044000c0c0c00008581c01c030010000094028a41130184600c284500c502c0c82c985910300140d400c40303a102c040c010f10f0842c2c5803100418050309410180690600003803081c1e403034a2069050301e460b410300036441107101c0c08007442070200058006015608000c02c050240624460002d036a03604a41e0203510500d81c80070801d0220018100c404010401c41100c0a00105001c50300c0d9100d28010400c035540c0a42070703554148440790709003007951000540040c6003101424505480649811400f070b42015203001305440b622070031174901c0400c061419410100610151480b180c00300881120120314092070726994948a5a0b4007a0b80302d0038480c403492100700401c0510030340003200105082811202c051034151400380008514000c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 673719901 1250 673718651 673718659
    0x70b16060c17061212030601090803270406031223040806010905090c0328080f0d06080c0d060b13050403080103110118210b010f090e03040e060603101a09 68
    0x400b16800745001403410703d2a0300c489000340601d41742e100154050b03030001000d50f8107002034032800040205e0244020720780100d4014424650700080c40d002e900c00b034a03010a03140a10b03e07010007030000544504810294444908240720340081e500d12141c441f1130712151342c01000402240000303407504001040c90603100ba07518140195038680c6003641d078581a61200f541d00d64030140b200c0141d4561855900041e0841000d0440350900540300c00c40c89920080c0840310050340084e0708405281035105070780c0a0f0503010050040440e00000207a01c0b01c10080010b00859a181d000d44819940e00098000b40251850144041c0c60242005841c500d424402a01e8002c0100003543c85903100304100645c02036031900e000701c420304156040740742d05000c1d105c600c0401c1c1e07020060404980d00010ba18002d08120f100b9014080c2000f00482c1030f1099003d034003039654014031040c01819100b900907a440902662211b45a90360180a40b2600f9120342c806088200080d5005900591141c020100450306807 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 673721151 1250 673719901 673719947
    0x3070804171b10022122081215130c02010e0109030305040201090b04030f0807110d110a0f03170c1c0e09180a200a140901080d02070b16060c 62
    0x1183c01420781c41503019004005880603980d50134020404005038004100c580317400c04100c0144110500c805c00e05100303030390028021445881440c800141281d100b948200707030001d0301040b6004580b40c02d0365078968444481d1542c1d02d070f1808900c02d40c4040c12418582d8001c1c01070385c03490305000e401032000740c4050780014000c000c08a4424400000c4500b00d0342d110014181d42c0107641c942902c0d41c0c004000444085592101e41c2080350344041510790500c0c020355001c881580711a08210354071440344d1141b141448061400c0012640d03054280b1507440c0b41d01e85403a5030314804c09249041c103c40c03c811226600c2500304011501c1d6200817006484c64054901242c10703158001d00048282500c40003040c151320015058002840c0698050340380c403462003c100041e072200c0000345400c0b2058001c00f4041e1007425101081d80740c90f4500c41c1c010000c80000e030400750380051000352541e02d18040c101e0200e80c006141c0c1c40c909190b02031a260b40b80c001d9010003030b400f402c01c4010030061801ea402d0031140c500d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 673722401 1250 673721151 673721173
    0x610030506070c0f0605070e090f07030b03120910051309060f091a010c0c09020c0c030d03050f0f06010507080c01020c1c09060c05030405030703230a020603070804171b 74
    0x29090740f4031043c0c00000d20400000e40d541da20000c1c081c0100080c0811800c00314a01d0b5a840b007682d4140280d09840d6105a94030f840f69008044465071080703940b280c0d021900d407000501e10340c0210307040c00c070b800c1c0e178040c04038185c0c000299038a10482040c6e8202c0f14030790038000340c0703000786a00500903100012860700d58a0f98030341482042e1105910302c0c00800c04003c501c05860760044110f0440d861185000080c8240e0301c0050408030380240c2081d10700354100e4000003120340340500002c070303205805080410060400c2c0c035601a141c003004000007680313100b40c0301150680c0e00072010307103641d640c1c099007540d55a00000038044c00303034003c010340c1d20040c4182c5681b01100820400991418119a901c07036000610303004084444012151007034a482c0010040422280c8082c440f6902070b502900c4c0155021081b030821400e503141d54004000290004204100107a5a003030407a41c018a0f5454500519103d60420a110b50500ca0a9000107000096082c0c2c0004031030101101400c000c000b40e4401500b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 673723651 1250 673722401 673722407
    0x210020f0c10050a050a110f16051e0603040611070f1505011a0d091505010617060105030c0306040f05040b19140406020a0c0c03150c110c06160203061003050607 71
    0x10308101000450030030701440d074619100700c002e00380f000343e02d00d8030340d10507c402651582818100d000b880c40e140c2203448883e0b0245030b08251803008003810360301c0c03030804629211404000e24200099070b11030304000000c40c040c0501c41e00480c2c182d122041c011a5991413920300800b20964402045841c0390444040c030303514080c0c40c81458121a01002e0b1614100c006242965169004180c969055550f59041c0e101041b000080207003c0c0d54292000152035040941c05019200341d4800ca10905050004011040c0d0f804003d981e001185500c005447e6290000020080c21904126110041c5040204814080200300d03150141c440b038040c20440100403100741d8141c40411004800c0c441821020600040380b6900074000030701d851401455440da9039483c035042c2c512640c0240e40b030350142c0569400d044c106109030001d00f0440d082c54507845102101d904e44456400144a12900740402c01c0017140122084d41d0034801c0c0c0c014152411403812400f01c080c2c1000c0d6020955651081200189120340 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 673724901 1250 673723651 673723669
    0x16080c21160b0c0f0403060f200a0c03030216030c0210020c0f090c120106050a0e041a0d0c0b040e0405010b0a03030c08070c0f0314010e030a0c02120102070210020f0c 73
    0x1460784499038500080c2d40760b9030000000901621140c050403c003081c20424010702070006140708610100d400f01d016030940060310303001944003804030032214034042220310131000c8070942d55039070801c450b002c0800d003000c4d0000d0280c02d5100341400084050001010b038000d448065540c401c0307502e8512041c18140c1242e903088904000c0740c2040200a00c40c1e1071349080c0c0310765030380500251140c500d05850f0014a00f1001c20a074460f81c0410b1380441d400c10b0040d000111103e220b60180ca0800c0030b165060041e200a15000504a0242280c4a19070003030002c0d9286000180c102a0f00450740c42e6542c5840c03c0354014101c80c1a1a594030b000c0000b1664609407801c1d40440750103684161910f10540c40b403032119400403804851b4580c240c000000d2030304ca2a49e1117402580104c1c0c0f05540041c3d419130042c01c3d62540419011107030401c100e80500b00b60040703440c107680d5030180d41d2590f0511142403098024442d0110184d0700003448403c22102a07400214403e01507220000d80380c640e0074500600100e00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 673726151 1250 673724901 673724917
    0x2040b04060302070602130815010801020304030e09060a170706120b030303010303120b0910080f010605031c050705060c07050f07120311191b0b03061516080c21 71
    0x808100030400c0000c0c0300740c0103070a042d4000c5070014508440e5a8078a0100300c041d40c01007180e0f4000e08201c0414040c0f4080e018014a01140290310354036165400410200212004910525280d0041901c40e00c1c0c0d80c010202034440d280440f10010000360a20340d442c2c1d214031070580091014070200c015080140900489403001800450841c0d00b9a0340c1a504010300e2a00c010042e5900c03000e000e03180da81d0201c614041c2c0c0f4250040c000c000d04002d4a80c1c00d0103141c01901001da814181d080006480c000365508507a1805041d9840020360307274108495a1040f800090041e100341e206002e0b8016681e030041081601c10f6088031000f0784105034041d01d4002c039100d203941e41101200700a01003170052082c0801881198180d5505a80819102c248881e01d41410364460101000c401400b01c07881e1042d01c00341048000071421803800d0400100e030500032510071500c466020400404443c0d022866007515a48504c507a0307290541e1240c4294bd600000d041500c100401c6aa103201001891046500306 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 673727401 1250 673726151 673726169
    0x12010903090e2a1b031207030b1c03030209040b060a020a150f0e010c0e010804030207090b0a090c0822080301122102030c01050a060303171801111e0307051914041509090204 76
    0xf87d0344a10060b00205000c445042d04545107030024a201c85a080d8800c5086110f0b86006880d0380e540018007048610107440a4011803007007044940c0c09400090500034030b42d0084901d84609200c24443c2d01800a01c002c1b03124550402250342d240e048190407090115902d55074800e459400c41c4011607040d642550090096080308106010070310290b04541100000642803100e19551902c86108a41e1000d41032400107040703000340180450001e030301c40000c41c01e1002c04002c01940ea00c0e4025240700600c0744a40c0d440d40080802e003005040c50a00c1d640702d070300e00d402c401c081d1a189406500c80d440440406150351a240010700c446a4500c00d45085e03940641d41d10500c03004c119400101c0000142c10800c242c0f040111180816a0902990781c5840c030044403940c403400100351310018841c82043c8591124030030f10400c11031950001c240c1e490042040314400745040319000548610110170680c08201d00c0000c3e003c5502c0c0c046c203455441103a0903588103d80c00340d0301c0d0117800490003580240054 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 673728651 1250 673727401 673727437
    0x3011b0302160206030103031d040e031b010e160602010c020613120201111305040501171221070801210c060e060912010501030212010903090e2a1b03 66
    0x80140310364090003040100000129004525400003511030b002640101c0004542d500812300c0b024040425800340c42c0261414000284085601c0e62603001d02410070722098254071500802d04425088007a0585040d000d85000c04c02420b007100c2141414001d0a000d9800e240d04504a14400605203110740200640d440da010500d070740d48080c1d5400384070104115034071021003002014080c07009080b440945145d20340f0070703460141404280c49050f8482820040394290101500101040c0003110084080c1203070b40d40e045074103c928082c4d08040303603c140c2400c0c3d9010089550b402c203032500d05803a103080310b1590a0300003040740600d045041c0401840c5040c004410060315024202204150b40c004100b00d0900040c03401088400185d5800b1490581d1514010015030606150042c440403402000780319000300e44e2005130204c43c10b231240908540058001070060100941a44009418211560805803103482c0e10b1005422104440800054a00340c520b1034280c000103d070b804001405030204 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 673729901 1250 673728651 673728701
    0x2324060a14061b030a020d05190809210325020d080c0c0a050307020f030a0b06190302040c1e0c020915030a050d0906020d08061e0f030304120b060301 66
    0xe01c521031220442d800c82000e000c80b1400621008003600b1103255800115110052403038000d1501044a0410042c800108032240c50106101e200201d042010b0914040ca6140e6064040c90301c0300c0c0c07900703034400f54000c0c00710610f1000d1100000d6003c3c07000710300c00555890b00c040e2000c80244422128030302591290030001c00c0b150055944940c0041314111070350411428607802c41c01c01c85405400c4906410004000085113080c1100c901646000c2c1c00a20030031032642d03502c50522a01500d02c80c444c0e811904084d100d025a6000780000d1071740640144401d881003a009000150702c1d0b03800070000008080f00c0b05882d8450b0481411407030300144204034a8481c20640e580c01c0c4000412544c06006200c0101d0200e4010084424516425500e0340c0c5d40500d0620000e090051184022007048a80010700102e690794003844842c9a420113440c03020100202c00154080c01015810385c1c040c0408078001500880591494540c14041c268080040c1c1d280c0007014201c9a02581d00215601c41c54107501d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 673731151 1250 673729901 673729919
    0x50105012d11100c0e18060a030f06180308090105241201090821010501030b0a0b0c0c090c04030203010b0907080f040c05060d0626192324060a 63
    0x2e64010200010303650850003500110050341e031210004d0000c11650710308080386091050f9940380b405140d2803610000d040160008001e0002c91001410b0340308841601010b02c0b0060b4051901e010710340400603050140b52501810070801200e0b40c000c55403a200000d4005100c0510088074200400078980c00c40c0081c0c020841b107840c10800a00280d03584170180d90028248400521b4202443c42e80010050304500e4006c2d00b45405070003071410035080c948600000d4450030840c1c429603440080c40c3c6d4403050100340c29841d0840d809042980b02c00004140002c1841c0e0f00014030a59000b98002d120021035003050090480058a085000407000f20001f003c50040803030f1240c0051255242d40d41c0301e6070300d000180c06a0400c41404031403550399237081001110030b00184002c620240712401015450281480d00d4262403408403280352090501e5404001c070520382c0302c0300c140618021084201a4444041e907804031459900c00070011141c404002d41061582e240c402c0034010086032695003800013031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 673732401 1250 673731151 673731167
    0x708060a1d06070e1e10080903090a0f08010c1803021c08030c0405040b10020715050c0a0501061a160206070f05030d050403090b04181a030a06050105012d 68
    0xe8520900e0039518140780414006580a800c03255100e02441c41900c04228551800c007a000c21a58052040c1e41c80030b454048290f5400606410071071420390313810712224110300c55480307465071007000040041080d1a58003524800d80b40c00310001c0180c58802041901e24031081c01040000c1c88a4440030001498515080303a4540381c00c40c40e0f2850f8007400c2d540d2028a0300144d91003400da0700302141c02d01c81410244907844031071780102d83c03445115650741006501d981f0743d4065038000080c00c50b40c444c0554064001c54848039091002c030340e110381c81c0d410031900801c0c09020740380d000c4c5a00c600c18540c0d240b0b0381040e1443e07450050f01d011840c407400d03820480e5aa201c4681103600e00fa075640840b01151061025001c11445040003051a14251400800b10400354000c540039500c2408240201003150f8081c00c94289001c100107010340c02454403926009d41c62040d00c1d4944035280f540000c00021f50400c9040f14802e0700c030740d540716004800f503001042c0c0e0303405191f070510b41010740380180512403d82 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 673733651 1250 673732401 673732421
    0x50901030f030908031204020319030516110a06020109060f0603021f09090612030e0105030c070308060d0209191b1b0303090c0b1b0105010f0e0405122701020708060a 73
    0x303c4030074580d0300c05200d0308581000364482c0300f4910380e2040005504041c00103203c80b42441c05031110010b4160f8019201d80030b0444403c10381d240482d075030b0042241508642c101d03180010b000c0d184a0381d9507000203003c3e0448030f0084032024144980b003586034250340107031026603500034004120b29243c0382d40405c40301c041b84841810042401c1c8001081c00085c40b030300c0080c000041c6d61600e4003405042c06442c16000201280c10032a0070020800c1c00c00e1110f0964000341d6040c500070300c040d15403a000910340c03800702602940c0180e5110900046032040c01030b0000119000700140500903882c0e48892107402d02800100103d0030300686111010301101103a0342c103a10074100011540c00f10780307621046000a8201c150202000110614140c9a039502c0c9002d0301c0510000340720642c100f10032540050020300c14035000c52500c07004201080810720682c1140c4210b4803449485080800101c0302c0d4800894a0202500c01c0c280700380001e500c00f20380d03c0140c5490100a10780d5454811480c0010910040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 673734901 1250 673733651 673733657
    0x9260913060b070305041e03151104030212060f1e07030b030109060c0908010f06050a062a0b070e031b13060b030408030f01170705040903090e0403090f0f050901030f03 74
    0x10002c103000c07004030050107001e4040d83d50b042e00c3e941000c17800c80c400d00300c1c0c0140300c002c0070821070108001841d8805540920f0f0300d40201103100400c050000e030181c010794000952048036044c110703030396203000075415210310440111600c45440383c20b58007022120f080c1e240c80d0460076100c00a481d10f4040e811484025002500001c1d0800b0326441e031000302c81c000c2342c4090005041c00350801c8080b80902861511050700755040080d940b500300081e034000d007a8481c0c0d80138056003900300f41f910181503100c10f030200c0c540c100422403032115181c00c0205030780031240400800e24003121002c83c0e0900003201c04101e141d28000d82640360101c0104200340d6079240c011818203071611800318002000b41c01850165100780d506c10b460381400c140b070000c02c400581065140070071140030000c08120000e03100c41101e009aa00140594a5040403154a03005410108a140301082030204256100c6c0940003211a14400c81c009542c4036901500785131554440d9590103000d5000500101d0020350001c41e195220341 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 673736151 1250 673734901 673734911
    0x50606040c1b2006040b07290c0c0607050309151f03150c031419060f0b032502120c0f060106120c0503070914030a050102030a09260913 60
    0xd5001c05984442c100840e00101e0314145503000c00000c1c1006585601c0032076003107013002d050103000c00c036600a0b9400035250104240e1446460190720807500c40f17051104003032003004e140c4104240c5c810b0744444050391803841180c00140e5558818020303280559800400350511066440c0e90f0074005001415641070704810501c407588980101c00414015032180140041d106403100c118800c4502141d40b070710030315041c0090b4060861007905603a03800206005002d4040c40324490503001403100c0d41210340f022140c100c1c0820580e6042024510900a290f90003000404140040084807003422801c00940d12401446100740c0c4c03c0f201409405010508440e400741201011301e00d000002e03880b000201d030800c241c07014010154060022961500d0410743c2ca1400d1051004054011030710681805c9a21138440d40201d0782c041c0204c22101e138000e0025520790400b510381d000200320008040b1400c0003450040f007203410803651100c1c2c2e1032506021545c14034546406001581d844400040324807030b42c0d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 673737401 1250 673736151 673736177
    0x3080301121a0a0b01140405090f1302150702131e0906111303030f0c030f0f030b0307150315050d0b101e091409060601110c13020d060e0103050606040c 67
    0xc540c0e03140c0700d070a6021004c121801020005421140398109010001034208010b001e280c94904206402c5000881300700b803555503212005100c0307460440300940c00b14100c0c4051820404690140a034580200c2d600804118002140c0040f02d09000300c4040e515646442e002c1300204580c48006000d000741408683e440740741002d0340c2198407822000081145660087c0309059020f00340f42884d03401410421420b0304030f03480103400c528211016408202450b0b61214010744a9007214034441e002904a400c1e03545c0314101440c80c00456101d40b400286005040d00e00da0483c0c0e46000c081326800340400c0909221760705c2d20050050b00074202c980f040480c10002502c8281c0740304d40252444c034040140a940d007444e070004242e0701c6400ba800c000100321010301050318000f042e0584c05c41824208002000310794a6540e090400815045510101443d420501c3d03407115001059010084082001422703280c2d1780c81491f00100380806489544250000383c21414503600803000300c107460404001600c25 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 673738651 1250 673737401 673737443
    0x705090a0f080105090d0e0d030e0409030f02010b010c0f320105220302190c090e1e030a0801060302090a0e07030c0206090c10080c16140c0a0308030112 67
    0x540c0d1156503421003107201088901000c1c07148a030000c01d4140986014590720000401a0f10004182481820906040307000c00d0b0240486c142c14801c064400d1112141509000d444030840070060700155082501c480e00740d61048040740c0c3c205034405000140d00007035403508200d024a100f025072110164648070381c002440081404003400421002140d01d24141c40010740d0011902d40d0036481d04942882c01c4006a00070906d500381110b9402c1d203800d03652503420504034013041c541c0003915a5203406110201c8250100d9040515500003c0c01c0d9041c1c802900d41e50368034841c405140c400102c4800040c48104e22a40090140c2c01005101901c8907440e03510714041001d0503500708021942d282441071803107405000c5142e12800110140c8140880da4020400c1d4040311003510082103120740000e00302c035446134285c88501e4400100c003012a00340c0c0c50460084600d00d800284030b84640c2c00c1400c0c4a28094074002c080d04c0e800000c2c03d046074604202c500021407407200441e0340100c03100d20902c2c4644 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 673739901 1250 673738651 673738669
    0x1a09060c210906090108090a20150304080301150e03030415030515030607110f0a030f120216061e05040303060f0605040812070c0806010308031602030705070905070509 74
    0x1005030081c008002030290400c1150110782206014060140182005542d5500544450a00c21308026030715540710084a401e0400c0342c4001405410300d0440d880c5a44c1000e1001810b0403401d60b0481401ca2805221140e80d001c210b8005103a0f040800c0188003041c0700001501c0f4070062030030089081c40842d00020b0071a00070740c000e6050103060519112941d81e05014240c1c00112082c0852240d003801c10200341c5510006040e0713820312002c0e80810780d480e1010800ca81c56400b5040540b403108106280042c40b51080c0210703000043c0c0e0503103859181380340c1d5100325100350310044120361031181c05644403800361025603e8038841041101620030103c1a500030f440c07007940b00e0390b000501203003441480e00c8040b9041d040241080740503c003c4c00b5a1000140c1c0c00000c00c0c2890440b6259500ea00c0d141d0343c1c0255a800030b400c1d5008407400081000b00e540042d5005500c503548094040440034804c0745c0d20300800034050066400f8281c1040401510742c81981c00100500e0302a01e080500d40108040035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 673741007 1106 673739901 673739917
    0x40602090607020d05010209150406020606010e0d0b0718170a02060d0b030a050307031d09160e060a050d05060904080d0b03100e0d080702060106091a0906 68
    0x164908040d00e00300359000b8142d180d02d13602450018086d4021550490007182000584104c0c00d40716030a480070b60703050358001c00c100c0e56040c00440382c01c5101e000a0745c00408110004000c41c3d40800d4407841212141c5410844c19841090b80492411950196a1f9000e072400000c014117004207058041c560115200c0792107414842d2940700810150030b000351315224810740b1408002021010380005070007900c1d1100c83c45404c040340140301030b408507240d80c4020038000048641030964610f200e0a903a5142600b9a5040c58010440560011941304082074020501568940031401605d601c00001c4e155040c0340c0c01c281e03950b00d50310f0040b04200301000e5216a52218103890402070481c0c10000400244040005400807a03240c1c104040345a001503800070000e1081400050040d0491300340e9615000d40034903101e241e20003080d01082590343c40c00100107030340a580d80c54010b0800a = true := by decide +kernel

theorem cover : BRFrame.Cov 673561151 673741007 := by
  have h0 := BRFrame.cov_init 673561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 673561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 673561151 ≤ n) (h2 : n < 673741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
