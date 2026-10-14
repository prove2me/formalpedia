-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1121
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:19:58.04605+00:00
-- url     : https://prove2.me/submissions/2d0438aa-e998-4b2f-80f5-4efaa7b8baf5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 201438848 ≤ n < 201618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 201440098 1250 201438848 201438869
    0x60305060a0f0b060c032a0a080706020f0d0912110309060906091c060c080114190e070c020102060a15050d0c030803070306171501170a0819200304 65
    0x180d1441407420741080e00e83c0c14019001507210006541c0351522a0844600704070307050840d644244a4590200c5140a04c0c244040036001d030803a9902e40c1c0301650b004520030b50303046400300940b10100045600501000b0b4150030001880d0b12107260007a035030035201240500300840403844060041000c011140308000850740180d030b032140800403408a0107800a00756110691082505217140b40400c40c010300c0748150810065021258416241c121081c041d11305903400aa40200660504000c80302c103c0001091240d06a41e6a01c3d01d41c0300400110307500000038030700c0648041103580401c0305a0304990312840c280012207408200e505941c442c0e01c21603215443d501080030500652010003006103400c010a540c0d02e10703007640c1c05005880c1c03074030540403500c03448142c80c0c0820b040490141c1250301c1048200e100359107020000e4035040058a414041c074003440602c8400100e0140040982d0004071000070810090314502904081c5203001d20760200d10031055460388101c0105c101c409a0300308500c0e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 201441348 1250 201440098 201440111
    0x21807080c071115040f08030708040506031320030d08010b090105070f0506130c06030207030c06020c010b060316030e030309030405090411040e1b060705190f02130506010e04060305060a 82
    0x80100901c40c00380724082c0c00c01c2141d0502100325520710000d10503165900001c00c0490b64922800d0352324880c2d45030250221030203010500c01d92501c44000d5400c81c000081600c0701d01c015484505001c0c0010010000c401a0104244228141030001480460090411540c03a42c0742c4100c7d00340070300c1100350850401c5000641d2600700702c5a50004e0a5003a00300342195210b00e0591440d1220352803501040c0c666004400c07000409922a00071104820b505680d0010a02c107155601c8000c0c0d005070685071169500c1e0100c001441d211000510302c60103103512941d14030505a000981164103c4c07031041007a800405c1004402d000c000304440889034241d500d80520344e59418801d4800c00c0b403008007640070f420b01035404490f0307600103005410f03d07030948420244160f441040000e60b201d03001f4000d101d50000e290340c120b500c200b003c410591600505001c1680001540080c850048020007800d00d9070b80d41003807100e15640018030901c02d460998003008004d0940e11941e555902c02081407030035640351507 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 201442598 1250 201441348 201441353
    0x60c0601031103030f03131e02010e041e0f0f05090604050d111f020702030609060712091a0f010603060e06010804060b030106150c0201121401050d210c021807080c07 73
    0x100305c44002c1c00120b80107440b418039041d02c861003202100107030361b40316240030340d075031808103030301000c0d0758694140c450000260941003404068400e20300003580084501050001c0d010040c0181070804114150000c1e001800308022411184042c00d00000ca038400340c20440061800541400c601c01c00d418049429107103006200d2914241d00c10040d0503d0300015861403610b00307900a40300c950310031025a03906986a080544d07444808071900c2c4002001030400546c0801d40c0d40c40301c10014041d54007080c0c4402d451001219600d07060b00d41e0b5a0004040004214180e414451440070b081600c121042c0d070704181c00001c01484018002400c202d0740c84484030000c0d9003d40c4860001c002b0109511120601c04101518043e152842640401e00ca41c0310304038401d155110718504000d0406402070180d0030305c01482981104140201e402e10103038106481040159030310000301d00c80b03681c1e50700c11070813440c41409110881c07800ea801040c0280424080d2260700400320075803108103004141d03220304990 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 201443848 1250 201442598 201442603
    0x3050a1e020a030309090c1e1409030a030e150a050a030f0e0703150b010804020d120207030803091e0a0c06081e0f06150c0601051e04021308010506060c0601031103 72
    0x180c001c0d48902c2d441e600004040d0020020001c0360072445040003000d402c5c62094403a10a9094841c101030340520300b82140341c3c000c0b11030101017100d0701c1025040070505030100b45002c0c03108a040d0041141c881d076005107854510034a00e000b41d03441e42d596050140f0740700050310703a0050240c0241495200c03444444004426801001c0c98100c142c11141026506d04242c0d80c114050300c002c1d10001e003480324010055000e440154001c2d03a000d0142c0440721050340310f40400d881000101011409900c00000110303285201840c0220502001f80031803520791807124403480f02544803c48260820b0004070042415807280e00102d88903801c0000f0507a0710003103e60803a0342515203041d50b00c1c6c80881803040000c44a460b86100740001c0d500c900c05804009001c0c899400344911410030b50340184010701c2542005000000c02e094200b04825003405500001010b9070043c08003005007040080b820400d00300709021b44e9070080030980c1c05920744a1603500740ca45aa00500020303185080f516242122500d04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 201445098 1250 201443848 201443903
    0x5100506120a0b06130b010504030f080f0c07050906010306050603041106040b130f0e04082b0f020306040f020c0a020418080a02150912121009020a020307060e010603050a 75
    0x280c82940d1001e142e03441c00d0a00060182c82c11801404031070b490458500091040c1c41c4d00d200c0503100c141c18249560f440e921a0701449004443c100c000344801c04c0454407803009000010040c2029103000e500f0601400002c40d0000d10540c105414540e08024580380d600c2200c0e0007640000040ba140f2820101007a0240308561228507c04030000e44402e0713014141006805990301803a040811550b5200a081c0d4a1070966000d00010b0042103041c0c43c1080700d404101d6603044018401507155841d444507001c580e01442140c1000742c00104002d040d28152107000401c0190b100111304140080c2c000710381c1c1d1811214024000c5944290160324a600707002030b007041c107a0210f4074030383d00d488aa100075194400060607080e840d4401010664807240030070391061038590116002e0800802034840513581030007501060000c03002c140041905c11941c002030040c1c0196800070b5955480c246082c404869041d00301c441c0907403420300140300281e000708481140c242c00400c00c0440030005080e41503074800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 201446348 1250 201445098 201445129
    0x5010c1b060c091a0408060a0b18070912060c030e1204090e0a02040912090e1302150d090b07021b33070c030b0c1306140705030f03060a050d05100506 66
    0x10131500c0b1240c21040c50091096070301013026240c0300d0b218800c5c1e5070b0a4640d05015107506c07520105040d0092540364081950241e2249481043c0315615110341040c9049014190b551302d454948c031031419a01405050301d2001003100a1501c200800c4202c6458000c60040f040055100c42280180e00c1e401c00210140c690014801c111101c914a8401c1032810420400c034041400e05030b0000c0c07980a1a01c1280c0304100e03440065410150b0790342005141315844120075a01c2c070042c000216980b05c0d0f0300c2040307070309482880c5c038226a0070000c1001e850480c84104a1040581050100c50a80c0f03c08428050400210140312940d03464000200300d070b070819805004544101144101c1440000450b100c01c690040c3c00e261600e44458900300114801c0d84880e000c000800d079410010f0503c90480c850024000030052401c02c01c056035598116070249070150444100401849024600000098005c00c03007211162100038150761000c1d1200c40c000341a1000300e0391940007a03520703120f20085101d45103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 201447598 1250 201446348 201446369
    0x9060f0c1b05040f15050907051c18060b041107020102100f0605060a05040e0106050f03070c0302030c161802040e01090f0f0e0d090b0301060e0f0a1a0705010c1b060c09 74
    0x3104e500100082450108580b4010b405140000c2c02e8205490450700400d410383c0c80c6898030040303144040000481d08800c1207240e0346c0740d100328440c4515504503050715110f0180800c41c402076000300003d50346a10030500e80c050040000200503a00068444c441e0030041001140701d8292340c81003002092140c0c0944e82001c0000307451420300381e01000070001e43c2c018a100d02d10311307605d9540c102c43d54042c048007002070840400218036401d0041e030301c00c4110b52003841217038501070354501490b00f04003446d101c148c0030101d000b10500c604502c0114420f6400d0038000c0c21801d281c5440b56550300d0030300600c0740e40b00881d655454150704814581007640c1c042c50303500c814060b084c14000342d65038441d070140e00d290015500c1100402e003600e0794002c582c1203842c556282d0201480c1a0100035820100f08242c95100700007940c001140300b08105c0b07050071002c80902c3c5c1c5881d0500ba0a041d800c1d03178505040d41c0100402801900750501e1a00d0042605c5900030701c0006a40003041001e40d818121600040c0c51407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 201448848 1250 201447598 201447611
    0xb060411250c03050703121103040b12090a1514090d0c0308040503071a0601080601020706210216030c0308100312120e070803040f0e040206030f04080d0203090102090109060f0c1b0504 81
    0x441100688487e418440c1d0300c807250070300070f07502040d1280994003c1c52185001004202110180322a0840c1c000402c1810f56202c201c669a610b1500120b0851100600b501e0303035058090748035802d0003554020b0315103002c0e001c61030506000a26416101c10300070705020420000c2000d01c10208103903a00c55078800c4135230340200b900040c142d03942e001c08c80d002c90004900200040240d440410345400703d07412703a01d4101080a48041201a0342002d0b0300100110303034240171121060f80815800440e040c06525441c0e082d42c2c2e01d04000701701d508020004210009404e07400c03c0029101c102d03140c0190528940040404994401540500012917041f21984078008010803810004801041240c0340c100011450642d182540d00f80080c0445019612000034000108281c50111101d0383c072a1107920010720709900070008034101c0e00181c91ba007516a601042c51110b42d604400b0440c0030f0310305404c1c0070800300f807901d60003490403140000062282054007a00420480010340d184040d000062050040c3c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 201450098 1250 201448848 201448853
    0x131e080a06050406050603210c1204030c09110301080a2904060e06060102010c020c060711100305010f090203040f0609030e03070b0c1605100c030e09040b060411250c03050703 77
    0x40d1000b50b07004e0300c1081c6040d020a0316403400007060091441078001c56545014213004180142d08004011425800b9864212028500010043c006584218250303900c070341c240540807040743c510800a200c1c0d075404000601c0041c4000827503440c03080d8401400c0d441d1361601866055a03030b800028a80b01c10040005100030000e540c0c1103059003003500130443d003150ba01d03c0012400e0b1428a05101e0150b0170070f410505040c00e1182c0102003083c014642c50000f801c501010038540c0c0340e45688040040c3d56100140800d4100b070301780a005046105007503007141803580b503244185025160050080e03940303110749001c160080002c42003050300141070310a0660348443e0b03402d00c0d81c402d400c44a45070250700c0c0000c025400729000401581e801a113448010f10b0040e1040d00c414900da0000e03424094040042440c5949081086104500c80e8000d03024908100c02404140c4e8014200c42c0d101882c1404000071040c0c0c00e50307005110710312009400b20103000900741540421141c0c0c0002d41035003d0b02d00048203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 201451348 1250 201450098 201450101
    0x60a0308270402121905061804110a15030e070308160f02060309010b030c042309070819050115030209220b01080c0909010b0a05041a19090e0102131e080a06 69
    0x72518003030202044401000e03110320210351b8111121903100e100b0003151460b603c0c000954690082c030072551249a10100b00018003200e00d281c0c03000101b203008140a5012aa06020700b2491500d12070040c60003e095603540041c5000c0c1c900c580441c000001c43c04810b00204000e020400340d0050440d540d01c2c01d000ea80b581c064091122018020f101d0002661294181881001c603280d100803d12840c1c0c0420200400b20960040c02c00442440b6545000c203420700244500210030030751451205440355640703492825503c007100e140c0c0c84040c0c000c1080001d40c4690601d41c0d449514010700d000d40c080500c43c641c1d070701245035101814a07051403001003a600c000107060740b481a01102d00703050719a220495207007078503407002d515500200c03032140070082e80c00c5c1900040058814060f50601d0504c158000c543c0d0242d00316501003028081507010001c00c1028411604200c0c0510000c0d4948a5182c8004c940d6001e588a44640d80c5136103040d42c11046501e600d0749025200c107030103544440c0c045050120 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 201452598 1250 201451348 201451351
    0x409060b0301060518041707080d05060a050916050f04030b04060507030e120d020f0d0c0f030c110307080c01020f030f01050a090603030c0b09120706090b060a030827040212 76
    0x74041e620700f06020503c0d15002d807055110744000360705c0c02c159581c0c0d5a2402001d42041e440000c40d00028029200040d032040080c3c071300c42021380fa0000d214035014081101c8410300c3c2d8041d60060038a0020b03c4285c41c0c810074940080400d0782040c554544141c0021095845241d20143c01e4800f054140030400c40d407508044d0282c076880e034007840140b00040031075403640401607003050300500400500c0d0070305807280c018099249a080090f030410304448680c80c16a140035090350300045421001c003d2290309072150a40d0900d02c0e00d0162001407113808201d90740e2042d41c2c0050074030303000803a44a18460094044443c81d0503041621501c80c00d01100302055040280500b52080c0c6d05104041950901c42c40b0704400c89804d40d03100000340c0110303210120f41180280881c5020b009041d228494654694000c010191141000280f4595207080c081000103000d0401c80c46075201c03040410124549106940304129028801003070203200c404602c15071540501400d401a00220b6100d507a00703850344006 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 201453848 1250 201452598 201452621
    0x40c11010e0718090201030605041802030f0105060a180f021603020f06061005030604063f051e010b0907030b040e060106093005010b0a060503010e0103080f09040906 73
    0x303001103814540030700d8450403140541c3e006040300007242c42c10b0022a0708030002150043c10009800ca0315540800c05668400170140c00b07000f030b01030381c000440c00d0070000d8030748a580202c000c0010342860000203000c02094071941054011a01a5800c0f0341c20983c0310840d1500b200601310740d07a420601040025042c250b0043d40540114404401d01c04000f04400740b00d020000c142d8412031484003005d5889410140c440c0d07411954070b400c00702d03142450324a88007902180b26a05052030100c005241000e000c0c4032001c0740c1e100035603558a0005031001030444190392030166041c01c00d0214607240c81c0100003981000b0f5010030144103000420b0f82551248901d000262002d1041005159089588000a11480c03001942c1c034001004200340e88034660140355822011441319400d2040241d881e80b0015034190303440d964a1526250b5407408422400080403c0e04001d42190302d460315522a02805104c09803d02d5000035070819101c1080341240e81da8007008000b0401c80c0081d013030107801030004007a0f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 201455098 1250 201453848 201453851
    0x40f06031a0c040602060105090c0c0601030516080c030307112b030305010e071e050c15060f150313110d050f0c0102030711190b03040f06060e0606030403030902010e040c1101 77
    0xb00d000488200b0840301612200d0b001000d6603480c01d418451181d10082040e50b6110042c001890140c2060000d44d000f0740c040c01c000c20266044501d40c42440800b61b00510044d8056240c0c22083d440101c04d840b0b840c0d07040603042c0c0d0307418024808a800700402c40324640c5250700300540802c03103800c2c0030074615080d03010340c0c0c04109a1380c886078116462002690141c0200d1845000a45070884941c8000d010f00202d142107400c0260035101d451902c2c00701c101112071810617600b08800c60502004403d5820402c840c013000e5060309910307007441d074403001d4100903034074070544080300034030046900401080c00b0140080f411041607007802603c0f40805c0221205601071010a02c050750320000554101c182c200d00b8000040c0550b000f04040120350040300301d41800b04000c0001d40740043c40141d403055008261084a1172624601541121016048500c0740c0500c0310130b0000316102d000549502940c9400c0019082480f4001600c5010790102e10036400f1341011062100c03141e002d94100c0b080c1088800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 201456348 1250 201455098 201455101
    0x3181e0a0e180a031d0108153307020f0d15020c0c060409050a0b03010e0c0d1b0807090c0f09050f0d08030901090c08030a210f060906030b0718090b040f06031a 70
    0x4480075003003992404034103134020517281100e1411216a281e035580503a4000050009c42410890320513040814a624940200d41001903040140f41e51401e0700c070485100b060f040f2240d44109044c1000501d504a4650106418910b604100a80c1000300c5d001003205494958501500b00541402c8407051041030400504803640d080502483c0e00300c89400000d0080010804103200041d00300080a8550100c1011300203a1003803004901e00113801c0300c001600712135040a00010035201120044000c10a101040d41101c0340d209004105441080f80c100410300304640000d64516010000a05a002c0020038046007820543c07090303500c1403090100c1c181c015a80c240180d164020300000c00c008c100c1400d43e01d101c2140706a414410104980070005c3c51170082800d00c401c6800c950040441d1a651b24030034014071000c40315050384038546103007840d01c1d401c0036481e144030352006109040c5001d03120301f920b40840e540c641050701400d0030308004101d519640d04280217190811070403103c0d01c0600c00d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 201457598 1250 201456348 201456407
    0x4170606031f02070605010f06020f0d0c03030b010c150e070803040812090d0b040f0b09030a0f030203060d080304120e100219020a0803181e0a0e180a03 67
    0x16415114640040141000e50000c031a01204584202c00ca030340e0203a401c0241138005101413044a02901e5400700c00101c080c00e260f00a8500140039920400b0ac2d8080c10003000c0242e03001c1c694540550703141c078000c21481c060b0001690040321580c80185103925181070b00c40258119403101e0009403c100880c1e191540d905455526842a80140d401907001000780401c0c120403c0010190942e001c3c0607100310180e991680c40300b016007520700b151700b40d0300402010f00b4001210300346508003c0003c0034500d0003000807070140907141c0360503094092603004000140325596840d056020240c200345002e40e00e180520f070602c0300c00e6003a00c14030b01044005e12101410b0402c119181a581c5080d0002d051014200c40146140008a04103d078485a52034010136203050500141080d01c150f4111000342c81001d0040244a54a50840751400070000e80b0b006004e40d2440d05210441d42d17511103224864585002218001c003034003000d62180c0c842c252420f020168000c600700001300c0319a000c45601d0f0b0462 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 201458848 1250 201457598 201457603
    0x210b0a0c0216050a051c0b0a0b0406050406080a0b040311070f05120102120f0a111c0b060c07140a03080a08011404021c051503010501082b0807120f050109020417 71
    0x14000d068000002c900e09000a01b40440d845d00605460302a40c190032580342e5861403280c804607480018281c5455803981503081a024010242604680500c100384c24910020341c0c130710b01d807000903107a14807000109003414020210120544c6105096030209615034418100001d02e51151602030b446010400350b10720418400c4d1540442c2840b03501c1e946d9115101082602c10780900b4040019554003465141007000400a01e44451135460782514000b80124040484032030310b218500a038002c020701202034901250040c140c034142040241d025000001085086505070402404c1a400140d810080b54100d5042c034100d4441e6030514005500080c01e22013030340500c561004603130f1501d002100004005402965010440711601043e681a034000a82501e1080e48104065003060010010365483c5070300242c02c40300c2c10451080f40d4011a1401018042d00915980030003444042038022a1100e0b00302c001c20446c425000d000c1561100038007002984580700e0041b410121a101140d0039001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 201460098 1250 201458848 201458893
    0x90a09050105030a12050f0301090f0e070303080a09050a080c03070b090a1e0203190818090907140a08150a0b01020a0c050103110904021603030b0303040e01210b0a0c02 74
    0x10300039202130f4405941705492480741c0410070041c0318042c807032201614040c0001e94020844494046403040c01c0314082d5080380c0b240c503a4031046801080c02800460b41100e603080c2c218900c40400030b9032800d0380c11300c07a08000e5a00703002840201c000a0003001d654001002e44589400780c0c0c41058641c8499a281d80d07903002010700200034840c103140900039100e5401e0108041c0f40058107548240e0030b0b030308000800390143d40e000c484040f80031902483c1c503100754003801d8401d0381c00d88a6401c00d040401001d035a981d8144140851041c0010082445480e490200070003401100c04913080607405965034000381000320780000500e031518640600540c070000b000c90b00315800c2003070303e4074071410030700110058059400f0710b500c1058104072080c00740e11244010510100068012016012289402010b03515603503101340c800e13441440244030300541d2803201d50444440112008a40940c540720b100c2040c0303454400350122036050204aa541c215400003d4822030301e0f0b00340c17403c0000028518100b0000e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 201461348 1250 201460098 201460109
    0x6020601060c03080406110313030f0c080306040b01020102040810020307020c060702010f0f020705030f010b0a0b07020907110a0210030e0f070609060e030307080c07031406060105161b0b090a090501 87
    0x1004030501c080f90103150401d4205024200100340b01d0508551a441940142e606201104040400c0002d042e4400e021040300c1c001490403031100d41443d1908052404040d080c01d02c200e980781c0c6802c001d43e000f54120307001444040181d607502800d03424044000d4004480000c0580500105601280790500483e241960305131142da021070759103002240c1c900e5000c0c030203400b9442006404549a40c0400890740c10701c020074000b141c200040824004807000550040781c56040c02d000c4207006075210200103502a41c146400d41100300c0c0d040c0307014504088900040d40046001c18a5494554150055211504e2050031604800018011796075035140600c54200000d01c055410f012440c81002d0034044098005e00312410b0044e96142c1005c25440200d101c6000d6100041c00c0007000b420740700e0401c48400d03980182180346884400a010b038440c0030000c0c0351a400c403070320400070041d240052913000c000d0400b1801d48681ca6401864507a0311078203440f8030800054500081d040054010704c3e0503141d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 201462598 1250 201461348 201461357
    0x1050307050d0905030316021009020d0b07030b040f05090c0d0c090902060c03041d0c070206030c031305010e1f02030402030c21010c05090406080307031416050609030703090602060106 81
    0x15100d200c229025081240294030302521080c0000215208002031030050300100021044005c07a02c0d00a840c00010414020649060410038005070392100480040250400f00d03e00d10750b52044011002040c0c49100070746d00a140014122012480e54025445000814101c4501c0b01140f01045010341410b10001c0c410b1070090820305c0310505035040f403040d6910140480b42031650001e0a1400c41d0000e4001107581d03c00d0513074800e0700509226940c1c2d041103036031395006d15009076600410340320310001b0b042421070000000442c1d0004821030303c800c200b5410200030020710611500c0140c46120f071826081e1210200680911f03006010310890b401a81e00900411219401c00c0a011074581c0325501c0f402a000c00c441210100f039420b0040c041d000916070307201903a42d103010302000110b455030707084108076a205020407000680c10900ca00b640c0c0b120520352584412400038000382c0300e01c40c003e00400c203008030420702003048800005820380a110351900240d5a4603107008998030300b003d104141c0002c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 201463848 1250 201462598 201462601
    0x151f0e0402090c0a03060504050406090b0705070c233f1b0d020a14010210022109030d09060f11030405031b070909120315060210021c15030b01050609010503 69
    0x8030f1003900401612030141800b00d0243c1e644e8001804039038003154107840850b2a90b41408c2004401600d031680080380341807403410003c0ca500c0300b4600c1801401040c1e86001c8000304103103101004441e221107914002c000d00405000864511201d408130b0302141003440c03c001015509000c50040302d401c803e540f40c0204407024000d680d01d0b07144a1080049604a05a031070440003685a03107400a000e040c0c055820b038401190380d00028039006c1100d05c6000711f18418401ca000d08ca544540305c944040ca083d80102031a180c00380110f04520940b510301000d9441c00000008000554201030140c0c060741c0030401a06180c108030f1240c41c481150000c1c000d0b00700b00042d006071410400c905090f49a0b0800b2a40c2c0d040d00d900084013100c1d891602680d00d8050580e01220103903250083e9022038041c200382c0928280340c0703240071f0341d5030021551b14041940c020400c000348101190320140c0c070401038601484240d1110090940003041d500041d901001c1c61000440c841c10030504582d00320b1410303554980341d0b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 201465098 1250 201463848 201463861
    0xc050105041a0304080d060b070b0c0909070315170706180302010f140c070f0e09010b092a2206090305030306120f0d030213090e0703030f02151f0e040209 68
    0x1203500040c01103c0805d014072003881e8100c00380c440e0314003810130b009400307a56101c64140340e040d8144c020555014800d04120041d66511071010306500070390301d400c0108a0403a2440852891503c2d0380241c22801c0301c2c60421950b00900007422070882d10700d510703001800c051744041c0e00d11b48c4d42d035408040d01180343d04410402c2e09200d01c02d8024218041018103043c103400a90090074103500394405c414604040406000c00858a81a01d030010140c400070081001d840000c103010010041c1060401c00c4d4810440c007201c44a16002c0c10000584803083d5070300c480e402e01d00502c40c0c2c0c0e05c0c02c00080c61280c001000c5110ba00864606064940000041d821950b444e01000100c25020320221100d0042c000f00070288c1c0410460458081d41d191005a26a050030381c05000000c6182d00000009007001040f01030144085400ea05491300352401a2000340b0445040e841c20341c410060f11303211300301d0b20704204c2545860710a01100c042003510401040345d6800c43c0f00180340082c0c07000786d441040c1d000407404 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 201466348 1250 201465098 201465149
    0xd050c070f0b060f0306042019090507260601030e151008070f08030d0b06190903151503020d0c050306090d030501060512070c060f0c0503040b010605030903070b0a1401080a0c05010504 81
    0x1902500404610340e49010031070708a2700d0206540700f000030686501c1801410b54118640554010800206210180d0409001e0300c0200c5c01410403030605980d01111030344020709208020003c203aa000d2050542840c50240405030f4092048502c0382c0900080070400c0507440020800f1520b4080003181807503c08401c4100812203a90307261ba00410402040c11510760401c0848241c035221340f03600d1482c0d17195042c12180b40c0c00c0c0c418440c0c0d01510703001a11040c00d451484034801d4a0b019102d000301d802c942c3c40d08030020205504001e0341803040d181001030320100044c28899081d400d680a0240341d13030319001a1400d004a00d001201e4096403c00240070701c2c0301d98a400c041c11f001b12400b051000d01c103d1170301e040b00c4d05c2d001c049001510010410003802032403a1a40e00621603458800d285180a01d043c94a030701581d403008000410b00c0c030102d02a08840d40001d035100040102c070a91035691007900958650391094101c0300244100301c0050590701a9059030300b1600c0f519030100540d82d05024042 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 201467598 1250 201466348 201466403
    0xc0807081620010f050a020c0a15020c160306180f021210020a020d17060f091306140402010e0a0605160302190302030a090b0a050d050c070f0b060f030604 68
    0x811803000c0b24400c1070640c071441800c0b08040e0000020f81440b600303101006841c8000c01051840380100304103440c0003c00981d00041a0304401306041d42425001c00034040d11900a40071030621034074954000098030074084000301d9126803030411010001c2d0003140480c00719408080c0c00340c510803100038090b04001c40a26404415001907a12440e88000c4c900100e801003102040141d00111841801036041a06000c400c1c4107455640308514100000400800d0301c5181036000b4624240443d0b620036800c10b80d0301a040d8005030a2000e01007445900f00e00340310032581030b4005091350300500400c0c1041e01380082610060b030f5885140081c10040300740b210380240011411449001c50941e0058140075010305414880c0d8090359460801c04d100415541c09500081400c0d0010020000400e8200d01201c01e650010580480e0741d03035401d0020a090700600c91b003e4404504151448101700c100000e2610881003185c0741c0d83c0b02e940402c10f05d43e80b0542114010103800c00701d184416242c0f4002d2201 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 201468848 1250 201467598 201467641
    0x61009031709120d03050105010e0a0f05040e030706110702090a1a01110309030105010f030308091612060207050303100f06050408060a052d010603060e04051c0509060c030d0c080708 80
    0x3a9121006680e00f5203000c02c00c03140600040d03950001440b09692040a030034801908480a0b40c0d240d04211b08121100c40c02d10a0900c1103681c7c003007a51503d034007417099030344194029604210b844640d01c0702d080320f944a02c0c8100d21451101c4000b4025403500e00c182e1011044424486d240410308800540380b005459007005034074403090090003500da80c00d0007228040c1010044110b0b0381861450301410103074021b0040e02e02a003000141c0d1001c1c02c0704114000458103000f003000c0486504c0e0a000000b8400c04e007000d0500d020000400039401d04290004003295003902052100d03a41d20b0000700c51900541c02910840d40040700852280041604515084103c11000c1c43d0000c003100c1c07004c0c3e5581800c020048404045000410000d901403107104014012240740d06500c1c9410340c0e9954039004041420042e007441c81d065000d100340701d0410358030110b030003803c60ba580d074500c60400355980e00300070300418850342428145840c4601c11300c2424040c54182c0ca400d000d5485188200c009000501e07041c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 201470098 1250 201468848 201468859
    0x60210090311010906060e0f040506040314070b0a0b0109090b0f01050c030d0903020d121e0203070e03010518060a060e04080a02030705060c0a0f170c0919030308061009031709 77
    0x2c04100350420700c514140d071403040000080040c0350004140f151803006100e00405460f540c10000031800210760b1984c4150300d454540d0400e01510300e0000c050142c00d00243c00d0816407010480b881c4940c0c0d102c5007088000740c1fa10710290b0760b0350648900f505d084164054211028081603400c55025202510b41d0041c01000c2d41e00340803094000c00200c47d1207290681c0180e000c40f00f8078012030f40181c00100003d413100002c0c810030f2451013030610032080c4030b00b02e00c80440d800000600194812400d85083c500024001d0200341041861142041075170410760304180148004680520355034402c04080318640010141c05079503584900403290040d034a00c60550104100795000188240480303803203000356280380340e264500f20078001d254266602e10345043c0801c0d010f0b030301505082c001da101d621404454180c0d41d200801c0d8040703211015001c1480c440d5801d41c02000c000c0642080046101d8101503030141c0c80145c10950480340c5220511000c5c1c807402c8124801110740072a01c00509103078a01810 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 201471348 1250 201470098 201470117
    0x5070b0a02030c01050a09021e06160f0b010303121a09040215160309030c0503032701030e060901020c0114040f03030b04020f07050705010206091b12120f04060201060f0602100903 79
    0xf855425541c1c100d407482101e41d52080c0c80b50862070081401400e4054541e0f030070b002314801c680800e82c41c0c0b0409040c0e01c01540200920820015110010280395a000304001c205596034a4094400d031006292411024101604c80300e10001a00e00c3d0082d1010042440561762120b40a02a04800200e036036244254204841024168407000001d0304600c20359900108515505103440a4042604810300c41c5c1c008000c18031300f6040c004818549a43c070458120f440078140780050700201405041c00103240900010069041810b40c090081d00c0040402403045000c602020000740f0000c540092503a5082003503840401d119522442003450050302c01450b004c1d09081d0350907242c008550484407030748081310a00c60f42d641805a0764000000707038014046080700d1008614100090709101d03001d08401c90341004a01c03410411254503003d001a200e40e6079101e41c0800c08207a1040c05500c000d5820319800103050301c130401541089500070f60203402c08441103204100906103800d003c0c1c040011858 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 201472598 1250 201471348 201471367
    0x60305060c070c0f03030c150b0301090b180f0304060f1b08090a08011a0409020409020612010311010e01081501030902060c0d0306050d08030f09030c0a0c080f0a05070b0a0203 77
    0xc8290300550381811081e48a030164034000c11242541c0d0024040720070340940400c0000d81041a0026180d0720207a02c07a0107245141c4038000030459150703c19850f40c20724501c20b0a0141c80c0c06180d0050300b01d4660304044440170403156039242582062842d0740da20070441040500d10130240d2801c1410245403000500000d803000844e1500324000581d001480012807400f1440d040c0543c1c0014904034000340003c2e491105002c06032003407030801c540915151004101103540d15400b025641d94002c00d100d4480d90f21002c044001706090001f02d580000f8100c0001c00f9600844c01c21307190020594a2803002d944000300c2140003500c0701d280d68145a103803009140143c1e900c0000d040ba2000da04c00812401b441031000070152645a40424050003100d00c04038049400401240d41c41000c036100703000f031511031844451451090200b00340080c0a5a101e01e8200121171030a00202c076052401c5800305840c0b11295a150390340f10000905907400f070202088170301841c102a0403500a0340c0140e80c01c1c81241c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 201473848 1250 201472598 201472603
    0x1b0f050d050309010e0115060309030905030601030c050306090a110402180a06020303090712080d0c0903060f02030411030d0905040b0a090e0c03011b1704020a030f120219030215060301060305 84
    0x51100314040788010040041c94402441210340d0212030300700a0040070b607000358081440700d40340100d500305900d4a5203001414081d018040090801030111052580d60b8104080000345500a0620a001c0c00021409000c0005022440c043d000840366103000c004804100080d0300045550310000b800b4000300559960750488040104031035006541e90340340120203d414a512038100c0d1000f50b0a0b441c80e070000c1074404c1d0603603440c0801d115000030000201c44059031000095400288620300b01400781002d0005600a140690300c42e40c23407812800429030800d9110b095000c02c010008d9a428020801c81c50103420002010b100a05236920558952080030f05442c11500c40e00d50751350190000d0000b5060034030400c042d2401030b404042c0d0381016004020800da0701004500103240401c4080b400f50f64518103000015540900e24058201e524940301440d000504810700c0503008002d960844111000d001030341e5980c1c140c2c0a41410946080380402002e8007510458041d03607104400f00005504 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 201475098 1250 201473848 201473863
    0x20a0b010906170313060c0c0305011d06071107090203100f080307030306090501050607061505190302150307050f0f0d23010f1404091b03031706030a0b0a051302041107020901151b0f05 81
    0x34030412a0331034004082081c50140003500b98401c01151401e0000003400125204c0241c54181d04050b0303503038803285107a4981c113030070b40c00003c10700110403000600c1d841c002000740100d0b8402d850a105150b6a9480401240c209100c2e294011b042005640000303104c0b580030313092070b103c0340c20544041602d84000c03411400281d210a411001d003080e0500541c41d00105546d1034050300c0d141985103103440d0318009d1841c0603008803c1e0000c5070101d4a8030b0f481d803d107003d4400c040c14034075007000900c03041101080380c4a000c5c0b0b85210a502402c0000c640300c40d1601f074010548030080e2a400c03161000c1e0b0140001021000b10580d401c4030309800030b4441d18020010380c1c00540c040c1d82c40306480f14000d070390000c50b4030019012910030303441400700e40005500b2001883d4403542c582c00014403a610450301044207005840000c1d403140c5882e26415441c0e01c2d52004c2d0100d14020342d08039420b40c0e01d0b00701030554075060300500070100750038403030f00d4241c0c02c4595000940c052281c40300400c5601c3d00e545040ca02800c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 201476348 1250 201475098 201475121
    0x5010e0c1c09061505040e06040f02010c030903080d14060108100b070309091d15041a0910060b0a0905011b0b04020d08030411040b0102010c0e060901020a0b010906170313060c0c030501 81
    0x1036013081043d460135020f01c2c0b9101140ca80034154608207903441104c000880a0024140800c004816051500031601c010081d030f0404996a5950021100d540040c10003e0030b8100e600e061501103040365110b1200d0341d2081407a50000c2000a0410186942c503801c212400c030200b00d00744002003a000b05d24020601d0b81f100c0f202c40652a8880301a0843c1001c410300c03150302c6802070718000c000c0400c110a03103500081c031002804030700c07c0d21908500d40c20a04610810801241000000114110003000030100c0300700d650b61f00e8081d0307921800115440e1900800d0905910300b4040340001040036845001e4200c0c1c4001e041001040e09030381c480029804c00c0700c058034003800c031001d108618103050290010f1014244000c01100f4141c0c0c1001e0009082d0000c5140501804907519441d82d0003048141107041c0c2007a0701107069a501d00f4200c02404142c01544035800d812802211408400020f80307000c415040b50070031078142883d401b00c905080f010429543c021042d000000826000c0c41250420903 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 201477598 1250 201476348 201476381
    0xa0e150703022b09020f061c112709070c0506180a14010b031002040312030908090a0e0411011e180e01032906060d02070804050301061805010e0c1c0906 67
    0x103013280104181c0c4007401600c1c50081004008500c00c20030080c01150242002e03090008851100b00b10003e000c4c00380c040e0410340c8074802c2c050340090384200d120b09501c20504449140310ba68641e072040b074480c094214000e05583c4607401086904001c1403080c01840918400c40c0d9903150207407121581010728018042c3e5907555a0016840b5040c03d020034105da40503601d040d45068a155500d00c850b144540128042640d9030006a04000c04007003210004000100350007030190322101303002c65042040d40c08850801e2404150300e465400f5503060314481d14404001d01c4011114141540c25101c1c50501d00c0041d64151000b01e000071090310098042c500030748074001d09180e2541c1c5028a210440c050000101c0400204a015558a012504850348802d0090303207130303020b0345000c43d000d0155070403669041d42401400720341c0e5400c80a03410051034009105120076683c4845034010213109441a01c8142001c02c200c0074144240f043e100c401c0341015000107411071681d101d0208466010a8011285 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 201478848 1250 201477598 201477611
    0xd080115050405010c031107050909070f09092303040902070c06031d060c0a0e0d060b0306070f020d0c02220209030708190b1e09060a0e150703022b 65
    0x404942880340e0045a81c201540790a00344400038186204480b0300500b0007140e8039619404070001d03c800c0f0001d00d40a4003a80a5050241c069a2190403500610102d00185440082c5d104214011805031542103503200b40c5d030000c000da1000c0d040d01c0d550203000003403008000c00903c4640303a00c0184209800b800d04c01c41d440307003040801000d54a40b00d13030910796074022004480744d211012138015042540ac016156035030b400010207032002d040031400c0e690310501801c4410244070180e080284440002c409554181d0358089060340e07a103800c54113801c0140e11083c281c9a03114050140011010300040c00d041c210401a01d00b9107851280c2403034030303c4190700881c86a04c6410308005c60809000c00d2400b40680000d0300d82b43c041c0c2d031034225030080c00304107201d00403c2c00301440c4140300740310300d5180322490080d28090303170040d943d00030580f40711554601c0d011084500c1480860200030355410791101d000c0f44d0b2130f40d030300c210041e40055070400d8102d00c030401c0074486120f0a031846001c0c107c5248010443c03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 201480098 1250 201478848 201478859
    0x3170f0f030f0406060e060a180e030c0726060601050a17070f091502150601030b0907020307020f0603040302030a120b100206041a3304020403061b0516140f0d0801 72
    0x3510203e60200b44065402000c2c490b10b9901c1c40c0100342035443c8500b0489c9082400707580c05020b031100d142368103d640030009107480c0807c0c0c00b190312001e480700211600030002981803201c0d48805d4007603a1000c50b41001021600070b600c614000c4c023114015103881041c04c2c054103901d8040c80c40c191a100045030030000b60340813651700a00b4a200812811080c00d1160300f140747e0180d190303003d0f8400c3d103116400070b000007400340c0e0180c0c0c4500c1031068041c00304c191078503020b98040d42e83e510100f0164400d04400400c0215442c040c0e085030703c55a41680518200005d101c020341d00306200764000c148140d11007049020340e40b100e900e41544108264000d10303281c24207080000d05030b070404019a2000899404001c1c9004a417a52002d44004504800500765003400071025030f10030b114041b503889400080c2c000248411604640c6944500c030140400c0048040c1c015035140c402c101040a03084a030038906800700f17200c568241e000d4500300066a459040c00c0c2100c5007460b6401100c0c03c081100803006104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 201481348 1250 201480098 201480101
    0x40e0f07030501080f10091b1d01080d0e0910080d02010207140312070c03020f07061d03010c020c0105070609060e0d090609030b010e09031306020c010e0a03170f0f030f0406 76
    0x600f0080085c101601c1e00f8404141c40312105000414110b86480c0d1020070401c01c200700c00d0790320f425810400041a19221107402851189100e0815502d070f2200104504a0204922100603129150003103804c0c2e00d41c042c480c0b510f40060071160b000f071a5010000e110481032021001c031000c2a8001682e41180e03162900301c0b00c2d6002c5000d01c0780c0e80140104140e01e02c0700e040060b04429903040005d20341d040c1389008c03071501c640032009100a015260303001502035000f010451044030a140706901403900301040c5400c90301d05d50126001a40082004641da50181000704402e0b4010031010031a560709848071001d6a0940341440c1c0c640e03020810400007142d0004401014110764902508040e195484d0040f601c1d0042c05880f07a00105080031503113405040040719021001440b0321341d4400c0e0366020103900d820203003158a0214011101d43d00c0c40e03142190040e41079070b40c0101c4040400f0548400603400303030400c21000000c02000c00800d054940c00d14080c0d84a8400d0038480955450149030120 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 201482598 1250 201481348 201481351
    0x90b01090c03110405010309140d26250e060c0c0a23090709030b100302090c040e1621050a110c030a180506040603090507051009060302090402040e0f070305 69
    0x41014a41180048100340f900304403400c40344c0919002c01e100c5c0792400d04000090318407418001c1440f41c0313a00d91020541105943e003401d008141240c020f42040302c0704800102e800c88154442d803402c103c080c00845409440100c4071413442c074003155101c90300c00c04203501b82c3c000c00c980c08041c0e1200510180794903000340842c000d0046507202580d0300016440324002c01009880b5603110f858448000780c1d0191140240c50001e5402c280d860b802410032541d10415020203001c1039004031a69070010f00200d00003403c480840e0300c0390450164954440b40b10254480ca0048500c0810041190080f02e008052500d403900c014908000150390611102220403507542e101a414807150501241102c683e000c000e5401003210340c1400d008189801440d200304c02c00c0c0f50015039000c800814017280d0340d41e042d80803c6003e031090044440460700d50040026400d540010030740010015681400300520030340150400c07110103003000d03090946400101044903000c548508500002004100320030345c1c90701a85 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 201483848 1250 201482598 201482621
    0x11030c0f0d0e01050d05060d020607030c170c19080d110301170c0f09190507020f10050103050a23060a020d2004050d0314070c24050304030305130204090b0109 70
    0x4400802c400001820710b005880c403020300f05940307070300085803912107001880310984c3c0102820340d56111880c010309514186038064603003100010f02050135100a808550f808203100d00100101d460004286d001001d8107481203840000a2200450785a690300540c038003c800c24401c039032030b076040c0f00c0e003c3c412801418000c892544000c1c0c155000342c0760041600182002500d914a05903607444981044100e05030001e10401e103000700300840b4641c08602c40c503003548060f0503281c11541c00c00c0b0b45425604c0a00000c1c04076044011260000f80b01d00030002046951030703103201304481c239901c10300f4141030301181c202c0c0c00d00742c0000d4016a00a070b28071540000304081c1004e09919000031006d900140514003d141c000c852088049046c07501603003076141e0800141c5117060740c56440d80f03003480e00500148200d1000400c480800302503181e000651205800d5160303145415551683c0f000c5002e00405404554880070314100314002d03840d580500d1886a02039248803409501d0000342104481c9407601c1c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 201485098 1250 201483848 201483857
    0xa15052403131e080d0e0f0615010905061206010e130e0705131e0e010b0607140d08070512180d080114030106060e091b0c01060f0501030e061611030c0f0d 68
    0x140f0b00141903041030b0344100a107403800055020800081c58942010303003099004a2144c0001c002c4008442116151003403400c0c2d0f90401c00c0703584e9506000460283d80802c019009243c0009052544a1115803071480070042001c001c40c2c80c0004014115088100701344030ba50403a0100344520301b402c00302520303070f041c4a0000f0046030800c400084448000c2140011006031070b0010b00031102801d4001c003c004500501243d41c440442c949006c401c13204460f0340c046070003104100111640903800061191043d92111454500000c464254124000f0308603070419054004060700d4a01c06c0005902d02d11494446122950501c603000c258031501d03c92061190303040050500c8010751203d210307429190182e03050000d903114046851022406007070180c0b1085004242101c031100150031100c00c50f2084049080c8103034442c0011400c0e15141002061254070110104485082c0710162002500071b13850443c00d00c6500e8071609003154090840802c1581c0001201041020180041c51052803c2d060 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 201486348 1250 201485098 201485153
    0xe0112020f061809060310020c100c050a120f1416031b02070909050309090c0406110604020a05060a02070e100602011109010c1b051c05060a1505240313 67
    0x226083d0284038041d25020700e40d52004118103807400c01020518400d404025521010a4913480c4d5031001440842c028190500c415801c0180c0900b00701c0d4140d81860381c90400708080c8100c9038020740307104244040304955990343d4184420f01c9102d16400380002c03000109488050607001403c1d02e0a1f12040b1000001804940d2000e94000402000b12102540041070010746428141d00314007400d1296500b00500d1010413000d018004000c04c01e892058594040f40720158490b40c2d43d40d00b04841c004d400c013504000900c0306280200c054505240c036481200c4060703858503501c840410058030300341c02046081c07605020160b02030107019100a161851203040540c1c090000303055080000b0701605038241c14035028030000140203010302902c00500031048800c0700ca4014866804400800d4520b4001c10020660881c2d1a0040a2a01c100604803040c00c0d418078081000d0306401000d5020b1074203400e90710160341680d60014510404a00703036a846805402d05181000543c4485007100d200c0303d050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 201487598 1250 201486348 201486367
    0x150b010806031c0e0409060501030b010e010e0108030d0b0f0a090f0b0103052401110f100606080717060102010f060e0901110f04150e030a060608100e030405090a060e0112020f06 78
    0x240c541d42c2c0c02e00c2e890142c01c42c03442400414000d160811001d000f22341404004400d004400b49818122030b0850040035680c1c0c1e80300307040c0003424000e0003005029001008852000300964000e0b81c1c8480008004c07a008084c014006a5480320603407000b6021501c0c2c00148172103030250300c41c54074120b60a090500540c500360304040110000c1610f61040a00881d19030394070f41c0d02c200380c59220340c213a42d400c07500d0b180c0c041c13283d540d070702d601c0e0b080320300381e69804c0c83c1010400601c2100120300811b625100c001c000f400980c46488180c4009002c54110340d45c03403000030030032001402104000c1c1a20000310300b07142004444182903800d0411405113016040211408011200c42210206c80300c050740d0301c50213054402e04942c00147c0c00506035051154520b060288140c0e1360154007140c0c3c402e000c548500907110342d8001034547d251040101600180001c000c1130400c142041d50064008100290094071603412850204083c0c1249a42d644d03800840b408505000d400000d400b041201e4080c02c004841 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 201488848 1250 201487598 201487633
    0xe0111090108040b1506030109020c100b0607022e0309060b060702090f072105060a150c08032502160506040b030c0a020a0204052409090303070507080403150b01080603 74
    0x1c3c2000302050504400245102c21111625694210040c070040d90f82d69654102c002940200790700720154060200051000f4045100c5d4040c1060003070003450600c2e20341c3c0c003000140d02c0001031030100c6030624090f08000e102c030bc007003d0000341410385001840c2052400c4c0384044601c0603030580c3c0035080c100200e1001d0707644e0724031240d07010307409024a44150b51b40501c1102c0c00981900240c601c01d12500c61026084840e41125108400544c0c643c1c0b400750f590b4482401107074034914403001151214039180c000c01c030482c00941e800a1400440c2c0b003080210b611035010b42c154140b081300141c00005100000710700d098400742c02000104d038551f00380b604081031201c0720720020700130f00034406000401c1501ea030b00900030181c0c080d030010000c210a1404441205510101c030105565003148051440000d01d00141c2641c06000c0fa0401035007540c0e40c0f510159581c0d4049501a03075440024000003000031a10340902080310810580464500084000540032070005002e45109400c0b031105814070742180c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 201490098 1250 201488848 201488851
    0x1815050a050d03020a02060a0504031e031e0207030b01290a050d1a09090d120e1005060607050d020d082404050718030c06020f030a020616031407030e0111090108 71
    0x848a074084038500e0f18003a4507214807000000d400c000c01203030910300d950304a00944100da0069118049802d045005403000c1101c201c401008030340f030100b034070149046500b2020a1a00c5900403220195100d0f101c1140150b0309078131114510044499080c160945034044940010003400107074109881d102c400381460003110045c5a10301d9030760392082602071146000e61b42c1400c02034124100c40c00c1036408a40c42d01c0f4650100004182c0c140c0c01400e10740391910840604a12643c041d080020107100d04001a20b0060841a4405014014000424018011294500c0090300180b00f07640000501500c80b1400810300c48045c2000e80c40e1488511700d4032078205070030200301c6001a0f0b90f918a50141c440311010304001c442e1000a10010040085d0180c440c000d40701700e40c0840780d15003004000660340b40b14021954005170040d1000c504804001c2c0e0900c10191003d04001c502c0340f408038142072248608031011000070391680e03424100a9428495240303002c4810040038600806200041c000400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 201491348 1250 201490098 201490109
    0x303020703081c091a1b09040c0c140a030f110a060f020c0a0803040c0902190c02040f0905060f100b2209090305030a1b080a050415061815050a 63
    0x30000c0c0188020001400a95288412882c00c000e004058200200080341c01c12581700a40e68000c003068090420251400e100b40412001d1850b020904c002d10000d0403460071440701780b00c80b904107000085c269003590f80101d404400104142111030400920350f103624a40001844221031481a612002156000d1035641140001c68642c1c065042d400007889801144801e41c00b549170f040381008880c000850086000d401e580308481d869100c080700328810720401403100e112800f802d104080c0501459000d26000400c0011065115002d28080d201c0c080c004507100e030400f40c10010020192142e40b80c00c010600602c0c8560750824800003a0340c40381c900012003420f076100d1011f00c0300d81401802c0c009002d83c0c40c400c0c010000c540c500a800350300251800b103075041c14018a4a5038220359588505250131a50312019103413503a14001005050160054951203480c0c600c2d06211025402044000c140f102e14040010054481c002d04032030108845400e030552811040147c0d5440c0d02d04881070700c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 201492598 1250 201491348 201491363
    0x8180906090f1005030d0c0b0901020c0703031b0c0306020301051c0203070521070305010203062b030e0409050d210603020f06030c0415020c0f04020307140c03070f06020c0d090303020703 82
    0x112143c2074449122240e070b100e2a450721880c4000c03205964804080c00340c035446844074000d5510780ea1140c03800c1c4c1c058600c059903143e00082003000864803450240d22020140c0f1040c80c00c41449440381d003905003007a003043d9100b43d0000010407446c00c0c801e1620004000000e101c1e907652003140e0000341c542480303108880c450b06408126030784100001e840222103099510858a005940e807034081c1c040e40044662074498403c07a1a44080b510140f500071006d1401d0302003404139850142d038280c8900703202168039a00141c0e500044000500c040200c5156a125921986080700e250000e480020b081460003420003802d040c02000107880380c02d054220540c007240e4980e00c96491040c41d5910340510b9005800703d9500901902c4042d8000c80d20b241c85101c2135510041c40d003404000c0c8400d81c40300b51290400644c2e20303035587c031410503000060001d8011441c2624903045003a2100348801003c9003095880315400181e08a40e410b0402c09462005168204080c0441c5151406502d0f280d55100107030004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 201493848 1250 201492598 201492601
    0x40b06010509060c0609120a0807030f0209120619090203030f092d1005040e130201090b0d1a1503010603050c190f031512031b08030408180906090f 65
    0x1a0300980030b4441e411405080c1548038080150901c0e503403181543c108049001d81c040369940800032508a603803880c015211200035032265a0103c00a00800ba0045202d40e42403111010b15521005900a07105d00c9000400041c20040034030f1130b0703103040c0b20301056000e03140401020050302e020050341c5054102c2c23050b090315030900902295100103030a00d021049071203442c2041d41214002d0700661895010340b178a44109016100559183c415805061001d165a9000442c0c08000701c0182245074810300d03100e0301140c2d6030982407100360054241940d00380d0f15a10920261907403c800c0f032310310203012505040304003a0400c16410b0341c803041c0070b954105500e030800965070001c0c2004403907a04444c229881916604140e00030090040c0001d0b6600190070048000e4030709152842d40001e0ba002c10800381e01d1040c0b43c0e60251030300e42e00d117001b0b550074522920005001c0382076080a50b1080c0c2c050402103030b03a180a2000030700c03c2984002c019128107943c200780040bc0e218055a1580310101c1d40170f9514a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 201495098 1250 201493848 201493861
    0x216060c06050c12010305030309010b0d0201080a090c0308030a02180a050622080307060b01270b0702030a05010e06270c090619090b1002190803100e0717010501030203040308040b 79
    0x1188941c4c10300c18a40b40d24007000108000e0004005c51189904000130003601c007002c3c080080601511902900080c1908045118032a4650001c0095803140c13010000d85a500e9841040b207800896840d03884681c0400d00e05840718a1007559842854100c65410340141003c0004c0e035280115103d0054003400860008107840000e803405001d0000078003285d4491066140c100042c0140d110468005080045508003c440340400c841d4000c082e042c00c40c8149081036a1386615400051003a6030601c545080326020640038481c0480c0406508090501031070b18a101420403d286813114030140000d114800c2d1f50180841d150380d40707003070441d031180c0d0319140c0e41c00003400301d10807101202050040e40d00000e1260305c940e21000c41060251103c0101c4070440364140c0c3c40d140c2495000f0b841d0011a010760001a0801009551040a41c00401c1c0007a8580043c08031103a4211100c8011030015040c8842c030703000130035202c0d00400b000d07c1d00b9403a41ca42030750001c00f1858043d05c01444142c292020424 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 201496348 1250 201495098 201495121
    0x20f03030a0506240a030f050603120a260f010501050712030b060f18040e0703050a02060304020402190c0317071d030f010207060f050a020906190905120d0216060c0605 74
    0x2039013604d0014022070f00c080c0441060b03255101c90800b0010914080044250304e080d0300450307100d00c0008024100000c80d45040150030f034801e601103420003c1000445405901520304d022424558005801ea00c1c500b0078040b14544006801c00c1d0706200090003540c0c001070080d03803603c1d5001030914020803070b00d0784000811154002d020b180c0c05021000700380000c44120514103640074460440e424001c43c3c038407440268803000c0030302002c0d1007034205024100141c103101c401160050b1000d4001407411800c0f952450b40c4034003001005000980010604e014158400c52000c901801c44400440f0b90070405000391803041c4008030001c01610303059090120390390a106000850810000039941c4500d0342c0b800030000e0010385802d410042c03038040402d401082620980c0e50420024103168503105003410002c2050022007d800704000c1c0b044404a255200c01c04100c2154a0800061090030394014019090103071144e48081d0382c242d50380301013200543c41880c81d0b4584d50044400076032070b211b41d0800318 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 201497598 1250 201496348 201496369
    0x304031101020c150c0616090308030c090301020f0403030f0f0e01180806180106090902030316140114070807081006122714030403020607060e1903030e0c01020f03030a0506 76
    0x95024008000e60258000c2c1320005142c084010b0050ba140703030b5101c00f0581c40c0c0316518600f000015031001003c0c0009045000107542040c94a1181410910250000703400d80c0d02c81000200c192101140c20010036070401d40140f1075200c58103000240000070f02008003560320040d0003130b04001c4420804010444800b0f8080301500501041d910030380341006150345010003660020005629184000581c40028405c0b0208168000c015614121038900c490781c008024990030781340c0504126140780c00c904244960f5000400900d04d0644c940b800c408040c0805c0350061040050043c203004001c0360b40c00c1c41e1003810a840301410070702200c0e14a043ca200080142e01c403140403c8a40c41d103001c044040b00d404416041d0300c908001440b080501c4d03071143d00c07805a0700c0003c0d0000c6061088000160b10350b0040e40701100420212008101450f21203401c0c1402e0341016000300341d0fa0fa9000000b01030078010740315081000c0c001010610f0b07400c01d8469485c880104071160701c030350300d07404a034441c0c0c0c0d81c84010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 201498848 1250 201497598 201497623
    0x301031518022d120601090b1c0b06131815021e07050607090b0415050d0f05182a0f06030403090e10060f08190207050c0918030403110102 61
    0x416405030445140c0030780700c80c120a0100700070303125000200c1600d44079091302203000c14080544803603441d1241c0c51000e890074202107070740072a44c2d0f111204e0040c00040060100f50240340d22101c213040c50828400c0f1500800c00e00607241e810320020a0b40b080034054441c051540c400c138140355480301d40424100a00801011000c285150000d510308400c0f2030001d4080306004038251030082d00e44c02c0e000c1d500666940b042202090b010f0000300b044104108140e94190090704000e8504400650150308403940c84d126568243d0303682080c030000f900a074684080221888000b0152517401400060040f504440c003852030003203500c000032603a110b1000c00c40c0300f0003000e801252207003064900a0081c101900070010b200000c80009190680384465032002c07103280d5162070f100c41e5540c9200700d030405001071130791300150784400f01c0c20100c408501c0103040081c010000b400d5810405400c1210b841c00280c0805080400803103614030000011040314105c941c400078100c3d00b2164000180d09000242420 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 201500098 1250 201498848 201498859
    0x203060f2503060e13020306010b0c070f1206320421020604060c02010903050403030c050f070603060503010e06070e060a11031204061506140a050c0106060c17030103151802 76
    0x141e00000d405810880540f503c843c103152895840c0104541c0006141c800a0350540c0000c004122022041c0300a050603031214043d00c442c6038803a800c5d504461000c0d0b0080c1e5a0341008503d04c4240505445a10036207a0a95000400600c01054021080f009100c284047d0b6041c2c001007810041082000c1e00f0414003105c450b80f0700c03280b40d54081d44641c8101c8050316071134100204440007074418418178071a1513054480705e00301403d68030112110f40d05c40c00708841030b00c14852510020103041141d08010030b41c136a40400c015040c0824142980c0408900002d268000800d204031143c2080c0c103800301d500250380e242d4681b4404101200c000200049083e04c9000000d040a400041e2103c203c1c4114050442030100d032100e001c89003106012481044001100402e480c441d103420140280014102454824103111001603054215022644540003040c03490001c0400c10009100e600e0038010400c601500715855511348410070441700041401c03c9aa40307260540c2d07200d0a012101809801426 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 201501348 1250 201500098 201500161
    0x120a0c0c0e010f09020a0507150b03060405030c12040513111c151d0a20030c030106090e0c090d0c0e0a060e010503011107022709030a14070203060f 65
    0x241c040031080030300466002c0da01403140804e8a4200e4001c507860440f0642d955843e15159803103e94046410340c0041480544402d000c66142e41c3c1001020302031401480510307134a00c10304070400c0c41c0c00c0a484813000c3d14a0203010400050b41e070101c0c0a1180d10030b6000c04a0400182100924144650250b80c6450440c00709030b40104000c030b80c8800000c2e12100004d0450315140c040c118081e810003072281046c1e400300c40008101411360f0300f000180c004140309001501d0100070120110390812603c045054601000402c4810b5025441100900d0500074902c51403c2030200c1041e54401c0f001e01ca802411700410752800c0201c085140300060204949100e540e0a185507014007902262107600c4011511500100d6545010310860760f000e10a0900b50f07140502c0d560a00074240040902541410710b066480302c14509000d0b6540c2c8110303080c10103103984410040029090468803100e2051410080c0000801038030001703255138000fa013140180605582c3c800711a400d06000c07a42503d4120510407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 201502598 1250 201501348 201501359
    0x21e031309050105100c050f0102040608060901050d08030103080a02100609020a020d1d0f15071515031203021318090b0a091707050c0306040c03020f090702120a0c0c 73
    0x409854480216000e08490359a102100c1096840038094503911180907801c000359207000e00c05840446208a05445400c2407107858a401ca81050340507101040541003000030030300d0402e4020b405000d04446041102d9240c2d1100b8410380014040206a00030015490040a000300300524803080c4440d003e02c071164503106d5010280d00100030450251140381c41d0822824000c800703142646072005d5018118219071020803144c101421840b40d0072907007141e00c0500301d0707402c40001c1804078021824212012030b800000c5007200c1c010750855031a903010003814030025101c0080000c100c20305240c00341c2c807607a50240003a10808654007928140c3c3c41a000c20407400c0140c1c120002e080d010f044522001c2da00d4140340c200791003808900424004404105408020201e0040e101c4640540125192010300001192402100380d0b001d03582622480d00130000c41ca00308d5100110340c80143c90180050a0034940a9034901e91545110201000421115070b2540709005000d82c80703070409501b024503903951 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 201503848 1250 201502598 201502603
    0x15040f0b07032c1005040306050c19020f0607050d1b12060515340c170f1c05130b03070f090b0403080d020d050f0a0e07050102070510021e 61
    0x1010700728085400c0e40d100914814484440040403c010b0128604a02414007001150041c040c0c1c1101400010b210200100380684079042c400ca04041c11182e1358154002c03047c14800c0181100c808540c08688030460410020500640207003290411035140d41d412110180a405030380702d1582c034071410785e0100e80d040d03a000e0000445040080010400350f500c400c2400300301c46100224102c5100f0401c800c2e43c01380c000d256903402c985c0204020041c24513400700d4201030044c1e0098150380c11840c4020500c0041c409005440025617200d00424a51410150f07198603207404d00d1001d074500b040b280c0c5c02030700c050182040300c040b070020390b601611060b22420740142940042c1d400000141102000c80c2010b8001c83e044800e980e100d50f02107080074610350740c904050780b00741518844681c09100150182d015401103074007903852400030130494a8440402822a80140e8258030954403510040180d070340c000c24000709941066420105850018074240d01c0d0080750442e485821449059001c40d601c0007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 201505098 1250 201503848 201503857
    0x10381c05090615121e01061703120f2503060503030a180509010605180a09090609020f0f0a05010c06090b070c0b0105010c2d0510150806130215040f0b 66
    0x901c0c1d0501244801c01c003c4c020380b00c0204507181040e6001840703403210070003840030445011007124008a065919111b618841c0d1107001c0d0700407015070001c41c542c14200d11054030302d5440710682d803042d4803038030b4030b078298845104d0f450f058001c205581d8049150181d109804c00d101601d40a01166500d07100114001d1032500c1d44401043c009442420100c0e982c60715880c424120350043e5a9a4240354260715a602c1601e00c22003076030b622200c0c042c000521201140500000d0310f009030000202213a250040c4100541110405032040555424054156803a041c021b02a58020310b8012004d9203d03180040040c540c02c1130143c80020610200071045070f008410481031f074400c40109196036a14401551104800b07a401064400c007882a0304041200c40100c0424000d0116112034083c401d0302c03180d003401c00780302808900640320b40b100107120300c0641048004000900c0100341e246080d08600201d0803507440021311400202c8a030900184810b01650f010305103180b801810b05580d95024a02ca501 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 201506348 1250 201505098 201505111
    0xd060b030c040f0b04030b16180306050a051303090b090d06021b0d030c050a0e031c0302030702160e06010c170406030b01030b030109020f09061810381c050906 70
    0x9203d0001300b103048902e03080e101102d601007070242d416240c0040c2d18958088000c0c95008020440c0360041e544541001010021030260700009694101b08181c8070a8810041c41241c0300c6042c000010006580b1640a00464035000b48844d214440100001c83c030aa0b0014003a19160010482c112000d014200703141c8504940011a03001003440001581a106420140e60104000b40005405640240d003401e074405001002c3d107070b4506a48001c03610303034000c042000f40043d03804400c01190940402000d00f070107100603413082205240159840e81d80c10f0080450381004404803540b01000148014109041c49010810740c80e180c0340c4000070300500c08040c405000074100588c02040341010b01c1011240ba401800b211031007041c40c014407111074005415150030128036109150038464242c13605010f544d000e64103082d80c51900c0074049104603498001e01160391442d001200e080d01d10001d50a100e81018000f54842c0f10b0004034054039403101c1030b240391030b43c180410044041c00c042403d41c803032003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 201507598 1250 201506348 201506369
    0x120f021611091308091e030d080a060f050a1401050702030a0b0a1505060a0806011b0501060e090715080603030702060313021206090a1b03060c08010602070605031b0d060b030c04 78
    0x50701c03040c1c3d000c1c0c0005143c40140003031504010141e840d0030490b450030307011540500116814007090340464034000c4411039400010b8108000d20442c60418040d4400410f0004cca0b00c0b101400e142c00110a14502d125419070b10060f4100e80e005a4000d80030f0b560320940040c00c0c0d408141690420750300b00d04080350841d2100d850700041d03008000c00b0b60509000c1e82d01c041d103403030300345255100c1c103a07410040600701a041c0803072821001d030701c60720140424800912610001c91414506642843d44d0403001e0080c03125600200d10a200b211400c5000145400503481c0001940d01c441c4040ba0a512940340f000c1e402074400010841503410815411410520035103204404200310344840d81c0340c5e4030035980140d40340c100000c0100400c00c580403622142c2c1700e03414101107980d900d98030030045a0b20402e6a4021542c918010882c1640601101008169500b48a451849e03c12403892140c408140c08510701103000c103240044031900d9001d840541007080c3c0f80f641e0781c10f0500240e8000d4000c1c4c4910940340 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 201508848 1250 201507598 201507601
    0x506010603110904090303150b0405030606040b01020a0308180111040e07030905030a0f030f050a1b050306030a0f060e070e01080c010c170309151504050601030b01120f02161109 78
    0x74400e1091a041d0022411201d0810700f0410410002c0e10024600390201511021800d034903440340304082c0300620030044000d55507803501050508102008141034030071490642c0003004d0b41d801207400210503505181c015040c1d40d41401e01e010320380c002044480b5642c43c2c510f20403803104108006009507100708951f0040c0703030398420086040d01c1c100d10b0b000b429500103110543e0013134090b8100c42a9040c950401084c80c0340120f1800d01180d90898035000d9441d150b0721035004441a12240d203d0190319403811925501d00070020a036122031011005001c0311014020f603041c8401640070050b03050000e801e032141c0c150340b60b0302951440d900b80034083c0f0f00d00940342c511004d076028445894001d5131040002e118032141e420030480d02e4200904d445041d000d04c08010b41034180003902ca52260796400210a00809440280812030b00001d000c14145880d05100c42e007240e03041800c130f41c0044440359000c10480054021640603029281146c01c40c107403205403040800c09441105292940141d0391003009 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 201510098 1250 201508848 201508859
    0xc070909032d0207060f050c031201031e0b13081908040b0105030313090b030313030501060303030f05040f060b010905030a1103210315030c0a0e4501090506090a050601 74
    0x440440120b10015900001040100f5401400d03030740401c0407207003401e074107114503000482d040d988941212010800c0e040018400c0204946c40c184072080c1000c4c041c6000020f83c2e40e150407075003024101d030064804c6030746507908101c494012248100303c0c60507000c404e40c0e104440a070006e80107803403c844111140002140c40c3c01c0c004143c40100304a03005074810b07249032502a0008080c0c41e03628a42600082080014900341840c2c2d48000750310410000821a00d10304004080300d662104403064503040500784004944004801c41e9480d401c101e00166284000d0016075084140da801903401d4020f44c04010140910701c0100c0394086415416210314580c1000c5515101078500819450781d42d0610110308941c3d192212410420344c0a42281ca00c00003000001d40c05030000c2d0310070760414801c41d0400c440401c4600c0c0040041000e034907500030b8585010f01c0300180149800740d80402c003003d81d035020158002504045c0c9002d401c1001c1d00c03403906143c104142c907030821070b5041d11103110340b4000042 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 201511348 1250 201510098 201510167
    0x160204060510050a0809030904151403030a0e0613090e0a0b2d0c120c04150306080601060c06060e090c03061501120c17160f0e0a05060c07090903 64
    0x10700b07911941d1054a000345804c030036160141d014005441901c13017403103e89056201c0c0c1c8101102e1b095041401321240c1d10b06480103900300d80d45d1810600a40080c00046a8144c1001d00307040c0c281030850303102e501c8403c14051541040865840704420f5030805468012118011404208440c040c0c0c402e034800740d4640b014132020803084034080b03034902030b42e20300050340c080c8445103c0d4004c0c0c0780e240c3c118035211050351080f0b80004140e0381c048039a803001030100010001100c84c0d00050a503030906004c81840d084e540e0f030301d5410510990052140b6082064100401a800310000d01108254a0b080d030070000c52541d5514070f0001403500a01c281c102141d00e0030140c000c0c014000c98140c5d20103c40caa622003144000c1c14504040100340302240031928284e0420000d028846c030240481c1e2710b07240703c16940041c161103504080c4070602846008140c0305441c0c0d110307030304240d850070b442043d600d40310718500749c3c5040030703036408200c8052800108008142e403161b9412924130000c14100300d00f40600a5450 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 201512598 1250 201511348 201511369
    0x2003071e050609060708130f0e0906071d04060801020d0b060f0304021003090f140106090b0a05060703210203061f05070209071b0807060609060602030417030f1602040605 75
    0x40e844500310381040a0300d4400010300300c40d070000d05541e0500855680700ea100d5042040c0c110303481c0075907103410300180b290321141c4002080c031485071501a050040324a82c844102074003900401800d2503510012900c100d9043c40c00c0140504108605590b071580d2900030f4211080701e940c2035050002210040c60309209442d0b1002d1f06c01d001c01d145840780c1d0300300501c9030010351400702410340b9040540d020075403c2054006e868050800850888040e9000d5800c42d411a0404509c071850003a50801d55102c3d584950180c640503100280e541c0e1080c103090740c0002419050420701c41c081504a000c9c601250051401005e040d01c40c58104400d9201000c42c25681000744d400143c0705014000140c43c1022119401410720f04007906402c8246000c01000180c6180035541640b00180e100104002c610909000f08a604020042c03d0708007500203403644128070500074002c450141c01e404149042c000c6600c0183c022a10903520301c09005c040140c094000710581c4194900354000034582081d02064 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 201513848 1250 201512598 201512639
    0x110a0603050108060916060f17070f110f1b03160b04030c0e15060d090206030a020903060901090f03080408040807090f0f0603230304030f0506061905210a200307 71
    0x503480746040901c100d235602030008100081019081881c0822150420094051500e641e1111200c42030801c1c00390102c01c1401450320b040e4866101103404d200086000c1e105108289540094110700c040001e1070502c807901c210044a6014000040389043c01005004580c0300b1300c0440f02990b0b50310400b1101485c00c031144030641108a60200d0103103001e40c014000001e00c1c0c1c1c00040e00715450307004190603400c2103034112451a400110f128440c80c040212545c810300100c024809150940d0301c2d102c2c41002c4402c0101031188107030200c0c080000381c800f0340740640008811103840994411aa4010f05440144401000d24200350070f80212420f00a00c1c00307803608002d010960400c60b034680c40440412080a528600090101200050701c003100807580b103014000a100c242450f80411030340c000c00003011b0304004c410760f00421850703d8024040d2030300c207281c2a40410300e10407100740e40d0424605001c01807040307c51899a009070000b00304484201d060035002c0352405512031035003010030803560540c1c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 201515098 1250 201513848 201513883
    0xa06020106030512032512050924190203091e06060103060b03090a03052b050411060301060c0303090f08031006030b010c050c040b0102030906040306020d2a0c110a06030501080609 79
    0x4c42d46405440006031b040c07041843c113505e42c96014406d007412104192030311805500400c1d662101c2c090380310300d141e4003881e80c40b1092440e400d111112000b00300c0e0300329580004540202c00034001311401d01401d0682a032040c081e80c1016001d285040d1038000440e11313580070034940b16002c21081902025248103020741d4000307002c84811603c06031256003182c0820340032104d075194003040c0799066403003004031704040080105403805c192501c080e02c010034058003801200d0501c01046041c0d806403900091030781605000030b0440c0f080c18007100c4242c060700094284040042400086400540c0b0f16084450b10713a0b041010102407001103076519120380c0c0c00b0b0555032205e41c000782170789043d070300c45103a14005004492401c15450040f52041e04a94810386286d03a000c20103030b40c1e222060044071444008841029005090450000e0b00b03400d210b2141810131081c01b024000308030301c03807003039200d88140240324004050340c80e01c008000c0c0009000e010014096140450f800400014013a40e044e05500703071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 201516348 1250 201515098 201515131
    0x406030c0e030d0c230a060b010318030318080c1f050108030406120b0307120c06030c050712020c04020319153006060e09060f1911090a0602010603051203 68
    0x4045400c602e40290030b94111040507a1700000c036208210403813440c60084044c01d6004c4060a01d1822940c19848031814503007880c29000030082c24108000201c1c1c0d041c1400500d0502041040c64042d84013800240b84000029104c030302e84000040e001c13801c1043c461006881c52a011290302540c0c028440c058035a4030900c024805d4071b000f15505000e81e01c40410009000740c01c3c2d80000d1501600740d20a604160099001d6401e0001080d10000031300028101030101c8040d400004019100300000980005181c004041c07069100f030103c03a00303000004005544134100940e0040b1015951079118021501d40700d014000d83e03480052201c116101c20484c20003480c40007803140c0c04107c0144c80c1020841041c1c50400c0001c10511501d4068202083e40303c0c86071030400b00342440c10001800380f448190811080007041440c000706a600b4800d203403c0032504029801007001c841c0640c82034103a001d09540004105c1c11350540c0420203c81c040c3c0d048641c20310840800c01c090344000c0c0e4007210124022003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 201517598 1250 201516348 201516373
    0x41506080109230718060f0504050d021309060b181605090a0b160605180705060f1c0903080f07050703080402060d0c031b0f05041e0e0108030406030c0e03 68
    0x140082c0b5070100c1400348190f0380d68480040141044101c8103140072502c400240340454161405c0c1901800b60b0341002c0c40c1c44803080c0005001c0780100d100c1c0a11031016020302c40c045498400d807400c520010b140301402844440c0c6403032405070024690b202c0c0104d00c2c0301c1e084000003102d05100ca008108140010107111400a0116a25440b6a4815410490341180041c2845020000b00510b107140c29501ca5074050343c1c580441a1900500041030044e102d1546004804000c03d42404030340007203074506d944100070350a64050703000303c2107202e1005160100700c0c012001d01d1f4010304029481785e6542100c5a66601c003000c0c00a00c10f507092000030701c1c140f0510000902500ca1150002d000400d03031800c000707601c15503000f900d41c00b10307006000940310307007608a1401c100d50341d1074114480340c18410010100c6250003800c50080d482942540612214038a02c0400746601410180c1000015000030b0742e11068465500d600c02d01c64180020320f0070f5a01e640030361190f080c0c9201458001d02500d80200c1c4c80 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 201518848 1250 201517598 201517601
    0xf22080f03040204060b0403110a050114120702070b161106070b0f041e0f0209010f0b1c15061106060607021c03030b03030d060305070b0f0f07031b03030b041506080109 74
    0x740204d030031603a50340001c2440745030f180180c0003c41c0700e02a13044820001c94140704030921030b0b5000906001540c92201220310910090b5004c0c4260301c41c1c441542c1d51100000c0b1300d0980160300081440000003440314900300300140c03c1a074140100403014400d01050107202c034500c51080045d281817030010204003003803012541290424001c02c0c0880c4d058038412182c50007406602c1048909031008041c680444c00d1900803c2e004007118140c2888103450003130300e0301a41c0314074080d990444c0e820120f0300300d10f501e05500035502902c1c181c456181807a21420094070b662940d089042480c861180010701c1032500c08100d48030300303a014142140905c440070403d8511003c4039000c03014551900c81c120003545040000d0410b00d10b140e4004119680b55051481c02c09509070081da860f140100040e640007145842128404a03c444089548606e1401e0840e0886a40e5071002c2c41c5150201c901414158560006d482d080001c50381000588041440c070010400c1911030030010230300481c01005500707081d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 201520098 1250 201518848 201518851
    0xa08031204080f0c070905090105070e031002070f080c0322140f0105120c090117040803070810030b0108071a07020a06051e030906010e0906070c0b0403090902030f22080f03 76
    0x7103040160070602c5a80790203091003015082031181544c7c810401040d05803d00810360425154246400b0104594000c2a158000c1089040040390000f030200108182c1110b1103d403150440c414030b48031071410744003d8480d442452501d014600b405542c4082d6888554400b04030341d02904040320040a600900c00294041e11685040c00001d20002034140001e17440988240115160543c0c1e52401c40005010006c4541441448022034010030000a00141c00c403030b006035039410503210564600300c80c003c40f0395407500001d0036048201c000044080d400030b40182980c900200c5c0912403107110100044a0041040180d401812031400308907990141d8000e0064016008940c4005425000d2000ca02c1d07006440c4c10319642c0c014001001010300f0b94000e95085400c280c0681000c0c1018a002040d0b45031000e40032b0682402d2001107810140290418030080c940101c1c00d5440340f070018200701c956082251030900c4d01c40c040790b0120f80050066a00f0059039070040c451030a1000384000200705800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 201521348 1250 201520098 201520117
    0x60402010323040c06110706170a0e0a15050124080c13140307090603020a14010201020d09051b0a0815130813031b14130b15090a0803120408 62
    0x54030840411140401c00c11070784994041c603030842c251882c2a000034410300c0c0c07540501c02147c1107801c0c240091513014204040d440c020984140481d00d07145c21a100030b00d0001940c920700c3c03050002040412220040c000d41e040017200b4200542da9965041d15844000400384595009810410800c054017610300c1d03540040c5800d280c5130504501b9140072843d000705401c00c1031114800010410345160411084024044c40c40042c0111441e65001c26450200c0b03010301d104c3d6002d86465070000b6413007503041d294140c803009803c2c051032403241017032900d80300c01100718914407241a10041c011b0a044425104413a0b43e000107003040d12020400484c02c54000e03040781034900c1100d40a00124100102a000603e28880e076030310003d01d58075000c0700348503405c406642e402d0800e000400c284180030310019082c2e64241c40b4030358240303400c6a54030010440c4c51125039000380f0b450b0185600350411000703032082807026920048038036121819180c1e03e00500c001103210459020002d0000340e26540a4940c601 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 201522598 1250 201521348 201521381
    0x6020607171b0307030e010b0f030718390c21020a1b050a14010e151216031812051b0d02010507030b04050609070e0609030109050309030106050306090604020103 71
    0x60320022012403c1d4410f030340c80e00001340c0b100f2461040000c00e21481e62000c07000c03030b0054241100540403d0b200d41c51803050910802262102c5003690340140c105560400c150350303040002d41c84100c4500094421030003104070401040c803814250354040c40c0f55500807604412740043d15110112000c4401c0c0c0c0c03050502c001c42c082c000301040064916120b145c001d0030b6004c0c0d200c2e40141000144034504415030f1200701e402c03518034040002e51340c1008100b804401306680301750000440401c281068441c070580b640078110f94008000700c2d0004c8412540011800f90307000e100760000a070441400c54084036000e00090b0307507610b003080701d64024401844503002c6010f8102241180d03a031003d003004021224500540d449208012030960b244c440d803400c1e170104807001c000d1810308000cc6050030400030701e08800c0c005203d00010b4156950700c103a5007000030041c000e0120040e00d107801501d075000302c01000d01139802c080b000714441ca00424118810111078004080980d0b607500110042e049514060b100341 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 201523848 1250 201522598 201522631
    0x23060a030b060121020c010b150d050705070f050706080c250f1209080c0a0303020309010e01020304080a030c0b06030d080c07030905090108161a07030e040609050708100602060717 79
    0x20b07111448011800a0741c0940140c840303000c8001203094030a4901c8043c803a278150b0012580081c0c01c034040e16050780d1034201c0010030b035403076900c10740701841141c00c060311340d801140016081000c0082c051082d0356584e0b44511403616007070f0005000c0e00030f0f03850b000c841e03100d0046161101824401151801401400302101c80301154407421411001500c17080c0020300080010b101ea507400f00310340714449500b07403141409689147c40003922801f509882d23038104204c0e400c2c0040c40d603200f001650081c21000c82902c141d14254034008d0070050001608031303020b45510700014402d24000c10070000e41d0a064448010b42e994200d0301031002d0340301140c11018005401740105a94860300c0c40e160280401000500200009002808840141e90301100b40c5078982d2640c00c840c0c003401d20940d0102075250600c0c1501640c40e00000300a44070640004085620780b6080180c441e621400c858080c0c0d46141040d0403c85d250841280c5a0303004403038020114200c48080d204580da00e00707505a00034086d08016428 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 201525098 1250 201523848 201523877
    0xf09020d0503041703071a070e0a060e010207080c011b06090c0e070e042705010e030a09060908010203010605070f050309040509250f050d1703070323060a030b0601 72
    0x280100801036032182c1c030204050049080d104880c0c2100728054008500f00341540d40c940003050394041c42e140070910310030080355460b4050880c0d542c4008c8000e00319024141c07902c00003000201e51405e11401842a2240051020404245417006d0903044c2d440310102d00441e40e42910080f182d40c0c0c00c0315810344c0c80c50b81c50003181001112201620039a900b040044c109413a004003407603000300c0c44500c1a49810840b842e01c41e0035a11f0595800038410b01e801401d8031a041050040c55155100e0125000009112501940c007601c2c18054803000d480d4048102e44030030140d4200c2c0000d00401011900800c03601010640790880d440610344903208a0f46400c000202040a560040d50309045c0b41c1d00214415104002c0c403002804080e200865410b0704a141c8010000b22885a02c07920340100642e54415080c443e01098030000d5030811190b556072420a404000c00030041c09925a020100b12100b41c013299010080d41406440c00620b400016810343d113840d0311051f00075108078180100e0f03035081d400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 201526348 1250 201525098 201525109
    0x403050a0b0a05071b110d08041415070302070e04060b0402130906050414010e0c090909030304020a1505031b0d0906020706060801020a0c030e0a0b030f070f0206070e040f0902 77
    0x144984120101903150400500321003e840003e40700009000f581440b64035000d280c102c522503550780080c440e0b0035203002000440c200142902d07000d1b1083c0000140032450340609100030001484c103864840c07010182da03185080c40e0140070030080058100c40002c02c1843c14010301190400e000b5040054200c18550000e001c0b6841030482c1002429000c4081014510510170131000f004183c505000d1403076811400041103105010764080c0d00c1080b0040b80c20003070360342d095030308200d00508228203500f45428555500d8004a030128402c2411145c0415000401c4200030001142c5807100d5003161a481080124040d0000303004859020a00012242402c1030040201060148400580c3c40041e82080001e6901030b030040340482c1c1c010445040c2080d4040d040004280d003601c1e0440c3c8544241002072501c0d481030b4000c40101c80084203010040e01042c43c0c06001e2000c6403500701c400b075690741c1c1c00e0fa12140c04480715004906507901ea8445410070b40c020010403002e20f1400261040030f039000a1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 201527598 1250 201526348 201526363
    0x6031501030312050109061202090a02210417040f05011b0c090603050f0a0305040b13090908121005131e020a051b0c0603010b09300d0c0f06020906040305 68
    0x50004034070380908100b00c0d0f014403400f03001d006600b005102d01d50801c8844803150321400c000a000d03a00240001d880c1e241c05070b06507000c01d0080003699040d410203910055941c1030a9409440308400c031040701d1504182c5004840446120020b00c1c8211031500005651000c00759800296080b69149540c2c00030302c10b0046080a4005080005074032821410000e2402225040100181d403120440001003508042510121410340f840c003607896951072072612a0a0a030380c041c20145040c41c141604001d04c9001408100740000404801ca41d190069144884118400c954008440345c00c1c840039041580c203e1950044c100c0208102d50f805110880c00320b03441003400380005040401c1524804051000c86820103045000509103060040c0008240d40703c10b120b040300e9840d0000d610308141d02e032010321a000390401ca0003101052011700014000c841c040101c844a401865122403109004006103011150010b0408444a000d1303511000254000102e140d07201300c00b400300000040c803c100c601d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 201528848 1250 201527598 201527603
    0x50108010c020d0201151401020f010507030b0111010b0904080d06050d1a090d0813290109051b0906070606240201060e04050307170f0d1407020a03170603150103 71
    0x1d06854501e0000b81003000304044030b011039040890b280160700200410740c00b034801c00d03450b04104200e1500144d2400c0001106040c555081c0002c1191032505030b801906444030a80300c402c41045091001822290a401e5560740803400c0c3d800310707000c80c200001424800c05035100c0020802e440d030001844084400c0d004503004040d440c001e101003030042081a4000d01e10800a0490601e98038018143d1400104540000d001c090b5144003840005d1061a88070300805810107038100001c41110302000d024062445103d08150111b10244141d5041c01001d1000d58042420300010b84100038090344025419142d01d42c031148040703841c166010300076561002611007a24908045036001c1e007910390590012610220290402c408540c002c000c88006503403043e00400c40111036040810180514040194108000f14000c0460b4902e50711071a02090042c004002136915000f08a984403403054005002070409a0281c00ca440312045003600700000400f6202926901c0703070b41e4001413000b617009 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 201530098 1250 201528848 201528851
    0xb010c0f1401020f250203060c07020d080307030f11030106020a0f140102041206050115050405040f1b0f0e030a0201050405130207050105070f0f0c02010212162009072102090d02030105010801 84
    0x5004a005031720002ca1582c540008a4a511420940000e920f07948000c041d032115440001d0700a08555466418021a0754004282e03501ca04200c00001d00511a010342c000a0314605044290f0008800d42641d04039074441e4014000c0d01c81699890800000c840300c111240065904124014802030001d000a441010386020004081c1e00709441a03400c180d2000000381344119025800d980d1120455066840c01d0702c01150072201d10a42d8002402d009600407206441c0115800300d00b640814240c11120590741e92000c1544004109501c9002040000703001c24401c0000f0000c031f051140d02141d210090160041c10316845485071800e566084a90364001401d040418103416017040c510000916980381c4401150800e6001035a6007600c170340c806a044602207880d00614140d50f0710380d0013169000749100d4180002c0c0640c4004d20b1401e9103105d100720044c0d000200514030130005118801c9004000c8006100944204002540083c0c15107400c5262800d4150140e1801d004160080020900 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 201531348 1250 201530098 201530107
    0xa0b0306090f04020a14010c02090f07030e07140f032401090509390a0801020a230406050d0f09050a0506070e0603061203040806010305150a0b010c0f1401020f 70
    0x800070000030040071015003070034040512000da2503400004050f00c4204d000351074208013030303130060396024180000254805030700410400707041c2418518a008840c1500d0070701250307104031141c0392200388a025000d1a0a4500a90341d001c1c07030301c950b000c0940c0b9000f6003680c003809010098120b07450a50203c0e826034000d0003004110424080c418680d019080001400e28074031040c5100c0d04198130492092036030031150004401c14598019003120403c0e000708040d9841e9030350311030a8040e4000e10301c844041291401c0b074076210707003214842960020032445050320302800e054094545401ca005000786d002ea8401070840d042500344030300060580100010015400d10345041c1e45403150003002c3c0c004001251181d10329540b40c2000f501e170400f81c01c1703905150380032501041a2a6015650244802d403040c50000024404046070300030740d045148200652659a205010098400c0081c00c3c41c00164940744070404686603072401100035100b891400308600300b0034012800c3e600030301e01c440444107000a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 201532598 1250 201531348 201531361
    0x403021c03141201240203030406110426010b01080c0301060f05120901021801140d020706020c0313060306050303040e040605070207030c080f010614030d080403030b0d0b01050108060a0b0a0507060204050a0b03 92
    0xc1c1085d840002038003c0f01c8031082001c4025103e0001030310041c441c548070b06d040031402150301c06480c06031981c0c85114034041070101c50115403a0320392030050111f510b0b002c22503086510540c40d09104c1c100c41190030f40395034a09102216400190000138042010a104104968403030703107440f07402000614005038840c00c02e1150142404544100141400030100329100071202000a07240a01c5014000681700e802505100e0301a224400d03090740346010004249410100880440041d1031084d642001680d48900c00c2c15600d102c0c6020304600c969a00002800040c03403500125032010f1184180d406241d6295148180541140c0020109030441412045003040901c179141c02031152640c15841c580181b004030f925010354003445800c200107500002e040c0741c040e070092a540c80003c0c0c91460030398000e003070a4405c03080038050756002079803c0d804a151445c050140409403642d107002d4514000c1c80d08415543c0f07900c60041119215004d010010f4147d0b1601415801804a028480d9585c508113 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 201533848 1250 201532598 201532619
    0x30f0f02030f010b0102190309120308010e0a0212151c08031603020711010806180c09010305180709150f090f0c050705030909130f03020c03010509030403021c03141201 74
    0x1202c407112580c50507440720620703a40050601c0242c544005081d0420b0f040d400c0484030106d20303401c0300d469800d21740179040805900c944043d040303900c01c1c00300e1550303a04d8200c00501a07104a100c8c05030030700300c0840800d02c151040c1004c02035020000b4000305c40788031b00d10840038600800c6001503d29013404801c100f1000c450204a034601d2a09190451a00030b40765540e0020340ca10003039540c104002c201c0090940c0c0c443c03005000500351a1420300c14180303030446804c140c130b5000d103031502e000a090070040351040124598089101040801514500e418070911400520b08405130501c140b551820020b09540e4900050340a49503d11000c203001c0c9518040100b1340b42440d101c041080801c11100001c282e01005540100c0821900d011868851f1038854103050f5500401621206141c0c207003a040540000761074003a4042a4024452a994041515207a0007180303c040d41052003e0a9051036000010151260b00d2090820010007400d004040015820508465110003204401400101d800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 201535098 1250 201533848 201533863
    0x50a06050a0e07060c080c010b09040615050603070e0f01030f020c07092d0f0b04020d0c08010b1303060e0a140f100207170d24180b09060907020106030f0f0203 70
    0x1c1000f01002440c0507401000c0d80307482d40016200c00008140030b0400013003074200c1c00c48050010b110865038101801d0490040001e95041e2012050300c0300f0000b00c900b03066096034030941301c1b500e0349074404c2c0711007080c841c801c0b012028141c10150b417070030301c1e0b18030303403801c0c030291943e440d0100007071081c5420070221030102c501186401100b80c4400c005c800100442d03600c0841100c400712408903000b22680f544c0400b0300803044d04660b1150010402c0b02d07446166030311600345903500e80c1d80c10303003240d90700c180601c042d00c10901d0040a25541d503105101048240c1c011209500d082001c4401c40c250580708c002d103400442c044d00c01a0f8204100f0b01022820410004040b600003250071407400c001075944020712a01500852000300b0301081e01800c0000d558420b400c140b5400480c080400c81111103000461010302401d03022420812001c0c00030301885c4034045d0076010140c031100c0b10703031295000c0000700740004107400110340d03d030000440016412500c00fa10184910043c0444144610415090205 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 201536348 1250 201535098 201535121
    0x280602061504230c0d0506030f190609050a0b0a0506010905010e01030c2304030309090b0f0904030c051209190810021c0207110111010213060e0d0506100503010e0a0503070b0a020403050a06050a 85
    0x1409201c3c49060300418ac244c0b28986614040e000f401c41d901d0984049d100f01c0c80c4c0a4a00d014005d03c010511906209040c400d48404404105965405005507020704050080134000790144e12101c500d54000c1d401281110650705291a03000c0700c0400d40f0170342a00210840c00c0070b2001050030000c06400510380d50161142590034449000110045110882c28042c11403148481802040c14540603003050705903190043c0c107441a03000410f1642d4601d5210743c2d4410b000751805071807403861401c070508400581ea03100020740181348185c022000a500a009500a903810200c3e00b0f41b0300e02c41910041c50346c2c510034850040201450000541010407070091b800e0203074010404821029400d00c204001e941a50600c0b111241c8030030f011803445180c40c0d0700207050340308407420f10214849240090b811254224000c0c041020407410181d01c032182c2d00002440303079105004050000d1070381e0414503030000842000609082d071b40c9d00d49074600f4490880c282d40319030380d41052003081c080b980035a0b0808107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 201537598 1250 201536348 201536353
    0x702150403082a37030210150b1201030c0f180f0f09051609020a0f0c1b03110901050303031b070809280602061504230c0d050603 57
    0x614640311034030103200c2d85003080056124443d000b001c0d6041c41402556040d4024201d411503091080500e07812101c0380e00d900d4030810b800c0c012500c0f048150740c58080065155000d072034880c61440c2e400025025403203414103031800d000408a015840c5502900c1c140004c00d4084409501d5404c0c100380d10348807038008502200d01648103100d0300001c2440f45100150f00c0d000080c2c14800d0100c01001001a5000b200c1d0300307806c003203d4a00b800b000103401d090070b00d1001018004d0301d640758009030481c424100c100000c5801d81c070b014070fa0f050007480b02e403d003a8003541c110324180c000d0381c45689002580da001215480210080c110460030320440940c05400150011450341c104440e02c448178080d0f407141408500342c0003854004001d004002d941041c0e03000342141e1781403005512406c010590801c28805500b24040e00014814400075955000e5442c85003c42e0441030501c0c20300c000b0302500000e61443d0712a401c1c01400c0c0c954a822076038428401c1e140318584403416100c1250503502e01903c0c1d50b2295 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 201538848 1250 201537598 201537607
    0x1211060403050a0e010903211d1818030703030608010c23070201030f06060c0203060c04050a120501020c070b04080115030506060409020a0f0605090907030905060c180411070215 78
    0x82d005400c4941989150400b00007001203000101d81c408070540005100700242d0000d13150b24200140c08000d030480315100c040404510b00d00c04030351145800e540075801600b42080300c0d14a54112800d0ba0048152180140c540483e14540c91030342e8071071441180042da5404080000d038800b03118a02d2084030a141480c01104442c54803480a600400040c8040383d000507108110780c000d41c0700014086801d00f061003030f5a030350309005e4003400c8800710590081c010070780000c041c00d0450045a045c0c1c0c6001705004100d80c00e041d0104c0c40c0c6210703503004451540d402c10800030b04103002c0007114000d10807440d00d04c1da140d0820300c2c3d00f4207403800a661801201c099040c1070000540100f0120740c86003003910b00161001c06400001d4586c01c02d54802c1d1900c44881c100410b00303a0744070000305144582a00d244016480710b103011011113090443c0038116422400100e55030500020040c501d204040040080c070041030000141100c0d0015813880c9610f00000d201000c50818501d0943c003503084481807400c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 201540098 1250 201538848 201538853
    0x30103061427030c250605040806040f060207080d0c0f1d040e01020415020d0e0a03110118270e030408030f0a03020f16050c09010b0a0318020d12110604 67
    0x41c2640d04405403104600d00d0007900d030610041043e42c0c25500d0301340c12074a5004461442d0550320b0b02179200c0e004180d42604011503003a00903401c4070100c5010781c0052403251b540761103007038081118030000c40c1c1c841e80801070310020804034030240c262403803902000a050300c51b92202615080600707540340d01b802180600c010b4180c42106626038150302c1a1008a80070f0a45001280284607580182040071a00b0780135800a41d40010018851021a21030700680e5405c02c00700f043c000424400100b01d40d18420184001e0b510800d001c82e00d10183c10721703880c100e5445583e0700d1040c0301c14500d221184000d840038600030a00038083c620b02031440764040c0d1300d024280070501c1e0b2280b081405256440e000003603142d0310103110394120351903804541c11103a200c1900820908820784910000d07a850b104e803a890b80014034020041034100c40300c0c0080301d840c0049000059002d0081201c04903d188400b15107070025840f220300c60b512551180200e00750804400c0b0004d0b081c0081d044070307101641c1c4501c080000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 201541348 1250 201540098 201540121
    0x1b1801091415061204110a0f09150e07211a031006060806010c15110d1b08010521150702060108060114010815030a030f022104030b0c0c060702030301030614 69
    0x82d06090001983c403aa5a81c20105031003003070031141c03640187c4803040004080b901c140b0140182d0340d0101c820320180c0301c03502510030984001d0061515408542020564450094441180c12072400310f000c48050400303290902200d00d802c05075036480e108041700c00f00501c2c06201d21009400d040c50100f000764101400103040c4003005050702d051240a01180050060300c030104c4400c10680c17007050107071508400c851407154000fa290500040d04000d0302c1071560846000e0300c1c2c00840b1954661010307030310380b01c10002010b0240502c030138034181503421945215010300007050a0100e5101e031100b0350500840003880c001d4141e01c404641d41000d4014060036003003c035080c0c41c1210034a40041d0716104c040328004010100021b4036858032400e41c03c0c2c0c007003580080071005441c40940a92f1740514122241d0021000076010040220b04100b2092000942000c009900100e03c6070708141040c84070411149803031001d03503058001d40d1010004100704001400740901c60340003c480c80c0f680d424080304161 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 201542598 1250 201541348 201541357
    0x60902040f0b031b0a020a032616090807030803010311090903040510052209060b0c0a0602160b010b030108100c1205040201110d0305040614010303021b180109141506 73
    0x2405442c00030205101e00741d07500010500c1921007030039641d10740c2c00090182da507492501007203011940c00e140d072001240941c0d00b810803074170441140401590724030f1a50520030568200000c1404040040800d6001080010001861090420700e40d42d5045040c200081c0c050b4145140c803456003281041020000441a10b003103407400c2d29125003824004d0f0050710140101c5040c815400f121825035404c0c48101340e504011604850030421a0300e44a00e1003015920880c0c50b00d11050740600b5440e00000c49542c0142014401c0c280001012201c070f0f030710340071060f000384e10150410304d01100510021000388061a503a00c62803004202c1c11001d0300c006001c0b0700e0031011580c0880c2d07035140003900356401464002c1652440001741c0b41c124a81030005001840107544c15030340f4034541000100c884078040d80d82c1d81170b80c3c1c060700100016030010f1000100301000d0b401813908103c14801d044005c100c0c0c4401180a0111810049282170740511002c08911004103036030410607641400314a40c4c1c407076000304c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 201543848 1250 201542598 201542609
    0x3070506040e0406140a020306191a0d1b120c051e030a0609020c0307060e0601060e0613090617060906040206160303020f07080a020d080c0a0503180f010b0301060902040f 75
    0x322850b66070750130490000c003148030745900404507003010081c0c12640d0350300452140000f11401d107005c24034501201c5884446001d005515202076000c1d481c00b00314907000c1c00c3d144030322000c0400c04550207a140c40702140b180d2011004030b02802c25541c0c000f05140690052201c03145405420000010041100010301c00c018841e500f0000005c0340784062583c000c00054141560305550312441e2800140d541e900000081e42d969250148040344101c0100740c26040740d243e42d0b00c1c0c4003100703988010446107522080d01c00112015271100011019203034000c600041c10f00070501d030040074090002030b042038001403441190303400103810080141c0e01ea0301610b20705445080004211040380c501a0001e20400749001d070110804204001084814402082a29a030740d09446c000a50000203541c50281941c46d10303140c1c4000c2c00010090351080700650790080426000c00f5103500c00901d00750420050003107e8115035120039080e851030509000f1880180200c41045140924180c0c00c5200c60b100390050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 201545098 1250 201543848 201543869
    0xd0203060303091504090b030a050312090703060603050d03051509010303050903030c1e07121205340b01050f01051206033a08040201020604142410050307050604 71
    0x440d44030346003041901d8490700060005604020084481301c81500706103d08200b60f8140403400030942004104486195800402182028200d9800d62075140c801030020015114107034000000c1002401107500943c000c5c805485d00c496401c4008066070002000039078240c14110907081a42c56200d00c3c1c40c1101c0c0c1510b800da44401c1300500080c00c6200e001e960503001c0c4100c200c100c282281c0c0300b1100c5880148001202e00f01581e034252488a03121141c809803002c0200700059010314001c600402103914140712501442007500d15a411928405480520803811260540308002402c03030001c1c094041266034184144580c00000c12500c9001d030000c4011070423101142c61518100b10840e00f030341070240c0c041c2081e542078035901c446802c00d400c00354005085460340314003a40500c41300c42c003032a0180d010b0240caa545d80c4842c1ca11480441d80600740d0b2144c040607040d1500110001084005c8509046c14542040d643c18104c2c02441d0304414802d410008040140b13907a0391085508585d58280d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 201546348 1250 201545098 201545101
    0xa0906080c120f0403020f160807051009030b060d020a0305100b3012040605070302060c04060903060c02120a020c0a05180414100f23040206030a1a03010603030c031b080d0203 77
    0x400303c1c01c0c41d410b87d600a0075882241c0c200c60402c0030300c5400d10140c9500404946c3c4e882d980390b04008502c03c24091900c04564000401d00200d00508111984040c000d0001d14800e040da5021500410183c1d1081c2c2c1c0f150400919170141910703500450888a4044542d0580301c00c45042e00300c0360403020700040130284021032040c2082d500c280007035820780c03008070803241e207955032004050007581c04018110018050400001d142e014408261001d032401e90355800901415542e58000800c15083d42100b9032044080030801c0c80206002052110510760141c8210030b8680180859074813182c00c0705200d290444002c41668021080d5194025040740445a40141a000540c02c02141040c1c2e0300c17446041c482d03900303944160307500000308600640ca00000c006102d9401800860010380740250301403010030201d240300d001500300b0808102c60800a0002d072140f60000390071903a5a900890200d264445c0302c006050308176001500c0da510a0f247c102c0c02e00a41c0e40da0445500c00d00b112450b02590120 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 201547598 1250 201546348 201546353
    0x30106320703120614180f0408070822150309051513081314010509031e03090a0906060806060a02030306040c0905060a02010e0f152205030a0906080c120f04 69
    0x40784800402010020095542c41d80941440040d1740700c070780750050b60042c0d0a5034262140d1a500740c842c00d00c42c02804075684440e940c0c2032144d488200140c0b2000c0b0148403a8001401d841b44001e900b02103903000000e601d26200b103005400000d060301c607041c903190080c0000800d074080341001846500080c4040f1641e1060380d11541d040c224800a40b42600128a0000c840134040d0300900383e40071030381e20f800b102e03050360011200ca11034880c425805030040c06000480780000240c192988010a0a0b2814540b45202140300000d0b680d00c9241c1d11a184d9104110399600000000d801c5442500c0d810315100b00740401942d42d20014081501481da0f5440d04e0401a1042c400341000d041c0060841d07607030350341c1d00314001c0c064581001d014200b405003d0308001c0c0b0b00c00c001581d055603500002d4195040c1d6800c802c4c041090140d080b4600a6074031200c0380c6000500900041011100c540c0b10940c1e50760521400422104c4003c211034086042009041c00204c2c081d100564050052400b422282d07440c2e1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 201548848 1250 201547598 201547607
    0x90102071406090613080901031a1309020f040c080103110d02040905010914030405031b0310090c06080f1905090a1209080606061912090512030106320703 68
    0x429014021504484a5500041c80402c0c40e60040c110700f8100d0340705032105031440d42c44c0640b00100502a810420035505207501a812803401c040d88042192402070000010031149040010407003051940c64400c4411482d040c460040c40004c295420460a00220fa02811408042c003002d80358014058203c02d256681d40b541d40000741e40900203029000782440e04134041c08115100700ca4028205a040f404a03e0000c20303507048407001030007001d8090003811703600442d0f0408507a2a4140c001c88442c100c04409900403480828864922415500e242000c0284200720180600e0f4824001e40b050081d00c20301c40b8600011036012090008003a2550f0510710319091034820300504003000020600842034010300c0c8101164400c8094500720307034070841000010302c90706440f215100e85070040c00d4941445101e41c61086060180c0000e11391815481d040e1800e542d4040c03008800b81d00100500040398000284100c50320720844040d40e8101d0100c406c4c0c85010440070500c41654081410420b1500c43c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 201550098 1250 201548848 201548857
    0x601170120030a050604050411010c1703040309030308090105060a030605060303070c1707090203060307060f02070803070c05040b010c241103090601030506090d0e0603130b0f15040b0f0405090102 86
    0x120300d800d51280c0d5200712003012a0000c60700705814a25100008070981031034007a9520907507206240348400800300006541309001d44600b0354400104c1e0b6418441c0086c100015405140241c80f00320348680356107001001d840c030081495007103905250038414103446100b641010b49510070030206283c0e41d4040464a14000c50b0310140804203090800241500300954840703943c1c8543c42a00d00326603c0d40c1e00380d03050344025100d03541c155010141c10414544036074403150361040720344107540e1001c0c1c0e1884000d2441d0041542620604802c0404020a03d850302c541c201304d440a081042900505423616002c031f4135920390301e02000d42584100e0304014a141d0201100c0c0440102458503420003000050b40c1e25001d001c11900b070700c500c07804100d2407071b0300192404046440e903990003030744048002400741c90f40015006610840c0521803101c00103000300c140a10034113000d11024814a04058441c0c41d841c07038440e03000c0c000e51070541141c00c01d0f11105111f10652205032070104440d101c407403126009110313 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 201551348 1250 201550098 201550121
    0x1d0604030c030e06130f090b010519030b10030e19030804060b0a0b0d0e0705090405061321080603101a0d050c0301050f0f250e010216080f0f03040806011701 69
    0x1e0007200b00c1c41030400171010385141100800c0384a4480d400c04040b101407800c080d003c80c1c1d061008448045e540422003402c0643c0e8500800e80100c20804038041d441c20851900219880701101050180c0402039051070907086c03c2d80115510b2692009069071700b000d48007401e450f03100d40c03d1042c90384452032104001d200001e10079a80d40f16a00900c0c000301101c0030118024020300000044c03074648201c1940c0101d0300b01d0050842a01d42180c1c2404811096034111080915284089a0550101c40c0501c03a84d41903115864285086410141800c08480e194001d262070b0280c87c0d4485040007800900039202522031010386903803420030f030303240812005040782c0c99800d107003c0020107000850003d0013036001490200c0c854a81c0c1c0700c2d181046800b40b1529080d80c3c60040f030b46503228400e040c5411101c506006407150544080c481d41d46d480c80039081183d01da8070400d1900c5440c0c0e402c2180088003040070002d542000e06150155480d00c20610450b000040d6040e9848074005c820b5005060489 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 201552598 1250 201551348 201551359
    0x108070f1112210618040c03060f09030305160e01030b12010c0302190302040b1c18050706020c01050720120609060601090503060f07110102040e010e0a1d0604030c030e 74
    0xb200d0101c080c0032584456116041034600300b401d030b03514440c80300340503008400003032008000c0244010075500c07075000100140c1d658024528000046402d034810340d13a00001d0904040f40d0700095080203000e03071700301524107012102c0f04840080100c1e44810b1403501d10300c00b40f80200b14036521500040e694142201e402809518186421002036015801072840b41d0761402d011172000d88190003901280524400c15101100805c0b24405440b00d0300e1400300b42c20403a007000907d04800204007a409550031004844c02d5021607000d04c02c091b0108207500c0c8488092030418a00400b559510080200c820380980f0a85598a45003895a480e2801c00901401d0306d0210b404030b02d40325103a07590382c02082c0c5d079440c08989200d50204407401c0200742c43e48a4050b00c0c002200b161140d480840b55000728104154007035509002c0810340700b0906c00180d000303001c0c0f04181c40c0300b42880c42c2c050301151035404140001c0840c9d400888801040416402c1d0300c0f942508001d5050345407424241d95402a1100d01c03903000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 201553848 1250 201552598 201552613
    0x120c0c0c0301050a2406050409050c0412050706020601050a051c060b190303090b190806060408030c07030212030a02100203070c0606030f050d1d060705030409090f0b090703020108070f11 82
    0x286440d44078444a6600c17100300e98030038000001a04510f8424000d000c0051010030003400760465030b03005160011503040700b440c80e0680d100c43d4aa10071580300000c8401c0e820141041021681c100001809850103e42d05074241d880e00300001d0344250f0b180c0040d00c450b44140c0070360041c4902c1d50302c580303940040541481c0b1060702034800782401d00342c02c0c042240410a900c8011500c1420320090312500364030080c6964950403540407e039002c0200030304180d070002c002c00c408504035809001802800200301d0040080c1421441000300c0120100e507404000c0d81309103c0031261941c00070340050042c51602005070349460b000c1080b40c3c84070300040b000d41a5070412000004122038110810001380c083c0c2c0958086141d868411124080d410b42000800f03807441c101c2c4800352910f40c000300ba013144140100e91510b50b9404106040c0c485501066451315556880c4c03e0a00c80e201c3d0045600012044c06011020701310382c0080c205110240587c803c110a0b940c40b403182078010740d03286007a1441c440803a00071 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 201555098 1250 201553848 201553861
    0x212010f0305190b06040e07080106090c091e05060a0e0a0605030411040605031b0406090c0c021903050706030e0f0703150b120a2d0501020d06050303120c0c0c030105 73
    0x1242030351004803454480d9802016107540082407208650707034008082c1440d40c8a01007000003620000268040038040c200e130000d4113100c24030500005000c1c215011545402c200e002520b03145041c1d10550402c00c0001c000920f80c07124424210984000b15805a1500a0742400301c070182845148a41c00080c1424041401508070018510a078401e00700007680d05600e4042c003066564900c101505544141240c01104d448003111032102d0788003410008441e0740d1810008150f602c01d11801000c202c07030007581829410940542c08050704d0031101d081075185156038040c0d68110501c00d1004150b5214100f1624882c00d111140c007008071107048604d03242c1c0720b0138001008000c0412944249284c03c0c560703405410006007926207403011002401e2188003030740743e8800c1c110320029402d8404405920807a02c490b10001a1500c040c0100001a2591105056030007211545e81195200390310a10882c003021f5042200c95600c1070748406d007544c0740c0b11018160792402803040d28403940341d402c00081042c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 201556348 1250 201555098 201555119
    0xf030d02070c050d0c05010305070c021c0314030403090506030a1b030501050108130510090c170f06070905030d0e0f06070803090c120a11030a080d0509061621021201 73
    0x8841c01042090302c0c080c1d9070f104000524643c05402420081d662a00f0001c1e0b40c06580602da100001d4207000c00003c1c078642c0000d2800c2c01096140b10490f12448a000130b26521803140c02c500d80b0a0300c1810300c1c500f0f0a44000e00740743c0051103020b11801e40080040c0114101d07402c07002195400c12a0801c14036210740c000380241409008030b600140c0c500f00000c0c40f05401c07140c6082080d820034003400c01c50000c9991440541a50141525440310351040000c0181c2c0cc20050251070030414041c05c3c0442d0450b01040c14940040c08540c10400420018007596802003180680c1c1e803014200f40090750103410104a0000301100300c81c0d485140403540105000d03820340298440c0d01e00c2000d540901190703900b002041000010400d41c240d002101c0703600000d4441d0b904101000b4010300301c401c44da907181d03155003040e4011a600c0050365203820900010207000c000f580d402c01410a0708030190111910b00400c50010ba5400b0040351a80081022158103981e040365104c8003d1104c00c251907840f20352011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 201557598 1250 201556348 201556357
    0xa020406180e03160f061b020706080a020711190305010216020112020301080618010902090a0209041b02030a12060509013c0504092a06090b090d03050c0f030d02 71
    0x307096a04120001e185030360007108039003c04840c40118110340c50780f03480302001d0102e408401c4071130603176a0450500181001d104a401e405542d4001d00900c0e003805002480d00401901c01d110050040c00340324002090b007940c0c081d95640c00c0e20351a006072000c441d90100140b00d13a002800d070754800a00350500780d4075200d50341d4132a8004c0e02c0d201e21185602404208a1000744071b100300b141c01000104602856807a00d03507644010704400801d445c20985c000450b540f9050382c0451060713900054a013004c1c2030071f000f11190004605510100900300450194807840f6945c0c40608000388103ea9410b40c440a610410103007002a1042075550703110b840204070702c0c105142c0d807107000740750180300118000302d0a1529841d460b10004403a800d403801c0f040c840034018000c0c003200c40c2e0f1601214a803140d1140c1c4452801d100c0010241c02c05a403070800060030440b2141c100d950948000c1003ca50b4640300d082150550540c5441c00750342c0c038a004000d0b1030070000b038002a081a8000007134400440322440c4c0141 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 201558848 1250 201557598 201557639
    0x9092d0403020d02072304050612030a080103021e10030c0c06090524151009031e02040f060815070e0a060909061517040302070506071406010b09061204050a020406 72
    0x403440c3d203840e40801c00c21445441c40341070503901240015181b0342400d4011316080540a006940c0e2413810003007550447d0011507003940040c40880c010419441c149802c5003004000c41c0043c0085400300c00403810841441813810145034444603030614136441240b0360191550401010807025104c1e180207505c0b1034003040320034081903d0a00c03c2e0880404890000d02522852a81490b54100c0307100f03101000b8180303034428013031101c4550b000001c60140455031103090300482e440981e99640d8810401155a20300006170564603082051002a9001a00612624280460024680e1842000c1760300070495000142c00403226070000800c681c21050b0b10080c0e501c00f14041c8040380d220070440109042800c5040300103410381e04075940d03801044081a8120b07019205030341d5081d445501051465014200495880d261040403518108090194501400c1444041c034500782400000400501410312200b07441c482c0c02c0e0205082110404c0f50014669001d007043c89450307594610705260801d2143d01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 201560098 1250 201558848 201558853
    0xd02011b0b0f07050406090e0c190c02031b0f040515060a02030a020c180c0d150b0a0e0a1d10090f02070605100f06030e0106090e0c03100209092d0403020d02 69
    0x42441d45000b04c041e1410b42e42140e80b404446450b01846030a0654041c1c82582d00d000c0810a03002030403214101180714400c691a1300308450071901c103240c138088805401d100036241c0111300505940e13949807480c82a04040f107000c02c00d134551240f092140350120024581c005000650400c0c2e658002c03002d045120903e80070b0742c200e1200c1d9818441d15803520192580200075000004441d00320001c06452100780c0c865000440c0001d14102c582d800751660001c5440510225103145215444200c17900038034420744409900d0341c42c106d02c1801e000300c500300303158040203440c00284541c08080c00c25801080424001e00c55400503203c0c02c4d000354810038054a045050500040705860701005e03c0046407002200c2d05c61913441c2541c1100145602406429a13540314000043e00150034054804c1e00ca158001904d0000140d50070503241880c02d80703002a40740d006000c80d0746507503260003c40e03a0008155051000707003081d02e10182040b011448048000c009014140400d050307001520300d9050764543c08 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 201561348 1250 201560098 201560101
    0x180b0f0f07020325020a0305060a06060201021602040c050d060e010f120213050a06050d0501050a20040501050306010509060d1b142706030a0c0912020603060d02011b0b0f 75
    0x440c0004100210381000250b4010019615407059040c0fa4003804000d03010046002e114580c00034015080c01d600954565125000340110303102e82e0700c5550000c00003800210b14045909242c9410920f05841c080d04c280d544003a0b03420114043c804640b01c880d9000e004101403070b150704801d200c2010a0144071004101c052010800340101618110f0454006154420040108040c1c00c050100184558000c54444000003544e440f416907148059210b08004181d502d09001f8800444105103240d40c0c05404207074207407201046003000c441c10380b2401c0c0b03440c9643c1e5440380016526441780500d010340100780060b88441c01c541c0303940700f038003d0402c09015009400c03803440100d03903409000250041407a8104a4000340040d6030202d43e0150200c4080d034114022403400261480e04111139611509440e261081c038150b034858000c001900c2c0605160040355100d0b0041107080c000106401c0c0181c000902e698250381c0642d605254181011481500103030591030400801030f810703030714200c92240303000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 201562598 1250 201561348 201561361
    0x150a0f020c060c060402040e010f020c0f1005010b160c0e0702100c0f09090504020a030807050708150103030c0308060103061a0a031802030a0b1302060711031627180b0f 74
    0x1c088070b00c01a070043c01000702d40c0721502004001c0000c2d90488850b99622096855586154005000380b025020060621070b01c0a580b9181440c4002e41c860402d1861311006114580403c42528503001070040010f840070250310f0441410b514075000070311841084020003541c01c0c0d0006254000740314564050040c02c1c1481c00640710550319204070800300314070700707001e000e0043d0a90186031b21600041030a42215507a407205052030380100415101e581080c4001d002c1100d00300280c100115040044818962468a005000da0074510b001820080e4040200d0416807003500007501411035800200d080022403813005065911050881002c03a0920039850300c440011680003180c45e4001d0050034a000b2140d651441d0198020112001c0d14545118200980c54280241c60220301c070355071074501e00b02c03940205480c0141541304400740c0c103451841032148600c80940f110402810392038100215001200d910054400c10303000440c1c000c0001c00d400c007806407000c2400c1c011641a200820340391900f5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 201563848 1250 201562598 201562609
    0xc29010612140703020904240302100905030c060d0b1f1803050a030804080d23060613030204181415070c0804060c0f051f0c0203130e06150a0f020c 65
    0x50462a1450840d0020340104c0c0240c0040000c100e005100007036a44444050f0756062400d070315002144c2442180c24400c41c204140c0d8034661300301c0f5003400e03118a441c003000260b440d0307201c0c3c0c02e007030061034045000d4101d440140c000a0341a007004180d01d03115000b900a005841012101d200c00081b031a040c0c3c80f881a60500511007500d81040180030202c4980c6c5042e12202e00c003034070484040c0001c1010361400e04251044c144035017208200c1401e800868800030541000c068501e5209080400480400c000d00c210900111ba906590200f038411201140380c008400000014001103110b211001240001140b064480b07100d103030880100383c4516408590000c0d00c07680052401408000074006140640c4100501502c170703410100d1a10030356601d0505200218040300841152102e00544031546401103840d180c000c0c0c4001c1d800d084000c07101111310203030341c800e1800d0501200003003219905c0f00103410307008440300540b840d5940c5051031b00a15000007012044014055075005d1030062421 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 201565098 1250 201563848 201563861
    0x16031d06041205030c0a08040602011a010e0d050304080a05030d14040b190603060f09120e030d0e0f04052401020102180f03100f230f01060c29010612 66
    0x6852203041c0380c2824080464401e401c802540c181c4014405002410390400c0100e01300d51040c0d400d079895a02d007881c0a4250341c090410800541c0f0100062540c41c0d03444050b08008000403605588409a681010390035449541c000210394019008100144a0000002d002010085208104200410584408150050b5401000d024461003c10030300030b0302c14008003c1c01c41a84c00011481e0356a070744c80046582103480d94030040e0f12042c07400f040c400b041480130b0251107517003041c080c85c200103070001e13803620070419600090001c0da410214164070b8510302d402c04684058003c0096044c000c14014994050b2580d0314107081c52101c103612154810f00070b41e6061480800d680300403d043c07004110b8040c090846050300340c424008545408000c5029000c410380d1001c50000761800040c48090700103500116555044001e027003844020821150158110303401c0345418003040080786002421a00c405000320911050710802e01ea24480e1503201a0480e401912400700301d00096041c04182d9a4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 201566348 1250 201565098 201565157
    0x21504030807080c15010f230a0b160c08031225110a060606050c010b0109051003090309030c0e0621060106050903210a0201060b0705060c07020a0801021603 69
    0x203060050400041110020303000a03001e500640e18880004482217507154000d80c420034094904a800300000401412066000c500f0b01c00d0300c1070700c21000004141364112901c20000c056000103041905002d41564507561b050340003100b1041595a50b403965940d410104501070203010304c0307011803036240c1c00c0c03030000c044880414007000c4459500b0b5000d58150000040034195400361b160241d0000e6050300ca01800361100307855064071958101d03102030031108000040350500032110070902240c1d4800c80845a856090f240200b9032200a107802c030b03502c104031307800103000350350082c40480d0403039441100c40d1003060b094604541488410300c8603103040300e1701c01c0201c52a4000300d005000440c03027680201841480a012103001c403102a86008038100d61541c40100c400001c501161a20342c20b001d4003008002040c540360601059841c1d46490b0100034045242840c00010305104545031021440020700e003c0c1c00031501e07450030b10192048248048022000100281100b0b09280300070740c206101d010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 201567598 1250 201566348 201566363
    0x90201320906041205060a0c0f050301031407180b040b040204030f03080702010236010804032015160e0a0b040501050d0612080a12050f0604090309090c05040302150403 74
    0x4a4882410203164001d554090b0030501c10070000c10704800090307060b103003036115400a184502d4000014412602d2003144038042080180d01103007041c1d408000c0e207041d03e0700070f41400b003500407004050749400299400468940501c4c0140000c0e012903910107640e0355020346050000802007001c0200303c0c401ca001c01410010005803180110f0b03c141000c80d88a900c1c5d000051401a03003495080c2c00c007014140c03200c80c3c1000d10880c07039125991440406071b160020708040132141441e540c00380c20003034410380d02900d0813141c3d4002c1c0c1d030462017000080700c6810490216107490030905684041c600400070428089207170300e0b15130744c0c550500640c04c804482102a46074142030502c40115070700c2d4005044007000540359840072441c40030036800302a0071807062429590b54003032014090b141c1d00804405010b65842c0c2003c0000490380d1802d40c0d075000c8012940000c0d82500351905a9403c03c080d000401c1e028030b000100707039980790410f00034010b5a0084821000040c640c41011040344074a000060004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 201568848 1250 201567598 201567677
    0x30b0f060a061e0c06061413050403051e1201032d020303090f06090a0801020702010807030c09210501110406090509010302030304210515060405010602060f04022110090201 76
    0x160014507207404141c07040c5800013100030316403941c02c26924160001155025011401a504e00e0051a101c942c10046013040c45186004c1e20003230164003401601e440a25102540c40911144280840c0c03c2c0807000150489156100d040400503220031072400324036480000301130640030802120302c64000d64000e0040d441c1c052008103103d541541801e406801c02000e200c450840e58401a8800103421024001a21044107000040c03081c117001d0141e0042c107180410040070340307521400c010140c0e591020000500d07807a9003000508141a0300c40540f8035441c000c02c6a440050a02c0104100c1e44642d0710040403d232240108030341560f00380b00095155000b000308100414400c0c040d030003401c2c55481d500c51901c40d1500c9117800c1500444071420303041d0307009042084034a02441090b01420051004140900e00844134011524001e807019100c0d811580c10302ca43c492104181703900300c2c0401e0050300e0702c5030308514601c005001020b5040b404501d0059201110210018005030b15205000c4c0034900c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 201570098 1250 201568848 201568877
    0x1080a0b0103061503060908090114130306270c080609030c150c0f03010801060e0a05090627011409010501170a060c09051e0301050906060d2901030b0f060a06 70
    0x204000002e41210b5441d407540000414a54031600383e00c0f90081c8e5240e41d6424120000401290441503e034030360b20f10610508503042c00d108022402c0e6603004000140c48070180030802060102c000242c00300001c004400303000c00003001207030f00898a120007110307a1612200ca40e5510b07801600d00b8004554803140420b0b0181d0040c4424a810086182e00302d031070060218003001c0b055000740c120b00d800b81c0d100c50041020390040d858040d80400b400d1001c201d00d007460b8200540b509030150861030f4a80780c11104012400614100c402c0303440d4580001c0050359410014004d00d1202180c4048040d4a002c1c0001001c018809030300214a0304540503004086607613403080300030404604000308110f40d94001150607255002c101c0780994100c8036080700900410105405d64400905a0b24103801007410300401d40c40d009643c40010754400e40083c1024a44060948180d261138888500410000000801c0c070a0b0500303070500506400198882d566690000e200b400740580c802ea90004500980c41440b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 201571348 1250 201570098 201570101
    0xc090218091003050604051506100f050a030e1b01020c03030903190512132301020d12020c030409090c0e01080a0222090c0f0f0b0d0c110a1a01080a0b010306 69
    0x9020b81000c81c41c92440791aa2122842d0002c00c441c01c8800342d108403c1e080b09030029030100395001000721044801d10650785801840300c0c080300400c41c01d000002c690000017a000c0c0d0040e41603104924122081040031300d1140d01c0c02d146400005016015659a8000609000c4110b03002070001400400403109804c40b00c9000e1707500400152414050303051403990b81c80c40c1c040117003d400d1104441c5142c80e400c0002d0b54800d04402c003500b49404043e5007240b000d42e60007003a014010500350070034890b542115000c08005e80f2a030f00d103040340c1c2d00001501040120540c0c0c050010240a4000e01044503150070401c9040c110038002c4080e1b070303803244a600005260440100c81c1c071070b8102e505400401092610301d801c1d0346402c10b0407250341d501c3e48400d11164003024241c00092410400103090a8a000542c020034070a210f8141e59031915000c01001241c003440c031507110003581c07400301e83c881042070400301350303d072202c07110000c0344580c07140001406800020310b0f091854120400110350391a6030348050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 201572598 1250 201571348 201571351
    0x2c0d1704020a0b071401090b100603090b010b030c1e0d0b060f03130602091906081b0d1a090a0f36020f121501050a080a17090603090102070c09021809 66
    0x303841716500f41c3d50340803021080c09040080c601ca841c0142060400d00c01c890390101554220724101031900080001040b10154283d046520b107082e00e43d40c940350b601c0389060342d03c01d10400c0d905403a00c4200f00300c20000b06100030303c47c0f034017480300410000305000e080221034840c800480444001c02d1010403005000e11140b009240e1040300300501d46181100031850740404403100040d00341038403408100481e0400364641e803210046c1c41c00c4045612040e0176407842e009107008170184070b540e00c108851501500d075010444a100401400442c07411040e010050604500781d02591030500b0007035038208038200c8a80d00300307594110141201e02c0c1f80825214410001d010140c3e4400e1144180d030000d42c0b154030002c42c1908004000d8140031701d40c0001c001c0314a006900007401000520340410000d07101184a010590384076070b9680507103044241c0058980660b0700c101c1d9000c000042809801803055008003401c41c400d448569405641e0b181480481c0240d0844031019400c403050301d00f451415a4525 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 201573848 1250 201572598 201572603
    0x613020907210c0f020f0f070e040f050609061515030711010b061602120c061e040e0c04050310060f140303040305120c06010f03020604092c0d1704020a0b07 69
    0x800b041450000140c0c01d03a880c10000d0030110780e08110324034682d9418800d00007981c0040c0e00608000981c2c3c49201d036100c1551044912a202100201d0304000c0882206e0384415040011166603007040302e400e580f115800d41e035a10406e030340d404141100d1309044200a00c0300c0488000c0604585e16580305035012074591030b890320386540c0c41022141076a641d50107081100000310346141280f525205115485034103182400003a4000e6072103018943d1404101c6020321418441d01114000d00d1104201e40e000c1c6030400ba00301c0c00c2000c2044003a000ca0302c040d10895108504032121001000c10207001caa2844c050300c290384800002c24030030103800c00018600d0078405002c607450550b8944401d801c01000c080141090000051424561001044680d000d070500240c3d5030046840d650025040d4800e512451030301c50f46403802820341c4201c1200403c4443d00c008c81d10301d030050303010f4181500d482c0041584400f081e541c40b2862103440d8111252481180d001d0241c40105d410620503182c1900220b204 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 201575098 1250 201573848 201573887
    0x5010f06210f0209031501050f0603010e060d02010504080106121205030601021b030a0b13060c051204020f0406150c150213050402030406150308030105040506090601080a0b031c0e030613020907 85
    0xc01c04d00e480070000c4110140c0380e0042152154103003800c001800314409112442054144010f00805064168907a0856000c40700d8402500075880140c4030341c0035680c411080d6529004000a102e42c0890360325004a1040c1c683d0108000904001c0e641e9020507145c890044c0d000c241d8407603542c2d0303840c00c11200150000741201ca003942207a484581a84081701c07845200754040c000041004041d02491140c078269007441800c10300800044003401078000c2010f445000003495144440c0c8070340c1c1c040c6019040301d801032024188106809030000f210450100d444003c41900b161086219100717603180310980316038010342d481c508420007000c0d4002810a49049507100100283c00a2036400302005600c5400100d89a614100801c0b04a0346c00420160150b0030420810400e80e9120042c15840b0028010025004010300042031900e06450301d4070249409240191013803503040a07801b80c405100b01d0444445645030f640020300344513070080083d000300000001c00c80c03140c0903010b901d80240da006803 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 201576348 1250 201575098 201575107
    0xb070305031504140402131506030e010f020301080a030c060b06030c210c120a060b13080d0305040b060d0c08011104080105061c0b280609050f011a0c0a080d05010f06210f02 76
    0x2d003c00702308441c1e0100c07000c66594000307040002800e0141d82d4141405120860035036243c0440c0c29142c80e2315950040801c03050140001c02c00800e94006040315030080c100c1034030b03441c0020000360964488188403141c4a41d84261002c44c10301420003511582a00c03881f02e0800c02d07040240e010050000e004e000415496401c08921074030104044c0030307007a82e8580307580d440500e000461401d042c200440c40b01010304100410000c501d103122440e070041400d540c2d81d60b00c52014241002224900d4104003825402d01d545082c02e2000c0c000a00309071101c81008000c40d0b2100c00822050b1601c0e103100320800610fa0f003069001c0303000702c41403580c44640362607103001d4009001c00d1450414100c5056003031a940c1c0358400e01201c016445440e50001058001110550525092946150903481080b980ba00c000982041602c01807014081055101c51400d844d8081100104007910302405001c0340b0107900000040c01c03034842c2507542c000540700c20004045591541d01900030b0502103002040c515005c01c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 201577598 1250 201576348 201576371
    0x1030e2a061603050a122714120d2a0c1b060f20070b130314060601021c0503010510110d0f0806010215060f0a0b07030503150414040213 60
    0xc100b240058440d9440603502d4596281c05464034003149110000707189411414402a10b0071070358041074480208030042c490f181840c0400b040c0301c1d10106803c0c503000e404c00b060503400c0d01324082e241c2a0500442404029250400090034420b00604c8070500d00b816601d100f100c40c02642c1440c0500d002d46410746000e12005441800810b0a602c90380020300142c0c114404140e210007002e92071400c4803441101c85807d440c042d9901d2a082c00780003880780c1c0c00144003c2c2a019030b00008001c50340700544417090300bc0144143e4a03050111416405400348514000404803000d49252198030b590321081c0c116400c14040c040000c501c08594401d20a00240a48200204101e00032500107030740e0301d00320710327100186005000301b4014140c0c50641d44103448002071045600c9800b944560295100c4281143c1e000024850300b07040c1c0c2c88a000d541c0000707001c07810b16501030000d40c401d041c808001070002d903005090004440b4600607103020460210003190041c0b8006400303100111102c94080350250440 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 201578848 1250 201577598 201577627
    0x40908040e1602010501060c0b0610020c03100204030203070503061905040c0b0309030c0706080907030305131e0602010b061612120c03060807080d171e0109090201030e2a06 76
    0xe030b070340c04964110810200c40e96542402964098030b100e00d4284010001540d5400c845000600344601c03941c1110140f6a460b48208501c9410810040c21a4443c41e03490140c4d000030350050109a0103401003910115042c24001002c5000c3c05255030307030080c1140c41c007800000404028204030b03060b4107142000104008d42c00d0145d13005a01c5c18025654443c00c8140c0c1a117091242d901c202c2c1400090400c01031100750100300315040320b4160a040380d81da01c02080c11885a00030350030169180b80310340884411403541900100540b001ca030000c001031042c0c107042207101d005840400b922014158020400a032826401c1c03101845c90303003400c0c031f41840011240000e88102006000021356500003c004002042042c24024651f48020f01210000104010000030651050b000709104100c0421808802d50030407060300300c418080100c481d6101d200c004086c2c0007880d030070b80c0041d0a000f60091500c00116400100c0e1500303919510007403411401803207028800c0051260b02c03040c00c3c0300404002000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 201580098 1250 201578848 201578851
    0xe0607060b040c03050403020303070c030e06130f080703022209020901090506010909091a0c040306020403050106050a060201021315050c03120402180411060d020c03121803090906040908040e 84
    0xc80000c54140c03489800e000484080002600416081006000c0800d4001c17085a40001e584d28082c3d8240303101e410700303480345590002c1d015000100003039032045100303811b40f074542540c1101008418042d92140d1480d610126808082c3d130103000703004481c0b2045450018100101050100842c0090301c03900042c4101c0402d03842030b10300e0b82d02c901c01c0220540c1e00a1400000c1e003546038003000003d0040c0c503519086803200516498100025000c2811810480e051742c1c001c61340042d09568490b164500140600401d12502c1c1c080c0d400c250700440d03954010f0090741d0507050314480380100f080c940050b080d40d4005015003042031100c01c001c002c150340801d100400d146850120500b100342454070500c08800118034a1043d110203850a01000503c90f40000d80d005004946044c1c407442a91691f10003071045030002e0b4020703c03002440360000b00300303140424070400010048161070030120041a849100782c58880d548800c0b040e000843c0e030720b0194030075a0498045d94005040bd034440c19007d4a0440 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 201581348 1250 201580098 201580103
    0x206160f03150e1303020601080307030e04020706140709031a041a1801060b040302090c0403081206011206030303090b060306150105030411120a0b1e071b061a1e0d030f0e0607 77
    0x441c0c04c090580411690b801442c41a00840c0381c00750701d890090003040507580ca90300c01d58000451500303008807070300040004040320000300303540d0818250150070340b40c00d44000c0b50410b50603500400e0b03021144020030300c15500550120850400408402e01e103940003006e900d600c0c460050030701084003092040da0081c01d2030303201c0c5583e101d082d03004100002d080108442080ca40c20001400003070740c3c000554040d0400711081c841035480381801601c200c205611808021880c00300000203041e4150481c458450007101516401c0e10380100740340d211201200c2801c0301c91005011550554802c1c0000e540c86800758410185070030711080014007003143c03204107203c958424810a014403400c120101c2d0841e040b400d51802105842c040003440400007408807052151006200510001c523458032001c013a84004100302e41c110b0200e14103240d00c071140d103160041c1c010f1925284035008050301c2c84a070340c4006005011904259808450100d505d480031000c1003070700d2000700300580300c2d00040c0080e00d1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 201582598 1250 201581348 201581371
    0x3030c040f050a1202010c0f02150d050703050705090f0a08010c0519020a0b01030204050619081e0c0a29030a0f0b031f05150a0e070206160f03150e 65
    0x340350a510000c84070441e00902e00c16041038004004400c01104c000803c680d081c02c008942d44450700342824042d110041c060f40181c028150605140450070082a8503050700b241007243c0c0c0c86400c0220f00702d84003150b551300852800c005100040c03a00c40b90784001c03414020030040c03849882e8101d040c00c0d1500c0152060105a01051680c161501c40383d201d1011a403038401499408501d448050b14440103100c080e0085558501044194540c8041c405a0019481c030212090b0340c1c0305242651202e4a001e080a10a60300c00001184e0340e020031003031120500204013100c10b50030035140411980c10188503811400302d0b046d21079852424140518401c60503568005030140b1002c0c4c49030190741d090901d0030310a13041000c003403c00304405000c1d0503c450f880354001445076240311010000803010400030342e1160070144c0000d440400c0d032000d5032050125509950054482d401c0e040500c0f039107694460041a0502210400d0070b01c030b6803101400500e80f420000716a03070f640c1d5800c8210b81c010344803003041c034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 201583848 1250 201582598 201582607
    0xb0a0603080f040303090816030b18011419140c030c070c06021606030207122a0b19290609042a090612230c0403060c0804081803070803030c 62
    0x150300910b0140080c1047c00c094589064030551015540d105400020306d8955802c02141015149a40c000c80350b14078030000b00310300c246400088001041c00ca07034854070782c4414400c1c02114041406600500c2c03503035180c008242c0e00c40e8840303c00302e5003004012540b01c213001c1c0180ac010403900c401d0340c0700600480d009403000008560214004d54195004442070500401920002a14080d02008500c0407490a1501000507020060b80d22190008104101c0789481c0000700303204201d50700502803400c54080c281c10407224902e16003542e914820300302005440d58800400072480c0b00c25010b003050010100c0d03241c5542c82001604480c140203560401c2620072845207690442034010000b00a5542840f604880c5030007001855000c002003105200c507141c50882e04a20217217907041e4079241c0740d51018840361510407031603944d640162100392046800e01030881003980c050580f103400383d500011914a0860300410242100084000c5140c052242100000300c140b01403001e503006030800c080c41e5644 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 201585098 1250 201583848 201583853
    0x130b030a0c020102180d1112010b120d080112111003020d0e0c1e01052701090e070804060506030309030717010c03150e04051606020d030e0c010c0b0a0603080f0403 72
    0xc407101e4500000070341e031040000d29001c61041c0541c4800351401c403502d10305d181061030108040100882c0107500040c01c1c8560102080d0103400094207084141e6000201d0340b03040419035a02d44256440d10301080e550360050200302e0181480c40c43e0b280c040c46d1002241c0000e007000c1001441c086440000003580400c030307482070754000d00075180705c07401841c0101391141026002402c61080c128003a1000034000301503100301d034014803d130f600c1080140e184002828012120f400e4800d5212485400201050b1000c01c10080003002503009244565805525640391764665000300070103000140e062000380040c40d002d41e002c1001c04084c100701200d00703507103c2d02e42c4200c50a450708170340c6000505007030010401210a80280304803c0b205c02088104650b252404c200b0305100081c035a80c06c22054034080800c0317164001443d0342c69030220781e03400c11180d480c41d4119a00d0350305034442c01d4001407895028001003452403e46640256003884001100c036030380e80d00d0b8501c0c2d5002034220b452141002c1420401e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 201586348 1250 201585098 201585101
    0x403020108010506120c1b16050f10021c030603020303190306170a022e0801030209070302121807121a090303160302070c0b0714060108030a020d0302030c130b030a 72
    0x40605850711400c05d45400c44040300b09034020540499075030b0204404003103518001c030103105056000180c9000c41d688035602440000c640c02800d01540441740e0030003550402c0d050180c440b44c3c540d0b0240a10720350258070540f240c4034041590040503111000800569018001001780c0b00b81940c0684048403a1301014041d6207440d8880c246041c10080740806592000c10021400b41d811141407560181560355001c80651800020443c00e589120450403140c00036001070680f4000c071020004c80d0745010303084003a0321404501c02000d11401011800c80456001b00d000318103090000d444145071201c140c002103122014003a90112051000301c02c480d603a0443e242d40141d02a80070f180f440c07810000b41c20340f007100e442408013010fa0016921080c4a4071905480240c94030380d40c11541c0e08040d0408180c40200c400303500c2040d0042100002c0e1129000007110f0a140c2280c016040c0501c1c011001e40094000038080239201900300a500d50300414403004001030100e814420392603080c1340c0000030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 201587598 1250 201586348 201586351
    0xd020d05070201061a0f030613020c280c15020703050f0106050a0b0301062007180b03060f090624060d091407050d02060307120e01020406020f060115051b030f0403020108 75
    0x9a40142c1c1004440e59121085c046448402840007060b82e030741c88000104440100c4e08880c140c0b5188041800c10f134182e40400c1e6903080c0f01454040c12600008400a00e410100c0904004c100f208003400400594080c501025048000c038010b581c4501c2c4d6a4540d6824004c04407240c3ca0565501e000910003071806280031405044040a4107047d0341c1400f10207001c0108459500d400140c2c0c0b2030f103a00c02030408105640290100d00d0f082140c00e100820b11102030080c40301d00510074000c0e8400602c03a104011803c0e4403800304400140140d1322444402c8e941a060030440343c000800c1403401e1192500da0200a1191107105280003c804200e37041c030f0303d19416000300c040e507503401804041016030348115810b03100e41d4045640d1a920740b6620000c0d1b030700b511048030710301c3d1306414a600056501010b40c0908111056a020b4a0fa8520034012031600c0304000d01a02c46c502010359075410250344608041c080c0c800070241c84504509000314046d2442d0417070b18102040d620002414411543c0c010300c00d0303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 201588848 1250 201587598 201587609
    0x103091a07110a0809011103070c060e04060e06130209030c0a08060906010e011401031812030e1b130504110d08030403140307020312070e0a08010605030d0507050a0f080d020d0507020106 82
    0x4280100f02d90303842e40080c1c410050fa2a040100d40c5420310303403800d41072040741c808079400501c66103800c3e5078003405801e1906000c0228440c1c0d2424000007140c01d0100511481000020210081446410001e0000b5000039842c6038040c81824803850582c4c840151b94400303004580010f022900e400140c0901d0880141c0080210000210040281100288800541101c00d003400b1401740307081c0c07031a071903d4107006a014000084417011100300c41c0d007680c0004009908801990038001c0e00e030f003e02609058003000d140d0000c0c51445c0110b9036181075406581c22500c43d013011111402e07860002050789242d1602910210000000d0004054000740703a840c0c5c2c200080002411490030000107510f0b405111521400c002214001809040c030070740365105100002842150201d03210810980204401e00485004c4c1c0725501c02401403074068000c1d60f80b8070790712000404c04c400a90341e552030003071807882c011141c1040c01d008603080110a4006058007841c1254001464900b800009080d2915603005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 201590098 1250 201588848 201588853
    0x9090b1503070302033a18140102150417031e0a060b030135031b06040f020d14100207020f1906031a03010603050d080709050d030e0103091a0711 64
    0xc1005031404200c07114502046c092005140010010768031618003034446441008624200d20032101e60000f21940103116820711406003140c0f2035003d40d40380d01c40c580721f46000d41d000000d00c1c031440e02c030156155402403054900c074450310107200c00d4a0b81a00b0a9943c0b9800c40d20884201060799018107504d544090380510510a0910f04020250144010f01800f0091001d100c07510061203820001d20010920305040080851468a50251070b03401040b850b43c81110781801441c0c0d0404005201d81c0202d40080807000c501c040d03582000a00007202e01d080711072080c198031500555200744207150350552007039405a518089441085444411585024400e03032000c00c454440300080c20301a0183e0314241000180d8000b00d5040034107410121100d6581582044004410002c001c501e1540181050b01c0f0f43c4043d403907441064031103d5407030040c42d400c42003034120117010902c100c0c88030007915018140000c808881c1d0f16201269000309446000d01440f01c82400001e41e07200c0c0241440f030007240702 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 201591348 1250 201590098 201590113
    0x20909031b060c0f071a07050c0d03020418020919060801052b02010806010e0603010924030302030d05060a0308030a0506150f031303021507030b031608030715020409090b1503 77
    0x641210360041d48103c3c02c0010380491185e04200c0c20f8480c1401c552050003400d00b00741b400c090010002d1b841034000480a00803941d4000c01d55001e40242d40517202116050210703c50740840390300007500f010049617400580d688001180b030400c40011000303841e465444402d02d60508081c04000e084c00000303042c0070800e03900032890b061020b038207241c4100d03424681382d40e0a40700d840c0122018030f6960002544070800000001d0070340c0c08c90384162500702c00d41044280744140185207468034485440040d015802c1040070081300c0d80d16500240e4440f00c01001440c41035200e444400d815001150210041076550080c0181482d01d9186a00c22600e4514414070b40210300c5544601c0e400b014001c040b4200c0c8640d9400200340c000e001000c0000d600d988408550300d04a4001000f80c002200404d0080c0100c840c8050300f483d60902c0c24058450f20401145881c2d2196241c00c40ca9605001030241ca503824007001c82d1001007030150320704031805611250928204803c2031302c814480405118407030350280301c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 201592598 1250 201591348 201591361
    0x30105010c17091c02030c100909020304050106090f0c1206060e0409050c04020a08070e060301030209160c02060d0b041104030c03020105071506260109050c040216020909031b06 78
    0x42501074555000200342c0d8860002c0880300424029030f100325078040c0100c49900704e049225104005030500032801c991440440328140503c03a02d040c02c0482c0064101542842003e81a800664103c2c1c0314100006000d07580d44132541c212041b1417110103900303032101c0e51001b05941c48221181c09640c011400c02c41c0510f807540180c0b02c4600b021665000f40d440c2c450200074090309000328401c04802800075569481c03403820082441004583e04030110307041491000c1c081c1402000d9030b05803a030280c5a60402d03101c24030490620001c130f06118040000706010710700141c58000261140304111640032452000510401042ea10540c1d95041c3e0341c503042c030081000c40c0d10346241c10304903502030a080f0b0750360b4101d080803040c0d10354120843e50500c4c2420000180080c42a4005452019000c80d800c0c01400c060304231400e0f621621000381c40b81e0701000703040d0801d07e026070003000404000e03009081c524010360b02103070104600315140245d07500040342d5400c8114500340380540704c014050203000303d031038500c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 201593848 1250 201592598 201592607
    0x190206060306130606030804030303050123031515030d02072105030708091c0b01030b0f0f040210050c01060e0a15030c09050a09051606030b0414061005122a03010501 73
    0x414800a4030040b21442d01131000c59803214001d150001b04d200e50f51526400d0140180c0000c2c820741d191146801402103000110345c030700100d510b00040c00741803c03500500e2524903504c40038284644810b00f40b04840c081d640c00300b103020198045600580f4525190a010050742034109415540722241a010700740040c1d000b004844e000f940c41500151a082000080380c10350827a05100d4404580c0700e601c00080c00140406941201d1280310500c1a50b0b076401085c09003000181c0300c22281090907070224006240c10038059658007201d2411500f032070a800d0302142035803a40d600403807400e101c001c00e00c002400d20b405400800e400041c4101101455a56001541c041510505548603a180045211100d9540240301e155402804440c0e5811540780010311088140c030407400447d140007203400e03640c1407038000c201c10001c49810304000e603590071342403201482260982404014003009207207504410660b2030760042942840c8011100c1080c1c201010284d441040e8012550062004000585e0301 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 201595098 1250 201593848 201593851
    0xf090c0312110a0309080c01090e0f060301180b01080f0c060a030203270309030c041104030b04060b03010c09080c01030204031104022101181a06040b250305190206060306 75
    0x4001c811003010706441110b8004802e0110a118001c00d0b8003c403c0c568007009a6041d508494180c5018904e031000560b0760351080c0c412010310714064000906805041d01005500c040040d00101e5400401c0c83c01c0041d0340500e510460b03451002d08014003641400b040740b40c22107a111001020f06404072030000740e40b8001c81803032900309500040050f00c007418108000d0503055082d84610407942103098800d40700d421040f076650083c81341c2e02095400b4603250045074200307030711000307014946030850300d07154410744004000740d5503251680b0030000c664400340708007440810265030b00b03078010b801c009a03035080004100701c803410180140001c0c0041480d8440394081c0c6030b0100c40050381c6110201c4030240c0410001269182100620000203486482640c840c0b103428421000b0001c04608001a42045c02c0008a06070041c2c404e20060140420b5040100780404000113080034121202003880e078050071403d02240010000b240c0c0001490001c900b1451580050001c0c003071900d014800709650b440e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 201596348 1250 201595098 201595103
    0x40b060f130f030c090f0605101209020d050717010507020705041a0a03060209130e0d05030622020a0e011106041106120a0b031212070804020a050301180203010f090c03 74
    0x425020000d16403440100801d002c1c01804407896490400c019042c94502c1030200860414800b1001110544942410303a000200350010b24040c040c0d0848103100c19101030a621562803403280301681e29542441da204d48540d004064450030160050014514010603410381ea0602051000c21900480c100c02900d000391800100c15100900341155a04210310003070b00300c468a80701000b488043d40050412100590711210102c030b0b6403a54004840c40c4a81003843c40d0030050050309440e01c503a000350f0f00494000e01c03000300c01c036a1080c50300e14900c20701454240c007540045d0825809401100803407540e031090030201d4048020070349464541900a1008041d283c000e806542c1c0c569803641520f0316002d0041069a4516064600c21300414111544a04c60320441c64200100c109002c02ca41c40001c0248d90150541c0720903205440b402c001030000ca070310030700c00030012030356071024071510305510140c2102c04044040c6005244c00c4401d00031012400c41d0508001c440454505000e40c421603a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 201597598 1250 201596348 201596377
    0x12031608070f06140a0501050307030b04060b0105040b0a050c1b090712150e0433050c0d0f0b1207080309060c03070b0f040b010816090c031103180606040b06 69
    0x2401032818029040e10050001c0c2680e11344420112694001c004072441a88444001c01551741c07110300f01980d68110340300c010485503e10000a0000d00260400300006c5418100b02e810551600e0b0b40003029000b021200380055800301701005441002c21150026181c5404a000c902c8503100101b1a850341c002d02e18010300025402084805071203601105035044040d140005564a4002c00c90300e51405075000e44515880e800403240700c5001500901c00404100c8115103150010661000503110040400890071014000126100b1140c01040c2d50301c4100b02c000940c00081e44104032103010484000c80d0203a0110b4010b00400a00008a40b241c04007150050703120072007031034106e185101e031480050154405d90244400144100302c1c0e07901a911810030717101c1585e00c480d196603485000c9001200d4001ca035400411602d400c65201c00000106460041041c801c4000359070400d43c002c2d03503203020110224034882c00c01a4103000d04d9400c004112024000c40c41d0141c00616a80221b0488802d030f40d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 201598848 1250 201597598 201597607
    0x5070201020c0a0b040815101203050c0109080c010e070503120702040f0c0f1d010e090c07050f0606030c04050405030d0b12070e0f070e0312030714030a0b12031608 72
    0x168000c1152800d0410000c104050f195102d0903a07101681061052480b175108a008141d80202140d00745032141d0750495018900b90315055124007050055541a401d00400708082c802014081c05042200b0340280d010594418802648900316480b56a84800540040100344403540d4041450754040e1070b1454013a0703c851840c000107005104444030000040c1c603043d68003501e01d07000000100000d10a0311601344000781044d07900103c0c41002803450000b0006013403403640349000c200e0b583e00043d514190074141603c5940c3c0c40c1c604a030000300c0342800c2e8484e00800044d49002c0100303505807802501e003486542841d5680ca03a59010740301320802002d494030302d034008a40f11351403200c481e810044100c5e0301003603681030712207540c00b01518035074007007004600090303030381c1d0b000741102c0f200711801030000c0c866103502e21840340d4039400141401b010000500d40203015100984080d40c019004403000282c800c082c0c81c00c01c40044485884840c517504103011000680c4069001d248500360000e4045549 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 201600098 1250 201598848 201598853
    0x31e0c06170412020c060705060105010305060108040f02130b0d050a02100203040f090c021507030c08010e04020609090403030f090804080d0206090d0e0102010605090a14010b1801030b030c2d0406150507 89
    0x52417071035032400b03170407140100f0000140400001e40d07a04130341c4280c0b0100103c0d01d681d401190818000c4502401c0f0003440d4030140c00504000700090707001d0040c2070000590f40078000000300d08065030042074801d036100360b0502d0107510341144511000c11140c00250b282615201e500800e171040f074420341e081d9517602d090803a40c80740280911800e40c20402091344403450026405002000342113071010004039048000301d0582e46940d0359502890300101300c1801d080017142002403400b001070080301059200d121700045403041d401000441c0d4490315440e5190350400d40b01034075281c3d580d100c0c502194441c20a00800c044040380c2c80003c20128500300c801c5000c00d80050780580f200e41e2002d070f040703c540010858003800c1c907400b11280d03a40c04040310b541640e0310344100f41c260249901d8083c0803402849407600d298020307070001b1440300014054800322201c160000340c171480040c070405800c002030b02c6140c000b6840c1c40711219a411040302c04021681c108680301840c821b107030708a201802000207000d0706 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 201601348 1250 201600098 201600103
    0x2030304090606020312070e06030103110d060c050c060c0a0c021504180c12090305090616051203090f01110901140c16180515040b0a031e0c0617041202 67
    0x6020302078000d116203503903058001d55136801080043d20a414010204043c00e200d20040386001781d00411a078250307421600c6841c8518081e01304ca550250041c0361034000101c2500a2421121054036019100c000d260481401e154000f411510555000c02c00c0c0c0000c290040c132603080003030f01654202200c0071601c081480a21031078002080c2a00700050000040c103e54001d40810901d075620152030034086906403040da45e26010080226006215038441400c050000e40000e106034060541000035645459003403580c611084115440008200141e8403420005440103142c0d000081224401060240c14180105401d4034100101c1030405070b43d02a000f03058494200002c0f084c2c80040f072a101854602140310300c980c00c01e5100181c0031a801d018688201c81c8110450f903403104500103060100002402410b04850384103000400c08404034000e240302510002e520985282c0c02c0c1c106080c800604905e42e4071410802600d0041c0400040c02c90880b5500700343d10140702c848214610006270b0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 201602598 1250 201601348 201601357
    0xe130207030219050a140607140306010e120604030305011505070206030c25061109090414190803010504110403050c091b070f0c050102010c050a050702030a0212010f14060307030f020303 82
    0x4100c10881c45503c00380400800c820b40414030450300c4031240d4502c113a09548a807000c0b100c02005c03410100420343c01407101001507600040502d030400c0d201002d0390025042c0e0b402d6000810150f84a40308000425806110321809441900e80c0300c00d44140c03070b0100404a204d00310b13002740221030110100d0341500c2401c0c180e40c10242d17a10880340c10000e251508c548100c458000a44246081503400052480c081c01251408400038141404564580e00c1300b1f440241c14405a440c2882614854140b04000da032651051a204403445a41ca5142c5801c200c25181c0b111550b5244510070041040000d10001382e40c40c10f04000ea031070b104503a55a50515004500040455514031000602007040141d000320b50b542045c401d1501c00c4c2c40c1c5440c0d90049088892002c882c002181c01080101d1041d0b00900c0030b0440284010211044080158045541030351035403000d01c00c683d1146c0c61100d51021301d0080745100056090904864945400003903603030310302440b000d4500b1103001c402c0380a5490901c00c07134 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 201603848 1250 201602598 201602623
    0x15022b0c020a0b070605060406050f010809030403080a0903060b010215040f0c0b03010801020703030f0608190512040f1811091905090426030c0d0506011803030207150e1302070302 79
    0x1e400d580c1e54000c990f1180e4042c07070003190101d180c8070000f1407a00e024030800054070006001c41d02680c0c0550b0054900410180100300c540c8814040000010141001003804250707587d1400d01440c5540750100c142e50020801038159048407000701001110780c03208a07801604200b900c0100c4205040a4400b00e110780c11807140e03560b0000004c5078003281500100103040c42903400304101c0d0103034014801111b4450050200940001d1840401da0382e48480082c1207030301540c1903d2280402200d055820b07402940304440c0c43e40310181c20400ea86004007241d004008010040c07048203101061050305200e1400500d2040c4851203155424042460319000a0080600f01801c1c5003480d085c1044d0703162250081c209500d8040250850b40d21010098078052803040030250b090002d4205407002500005006504004000304e6a154446125581c2401540a60050a40f42e402c1444102110100140c1d0800b801040300d030465003a180d0f1700340954240042040161640d010f031904031305250101105 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 201605098 1250 201603848 201603859
    0x3041a0106030618050c040302041e0501030b0a0e0309150a03180b04020a050a06140304030c1208090c03010b130203090304031407150e100e13060e0115022b0c02 71
    0x2080300358141d802901a14880040c0070501d81046102c003045d15030890744040c41d00400d100130801400c1c81c3c0c0040384003092191005845890584190007141c0c03090b40103465035101c032410f100030b0440e02e202e0f58107150b1030b940c0a507260804200110b482540440110b080d02240019510b04840c0310303a02005100821608040e40407100f41052010400203032020f03403060b0008800040e8901e030042c1031f0405c4500380d0301d030805d40490225411301ca5410081055007406041a22880014a03803000c1032a1001c1588a00c102c03801c209500da864100c0c1d10400c1d0b4081e030b01d84010810155a10000b1660001320b00c0000359484e6100c1a5142c298040c1d58002056484a542c117000c0c91000400c4250940d0000e92990f661303c140a10100c1d10200480442908030744104e24441000341720b04803c03c1100000340c101401030200c4034009040383c03503590103100108209001804602c515003a88a1040101c0c0f000b402002c04040520302c4000b403414036550810308111212500c140210707103000060342c00800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 201606348 1250 201605098 201605101
    0x10e0103110c0c041515081902030708091c17040c09020c07240e100903021e1206070207061d061b210301060e031203091612030509010503041a 63
    0x80725980c5100441c40e80c4130b6820000041c200c401e40c0c1c1d070303542c003150007010180181d000030080c140d40d001809000001e6541c000441d02400d1091800258000e40c0d01d6a83e07101c55251440700355080851103002d885500c03504000c03401c0312651017090810501801481d496113a151031174625502d180e540d11a2003a140049171940c003500b000f141d010212000440e1079071140750a540d1415000340344000500201d008521540704900340500c503080d0071500740c1001100c40c0c0c0c0340e800007500c3c260202200d0100d81b400424015450030843c0091000c41030110040406003050f0700040d440d4030450280d44104030002d000da61a44400c1e180704000300101400281c1e0750024461500307003504280041c28401c3c410403007071035814250003c80c410b8205003210001c0c11039003015022107007025040b503c00e0f45845040c04003e45540b054000394000c2007281d00610441c0000000f840d0600030b241e00c080816111080e08102080e00003044030048102460080c0d661713540ca04c0d0000051407800c0501070013011080 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 201607598 1250 201606348 201606367
    0x5090303011806080a1104090204061701110711010f1b030201050a060816030201030507090f0f08060f091c050408030c070905090d0e09070509090709051e010e010e010311 75
    0x40154181d4000030442c01d1418080da0700e440c10745020b8440d010050b482283c0f00004594400c8152070010300080000c500001281c0020341590102d4028103a00c080c4a000d015000c8400d00c17601d80c9180c5c0070808582081c2c0b446d03c03010701d80500e0300601410704c130001001e054a44d00c80e0f6643e0400c155030120001190f1319904009000746812251145401e24103c40440c6d44038002031403d900f6036102d070150180505660045001e440043e00800c1800440040403400300384190120002d031203901012217101e85088a91441c1c614040c009080d5110208184080b03644049482180402640b210300003959007c0340885091280b640088294000403440004d1808003061841c100c5d910750000b0300c855120094441e4a43c0003020b18030000c100342e480c989a40e8102113156640c414880e00300181000b04403004500c40e49012030b103540020709070417014001031a1a0311161102e07500c0c1070b8203401d4000c02900180c0750b0350381d21102a0505c00c0145102040340c2c4030ba0007500c0101e05107412030b0707100c90500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 201608848 1250 201607598 201607603
    0x1050d24090b0f182809030e15030408070809010207030f0605070206010602060903040608150a0312030501060305100509040f140109021c030e0d0c03050714040f0b060307050a050702040509 83
    0x1912103d10400d00b02a40c480035240c261400414914203c00300700c0e8603101c1c000e02100411500200c00140128041c41c24800e1000e40301d80c0199a000b5111801c04030900001c21400f010400503101c0805000c0c0203000207e084041070f0781c4c0c925480224640d96482c5140142d03c0c04400368002007404040c050f89104104d82d0340c10281c02100305808030b940380e17602c488069841d11011150380c01190300c14801000180c3c8507000080c3c2000341e510040ca000803038440030a103d03041c0c2d60000e5621554010b4a800d5465041c07042600400301460204a907080c42d1810142c618458466144514200008602403296410a4040d0942d00884900c400300e03610034141d011300040c440c1a072103003500752200c0da4407241c201c0300c106d055645a07070390400d04107129041210303102c01c9907000c0da40405200c00100008030108499030240070751180c460514141c0804110603030f0f034000e580d02d004030700301611103005807140c6003500d401011a090180e16104072507001c0300c8034051104080d40c001d080900f0300c50040c101 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 201610098 1250 201608848 201608861
    0xc0c081b0d0c05010c03091e020a180212010807050a03030c060f06030c050102100b06040312050d090506060f18010303030b010e150301080d0206090a020d022701080d0e01050d2409 79
    0x48009005c04542640154200c510b212001b0300700e4503d05001000100310035094000f11407008240c000d81c070782c503601c040019803502003940740c115500142000078171200e81d120600510114004081a030300386408500590700d24880101070020210704001000b00c50781108080800682042048070f44d00c1c03c01d01170f030f941e0a21400b4090301600751302c0c6605100c640156400f81074080c204624251842d51441a6001a4504001089814001c4060120a500840c00c0d681d01900042a00303051000402001038906503c1a1083c00c440300302c01c1608154100c483c0c1141d4060400041c0c0b1000000181d0f4000f0480c04029804120480350402400d0307140c02560680340c5d15004c03540082c48080060b83d07511010b0b90481800d0340010246001403404c00b010f9000d42e8030191041166040d030b40c01c004070804a0640881d0156400001401600e800700b00041c259087c9107400046043c0d200300181c4644517014141d004291905401c8068869035600320300004940700300a41800c4c1d48035441c03401040c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 201611348 1250 201610098 201610103
    0x402160204061d0606070303090203060411040b0f10030c0504050a0611010b010c020315040602070b07030504050c0303040b0a031a100504060311090a06030203060a15120f0c0c081b0d0c 81
    0x7820b800810407043d04801c2c1c0000141521031040180c840c00d081114940013080120708050300c47c0c918800585042c0f240703030b024500c21050a865100d03010104000e449400c5840380c025150420004000d1b95100c60000b0b41c06c429040014102c012079200321420b20440d00000e4100e40ca0850010311168445104030f104040c440080081030598001111031300f414000207541a0b000800786000d0890003401f5603041842120f006140c00340d140c0c1c030003000d10f8048074007202003960f41040100f406001e000d5010304020460207185030508102700528140180313420b00b010565107004040e90319600040b14099031100409940c088a40002d004140da400b500442c40041e00b000c6200000840b0031042d15400030000701154417080c103140084001b904001c1c0407550022811500040b2183d06c5e40201e40800120b4ae01e5807420f00340000385030240ca0b184052040e5841c40c00c13104507400c5912041d95440181d000404a035981064002492540c40c1300712851068040d0070305003140c0a810600402e038191 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 201612598 1250 201611348 201611351
    0x90c1e05060405010e060a0207030c030c030201020613150e1f02040503120702090402010305190903030c1107082d07120c05031506060d09060609050a0b0306010305031909050402160204 81
    0x20388500c00d11030940624420303280801c55603014910700d4500040030303207402900c2d481140c0c2219929103526802c0b05607075106941c101c04400c01031007035503414070409074401180f10780d800c81c5502c55969400d0841003c858025150341d01d1541d4040034005004407450345221031076040d01700700207182190003540300d4840c442c843e208440e0b03106105103d5a0035165400d0f0001c21941c039564807900190040d0100400420b44200e42ea541c40318220101e101358900b0b00c0c0260340000d0100010040900743c1001c10031240b03519402041c040061500000d1340b140309015400d01071407050414048051610b0440080724514040c00c00d020807485200301103002c80602070140b03148031665500c14552a40c940658000300b0003a12000030303206081071401069108614400003558040b02d841c3d42040f10340b25004401d0507601d510601500014078090703c011140304501404c1154910313641c0e0382e924810260042d04081540c10398080050144ac0c50070001d2101410655131004c01c8000510030b16580d003401ca200c3d9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 201613848 1250 201612598 201612659
    0x70506180607120b01030b060a0e010801060c05121b060708040507120b0a09020105090301060806040b0a0c0503010603050a06050d050604020922080702030f0a0f0b09010b061c090c 79
    0x40c140061558061109600c0f03c50300300100c68008000b03021000409818152950559812625200300034105402c040d41c0d80c1000b810581c000500300107060b8040c20410549607481d0002c1140803c0c94030f0742680f40c0d01700b9503071040003078100c1e0441243d10300345030680d020b0a42081851174100e800e85200d580300d001551842a2111046081c0f038440c100003400c0c03010681d0000e10014550351240c0f1440b0b005041c92420001c0c1640041d00b56100d54002d101181c008906010070088042101d54112481d10403c1c0500310b02400b0062081c041403041404150722031020450000141d841403002e040e019001051940890504d035985403002d45049001702000c800049041da00c01c11407015607550803174001655a019101da01050300f007402d0980c0d01d401910a6150312501c10860a690300b442000720b890580c0a6040000c000d000c0146a004180d051501500150391070404442c05940740446008500c900540c4800c01000c40c0a030007462220f03940f1000c110b02900d50400c0496821200080f40403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 201615098 1250 201613848 201613891
    0x1510030f0b0a0c0507033c1d0307060c03050a030204050301020f07030e030d0905060903030c01050f010312030b0603180f0d0806100c17071502040303051803010209130e070506070506 80
    0x46105e000c0020b400034500318522140302601516100302e0030008581c80040c2000c00301000110b110307a01c40c14010580b103240903800144030103003611400c203040780609241e600c0e081c4080c0403440c0c8804003c041000001e89244428003c0c0d06031030240401800031500d590901078220019070100c1801e034081006820700c40e8003850f0000340492182101d030b4170400c80078946414404650022030400e580350006001ca1040903609115403441071480b21210801ca501d103081c24084042d14442d440101810031480d43ca2985400088030340101802c0320106220b03510310080d07802d04081244090840c007400c202002d00780c0d440a402c9008100c21941442c08840c20303d019583c41d03442c0d0030010111480d00601b4184031462401810049014035060b1504400d4401d51004230785c03040d0400ca000c40c00110f14207a0308459200803818059041d8000c40c1b4090003a00029074841c064101403281540b45c0001c2554400d050000d103008100103002c2c42d48400301e910f0404d8480784100c0d901c400c80c80188410284 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 201616348 1250 201615098 201615107
    0xf0b0717061e13050406090209010503120a0f050d0c08010f1e05090a0603050601080303010e010e13020f13020a03021b0a1e1b06030509010605030303091510030f0b0a0c 74
    0x940700003000e41c0e0005840366400e00d4038061980300c081c0e110040120344040c29040d0302480d0b20441c424400002c1c8912144100590000181c0116000303511010074030711140054400c689087c0130320304004c0c1d40010101d42c11542c170f20402000050141c1024402030b2215088003040c1c1c140d40658039100c0c0510344508070074401c2d0040d0b00c2120000309031405c0c02c01060030401c00c000d402500000340481c0c4181c50b9202c50385046801c0e44107c07000e501c0000100032890440f600140580000f00c031043c0700d4104900b290360024190709011b07202d6402056110324541d505100c102c2d0381c03162a0810b41d160010710301c002d8002e400c072109403803000d4803c5400c55140ca00124085150641c042032264100189008088150141c0c0400b203079183d108160348400704249401c010300804150740c0206842c80c00382e14180c251000c40e800540294818400d0102c04200810706202c41044482d4142d06036a4203052249001e026178005414000550349210911001904907441040020030074070a000341b01d041242c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 201617598 1250 201616348 201616351
    0xb1f180e0c0619030911030601081005160903080c1005010f06020f0102070507060c14010614011107050a0501031a0d05030c07120b1303050d0f0203150105031b030709030f0b0717 78
    0x60a685414410f480300c1400313036000c0710b07485010320031341d440418100011a2808000782c004008aa001ea00410251803290042e03550101c08903284a600c2d49500304040c10900c45408018480b035000702d038450300300790100403220401d00b00d003074240301950b903c11501028050034003440005010365a5400520311050080715282ca034808010010765140c0001140c000c04c0040d012245000410300820240209000300d401500031448443c07149240c580015100000d0b03078007a02d15681106034100103070303a1080354441c200e6a0a090118212140e01d1540300d400001000c05a40152090010f0040c001c000001e0444100400d04444116841c0cac90455102c0da40218014940700308403000901d6115115080642c2c0e500c2428054100a50040300d501551000301401c4415a0f020080180024000e00b01107820403003030078001c0c65418244001d804080c00a446000c0c50340002012a1500d84540522801503400410018140b401843d0086104109032071b0100003c1d882481400003800e07038100d09 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 201618705 1107 201617598 201617617
    0xa08060103030801062d08090102090415030302070b0f0901051c0216020a0f0302010813020a080d110c090c16030207260105010608040b1f180e0c06 65
    0x10031032550b00d54011595504075060012010300c0319070000d100074442c602107c1a41d82c9040d00d501a2044444007030b0002d18155120170040031b003050280903a8444d600f070300e5500740e55016041e802c0c01403000c0c1c3e99660303d013003010030510b40c02107004104c0b01c0106c1301c2003d200d500c040500380480c0c114800700c41b610008440c5c0030003149081000d980c00340010036a040e10b59411900000d08c4100024041d0400301d440d034910301d00f0b541d201d065074001054410120b80c0e40b900302c01030003869281c50f41840d001600c41d2a83c081c4039441c0204146124801048606080150040f0325819105170103009400758007440201040e00640400c81003c800d0310410302940032069200700ba421507005900c0142040003481c05d200006440c44c80711a00110840680740340d4880a2182c0d00010440c2d41c8100110051044025032910068100101009005003a039452004a0060290302d11820502 = true := by decide +kernel

theorem cover : BRFrame.Cov 201438848 201618705 := by
  have h0 := BRFrame.cov_init 201438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 201438848 ≤ n) (h2 : n < 201618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
