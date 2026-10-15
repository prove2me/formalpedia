-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4418
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:33:16.942551+00:00
-- url     : https://prove2.me/submissions/ce506c54-ad42-47ac-8007-3d562af59677

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 794424460 ≤ n < 794604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 794425710 1250 794424460 794424469
    0x2040b0a05040c120509190314040f0b0c06090d05180120071e030f081b10061a281e180603020a02071413020711040501050a0e06 57
    0x4104150040c04001900c1da11004501038521503883c580101d180072140c1829280306000340c1d58001c00c120f01610342c01d5000d09407a410702c0344071400501004003d11303d86e1840148001103401030800ca84c07500d041c0d5070b0344181c03000c02940241c04c401042e0240001207880c0213400141e03e0020099900c81d40d09002410f0482c0015065112007a03040200380011804082c01c0d9107285589012000b0181000a01313080004103405101d0515880c418445803007040450301989558100d16442481c45035503401c004180344520a049096154a01070400c9a08094245901800407605005609118ad0740709092920050240d0921020200784509050710f03100500465641109220b041c040340c041c1c0540c03001d8907080401c45104000c104020381001180740d08018040041c19103290640c603102c400300f0003c0d122000e521800030303c0c1681c2414002c555694040c0301082058407a0119110801821b08031244202410528000d0f07180000205060402c10500019180300801000e0710342c81d03440610 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 794426960 1250 794425710 794425721
    0x3070e0f01050a291312150e06010e0f15030d020d020706020a021c050a08041715061e03030910090e010b0405010207031e0b0f18030405240f04170d0201180204 70
    0x1040c4005c3d040101064250085d80c65111042c0030740960100034140060a0040360b401110003580c0d603212900400550807240c2b85554050418040d8140c61348503c3c0d6041521a080701060f40c2c1070041032084021650300092403190800f00754200c0d0b03103040e56540d040c0c1e21000c1c40701c0302030b400c281d9000c0000c468420480c00301d40882c1c40b0f1000c43d4081c0105860700e40c40354003d078000308000d803c141c5041c280e44408000410844180028030340482c02c02c0c0c00003030004a48001d01000140c840344107505c0030fa8090041d0340ca486009044c4041c11400d07000c0c020141da08601039618a00f04a40002c210300c00700001343e40c03d854041c2c0007404001d00b161151080b50301020301c02e800081ca41c03080400002c3c0b10f40c140c0c6028184004401d100e5003400000c076205907201d90b0019800c0c0d41305010400807941c69113055212003640100c90f13141102400c1d00d0b03501c01e1041c40c008004400c1d00250001e0050107030a450180d0622101c16910080e03660074049003a00c609240341e06220b100441c04c40050315043d8401c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 794428210 1250 794426960 794426977
    0x150614030a081c09140f0102090901050415182c060c030c0c03130608150f0d0204020c010603050c10020a05101107060e010518010905060403080603070e0f01050a29 72
    0xa011140c1003c040364415a946502d080ba5000150f410414800310100a03000201103860001e6090104140204000c403134144106031055840b80b0300c8026082800d0360041c007400d00714004c84d800d0150348840002402d540c007040400130801d81c0a010100c19900e03050a2460000300142c011a141d50304159020f0b0005000000c1e461004c10038000c0e0780c4030800003041030000920340341081c81e1400304090700ca040010420050b41e80c03902031085241d0740f01c0e0803501604504580301e540c41e02850000c90f0081c02040300032062907282480100904c0307030000701940103030310840d20311180041842040341c035882032010050280c1e02c8240107241075403007078002070080c8401e030282c0c1d802e001da2501e84509982c03008401c1c0203965562001d002c40720f0000850000c01900810091100518641d80e032651044000d0002d004c1240756408510240d40503c043e034000d05007082c6201003820000508102c0f4102881014410700d045600000d0401ca00031824103501c2c9401005a80c0402c000d0920459600c00c445 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 794429460 1250 794428210 794428237
    0x3011508180a1505090307032c0904140d0c0c090522061b050c03040506031b03040c06350907090c030902040f11070f0602070807150614030a08 63
    0x78407403018182000740b4040340d8000c6182e000c03449140c140d14022035070003501c2d071006600200441c002003900007100a0a025402c401c2e210f06101d40481c0040580d142c003081907100d0001401d000034001c070b2003400404001600140c440308809030302d041d9200e54490500030810b0042c000c04204110b4594080c0d64480003040004556920744545048803c2d040d450854040d1307640d0031446030880d00b500c5111004c0b8a90705001c1d20b440102840c1e141c2e20b000301d1107406c0c400c540010002c0c070361100740740e982440c240c50401465102d040c503141c8000816128010000020503010900c41d120345912040c00c054035240308140000b4480d9078818002d0f07807004101e2140e92080c0c29000807503c145210b0126007102076500065190041c0c0304100c1901d00452011088900305150305201c04940f00c00c50f1802503020b61907030200e00c21484c0090281c0650940a817001201003640b00a018004e0105a5182c040400801c1801d13200c00190071600f10160a0603050390184c0c05ca040000c00d040000c2410442c00030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 794430710 1250 794429460 794429491
    0x203100c020312060616061a040c0207030b2212110601080a020a090e06070c110a0b0a030506091006142206090f180902040f090602031b03011508 64
    0x8104006944268000500607807001504840700c4403403189640d08610101c2d1080d00d441c00a09203181126207041020b40050f98501c064003186040003e00c03499208060014801444d190501a403266418401030314106500b50006203100441102c4900c0d0a0303840a01020b2806561180da081c1500d03c2c100344140695204602c04620040007624001c10840000f811880018810300220790403540c0290f034160308180408103803001c0480c1091780075110b8900300b00c00c0009800d1041040c905c150350b03030750030580341c14000c140c4030700720801800c40c503080341c85c1880591100c00911200000c112000862181c09440520142d407060380500e07500c0d4020340c006130030220542903d0001d03006c078410b810b07558010040c04002950b04940c02a00411604080504041c03502e900d01e0b5010180c0c15018550f00d80c2c501180d411542d80b64020130200381a01410022000c0b1807402c18002e61098420303014030890a4030080701106010126410b070740c081d000c1040e081c3c40702c45050310b03c000c001e4000708a103540e90 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 794431960 1250 794430710 794430733
    0x20a03030203151e13140f06030a080a03022703100c030e060a0204081218060a0c211211120405070e090a06061203051b030910030e01050c0702011b0203 67
    0x902d58100132030b985241e2040f4203800304003040580e8011218084c07142d414648008940d2845c0883ca40c0c0c000200c0c03070002004c1c1e03140c074000380c105403500600600c882c40104070800182d906902401c61103480c414060b0003411601c0c151460061a03540095060380180318080212403180c2090310301c05801d06002c1a60602c5445107820200e040b101040116800316080200310f41c1006480b0b401a0402d141c203281003088842a007061008510b507a009120018902462501c240e04403004540c11030308040708545000c00030031a8034a080c8114002900090040000d11020312134504032001c6044020711f00b10059141d860450802042611035005820b00001c4403c0c1407400e0360711803030400c1c001c1c099004007032070050101c1c2c4e032a82090000e02d04601d80791000a030000c0481c2c40200104214500c10541140b101e8a54840c070b80b0b0040e080005089554001348c1c06400140103150580b00a0249035100210a011f0380650700d006400280600348100741d440d90203413120002c500260945440d000312 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 794433210 1250 794431960 794431969
    0x61d03070609020414010302090708090c0d05011406090106050a11100e06071106101205250305250b0c030f040303050903060f0124020109150501150f020a0303020315 73
    0x1185041d90341c0c64441401c5421440d09104090200880c414111030550458002c130f03212144c001e04000c2030100d103000ac00d2000320300300714140e017004005190005800b01c0d803400034060070400081e100c04020307038004280c041c82c1c10307540b160584017140d440a08000d150369007180c2181d010040315409010b884131501110840d800b410080d40d44c0c5900404180c10801c0d030090400b0320701d5040c0d889030f07042142408400d9207604d46440869414580c00c81d140354580c1040390030030b105e03401080f9010034050007400d69850220500011240036009981c039595449aa000e0403081140e01c1e04401c194200c8280180c00c10b80001c0e021105495044a08101c503110340c2c0c642035403040d00160085070010540c10264502000000c1c0c2c02201d0075440d11855141c00040f41903022070b8036007044400050744190303040900c00d510150005400c450a03100d0981c0c3d61507910001d150a01502509002c0d061502d01014015800d425004406a0040184801a4030110001e40003e0640b4010804407020304607103503038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 794434460 1250 794433210 794433217
    0xa0c0212061e1b0a0807030e010e06011806080a1209080303070e0a050402091e030f1e0d110303040611121806090118260f030609010501080112061d03 66
    0x101c900c640e0000c0480b5034060a100d07080100994220140080c070384100c040414207480702420181081002d0b5200e03400d003540985001c40441d08258a0304070180c1c0340c102d000503194101c80803c90643d03c020f00303c107105c20940d10a80294045944142c4000d4001150b1030030000801030700e454501a82c9480e600303050f00310b92040d1110702c0080c0c142202202146409820b103001420101d40841c501034090011941041040a26640c81121484503e1142c1c40c1400741040b211460b9061380e500a0000c09052442005144081c0c1248144808586003500521401d00d031001c001e0011806d503a0b8542e1204043d18003144012900c134414402d02e203080c1164980b09004500d007400103680c054072030301c001d440c0160081244000c0d80c10714001c00f007020040c4020315455500400c0016050b075811a0800d0134580c0c4211001f14010700240d4188011200809503008000864000d451070b40ea03840110b0703407e0820702643e90700c0e090003907070f84001030b400c0d90240c41002d4034078000007120078488140500b140c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 794435710 1250 794434460 794434471
    0x14010e130915020304051b1906021509031e03060406090e030a030f0216170c061315020a0516060b0a0602150906040f02060d0204050603130308060906060a0c021206 72
    0x546881d625410002900c14400d03240144000442c15071800f40c840703e03641c00341c5107004210804032403001800d9445004041c041c0744682034411407102e5071401c00035603030006041c82d4a4100016808240d41480220403036100d802895402009014800d055081980c0050105a809941c4400006407042c85000721450544240050364480210360400b4042d28500980e041c280c038030400003440c00914107006000c00c5d540040400008141c2c3d2507009207140b181408a511030300c40c100800200c4501d80420400c0d0340c2c4115240c10b00c1c6a04505584164002c4410020100e18240410b11041520f0407060520720b001d01e2021841c544c2d28404544880690780040005070803001d1403500300d40411a0407500a509440101285e180a4484607400c4841c103000900c1010001050014010260180c80203030038000e014981ea810103e20042e001401c2450450200d0301650000f80985441d01c1420b21801c5c01a01080c50800200701c100c1e820318402070b080b40c0c0410040c4004070403002c10091280b044 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 794436960 1250 794435710 794435749
    0x513080a0b0a050601110d0f231b0318040209031f0b041d070501180906080312162001090f0c0501090b07050d0f110a11190f14010e 58
    0x14180b8034003450a030b44005110343d0602902c02c00300701e0300940016401160128914003020707482406e140884001c608020a452300400401b00300110390761000c0144400a01494682c0e560039000c0007040c1c482c09081c82004150b0054082802e541c1040c1d0028a41d291000b000c6c2d50026400c42440d241900240342072202850382e034508981c030b80c1003620a10401e40e041c481403038415612401c500e40d40b014140100d904105087d01c00c1c003001698411490701420300d03242c0c240311554860f04600d0f0380b07070000e03006100c03421030003004a0000c40031586c030180884803651341c0158088032840301d441520b0700403980b40312079940c078540440440c1890b4000c04005200f00c2c60402002d1a040005281c003059400254400c4c008107c80000908000b6000690912a052060b1540544407040d580901034030207210960040c4801c407000c00007001600c08074002d003201d1508071003102c0c1d050880d070341c0c0b614044e04940900940701404103076041d103100c085a000524120825100c0e080108420164421106891 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 794438210 1250 794436960 794436983
    0x50601060801050301140a2a0804030807110a02010f0e030d030504060b0f06071e020d051c2c06070c0807030c060302030c0403060e12041706061905010513080a 70
    0x540d91241078140100780c01c50080c4600c10031407148078038041e4040c000021040d030710265520612040f00705110742c0c808842a0080301c4c001c4040c094100c20044074100c000030101000074480c203004010079201560000c0013091540d01d50350055510100030941c1d002800400c44405511380d40421003c11300c0405944d004c101401d0904e8640f0544a4000c0154410303900422403e580f51030300d40954078003c0d00060040d01071600300442d00c03e0703103004900180d00300c0b5081c000b140911400042d1000c4c1031300300c420550190025010300b100e17581c0701e045010210140401c403c8010107800d155030b000e47c0100a041c0d030700d403007026510390b004482030398482c0503e6080034004000b44010503076240014a0582019860b51500d417007074608502c070b5800000e0490b0399607070020841c1c1c1c804200500031600710528143d81c03142c0f6584a40240c0d14540c814500600c1440c1c001a42401c281000c0c0b050010061102030403541800c00546098001c15030b00100a0000c0c00006450380c002c1000880c42805655100103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 794439460 1250 794438210 794438219
    0x30e12011b0e03060702150406020715020306090a0e060109020705010212150306010f05010801050607030c05060702010e07210611070c0e10061809020d0f15080c01080915040f020607050601 83
    0xa042c10091494070940000c0100000c5e0b43d00410070100001d10030009504c90303a070b6450100b000b40941c81c00a071984098107c00c01c400040e0764000e601443d03040343e10441d15680c151800c01910202c480724542078208100400000c40203801038804544a0700000d82800c000b544076a0500b841241c55026443d81740161601d2400c091007014054840107055030425400c0900103012904e041c803d05019540018072207041c10b110f07403040800e0351b50103016601c0908144c0c60080c0079121464100c200350091400000781c0c4a0252944042d885c00c446407185500001d44800c1c00400c42e420807003a00901c100958000503c00045e80f030050914000c00e010f240c101091080c2410245401117414071442e03140c0e41400b00802000c1c0c0d03045842000b80942c2d160410704101d000b5040c1d00104920581c28082c070a46007080804418064030303031074401c07141c1e4001c03128011191083c2c180d03111169070304a46102c145008111581590041c05003403100711501080d0b004c035000354060402501e40b40c204800500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 794440710 1250 794439460 794439467
    0x40b06040e030a0c0210030612200a061202030736050a05010507060c05210f1f0909020105120109050601030e0d02070b340302010b030a0f030e12011b 66
    0x380d203407071400540c140020a00041d10b00300031544081d20400f040402102c9080c4260800c40c060a101054601c40c60601c1c030b8020404c40c0d1843c0409010b10711540b000340c49003014204182140c2c500d0755001003907044030105100a40c0040d16510411030707400702c817081c580c29070601d10000e0011400c181030ad0300e4815000e043c2c01c2820341c00c0f003803040403013030380030090342e0b92000648828542111001480705441ca10a460350710a499204001c201e04130105142004506d001503c40c03002c0f080300e41140d5030344030800310649510b04894140c440b1034060a0000701000d5201040c0a441810300c80d03d0204290302e5000da044099000480041e12481001102d503807502035420f407280307000010601080051030103500e425081c0100740c040b4001140c1e0b41643d4010f0403600340c0a01880586020104211082d100d8040004109402540c2840c0c0d031880e40e800d0028511441c4c9400a56200c00b0b60455a000c840e0340803001f5141d07038070201c14803071080f42a100b80b04030244091000c83e4481c52140014025 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 794441960 1250 794440710 794440721
    0x7050108190510050901081b0f0114072402030702010c080405071401020705040c030b03190807030e01030b120d0f0206010f0e060114120a05010b070210050a050c06040b0604 76
    0x4a040194160501c5075400442080881401140ca400300d440d60b50011140d030362581641c01140c0c0104080c00001f03400c100443c0c1d14044803c040c0322048181c1c00e00c001d00000ca00891802e6000880307003403600581c000440054444284500304610320348100c02d036103800c042c4120b000c0112080c1c5c008280b2201d241c09215816021008d400d160720245015190381c0c0d143c64040c41501030800801341d010030b80d40e20030301071500075003c01401000498042a00180108401007005002e48030b07203084074070380b40d4088462b0110198000f05240ca06031003640d04a40312100001030300d042c10b44031202280e01b582c030070f1481c005d81d00d180d00081042c1a0f181c84c000740115001d100b044255080b03000180034680c41401c0703840c103403040c1602001c0c4a84bea40300486100c811007000b403040040c04508a104048076110031809856185424450340c1d0301c1c0c4404000c14400c0305030095104441c3c000d6141c4003809407004c0c048000050411318144441c800c041405c0c40000c8400302c0340003d10070700f0080549030a1045 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 794443210 1250 794441960 794441969
    0x30501050a2403020c0f030f03040516180906061214070b13120c05090438060910091a120309031b1f0c0309061805011d1c0507 56
    0x361140c0702c02c00d95852000d1644803010990000740e20110340108110002400030740340200c80d03807410489200e07c2550425a001c844038010184078482d20102e607006001500e01410300301074101106a42500281010765003211003680b9294000340c0509105003240f51240640400c10460700d444071001d0034494280c01c0805d5107007082c452010031041c2110070314190303100b140e0613035031018950800052030101a1300640d030081d160010401000507000b14a446404a8440c03049081222122150704078114010254591581400a845880e00883d49904051581c101000c1c081c1c45100d103a068500c0781d803100901c0140c2c0300030380780c00b03040018210400c2e1a40c00090f50031b005620f000a034603409120100400211808a00300c4a99154001001580801c01000c1c1d20a920f440d0098556491358000382c000c02c2c0440c10014110b4080d00215281503101800c4034032260400c8019101408000e40c600000ca5181d91105020b40b140600001e01d60ba0a0480d511400211b203801854961705820 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 794444460 1250 794443210 794443229
    0x611011b0e09070f050d0b1c0818060306060d050601091502010209092d150a170f120a0311040510031409010c0c0201050f12010f080d08060f2707030501050a 69
    0x3144c00c0143da220041e20084000710401107611070750340000507200c403202600f000300044002c105404000c1500010002301a020400a0f40d00814008002090204442c16600039204000304c020a0f2074961029500080504143c412651181080c101011152089802507940058072107464904940390907802400c0081400142c03404c01c866260007140e00000450140108001c60102c1021400304218042c000e4904211b2070b582d03030741c00d03100400389002d07003400381c040c621034010900d5010034000050351100d4500380c60850600d000300d00511903142c8418034420244808211681c84d03400b090303001002c564000c940107180030a404d80112000d0b00406044c1e142c007031007010154120107105540d80e02400c0c1507486815a86140c0001c0c421842c2138841c280304040040380c2c0f182201005800d860b44901162007000055034207a07034201c419500c4583c00319074007510007000c0c41d11090103401e060341401150780350324101c202107440100a40350600400d44500041c0180e0402412642c002c000d42074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 794445710 1250 794444460 794444477
    0x190501030510020a0903081c0506040e061b360102070f180e1006060206060105131203030905030f0406030c0507080a030b15071514010f0611011b0e0907 67
    0xc1c0c030140d466501000800c1d02c5074000c101e005005000300300050055422800705603840c2200400010380108901c81e2081c0c1d549000c02003629801d141c030502e054040540c00800d202e88030b00d45646a800e00051203607607002010008040c103c081040c1440c00b1011b070003000b00c04d034070700c0e0301c220407000c1c2c0440d02003811035000c241d0800c900da034203600c081c00301c403a1503540903503610201c80c00c0c00240002c1c403002115840f0b14180780c0c0002150390300c0801210982d60981d40c46803552001181c0038410586103044080001c4400e0091480c1024840c81c0e1a2081c180040ca00e1125a1024211b8201c00941481c00402150403c000341d05401400d003c90920302e06680750101694a1501c14000c440c41141015641c064641c8544c803040d81084189483c01c1c4041c0c1c031010316103051800702d000c0a40c0000c400d801e0007511800b065100404c24140c40042800b402d101c2e0a01d0000ca0340101c1450456a0942d200c0070280c6105c82040805400b010040d5242103180c42d85101384684000e024001b03200700040c06c0d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 794446960 1250 794445710 794445713
    0xb011107180914100b15040605091305160915090905090705090c13090c0504120807060501031203050702060f131b06050910050313080a11100519050103 67
    0x81003900540d03520148022680034103803074030030041c10b54a90090011080000b2030894000c0003070740d604014504801440009800402c2c4480c01600248600c8880d10070700050006074000c0014042d0700201511305030645c100003a00c04c1c252481034a06481a45a075901900030b254415411000340c99203a5501e41d114907038400040074800c4510842014594401c04100400e00901c90040181001007030389400d07050a0f108402c0380d07030005500a4a060280b480043c00c400c00c3e0150203a40c41d159181c9078205403400c410b0040c0440540c400716840b580401200000480510441d8081e43c021030b00c1c000381310504035005e0111180a0071a0095500a504016107042d0010131694012040918000005010703c0d00303050140c2030500405401071180b40100b0781940c400040c0c40c0b46002200c3c88000041400400d507014030083d5540c010110341004250041106c030001003902004614004800c1c0004000444c2450403096418103d00e8a4506111820401c810f445080e0455080c0030803039540356 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 794448210 1250 794446960 794446963
    0x3020607050a081302030f0a030908100b0306070c021c1527030e06210a110a020a0f080f030711010e1f0f15120b10060c1704090e0609010b0111 63
    0x1030141040d01d0294810720115101481000c7c00581b40504443c44503040d450007034030262440c060a9014450820001c101000c14000c01c034407a84090060701207916914004c55036140d40c0c80c000d98004403401100b822808800c20f0420b9454015001024000300c1100c4400130741d134840040200e090042854201d00090650180c60303c540d06040c4140000d4820012622600031080840c551188425202d0403100c2d940000a00c100b09441007001709070900c60b030381c0c0b0031806111682c2006920100107400018815202c0e03074066401041c5403828040c0303500404445510846601c00011041e08034040601003d00406001624001c00b400c41c2c15403010f01e014050510051035240b02d91034889085118007079078040b04c0300c0b0b020401048000340d211460400c840503008002c6540d4070007680001c4610104c110504140e40084d6100720145020b034868900305020800c0e4161030340010840041c0021180c8103817050145418050030061a00300002400c440740c480816040c44078860b00f5500d9201c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 794449460 1250 794448210 794448227
    0xc0118240c38010803030f04110409060614060c07062d0f0809010b0102030d0207020a0806040c06090605040f03020103020d0f051305010b030106080c010f0314180c120d23130303020607050a 83
    0x90390507d141441c2d44d6424400242c2e10003a01017a001486d081808090003401c1c0c1110044d1444030101003808484002481b11a11a180301c2c901c00da0040ca405103c0e180c45240c021204132101188002d040038208080300c403200440380d030040071407102040c0d81062500100080d9114080a0007005284074070710010f9120300c075049213490380c03039400221041150741c0e806588000e030100204172113440c40c0c24030b03000021500d94003070707640410780c11600000c62030700c0b540403681641c070300c030100040301c074955030056010b5081001848400750712410904642e4000388501e40c41500c510480403803140031400c0041c2111100c0052034080e90416400b03100144002689010744c80c002c1c6480726034944160300c01c400419605100540f221030b00c6042c004070008012408054880600031b60b0400341d03250003002030a54191030940400e40007028803000e014020628402c0b4080d101d0400800031404a12100706940481340907a41050401014820705904204095001696050507842c03c0380504002e0b11810 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 794450710 1250 794449460 794449471
    0x6060905090c0117150a09090305070201081302010f08040501200d0605040e0d140705060411010807080402010c080a020c060301170106060801180504060209120c0118240c3801080303 80
    0x1140080c0380021786c8800040f0f8000f000b440c042040205031a1400402030790083c4130581c001140c460104400018112999a265605031a803030ba00311004102a2800b10740148250340e01e56880ea014450901c01c8052401080040c000d4260317101c00da9055042180c201d038120f94040c51030148024001000042d241e0000b1166040c402d55120300360100c01d105109000c1d0045c054003403501444104460b14118210030502600e44400e00c7d620140119500da03012140a8009400e0720308402c041601007004080e4a54288140c03055a1445004941c15502c282c3c060304512024081b0f400d1100401c2c81844050030b4180703004500c03545003a45c01081354003440708400000c0e640300007060400000394102d424240d00501040a8500c034040c02580303400d0000640e90104485000410342c140b8101c07001400e80d0000010008419003840c0701400d0445604080c1080c003804c04c0c1800007282c00840daa0068200c0140d441146680301001c6400d400c6010080741c83c085a001d006010154000c400c2d0f81c4c3c1b01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 794451960 1250 794450710 794450731
    0x21b013c0902030a150603061109011e02070512060108100c2118150c02060c0d0b0406050306010e041a010f142404050a12080a0c0f06060905090c0117 66
    0x1002d000090600084c020003d10050802000401003804d40d080341c001c0340c3c003400b0b00704046400066210054402d40c0070f201d00145c61080c41c2c2003440075003001e8140c00010b9204442d2096115004102503d1900600b0b80302907210f800100604c160030028a03101c19004403040c4401d511410b0003800050b140002c008019044102c04a1182a2940090040b40ba100c508091984080c00c000d40800c21740c2603103501e65410822141521400019030b0b40c003c650070b54106240c01e0000d05c907a030003442c50b40c1409500c42e441e0b060000e00d99030704001c240d01a1995800030941070a052601c0d240d02040c205120040380f1000e40108103a1109103210412600141c540d03407400680b00000443c90301c003203510720313000c074409100750b11300a401100039006450090381d00007545600c803850703181020350201c0014544001003107a03404651085070300b880040d1150b8403009010301a0380d1100203490780c40d040b200801d66944200003842070100100380d0428000e0030f0000040200390350111034000000c120310001d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 794453210 1250 794451960 794451971
    0xa02060a031b2a0804050402070c030606030825030801050d1e03020d0f0201110f0a0c051203073e10060b0c060f100315021b013c 57
    0x29a000390403900a50310001099010310320031000c00f4005114000c1d540005102c1281500b41140c1c0c1d103508800100d400c500038030306040c507000030031002e5446503000700c5007054a00c0000002601074040d040156114480749500c4d00c1160b051401d4031510b48140d5070030480c10340c10840100390050075081c1561310a881e40c10040c541410804042c412408007008032209030400c150501d43d0200c0d400c0b420381e495540301d2001c030f00101310403401c3c2c400c1c001c03400d0302075034007080301042c413510117401044c2d00310a0381420010f19260b81c907800d0400d05034030b08604103250000100400c66070310604541d0000303008552140c90391020142c159044c24076013503070034080b65407110603e003003001000000300c01907070f840041c81169180c0c030468401c1d40044045d0009403041c0000f140c224002c1d2482a407180d070030800d040c0d150620710f88a006c0b031400c004840109451342000584e40c0f00f08100017072104030781c3c004000b14240341d1100c0b0703645c110792480c0000042c003466000b03180c80310000302c075103007c6403094080003066 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 794454460 1250 794453210 794453227
    0xf051c0c06050711031b0a3014070b0706050a0204080312100f081b0a08121c0203180f010b0f01030504020609060a081b04030c05061b070f0e180a0206 66
    0x1120380d140605a06108500c0c0c1c03984004200100003154190644518110365643c1c181c0250070504190960011541094008913a480b12061001003038000d1027800c610b1522404034505194a41d0810701d000344000441c40b042c0151030245a41103004452304603d007a140c0300d14191240101850000040c105101007841107d180f26008050f0840300d4180d41c0c0307540d030f07910a40d0399110780c1007110800000c0b4118840c15882d0100b5480201c6000c0c1c8040d105910f07800e5858882544020203251070902c0781c0003400302941041c03024512808100002c00b110700403d643c902d20308010818180d50a0b810840040415158178000114030182030038080b03416169440055928003500700c115800c410040b58501c18240d000c1155402402c41c3c1b010100c51840c00400c0c5003561195010180c032046000000304500e00b030403801030400641407900e100ca041c1800115a041440c664042034107060040300078468070000d00a03094018900e80c100584581032400710303948919441c0e60103846101c001c41c0501 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 794455710 1250 794454460 794454473
    0x103030c0f02040221100506070212100203010303030207061b090b0702060906070f5a080301081207050c090c0c0a050105040c050105030709050913020402040f051c0c060507 76
    0x5110340d4020001d54641072584145104200c11500341041c116200c408a06c094070481a04001d890700501054a421590740a01042e0000050001d407d0310400342c03419040b26641c40075501070361107950050b80c8c0b01180e040007015646610329140c6001806c402d108036482c2c121642104542040a94a403107040e540005001030007110303280f41c4c000700c002529104000000000c02d0180740705404e40c071180402c1c162038030071640e0041d500784120805014144451000c81d00310b84208454126240300034080803070302e0780f03801c401e0b0076044035001d1020005010407503003802101070b840ca41e0320340c09041030390544680d0b603224002032006000b500c0070070105210030080d600301da0603581d60400304c4124500a241ca40e00825080300c058400c2040308201141e103611500c00c882c0114074540c1c4000076103080408000340210003038011512400da1015400c01a11640080c1004081e150705005106103803405010009100706140300040c030740554002c0001e4500c8032410261030036485c040d070b2148854139212 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 794456960 1250 794455710 794455733
    0x21302120a050f0106050301120809120d110d1404210b090a030314040b0f090f011514030102040e0a110d0626010203060d0f0503191d0303030f0103030c 67
    0xd500303481980341041800c07000c50708110700070080c410083d0210780e603502c03044645020038050f21200b2042d1034003210200d25030f4005071400302801068042e44a0350a2101d9240104590990000c2020309505a031000018005100400c9803404d0190046060851082240c8114081c0401404941242c0c2815550704407030a04000d41c040d10a440d541000480141d441e259081d041780040d082c1201e132100380c8904117030340d401194071200102e0701d81c80e807800c0c008120000500600fa10311600258100084003409150320b400245000401c4450405d02d8811946c12403401082c0249e0040200b00022042280810f80c4104c404c800040e040302604e110030064407130482c1d0a003509092840110710070030106521103003911034040840a030419006894241c0c0011903600742c0c8003c01c5580003020814501428001c41e2240701039070300e401c0030f421214188942e24230485000a4488400c12140311f0203500041d02c881e0202c00950440c0307040c1da14030b404040140001000c02640c540c0140820105c01c020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 794458210 1250 794456960 794456977
    0x10917010f0603081206030d0801290d0c0e0603010f150c0213050708060d020907140909070e010809210912010623040e03040b090109031e0b07080601020604021302 72
    0x244140b541c2c078201404140c00000458003120012000315450745800102d2140c02000c40d15090741d540e1908002c65000307001c0082e02551420302e5400e00e142803403c0d800610b091346500c480007514480890008106501090034580550020401071180310659452201250b24986440c1c0100c1040c84084601c1e030a00c4400039000102e20703d5561391101181c110921458560341c07034001607a01c04040041030070501101941140e601004030f1003c5210b0311080604107001181c0758a0089200049218440c0440301e00380021181400d0520b03c0d07074407040982d00039402e50001c051003070460b40d03c0406086040341da03484000c00001d01c8402038480b0100035041d2080c840c0204042e42d544e0000368480d0102c2e80c118402c2190308207204141c0d01d05403041c80c1070f00b601040210b041c00d042c0b01d03104401e80e000355403940c10700c0401c00d40040002c042006003180700e403e00307142c0e402c40d441074a8002d201c8140541840305100c400307003c109051341c0c00504240e125404844040ca0402e049846100900c1007224 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 794459460 1250 794458210 794458241
    0x7051c0305011508040c03030e06070b0a050a0507081501031e0207051c020f070b03040c051e09160f18180e070503070b07080310211202070501091701 66
    0x10400541651295040f68194a858005500f00f09401c484007842200c008040248441c0d040c00428440d02c0391403c050800b030451403800380c02d034507820100c441c12901c22100d01d07220010002501014003803950031010b9401d080c643e50034403103141528102c4010415042558800181c2543c42d00c8a421101c0a2032011003151b440b441d90030235a8441c3c414404000c1403285001c1808201803000403100d00d4003c92002a142142c200100001268000303003041d203900b6244e00021070140da481e250081c903147c0442c0164040924802404009134000f4582c003182514201003280050300010089001d1035189081a5207562401c080789491101d90010b80e05052007280c07055031903040c0d902c059110404e900071124500c0e507810030160f480880c0d00030060140341c2800040300003a003240c095600403048541c4201c8540e1203a5180d0f217507001d56200f0302102b01c0c580e800c140034000c0b18003001e1000b03680ca2014000c1182405e0028001044c1841801140708035103062894184081d03009410700c480444 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 794460710 1250 794459460 794459503
    0x60309010203040c0b03011203030f0f020c030c06010608040b06062a0d020c090408091009030f120e102c0a170d0906120b01020307060f05180106030f06020705 70
    0x280018000d4008480440c0c802c2c84008001c6000020b00e01900c1c12111030903a144021405607400b01c001c0d1448580310844035807203d0f0107451500990014000840030340c0011a100c081d0448c0d07041c42c1103810b07800841030081d030100344400310391604400d82c0d01941c00d840240d612200302040c0000b0143da01301c5411020503075403070f055010070046644400d5000a500b00c0701c0c3c0030042c1c82001503220f401d0340d000f80128410402d901c0300b070902700780c400c10510752801d060610568a86036407104101c0a0b03021100180b008141202180d00942d141a03010000e450005840000d440c018240603200c00e003050680300c5071102c408403401c0d00c1c0341e0b402030010003810024204c2e03640c0b803510409611038200001240142c01c81010078900c1096420202e0300e580c4c5e20b03411005140402a0003c01960030510b0441c0030400000010074098054284480c1c4030081c005094030300070703081c60b5149401402c11006a41080420008030314419480f039415500511300507a11406468070501d03056045241400d05410740 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 794461960 1250 794460710 794460721
    0x1e05090706270f080c18040f021201020c030301170109030c0206180402040305030c06060907090b13080f07090f0c02070e062d2407140304170106081504080409090f020603 75
    0xc2000f0111614801203c1d0b6030520300c0d01b0400044030b400b1841140e020310f0000140419404040c010410b070000d400d00c0b6401c00c035140c4190030b90348000c0b600020b9500001c0100b200b648124000141c0491082c02000f01d9903403594002c000b120746c107001900c1070b60702203013101890050400d50444000000c104541d41c030b5580c03901c96140d409c0080240340c00d0241e5400076485007041c2004601c5030b50f8551b184c0100c281000240c200c0b0340c019071805440d0004178100442c98202c01c21a00c0e040075011001020220700e000c3c409015107641401c2001301500b0901c14203429600007803140c0503203419114113203541d91941c01090999a00318480f80900d0600a4650720b004040200b40a10b41016580e0416003a02e9080c098614181c1c03403003010300410200640401300381c01d81c40c00122030309080c1c180e03407802c6d039600c00078030b80030070549903030389103650f5030641000991010040320002281001c902041450141c0794000d1038042d0b0f11407010b0090719170342000c0811500414810700c19500505c8241c40741003d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 794463210 1250 794461960 794461979
    0xd0e040b06280509060703031a0604080f061008101107020405040b07090506040b1902150108070608010801060503030a140c030703090306050609091c0c151e0509070627 74
    0xc450710340c00145045908001c2043c40741c41110a03c2d0380161480c0d10340003d9580403001042006a002e0111050b03c000501c203513260740040000f8031031200181061090640014103014002e001d0b00b400078005d400c1000006404111380000e404000c40014060039006454080343c0325014000354418a0242000100518500000c0c0689140d50359448400d40768003d1140c0340c45030b4050000c00380410f201600081e4062503844800c85118415103c094181c3c00302e00119444c01e03004910542c1240400740030703142d80101070f00c1c0101000d000078050140307801c2c0803a46903c170b01018041040301c80b40322000b8521182c8110358000c131140c4110780c1d56107214207000349007141ca8041268602e00384400720f101894211b00403400b40041e40007810000110306440d13000031603900000018016280100800301e219040c09501c0220340100204800402e103407501c4100825245a001a601d00f100f4400640030004205081e2003070340c01d01040c43c000c2d40e0010411030f40500842c1000880004000c5210002e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 794464460 1250 794463210 794463247
    0x30b010f320a090f030c2106060e090d050325020a0c0b0306042a11280c060c05030d020307051605010902130209061e040506160201020d0503090d0e040b06 68
    0x15079141e00301c00c1d460321480c0b13040d40380074032015001151401c0140500d994044200402c80084413807844a02030a964020540f840e56101340344030f080010401240000600c2201d07801d445e9850318074594685042412030310450390002111440351028218400341c0200301d04a4000d400c1110a031001e540d90303200c0c90059100710758150085003400840d60044100010007140c400e40b03111041410381803640c04076110900c42141d590184216002250801c0e46a070445c03100c00ba04e1400641601c4040c01d0066030100554011010040183d0310807000c03541c04001e0365059403c10704056940c1d11590f0b000c0343c543c002d160003040344d00c2c0c56416000401405602c20b1449034420745c0c80d01c01301d080481c1080304a01030754451a03005401042018038035200800002000d0340d08101907810075032900040f0f4569000192034004043c00003800b03030155a010800030416211910b00545503103044141281c8401000f40722109000d40171006840341c0d078558002e00250070000d8512078031490071603811120050b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 794465710 1250 794464460 794464477
    0x904020c160503160303230f0711090609041a07021501062601050a0306020c0a061418030406120504050c1518120712061514040b01030b010f32 63
    0x100b0841a00c1180c000c130b804800441e50151a00c00980810309041070f4410307402e500140603c60b0800020748000681d034003802d9060700400d0340c0b000740139240e003d01400d80c070060f003101d1141680e83c04000c0015400c00244c1c940c03442c421003044403512a828207a00e8100550704080300b0720008c03400441c02e00d51140c441c20342600e4a40d00c00c3c0c000f801380207407806152028041da940225003a0b1043c4081407442c0c00034403092407120103d0348405071030340700e481c225a2084407004e0405580000e0080d189505058104c8802c840c0d000b541c50301d454403402500d090217031200210700c0c2e6103c00004061103018001140b00405c09004650f0821250720001115803080d4031441c507000b540b045c000300c1d604003000780d005c1d01c01c42d2a000b4000315090605551090007226005c8802544881c8900c00e60450b42e0300c00402000e0300e043e0500312091280410040e51084011141010324001040b980780e80c0c08120030350420880d050000c80300e48500c8000c402c0540e42005c100c02c98000c44504030950459034018420340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 794466960 1250 794465710 794465713
    0x13120804030501020403240c080615070507120210080c03060f031e1c08090d08042a090c0c0b0f0a020702041505120303191104120605010905130c03080904020c160503 73
    0xf41c47c252041c00c02c440711003001d000041c01500004005042480040030070002240403079041031003070381c2d6803480c0c178004e80c000d030a0580d0192103141c1182410142e802e10180b05040c40342e050b00d80021b407000b8500008103160b110b44010102d0401c503440603c00140940442d050044e003051b4038102c042e40c0c0d1921140210079a60400150180162080b8042805400d540c070182141c05501c03041103641c4c5401420944ea00e410944128003503d000202c007410110340c956070400b2451520384079108403020103840c0d105100d036040511002600d40700c0301d0b55000742d06403002d104036160720380e03088028000c440c8001d40044c40d00e140311000910141381c1038111402201c200000e9030000d1411512400180e90110700703070a506a8201d4810415080702d080e040e040105a4149a5514079030311000c0d603020029200c01d07aa42c001804103070860b000e0a0350061003001d0b24051666a07a540300301c4a540741c40003030180e00000c10198400c1c0d555404a4003070b00410ba04849055074145071400740d084492180d18484d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 794468210 1250 794466960 794467013
    0xf08180108010b0702030a12021c0807080106031a0d0804081605190602061311101205090c010c0311071a18030d05160311060a021b0313120804030501020403 69
    0x4108403040751321003503014001d41070068090366000c80c400104030300281903005000213408840c2a1110092a10307a043c0e40307856490910410140115506070481810503052100c0303081154500100042000b80a840322010020300e410319901d1809580c103c854640102e1059006030052080b8800c00d607501280e204011100303142103004000c039035118040240c0c0110740060300d4036821980d0200704902603584c031545800e0000c001007480e012180440c02040b1580c11040482d03605100c0c080e440442e8000520000d034040e80080d14000a0840c010100010302040001e000d01c240903a000800d1000300481c142566954055100c2d00300b075115020380501c4880c1c03a00203103000120301c0004011034031500e241800d0840103d00305481c01c40254188400b041c0301440c214400c00610b440307401f0031000140c0b5461103490b017100e44180901d48000755841070090800d038004c01900882180c2070f64620020400491902c60b002c0d000320f500c00341c101d5102050000034040d680180d42900c000061840d100c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 794469460 1250 794468210 794468219
    0x1f0903050f011a1302040b03280905100c05040503030406030b01140a140309242202062209020d020723060103140f062a0708030a02070f0818010801 65
    0x886030000c0d00c00c0080e81c3e80c02d04094490610f03016600001c00007003c00b62405445561030101a4030550b010038000d091686856544c42c108442c0c6c5003404102c04003400011100d0b01c955a40d070601c03c5031844020341d14010750214500441c02c0780c00805000d816603444551300c0101400401d00d803451680850b116100c001d084401c1c200c00c0b260301407440d844000c4e001404100e5805640c00050483e08507204d03081104052008464003681d22001c004904000b44c0b92200304036400001d01041d14a00c0303480d2000c5c8200595801081d145520020707002e1085800c03021a9490360020140d21151245100182c150040c4186800801a49001b041e0700413002441a00c1094845150081c861540d000f0a00500000d1011003850b0342d840b0200c03046610310b21034002118108103050b036075000b00c07010072089680b00f01c0381e01000c00101c001081000e0705105c0c66072a1200107102c028100d441099000a1000401c002da203501211150801e403010f440e0458001c180202c030000e40202804038481c03200008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 794470710 1250 794469460 794469463
    0x51e04050103080a271509090213080c010207060c08090a0315020d05070801060f1d040f1a010503040f030c030c23060a0b060a12062403051e0c091f0903050f 69
    0x54040c003035506540c045d91400281c61000446484040200117860310001800f20850000d403030840c0c058207954944a02d0010000c0c40d100100b00b02c40e042d07402504040082d07a0b048000543d50a401a00b019034034841d01c400246d910300150002026015503020201101111f90b0280021401c2d10004003c291941141962040824032850002a240d5000100007900c40c00b103c0b041e11144681241c8000d00d40c80014080e1440da4001c1c5800700d42d580e6012070787c001c50340200c0c1d48008080c249030b40f80d420103464401418484240c058144410340840703600705441009103a812903040441c0200000740224035a00c2c03d811015092286c1c420940801c1c0c5400f0b851058a004240c020203c03840e0a0781c80c0340070b0722441b207903509100c0959030300d4500250254100310420040e10005e0968130315114450005021501c01600000ea1001c45a010180440070f034000c9580044a41201540383c4200900107112640d051142050308084030310b00e80001500300702c0c05010381f8810010b4034500ca400d1404503 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 794471960 1250 794470710 794470757
    0x7020d0801030b07050d140a0b030c15030c030c070b1302120c06040614090a06030504020307170d080a18030f0906021204151103031e160207051e04050103080a 70
    0x181206102e81c000c944624000c0c001806c0d1441e086001082284038030151440502e02210860383c080c1d1155031080726890140500303130120004031019071811070100c0c0c0781840c44c000141044211200080851040c06010095403282544804181303400e14000c0021041c800203180224002e960b038051003c80c1941c00b01d03500010310000381c901401c2600d402c400326080011f968044400b80810021440d803603c4080c20b00d405400580c4000c41da6043c00c3c03042c9890030350f0a0b8401c0079080c1c54000d0740b1070081c5000c61111042800780c41c0803140340d01d410258030010611001ca11281d0f400c47c6032203004140e00710301516200c80c401c1e00c2d000c0d49903588101c2a61280b030510282c1d085000e0130001440244203540920591501525000c03d08902c2d0700702c094510740c400d44200400d41e012040e00d82e1300c0b15030401d442d94089142801e444044102c420065038412035030090b14402d004141c03942041c94440110300c0000e8000034410b012559490a00307038040d030f101c42140400117512040b44d01e0001d8409000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 794473210 1250 794471960 794471963
    0x1103030306100f112b0c080406080411040f050414031c0507140408010605030106060905010e101e170f0f040f02041d1632060c0703050607020d080103 66
    0x440c0b100380340c1c0702400c455180c00c4807001c0c024450809034030320245004120740c400c07848000c102d200801200001150940c0710f200300032000c0000715410701000840c1c3e002a9400c45070941824941d5450350f02d007503080411090302d030300e40280c502001c0300d0000c5d01c01d0b0040780c001c40c020310000708180c01000c6026164403418040c0748180c03a840007401c0d00c082c2c1c103601c420384c000398514080c028041100581c0655501c142d200580503234540b0350a00c079501d028800c4000500d4a81001100c0720715000018000c00c91030403081b4400d0081e104190b82d500e018082c10403c0040119208116050b4154040c040d015104142055561a0741c0001c43c4030b10f502c1e00184c00750b45050000003030303a0b07129914001a850200e03012a0031645910407190048201031004100504010140100a0380141c442c8042d070310551210311805444034042040f86510340443ca40b040e08190750340e002d2801c100100e141442080695500b91052315000424060b003c140940200401d500761546804011412200d0075030a010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 794474460 1250 794473210 794473219
    0xa0b04020f0a17071416020409031d0a03120f020a0c0f140906060f07050309060d1b03140c09120f07030309090507120b1f181d0601051303060908071103030306 70
    0x1545c0c02d2580030701403c00c3d000000e0140c05e98282c9a40480c0a42c2c0741040214041410b02010382000c0e402e40340c00c1409114140c4a600340745145444800d100703002d41d40c40c00c05106080c0c1010040510a01c420320030036401100c51181079584410310072110820340305418907008407010304007140c03401980c013901560300203107002e05050242e080e03696250702071034080340d491104000301141504c4800180c400c865032840c00050b60564041290810b80100050404041c50511250700e1100e07003070005500070503c0c10340c19031a4182200030072180368262030100c0c0140b08140c442c0da520f10001a0701c6d02682c0c480d0303030740460a50752003e03c08282c03070040e0344030317008a8000d500036160f40000e94000c8000400081510742100115075103000c0001d1510146000180515807552030b4008004814000342403445618002d415a2013116460f41409081c841c1000700014003444118041d4100f640919000041000007803240d15040c02c203030740180c1d812241000d65401c0c0e08528900401607d20645000c0e0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 794475710 1250 794474460 794474477
    0x40918080a03050907090504080304021f0f111e06010503010e19020112272d1b030803090307020406060f1b0203030d0e06091507170a0b04020f0a1707 66
    0x36040c1e003c0c100081210343c4d180301d00500001c0101441c040d0310b01403030248405076940d06040c01441070741040f071a80304a00c5010603202c14080d681c011150034542180e440d005840798031010181d81003040130a403648140c90100b180f59403102011609a040340e0085008100c529990111140c469903400c802200c031410301e4004e01e01650082c1c07418510384a50140c00503170744159847c11000800130314444c82c2c49107400a40d02d810011325504101301d1085a104418039440a01003000d00c0c105501001086210015650310800000c184050302443c2e100d0405900ca2405420003030303881d00f00e01820f910850800c10006280f6020304c17030b4101045c1007603441c001105800104850321400009040760988030030400390f0104845486080b50a006c0ca40203007044e8200070300c00e686050f4007030400000c8611460240043c44d60081403020709100d101441e5402c558444041308001d00c1202c05007a006070000921031070a104010041c010021517465501c0e00d5032200075190070315003086a1450110f2800c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 794476960 1250 794475710 794475727
    0x906070b150d02090c0c0304050a03030507030f1103161a0106081e070e060a0908010f0b0108010b0307050427090b04200112020f090303072301050f06040209121204091808 75
    0xb00041006c640050300301ca02c0c0560320700104110350201d504c10350000d0004a07000c13040540c03203401c0c00c1c0030a40d00d00d805031801542a80342c90f00c911410440d400d010000da108ca00c200440c44e001519011603180c010300e000d41c1c3d01c2c580030380203081c110380390b10034200c030b5206801d522aa170300d11350b038003550b4aa960035154924100c244940c40d032141011000b4002c40050001d1042000d0180300c1c0500749a03040403d80a0403400050b01c0c8240607084910614005c0c810400015031150a5804450580241101e0481c07281c0c00e44400c00740d41d51102201d6424a03800c0000d029211800c10301403803090481100030b0351340d4020302d0440307410f16110342d00140d075211b00c40c8414041034025040f62038110348014540202c1d1400070345154440340c0e040700e030300c00d055408601a189030140d03400c2c1c2038083c0000b030000d80381c00c105d10700607900c00500309132040e47d01150b1b10301c858648001c10480009014115608050900e840d035909400c144601c4100506001c084031104042900e200d0004c1d40c402c0c1c41c141031440303d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 794478210 1250 794476960 794476981
    0x213080a0f0f050f0601081c0e030613080f12041e02030729040f08011515080a060e04210306030804120501110417070f18110906070b150d0209 63
    0x1180c1903c0720311a240f84019440c0050044074000e100b04401001c892685807140e00010303035100151002c0c09451070708407805490204005a12500380ca01d41141e00316070b85094001c9002c2c0c40401458184003252960300000d8a140850069000b40d4504d0800303524444054400c440800e8001d401d504203a1080011103241540c0c3c00412001d005034458074100348805004070f070442da002c1010820b00c600200702841c0d00f8411030018400720b4425100040c24020309054112000f003440b410400d1850008001c500107034046009000c8a1944808174282400c1401500c94071600081c2005100c008032404070380079110b900304407a4080e241d1820b0524100080c483ca11101000b41e40a5486600e0403451102450051028180c8400321000b0310380070800c080d1400300c958110003414080f440c3d042c444070356903c1c4002a00046a0000700d9548100e4030b24800310700a01d078000340c10003004203044003081358440006100e400024000038061024508101c003440000310080c1d0403880603008540510034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 794479460 1250 794478210 794478233
    0x1060504050105220e100b12030703082e0e040204050906090c04020903070905010b030a150e01140d0c09140f0705030610031b1119020f0d020a03020d060213080a0f 72
    0x5100c00030302c1c0148618014140380306d10004926050340c48070340e1820340c540030b11020700b07041032580111b09110050f0340c081d040302c9000e13141141040031030b1510594000b03101a15452101030001c0b4003c4241c0e903c07412030a0b402c040d1000c0f84182d040c040040e00b0354a000426a100700308000003056003129000c1408000d602c0851403980601070160040f0b03541c1261300845000380000203501d41c1e40c1c903208072618200c03481c080585601100b041001c02c44d128a4501081c103580e80401400380c0c140a61002170507078012a10010040d02d81340d42d00155044059100d030088222000ca180c075955142a400003011104a42c0b60010401c20b0000c1202400c1c24490500750b14018140010608000340c1d1350441032600c1c1e0341c8080080c1906809200c450340078804212106909105200d42010b00c0c0e0015030040c0c031030950380b4041c0562186d5071066540b081d030450b000310340103401481300101c64108040654401592003116103a40c544c002100c050005a0a510071303000751a0a0032400280c2d1480b80881 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 794480710 1250 794479460 794479519
    0xc0c02010e0112180b01030212030405031509010e060c0408101e0509070f1509050108040c0509070516110405014103060f070e0303090306220804060203090301060504050105 76
    0x40d070304c1c000100c2c0c540741031004456190041000c24500d40c907520401c196810103449102d0b0702e8201348030802035900c7c005802002608400440c1442c0d9640e10301d030740e0051038081060700d1076110311024441030b4100c03c0010702c1526061001d488007807407000045c006595114501951480540b90711318140003a56202e940c00c9111a4291110140e40301c0380804001e41079007214102c003c21900b080c0e00940c000b2a040002e000030f0902401c40d260503224080c00342024803c49010b40034580001d58030074860f00890300c480d9000018103030300c441030341450511141514559030003185000000305507054a0303080d40d480b034501040340c40703c0140300b07003211800c0003d40000301c61144880910607240b0341d0207000386880b900c006540014640f400b104010301004c1013035141030080e0030410010501d902c1c0486c035113a000b221040b075040c01001c00c04451085034200c0001a150341d00105001c02c11729800300040840b40e508400074007887c0d440700c0400c01110420300c10194440410b5028903000d00e4008245404031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 794481960 1250 794480710 794480747
    0x1203030a091109281103060904062309071d131104090f050706230c071a0c070609050d02041e0204180516051b030c011e0c0c02010e01 59
    0x2016502244019070113452210422081e02c0e60440082200d20748040940320301d0800707000c001800103200c81a488003402c3d450250101030001000d00040303401c81031400740700307148980d0742048030041080b050905955040c0c00340204000014042d40340c0c4881c80418030100c0e90001541c0300c1c070f0424100c240d4191412610304a5152a990165841d1302c510754074103004920403048410b1900e800c80c2806860b4001c1014019940d600720641c440940400209082100d145946e038000840003c0c6400c03100e5001100c140e070440e407c10a9800014050700e040781c000320440f24000e40b031780400c0d1051251130003601e0308100c12544000148c503160f00701e4451800301109040440c11460b8548050b03134801d4012a003052a044095500904103105656000c80300e40802c91000d01050307801403c80c8611190b4031351080c000c412264143e01c09004943c0c103012194020401403107201d00c0404c40300700690224611618000700c0d03d89560145035281c1615034141c0d902c0803181c002d0401500c046100c2d40781d24802 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 794483210 1250 794481960 794481983
    0x80c0903191506060f0210060e0c070c0b041202120109050d050703051224030a020906090603071206060320130203090a0807084b07021801030c051203030a09 69
    0x40c40043c03055801600e066620303400284170f05000a80b50a4901c02244400c0c2c0c50000c0c20409000104000c40d00a20f2540d4803907607901c1c4904012000c00c011341c03c0040d400c5070010b030000e00c0f40c0d96403080101e50b43c42910460b003402c0c0c00d81080ca003203641411024142d9001320b201d0002e0688900000c01016100381000c034141103072107400c061102c0342240d000024450f22454594900d4000d002d61218803000c50040c5031040e0907a0109040d070701c0290825000310741d1040410304980e01805030030040d140c40c41c10511030143d603042c08406061184015a124102010161210a40b80311100300c0d10702c000d04154085540110710800a51000740240a14040c1000b024001a120070040c841d050081d8022521117181c0011504241080d00c80307105c60300000b0040d05160388140b9901c448030000817203151410221514118454441d0000081d40310344146900744907203410a921a043e240903200c02e02c206134403042800317070958403200004030f140d04c28000198258066003244003c540b0410b2246035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 794484460 1250 794483210 794483243
    0x120910030e0d020a0303060b040f141513050910030209130302010b21010605042c070506030a0c080604020c0a140712030f021603080405042316080c090319 68
    0x20b042403a040031005801c024004010301d45d260140c2c0000d40041055103213081d2402100200042c0700c1d00c104200400d21031807614282daa40c2d208500c041f140c500301684c0d510000e201d0b0052500795401100c0c0b10b00500c0002c034146110007000c0c542941e40c0606003003a40d45911a041603960011007040781159242c0782181000e445440950703044a04c01701d83c0180c6840d90038001c609481598100f10302075850020b619000314004806280c1c2c0c5040b1004030400c0d096024103981c14684940c01140d0010700010903c0406e0030a540300b12070160a42c0c1d10701e0815224881040268401c54003003198030b0f40404600c0c1c0c0417908008501c094100800120b9000541d58112031180c0940070340281c0c00300c0d06100d0030aa00a4050203802d00111030500500e0120707081d03999a4040d40120300940c4c0c001c0303035a0f04130702d2030484007403c10011180440350004076500c0c2c5803d400c0d151750225006800020300c0c500c042103000e001c0505440d4507807070040142c0341d10b10043e0256a032450050005032110b4100c00750840c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 794485710 1250 794484460 794484463
    0x21070305011d06010e041109040323092706060a110d08040b07090807031509021207060f080c03070809150412080105030607120507090801050c130503120910030e 71
    0x80104203241c2000d8100c02850302403e0400583c08143c9150011040100244d010710011400900841c0c00886645590500b1a060341c00001c035580056400c0340d090130410440c1d00030301030600b02100d00180d03070b03200902d945060280c2240019083c2210304003151051511402074481a801450000733005a148071680b460004d4a10800002c100c2e1501400140700c41c0c1014654072440a08142400c60326007540c0c07070382c0d50104d440040c01882814059044010b4103070807031a180e980050002c0e510a41e421540c1d03448820b544103c802040c1d0009001c40d40300e00a0781d03503900c503006205185045036aa01c1c0103a440060092050005010302042c0010222580361100d0150340075041040f10020390503006080e940701a00800e100c0d9009808201c20103034000d0007120418a90f600120b180d0301c1d0084243c07a17081e05c6402412280d400e19040140c504417400c0904060b00380101c01e85a01d46c0d03144149611428244862903100400304900d0700b050804a441d00764003891481c4c000f546480c9a141e25 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 794486960 1250 794485710 794485721
    0x8241311091c0605011d060915222702040203090102040f0b0415050304082703010603080c0c0114070b1e0103060c030c0908070302091b03180f010b2107030501 70
    0x2c142e800107800c0361000e0100c148602030241501c1c1e85295610030041158420701c00d030083c001d900c5071900c1400201c020b48440390320710000c84003600484448400d000c1c00959840320030401c40085140108801400e413140150340354400300b04101d1200358507180c081c4030180d030000b4000c410782e40d000c000020311060710118080007800116801500d80303040880559000110203401c0040140500501010605600c2101d220051a08000b007811600c401d03408407002c80010520f6140d46030910000500c40000010401c6195000a03140d4100d410001510000d8440d01403002105003800307484d00041c0e1814100c0d400c80a56450740c440045080d96400710901c090300122140c44e2604c0d40d1109598140c09001b01c01030740c81c1801c002c29410700c4c03c282e0b5500800d200180c4644600c5000c120b40030b00c0c60440c4c1886180040341d0030b542c0d01d083d5400305000500c036580d101a92143c4a01d404c1c940b4018420403603c5000201800c010900b08802d0381e80620366061010046c4c0101000080000e0007403040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 794488210 1250 794486960 794486989
    0xb0703081e0408071e0803241017060901151103090d080901020606150a0c11030601090e120c060c0903030c0607180e060306060d0c0905070824131109 66
    0x2000e42d92480b41c607040c0c084030780081c10040d100c074503540c4540000346c0780000e6070340c1700d02c401070a0b0341c00003803212424110f0102510b00c2c070f822408400104d213140b40e00589454a07485030041c4101140c0794603003401030040c424411304800840c0980d40c030b04020710504030b0b0701200182004580c02d044014000035010601040704407000d242c0050042d0f00795805100c0290301c0390040b01d28182c20303000c0d161019a6072180c0783c201010020b000704078608014404114020400c005412124190303150103450700140f6001d2616040d42c860154140070900502c81258900201e00c0050300154a603070800100355001b0441706179040c0410310020740418010860700d0710416090760b0f99403848a522401d8507000c0080d40000908461030740410656403000030b0003503008001520301030180d4110b828900390f01d6181d60400003480741060188043d41364000041802014401c681e80c00c1342c48000c140036909030341100100e4200c8040e05d90850045030550141d0340e108804031400e0f180584040c00030b4000081c9030701 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 794489460 1250 794488210 794488223
    0xa24151410211d0a1a0903070b01080102070525090c09172a0603150d05060406020a0e0d0f1203020c010c02100b010e06120901060909030c03080a060b0703081e04 71
    0x20a4080c1110071454416407003043c0010340100807498031034a49098030314403801d82080c11701c0d011404034401042140da030a074000d0702e54071031035840b012068080e600910341900c080c031889071440b80420522240303c4002c00b1540d803001c400c614085054020300702040720042404801000040c0c2400440c5e41028481e85240240c14005103a00d944125040c0c80003d00d103000f1500c0c0b01e007080704d444510480303400113440c20011145502942c001201009402c000500c0d50242405102c1000580d40150210032129124040d40c9000101881030280341e0709400b5010760803242e8140046440084046c114200c640f401514055402d4440c500351181c40c1c4044005078000c00840c000c00c0f80511420740321410918280001c411400005082802203d6030840d0320070340900070503d002000d6002e44001c1960b52824800304416090160002c0107103030003a000300b41d0400005445001510805094501c40780c400380c18006143c6040700d2184000301440100600d1440720101c81c070b170700c0d84814443c038840c40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 794490710 1250 794489460 794489471
    0x2030c041107051618051b13330c11060301081b270703091209051804030212070305040e0906070f030212070e030a2415141021 56
    0x50951321300b2540030900e55041d04940e509114505101243d8000e14080c0400461180c81e11031301802d030003890303051490f04c03948006800100c090080707904808445c01115929100700440b4414406224002d19500c1c0a00048420280d0207004958600c0787d240501812112205610b0120b05c0543c001c2e0401c14441c0c1c80402002d902d200c0d0000b07144512401a0b0b984110340c8114101c000c90030401c040342c1e0350448a09000920040d202e40d0007048111340001204141c0400d13000050f1659074280901c074010600407905001e11034440382e1580c001e5916600620118800200304503050300450340440402c034007000000b503030740800b035001070140180e14040d001c58207060001418240c41c8241c030005160041c0440310341d9020b242051580404036040510030700509000103400c04003100e200401e014a100d40c099580101550300d056038828174001000030145940ca60100250144642c042e604042140d80c4101e05020701e510300703082014100003c00d0003040d4280c481028585040c1c408555558 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 794491960 1250 794490710 794490713
    0xb0a180b12030d0f1a100507060f0f0f1407032004080304080616081302131e0c020a0c09020706060f1401080709050102060a0c0e0604180f1401090902030c041107 71
    0x14400d81002c080c0e0201d003000b01c1a800d40344a01d990701754203e018881c610140c4000c50f01070059003218007455229204000c0035885402d4040100503803131102c040285400102013a0300e03030520502c0c801c2151680052a25a03ca5400f200580f800c90042e101208840c0d41c040600d80c90031010300040c0003100051a1076600380000c0d980317000e400403d040344581101d075000310ba0030b40010815410215495407422011518008079601c514140480c42c9000e2500c82c0110b002d024803000c44425a02c910400d01c409220b02004076591032102d40080c200d070408400802044005a0042c90050300c00c40020a000e541d842a0030315062007980040711010700034070700345515a031000802d54070121504088901a0610000035070303820005081c03072252030b96610700c0d20b04d070f83c00b442c47c484422600803c160b0b980c41d100c0351301a400400f083c040410881c2080008149180305007d0b0450204e03088040e40d00303e82c03074100c40c04040c0c004400d080c3e030180121070f494001c0340c0ba14040c940410b10290100341c0d40361850f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 794493210 1250 794491960 794491987
    0x50304080c01030207080a030b0103150e04050c01090b04050402090d05030309030301090501051c021e091807090204080a0f140604061a0a0308030a0b01030e0a0b011502010b0a180b1203 81
    0x1554912410107204001540001c0c201c6c00c1030791616515807400058880c0ca140058000300f82d100f10714008094181300008514040d059202e210381c0c4660705a80c0da400880005541900e0940514446140f0038030042c000c03420503601804d030382c9400404014500406485882c2958025140d0707407501d810000040c42110100d0042ea80104000d9490142d0128134240301c442850030301c9002449000b5241f411a07004103000c5040c1154540200340e044036040c041101300309074280b00c00c1003125001d038501c0000c042c030360740c07090b10222681803000d4190111141c0d140305580014000488458082c041c150158850400040740b15510603100054982c80307100540c20340190302010940300d154550130030304c00110f00405580d000040c122020803200884001a0064552140081d0981c071803103101c6814400c120340d20a04aa4592200c1a01c055110804900362902d9014090308030700380306003c12081500750040e84404a0070f6500081503152540080c04040c82400902005e500104010364446030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 794494460 1250 794493210 794493223
    0x331d010e0a081e0c1005210703020d0b030c1c080c07060509010e0909100509030f0d09030305100b0406080709051c0506070320070804030b0a020c010c2f03090a0305030408 75
    0x10f40c400141010a82100085e0040c0440261a02004000b081400d41c0750424003c03d400000000d0300c5000034030b85004014000e401410100c2e40b054180a0342c05245d080100d0300401c1040003912086610542c5007044844040040044940d40804c10141888003410303c0702801a00c0c140d91007980d40c9030701e40001001411029041440b81d40c448041c00004000050f50901010a4400c0451680d440446280c2140141d4006000c003282c00203ea0302e00746255405030b02e0140c400c0e1001c001035160600a442076818a0081c0503819004101c103000715801000d0040d4050860f1405604d010b480e03601190750a00752071003a07410320401c000310300100001440415440034981c5401c01114101c5150701d0000b040e2160044811000002c03040c4c1440207100481d806981c0152099805040401e05400294800b8004031219441c01d4082507520740304007507112000c80780ca04542c80c0d0303005483c014040c840c24156185605c1c4030070403c22003143c88410b40306c0c0086019101a540300c519001c0190704248 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 794495710 1250 794494460 794494513
    0x6121605031e1b0f030105040509070e041515081c030e0a26030c0d14160e030703210e190e04051501331d010e0a08 51
    0xd410300400001040e0b074880703010b81d200c80d1200c04074103448211540907522018a0b200703201000c00a4040d000c0c240c101c00a42c101c2d9004e69003000707030340d542140b00c0d07880b1403240c080c030000c2403002c00c003140105240d511054003a00743d824000a0048405103003251000f200d601183c040c0e00700790b194000c40400c040041d04e07560f2071800e0601c003840c000044d050325240581c40080c8003c0244403860740544c01c007902801d810358200d400035641d00b0150076100268010001e00b910305400c151110711309807101a032aa0140c8800d0311003030300c840b510440983d100b01341240082d4143c4520719001000c5401c0c40c1c2000c1c202943c42c0e80040d44a403000e000101420024940035019038071650050241c1c1c200400103000704c0e80c1c0d6810344d404a894520b0107508003001e480c09190000c1d888000442c428003a9954045000d555842405580324603202c00d0007503454a42c50310300843d080c2c160360581c10050840c0d041c0311035414505005101c9191000586911058100c40e20301d40c014200165440820800030701e000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 794496960 1250 794495710 794495717
    0x3050c030d02070b0d020d0507050403050f0a171b01050c090315010e1305100e07150f0e040203070207030b040819020a0803041101141b0607030b0a030b0411061216 72
    0x9101c50200030b59141c0291103480c43e5000f00080842415074160305980c0d0301034504034140018107113240010302540240c0002c0d280e40c0a40110001050b41c00a252050b29a200c083c11520301700749006000d03590098605d15000c0540542c042201040a12030144501e003c0c40714075458035141c07801d151508601060201c04d9000c03043c010311441906c0d03d0f0316a4480b000f01d56081d6004510300d0054203025136124104070441c1132040e03103113950701d02042ca503082c0c8110001820b0020070022084490200030101d03500850400301c54001e5500301900119881724242c0101c0e8881c0f07a07283e03180c96006000320350aa5582034046032803c0300342d603c2c4132401900d052074801807401c0415502e54002034400034200a0096240025100260340212030a8010700c0050345081e4070f0310282d95111051120303824814440340110030003c0c2d00c07207019208903100f80c0f074090a812002401c503544d0b40c0712400082e00650301d0803103006100c1007641d5160010220380724407007404111414003c25507140715100000500a2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 794498210 1250 794496960 794496973
    0x906060e1b160809030a030c120e06030402190f1d0604050603030d0203070201140115090f080d0806041518180f020f0f040c030b030708030c0a02310603050c03 70
    0x1028180180c0310b680c00100080c40d280c1150b0714015540340700754811690140a11031008041c1901706200b04904c0380030300c0c1c00030002a034400085500ca00891200c552001080c40464051b0900301060410341052200303d030031940c0c0340d02528a03e80c0099110800b619401e03640303040c20381c001080d4a50800c900703460611050800f200020b440740140a4200d000590110004040310f100350005003840300244901102961114100700c0f2247c508162400800c01c0d500001544c00c4500d103002d4100c0d4608405040307403041c54202241d0010007d082c055000e611005009094192244200014007000808040c818042404481a203140c550240b003120201c1c8a4440410721205d0000300c044d0341114161441031109000921f503101c3c5c0f40f001d9030041c3c40d02d42d1300815150960310a403151203044080b10280c6640320328841e079034400d08101d440a5040b04000000600700f0103016482c240d0b040c0d08420b003461182c45406402a04151070040c415180c400070003c2c44411302c540e00b040c68003600034000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 794499460 1250 794498210 794498251
    0x120e0a050f0a0222060504061818020102030d0f0e0d1106090a030507080a02011d010b240d1503120507060f050609040b0615070b01170a0c140f040906060e 68
    0x108001d168401100450761340c0104e804000056200c2e02c003900b03000f042088455110141c03060f41c640c4040c501401e541c5400c50b4550407100c04404565015030590095150410181451014002820030407480c50744030906d1b0321001206000810696145a6a42e9140380428030054034142c40038060006030342210401001180c2d10400f1038aa2130781001501c2c0c4d0b60003120038100c1c01002604264402c1006480c15180c041d01e040d0415001c1c0b03e001c644030b242050741c055003864001d00510504034551010030484214080941040c0ca50039558088102402d41d40d0b01d07443d1240d071450000000094002903910200901342c41403074495601c1c240200403528000000c02c2d082c0c9000303080030f850088080d00003883c5a8980b155480c1032500f00c0e154686501051030203c080d59401e0240c441140000b01420104040c0017502824103070708510b0800106161100d01d04404500c1c804c5181c10603400e8900314026199801504816403158400042c120724100040d581c6040240902400f1405d50040c0350 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 794500710 1250 794499460 794499469
    0x100507140304110604050306040c090c0f0e0d050106050d0b0f0a0c270f0f0f080f0a1106070804270e0c010e0a090c0909051f15120e0a050f0a02 63
    0x354043d43c000c00454110b482040019018005c5a005552500c200401c03c0100880e0351000d034211807014005103c01c2d0349450b001d07510484418603110000385020710903501d0389089044450954000c60000170b0603071b1100d01040340e00791504400e540c01142001480b100c0c0b01e0801000e5440340c00c500c42004054140c01d00140110080d180922008420020508034100c90350001c00040c041074808036030032a5280130b0001c2c104682d02c181c12003240001c00000e880c1d04089108146400d00c2c0028080c0520590b440e210212040d01c00c064010710180552070020f40804001d002074540c0050912030039000003104030440020b616001411800c1ca001360b42c0042000503800d44451003403c140880800c0140460540c8500b54000110070f400d1929414149401c50426002ea0381080f00a201903034990403041515a00c00e1010302c101103035140d04111281c812007100c0c040900b14580400c9540e200c030081410b0300c20f912095262500300e001c4000800c20108142c000e4680880301a08042d810b0740c0014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 794501960 1250 794500710 794500717
    0x90504050f011707170c040605030601121205041809200907051e0a03090201140408030f030c160302070f05010809120901021501030b061e0904020f0406090e10050714 73
    0x8480c008103000030341d03401c22051001c080074001205d52a018490000d0003c3c2d40d48030100c2030a4091441c0410209071401e0100e6190705072580c042e07686d03008040c1540d8880140b01000903071010450240303c01301d9a02c02500082a420000c03c401041840c02c900700303480e80722291400c0311038401d005058401d45403502c486196001c0b1607420b2868541075540058210442c140304400d40e08440001c07143c0c909601a030081581074002e81c1e55030212000200c4140303051095015243c0c141c3d1083c0005e00c1d0300c0580c0c40085074841d180c15016818100140c0c00000035141200085000d0780102c0d03824807030503000c6401c1000074002441e0223101d6040509140752942c0001c80180180100000c0d28161130340200314045400503a60101c02a9681d681011400c004054460034442c1c05000314003aa100803034051400110300003080d5a0841e03c0e560708001500482d50b4001d60807070b4694000050003e09031044201c142b100c200601100c0e0743c0c0041c3d9004070fa40040c2240180009070012001d07031381c0340c003040c0d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 794503210 1250 794501960 794501969
    0x10215010b120a29010c0503040306020a020f03030114060a050702180402030c0d0b0f130c060503060a05040209180613142706010b1321050705060a0c020423070f090504050f01 77
    0x1113154202020004895a02407150060944c0c400020000704000869008004020041c0c0c25a901201840d000d20744920082c031428044650795542d00c1c6484c80d10400a2496003403034103281345400d0556002c034442001c3c554001d051180140c0c100000e40c1014005011111412900c0e440c0754030003541c559000010180c11032800b0581e40d000220507030700902800140355001107083c40c00a0b9100d500502c81da000f112414018445c8078400581c40c20203000f0344010b060b00500340c419038444900e0308001030400a2805600c0030300210f4802c000340151190300c036140607401c030008452800c020882031002d18840781e01e1a00c40d88940390441003c02042d09410344105801d216581c5aa010800b81c801e10309800104030003540717145042c0f401141d56007015004c1d1040741601c0006a4440c1044803d000b030101d101d010a8015003840c0c0145040e500007041d004510868008081c0c209001d5010440100c408a0216400c03410b49c11207242c10002c000000d20b42100c050140746007200140c5180c0f0418480c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 794504460 1250 794503210 794503271
    0x3091e0f22051b0c06010824070503190e0c0117010f12061e05160f020607050d1503060204050a080d0504090908070203010e100f02040b04060e010215010b120a 70
    0x70520301d02d09484100e110030810f00815840d40c50000505031508001e1082c8500d038410390100b003000ca001c2c2250b04040c4080c1c4142003e29555100d000d840a40c0f00608003112411201c0d507080850002d8071907600c0042007407000745030b1131070028009004851a5038040014a591200400c0022007207501c0100340d85584d0103401041600749082e1000c0c10074908040036074642c1101c0c0000501040e40304910514000d1000c0c00c109004c40c20580c3c030080c20001680c0140c0003480012030990007100105022100d170030000881401c0700894a101a81e9900202d81141d0001030400107403070205400d201030315200c00500741c404965007010b4014401d502c550f12000352214400011f00c416030b0140e03001c41d0f4015000340010001c02c9222a1a10703140c0d11050170300d41c40d10100241ca0b40c01882035800b07a80854400b42d10f0503003030003420303a0b45089065a05045209416002d0315242d020340e0301c1c0c0c5c0200410210145c5542c5d83d001c4500c174521000f041c40762a9460032500107581001c000c03104542004058 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 794505710 1250 794504460 794504471
    0x207080106230d05100509150f060d11060d0504110406061704170c060403020a060c0201090f0b06191203120e0a02011101060801061212080105091803091e0f22 70
    0x91300030305240c589039178444440d02d02810007440200124080d07280720040044107600365960f04000a9201066640d56049000e902c250700014104400030a03c005008018500b00100b11410409464046a00f25a2092150700d00c1c82d03542400d00440340036217018100912400d08465401c480f981009001a2030000c641700c6d802d1880110800312003542688100761459842c1c5810065602d40c046002144c01500d0039038a00382d128810710402e010650700181e41c615070885c030f0300c0d030300d181e510050411903000c04421040c0240301200d29000e0001c00402070428076440c4942009801444009450340340d1500302140c002a068021620070041036090912001c4040e920f10b03118018081a0082611586007200206010305c00762a5011280d1041c4101d10000d02a6541141c04031803c1c454950000c1c051400715025494000c00ba00801d40c0140c1103a0903e0110400120f01c8200902180c4800c04052200c50803801c0c00e120041c52001c040c0c031000101c00200101411048000c0c1520390400c9d1b888 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 794506960 1250 794505710 794505713
    0x8090a0b1003150e0601091104060806040e010c08041208010b04050d03120f020403140a23160b07150e060721060f0e13240b100207080106230d 63
    0x14241c07005103030042d011061449040c0c0d601c80051035814688111886a01c00014400b6070900820a075075111181c0301303041034900801070342d81000c064140e5034820349911402d81500780034490926a04215507034500e40382410304281d040201c00d00d203001c003042070040040c03107800800b0342100e01b210303416101001e026810b410102c4403c2c2c0340200c40c0381060f041010b4030705d04d0b60031a0040d2043e01e001d800c4c20000c3c0700c0b5221301c1e15070324200304100038403040c4000b080161032040da403100b9608004000a8546009000222955822041c0c1000412800c00724480c3c0900440c41d080c826001000d08081003c44501d00d80203644440040c4410100840b6240701d403411042c031452044411a0a501803003200d844640c03103448103440e030003a2a4140b03400000550410070140500701c111f03030005101600b108810690300160a03c0524144c0c40e00c0c2c4502c0c18540940342c1c60401c4015000b10f60150000a0420995909546550f485400380d82140c1e2454102c004480002c09002c62044034103880c211003a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 794508210 1250 794506960 794506981
    0x21512040b040317010e010501180e04020d0c0f06020607030b0303122d010f150801030c090203130b24030a030e100219050a050705010c03080a05070905040213051008090a0b 76
    0x380d854613960000f1400055185001d0a00398140c0f0f0090f210a0040000080d031023003009079511420014a21910105025040c4080004c3d04507014403844140251544842150540300340c0c89080168858000c009a03da41441480c80e4644110041c0d450b2209c140c903020b841a8000d84550150031000c48010000110b0901c2c901901da00c4050402c0c0c69a5074030288400303080b841c80380d241040ca04050001941d445181c2c001e0580b40d00000d5481c0c4141000f400c1002508014032003041e00d14008004004100b01112a0b0b00c84c1070340328501104403d80707440e000d11600440b8801e50007940601c2c51000069007081301c4400f105010380306050361031042c510032442c1c0180d060311420070088840100d4280b02001c42c08681650152080f05c2c007041e52400111074030603400380007500051140c40410400161a08850342040c620b20300f04850300d440d14001012a0b0066103001c5040456505c20030007070600594096441001d82032459a9142100392503844000c0754200a01c00034000e400100000b00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 794509460 1250 794508210 794508227
    0x81315111f0b13050f0a360b0405010b1509210a060c0c0b09060106050a05130308030a06091a1c0311060c04080c0a0b0d0b0f060d02030103021512040b0403 68
    0x20043c64007100b1003400d00c240d00108425100d084005c0b0044001450140807400340322121b000f110b000120007980080101ca802e0202140c08150040989000d00810b1241c1c1260703010310702803800043d56400c6207040001d07504182a0581c980242488a10341c2581d5010b004018182d0a0b0700b0220110b00a911203404c14100000040c4400d00e04100748d003030141d00015401f042413050b07000c5d060300d131034102195684130000d100345800110f040100101003403240014010b1002003100015480e070300d9035a102c09035001220603110403592464100000c00c3c00740034008032540e02a4805140c004d05002160314951001200d0700c00c024005660030802d8801c028528010360808c0c2540d14034104100c8001da07580c070521818466124010908c1c0c92840e000d401142103030281709800789008000da0100300600040b4480540c40008051050340984481001702800700841000681d02d43c1544100620031600483c000c58400c4103004106039180f403200925042a041081c181c16951607107821101c00c80d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 794510710 1250 794509460 794509481
    0xf180906010306051f0e181f1401110f0601090b0102071d071107080604030f080a2a1101021303020a0602060c0f0d060302062205010c0b0f090307081315111f 69
    0x207143e078202d01c0c824280c50503c10302840d40a41443c1020341191a29440030200c0d000300020040189d40740483c030340c040c42c0d245090040c5101619610b20a4601d400c2c01c08109902c181c03241a22182c0785889982e060224102400c20305204107a02d9126400c0342415080043c00b010904c00c0c0032402141240c02040020001e0440130226040391520b0304d00140181600d2b200080481c01200101c1d040145030f00030a041e104021180740100500440d090108410b04d002c1442400410744800d103154800303000400200403503840d684112483e51043c01480384203a030110301150020000e00184101c601e00301c5003611100925140c40c0c0800510030700c000c4c509580000d6000070002054440d1051401e041c244808070701d00d5842c40c059a90700151040150890010014003050001407990484034401076001000e140c2203030308100e499500c800d03841e40100300c1c800c070845000348100b00303c040c0f0301402800101e0078544408045004810340741d54002070080000270341400910284100c016901820110 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 794511960 1250 794510710 794510719
    0x309030703030201020901030506120d21090b0105130605010815011b1506090501081e0f071d07050a0905042f0403060f020903030702090c0f180906010306051f0e 71
    0x4a81d00d14002c1d00035409450700c0340c0444d0800340041c032140f40810503440ca40f2107113000b40c03540854400c811514560004035080e5800301160007030742c03c00b00307612640103514842e00c1001c1480d41000100400d00c0c8500c550041624249041408942d80c007106040d080101c04840c0340000101340b00603510744141c04420750a0762103001e0703000300744581e404440704101c0340388070200000794030741c4004001d07614240030702072950348043c24200c2c400c0030106021071021034507000e40300c1c4d01145162007410318425070b000200d4042d100301041c02d00410410415009540c03030511614005079800c2c05003d40344031f849007d102d540e8409800d1942040d01c03103c1c0681c44440d892141c255900280390b4a99600140000d45000b07140145070280318080748201e481c0000024000c60a00e0000c1d03007000003d903001031241c0174452090002035000e0140c2d40191030101400d040c1901c45034109814000d000000520003410942000410081c544a00d041c000780341460b01a10120214141c00c01d59a9000d41c007a0346800 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 794513210 1250 794511960 794511973
    0x121b0c0206161b140906150918070c0302100c081303030209030a060c32070f0609050309040b090f0a020a0e06190f110628151502030403030e12030903 66
    0x5614002503416550f01c0c41c662103c0f11440703018403500500484101d1f40000154113101107030003c42c000751010050041010104011601401100d140140c0f81c4601158603c04007208158060003c1051100c10b44410001840300210040ca200c6001d8261300c2c0042c040c401340424075100382c041702c072031890113070464480c0341d6940ba0107002490f800d80850001018440340d81e03441c25210641003545010402c16908034561120701e54030750382c0004800c451002004100b40d00180c0d19009450101307006601840c0c64118420a100546903131240d480d1094100da002c01c0841048840303079a4114107561001610f41d480798000381c8000b101e004502d60b1105001c1038580b2051410180008645515a1218203102d02d011040d02c04900611016490350031150014000809919001814490100542001485041d040d900f2159041c00e4030a030561003145c244000c46842c00b00e0303494802d4910041d490a40b030740d10300800c07004401091a03c030723600100c0b40165665007001617504860005090750799 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 794514460 1250 794513210 794513243
    0x3020c011d0f010c020c0f0307051306051003050402010c030e0f15130b070f0f0512160201090608221103071e050102070b160c090606121b0c020616 65
    0x50559020803110540c41202c8451000d01c00c180200003910010303400078a00c48101400f002600c9005540c15a014455a94001503075624030174010b501ca44a0040040d200d03043c24280b1a0000c1848600418941404103010060f40d01c0701c0d0800b1255010700c1c004030017102c21000a00b100341c00110603948981d9102c074154442c18107500400d001d0083d803902036900e5944070882c40e0b03240102080600b07200260311240c1c011a2098609040403445201984e5044901d1100c02104da001500c004140041106001e82196040303c1c0701c03409000d281c01c0010103031030020b442001450100b81e1380303002c0180b0315a030041045131000d08981012801416100d40940310072404803c040860207130203000401040008140d400403944001762414a034004e850207920545c116220f4600c0c10b003c0311103101c400c1c40010840114800d0001a06e501d84d95030309010150003d00e001c1e81e00884450070b03044998140700c0e07603445c0c00400b00f21500d036040c1c40b442c0d182d0074203000c0000301e5203100101400c0c501048941d181c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 794515710 1250 794514460 794514491
    0x103050901140c13091b0c031e0f02190b01090209010210111e03070504150c1a1e090a0201030903051303051e010e06220f05060a20030a0203060103020c01 68
    0x21342c00c07100c0d4000103625581c90b49400c0594445402c11300200c65401441d6034182d20130102c069440e03010b81031a040c2400040a417110464041e111500041d8488103109a080d605100e50340885010039140c5900403019191540c140b0018440d8004255000500e0a40c6900038002d0300d080300007101c01003041070340c2140d0010b41688603005401842c001002045290000300c415203015220603581c0c1c0b804c1c41d09003900540c584280da00d0a00501400010650005441c002e143c0c080c0110b10030306c0c10103410706150500e11403040741520030b9070003c81010017904020000e0024006502440c1c04245624181000d481500c034103d82c9120b000701500c40030081c080300041030203070150b07003048014004400094240c201c90b15011796648a4120102040107081c41c00c82244075022010107004000280c0d988030984901009070854440e00004104940803081d841800c80a50004208481e608401480f80741240710003031101c886180d02002184c096403003035060301c0142400390020092402010b0664 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 794516960 1250 794515710 794515717
    0xd0e03070f2907030b0d0b090d090b0906180a0f090c020709110909090c0d03091a07050709021c1805331816091802010c020103050901140c 61
    0x2a20b0101d486031a40d203407490350b036000c6150021801e028442036251040200c02403d020f02d02940e04c101d0b0100340c0404100044529400b861038070004181d40302d2038400191410070940e0021514842c10300c1000c0c81501c0b60300c1110040e50005443e00303400020700c80045c0c0360704076a42020143d808102400704110003180d00010302c00c4001d0f02207a484a81d05d10880303056a17040203500c42c032000240800303c81400c00345105600030b4401c2060f15001d1031003002045450200c040c05900081c0c900704100402c3c4130081c01c0000d02080c00e82410b140600c1511401d5030755855104040d805036000401100c1d1850703000292507543c402d42d805000242244001c0248030038040800e44483c080d200b00d00c001040b2400030b2108400302c204141d440c0200c00452114165402000c1070656144c05000304800070b0182f0200200c4000078084000c898241201c8008903010005100b00e540002e034403550150b038000000031242542484c0116040c1d883c42c030201e001d002421414456801340c40244807003071032030301d018 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 794518210 1250 794516960 794516963
    0x40f0308130f050609090712110a0908060402031c02070807030606050f010c02030d030b0301090515071b1a090a02040516030b030102070b0f100e010f150503070e01050d0e03070f 78
    0x8954030300d511031074001e0a8842c00e00c00c1e583c0c0103001300816103450500360346135a4005640d003400400040d04c04075203001d8810b0312240040174000000e20400315600040c41202a0402c007005010601d425408256107a0104880500e10000e204203100010b20070000d5101610f007210a5500c080e65a01d4078102400041c0a003d115205284400540e0352003403120744611900200100b460070401a0180e00500c55902066015502c41d201040400c100f007112210270a440e1200a400c3d150040b0010300720b80003a1400021070649540000100f4403090380f4450715480d801c2c0d0311f8107980b030f104081460f0800f1404001d4010707003403074100182802d4011488549428540341844140d0240041600300c2c070424070020000b14625000c90008441580e0280d44203130140071001006890b060f015441440c00da0001404c42c0700c504040c081c466800024110801039400c100d811400c1415000e00040307103040d8000e040140100702020035141c0c94000700004240802901e5550015041c1070f55a148100710 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 794519460 1250 794518210 794518237
    0x91c05070305030a0f080a0504031e05131205071e050f1f0905041505010206160c02030f06060f06071a101d04060b010f0f0c05030910080402090a050105030a0b0903040f0308 76
    0x341700155507000b230a21659140e90b41401051016a0080c8400b00421602e01000014030505051000f03800d0003201400d512031210030f984102c1c2c5042d51419800303820000c482c014050040b075410044500c0001518400c4130659400d00401000c9030714003078440788c422101d1101c0e84140042c5500f1140305001c4d15025141400345440380303416400c2c41c0b1346510405005910650009403400180f080081c2406403918090f2142d02700c580020b1310b050107002030320310075400c09028080b00389803110302c01c01603800a80d83c4900b800d5144c1c64200380d428450b4001140b82c4814070000e10302c0100c0214010142645000402d09444441580010f03524101c904442851074440a40c40641c011900d030300c0b40e03107a55550050440740c011300448210902600c00c94151100348174014050b40d5601000b5007040450303540d0002450701e40100140f6100c00b420585200740b51000620290302c1c04100f46481c240c0154607481c4c3c2c0d403200c4d001145944250307484602e8400d42250b022080111084c01805802c80c01038 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 794520710 1250 794519460 794519477
    0x1b0f0c0d05030c040e09070b0a020d0215010510030902040b0909010632060c030409060e0f06041e0e0a020d050606030709061229180d020102091c05070305030a0f 71
    0x400c00d0710184800e445501c0454001d010801c01e56414074001a884181c82003524001540c4401a900039001021440c01503041240f144080da071f030400640341102c0d444030007491194544404180113881030004c4000305516807002c40c0030b5443d00d410517400c40001070801840c600d03000716070900810340c0d40126500c3c00c440f2120b48a040b8480704005030b02c052000e6803881128016010844a98005032000710140010b0200090090076842414004c04448214130050300d4811080c0c01d5459005004503c214070304860680b00c441e400208000b000100b01c000140680002030241c900b0000c0c41c0000e5201c0482035205c2c0801c0b0020507954024903050b000c4500d0551280700e003000b50b40c2c8501985100746100030100020550b04e040004100d501c04003100d07200f00740487d0102c1802c5040340d00614501104460414102c420002604c0c00d401c00d00c000c6040140150000d0b101d8600307901502c00c0e41002021090070710005110030b40040d0340c040e08803036561400441c041c8c8400c4d00038124001040160 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 794521960 1250 794520710 794520733
    0x30f020103181b14010810090525051b03190509010908011107050c01020607020606010e06190e0a15020a0f0501020c0d020f010501090605010c151104090f050a090f06051b0f0c 77
    0x580400f4010710280c1d00c402c072000c0c08d000e45d03a0020329000700f1081006900c68400c0054240150050065501d0b50f1b4806548407500044808011416601c1e00750a84c010401c041705004000f05d48a00951513250999a0311000401281d402219030041340055103000a4003003e150640d00501c2c8451013201503501a00784000166110700742180d008015030030640024582d07600c210070b81602d02c2d000a1689040004d015400c02028803021110004035940e854401d00ba840c11035150b000901c0c400e50048050f602e1004000d4445e0096040105480c010b40010b400f081002c0d0180c5c0d0121050608564080500c00002507807040c01382a0015503500c3d0100210700c05100c2e00604007981e0042e103690f603000116076241c5011030a6a926403000c540c1c1c90840c4601101044010001405414404140440c04241000440300058400781d4130300e14000c1584002091010010500d5400140005055680d0f000d003211490300c5c4550078032001400038050b03a540000c403001c1c0400c4601c1c00110350314245071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 794523210 1250 794521960 794521967
    0x1401050f060d0b04090821010b0f0a030b0d02030616090506040b0a1101060918031107150f03180b01080c030606060f07020f10050c060a06030f020103181b1401 70
    0x22a0304a810540402a9001c010869084200205009040003c6a10440d200c810607078000304d54103c910540901d44030b5032080d01003100385c0900b5402c0f09282c0307480c10002d0900650300c80ca07000744003803680b60030490318907680308080710780c5550b0013405661640c0303020b003001c1b00800000c401603030109207038100224950411100340d406846000c4421450086a00c0041d2211110341c4d00300c402640d03c40001051000d12401481400344000044140391451850040e0000c1411020001183e10660040000b02a00040b02c6981400c5007070002041020843c124060000c1d0180d001d104810f08004004101c03c100c4034038125023100d41518200c01100b01010780742c130011385801d6401542031201c080c10403418402425003e10081030300c4d80c030400ca440464a0003010040c0800415000f1800d68456201132080c1c650100ca0b40b00100318643c1582d640701204621a14060f040640d0b5883c92083c9c848603500c0024542d401103a48030701c69044010600711441e040c0912304080825a808080035401b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 794524460 1250 794523210 794523229
    0x103031815050301030f021f080601021504020319080c0d09060e04140c0d0204050406090b040b10211122090c1232010311091317040b0d140105 63
    0x1607942c400e4516482c0d44c8443c0b19070003046009a03840113030100501401c0c55040381c030700702c0c16100c0e171211103c41c5402c00002e0709248803049500c0c0c0d0048104104401a580812400081c10004e900e949181c0003501700311840340900304400c0312612071065410700550f041010282100d441d55900150821075005200a44054401c180e02d02c1c0860008a00030307000000c054054040340c00001410a40d030780700040c0a5802079482940c64035500c0d810503407281024052895503d02c10340d262250941200e100400c0c000845070300c1240c412402100c01c00081c41d0390456120040b14444161300d84015103403911366150340c400c0702c9560070007540000482d050345024482034085292190306081c01c4c1c0088000140c004007059007145220404004012044104040d103c0c80d1280141c00166066140101c40304605210981c40707495007204020500f800302e045040708aa00a88858400c110601d0712603a600031707508400101038002c201d81c071000d483d80d4459007854180c20800700c02c44e41c2c0e03103003405002030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 794525710 1250 794524460 794524499
    0x3050a0c0f0e07030e100f050114100c0308130605040812090f2d060c130f120201030b010e100c0b060402030c07030815090c0c1c0203030105100e0901030318 69
    0x500c860004150f24042e5004440d045003442c2520b608041c00d40c0c01e40d04441054619085040da90700c01440100f602d4030083c00280703070550f20482100c0041401a11240b409400101000308e86030001d40c480e4000c090003094154030800034802c40c1800e140002540e04050800100c070220200001e244100029804003034020300300287c0359540751115103040b000300c1c2002441100004400704401e41c3c008221443c45426025080350f01c40740c0d010040d0312458600d03442111142c080c01803c0c00441d07042c048008640380d0908001420000c0e41005030340403111400c2080c1c0c010310610103504050f0700305090f6901c5503c03410300c80300c0caa0349100030001207000a03105143c0a03030050051900082c0100c401c550401c13018000d440c81020001c00103000c0c160100c3d0b0282001d880400c0c3c032900c0d003404221845070340700e85503038036202601d6080c40250f403400305208141c414144004e41c07400e128080c0303030300c501c4402010702500074940c5c40b42006045160324003041d544980c0a010300007201903004c482d450951 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 794526960 1250 794525710 794525729
    0x9060e0114011701110c010c090b0f0f0c1e0f240103030503041703150a0b0304030c02090c0409150314061015050d0e010f0506190e0901021303050a0c0f 67
    0x20b90070201c500b00e460380c1c6800c80144030340d664400b41010300d4110b4050426030056400101e000100c4040003801e1841c1c55020301c0600c1400c0c444586146070610541300814502c0c0c0742681c90380c4041031030b20305d01035030700d081010011010138020912120111303080c00f05000300000c46405901035414623a403611502009074101c0c00050041c0000fa00c030300c00071030f04103001c0c018600f00000c6058568129500540e0381c0e011002000c4024215410a111a80000e1422520050951500307842c0908001c1c1e03034407002885040042d002440d488002e000340c4000d0182224100040311425040c00078891490000b070700e070069450054101c00b100020300c54070500818023498403140c68030b54462400700410700340350203002d4144405000020a40310b1150408803c0c400441c8074003440c1c8009086031005044140200740ea4040302e02d94100007a80807044882c0b40b0b03900a035554480c0301c4c26009000d44154100c0030b58480c0c000205214002500828183c0904605441e06a44002c0141840458460035102 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 794528210 1250 794526960 794527001
    0x50c040506041e031202030903010c090501050304060f0213060305060415060f050a0c021f0905030c0d030e1306081501050319060903020c0a08030a091a0301210503070609060e01 78
    0x20f500815000c001030188043d11401a407641e681e01100c10f40c1019560040c2c2c0081086400d0f032500f40550f04907030300c03141003001a0710f092100003405440001d00181c2007503142c00243c202e008095049900200442201c0b07a00a03403502801000b034074040c1d030141d102e182490340340404212070112850440300d660700d42d8034a000700c120090740c00740c00910400c6c091100c10000744015031542d000b990f01301c3c034032101c02c1881e00d81c14542c06030000d443c1d508258041e41c8800c00e0f85600d603c800c02100c03c00c54040c10101514a0b85000003144c005900707528030f80003400c2820000344200005621807443e50012207185843e03072104249075803240d250217844400d0200c8003581010441c5a40b1404001d40284107450511020b039000c505d241c14941d1040040d58000074045400b40d90180d406000303007140360f010b0392400a1090b0a07c9640c0010300032064110301503008130400d04503010300e115001e41e0041c00d40b42c5814113030800fa00105144401a201c05050464085c2030b0314043c82000410009903000069 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 794529460 1250 794528210 794528219
    0x10605120a060f0303050c0d0309083a2003060a14211e071a0a02100f05040c060e150a02010e03030108010911100525081c050c04050604 60
    0x10030440075000900403a550784022510040310078001020b035000e130301d4007680c655106056514041c580328921082514203800764000030118012220360b0520f0300800c0c0703584d48080b00c0c0117458080c0c04a005500842c041d00c12010f0400e15000201c1c03846110042e16600c610403544440184422105144c0c41a040e5200b403003c109402481d0480da0000340400305035503d02d09550f607040e200d59070070351402d40c000071807034245004105000c2e038280225400340009a2904100422044010803000c0440780042004404a4800c20911040040040c014003024000c00140d01c0100b4050740c00b40c80800301e2060108cc242e02901400a42d00c1010f04001e241b03500c0000c04940c02d40056800c074046540714800025480b0041020b54080c000510000410310726078903144001e03480c12a0700c58028100881040902904001074400f0303900349115030054814184007054840c0f0b03001c08010714244000c54200070404a424240980c0d0485072800c02084c0c45900c03851500d4002d911443e40d200d00200004e01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 794530710 1250 794529460 794529487
    0x110706030f1806050a18020f06070611040617010b0306031504061e0e0615010206011202010c15020316110a02010309060605090705180d020d14120c070305070905010605 74
    0x81c1c10411a10700240c1600700d0703506880da010101c1c10990300d031a101e2040c41040100c51107248400035400040c00f0301c913545540410055100d005030284201000f003003ea0034411030707401c840c140158134030045950b1901c0b00360162124201c400103035140d158440001c1221200c2c88200c80c01400001c006020681c1d81c0703a08070001400041040b501caa0b101c0020b030172444180070001075101a050760100c2d545103065075076031424200a0038440c5081078000c52641c81e980100328141901c0c01c5101d4a5072152060005903001c840c003510040c4518003c20314500b0300c01c150350195014249042000340d445040d000119a6061002442d40c0e1540140380703170a00641c06980170840c114840c080204405603520000b4000070400c41e861004983c2c0020002080412000a10868001116079102002040d004143e05405814000700050302d41d0740302100c90381c0200451400d200c0341091389030351546002001d50302c6455034401120305201e005c502048141c003901556042c1c49041d581c0c94108a1410300c9030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 794531960 1250 794530710 794530721
    0xa1d0f01090e0421050a021009030e130603020303120604050f011802090d050109060209180f01091112090705030706260601050f04030803041e0510020a02070e0f1611070603 76
    0xc84e030011510a034148462800611142102580d840e4142c80316110940a401c0908c0e1101c10b1001e00c0c90059140300090300010860650001550040d503045030b46d614140040c403081d040a90b040c4400700303104580c11074060005104400556040c481c548520341c241040b41c60130700645100e2010600310440030f040b40e5001e0f124228005040746400480303600c2e010300f11111104151101d0b0380003e07001842e0709140008241c490510842001203150503001e00340801018010049144c0d01c0f1502440702c3e0f403900013520002c2168146070101824a10b200b160b4880c158404c1c05d00074014034900180d268081d241302001e006401e0640344a50391240102514050f00030009814000f090188502a00180c40580041c6210322005640c0f400c2c6400c1411443c40a0001d0201100c100401c00780003880210742820344103c1c50f040962a0742c00c2d06800d82c18a41c06400040401042d00104420400c20208550041c04200441d11002e0f4210a0840796406801e41905056020724020410148680c6c8030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 794533210 1250 794531960 794531963
    0x20303042f0a0b03180d090306020d02041e05030613051e030412030f021e10110f18121606051e0d0207021801050a06051e0a1d0f01090e04 61
    0x1918075040d0110005610582942040c51448008820019400c0b0031140c4070310011380c03c60050440c4a1100001055094a400001c10041d00420180c03550340d510780548000e0044601002c80044000e14107a0500e4aa071140030f01c03e01c01c08020800b8041010440c55440382c0101c0901002901c02002c078002c038002c841400c2040c4003c000004180380403030b4115075454070070784e40c0c651140705030741c030092600a1038241002d01c04401c031080d840034000003d40180c151030740c0b0380220701071041400400c000e0081d5821028070a200007501c40090102425a800861084545d80c02c0c80082e000c02c030b9568030080070507811402c002c04050203024001c40107080c0c03015400200906082c0c0c43c803070110b0190080400c00403440d8000c00c0e40d80c00c501e8100c1400c01559024101c10b00c035985440c1c000b6401220700d11620013403000c00a111803500d94545915140011604242c542d10103220780010421185e804546000405010200c00580f400f082c0009071102e051f51100850341c1810f100c1030312400041c20 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 794534460 1250 794533210 794533283
    0x3c05060405271e0601080c030304050603150a09230f01050a031e060c21050702030d020a02010212100e0a1a0906040b03120d0c080919020a09140402040c02030304 71
    0x40d01d4a040040e811601d0300100c4043c0600301e154500300d600b51411640b80300309803198106100611158407603100b5260320012291000c80703544204408a01f000641c1e070040c01105003060000340b00c01e411203100d1031100703280300040203c5a0f2007a01e2401d50000a000342980641850700c10004501d00500c401c10301c5918840d482e0348282c240c1d6922049446040804012440200005400c4031800310b12741c20b00107401c48140698a020b500007074403445480c0142000c140e0200341a0020780c03003541592401040c90302040303030900b000340b4942c05059084c0710350070300414070900180e0050254001c0359003094224030158001d506190800c86514001808203810543e5208003054030780c1c0400c030216800c070700d000c002c40c3d45441020f07040d816034041c4030300d600c1841111002d00004003c00203424402d41c208108850780ca1a052000980810095202e174103594180003101d103001007a0481d1034005c5100312010007510a001031700781c3c2c69002c2158041c003035021900c508120081d0960905120313024204 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 794535710 1250 794534460 794534473
    0x5090601050d020d050f01050904120f0c020315100f0b2a0102030a090b150a0e06010302040305061501180510030504140f031314133c0506040527 64
    0x2c075000072a006400750021054a480c203220360691048942c90140506560242052400c1c0e203440300d43e01c1141482c0d10070010100440e02406100c2c0d030700d108160383d0043c1541c0e01141c4003249502e4004083e144507100d00c440100006000240410880460b02d04030446030600d200c201d80e00e800d0254114810551039684010820381c2d81d8284000c6104995103000083c0300c02c1c0a0a00d83d829002c02029542841e9401c031a071881c035540c40441104580680c50384100039954980128040d003e81e900040485c49a01d090020414000341c2e495000302c02aa02c0b0f076a000045180120008080d109198100c1e04400a00685512980006c1e502500455554110040d00c0c2d400d24505010142c0c01c481d15000030412071414668408004014804080381c84d1030384000400080781080780207008035050340c0e210480c0c05190ba181d460818412406943c503003590000007507940c0c9800440c40e0b90800503240c880042c4861a16114043c0151107142c030300b10141c1c110801084941c010310821080324841c40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 794536960 1250 794535710 794535727
    0xf1b010207050a030b150a1202041a09090d08061f03050402030106210314042d0305060c09030d0f020601050f030106030f1a070203070b0a1d1e100608070509060105 72
    0xa4643c0300114071034a03244005141a040c2c00c90540208042c1d03a1040551007810070010700008400b81a050301120b0026030b48a00310410b464042000c02c0b1550400480380411102d01c2c00451051a02d482645513400c00b0b030340b42001c01c1881a80b141d450b81d400a203074030702542d455201e54400da5200c1e102800000300d1a84402070556180b100c41320380140015485118410940e115410540600e1810a1941458240500c0c185062249803928100b101c40c54854640d00b038503188118025904203040c0c4406040c030a0080b0b149903c8890003500910500d19001410352050030f0701c045a24082e4094025642010700304015400b440038110341c90341d201e900100200f0910070030755041d42d00c9040d20b402243c440d943c804403074110003442d101c1950001d00100740412110300145500140c0a000043e440c450020076182070b40c3c40d001304070707607a100c2d00c1d4409500f05c4d140450459000c880100701d81d1112b00c09038508054902500806440c0c0d0001c1c1001c0266003080d84015410281c141003450405012 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 794538210 1250 794536960 794536969
    0x90604150911031f0c0905060724020a03050f07180302090a06031e0314030405030322150902091005060d0e01060b0c0d031103071704140d080405010e0f1b01020705 72
    0x15242004030302c00c3c81103840d5004c00340030300c40c04d00f46110909000c20700c03900c0c0c00c0000304540180b85c00a032005401142d103210815010a0880700c1c1801c51030215145d000d02240180107102c101d40c405031200310030300464240e901a80c51421401c1048922195480c19075007403103d030501c0079120a0110b0b0700e4100c00300c00200c11600e8941462a180408007a409090400600d2261400e1f00c04100c038078200148008600b02000f1244e000361203100c41c001d000c10540d407420506c04110805421040824000c480c0000640c200d070720094001c844207001a01c0c4c0c4c001c004c1d02040c8c01d100321903010341d04000c00d40702e6001507041502c00c0420360000146455480103407000a50001d038102225070015202c0c9402c03d81c1600c03d011301c000510070306909518009102510000c02c0160300541ca01540000504106000d00081c0301304d06400165a4903400c030f180c01403c2018155030440783c550a0405140155500084664410942000800d0340b801c07902c2103d03c2511b45041c60504501481c40042055201e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 794539460 1250 794538210 794538223
    0x7140d0608160e071b211706060c0d0815030d2105070c0f020307210606050312030f040c031211010b01020106063501030f02010809060415091103 64
    0x40400180c10b81040140e001c541c64265074003c030300302103188070034440415401005031a03200a1410340000300f8003a03082000341513854440884002441003414004a940940003034400d65480d4800c80a9031201801c000c9180502904024140e001d55820341f1600e01c00d5022640101350b20540e92000d88100c0c011a080000004105000c43e04140c0c1e200241440c4506c0d01000c0c03680759108001c682000c43e0005c0240310f074080054204c450038513800c0c1c1503690600c45a0004e001b05069040159129040ac4184480c540342c00d8038500d20b00400041c0500700401d40403048942c0302005450b6583c3c801c0e01285032800a8070030b80e0701000591000c0300280503181408901009a240d1101d0714001c2200c01d401e645a485602c0c1c11a41080801c102c440d030000120b103d04107140703620036440038012220040501049141c2e100301c0b40594000001c1c0030341865240742c1079000783e0b520415a0b0312920b4450361340b50b0640340148411040c101d081d1101784107a002c0504544100c0c600c1703040ca844807000034039010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 794540710 1250 794539460 794539469
    0x16020a090207030c2d0b0c1b01060626060409260304021c170a0219140f030f0301051905120c0f0d0201021b04150b07050601090e030307140d06 63
    0x1481052500184042d0103601030a00091782d0891000c4400c100000c48000c19201004007490469404100e07404081001d40b404484100e040c402c19015035800307240038004a1242c2408100060181c1c1c911607800c503032448a004030001ca21865460303000078003000384601c0d9003c1c0c07144481c40d1120b401c1042681400c1c49e202a007400365035200e040500400502c140505002101d80201c5249c500000d42c80b010050340701c3d005461410784528120030309034144141c150300d0340069013002c4c8003002000302da034982c1c00ca4055000c0072034102500c0082c031540d0300d1145110245d0600024001000710b803621002600d180d03007403034415004482d0341d035022800702001d4a88486581c3c0060982c207045080500900c0704e10350382101c49011184458002039100c24001a01200740d80c0460300c524450b460361340090324005018075916009030380c2e5250154040e08001012a264040e8a0002651000d20300440c814507020501551640c0c40d5603106484881e0080d1181c05d29600910001c0440440c034882c400050 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 794541960 1250 794540710 794540717
    0x20a050a1409150d052a010c021504080a0b1008030405060f0f04090c0329010c03110a0210020d090504020720012a02033f160c0602010e0a030516020a09020703 70
    0x2260401c0440c01342c110600901c0da2100103602141c249603034007148c3c10b00107a4040c0c0f0603030003080404810441c244960b070820f8400e032090000810400c020b6841443c814004440b50701c1200d6190001d6584a20a40c4540c0750310440901c036001c1404001e030018143c031481d0255035450030b035450203183d05640c0700e0380425010954400c2c40361103070740a08510030751040785e07030b481d08450038808000030b441e1f06045a000782c104002c20104501c1540100019101180c0007001c00d141c951a80000a6440821000280000d01e4014000031a4141030094401240c1e0040c01503c0300b00280240c44441603640c0021410054404d00c2c0800c65030780a15240b80080007501340100340342d468014540342c050900d1010940800c01d081e03191200040d0302c2905040e240841e9984c80344451400818010702402c459280c80558481900e02081842c00a00c1d00b12030454000b403040c129414003550b2949375103000a408108100030040420b07544d140e800c20b88520040440c8489620b5001ba20203e030031080048020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 794543210 1250 794541960 794541973
    0xf05090a17040f0b0d1a062d0721020c012327040c09030b130f05011e0e06042003160b030405190f08280c020a050a1409150d05 56
    0x41006400303020f00a020f906c00c9154440d040201043d400e110b508950b89409030742058142000451090600c80c044120140d10344603035982c1850085004401c187e6410a0351151207a541a800400c20b40d03c4204140c42d040d2001c1030100040d2030051454589040401081084000070030f5180e034908a8550f555050300d0700c080381c05060208032079404000d40f007480911102040000c01b07404c210ba40c00401d2400341540307002c40e89800c2d015250a8800280076508000522000c4400a0f45d0b6280c0c4489582e4207001d00b502c08050252100c0090382d02800c0312100e9150703410502c3c6005045200342d000502142d0110340248125100840320340c006400301140082440107100c001c002c0d4007144e0320b150180c5003410300182c0c0c402401d0000554018510100400c0c401c2c08222046078914111074070101c40e11840e0405480140745040c8140203e225551800300450241021000d030f03400d950501c0461130b0140a00b41c104042020020301c1100c42041c2c1e19110f1001e03842c0c00071040f2000380310380c0042c0394 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 794544460 1250 794543210 794543227
    0x90a032604140106090e070b0d06030209040f1505060117091c0804120f0921061d010e1f0e030c0d0504090e01090804090b12010606120f05090a17040f0b 67
    0x9403040303a4001d14825003402c407031b64000a0302040c20821140000e4041d80d440880d00c40144c041c10040e07201950081941c003c000c180524203250802c80d81c403c3c0c01604660360721615502c11183c003550003500040810030030350000701038482500e802000d80d10449104c0d045074208100003158402e17640000429500610082040c4000400d05507407503401c080d004d001e040c280003086040c40c1d1007004022a09008155034480204030038952654001c5418800070103003e13800c00c0025005100302400b1f62900442c8407040b80045602e51441c1d004c000342e82c09160347c403000d0002820b070181580134a400200441e40904130304000701742c18a1203a80b140d50301c0318030b811042c104a90600c888074505904109603280029031003c100c40a07101980c1001400036a0300007ca000d04d40160140c240303a41c60100702180303a9070407101035900040000c030f00b485940c82c05d40542702130742c0742690034070115404035250100090f0180c94004c120706000804504040c1d550384a10ba080c440c0740e0040d030348144005417081 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 794545710 1250 794544460 794544463
    0x9030705030a05030919090c171506030a09060f05040b07180303020706110102071202010e100207021305060d050115060e03030720060405030102030a1a09090a03260414 74
    0x4014001107000e00151085501ca241e16886006056482212184e0111030f0b5031004442a802a02502504006002459a001d0b089800140f40c00061160032070008400760b01c050340b421074985005d0700c6141541c540c484580003070301c03a0140c01c03100140c4840d00c4102e4160b09124052045000da07103030302c116042600c2c02624085559241885820703402c041400400d40008600c4d0813034a40c0d2619905c3e0f0410402032070700900914000030140e0303002c0c1c0311070320750264150014000b0040381d4080e1401b401c6944c0c038001c201e03c90214002c0d0051610300001c8003580081d0720060b80b00801500c944d22801040e5600c07400c4070500c40f2407100c4c50400200600086a002d203816500800c190000c40c5800341d02d80701d204405001c100910000d03041192021041e44400c0c055600800018000355141e0404202510240c6200c0c00314081c842d088280e840101d01e00840e035107004980c0f50014154032101914100c40d80a14144400f2040810065184c0c8030000551100d202c1c80c014002510000f14004209 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 794546960 1250 794545710 794545723
    0x9040b0f0c04060807180b070501091202030703120f18050604030206071b061a100215060609060313061e4a01091202161a0702061e0f0903 61
    0x1000c0721103082c0414841c0300d130041c100c1504a1241c1c1450403440224400704207080c4c80035040138884203004600b10080182c1500454601da12030320701e100101030013074402c998034003807400d02800003005220b110001c04c10b80d0340201d030b02d244259004a92014800880c042183d007403882141ca6520880c05c0005150b410b1000b03e421a855103043d10340240380c514171103141e038074040300a4241075031030f200d403102c034000042c4ca8000795801030524418164103400181d1076030000c000c2a0618120790000071420701d440d004a601014004051604545814480c0d920196448208440325540c401c01050100c1c00b114040c07844e1400da26003c110500020044403112903030203900b41180c00001c01190440ca844448202c410003444003405050720004007140c05000d40c4140948441c445d0480030324980d502203030a20541e0940401c1d03010080d95032155079801401c0300101c000480c0280821801847c019000701641c0c165002040a0143c01c1c05802441f0b60012a02803400311000444800c0c07030406000b034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 794548210 1250 794546960 794546971
    0x7150215010f0f142b020f090405070e070203040305030714010c0c171e0a0c0b070807080c0a1809020a030b0301060b0d0e101505090f072a0209040b0f 66
    0x22240c800d1501d02c8060181850740220000031400020029440e25545c1c80c030308194a14031403241101c0b58501c104a00e03411643d8003039010310200d21f005401130505081c2e01c3d004551210007005154901078154480c0303140078000c541103010400c00000401c2003000a004118000d15010400d45400d4802d10b0071030b000302c01e003007050041c6c4c0703110040854000000210051032601d104d9564203410b03030b1441e0407010f5a001070280942cac0481d24000c013680c0710502c1d00c03080e0700c02e0004d4221500c40c160306903120002200d602000440941c00035050000c041c4c0a04030384200c60070402d007001001210046841000c1d00301111043d40401c0c101c040a5060103050b01800e019402048560300b40b91030701c28640b2940c27464002c81600c40001a10781201041602c41c0d10841580c20403042040141c070440c0c800e021701c5154071454408011071201c4120048880c00f070300041c0c54803424110141c0d401440d44c40f5804885c00e03585056080003000d80c56400744184210b204010107c0c50303203011020102c049070701400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 794549460 1250 794548210 794548229
    0x80301180b031b04110d0e0105041101022b0c0b0717060d020609060a090302030312010e0c03090604020111010219050304060c05191b02120109060b040513020409050715021501 77
    0x1034040c0800fa000d003c01c2c511240990f80800c1c8002294071031600e500c140c1141868813483e081403c00744a006502280c0506c1c03149c866018007401c00704c0126581c0a412000c24640781074050003014802c15071100b1103c034051420140d0440f52140c0703a5280994040329a40041060035010000388003d020115921150032908400322840c0742d0049003040c090780c4180303070040c8030010340d00c10910302401002005540c02000c4960b030b00c1002c0a04100e10000784100c0391030380400000b0a40c100390100c103480c07041c450f0400034242581c69400440d000c020812020f05155420400c00b166020000c2420f8516501600c61640d40e042900d416021075011a081d0801c2050a000d040700c942c0007013441c1313a200039052a140100b012400e120a62058142c20b000394440c2800071035102d1030070f06400501205026100c1001001031100c14042500c1e400c507265624000300f42ca007480140781c180d200d002500d0280c411a045151100d01003810084200003840c00341e44411901000c41404969030b42c050220f008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 794550710 1250 794549460 794549473
    0x12050601020a20091602030f1c090302030d05130f08070f0c2304020a021509030d06122901090903030e012301060906020706030c180b031b0304080322080301180b03 72
    0x17030000f5100c1c010309840030711013200020071550101c0130320300c454045100007034100020041c134507000c0e54035800036409405160a010004018024000640848a03040010a4078041c00d503540d401c0079510241d070032944002002a01c0b804291050381280c0680180741100741c014404041c0c40e0381c4242422001c6106900401880c1c04442e40401c0ca4003424580c11000d21040d125085014118020820141501031406000040711280f10701641c10040c003603180c00e055403624500240d00d8002400b402055012130707100401a02a40f076100c02500c03400703850002a0010038138034490a407520449400d80350b6000c44031441d4210204022540100720740e0400025481c540603000c0d44078402c51084106156403110186e00c00c602039100d0090b0b0405214410705020703142c0c08800340d1030300251000c0526081c40d00300000c003040903900301c3c2e0080760004480c605503a01e0444802400890091145d01e0941020307500c0d00045102c00654007a12070040d400007140d80c03d0f81102e00300e540d0645464401e03030150 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 794551960 1250 794550710 794550751
    0x406080303040f060b011209030504060905040c08010e18060a06091d0a0f020a0e160315030c090f110a0e041b0e0d230307050f0c0112050601020a2009 66
    0x349690311a459020101050030301c0300c5170068a2070b0f10720307284078502c1c241090092030070164040c000b00256a041d440b51070845840e441804101c52460040101080b0500014801000c7e041c8101d50700c110b48142c001d000500c4500302905054080e5850042c95403100e03420304c202c0003079004400c0303c0a20f82220500c440c03050901c0695460b07140001909042c02c4c1d449900554859002c0c04003d085256600300c41801c00002c580008580407a524000924080d058108042140000001c0703d4221180c04101c03030920112070010810780c40b442251603601c9159682100b40d01d005005860140d8841c0300e2808101424803054414000e002910000301c041c40702607485d00300215080710303a401e90303418000051501e0320342024078190004880207e0044800114540008000c080861188068035408041da041c00303682c3d00364080400f80070800c0300320150200b1a256208036481b11051040700d44403045625040340e0742511003075a50030240690103000490030705803180394220008880c83c0c00b654101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 794553210 1250 794551960 794551973
    0x102040b0d0605091312050304030e0409050a0506180c1504090e0d180501050d050a0f060807030c0806220c09050a060321050306061605101509060f05040b01121a040608030304 77
    0x80715010021f101003c0042001e06104044000c605600548208201c03001c0781031081d80c1e15500e00c03084625100e0791001580540b0303100c078420a00307090f850082c26240c6419040001d10300f040c000c0940b03080030a110020710740b0790038090300c0701500d0311101406801c194181d00401e18140384060340110640010100b103141d81c01400c88151414002c030000c0e4540366211791401404c00506030001c524206140462200310100c1c0b00000c50340b08044034201550381d0300b0755a46903082200d4600303224050458600e03016401030900403c140c800d01c121980c6645540e40741007142e0050351841c41095581d0700620401081103071840c00514448404041d10741d9408001344180b00052400d401032601180900c1041103003401602c1c03043d40001598031900d007803083c2c000100740c28850800c0c00456102c000a0103072180c4964400e0302d04c44040d1284080c02d040c140301c05000c0f007246090410100d41c04842d9440124852150000a4119500116101c2400300001e4850542208a0540041040c40000b852 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 794554460 1250 794553210 794553233
    0x16120c090b181801080f0a0b06013207030e2218020a030b07030b010f080c1e1803070504140a050402010212030901020903011506050315030102040b0d06050913 70
    0x74110589039502081c0440c07001d070690725401240c00060300c0c03580303808610340410024180e404240888a030314241c8111190b07101041c20003c2d10324012080800d089511800c0a065034a42164a4810302400c540101d41607010355450707088440b030045109002c044c0d100c0340300132403000704a40f81c05042c040010b45008074107403040814461030303541911b44031650310380749096030454004200840b50b640d203040c043e001c2c9104940a800003850440b0750480e035030151101641c0045039a0b180b80540e6220140c003d11680241c10103c00d6181c000c80e00e140450111b001003d22003800e0700c0d0801404014130a0501e461420717041648a10308000d21041400c900007041980848025004161519140010307820143ca012072815100000000c01c01040700540080c14841d0b03064000300628500000090302c0c9071114050440054020004550888068101e0800000c0300400040c40c1c1035071910034000f258040b1040d01ca01035100c00d400c02951500041c0ccd25400800740c1b100003d044401d6035442040c51 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 794555710 1250 794554460 794554469
    0x330414130f020a0314100f12030e10051215030a0609140a0c0f050d0b0f060406180603031b030e01080a020d110d0b030c0a06030903050c0616120c09 65
    0x109468085060340203030760040d900740d0000c64802c42da10751503120010040c1c00548420701481e00c84c04003143c401d5500045641c01c8030188140759070301509001c01c1b06881030901c0415420040d001c036100b002591106050140401e494440e01d50b100180468800c80c0c40c40182050070701c07544003201903044d450224101c01c01c82e038040800036064084c1e103006540702c00d168000f000340b4460207039240e0400c00b070740600c8015500350111114220b5074507001c2080400c4c0100000f01070303130f503028081820348810100c03564220000400104100d40c0312000342c8940000d01e03450320545600d0305000c000b4150404d901c04080c000601c1c5c01036a00b9030a4401400b12000400480c0c100510800001c5039001c8940c10b445000808480c24804103001002c0000d00da00000c031080486c62800c040d000080c5070000340c070026007802070300318400d003481c00c0c100340c000300700c001420f03824030004000e055031110003400032074030900c0c04c203400b4a1090426140100a010b07204880f170a0189801903080b502034101c94000c2c100c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 794556960 1250 794555710 794555719
    0x2d010f1a04080706020c011407030203091c060e061501020f070b0f0c030d020d0c02031206041a06031303090b0f1218030c06011e18020702010509330414 67
    0x302a03545450540d0320695010400380c2c0a034401c08100c03643d0100c0c050611150990303030b20b826282d030140c00c20201e20900304010090b0380104041c80e6a41001c0d5102d44c1c813660401700d90351140005031038001c00d541d03450162007001e4004604101c1100c6c415041c0d0840c00b2004c1c4000c1500c03501d24805d15507a05501c0c09441210705001ca81c075910141c041007190798103000707102601c1e243c810340d0141002035003040700340c9400ca41c1400c5141b00c0c818030020079680403403001c3c8054005600c4640c184801840d002d80b00c0588030902180601d00340e1520341c0114025010513050a80468050800034030014040e0040b8180d100104032100584c1618021f850900d8481580362016482e20040d12060110200104255000c042503070001e070800420740380e0494054a1541324218038601400d100e400340d038081c004456042c0c000c50840741c01c0b1640a02400340c07060401c549071030f243d000050410720403070000798800a48031a4000d501541616411221300390056410b04290030910403108160503002100d004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 794558210 1250 794556960 794556989
    0x100b07050a0809040e1b031c080a1113060915030203190507020a0c08100b0f030304030803041a010b0304030909090f12020a0b0903130807030314030a090602032d010f 73
    0x1550300c1c2e603c04400c0701c1d2040c048605054004041d4911120f0746e9800510a00441d043c03000403100e01c6d5002003610801d50748056041c2d5556424000034940385400c0c1220309000d01c13140c1c00c000d140c1300c0317001c020300a540c45500c186440c02c19440c0c0c1c100c2c860310008003014018010301050b84d02c0f0403100b00c04100718180c0440c15655954040703140020812000d842034141c00350008280c3c40c082613507000502c584105100c0e95001405101030f58100000050309070340104002c101007010113002e55080b5115201c8181e416400394882d1421400c280c00650381000f001040c04205604014000700801001034140041c6005840d85049071540c1e09000e09101070b80c15072a180c00303100384142c1007101d5000038000e1642c106140a40c0d13894101070360030800c03019a00030100d100722000480030200c030f6240d0350300b03810841034082004140e000a48101c5d0540d4840240d44e0010758540083c520862954200c0910102c654504031100312081441d5581500d8550040c0401700c146600c0606a40f8509048020b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 794559460 1250 794558210 794558227
    0x10b010206041e0b2d040201050d0c03110f0c07060815061b0604120f080105030a030e03190b0403080c0720010c0b040f05060601020d090509040c05030a0308100b07050a08 75
    0x2610f00302e4a4000380480103900402820f1074045500c00005820480c03000c04941c1000c019a0700e00380141da020380801c401380580001d04041d41c00c6010300c0c4800b8030b0f002c02c2490002e58034025070f40245104045c01c071004a4805140f41d07003002220004c01d01854680042c1c20700c0048801e007101148141c030701440c00010816040c800600141b0b040703014541c1180d074686030508016409035000c1081c100010f100120031102c2ea4426000b250698034000c01074a8907942c01d0384d0580340303001402100340c1c042c014081420100ea482c4030b112501940101c421101074989403070010201d00f13006004014010091003170f04c021a00701a081d4a500355580e980d5402c0408400050310f500c400d4800041c90400500304200400c42d01c00c995900b1184201c00b00ca540c0d031540c800590300c803842c2105e44c0c00081d0b08004c0c100041c1c50304c1b4000e950494061592100072a480d00b0129042c03800b003890540c045403080d800d0080c0e400c0d011598800a020184800e818016580d440c40e44400742c114024010820204000302c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 794560710 1250 794559460 794559503
    0x5060708070f06062909040e0106080709020408070e090a1101032c07050405071706011209080a02070504020f041a16050d140415110703060f06030c08010b01020604 72
    0x11210358201001c49110002c5181802c00340c01c1c01d005100a1030300c101001c2d402e41718410380c014103a072a001d00c03072400c1180b03081c2440014500d240b60408a0742d243c1c48001030350341040c0b1441c400343c10326040145e079450420200c94a080d10550004450080d0f0408004d280c010201c0d040341c0f1191710008882d01d07800140012006040c0040555890303a101502d0b00c1c212a11a4030909080d180c0d28050350f41c00b651302c808000840308112081070100701c10804000700b4480c4441c26540c0035505050982a507140351001c0003ca80b4410390031a01c0c4280080c83c10a180c0e010072400005103421501545400502b060118244c02980f04038542084041c0a801d40c030b4030100c0c04c0d100c1602c0504541d031f43c82c540c507080c43c50340d6002c240851b401041c1200c00b03038060950301c24110f600303a410402103445882847d01040b14004003102c00a20315018042003c000283c06004e0200c1c05d5500400101b1202d0550a0000c0c542c1c210f948404aa0780c500300110010b03907000700f1590b0307006070880d519180c980034104004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 794561960 1250 794560710 794560717
    0x905060d09050c0405161115010302061e0304080304020102010e120406120204030519032a030509010e04050403030519060e010b030424060f092c01060909050f160b0405060708 77
    0x1580c0c130a04002c01c00c000d00d03280e000104034214042d512411104c520b454402d0300c8a2041008081109241c8010300c09030400301c0c000e04014000150000508200400c0032255420544084a408030000140420340d80e090040300307040810a00540300e035021040310040781d40b10f24884c203014031910b4560403080084c65416500103503002002d0382d00c180c202c422040401001610200c0102c0c0c048081d05c1d0069450030900c840f000351600e45500b802e40305440644154112201072030400500f903022030026150f60003601d0045200c0c5e1000316650404800d460f03825000841800801440c2050800c00c2c1c450341c1c01c0036811100c20000c820b0744c035295401c00440c02524419945143c21840f0b90382210701009030711500031600c10f0050011904d807107411450540d882d002d40482010000d510011034035204100000352100c45c040000b941c203584145503403d03910b0400c2d050740c854000e10306641c2080824041000011110300308040f9180c20a03034484128000d500425024a8001c00d94100b081004000c8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 794563210 1250 794561960 794561983
    0x1401080415200406031805071e0506130e010b0c07030b040503090d082d0d0f20071a06090408030c040f0909020f040b010c060207021f1706010905060d0905 68
    0x10840e1442c41c501c03212010343c2c4140302e1a00080e01e098809018103400c2401c41840c941e1000117002801d107454408045068070002424001c10708000c00101903494a0007000030000102c40c0707150303e40c501008140741b8039050784501042c0718104aa412000b030302080682c02d603a0301c1404445192154245903186024100c00160418030500240c011300401c24098036030900200841b5000b5020154140440d03d20850b11156480c007d2003105003098843e000400c0003040100001800540f865403072643c2403258600c408001d000046000500020094890100c85404d803881910b0030640042060707100000d0015017001c4012000c6030020568a0480c0c0041c0010454505020785640c03e4400400d81e040040b442880d950280e45030380e00f494002e001a045058495825021300c2c9e48405010f90701111040381d004290b401304688a0039480702841c2e805009070341301944501e40c0d840340704021502401240c180031408204001c0d41d541c400032035074129446000820a054145081891305d80b80d4080d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 794564460 1250 794563210 794563241
    0x50a0204090e0708160b030411121608120304170a030212160206070305101707050a29031009020913050c03061503090607110a050607080f011401080415 67
    0x15401607182d000880d030b42503a400d842921981c20001e02e040428103041c1c402c0300c008200c14030010b004200400c1101c3c001450147c988c860445095044508000700c94000141070b01081c442400041d50400035110f4201c88003074141e285017420780fa030800d4451081d01440d1110f20014508200c144a501035842c0b15884c03403540ea42c241007542001d105e1160302c401c46001885420006100a88079000713a0380108500002c0316a454181445240440354100201e5020721651000081c2d03611108bc008004004800c01c0e840890500c1102003107581c0340b5840c007210b060086c0107018880c00300303041d180101c451300c1e1001a60394607058045403100407890032101f0210314140c01c02200407a0704d80194413030442101c03c81c0d000034210701113414030b0000b030700c0d200e07031643c0200b0000d45200d0244400d400d00d00d40980c21101d814615586262134034100b00d0b0710720b0002c0e154005014031007d1040000e4090981d44e03807513030803200b00800001c0c03035030000900103401154130600c0100c0c001607640c08000c800c2c69040707 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 794565710 1250 794564460 794564471
    0x120b30120d0c0824090c0c03031509070f0e0d0f0206070b0603160e1302040e030c01090203010b011e030506061c1a01021203070c0516080a2a09050a020409 68
    0x100a0020850719a1410120300140d000401d80c19400d4031032003030719280b04c84400c3d24507141018044e035640028241c040c0e0300f0003000112410300c1c0c1080558814682855030195590104092210190014207500103111302d04009882d510741110760b0720303100714090b41c00241085050400322100f2070103000203034000500084810038851540c00c050311840090b0304982c40e04040309124685070b40b65100b501929004d1401007568481040880c0d4840c1340010b0012032107454904400b802c0d5800122601d00c560340d80c0031003004504081c05442c80300007090030031075401c3e4803198884180408400016040658070340000f14581e550301c0c01d40303406400981004101f00304080115000f40044040084556140b54200c207203076100280000040340c0091280c1d00f9900e48003400e07960000b090b4805c48050145d81445030288000c002c89200411a00300240082e44181c1002c240940e0201c4800100158813400728014581641c4a001150903030300000030550b440d0f080300002401507401c480701860419 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 794566960 1250 794565710 794565727
    0x30f010f321f1403150108120f09030102130e1b090d0f06055203090204110304122a0f0f0f050708060f070e010c12120b3012 55
    0x41d42e40565419000c580b00710805d01100040e0f45401d225203030075988800b0720100860740303913009401010240c01103282008030038030000b402d81e000f481944041c0d400c4082c040120b50003030f94019403c4080740d40e00c090b0800908890043c0352280f06101c502540c0e80f02030741f81c01c0105c2c0440700ca0945401500802207810200844d000ca5200d0101a0381d10082d003802030410148400c1c40807081c04205480d07213800381500c110310a500700c48099100c05042e03450442102503100c41c06040d040d83c5545018564901c0e05280c10582401041a6042001a9010300c8071030a22403001c0f107048001c2d050704d8854003090501c0c001c172004241220041807103801c44526400c1040ca083c11070101803080d07064032000ca840740e000540c2c9400440c5c01100561811010070306490050201007000a01031400030030f104026101c0b2010b41c416002003000085842408007410512072094180042c000c44014403082c0c001c01035851050403400700707210104a0b09429180d050300c00c00a2007a80da02c2d507012a0344138400c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 794568210 1250 794566960 794566979
    0x30a060c0e03160806310b0103140c0d1104021c0b2e1b06020a080610022d070e070c0501060504140a09030e030f010f321f 54
    0x100422074002c0c80340703d025a00c02c0c2e0015000350141c41090b801084160344484650030b002d0080c01e00d0006168034403290003464021800e00565480c01941c041e4615495860141e4900b000082c0004a80c0c00280c20400c8503a40c002402e076209030011a0100892200304c00940284511055908100c000301c0c08001c0312860382c5c02c00c008124080310b15014002000300c400c03242e075040c21300d4601000c03403410007500e4403801080100300711a50083c000c41d480e0390b5942c4000486e0300c402c03014000305032110b00304001403070210581400490540301070071413500202034500030020010555250704040d0796051588050801c4160002e1642001d071108a003440c58014100303e47c091010344982d401c00b01e0100d42820503000302801544812050103556499001c001c1c018244042d04030b0810135040214070440d40c0c1001443d54603002c1d880000b4858241d4100081155115108000004d21a84224001120b600f54a0f0791601880c030402d442a0b0301c401050203500c0a03a000c2103856111110086040d010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 794569460 1250 794568210 794568227
    0x25030908090a0e060f0102060403050d0c0e04050406090c0b04081b18010314061f0b0c330a140408220b1902070b0409090f020a03141209130902030a060c 67
    0x76503010382c2c00c4174040d00482c1c50710411100a00403420801410340010000d50000ca12a9080c0c6010300c20301314a2400582560019201aa281070f110030030a000e0003001ca5040c40209104a060362906142c100b0054961424000036103200d070a82c06a2442d540340e95030300090300013400300d445000d50317180c0ca081c036160305901c00c44502901c68000000d106401400400459034010503445007101d1510310001d605510078200c2c03510a020301084024002c8121100300f00480e000100584403907911103402c06080401040c03101410b0800180c07000000441051540054110001d280e0b074558880e030264407954241800540103080f01800109648040d02501c900e001d03807052071600d440e00701012030b5074244500410050100c20802041005065803003a40c116100345005841c85046030001104200d0070380c41070344c10204194a200421106205150314202c404004506040400d004100014500c0d0f0b860b60720207543d8660002596010030000380703166030210f418414001c280b40300070003610 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 794570710 1250 794569460 794569471
    0x510050403021204050f13020714060603010e031204060506180a0b09010801090308061e0604150f0f170406090210020a020a060507050319030b0d060209010825030908090a0e 76
    0x103540c9007020280c003e03000b1101103510090843c20492105400c025074090b07010361208440e60300300180b60008405040c822201500b40004d4401032500c0030034982955824001c00170150020015000111603c1c19500c0d0810b030041e800151a0760341801240f00c0d0000c2c21388841c1c05074084820030095202e15000900f4260007036444502d26665141c5803426241142d030020042018030000460074107014149140c4e031000001e440c0e03c6d902d00741011840c2917006402500381185420f204111080c0c210420804071400c500c2c03e90444204100700800c601d0607120310b01801130550010600703121584c2c101c0d82c6425001008684402222000a542c80742690802c83c0100d01e14640000d4460044007074501c41600800074620740304000700e5191039807080002c00c800741940c0d880400070310f498116801c425248900c4005940d180040700140c6040c00082c0301504040c811403404420b9140e1404c0001c000c4039030704020820b09024a081480c900a880189410541c0c48000150903660300b8600c90154 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 794571960 1250 794570710 794570713
    0x10b0901140c0604020f0a120c09061d01090b031f020c0705040b061b190f060f0902010e120106171011030903040e13050703121e1d0d051005040302 65
    0x19000c0c590341c00090300a201c180b0806400c0f690004016060404152461060052140b41c22075201c12030342001c400d00b007400743c034010b0610105028005982c8552009403d403c000c15130b4603200b801ca0403d5040050042d0002251205d502d81c020f501d040007284864408900380e85240081c0e551200c0c000e4000c1c856400542c0300382c502c0000d032400c1c144140040500c0c064101d500d0301440c1000940303c1e4541d00724200c201c4c490315a0046c8040660903500a100f48510041c040b4040c41d41802c00517110444131706d03004146804039810040c0c1e00202500144031701501c1d1400d0301a07280b031405006280b180e000c0310b4200072218410601110116860341c42401074881041708003d03501c205c010300e002c00c8400710f445500400003403100f00002881941e01c2040300c03030900300c000c445548039814403600e60b00455020110095094040b50818203440240440c0b0010484815100701c5c024100d140c810b82c5001c1102c2181002c02094403145041178000d0703080000c6600c1c01e0387c122115402088121420b4005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 794573210 1250 794571960 794571977
    0x503010b03013e031302131b0c0f02030307030305101410032d06051005090f060912030a0206070306060e0904030e0102250306060f120308250c2307090b18010b0901 72
    0x2208088c40369071510780c8213a00030f010145074000c0030703180e04181910580380700c250085a1801654100000c0c280c2c01c2c07290360003180310b0500400541d481d50607500035511002030303103601c60f080d510748030030000351010949808100b614040310324210340b1900e048030104034445008840c4031001a90424011590141c0300d001180c58604d40c1140d00c0c0c012030805c05d500524204203a241450201c018200b5150f0090000c2101080081018a1079000c60079850140c0c01010800100c03a8040c855000200198141048d0071815640022000702005000a041c850b89031075041c69a442000b144248520308503031924260f0803060b10b607911011034801119818144074000c03a800540100301c01c119400e01400382c4094074540d074203641094006003c114140c80601260000c5003071050741504c20b141b00e40755071a0740015030804070000404840b48200b40350524085c401c29030070004400e02215031400e80050144180d900041002d148101e8001e00d10001c00004924010440001c0509403001d032a980360 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 794574460 1250 794573210 794573239
    0x5150310061802090604120609050c060f0d20040b0409050907081b010201110f0715050c04030318050a0627050a030b04150c03060503010b03013e031302 67
    0x140c03070079801141e2480518040840066240ea0068048076100410a500741910360440e142031300407006003502c290b500e60030b5210901606014184c1024401e8a03101d10301031602c00281703000e11810001030000c0f60f60303500c0c10440803d4500140e8910503d440f29035541d42d51000400e1b0144c009000b0340e440302d440c280104804801c0040d40c1d1088548103005060b20030314489100315410007411205055548540c103480a032044d58004004443e040c41d2517a03115101801d040e203042085102c0a61040c3c644402e00c40400090310070707a001c0340c2c1d26141030a200862282450399444195000980000c440d60011803404e4010b12126450700d030303aa082c1078511044203d4480c03000750510817590410800d00050000c6400d0880903513020380100480640d80e031195043c1e40440d0f5100164030006a0307120000d01c824942809180071441088009011004030020310784d030302c10440c04404501c1c00020048090b151804150118a51822034002c2c2e224501500800d042000e260b100b2403017060788010030107 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 794575710 1250 794574460 794574493
    0xb0408160e0108120c0c030706091806380c07170a21110703030306150c020603010e06150c0a0c120c1509080703110405010f061d011101051503 63
    0x38103d6207000020300c903108416902c120507502c03c0107050760900807458200b090f03450421003100280303110f940b4148800d24000440586020f07404000f101e00e410494100f0508419540160038040c5c446180b007128182420708501c00802c1c03144603024090046480c0f0035040c400b1415408541d5005440204104c0d01400192100130800000f002c40720f041e0094074100d00104e001201140003401c1c1601012901c0d06140d1a1115039031040740000e1f160081480910500c0003c044c41480304c2c204510940e460f940058130b540014082d15058607202c600041142d540c2c41010596004940c00041d510701c0c620140e103480301c260384c0b0f090f110141050b5000541420000404100907040540c0501013410504104880d10b40c1d090950700304540040085030f042d50510590008511502001c6c8940f1100750601046d01c00c16030040140d020226410451160040c5507241c04411040122507440040001a1000c001c4400300d940d042d03280900304034070540d03400918015180c04500311801038403010b0310b15 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 794576960 1250 794575710 794575739
    0x30c011112060307180b0a050603100821160305040f08060114060c03030601080405030d15090b0102160603050a1107030201090515011d1e070f0e0301050615130b040816 74
    0x80d04134400f0a1a85e0b0424989501190346448010200824580d075080040c100b50010388042102d41d0601100b08441030040240380e0421034600000c448200d1b0300d00c4807407001d0040c8640e2140c2c01c2e0450180f0420035105208940240c03842084a0845070f031211101c036a121002d01800b100d071403454041c800c1c546080c00c151121124610020340c0f555070f41500464103100060404c5410380700a000d001c1500c00a402002505828070300501c01880c5465100c2003900c0002c2e10f03003030540d08200903210801d0942c90b404425661076080224143c2c072003290303000003426071940703901d604900030482000301a419041041074a00030030031900300d004a883e4a8407442c0082c03003064002c88030380c1e5064803150348000c0c84a80c00200c8000305100503c42c0120510041d074100d60280002d103200340d4041c3c0c1950000c82c6144409410380007000303645000d80104003600c56130004500d00101c046504130114150b04820340c0074088010605403900c2e075841c0260303a00c007019104050b4400c40c2441c041504090080503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 794578210 1250 794576960 794576969
    0x1507090308030606280e0901170a26120103060b09011404090f08040305060402090a05040b070806061e03011d0609040f03052b05090d0c021002030c011112060307 71
    0x1040e15688511007040413a034401350510100195010303103c403140b00c0c22154800c43e01c0c5542c4840b110341c03603a10b04204021405802c01d800c030946444465003c614002161041c503030740700c000c141e803510901310102c10703a11029014042c260000640408203080c0c01400c00d040b24802c20090000752100c03020404211300034050004110002c50b6598a01e10b404e4011803e064090114003840c54043d80301c0783d841d580290400d80b1664407110501007181041024198030565081c0304200d2030800c4c1d030b00c1d41c0040c4000781902c0e0412401030081003a56450500301d54903014082400c420b050405004000160002d01c00c010912400040c445522000382d010188170b68002002a1100e80d15a40da25034140a02c0f0800d0b010040240a400d1a048090740c0301c42484000d035180c001c102c107000d46140305455000300304460b1703500413031120400340d44c010014001155049034020411100024200d00d5400340c5004510a90b08044008a91001c1800103005414201ea0050030ba40d5955003410713500c200350b01c034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 794579460 1250 794578210 794578223
    0x212090c1f05160f0c05090f01050d11040f0c3218090a021e0a020616110114011401110d080406020d0501030302100507030614120f01020c15070903 65
    0x20300c01d000341000490101d41c8a0420508140c11440c030101d0b031100e00b0b401141c0014202100d0002d02255020800083c603085400d08010b1802411100d41e990061207214000c40ca0b00007164100884480c05211000010300100003021280602c0c1016001c1c200310341c404a0300a6101c080c400c801c0190071840d1408140c50b4607402c2e80000c088020710f0740001c0020008107100b4000c2c01c5503946d05080a802032511450141e120710300070303405040b0a429116140c41c403030401c000c20701805401090701a400b0301074290024880380208815142c040b68285000050b500e41622080441805200581a507106841c1a024040071030015a500042108080125407002112080f03a1f480348200503400340c400c40002d400c0c03050555102040d03030300a030400c4000d60800300071014903604c01c4c070416a1090980c603043c0f1040d450510301c51500c0480c0440c0e203000e10201f000e4240004401c03c041026641008000c55030b4502c2d010680d51500b615039042000c416030b200c08508410712030b10f90300e030903207800a1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 794580710 1250 794579460 794579479
    0xc080316031a0a21021203030901061e0306050403141914040e010b0711090a23040803180307050a1b060203040b0f2506020301050301110313020904031701090212090c 73
    0x300040700454201180030500c12413031045500688600781c04290300d4080d0002142c4a0520f02c0b8071030b0035030b0516040100b41e0207403a20400384034805410800201c0390082400501d988480c00c0480d4040d40000107045a0140041e1007030201e100c86040d01c0403820345640351005401c903150548031a1146108486d1b40b072011600501a6201200081000c144281c46150f00c0000001c00700350710710401c50341c0f200e803103030b50748030039003000040801c0c450b1401c41c02403d0505c3d5260903a940341444c0030107000041e4050110103400f0403510200102c44030715030408226100c146091400c051809001151a0080c074011800060800e00010a40301600c982e00103da0600f611103060303403600e80080300c036145540b01080c01c0304a1036030300204a080c0c060061001594940c141001d05080d40ca4000ea82018084c04004110f001c2d4071440f1000c501550440e0690029141e50504075090a000607030300041040741c000015446440b030b8000c0101111003c0880f030320b59103640380c842d00c07000500b918079013014055 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 794581960 1250 794580710 794580719
    0x30c0f0b07201801080c04112b0902030f030306010f02070f12060f050906010303110a05031213020a150912260d060311040501140d120c080316031a0a 66
    0x61804040b2941c0c05400541049941498401681c2080e072041c003403178200f2400b0244a00300b50154042403c40303800f0042c608a424905085101076900e465100c110928180b425400c60f1768215000142d002030403200d0881000301041d8480c0c1c0181c2e42c90340031a0341c0412159803d400881d206007207407003d4046952003817400c011444010360348441107072865030b40d25101d045c5000d10b1040c64015801100140059810340c80d0103480280603400098a035170010410b440020b0001040340c04135600c0102d003010540320400d2214911400c0d441c000c1d84640503510114080c0070807d0740985982840d940d4540b2180e5034080300c581d54640013170180031507040541c2c2d50403079101c2006202c03141d440c0510b46441c1c0401e10383c6440480e00e05410031038402c03c00c6404100d03140381c90300465025100000d8100b00007007030a0001246c403005803a0052a60841e80241042e003805904000800394214460686d00c1c5400c00d00800182201d0338034030302080c50324403c10710508411b02d10b4500203c2c054440080c00c1c2c2403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 794583210 1250 794581960 794582003
    0x10e09061302060910031e02033603160318030c03140703050f03070212070b1b0c04110d151a1e0408010c02071401050702010509030a0c030c0f0b07 65
    0xc01d406980049040004c18999290400c03000941c4011b42d500041c0b0708815401c05010b50507269054a0143c014000c2c0322001840c183c180d96081980340c4106000071110307030b071912900310700301e1420300a001c007041e4000c0182581000704086c81c8a41d6401900f0800160490320f0b040c01800094134024010a081c40060303000311501d865850080308948019640c1d948982c130b4291409262940c50f080403a5160840c201101542d9901c012903001d440d4690030100812140c5c000e22402c8142110000d0300349002034014006585040c00280092100c1d5070a1014031326542d006010f110001d514001b810000384000e200d40c1402d0b10780c81c4951500c44281260822103071b8004900b124580e10b031a1141c9075010601200900060418000110350702c400440007904003001580700c514511038017503080105a0388101258907175542401d1254949078090040780c54250109001407009443c22030100505c5440c8441004035201c4920340000741d41c80307440ca0400350050150080c026982400750a182811 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 794584460 1250 794583210 794583241
    0x130203160906050f2b06091a1c030e2101020306181608100b0c150108070806010306152c010501030b011e02030c0303100302010305070f0c060b01050c010f05010806010e0906 76
    0x581d090205c0255000080f21013210b4441e41314066165550342c0950002030a074145480160341200c5803486038180c0b400701c0e40c21075842e080003010000c13009000c4149a50700703a440ea0005000010080081580d220b41ca8000c0d8010f0700c0140c0304800304403010412240084445210f04200d05254905400051041e64480c00240c80c03c0540b4240c51000720381a400310300900624000c0c040142000314180001da0311044040c3c001d600342d134101d02028030051800081a50459038005030020324080079022054403074045811800780c2103200151000400c9500300c1d60119140c0301e803110007040e6650401541100c0090300d1541c041106e03409480110405070885843c03035812070044c0d0707141a08000c00b950440e4021903400b100c0400d10b190520955916204d0700d580192281040e6a00d80a80703007001d41100c1442600a21460b140e10f2282d46c507034400d90644d080301003000000e000504542a001d00500303024000c10302c0f18481c4400000301d201c04201c2680c040d8441c000a003030141c80b0000301c0c0744280e1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 794585710 1250 794584460 794584507
    0xb04030c021c051027050102030103110414010b0a0905150a110705010c0311152401020307171e0f280f1211040f050117090615130203160906050f 64
    0x11760200545901e4119801940040340b05200041c0c0d00d40c11403810000441c0d4916000d401a0700d82400e4499503400d0f10642c505454010100c99240c0c01801403c841070000d0360001500819007003c507a0048880c5005062801150b89800c420410410140395460483c0e01c20940000c1c1e00c1442140464040c1d414241c503045800282c4104160007214070301c084034203544482c10144900c03104140014034070041e10914100b48091403800700f070f0780c503001034001403100d210302140320001e500c0803010458909104c115905500e83d94440c440c0e800100020341145001d03a00d001c20941d100f06c41c0e07080c80f805003d4500c032681c03200b542c03c1d64840002c0391220020059100029a60f00e00c0885100348100500b0091400c0c00e02c40003028101400140800d11140b080d82018244406110749010045401ca5014512091801440018ad40001c0f113012030510a001c52500c00014842d43c01990007080b103c152042c0c546c0000c990703840390115024803425044980003002441080c0d04d000d10b1f618003d00b5913 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 794586960 1250 794585710 794585741
    0x2010b09130b0103081e04060504090509010b032d16050307060e01140f090405090303100909120c051615091d0f060303040302190501180602070e1306020d0915060f090506030a0b04030c021c0510 85
    0x101e0b640102d84b50203042866a2152244030b03608019600e4200a44006000180303030542030441941d0010b840540b401c1a00144860302050301d0002110880c103484060340004d106020320f003007a01202e038036540161003c41911001c27641c0413440c5901802901c6240358847e0440e80e44000207202150803900c417203c2290580241c41410040400454145020b410000c1803e0704041c808030024002d03405680c055080718030103000403140b000303208041c03e80c02200025942e07604d642c1c4000181c01e61080303810080d80441c01c0d10310800b0302070107120380100342d640c03c3e2581c541d00003000b040c015102260b807042c0b60040c1d200c060140180d0120241c069080104810102d020228556031031080e0f8100800c181a02c80e0764081841c10310480d04c00c840308221140c0c01c10841c203420400700701024a03040c0540d1807490380b0790002c01c0440c0c0f01000550318007134103c0045d006500f051302d002490321030140c00603032044d45003a02e0740310618136062403404516840402801d03a0740d0310201e07200141c41100e0002d07000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 794588210 1250 794586960 794587033
    0x151107060e0a0b0c090901062a0204150e0103050105010801020405060304151b08070206010e010f03060203100e0c0a02010b010806100e0a0b0a02010b09130b0103081e04060504090509010b03 83
    0x35104041d00c9020300c00c1c4e00401c2e5107698443c0103001d24250140e02c03a004000321000040040103004220301680a905a242d030b00c22016800400c0c040e02042104200740c03040f10000250000c00d000c401c5058a1154000b40802e0f64ac8003005401d030b014500406501903800c20100b030015010303803c0b016034901524000b050404040b0352481c040700e1110b4041c0c0c04200e2180c1000041d0303506004840c00341a044500780030719414018841104001804005c01880c1c2c0000030032510030314130914200800d07150765801654542000a41c0c0c0581140606401641c00d21410031101d40c003030121a8480c0001070100e4486000d00d043c101c071040781580c3d180d40c01001400000ca02808500000c11303401009030000f14511441c2c0d070501c10200380c02040101420050785803c0e0000d122000e1752070440340c102c2c41032038a0300c144298100c0f40035019003421100700f07400140000c200b60024007500c00c03161112420041542d6600c2094203907504100c94543c1600001025035404084500c104090707500c00004409 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 794589460 1250 794588210 794588213
    0x302060906031f060305071701150f090f41100c1203150602060402150c0f010e0a02040b010c0c0306020a0c0803130c05120705060a0c0f0c03151107060e0a 68
    0xf40e400e02a085100020b8480341080300c0a46c0000240c904540d000150011b9903140c44982c40d042001c42272003004001c103540d02e4078070261107503680401500d0540c08566000c0c0c1c0d1401c12221a06002e4424881440418030b007410180f14020304400603450000900703542e00c1c584040114444040c031680c03040c80140e4070b11344081a050000c0c510100a01d44000074204201c610060846101303034030000466105108000060722070304602446002c62a0304140c0b01c0f0b5441c0001410006082084001c42d840c0114a640c100c100217480c954950090310304125500b00c8800450307180c074410303d0190101010f1082040040c403140d0040c03036184107030f182084898801da0f0f2464501e0340280e600e07d0b001c130704d51480f60f03060080e094140e038000c1a04690016410201c1c01507562203005038401c1a00c24080800d06901da40d014403440c090180c0e2108103034105601714a061056001c41e40400d4802c072014004605d0a00e00e588104e010343c072007600d9103e040010980d1000040c10701c0c030301c1001b242d0080102460 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 794590710 1250 794589460 794589511
    0x209010c0803360309040b0a0522140103031709190804080c0306041a130606090e0c03030a020c04050c070c030302071a03060108060d051e0c040f0204030206090603 72
    0x14000e10034803664803100341c40c0c0322600c007080e080088060f880c4154143e6491004100004a8114044c03c0d9804501d484402d00000d40513074081e8081d94100c8500013051008402ca140f01c810280901c801c20020000e10180300400700d070003408001c000c258001d9405100c000310043c12a030040c2e8900407940c944000d45000708007424100030403034280d00003080900955105008084051005800800e40c41ca460740b0354940200c901d0060020400300c07807000c143c4088000c1c1d0380c81d00c0c0581180e42800183e0b03517603071442c00401043d003a0318403e00502c41e10360071600c1c001c001c03601e0340081c55004220419941040200030400136003103510307192040000c0000030300404c400384002c41c000d0300604003030ba240030241e05143d91004440500b0340c10070020840d803070381c00c500c0041c1c002d80c0a643d20500d03042649030952a0010201e4050760103030301c84032003c031411000680400641020b5070180181565454510240e0299000081d4002024041e2108504014019581c81110b0340c50301ca00d202402d54104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 794591960 1250 794590710 794590717
    0x910051b0715021b011803050702090403030605031b0f0a0303020718020c0709090308010605030919050c121e061501030222080d0e0303030f0a0f060e010f05150a120209010c08 77
    0x242c2828104144d500440f2000b0701c01c0005c14003a91418040403229a68010700c01e200c1c81100034883c5620101060a26100c1e502c507402505000d0121526490501c5600340c0301c892100400d8400c07204e0400020141c00d0500c1c505003107a91540081c0b81d500d08113580a11101c01414418a400758248490112600704102104c001c1c4549000000c001866040041003484160090002e1010400c2130001c19080000c40d800c9650300c040504004520310b103485424806015920765010145804401c0c40940110f036101c210300c0403001c000e152940c180300140e00c0390f01c11140b0400c2c40d0401519244c81d94043d800074640765608903030a18842120703810b18038012400d130b00103102940c0240034451072130f41c015004031140041200191b041d0305e028803003080030846c0201150170032398071841b0b031a554800c00d8100802804003035042c140d50f513840d48403540411040c2d2090501c10010614244d400145400849080e030166a03941010003000104803006580100701607030400000130b1900012404041c045c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 794593210 1250 794591960 794591977
    0x80409050106022107020108100b1201140d0213150e3606190209040e01020d1d1e1212150901050a090513080309060910051b071502 58
    0x360381d4100a8001e20700070610742500004560b1500c03910300070301c820b0151030105909190070441a52022008038031440d0f241c1c00450719020110b09100c1c42d1100405036410780301c0d11000002200604810050407802e0b080010b50001e13032041512450f4081500005291284200d0000d100c41d03940c03d10a1614000321505a580c03c0900d9421540c8008506034080041840500b00c0051981e6880d03940c0f2040058402141040101a641070312442d0390155a40302000400401030780000019036400707540800342c1d151865140100700070307541c42c842440403500d1440c000204071a802c800c40d90740c20000d01c02200505481340c5551090781c1420940204010b0311840700100887c01d218407031000124114503114442c0e00c8000040c01652900d01041d011240a0f0102041e2901c07002c40c0580c42840c0900041c001050020800c5048600064818080c130304160440c1c00d03012a0070045821684291600112880003800300c094162040e005070a0f06801800c0d091000707680400340c6001c90f40026031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 794594460 1250 794593210 794593229
    0xe040609021c05151b030a2403020307051903031d030706090806062b020402090a0305030912011404060e0319020601091112010306020a021c0c060c0c030c0b090a0804 73
    0x2240e01003041c01e00004c10002c0642c07400310460308011555880d5079420021500a040c400310006942c1d504c2d9030002c000c06c03c800c8912250003a40c03900c1008000c0054003082c3e0280c442c0c20000540307420101d50880d4440070003140c01e00024103654044070000404800b51405030340000d00942a95410300c90b500040c101912210342e00b41c036240001c2e007403080c01449039206281d00c0884c085101480800c280c50b050001c5d00134605142c1f03500c0058000d000d0400140e070031940c542c001204005000004002400045443c22400c4801c00c44060a0710240c44600740c03100d85e00e801003400a9025000200720544910669007021038580940007076181c1740f101a40181d011030010041d420080c4680c00441c88001c9009240c51036044204410100c18440107140f1540007600000440c800d02a03103161603c1c080c80219003203920000280b58089000d41a204a854080c8005c079a0b805210b0382030f01e0b075034180c688000300100380c1c451503240e8800804010490080b0310802c400a40310304002c002422807201d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 794595710 1250 794594460 794594509
    0x70b28022104050705190801090b09060907150503130510060501030e03090102120a18090e010b060304050d0305220f050f070e0a05040309090608010f050901150e04060902 75
    0x101d801c000612241c0c000d0000a41d04000c0c4400700d40c000c0741c1002514001d445038074660301e15001e108002025070b400a40c555203006500c80c00c0200b4901c10038061740410049400390b85400ca070094036580f0764070442c28011171074440c145540c0e00440165038000b16050700c3d00c290405548031700e03007082e0742c203040f000340640d48480c148019a01441840600201000114204030340c800000c1d584002512401507503800208070f108a55105e0072411140030746445080d80c0b1266030f00c0c038a401030700c0c5204038401c00c3c0d4202030700c41c2002d003404800d40384101d800400030030401c030b0126403e4006080c0604803015441e8044020400511000d07a0b1f20700f502e00c545841d541440407410000d040818900c3c68000c00d0700305030000c10800f1420b1160755081451010001400d48035031800355032a02030b661005400302d0420300000384c0e2100c19809000440001c40c0144080c1d80c03000e094074200c404003c6601f510900701d080910104246e01c0742c04e035109200c0d40e000100c5161640000b203603119900c060022218125 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 794596960 1250 794595710 794595727
    0x1e09060e04061a0d140a08040608070e010309110108060103150b040e060d0206071e02030613060c080603120c0709090c180603030c030c03170f07090b0906070b2802 72
    0x3c3c421408004000755564007003241890005049441916000d402050041c18808519038140301200d48035512126142e40d581d900e02024207210011211103001c104510202601035000c2c1c000c24016580c801004541207800800640d19454094422030403d542c40c40f074071007202c00441103200913080d074480d46521145000b44a5042d804001d00c000d00940e1401c61080040c0c0f210416106521361142c00c0e00a40b0340043c40340c01985200b028060741c18420641480000b042c03110600b000180211414420000d041009482c074003c03e855164140d0300501d2442017212042c80904100e65009040e03601d566541c03a41c0c00706a81943d40252440401d000c01040b0552507480041d13000c0480d23400510440c1e15644018140c0504000041c040c0a4910444000c152060100b48030b0941c1c000b44c81241d0b42048440b01d078080000f2607190010502481d0003107002c0354680c00341c5071aa40300505951600c89641d80e0301403206005000c6008500c0784070351039800b00c145166288a6020800d03001038455084 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 794598210 1250 794596960 794596973
    0x5191e05040f03030309021507030c02040c030e150c07060f020d0c11030909040c0e1603180b0402041a0303030702240106120b061903020d0501080d08011e09060e04 72
    0x29051541840001c10040014101c48402c10080740d42508002824040500200f40c41d4900080a4a90303440c0010b0030b04101500285601c01090099404110035101d00780290121a0a880380c1c00c407039440702c20b4103241d01c0204405194031500c0100d407035003030045d240e07100408e8580312041118403c0e004a00c40e20b004010313109038800440315141c42c0d401000403501c0681c49210320008280911500000102442502200c19000300180c80600074030380340c607400c00040407407901c8504000906040840ca483c1c11840b903c030040340e401100b924041c0c1c841c0d40c01c00c8024442c0706071000c0c07403900340c0704111065070b410b0001c0c41c0304094503009045200e41590b10010701103200103600c2071b482d21400040c00020b0340544400900c1c84035090014134980c5200006407240070340c2458150320406065444003159040c0c0103402540780004091103140d0300c410b0750300d45401d06034100070000340c0b031003004000300030b0b070a00c41c01b2103180c4e441d81d0100032540741c0c1005025941680c20104141c0e00c0c142c2400204040e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 794599460 1250 794598210 794598257
    0x10b040c03050402120729040f0e07030e0f0d03020d0605030601061107081216030e0604120c090608030913060e0109020720011b031b240209090f04030519 68
    0x1060000340c8080c03802c0c414a6250030905100303400b60072040003841f010510829081750003030544180c0301401c85035122403041c038914044541c81c00203800c0070816036100c0d400080d500b11b0048400301a000c048184402140250400c8541d85a00398a90034006610b440038440705020b03007520b40e20702c100c0d10000900d0a00d080c2007640400496880f880c02901e80d64581410b8070a00702541c0040500303070105040c226084c102e840407582d031001c00000c0009805551400791040300388111640816a60b6a1010354201c84007072180700c54640040105100a2400c1d030540e01152500100008069445110b00d0310111402d070001080b065000429500340006e4140e400c080e0b480f01c1807681c0b0074440c0000000c0122090408241900d076040600c0c008160040c0150440001d0780e0716451900c0c81d40b81410101003020b048140070003181d100c0e6021148801c1d0003210000480605808030030380b108103a0890854004000385e0400005100015032074050485206076404260341d404180e0408599501d090035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 794600710 1250 794599460 794599489
    0x518090d1b11120610060201110c030a0309150504060b040f0b30011505010e09011a07030309060207030e09060d021503100b072d050a0b09010b040c03050402 69
    0x1481c1c4801060000500d080e0003074407540140818035803202000802c0b01c000d40428194403034064201000030440800803004200c038000d0f402880f408840300d84000082c46501e19400141d00200205181c59010350004501140305003100b04203100c102d07001404407802030314201c1d4403640b21318030000c5501d064029100d040f903281408010b1442205c0000d940883d249400e04139855444003c0380381c10000598010703580c4400d00c000c0c4442c210013250b601003681c3c240949404034502c0642c3e4103d6007061658681a10b03003502d1006040c1d00354110000301600302003011070801d03455054032000610036002401c0f005100782c44c0c90640d8000842000001c00005007918012140c045042c00036039280455012190400e0f00042c3d0b89459107030040c200b03d45190030008850900040020410000c007400d944006079004801d8081002e0a004495002180b0805055680407042c50004a8510291650000c450794000a402070100000c0340079118003c0c902e2002c643c0d101e00300001d40c1408201100c064 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 794601960 1250 794600710 794600717
    0x240a050105060306152203060c020d02030301062a060b15180105030a060f0b030a0b0f0f01112112060613150c17180409150c090518090d 60
    0x40d810400810282e000040c1514820301c11480b5044800c1c0001044800312410003030600030b0a48140480141c200c582d2108588151400158502462021500c1a6007000c0e0398040c510b07503481d06c4002c03601c110203a10f0180813804e03804d1582041281784075400246d18451003011a80c070800204101c43d410500b6146003404504110650224022101202c01000700b400c1c259180e48951003400000e000e2904184440e06040c50041902000080954440c4080c400d05012030021030050089080340038540700d41082e02c14205c44c030b4541c0100054070230403400d181101d819020341e0006da100d0103c1c0d8452001c10020008507410422516495180d10035000c0c0d0307450f0716060418002c40300d041c0162007a5404e01403000f05003182e40e40300d49002550765400489050012074003024400c000d512240c1800220716100034202c52609203030040a0005400c40c01511150f1241420b81000e40b035504103481c20003801c0c44000c03c060f9a0710300302c0c01c441a026145d85401c3c5c50503100340703403502c0a04070024050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 794603210 1250 794601960 794601971
    0x604050117041a070f110f0c010c1103060a05090d021501051302130f15030504020f06070503040305120d0b0111060a02090103020705071202040b0d080d09151d0d05040f1a0c240a 78
    0x2c81000840c04c14a400c28a071800700450ac0742414008426030119590345401404140810401190040c07800741c0400d1054170403411400f80c0030ba0303881030f15090307494200112100401c254504071a84184d02010800c0151030266080082610b14031304c2d03040004e400860344020300400d41d840b03032100d4000030181004c101500702a000100c0200e405401c1e2889200300064141c2044010301c00d0301c000b50340c0001120403540c001c103101d400d55000a00605403142c50124100c8581d0710500b441100106840040c1c501c40c0c844a00f564040d50200c089075041c541c0800102000640400141d0002d0000a5040e41004094410407050b594542045486066107100c5400810103240848405055107600011041880c3c0303004101c0c901810078084141d8a0650701007041001d61864907c80340742c00c0156030030480800c000355694091070050700c514200f400e1027402402c03061005980c3d0511002100703400d250301440c00c1444d01852030040320000c1e541d007038401d0f03c0b21200707200b03035400c0804004207112 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 794604316 1106 794603210 794603233
    0xc0a05030a0c020f0618041a031002192102070501060b07110307270509030c0f25060c020103020d0906051003050c0604050117041a070f11 61
    0xc0d403919801240178584081222003000205e6400a410040d4405000c020f0040c031030003036180c6000010b1403010b41da04000c0b14803100c1d09200302581c0c0e204c60582180c074100b03102588005104400850785184d03400301502e00a4801e1442c40181c8030740507070504030701511182c1c1c4a000d000d0000942c2c44180804050302c0c100e10f1800358100c80d030055031001290001c502c1d01da01101c00050140b070841ca02c0c0c2c0180c210b00c1d00102003c0844c0e0410301400852400d00c2e0203c2003042c41c65000c16003d1904009070b01c1d001112510380709458469500e04407002e0316900320204000d04040d40050110110035041c1d0280d0a890b800030410081c03440c10012180015400780020303940c1c0d12482410b031691740b8000e01210207441041c1e444880b0b2070400010140801405041100c000e081c003202d05000c40c01c0e11003e07501c208450382c0c401d4a6400401d0010b0942d428915083c503494100300230042 = true := by decide +kernel

theorem cover : BRFrame.Cov 794424460 794604316 := by
  have h0 := BRFrame.cov_init 794424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 794424460 ≤ n) (h2 : n < 794604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
