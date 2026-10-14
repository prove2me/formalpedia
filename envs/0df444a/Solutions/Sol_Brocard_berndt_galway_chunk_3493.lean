-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3493
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:49:08.668748+00:00
-- url     : https://prove2.me/submissions/45597182-c3a2-49d6-a492-55a3b07d1594

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 628057553 ≤ n < 628237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 628058803 1250 628057553 628057583
    0xb0d050c0702100915030b0619050d150e0703050403020c13020d0e01060905010e07020c1e030d020f120a0507020f0102010b1305010905071b12020f030d0e070902041a09040603 77
    0x1102c09160121681508030b85481060785d00140d040c1d4040850264200340e0070300802c0d40c501e9445441c50085521800c2991920110104500c00c1e503908a162403160b180c4003604101030403000e50380c582d000006150401c042d00341036a000b506d90f540d810f88188528001850001e8085003541101d030503100c031060400c82c280201c482140a8450b034811044c50070320b03100c00040e01c0c1c40e9a032261446101254041c00540000f14100130840303006032051450400c00c12507004094404000c103610b808419001041300060300240743d480c202210070b400080d480c0620807240115084002c0d64540307a81151040c80c040c24140040b40100200c1191039846400440364646164417035100905a450b1840c050040b5500c81205507007840b455003041c00c54010301f15803140440c20702000582104403620654030203280506059195070031210301001425980c031020603c42c0410005900101f88441c01541014a40131030701c203800342e03c81c000e144c02c2100000c0303019460740c5da40e00a0000e1075105c058802c00000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 628060053 1250 628058803 628058807
    0xd150906030606051003020a09061805090c07020f060a09030809060f1303030f0c0f020f03010f0c0314011a041802090a0902121e060613080a06020c070b040b0d050c070210 75
    0x815200b0760380605c0e20000c002c8146440380c001c0310b0404a654071456201480c1010844140d62240140c41d400000c0c0b079808283c83d40d480040742d02411003119201c1d1903e869004000501c080400c01601c80c0070300300240502e40c0e400c00c8040003200d4015011540f2030480001080d19485a580c0702609800000f4980f142c62075a1306180040d03902a0340c40f00f4441d244005c0940d50000100405030440388520240001482c0c844d05032a0402e00113800800c81201d403452420a45800c0a1440c000c03944400c0d0700c0078415645040d0306d005090030320038070303a480151016206070b9102c0d40c0100c201d80e05003140c2102e004120b540444840078809803400d507299555405000080d00320755440005202540c01095100c0700c5109125034020703151500c04215100c481c10009a5800207085085140000c3c20004050304c0130300c0103a0101c1c1c040d040c0035036240c03020031903207050401c2034000b00211101803106000a264200980c4e41c24812440c0000f1540c0310342e90500003a001c0d040c0000e40c01141504694a529 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 628061303 1250 628060053 628060061
    0x171c0606180902030f0c030903071401060501271a040e040807020120071e0504020f0c0f0601080c0d1a0a091103010b010c17090d0803011a0c030d1509060306 69
    0x1103500750301c80003a1544034240c16440265004100706160001049038240c5d00001190042c0950f001c49140000b6075854038490158003d100203503035950a4204110b5800182401d00203401508110f112144e080102c0c0c0020ba450041b029681c80e191051804469020100e90281204540414080c9001e10f40011aa84541f0040380041c0d803806182c02140b443c5100c3c154030098071405040070609040410001c05a812001c0700701c814000b00000305c684036440148080346045680503550003480c50b40600c0c01d040c007241640340f9804000100316040300806e2405a01c00106c98943d103000182c10100000015800b290701c16030610001d008a111090384829042071240c0c8030026460461410107007258203001505000c1080092058000392207008900c114070101c4168034240002140865510429090100d50400c80000180501c8401000520402c0142c81d2006c0ca01030b0b01c00407080d120f00403101400c120740d0b164800900303119510701d03018020700702003101003003016600e0400401070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 628062553 1250 628061303 628061327
    0x90f041712070e060a08040f06020409020a020703060c05040b0f031504060e0f0703051b25080711090415090c051c17120414070305010c0e130603171c0606 68
    0x320780d07002c181c02401e003401300a5880c3d00204c2d03243e401441c2c0e50764803044810103483d00e040b034625500300800318542c0030032700c094010240b241d8020300405e800c1d80b40601c100c50158800740b051110501c42000118040c0084505044015154a40703a860b22000341d50000c84299465a005003001408100300300080c2c443d501c9070360500513000c05604e401e04240c04881d02070340c003140c110bc007c0710600b08840c0044000d0918072800840711a800403620b07410408207299010465400d100080c0300c900b406002d40300c40c500902d08480d00c01d106c0c2020743d11494207403200c0c4800303030100b0340303d0780060700f03002400700b031403004100241840407506843c0c0019040e414400504550030310010344400104070680080d01c4a8400f5040010b009450340e45588040001000c55a07c45116441004c80054828047c40c805c0005a454041d00180301c8800c00604480720882c0513640d030b1504204101052501a40e85090340c000d08425548445142c203e07011046241020b803541e60510070b001500603445000791b245 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 628063803 1250 628062553 628062557
    0x807020a0b09090a06031104020f09030d092d03030e0d0f060b03010f09020306060f1207031b060e012a080c0c03010b0909070e15030f0d02010c02010b090f04171207 72
    0x644c0d5501451401213801c0c80c04003605680d907015074a050390400d41e0061111070300301c1c40c5903424100d2030742c002850034a0401e440030000707603c64410800507100700d054030841c501e07035402142d0b0710084802c0c6000300c1c4182d00c0050b040004c00702c07800c60f19455031441c0a940036008a100b0b0903500c10b5080c02d201500702c0d520540d009601c1c001008800c0e0240d485018a83d0343e0040240800b81c451104005840e0034840d8451b034045515000071412110803c5040000e51207401c0f22a59030041d1045507203402d005d031380a101070200504103080c0a07071344426050480342c80c1c1e0201c3c500d03859100013010203030400100024501c06000807246521800083c0020f4200c4046000b0300190f203400c810300c41d41400549000030a50301c1810140158039558521944c881d000401800301c19111100080c6044110a43d012482e0850301c00303140490303420702800c5001740c7c0d640024080c0206400228801080c0100844004403400d0701103820400004240c940c501442001152908100d100c0800028000d483c1180 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 628065053 1250 628063803 628063819
    0xc0f070506040311040e011b0c05070e0c07170f040f03201e032d0106080f03040b091302042408041a0604090c090b120312010b070807020a0b09 63
    0xa0140380500c22181a40e13882207074031001c00f1884040c80054400415000065520340c0340300411800e4511030030303101c1c07804c5580310040f408090070b0640c10031036260400000d6050400c100604503144404580c1c100c0d900013022610310310040d01c40d16540c00381b5542c1c48420300380083c000401c540c40328031407001c6c0c90050b8040e003026038101405100c20040000541c0d00403030030f901b01100d0010310310201c60100340e02405403050604d2641402e8982e134407020b2124032406441465080c1044244075400c0603101960080c08444914003d20355640528071030754031700c00e4000a0b5855603840e80384a4031040408441c0039502d96440e010390b074400c103841d051030081141c003000104840a00c990215802140c101d000c00100b40340500721001d074440002c015a0700652500c0d41c076400a401a2200001000c403a240003c1c0e08a40c0f40810101c02c2c155032102e56540c0c414045201104420381d6580c0c112510940c0807581c400003407a00d044580580000039512518507000000c948d5000c00003004101411140c001c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 628066303 1250 628065053 628065059
    0x3091605151215040515090a0203010501020721021c06140613020706110f030403110303160c1109010305030c10110a0e03100221011d1b04090e030a030e0d0e13020403080c0f07 77
    0x4001c2b40024400c040c0142d0145404102050180e0032003030304c141224007100d2820700702d500802e00d51903c031a1030b090180369280761001445200d2207495000c40d051090b074a014244840080e040c010581582860301e03a000804104010859001510402841d442c00d81c0380c170104042a091a00200c03011350204503800365061903108040100c2c6d1103203c1a8109d9104800d1204080781e40002004c0300b1504204610700c0406943d4550360a14000e512510003582d403030766460400d60405141c1c03891070003801e0618040c401d0004109043d06d012110601e80b003250380c0e4400c00001c0c6806003907004040e040e4800100103484540b000032030046030030b200c2e6039090340d44d0341e60906403502c5001ca110280740c002882d0100d007400200001c0484082e1078103207400d00705070710703014030324115080708601e648070380e10016410700c0054240c0589481500c0c154080c0126070b9192001402c180300300c20707086100310000b0401c401c88a5955069501440d04440050780790261400c1040e5150650104814507121700e00f400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 628067553 1250 628066303 628066321
    0x172b0905150f07201015050a0609030f050a1b0303030c110a06051b13030528060c02030d0614330c0a080309160515121504051509 57
    0x140100c0d40b403405111583d882c2002240c0148140824215100c0d6010310040140d404000040b81030f0004100028a841c241484c460b221001b544281c4c000c401d4480208862a00095030f102101c1d00040380424482e402d10b4000d084c100c1422004005820442da0300000d11186047c000c01c1d24400c0e10300f040f080420700c009a03915042c8070784090250780003006400008001350000c41e003080c144d02c00d9009620817101840181d411889400245c0c1c100f03040204140300041013000d003081d07285030307079900e5603a42180300c00c4032190140400b404d0140c59899185440e482042107420744100014200310540d1100480782440c00c0c000d4807070307200d0601403004119004070001a05100ba0346900c41c407416202000e0031502a80162100c900305000781003000000c240040015842048190094500186101004400b1900307035001240900703010319a1100d600c000c030007280c40000008040140e5540c0344038110030580b4506400a4001d030502c010320108201000700c00880105c102e40b1078810760740303441d01 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 628068803 1250 628067553 628067593
    0x3130e0709051c0311030d020c100902030a0f03021513051e06070f170106110717070e2a03150d05071205030408120304110d172b0905 59
    0x5a260f00010402860b420701c8550608078501c00c1c4a401d02e03081304082e000d2098103640000f00340b614059000180d007040703414284595240c00c0c1207220b04008a46654010a607180c10385c4000420b03080e2003490050a26000b04401503000100c0d049100491921031510b03d014103085c041103503c1c0c410744000221041c880c151742c02c280d43d81c142c02803400c2d03511024200c3d00b201e6458841001e2100082a11401184d05c0501d42d020300040d440702c03101202c04006851402c05541d0200c64148003c18007800120800710b10042106c020322046101a210502d80e0251074034051088640044c488a03c1d0080070748a00185114a5440c14441c54240408060101c7c602e40000d008002d80c20410f428003280c001d244048030113038000c07002c50382001d480c1c2004a1618010004510440501008000811800c1c0003030660105054542400da840c441e60350682c2e19514034800b116105010231420000c5a002c5e0f00314508030307090f81c14910582e100401c42c20007418420300a58040c014850720401ca4240490 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 628070053 1250 628068803 628068809
    0xf0f0d080310080a0b0115051207080a0b060a020105060f0103020405030c0d0f050313030c0f0b03060405070516030905090a0e251208090a090e0d05070204020c03130e0709 75
    0x40645450002aa204012544014000e510603842c0e180c000c90107460400c0000203091140f0700d582ca4a50404401502ca2800d00c00800c04111003000100c04a2038080401d58014007613080440c00d9032905140c1201620015420070307088080821207040840d415005280100c100351261101040004011016442140150354150340038401c2c26800b420159190010035001e490141c100c15180d5484605603408040e8421000d100b0301024824440868010130007005522941c8609a141466599071804001c10b407a01c1036650304000340482d4007450455403285c0030f1100d0402d0b41748491a002e404818180030b2940104515070006c8c0e0354001750700c0b64425820494000b464600c030300e418000c3e8440c0d090383d07580107498400800018104c2d206041d010303010344140035250300d0300700d00e41c04c6c4600f21a02d40c0c4251680c0e42000c0c1b10120b141004070b00407500c1c80d000c0c41c0c840c2d511780080c0046000b03407040629110240c80000307801418004444030b400c0542d69103a908060689550f0b0b0101c0711429140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 628071303 1250 628070053 628070059
    0x71b0e040807110108071d0d02090c070605090307020f010f0e0a06020106060e0411070b2a0910020a020f01052b020306010207090207171605070306150807080c1210020c07050f0f 78
    0x5061f40c40a02c104128111056005122452002280d40894400001503605005034500490403e040050600409034800384982c021802c1c0840341d00041e000642503411581840189040c02e600f8031310410244064801c040e01e074807401d95503a04024001e09561040c94000346210032141c2d018a071a000b884000354407060502c3c1003001d16210120581e034007810342440360b501104807850586044401e07494000d25284c52903160003e5006124a40c05941e1056085400a0f11a4801030781c9100e032200c8504028640a074950200c1819038603921042c3d4001c038079400c1071000c00580c0461640082d4825202a400d954116073b0782c0d400d401c00e0b80200f000042c0304454040e460041c8103010030140149040d4900e4681800c0819120b09050141a030010b8642075120744020311281c0c42c4103010710003001c54000502005217003080150715548000c0307030b180c401c080c80c1040c81c2100108000c5a69440a600e40c00c41d0344203024038985544417024410300e409084003000d00300781860303c8904400e43c00009 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 628072553 1250 628071303 628071317
    0x105060a030b030f100c120213060305060409140109051524040204050619110f060a05070309050607110d050a050d0b1507141908071b0e04080711010807 67
    0xc441540a00110805240c0611554021003c1e00300300b001140310400c44a0000500081c01e140000c04520b104441020103d004100c10b80d10400100c01b00c2048440910300000d903922044001005001d0850002d800d45000c0390141f410000c041d03200005c3c40d80701c0ca04442001e004414540842c0c10100c81c0e400c006900000c02c0040060f210a026501e014010801841d0540350310008603070ba00201e24142409081c0d1182e1941c05401599060340d604000c0001d2102c030f010700c4003490b07440a00034a41981c1d2a00d0fa0040341e0b066020341c201042c0141d00605a40c000c1c9001c5a00600c1444040a618001c0c4101001540f01c0b82c0140c0c2154480e02d115502c00385806801e2100c00054100941995001032100c0f00740540350350080003030700300244110543c01030403040305035240c40d0000401440f0904410b0302182d03000141142c1c00c5808143d80440300840360308820342100c3c2c00030100d9000c68a0080c007001000304106800008080e40707403243c0008448550303c0001151b5040c0e040f40c0b104003203442 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 628073803 1250 628072553 628072567
    0x3101d1b06070b0903070f0302030903010b0604120f0f02270a06061403060109030b0c21070801030f1712090d03060303020d050d0b0307141c020d0809031516090e010506 74
    0x4883d1999a03c1222035040740e04d440183c1c3d0300d400381020400425401a00003103290f804610307080c06801622002154103504203404e1545244e007141c50050300900d60040290800104040c1d100301c1d4840707640060601c1c001688401e0500e0802d89950000c0d100c887c000c0340001c102040354132031001540c810f942d40012082174901809006c0d0b00203810581480a038040000006d42c0c4000820310804001036101c0d125003450071081005001c421b181c0c5d104900e41c50802c0780725503109102070b04494100d0406480c2d8049403c02c80884405150010f0301885c00207803401c03020540021060180810300215078443c880700c0800ca045558a01004005801034240300da05a88650080c00f003010301680c00090707840c02c4000191400682d0347c060303400e55201d5843c042c91803034550a04189403a02e150b43e68a0b110403070340080c26112035800300608000703003c50b10384100c0e2001c20000c891109001e08041c001c3c20020105924000c05104180000344040c10216602280182480c1200c601030035640c01d00030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 628075053 1250 628073803 628073813
    0x1d011e0303050315100f0f050304150506011205070309032c06370f0f05030420180108010b010c020d08180d03030c08071e0e03101d1b0607 61
    0x22002d070120f04070200c0c03613030307014251395411016106800d1191901e2071240040c071406828817010018242c1032107070074410440452604104412148002c0b90b0008550343c1d80c00040e101c4080c4117a28840e00c074904020489040d0305580030901c00340c020344030020402c4600044105003101d055010480070512291900c6605208000d04406003aaa8224031000100c4100c43d030b1070103401c0c49801c160300510a45002554001c102981c1500e85440c050000c1f400040001e005441f01902c0202004480468407240f2880c0301c4c02541c2d86a0300500c02c581210200000c040619001e01455040d5444c1031481042d941c05880300f10040d0303074082c2200480140b680c8404550b604800c84204111405c01a091065070f145c002c0713003c1880c46501c00055110407000300030180c0000500b41018405080c25044140880200a070702e01c904524111248145050110b810a403810805100d06418941603441e450070782913107880c0c1015042c00303e80441c02d611840140c00049218072036040b00d010407040e80858 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 628076303 1250 628075053 628075057
    0x405040309050d0606170f0607050c10181203060f0e04020409140607020d0201050105150307020c100f080c09211507031a0f01120c0c0503041d011e030305 68
    0x6406414550241a51240440c0f0115205481100c0003079441a0038080e10000c01e40c04d0640341c041c0e20092032a804030316011641c80b60080e04803001d1002c040b035a01c0c05081e0030800d006003510191014080e458206440b544203d000240c1113485041c0100c8156855109105a100b2118483c040f549040c0c581002243c2c0e0260240040c0d07086a04d40700c0030004603501e81505c108856900006000303030b01d4043c10003420048240145421a41000010810341c0d4412004082800c0205003680e03030781d100c00205925009514040c80d4000c070441c1074200c011600a035020043d00c501c2d40301e189260b51209021740142c401d000c0015408103180103c0c1010710300815001c9600f80b148400c65450f07401d90002403c042c14211030201c0000d80703400e8001c3d44004803003180b00000b10f0035034030313245001030503c00a00001a03022500d003515603a5400140002e204080511015030004162690703551600021a11902840407941c600742410000280b001c4000c111207505101041c4180c1c01c82d03040d654210b40c16 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 628077553 1250 628076303 628076311
    0x70320011a0f131a091b0d020c01090501050c03060a06050c07090e0a170310140f090601181d010605040303050d0908091815060703080a0903090b1308060a0b010e0405 73
    0xc41118080d210000f110f500ca44e91082c2c601c2c1c1d204e080003404680400c0710081006180c0c40014840452504a41c8800701c01d94030b0b4103940e1080540c880c82e42c0003100d401819548009030403582007105000c82510420300940c001c95052301e030030080940f00c1906039420b02c580305c00b4101e00c1d48040c1e010003809603141c1c0074400350740804068601c00e103035584650302920095800103501240000510200103032031121000141003000c186803180002400007203d01d0100e800303003402482c07503c0000c1c1c0e40e84c0c4110010010b81040c4407401300c40c0c40e1102090010304281d0007d10300b000b440b140010500d940103c0c15502203a605942d0315107001d40b20343e0f410024107251030040380d0b8507000348552206640c603000113000740081042112240e00d032080c081c43c600044d07080894014201005080c7c01300c0ea01c00310742d5504c41c00c5903001140310903007454100c17800081075005680d00f500124407400e03007a400120040c1161900d5044540949500c07590b40c044499403058036000c2503000b20021040c0c14260002c90740 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 628078803 1250 628077553 628077559
    0x305010303033e07150501140f010e0d150603030c11010801030c0b0a030b1201150905101a160c03140601120b060d06061701110f040b03040611070320011a0f 69
    0x805041c0d5076280d41c0b043c01d0100410a960b01d0b40018841038142e03da205010350000c07274099210030b4000d00043e03e8442142c492902609820444800740301210900e8104923081080400120fa66414014a5112048401c41313880c4c07413544040006d0740c4074404a5060342d401040382110340b40b50045c41c2e0300a9001000000c1410b890b40004202a031700c441280300c2c00d4100c9000070480f000c510114200070b40054000c40c28103440c02e0103100c5150b032401c12190541e040811401c0d0b0300c0b41d001510381400e015000d0301078450310008890000704803039640e5202c100c0f80b1800a0780c10001c0f229a800d40c0f9001c3c00d0050740d010502d080d0668001c1116290203541115003c0c20927a001c003a1501d80009440d0290407500b018a0030640c2000c10b803000b4460000c04d000010022030410303442d1405110741d441140f1510703111110110100d130501c100b6070300801c9044005c034500c075940d5416240250002c000c000b140c401076250010b1402c1c1d6068180030f0440c0c4030695140030301c01c1c8180141009442c004011807550 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 628080053 1250 628078803 628078807
    0x140607030c0c0e090609070605030604090212010504081c0219052808010f05040204080705090402031912030e06060d030f02100207050c1f0207032009070305010303033e 74
    0x11841c000342d041c0251540c2c010455152a1400f000d9107061406080c09203660b002420410401d9030040039250032001c1120302080c103104900018400107020051000b041d46040203000402c40325034028100d06c4800480d0b104240030700e900110480c01803502031003090303548000d10000d00d0305c0740c401000b18592002100c40c1d5002c0750b1501000c090307020301000000c40e154a0060001c2c0e00b11905d4a0002c100856042d494203041004c05601da442600c6214010900d00001c00d086603014403000c2e100001d10704c0800d012020701e06048540640d03170064038000c42d1401030b500651000100d01d1030311840d005010b4005000d0180c2e000c640a4107400340300b104500803036450041a41c024002410424012001880000c0366142042000c1841c00340329043c14510a0742200d103190042121030490b60460011490940e400035259556800003c04a03801107141e803c2003090b9801d0f0740114140ca00131f603400c01c1241d10b118010300001c0249842000344003031040d65951039045c6005448030b4140c000406034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 628081303 1250 628080053 628080077
    0x302130905180705040b1302030c0408120901120605240f0a08090c011e050901090b0a02010e01110301052d060304030206071211091306180c09080714060703 69
    0x1401c9680030b86078207908146050941d03102c039908020b1000a44011542044841c0b0484005034445407110b4504070015000f20000341130380100c41c1510010081c10060310100030340800d40000c44d5000c1c03102c00b0301046150071140c2c0080020b00c07802c400e41d5805020040c01840faaa020740720700c0b0b0b030f40090300001d42003004074010b440ca0000190001c45001d440c1c80c0c03417509002030080e0401800100f03450402101d1181c03400048031401001d4a038504900f0410759914246004031540080c80d002100c0800e80040c5c0c81081c4e81c0e0561120500301540340080ac0700d828a200c0100c4c0e00e00c820320420707904c40d50581401030039840d0034a440e040011905601c0c3c00b496070f020f010402e181c2080b5800d50250b001042088501c44d005010201d0528680307004000d00c859821a601c2a40a0a06001d005403401c003010031a00786194004e0024200428428103890300602428000d0038900c4a424000303882013000003100c010004110307041c4c6030001d040349210b040e1182403101ca40c218500940403c03021200702c03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 628082553 1250 628081303 628081319
    0x4060905010b0a17010f0c0807200601060908060603070f060f090512060f160c0308060f18090c1509010302091c08071a10051c060f0203011d0106050307030213 70
    0x540010041d00c60040a803d4544400d18212060313401b0307484540381080704c98003080303901407406a4040034900700401603220840f100031407525208507560603881400000b1032507070f0304001c0785d004558807441119043d40e11003060548540720707481340580c010b110340c4007804494006d41003403071282180d01e403039507800365180c0000e99220b10343c00d11000b07640c021505101e001040b5010466201c80c3e05a0070b22103d1001c4c030802070040d4004c52001d0104002d0f04040b40303403503441e01c10140b4803010007000134010810400d0035100d2801c0c01e0324030b01f405120300d40ca1807400c0d041c01c05142488400c00c607a071604040d403000040d8080e51143d44403560008004003c0c00120389c80c100341d10044e42c000da00c141d4030b80006150ad2044050a0581080311800c5071041000103141220381d0001c0e03403026100100c12400d40e01c2c000f00034540c00341000f001c8600708404499049060f40c00f85040703507070103200002c9040c5503400442014400f07001d5680040d5041000403210740c000e0300280700001c600f002a81c1041c0d650112 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 628083803 1250 628082553 628082569
    0xa09111201091a190b0a050405040e0607111f1d0a150506010c1e02040e010e060f0705030106080f10031403030403030e0c10080604021e0a0f140304060905010b 70
    0x100c0c0e80e0040d51600c81d04800140105440983c89090360034046080261211000d24541e40c440c06140300c000241d5440024806c0054a00800c400b800920090948801298444804649010018002140c0e20500d050000350381004003034240340f41100c0710800040300300600914583c0b1500d04030340292003114890101f1003c100349000d00c81d01c4411191140c00541520307009080c0718100124148010b000c2849070b85072240341e402440c042884a40c1c684080390292400c0c080714400c0e03519206804204980c0428403601c0345104118698013551003050944040c00b003070090030001210140024201c1c180070105d690001c2100462600d695a244e84200c010f07100c02d800c03881c081d040070082c0b2041540600544c00003040d03800103041122000404149550a07803a02d540c100700030350020904644480c1c0c1207500c0121003c1c20f5441084455203948520b922031030016002422642c0c3c14412a8400c0d03510007051006103d41c80d146480d540c4418000e0015110241c440e55030703802030066141c0d1070840c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 628085053 1250 628083803 628083809
    0x50421050a0203150f060f0f040e070e16110f250f03030917120904021c020705030c0d0c0f030c02012601090e0303040209042301020403110a05040b0a09111201 70
    0x100c62134283c075019030696408007015019500600001000c91100e40e640030f2004100d02d8141c4000070074a03c407440c21440d00c0c030b5950000c7c00c4012242e060044248410102d0350b01c90100f500c8161801c801441c0d0541e452901c0d0444400c0d41d040710900006002000b450852140c685445404100d6128010241100b100d0b6100f14041000c1d40313004c00091404103102c00350503603190041c082005032003840c1c9110707200c1c07118114401c960000780c0c850026925030306100891000c490841d11501d0300e181c0715503a5400022010792521405105100c110301c00e41d8400c80e101c1d446941d904441e009542e00f5101500010412414000e0000c40c0d1010440c4002d222100d02d00400b8009640b54502000c140450b412101c180c0c0c480e410410030880540c0303414045a41095002d060840c50740780d64005060040d9801e03007954441d5000043c004203000310302290700c44090007118954038440d590b400b0442118000031010350014089581080041003942c00b8901c1c1b844036990880c6400c0e800102c0071100c41d8260 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 628086303 1250 628085053 628085083
    0x408070b0901060e0609060a03060209031207060c0806060f0f03040f05030703170601020a03020705120f100b151c0509010f0905060f010b13140a0320030d050421050a0203 75
    0x40f0402c545460b0b0140241c000340140c901100c42d05011000c21000301441c000900403a80004108106440c20440f00d15058040703118280c4460303603843d0840242c818a201c000000700d40c0008503400740703400d80442d000750034001c03c52454003130302061510300c1d500014426a80000c0c003030400804504240000c0c5107a80c860395038a4140c0445590500b2014800341050f81198003800b40c00340080d0700000e074101900c03403c803195465101a0b013181c51401545540d03040c0746020744c280d07a034001005d0760002c450f000003c071808822190b0b8070b1600704080c061101c800424102c05038081e1080e42d40760380a990049075070fa00210307125010701248016035444a07021292607000100308140708441e58a524054980548642c0c0352020014626804402d80d000740b1701c0c01c0203c0c0c43c8400f829540c060b030420081d90b20244c50b07030f00110400c42c0701c1041003150201c280a40905c0c1c644e80c1c0801e12401c00c44090725046020390002c030407081c1d140d9241090f0003c00312800c0c0f00f10511000540d90801481c03100403942 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 628087553 1250 628086303 628086311
    0xf02070b22060504020d050708030d0e010c05161110050a030e01092105120c0d0b09040c1a0405040f051609030203030306090411040504140706081e0408070b0901 71
    0x191400d0454000010000a0a07454050515a08411281d55a42241d0700a0004034594807280001140c0c01104407000302580f24001001a80348004000f905445c0102e080c200600b000c40754983d4240c48103440110005902008208030340381c07400b011010640d0080c4402e490414400c0d001c04c01c00c00d5207424100225001040d074a400e2079141c01017500c5041d20000a22442c5519a02c0d001e41c2e2015540301700704046032101d00f0500e503114a040d60a0360244165240f242d0400b0060759605500c145542e40c05035007003842400c41c1d0f05102d5080c1d4011070313005e4000700306a0300e0018081c0b80010001c2078406040410080002c8503941d03801400040304140303800042e60300740440050300d0498020102d80600c04000c1081001d84d40c040240c950107035095074024002e40e00da142000f05110b4110340305900501d00028030040c09084038030f00240c010076130100c440300e40d2181002d544451040700c010303121040940860f50351081d07040805800c0b512030744030142000c40301d59401c0c8041604544100c0c0581d0340e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 628088803 1250 628087553 628087567
    0xf0e150c0c061201030605190c08040b0901091106130906080d08090a050706031104030b070206010e01170c0f060708030a0e061617040201021e031308160618090f02 72
    0x2040c050100501802c40300c440c64101c00307008421800c0414400680722a83e0303840040d0040c03900c01d6640342d1600001d40108024107030300d100038009003000d507001da5905010100141c0c1c0d4030f0052080e444c026402040603c200d06116080040d03541c00012181410603000c24001804601c50040002916042c006016035841e00c0a005000007001091910940d022804900c0440c00229105099a10515011846540040c0e200045d40318550000300100202001c009030a54040365080c140c85100000c0c0445989c0c400b1030100034100d0600c86002e81d0007583c44008140b0700504540d04411010b003030282002c1c1c06450303041c4503420491740c00860603241e0140d1070403800c0520005038084240038a0034070506800100805494000c0302d00c401e040d060301e01180c1968002c00c12040000744240070603c43c0000100c026481e6000100c140384d15910b40180810043da001c5041c1000e0034074040440030440c500170003112480c660340c490f020105140c010102d0404114090007142070302d03014016a540d62 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 628090053 1250 628088803 628088827
    0x7050c0d09092003011e0302060406050a0e0102030a020d0509041b02071a0f070206070507092d0515220501170f07051309050c181f050109060f0e15 65
    0x1506506401003d8512001c02e00351040005030b90544400300285c02200301c00c0040302c0f031740420a0b00701079400b290100b400224168007500a0202440035030f210085240c03001c0040e81c0d64000d24a0410260704076141c0031603098402c0d0060880d5070340081c401300b007001c400c4003110010328040c0c2c83c510050b04045d900344118680d40900e24803601980700d10b0340c40d00e02d222740d051500e8061044000e11604000400f6424400200000d402604008804220007012610301190580501c2c20981c0c41d42d000855141e107091481c840c043c4620894240d008510712010108a1040c802078444161a8a0140f04070b48105851249a0180c00d03622a0f03602c0790354594481901e880c00b20140820654843c2409229589412081c00290403030010041007e02c280c0c900907080c6045c20142c20307013044203d41d21240460003480354501403856505031024551460505906018060190a0204066100401205101c0c88481c603641c0407500d40f1242104a0400007245444206c12013059007402244201000f4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 628091303 1250 628090053 628090061
    0x180114100c03050a0c060f0507030b18010e0c03100312021f02310e0c13060903050303060d060612060903030c0c11060c0c120105040605010b09130507050c0d0909 71
    0x42140c1410300038070407242e40091482c0300d501c40100410a00c3c4012108020349600014203d09003020280064544008020010b05201040760311888070004d0138842040031524680c1170300c1844c015101903075103002415045a10103000d00004c00504140000440c0b907040500386c40e84d4a075030182c0210228030184206400d601444d2036042841000b071442c500d580b28056201d00a049946200c0e603d900310070601d40015241d010348a030480d10b004104082440304c1c000e20460804c00c511030f03c1c0c1074407000c08440c80001800b008105600070000b00b842d9144c601c00c406040c80c4601d6000c80e500342c4072410000b8000c84494111100c5072a42200c83c1003503058090b840c82c04405107011a481145611051034040740c2c050924000c007400950541002000c0c456401d00440103843c14841c0c035803807a0820300130601101d00796609440c02001180e00c0d401d0000f01d41c90801b005207a002c003008156001c400a00020702103109000081152454403202800011040625502c40c90354035454010100103803 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 628092553 1250 628091303 628091329
    0x12081e040621051510020708010f020301030218070c03031812020d0809120a2102041e12110603060d060c030902010206010f030206030c0319061715091b180114 70
    0x40c0d42003d08106008540281ca0003601c40700300c8000704000c07880d010507414050350b504040010750805d200046000540e40046049038030940e40c444c6040c0007452201c2000d04265004000200d040c4038035008248a07820040151002e078103501c1b4134501c02d07680c042c0300300121100503015130465001d8504080e0802440d903030001c980750213005e4025590003401c1d02e03482402140e0342400030300701c0b03282c581c01c8542c41c2c0b41c0304140310360b0001c541d920f41741c0b142c2e5801d90051085100c000c400e4984089007d000e500c119501490340103813a14151800c040400c140303038000804981d0004040400f00c03001c28614050954101415240080c8101c0140002400c080058102481848901c0403c00c010384440b02103a510540381c0c0304854807038882c4604101c07018a0344420200071424460041041e1a20a1400d10001900000c4402c0c42a4600c4204880001111204030541203040c4070f140380101041c8442a086c2c006041e0a01d050710fa64000d08001401c0c0c01840304501031980b803641c0780c101418400b000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 628093803 1250 628092553 628092617
    0x507030f15060801061103070210080610090b0703030b1807030f0b0a05062d030708010f150e090604111b01110c07060c030e031e070f12081e0406 64
    0x40d142c141039000e007a2403410f204050401100c021340302c0d0404818800e4482c2c0b160300402d4042d01d03041e01c4000515001c8151652403141e15944201807505018012200c1182c01200303007942400c0c1c460b1410f60040202d40200360304140c05039094140288120709840c8101c2050b100011141c2025034804200e0f1003e140c8207020300c081e94024010f91b46c500c810b450391681c0d890f500c1c020040c420900e9000c010010119280c84040c0072040c030640700c2e04800c20f2410b890b2140340501c1415079403010807040c400791068500c040342d00c814440c141d6060400e00c09500c14405080461024020141c0c58516800200354140700c0c02110482d01c000d0500380102c3d4035918020401505100c500650030b034903010365114580c00c0c0818140c82c0000c045c000c962000481c07000400796480c99140c0c41c0640f5980501503002074040c019240d010a2668100c1700d010240ca030101c40c2072039014a0b80d40d960001c0e60004c1d030403080034001d260f0394104000141000300040e12140e40c0da9541c4202d008e00083d500101450503c030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 628095053 1250 628093803 628093841
    0x15061a04030812100503070306050f130b07120e0d0c0c0602010623150d0e120408030f03192d02070f02061804020c0c011101112b0507030f 61
    0x404621120181c83c00c1d4401e000d8100741548035108901d89044503607100da50940249000007060100540c407442c40717a1079240312a40241c0d504840542c0d03880d4a544003c25452800300450210340c42800c40741080545441c000807961480320380700b4544241d410019001903100c003001c80801506007118401040640000c1c0846402c1144804a120702c001545900c2041c41020300020f82c0c907400314406400c2041c13100d40d0341d046140c2c41c488c0607140405010203248a04250502911540c00494048956804c095410b2864001c205400b80c3d10182c0484c43d4080000b060301003c0001d44944804403011444180b80e2042c01c0000401c00c0088024002520b88103101040104902c51314254080e40d04441555440d100c107020311b030f888234009164941092004c1a0350b5034408000405001000c8242c0725016002000d100e01400d841a000d0568401141030140c00208400444500f40c075000024075000c01c0544099043c003250302c2261500002a00e4010404480c21140304804c43c1d47c10b400c102074 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 628096303 1250 628095053 628095059
    0x406110f060402010f050706020a08012909010e04060302060f071202120906160b09010f0b041e0513060e0c0f03030702030705310c2c0f0d15061a04 65
    0xe070301d07418000c00103414000302c40e0310320550724424001c40b44426441501152039041d03080e001009604c0034041d80800340c4200055001419100080256003071a0100e40d0740340022840046402c21143c0400b00d41141c2c0740c40c004001a598400a0030510a40e1210252200e026003000300d407120030119800155000f8110010240002900b03e8601c00030aa0360181e40d4008240c40082400039588040c1c810031001c0e0502c4084e03101900045000b03280c148083c007020304164104011038201441c2801d44100b4405034400400c500e0700b1840c0d00c2032510032080030b2883c041d00d450007903035403800040c1c9268102c419000b68600d86075100329011001a001982000201d80c007090f42c44615006403031140d09840c040401c52118046a800001e080c1c048420032907004102d400003034107135003e840c130205c1c000d188440206039107040700d0001136001c0c680258110000a0030300449000500c003141d00811305800705008203000d03101c80328a51381c44400016481c0e20380031286d900c0342d40040f010604440100010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 628097553 1250 628096303 628096333
    0x121109130320011e0c030209010914041d030405040c080c07061a1201020d1103090d05090411210c0a0203220e130b0112030c0f1a010b040611 62
    0x30856259041c14030342200044504240d003810440103200006600340342060206a89660340c040c0c010556140c28041410740050a070203034012540b44c00e0000d640c0200c2046010605181c240000c0d101503c0010880302c4a2141020003181c66210700a56000250801290070301d40b09200fa90181c920b0b2040c0c003410321514070030040c440c4a102034041c0340c8400180614501d003c050301d132044002806c81c00619940c4051070301039005590390b591903500c0d042110007030780c42100031039208408880180822510f01003054625130840c0710216001603950a007000074400307400c0209501505000d181100e800032010160800c0c40091221780d455506005140e81c240c1c000059a503622850958a8000840c000e2401c000342010f03030007003100081c410140680f54451944903090310780a8500c481a681e01c42c202100404113003580140024ad0452446001c01c0a00105d20710300d5108171014003c0500f0b40f800c10840b50420717044080700500004081014503040710040030341c81e4800c000307014105442860 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 628098803 1250 628097553 628097581
    0x120d18052a030a2a05120a0606090605030d0c080909010f0e0a1109210a060219050a0c11040212070206090c031b090903040b0f18010503040b060f03011401121109 71
    0x4070b640325104c114445600910303104040000d880003a00340c0341e185080030202d030756074248120300356007141c504540400e80703020a0240380e05030b40c80500182080e43c091101120f40d8652018165002c00052240d5030742c0c0c1d5035091600f0b0080c0b481c502e88164003401c10402d60038a48001d00f0880c0841e14003400082d0710001c000c00c2e03810340c0200300c55030840c20b000081c400d40340c4410305281403424001c1841540400a041d4042c0901d880025055461005124001e503001d10640c030804002c210a0500c0310001040559001345815001e0400b40c2855070b0480d80710b566450555496016810600401c10500300401103a800310404600070004410816807103850741852922940c0540049030014006980405c1190010300c414008a07540c0c0805400b10540e0f80c01c2000809031a94200040d00721640c07080064900464118611041039101c80e010807040701c240340134285e09552200c50a0800c04040c030031030387c000e00362005004a0702e43c65181500c2e50101c0240f0581c400c0303011405100c250040c82c2c071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 628100053 1250 628098803 628098833
    0x31e0309170a090302040e0c13060303020d0207032001051611011b02060f1b07030311070902030910052701061701020a020601031401290a08120d18052a030a 69
    0x1b800280c078100041e05a410f000301d20541c00c1d00142d5a0358600b140000540c04a41168000e80c2038501c558000071040340c883e0940c0c8405070407681d07400705090414007021f0003591044014100a840c01500f1f2410214040e900c40003528480043c550200e0956003144880c46202522224400400c80380d0b03000030f440307014801d000d020f500008619040d41034140d413800c080c0710780c004044411081e664900140848001c0142800d00e0051040004800d2401d0003620b008641010242c0018a001070840e80184001860054180c80d00d244030f000984650800b4038144000320008a05c950070004251203401c800040840c0d41c7c2c1c0b0420800c01c51340d0340492228150b0741d02c4552607411885850720305024110480c110540202a84001c03046200014040c144480003515a80280c5039909042a01c0300000503018000304003c2141c03d810710b1055102000c02c18034000d1140484207103031141417500c1c4880d1501100214005104030030360204000400c82c0c0c54045004040112150380c0391000741e04681 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 628101303 1250 628100053 628100059
    0xa03090203070b03090601030c06021204050d0302070b130602010e07050117040c090f0905060a05011a0c0a0803070c0507080706050a0c080c0d02100c140a0507031e0309170a090302 79
    0x2010400456a05000d1203006014951040d600d904199003800c3d00c03030b0028813049419403009240011307080e0010540c031030713078249100320356042c81e16200900030120624441101140148040800c3d502401d8001e032140c40d078400c81d41002c03141851406800c4450300035007400076034880304040081d81c0e0b008039160301d4001e0907050515107848600d0480d9100720580c024207003160800c107070704034814240d901503142d15005908498403520340c503240d50211a428001c110610b0800446003000002840003050f2000a6008640c4901240d40f1210743e80d40040d244440041d100151f104207000080191402509001028043c1d49180ca0342c00307019482411150700134042d42c075442c00c060148440946490361a40380607a40491040c0d90001e4841c4200c1c2c20400d8654a426011406540300302090501075024845030362038040c0c0598181e840d40c105042c1201008076240f0166440c0c540000130445491007071720b010845030304a2408102034920801031a005034018400210032907401091038007103039015 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 628102553 1250 628101303 628101311
    0x30f0c060d02220608070f0c0b0115110105040506090d080702071a0c0a2d03050912010e0f0303070207060e010e10030b060f040302030c03120d1505091303180b0a03 72
    0x141040c2445041d183e01610785060040c0000500b00f6040905184030f64015582d155500c021100e0a84203400103c20240c500c81d02d0f000184210400603581c42c0d22800c090a014091034500b17003803c1e00351001214201d8458124900f401509901000600742101c15410108024070380142c00a50398041d51096000000429000100704c0021408030340a0b00c41c4281544c1240b01d00341010000504035112004d840280030005c028410a1074800c0031110382c0c583e81c3c007454206410708004a40000c0500030706255601c003a00c0408620400c08900c1140000380655124030340008e0190400c1103582c008000d018a00300381042d240ea00900140b1585c4e41207480c0f045451031240d041700100041121a500414001020022074040703102a008480c400c81c1207642a0071303d08181500c41c03801e80304d50940244140310608807510190030510204071820400d0510325640d0002a000d00c8040c0c1e00500700950f55884070007403551044090318400c1050324107150360381c035002c400412846080300790000c160703031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 628103803 1250 628102553 628102567
    0x10e030d11070606060f02070f0605120406140112110f0d08030910051503010b0f010e09091f051e07140c0c090403051902120306130b1806030f0c060d02 67
    0x140000340c48601d0b410030010401ca40d241e0b0000303003030404202c051b803001d407017066000680d1400c5003007464261846590394030b081044144800c0c103d0070b0050002c6907526200c90422041c0300c50001c05900a01c81044041014660780c1401d081c905094011207010f5080c000c0b2500755903d6543c640c6d1051903100300041d60302d03540c0500040c00c100702074018003060390401040c030002d41200700c100d59a41c00101c1c002c100c006c441c40c04000e20ba003035031034916022401040c410f00c894a866608180e0100350346040d501c0d51140f50001c01c0b044101502c0b2030f020550740b50140403141440005ca8102d00103c458100183d0030041009080b07105050700c076a5116030006001c010160342805002e500c6480640706c01200c0c00d2070f01d00a400d42d0001e481219a03016018021113074144005945000c1e0b0001a1580b840d60f02c0345024000344900e201c880b00d0f00c07036803111000750103170320b0340702810708025000c40c88605c3c242044005c150901c01c01c450302030629440700c502c080c0140e07a500200c070300c80c444007100140d442030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 628105053 1250 628103803 628103831
    0x6010513020d06030b010f06020114070c0c0f030b071209050604120c0b0118050916050f2d030601060e06030c03060d080301031203050c192307150608010e030d 70
    0x7181c1c2c45503102c01401e11500000300000401014143d40c0440342d089412515004100c0c200c0f600c102c6000e005941e20300100d010103014503c01140c560103420080345081c0c85040000c6a0000303a4821075600041a0070800f0043d48240043e050307100126051021180603250941c0d00c00c405070010305141c800e00903130b100e1140605003d900300c036404942c0e00859a0366000d01c56408908030000c08809042000140341410041001c103604000c000028010303034182800c0c01440c0d840094030641103200000d4598001c041d040d240d1b10081c03000501c80407000765000034103082c020306910204c203106004807c28400c0d51240e06480d40700005a140c1a00da58a140010302d0030494148050b001180c0040048144415201103400750140c43c0c0f02030080b0f03112510500224490030810f02c0d1003094404c14003009921828000440700d440e0700002c03014290141900d041540990030464840105840000b0300380f030303d03000d044000c02544008001c0141c58806a84c1c0340e102e4111400500369a603401051400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 628106303 1250 628105053 628105057
    0x903051e0d0c0c02040b012f030f160302100507021902040b09072a0201090e1005190f0806060d1401060b0a0807201f0e0307030816030e0601051302 65
    0x1440c0e11051160003020b20001d414065016420b0b4002c504002054540b035010f550440007100d80c0f074013214144242400c91440036158115100c40f00c0c00300f00500348001c05400050701740c04580e19030b9040d143c0304501d4042d151501c041545441281824100444c10b80c000c20300640300406071241c1c04c0181c2051002074002d100d40356215620500100521044582c0310700040640e034100c11000a81102c540c07006852101c02207402030006d400c101050100100402038a50017581c00b140f060725607616000040e010000c2285400c4881440c1501089074007a20a800c4004000d41e1000d4601824004007241e041d0030b11000107070800100656540060009602a2004001242c0c41c03685945040340010211101901d1000001c0c0192159100110a02c080c1c0300c1e84c49040b40080c48010360080313150b941002c00c1a01c61341e00c50356816003a807030070301d0610003014124031030fa580b002e2074500300c4800000e849820444d24201482c065444554240000c0e52905542040b120b400350703416100c031608064 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 628107553 1250 628106303 628106317
    0x60c0a0c060b0a030f03140906030105040f0902030111090424090905030c10050a0608030a080423120309120f0f070c09020d0f0b10050304140a2907030903051e 70
    0x3c200441000018000414021001c581c0309603a00d00360000e000d640c442107402940041030b03000004200412103450075500298a40680e48000719072000503400280c04c48408240c4013940c0c91001900e06101d2400e8401c401c0109110421996140031024009141c03080034002d55410b41c1d601c5480d441030100400680b08030b80e01c481b040396400001004004042c0a080d21124425800c2101c0420311440104c1a601d0b0b0f410365507100d8036580ea403920f03401c1000010800741406224803e038440341c12a41440740c5400c112022080c55500d08042c05580e280ca1540e0702030100e114814400c10499045040c00c480413030302038850352515154203040015550a071940410709140c8001052a11038940ba00720b40b81c1d07143d555400b00b02c0144100144803940c0041c040700c030002482000028005080503904070721144601085624401040d40c900b070940c0c200d03c5003803010b03c480d44001010480517080b0300e64450710924060107243d8651742c01030310030700a0080580985081004441410030b12400303481d01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 628108803 1250 628107553 628107559
    0x24030204031b05030106090902060a0315050a0803181804080f13080c0405071809020d060b03090f0706050a0807121e0e0c0d050d0c0f060f140603060c0a0c060b 70
    0x2c100303010728444856402c644595030181d402d000c4c000540c240c01744240080c0d0398001d895185040c007111700850040041c44007680c841040c1400100d00c5031280c03950783d4041c200700d100956440500030245890548041c440610441c2e540c4200d603d040303040e60300190040d40c01500039403603030314a20502c212401803568884880b0a01800000d980303000140450900c1010349042007a911520070844603800485136054000b042c41c08200305010940c3d008100d4020984000140a600c0c2d1204600301d90042c0d641074907951003490104884030060040030300421090801516241c12044c0107030025100900c1c00c42801a050514558416140c001240d102e03d0b03805840c24151850035940c000780740740c0040c0840d034814403492a800b418007800481c106904078005003040c8016080449120109907030444000c41c0300079000e000600603004010288030300745404103994a1404d0071345c0001c44011b0000e44243d01034404d001c00340008c0c3d01143c010242c80d14000b1035840c09401c114002e4048c4560301c44e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 628110053 1250 628108803 628108823
    0xf02120304092d050108071710090803011703160209130b04061b03111803070306090c1508040c0e0702070f26070609140f040f0c080702072403020403 66
    0x781d8109140c42801283c01c848003050703d4601000400d0046030401d000700301090740050300a010305120801c8401c804003000d02101d610740c100d8400c1000703840031044102ca0030b280100061000200250301d85800c400d019000f1070800754800c1d0001c05140042c0e10203401200408040703840c4a440c111a201c41c503070850007120541c1403614120004000c2c201840c800190b09130030141c0e900c1c1c0b1a0046400035080310b01e44030700b0152600a80000c40721101e0300160300d40700766000000011038a004601002e4064550f9140d0a4544405400d0000e808030300d2a00300300080081200040700811514290344400744012496034801c80b09030700c0d203492500700109a005101000403a9288104582031000f1440489100c3c50000c5854681d514044c0c0142c201054840b50144280340c1a08001c10000c070000f003501d0082c07210400402c3c1110100d41c00b01076550f49a52806a05941081040390040c5003407000741086443c03e00300600024008a0003860700c081c40d24440c2d1803034402c0d0155001746420200c041 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 628111303 1250 628110053 628110071
    0x30403120b220f0606020312090309030d020c09070e010c12091a0d0e060c0a050a0201020405060408010203090705091e041a07080f1e0c131a04090b0a030f0212030409 73
    0xa855081c900d8242d80401c0c20490350741064251030140d50112103050300114100300d00f101e541148542c00502d02c01c00c030f01c0240075510090360100030345802c41805030080d0000c00501d00c14400c4c03142c0c00400140500240c22040703600c0782d0f8061004194541c011880002450b14404211104a999401101103400514079100021131b8030000b4808034006242c200052032241e0710450301d0b01011102c040b0004414880001924015001811a11103501c0014941b649407030000307100740c0007600690102e82d40401004050704040011030041c184c1100ca44465280501d81c015803c85605184034042040e032000c07900300122003c0801c2c1d940010415a441c0d0700d05004020400b48007103940c101c200b80240081603c40301c1164000c41030300c0300e80e101403000366107440c0c41020329030081d04010f10741c07401c0b40d10026070b005400010405080b4581411030342c440c54242240103460360020482e2081807070500810004500c1c191f54000f95a0540390100d4020b030060444e0309500850303100b00c0348203090060039 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 628112553 1250 628111303 628111339
    0x3180a02131a040509030910030b030d03060611010b030d2303041a0a020a050a110a060e01020901110f1b0a080d02100f02030412140408160602070b030408030403120b 73
    0x2015549462442d044050074581044140c0340251030040141e00f040103021814140400a540196145e04010070410f007144042864030101c2040035000940d12072092220b587c1c054100f420b01e41000009020011034100004d464414540355401444141098502c16070000c5186070071400520340015100e1038582010094800c005010040350180c250004441060ba032007900d83c01c80d0b10b9a200d905110302008165138180b04004c0d640e0070f51003020038200000c1e6090161340002124100056216807404e400507002c0002c9540b2040c01d9045a51202040f640026078000311880d8000c840202010400c08180034039180d03004042a0b0040035148858685c000420745880103860404004190070040058120300007503c005200d007002003541e207006449640641e5107a10b680c291a071806517a4290345203401e44103260f406031807842407020020b0b83d4040c80000000d1402169407480c51030503960301e4000e80302c01403008042c003e600c81c4081c0e4030075140d880591110f4000c1d00b0300003032030a08501c0b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 628113803 1250 628112553 628112561
    0x420307030f0c0e130204150e15030d0e0d080d061d040c1409040314210906070309032c10030b0a2301030207050a0203011509060602030a0503180a0213 66
    0x1c19240030041c040001941045254910301c20044a802568240707840e07070070080039000c6003410307405c10100c0500228905000403c00c43c0500c032841c482d1400d810028040c5400c0c0740302001c1080601c008102c24600d2034a401904003845030f40074001036907554581025500400341d5400000c0c41c440c0000214850080a01010b801280030301900c298480d42d034030704001319a04a00301c1036048807560003c90300181c019440310010082000c0c0c0c00e403c01c92005190a44400040359199940c5a480d0074095204428070074a0f0b0462000e14080c860310416440181a000c54480c20440c0103800f546c06045043c412440d40700780500080c00204034180c0e41034014083d0010004840c41400e1442d00081c180b070141d01048040722000c1c8d900164042070600540007500001c03416515030042c4a442e00040e902881140700704d00f03180c0710600c010740c00c10f00800100c4d00150885402e642c01080f07029041078200341500d610480f1481e5250702008050911400c22001107002508203000100c40004214aa00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 628115053 1250 628113803 628113833
    0x304050a03080603070f150c150c030608010203091c090b0a030b0f040903080a0b0f0d030f1e0215040516080102030a29010302030903070c12020942030703 68
    0x1e200b00742d43d25003400f05034403944984107044a42c1e0401e4410005516151047d859681450504904060494403031b034005200310700f400d0200c142c0d5030418003551703509449020043e20315074000314190f280540303009660300320f50314400110000310400314500c1442031640c200034205c00c008594845100500150240081c80c0c1602d203d103103090b0030a141e900701440780c2000c00740c0551311100d80d0703100c1d040038500a0a050a0490300100680112903941d1510789010003103611a0f550b5014006a849004200f126081d103111041022104080d40b03003039002507005000e10300328a515003030780c40780d240603440e040810303545028110b0810b100180408065021b10710a520320b1809014030705044154038442ca010440c01451038080100d10440365100340d0145a010300c3c1d003000c49141c0032403910340c04800d001940c00422002d0080c401d139411410300589941e004550340400e80c00500d42c12218400c030440c82e202c0c0000300d50148540c4980c51000e001002c0781e104020f81030b18009500ca06002c2040f041d100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 628116303 1250 628115053 628115057
    0x1a07230a030807090602030901080403050313060204030b06041103090c37030201140f0d050408070b04050c2b02040b0f0a03050312180604060f02040510030f050c0906090913080304050a03 82
    0x4c44c0028054008403c81e040b0b650165240001540c84d035509403501c1c0c1000d40042003401d104040d034400a0650300c00ac002035401450406203900d050400c2100381d4095402c0c80d95004004e2090010320800000c0c0c2e240040c500729542a25107542080c100d00303509554880c0c452202c000002c011035030204800d80d8040c1c074002c0c0d03241098902c031680140e42e01e104080b10030078041401c009041c43c0c03140e0b583c40640c20511a00e6030714a0700125407a0b120000f10255001e40f15034014501143c0340345008250300841800d00b10b0032084180041d0303081d102040300c0320310190049499119094540d0b581c00341c5c0d02c0031210010410200c0e00e03140c0c102241d0302d81001e801c80380030f014948081540304481840c40c00c20102003400a04e001d651300d603201005408102c14000b4555020300021545586020020040d910340da0f9000844000200134001070b103001601d80003d40034100b050401c0ba40310320084500d514402d0300c03403074159115510320b1a0790110b044805000500080b052004000020400d1840c0500a03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 628117553 1250 628116303 628116317
    0x5060a0b03070c030818160f0501180e1305070f03020306060603091906110414030d09050a210503041203020609060c03011a0d06031b1a07230a030807 66
    0x1a0141240d94032069440340e010411007078501000074464000203a01c820010030842e012044014018036000301100c00041c40301ca0740ea41440120700c1010408020042460000d009110200400488140c00d0050300702d003000d0070000408a1003840c00100b04540c8c850203d410165070340054034090841400101d00c40c0c02150003096591074000152402404d00c0b10152030390030420380400c100041820003c40d60360b610307a81c640040103c5000900700a0138900707000c0ca41c01d54803a0070181400c512201c0b00342484050340082c403a5468840514041d111803000c1d00c00485902003503001d03940881a00140302d88400103004c5801c0e24a00c0035074112603c44d07000c0300c000340c84440d2450744603101202c0c40121003405000402104003d010181600d14060071200e141c6801c020000d42030380e100c0e400c1030b96031408001c010f15001b41c0d1442180000c14482807031260303044c0c410306003220038820b50700d004c2c2c0700c0c0081c0c07001110000c40c010070032007070070340100c0031100202614940a030604004035071b40c4000c1488 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 628118803 1250 628117553 628117559
    0x150602010f060b2106011218020a09050f0c0307021e030a0e03030a05031506071b0503100c0e040b010314280603030c0b10051005030108191e080706020d05060a 70
    0x301400783c80c801c80c00c2e0140c945400613240c11032a020940104036504000c242d21a0312509001d0b440340c000307100c03941038a00200c220036005000019032280c3c421f403051840c100411940300001e0500b40c0d004a2581c44140c0d80f40c80d03501c0100c3c58100055464005a42c0075000c040d24400c000004200c03400c102e0301c0d10310180b40b8000c00c158580c0100510000800c40420005054443da515072541c02500104003070304206668441030030031800c0880d1a0100002c2500521a40c501003104481080c11290103002c81c800102008102c0a20315100c64041c5860380e001d400740341c0c06508140d42d031001c0440301000303d140c854808008404102c104da4248008920414060a00c90113010700b62501900c64000800042d034803100503034801020281c2c542210403001c070305d5076602d040140401040e55582c0f51039504102c0c039141007411400c249010f884140400d000010320740580c0054a8020807103251783d400250031b0010351803240400c0207101c20310004410441200d981e021901591050700c8181c881ca0f1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 628120053 1250 628118803 628118819
    0x112020a030b03010f0903050d02030403030906050f070810050102190510110a2303130c05060d09020a080705030618010b150705240a0f0b1201050403080f0105060f0d150602010f06 79
    0x50701b410003400148042003116090b0300d154009541080c031a180c00584035a2075103a00c02240c0702a20541841c0c6484020f108400e944040d0b916084541007007030350309440c50000040e54500c0b2485220103070400044044041c0722090080000d42008100280b0400803020706800c000d07802001e60401042d00100306070190180001c411080c052380c24841e500c0c0da10340340e1901314040c401c240c049070765420800c8007044544402c0042e00c4100380d107401c08100380d8034038810401e11600d150054107107a407117003100300001d40d40001c000303422480c1907071901c0200741c00c814540d0260000700d036940d0300180702072001114401c0103400ac0c0300306805030050b588035000a01c082e841d02c00c0f034142c01c007445100100219607272901c281d200c0e0522143d5000e0005100469501013241c0c00003014000303e5995541040209060b000390140c1e9001d2084100c142140d81400002500c03030049010f190141036001c5a141080030b096840401c3d440300044901d1200d95030303900000d01a1524013091081c040c1131940000e00d40c8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 628121303 1250 628120053 628120061
    0x5180403080a090203011b020607091e0e040f1704050103052503020a02070504090c0e0609190207020d021801060e120703020427080408061302010c020f0112020a030b03010f 76
    0x154980d4400340503031500d20b0040041c021a2070145c1e49956680b07503040c00c04a8411081e8007403100c6801500c910300d4040009402810759901002200401a00000d0006c0c80da01221043c0e6051214103a40d035103803400d01d0005000c1c40c26000b0240b201d45150810300e4641c81d40078100b25002640c0c24040c550f03400d050500040c3c0c0002c04072075a4009807005c41d1f43c103401781d0090014004648100c46420783c6e18030000d0103a0b11011401d56545507528800d014004542d11b000d40e22010a0364101d84605000c015595410a900046422590b011400c1421540c0c4e8202011460350024410f60340b0803a03101460141318000c0c81620040380e000584000c0078280304070f03810300c1094400c0c0503004203460741d0280000b5040c0c9607041c0800ea50800521442d101000a40200c054002d13540d142e140c0303007040c01c0580742c8a80505036101580790100f01c000143e0303010040f102c611798150f40410150340c1d020f0040c0c4008400d68000000c850001ca03845001d50740c99840710820040480082c0441050719203068100c0f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 628122553 1250 628121303 628121311
    0xa0908030a1e0923031e1305010503010608010e15060a081e15120102040801020406020d230301261c08060609033f1801031a010f140705070518 63
    0x203488010b042241c8500071400204c504c0d800e000940385050511075407040d08803006880c0072100f170b80221b49000d22100301c0c82032802400c420b00f0604c1c990f504009010300000014444d800b20b55a1880009560b0300d0b0740d58220981c850f015240369160000301001a02c100030407164001040f00c05e040c040010004220018000c038081c118401915210401b03000e0703501c0404020103c00d6400f04400110792100348020002040c0b198080c040340c410611000300001c1c0c003194a80c1c129145071188400c42528141142d0440e507446034425061014810070706220041001e0f0303402035024210404204641c400e0641500d44480d64030502c083d61030208100f800c3c02070740e1025405900141c0301c4001c540340244480e009261160300b20000301d002c1c0406800460740c40001900030f14000c5154001001410310300c10300c205090030144200c440d48862901c40301000401c4d0350400c00c032151004c3e1800d006841e5064500003154031242c0c0c03882581021f542d50852889820300642c2d4018a0400900309044401d0007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 628123803 1250 628122553 628122563
    0x70b150f10050f090301090f03080613020301060906030c030e0d030203160203040b25050715030b06091e0103140a0615140406031109030a03020d0e0a1d0a0908030a1e09 74
    0x60105280c104051508a04c3d00030350107650751009507001c10800d0700c043c02e0a40c8030385c1d83c1c00100e1034940f0602c40300c440c2e80682030006d5070050005001700b5412032080700903601d02e45000070300c565080c0c0c3c040b005490003425400c0c4500415024089081c0d164000354464400c4149911444400c1402243d1b207215a1064000c40a4184248614440000e40440307113400142040010203019440d124104101680405515140403422208558050088490b04401262410300301407040c00421a9140c0c0c40005259400030041840d40030fa0195000c3d80c048902120094100d00d80030308200010600c81c0100c6a510842c01e03610041248030b40a4210003001981da01401e20b460640e09801134003403007100200343c02003404800740d103480c20490b07240064003940c01443c0e80400201b01920304141d600f030080c05010080420301034404c404007440d46907850412003c00c0c941c0d074901481c00800500d000100b540b036001051141c41011034204150340c03d0183c0d00c1000146141c0e0401003240d80a48004007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 628125053 1250 628123803 628123807
    0x60f0a0f18080a0b100b041401030b10020d031d0a0f02030f01051e07090b16031707050a0509031c0f080c072d0b09011e14010506030c070b150f1005 65
    0xc400b0804e00e600546166402c4040d607484071213070201608207811444504045c0420454103682c5405205200706040d10881e541c100071010094031040d918558206040e241d0f6113040348180111032241c0c419511006a807045511854010000000c18505074424030400b160060a010180700d003501481e0031041c6c5514140003100d284200440044c150003c0c071040c411300082858050008125000a01101034150012441c01030100384071580083ca00340c09860400c80000c1e0800c00325510306c8500c2c24090340b24484034000900d0004602103e80d800f88030006248001904072200701540c10f03803074403012160750b1455581c0509000b14080503041c05030403003484244c3d080382e00c80710030050b1480301c80f20a0b410b03072038480c0e0000324800e9903800700310380d91040201e81905441e51a01e54920b400c0006000e0303004000207605465406000d0103100320000401326829082060444e000d440d801101468140b41c40a00101801901061540139000c4e20390040c1840c41d20f5020790780458030315200e443c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 628126303 1250 628125053 628125073
    0x9010f030314030124091d04121d060c1e0f0f061005011d0d082116030e070909060c0f02030c0a060506120a0f022d060702060f0a0f1808 60
    0x20034a20808149000e216007910045500d10801500c10139044101c2c00021f59410a031a00e00c1b410780051003c88100280b40001e6422700840314400009042e04968944d205c0d528815043c0c2400c000070000700d030454641503041c81091021440102d800740c503000382d40b0070000c840f18054032100304550716503c41a120703805000c2d0f076000740201c000c8124411103108040450001050392601d42d81e40270b4600d000d001c101091700c51a410030300411502100140641e0342002d01e42c1d104400c102c3d050034018180c49283d0700c80586010091140188452304c070a0040043e9800c01000419907018007c0c00260001c0c8040d040e18000400c4514248036103004054109041e15440f000745400740145034030a8640d600300c422900304001244a4601039009482d43d411030b0702c100a1107141c03040550141461440003201d040210808508004805076a003a5032034a83c0d00c001100c070321814a03c80c880d90008242000b00a80c404408a913410168503852180c903c1f1808080c400101441040703000d5200403050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 628127553 1250 628126303 628126349
    0x405180d0f0f0f05220312090513020904090203032d09100e240306041805060c1602090a0504050c0a1a13030203070b0310090c050a08130209010f0303140301 69
    0x81100300418a40b050902d5203407007200d02001018a45409481800c55040c41480254a8403401e10211070405c8c903680703032030b0001281e14a600d101103411216800b0403042c0b03164031603804c02d030740030303a03005042e070707564003540580c3d00702c12101800a00381d003c1c02c8c0c01c3e50f014400240c0080318000a00100032661011101e1004c46113507243c10402ca8016108400b5802051031078100c0411544018007825100c1c58080c0511084500582c000701030303140101c01c281701052010407c0c9401405020003165500e5000a29aa14116050000b508145c000e001c0000316080c50703011a005611800a0310b07503c503803080801c5080c1d070b42801020b01e801581103590030f080104800074541d11151101c8003400640d01e400280c1446482d6000b000300610000400c9581001e8906800c041d00403020b0421550038414001052406000d0a0308180403181003c50b41401000740f000c000694000c01102c010343c1c4401c1030080740803140c48110045108816032040358115072048d2030580d890f1446003902c0c0801d118030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 628128803 1250 628127553 628127567
    0x40504030c1b05060a030c030b0303040303050a050304110d0803070305060d03120903020c04060b120a180f031803080d1401080d081806161b05120d0204050405180d0f0f 74
    0x2c032401c080c0400c18009019102e100c081e18001426403400500c0c5800b4510150540f602c0701c200e940301e07820400092000035041070541c0c2201c40f140c40c00a849941da8907100032400c8085240c95401180b40080008201780c08000b5441050705640501050b140e039010b100d101c1005090050103c0e03e581e5040324048000da000150031402807040b0303003a0708904800300381202c5554003c90341101d00054075000b16044900074681011100710100690842c5e4000704c4090f10391200d00800400c0e00c0031041051611a202c080c18204482c403000c4102079481c034000d00c0980c0200110030310b140c10695040e020640415109040301d01034000303804c100c0c0c41c0040c1158a4a4000c107485074904200700358040c1d41c0420000288945c0309088a4155000301c090302900b440c050080c074120030844024800c002030000302e13102000e4017820307820343d0f01c0d040c00d400440c0290285800040c1c100d0300e0310301040a078603000040c0001c0030300c0e4131007500c0c0050100c103011102402502c000e00301260b00c1850010b416442181 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 628130053 1250 628128803 628128833
    0x91a010c0c0b0307090b03040c091b020d050a031d06160e0f0f0126010602121c0902040e01020705060f0a020c0d0f090e011203080108010510030f0c0b1c0605040504030c 74
    0x30b4000b02c0071b61100d17000c01e001d8000b9201920400b01010050108481c54030850800101d94425540d802c100003a0081d034030580030001d00d00300700003c10146aa2806500100129a10241c105d07001700140c0001664410b01200e100c040342918441c4801042e0040c00c0541c2840c5c1b0141a50400184040c04d1001840c62107220504004100a41841c00d0850401050205440c1c0b82c0c010f6a0f5450001c00038602240d507082c103400741c030080201181c99801c1c13071883c2e80340f115a094045009819400060002e06170300c56040301075400022180100b00002c2213481c03040e20540c0c080d02c80c90311403010702d0040303004440c6039000c0c6034400d80080d00380030b029000d0000c1401007482c107000c4c11034032401642d18064080c1c0c005a0000c0d0300901820415030000100303409030560300001c0017113240440c03030344042c94058403010388200d0002e141c0005000600b52a680901000031a103a6030340220454800c080b55101040c1c8001468160041500d02d00340c090180102d070540c3d2210001007241d1241e1520f003117051 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 628131303 1250 628130053 628130057
    0xa170f0708090303071407030c060302131710020a03380105030a021c32070c050307082a06091203090c150d0c030e06011a1201091a010c0c0b0307 64
    0x8003002c800a41c001c480240c84c1d9040401810b2441d01c1d502c9c080e80d215800f5048401032600500005002015585420f0100d811003030801c2c0200383d05c00b0704142489a40d10b5001c198600002d28400c00f00e0f01500f011498401c07180d12500200d00c00103000100091000b4901e40d0000301c1452a8143e41c400c0024540151460f0001841c0101c010194006802e414403001d0701c1d5511107140403442e994220441d900140c0300321081c1c1030400c03079281803000300200401d940c0910040081d15003d00608105850220307074400d10065503440716211690500d400101d11100411241c55242a1144007045103030250a40c100280100c1d11001c8241d40075800c0100441c00511510b40500b00540e00e030303087d85a8a0f4080302005580b9240e03a80d0311003d499040111806040c10007100c04800c0700001211811558084030350500b118140100340644d1140100c007400b50884440081424049940082580350242e0589040c2c0241d801c010360f101c04000d03102030144001c01c80100402c00540b0000d6034080054 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 628132553 1250 628131303 628131307
    0x180306110412030201050114040b22020d05010f03120f050d0917180a0b130504090206130e0609010906061b030302090a090b0a060305042a170a170f0708090303 70
    0x20000c0c2c011041040000b03030010b0b0344440042013501c1e140e02d001103e0000550701806a06014008102400f84890481401841003803005040185a80c1030b2406202c0324075050026580d03130441103500100600003942c00c44540181c08501c103010b41d4000581940940b102c40c20601e201444000500480350241c900010303010008078500ea61070000c00610640900d6240460100d07410302c520070a1380d8000090f1400104000c41c11903050020140444070b0441300456001d001d072001c1040380c0030700c540700d000c002c04491011680c041c81c84040c51058206894a000d207aa135940503206880d000e10a040106450381413121031208412510800c0074041d09015241071b20701404502c10701c080740c6c02019025690300d410317051441c0910441c001003142d07160511003401e01e07840c0c52240902c1c81c40071900700e203070703031b502140c01541c058404000520707500d48080310880795001415150318031910100c402c0002c1010362000701e40751070195a102d81c003200324642415520303030390640940c6c40311031080d0b4141703c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 628133803 1250 628132553 628132559
    0xe2404030c17030a0c02070b0409050a02130b07120e011409030f1605010306050f01050f13080d0c1e08030a0f0e120c070b07020d120c0506160f1803061104 68
    0x403000401c1c40180c5031550080d030f01d1070000400011034401c3c5d004041190020b0404020703d1030300300123940a490403901f0015040c0c440f600c4c0c400013807044486202e8040780d20400003d442411102818480e801072000c1100811980000c80e00001d024901d82e001c1620320844030100300300f4a000e804402d01c06811100c0811940000510704aa100408020496042401d10855070726001d5000140415a85840090301d04400030304140900c0e00c0c0e81803103a00225014103440211301440f001010040240e0f07107170130030b16400103040c0c060700c54017562074400001408030781c84840d16940c800d10360880396090841e213414501c000a0b00100d03c4928119440322a00004810144500c451007400780c0c1c4056913808520141c03600b0122164050922003505100748005031300c880034002c08a580c01007403240050841c540666010f80910300151451181500300042c84403048003024842017191a1028078000c2d1010807282d60100f500c0b1032040802c085803c000180d41904100ca0107990b0341d0255041c561 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 628135053 1250 628133803 628133813
    0x504050309041a130218090c0f04081b0619030509010207050f0601030b070206010602060406020906070b071205101d06010c05060421030c021f11070b06040e2404030c 73
    0x10307121900c03441801c100301118040d203404e410f0808076100c8800c0641c24031144600c04002400310582d840d015910210006254000e02401c64004e450041c4015484a440e205a656270300c00c405411424154920001605450280207a8042c091403408031003500340c3c200000c5018140140099106640900a50300002c0b42800f07404180c40c015002800e240d0715500704070031044405409402550030101c018080198003240c00c69005801903c0035039156128000300b5024854610060302054803d0142304445a00c00e18428509a18860503c4951114108044044103500c600c4004401458120741c3c5000344044803a84010141041c541400d51500c515051074030440e01121200742c5c1070051075130300c041c0c8a00411546200d140c00c1009d05209000a550317551030882c1c500e54551801d86001c4d43d244140c02440b451004041d44e140c8549862601042d4400c040d10030070302c0345040400c0e4440c0000300080c0b8510140300014800480c040c1542c109414040242c400e800300100000b0200100d2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 628136303 1250 628135053 628135061
    0x60a0f0306090c0e031b030616090b0d0507020708010b0a06080408090d120306080714120f0d0203090102011b0804020603070201020d02120105011b2006090d050705010f09030506010603050405030904 87
    0x603880d4640a80d88481142094100a55aa06c281244a40c000c9500c0561000510710381c6c08110341059800089111340b00b81d4041c000c0e507101c260040c00c006503441d41401c2e6600510700504103078088508298560350080c4c203888040134101d8020441e41c1c41001441e01c550240f540280c000c0491038600404000440c0310020001700a9400e1411101d620074400d526200d104000c01c801c001034012241854041c030740c8224081c0b00d240c411942d030440441564000d00002c1c000c011040d084940c1500b148601075244d80140112501551a018a5102484034034401d2107503440b042e9100b00c0c0650740c0d682000103d4002030308000c11594280004078041c80c5a100401c0b041588030002d03001580351400040c42095504298000d41c03078210007040000c1d641010008421085200c8101c50011241c0803807064014001190307032100307a0341114005d02c140802c2c0141a240280e0b21003070302e00c580e50303400e9448902030f2100604079070001d00100f2800d403096020907000340c450130a49281c060150001003e503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 628137553 1250 628136303 628136321
    0x7020112020316140f040504020702121b010306060e090105120a06090c0504060803181e0a0f09050105030d1407060f0212090601060c020108011202030f060705040e0c09060a0f030609 80
    0x700791411007a500c1542054030450303c04d030080c0700c1178038081c08154070f41a14001c1d442828051798011500400310766941603211449003003441100d022005544000030008540000e45012130300d0081c0114030350b4030414440000d00c40261010404c0c0e41781074144540c0d5400c000f295800790142c0c030314400000da0b40c0e0003240c01030780c0520105007070181000f00308030464a01d9400f200b51503204000d1200d020b250180e000c0c0c3c00010442d8107038040c0000d6058041044a0100800e911032840c24007c90511024440c0d10240c84444504200b6a030301c4200741950340402e82902c0380803074034140141041c0b2030060f004090741441520089403a1082c10460310071303038018000054550b035405041144d0700008020f034030300501051074152504581030300042d1503010107002c2c8a044807400d0000d0403d64800700015256440c002040f55441d00c1c00900c000c00c5500540105a0118034000108240b40300c801c0a8460106c0010b05003440d100000310195202a0384051103424541c503540000b80f64040c0d842003400c0c1e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 628138803 1250 628137553 628137571
    0x132106150e1e0f0c040b1902010c09120201110304051816020607050f0d0209130905012913090b0f010e06030c13150f0602010b150301030b0105010c030e03030d230c0a05070201120203 80
    0x1247c10340301c400390954038601e10002c02c0186e1100e0402c41c441284071030300101502801c1c40c840b8603024014160031882960409500140303605d200c1070021011170350440c800c2d45002c42840c10460549030880c0c40f100c040d1307000000941d05018451041404100400c4030400d4154010702d48140e220100b1a8018803c0c1000d5445586420301018020f080c0070340e101c600384190304003000c5a02038100c80301c0440002c2441c0d001e0ba10b210f50f090b0409031154855100c041d00441c10b40c10034a0981c80c0000a17210034018030000b2100c44020401600300044c009081e860001d121144244002e1815401440d00504904009044104c0000c42c40c00c2d50340024060841e543c004501c40ca101f0090012031781d07080c88017520b04441000100302084442a0990550301c1c01d2078124034842c41810200d4160b0341080c68994035010005404481c440103500484d0a01200f140205041d8550b181c52410130b8422602510844c208100b00f00380644184020180c4c00d00c141031100b40c44a0043c0401c00300d03082280c400203 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 628140053 1250 628138803 628138837
    0x307141e0301081e0d0e040b0a0b27090a0504231c0206100306150b0d0b0f040504020325080714010212132106150e1e0f0c040b 56
    0x224400741400342a19400fa0030031000424090800c810303680d4114405c500c2c003080b00c4000000190f07a6143c00006454400400d1700020546503800854907521102c8030903d41e10404113066402c1207250349049103610300910405003941c49040341c034054440100103c0d9210000e80382c000f050b114445440030140c10110003804143c0107a00304441c1c6042c0c203401ca4066512602c00c0154080704480c4070340550b58001c0000c00c0f002c0400c10980d07100c000d250003140328158085140c3c049624264004180c110003214403200d004246800d0200700d40040e07c020390150428003c1e03200f03840240003811203074181d42040400f0642e803200c0315401e040d5260011803040c40c0141d801f020540c0d040111021042d4000c80003032408400c031581c5003030f500039032090b00e58100c440d5803854540850102e20405194203c0410720030b08002c0101000c200f0f1050046210240c00f183c0411404d0130700361012000ba42c500082c103001929078034015110f2800003402d0301e045a908000202c0c6440c020070113080308515100e00c00d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 628141303 1250 628140053 628140059
    0x403020c01091d18012901030f050403081605160605090c06040609060305070c120509150924070203070e070e0303070b0a020a09080d02030406090512030307141e0301 73
    0x14900441c0707500c081070500007403001c0405600410f0a05411021a51600c0441030b03510200d00e01420041c04191207001c003465490b1602e442e07081403507184803800d86c2d04101c20039108022408580041c1c502a000860100014001041c6554a640903070041e04100f400c049507104440c0324901d02900c00c90700b03d511002400300f10001000a800c5041d02203440a0401e0704101c8020900c1180b40724800405490740013045240340620092140f2079007000420303010054034000907050b980105c448601a51520760304025001c1c1c08000c3d94422000180060390a020702900144400700c1019036000b0304000b04021801a41c040001c007004164180310309500e4a0a810050542083e80c031006010350410440000000c42a0346c10726480150311400589851091804a400c200150044c1e507041c030680c81142ca01c00c1e000000360040701d04556820051586034402d100c0a9003030000c2020b415441032012940c41802480c1c00c840b0000d20819a5041080c800e48405003001d942c0c40500740058000018 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 628142553 1250 628141303 628141307
    0x3151e15070b0609071e03182001030e0705011d12010506120115170a060e011a04060506030a02091216150c02030604080f040f09060518091f060308030403020c01 71
    0xe00c0d440f0800311014001d5107002807028241ca200703055600080d21400da030300341503a07010340d01804115200c00007512030050747c3d1900800c1188200740c580601d941101d0000301e198480d004039980e005020000d00203440c540b00c0155460304000802644130815040d880e8001d40b02c0d504840205948000085402d04002003400f2000c12010040030030b69041c0a64402d1051842c035034074084440c4214041500c0701e520f0307052400c000a000c0d002301024200703510240c1c805030540060008161840f4050303500d1986600300f004403409403103180d8200d02c042c0000380c0c1c0c00719a64054a080e01300500740320130324a50201800d01340b450482e103c249129644005000c03080001100207288400c0c0e040840f4141c40680002c0d5440b82d0080000301004c0000544000e401c8082003034800900d101c05a210800d502c4203d104050800c6015030350041a40c0010803035032687c985141d5000300f01400140800c60703441e80055281011340070211440760303114680080080d440c2c500851095000780d0180c00c03085a00800 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 628143803 1250 628142553 628142573
    0x6151917071a210406020909070c020a27020a0306030c0303111522021c050f0d020d05040905060303070c060c021201020a0e0112061e03030305090303151e1507 70
    0x2950222031030502c069070003256483d69010a2811080800300c05136030b54a00301c0c019214030031166822101c818280300342c4980014954600c507100302c40c507184007074561120310708106c01c8074070380f00442c05001410964040c281d8020b000c0a8010b103004038582d52261205540c403a52540110006440354504824101041c040801c0485085103892081c0c1880344030140203a02001c0ca486d180d0b101d8080810455542d030941c04a000500859500100c0160a0403901c1e011210030041d09070154a107a401c0705e51011584050401043d01c0d8142030a00300b1040c00000c12001b010f407905480100034a4000c5407003a203a507001810307250340e80c2c201007000c4c0c4180542096110b0f80e6016682c014015644004c0e003041c1200d84041c020320f4001c10700c010540c0c00201910255228101c8000f08039125540b48009000e05030035607000b92020310a0b510ba490403551b40348000c44200a0760807542041c0b2000b440d01007020500c1000080c402010081c3c0200010020101c1d000b907a040381c8800215003041002c00f078a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 628145053 1250 628143803 628143839
    0x16090605011809020309160b1c2703180b031f2d0b0304050705120307020108130317070207080f06040f0611040801051609080615191707 60
    0x60200e07020040780100095407256800343c601142d03004000948400010080c06443d81082422613844a60341d044130301c01540a10f0a080140a90140b64640103c085c0104030140d0f804441401e5024010418600400c40c80740d0203c00300030a0810000c900f1442c0c1c071600c00508440500d85599080c80242058840340b00070b82041100c00608081216100f40d41244844842c0750b0039a40c1840807111144d400ca4000d5044181c8051000c014403080c090001144030550342c0035203520103140303000403143d940c03806085002400228603500042003903580044005819120703042c002072008907100b0b100311405040300c00301f0040c3d002410410440204105035194401010050010350400f0b441e041c200100d80300014003c10344400502030744a0750380086400070101e80000b00580d003000d6008024000d0904403010004403203800100751420302041d1640502150390203031b8000a8035409101c4261a01d000f000c0400303040c40000200c03030301d20403402c4100010341d03400b4008590800d04a42a50300c55a4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 628146303 1250 628145053 628145057
    0x90308011419060f140706020903010506220f0b04140403020c1008130503070c03080a0815010f0305060307090606080405010f11030c09131103040c0501030b01021e0109051609060501 80
    0x18201d81c10002c031014148103a030a14034120700361540b404003c0c0c03001c1c2d54210f400381c0c61800002c0d444040c080c8650140025040c100d00074030054440000300440314080a807102000701650401308010701030355000c01100d80103180c01007043c4d50785000050481e5074003103903032000d180200100410194180a9141050000c807001c0d02c0448070b2201c0203000d21402030484080d1201030001c4418040d0401c141c40c5c0490784400400481500ca107040ea0f40c94000c41610000f1449210108000b00d0000341d80085078035061b961890701c0a10b1000440c06401c02034142d58050003143e8010500403104d019440151810340c030b414849007403e1603c503086490300a003240e001890a64904d0061103040304490b002101141c0c06621803050200040e500c54040e11410300407807030a5070210300103044c40060751241e0701621120402a95980054068030800c05045005810202c902104240000341000746488840000140c5030741c140d460919205075044c5454064400c48401c0010030418090800500030178 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 628147553 1250 628146303 628146319
    0x1a04050c130317040e0705190504150c0c03050f07052b0311010e060a09060b030705010503071115090f070824040311070b131202130b01120903080114 66
    0x8107042100081c140002841e1085200c1e5044010440d04240c5000c1e0005600c259201d081c404405003c1d540401c14403020003e07a65404a80940100706580072500900c0c0d00c5449110685030403500c6035002201120f0902c003420011020420810403032500840d80001407140c10308107000c2025510203c03084501349120100c0300740c449491400c988108643c075013407008030b00744480040350260130503103200071040c4207140c2045040c40c0d0b181c10001d5030600540c1c2c108900b00d0703450241500c9030480e01440740803070790400104a02c684101103050100c40060183c4072a50402d0f003c8080c40e84c401d403010211307980b0000108042c12814008080200350800042c941802c02a49454030707001c0355850210340b100000001402c3c58041c03148c0091001111095030b14007038079401e41c2500303a00702d031481c6941821000c4d070206880900d0390b41a00b98507001000c08012029603200080544080c03d0200e041141e03182c5009003c0c0c2c424010016814402e45030100b1560402c1900c031060120026401d21072510 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 628148803 1250 628147553 628147567
    0xf090501030c090507050f0310031505071715040603050c042405100909090302060a1a030a060906020408070314011803050a0f2304140103090203121c1a04050c 70
    0x1801c0c90003000c80c0e0200034007280c0c42c1c0d900c0c0700c140c1e06c6020703402c4013030203400c030000400c00c5003102c00081c1d0701a2407107400394000381000a00003e04441c0c0c1200e1040126500d14100006424003440c0254001d04c03c0701d4040191000202141c10360710981d20840d59a0700c403070400c07202031403c1d0241050700308000881d402c2414800740c00c040100300b54403070340d030040c003400302003c40f094458202e11003d094012001d01540c81c1925009642c0da0084880c0c403401031900d2018141404102100c40c0740c07585c000c00400154010343c444c07000412490b10100e40c895402c0000103041134050103458011030041c1c40c6240100510303079080c0d02391140441e0300d0039416105065240003980040079151140124038080104500b50760b0190740c07081c00600769510020908440207000e807000002031041c4c41070603614170341402000b001507040d101c0040000354585c12111201c200d280300386015001c1d4000c1034484620fa8440c00a0302030440e410b03062005110114050100340604080c0507140c1c1100c2940412032030000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 628150053 1250 628148803 628148813
    0xf0914060103180b15060c0c04052202090910060623090105031f080f0a11120604020d0c051c06140705041202040227030706020d051e07140102040f09050103 69
    0x84403000090a0019039000f00b820150405c0d941303141c0342d801404040c0c3c0c0c2c1100c00c022030703519000a00001d129500344070000300034404408c504082c0080c0c0b9196455214020783c00c200200170020308147c1644a200c00520401c081e0307000e410014030b481d448144142c0c1014602d820840040001001c070105c0811007002183d0b0301a08890340700c494480c0f62005125800798444840c002944460818800c12a04c05582c44012490041081c841d0205000c05c0510806001001c20071140c42000340e00000001b0303015007041d1252070340d030500c1290061180d07500c95002524030101400301700e1146007402c0ea070340c0400c101d500c00c21300903060010180d981c0d4640600c00800c6845103005200f44110412080130071900c4503019681c0d400f13070405062a21035140c07842c10580e00c03d94074405100380320f100c0000800341c0c00030a003507d080f04940d43c0c10746001d2003840000c2c1c0c0790b8000c01204681140402031074004c81c0030f070002034402e003085000150760340e4034018203641480f000e900841405840d0100400c0058 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 628151303 1250 628150053 628150091
    0x403032f0d030e0a200a0905040506040201031e0c0f200c19030b0a1407110a0b15060a030905070f2102150c01060501020d05030f1b040f0914060103 65
    0x460038035021a002d050150f00341d081008501c801410540c502108541861103d00e085022800c10740d440160300fa5580b0003101912401e03540a00243c01c1380002c2405540729401c07000c1800d00e0607107819400031a40030081d04071a2811084000264059117054165034001c0f010144a500c80c903607a400350340c0d00820a501d80c1c001e000038500c205c22072100042845608800d803001503800041d141c0d02e52401204d40360140c03400c180701e03070103007120303140000c0a1600508100c000c0310007440040c07030148005c2e910010030700b2016054490040e503024032503070190b9902c0c0042100880303543e004140c452192030001c1ca8001c2640200c440703021186002e1180448104225890141c5684c00712420400d07800410500c1074010040350802000241800c929081500b019003200c00aa0841d0102e00c1e42e4401101c0324001907034605485909440840c00f5a038519946803450f00d5003454051401341d4461110340901e40c3c0ba40640340c082d40b6441c0d0300d51205d00c0e0211030380d401042800c043c40045501c1c0034507a061 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 628152553 1250 628151303 628151323
    0x161e030318051b12010614031c0804060207050c12010207050c090606092e02030c0f0706170709080f0d110f211c0207200f1201110403032f 61
    0x4990f0925a4181c9980d882c54001c1c082d0381a40c000700074803500d4840007130003012168001406031043e03211845418207a148004520101c07513036a0440d0b03441d656200d0b03001e0341c0000307410b50f03d40c070440e900c915281e41e0702c50a00104c51a1840016581c02c0e10b8a049130500c0c0030b1443c0d052040c43c4200401800341c0700c00046900088045031400002d20152990310154208044440360801c0503d082000741034000009000101705c02c412510441000b0071060343d1115503008223070010b044c9011240b50100070300c40040d00004103040c580c1c4540d449250440c0f9194001c810402e81740d1000304401103183d00700b074940840080d0300c1b02074000e50301100000e0b40c2e21188d00e0140e0707012000b81c12130b00b500f0011090507202d95081644124514006c800942c0c400b039041824241c0700119005480c10030018450f440700d4903110084c10450000501c01d007045a03000503618200919529540d040780450854401130010b10304c43d4841048400701c00705030b1403601c9030540d480b8440b4040080285008080000c882c000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 628153803 1250 628152553 628152583
    0x120a0c140c0a0b07020a0905160206090313060f030212040605010f0501021b010804052401060e0418030819140901180f110111011b1407020d08161e03031805 69
    0x10310141480800c054000950059047c0342ca01400c0c0458001c0c0d994440f40402e50395801c4461545038625241d469100300b2000000d0001800001c1002500459215203075800c5400d00604004030006071504c100000c0b60211429035507907005001c6803070981d8846018080c00c0c401040aa1a200a10070b1031040c0da038415818407070501b000800b008010451900c10040440054044040400c81440f1000e001c1c0a6800491441981000710781001e1042c120800c50804803d1043c0d242520241c540305001f40116220080328100710a40761814051300901c808091014040c0e41f40c9522220300316009140c9001350300815850340c00115040f040000d0751241c01110090f1110b0340c010060341d0807034440007540225400d00710303550300701140b418100d80e0540698440b0180c01400510f403042d13034401d8000003035210002c01072110206114001900c4d4000c80c40802111442c0d50b52101c0c003641d0000d00d420003454000122082c1050b5140c06104030314007038200c5019402034255125900e4458401007118 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 628155053 1250 628153803 628153807
    0x100e010903080a090503092d04051603052211040c020106030804140604270b01020606100e04110f03010f240f12020301090b090603030a021e120a0c140c0a0b 69
    0x4c244041401180c0e00d03c03e0041c4030b407280da030003100c8100c10030302c04040524101203840b0004d0545d08007401003c0c41800c038990080810909041c0980c0200005050007080c141c00d1081e00820401d0108443c1d6014055440626442000310800081c0d8150100c0401164101a1304100058a520907035040d118a4450b481d01a000c0001181c0d1502031944490032100c1990751180001d00e5081c69000701f00c090340000d0000e0405440166034030807003540d4494200d0800d500203010144140811400000014008200c500010200c11903d80002041d034580c10380000040200e00d01c070030f2100e8014042068480148040805c2180d00a10300211040c148405488511a078500c075095951000541800854803941c681d40c40500805052000d18001c5402d10081442490004140d603401341140c1c0c0100001520075005040313601e60b08444600501c205080341c50444251009082d00c0c1e03c0655403d0305140503820720410080c021703043e444040c0c01400b548a51a00ca0307508480546000030141e0b6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 628156303 1250 628155053 628155071
    0x190b0c162009070509030d02011a011808030304141603120e131103010f050607080301090b0a1d10060f0f050a0e03060906270705190e09100e010903080a 67
    0xa6124500c030164000b14260810248907000006888003400503800c40c2c1440034044c2083c0d080b1415111060b6090365400811880c40d03103c0c805c14446605010703104095070350782e80799803441c58100746c50484030344224180301303a1000c00402003d145a52903401c40d00302030b4a50f403a101c80c000211600c0703c04111030030840c5052a2202d08101103070301003620080007660a000071030883c80d0000c0c041d101918000010000d050710340b420550b501c0c43c1d00002a1851640303002c00300c00040450f0220346400440e4400c00044c11042e8005101c814540381c06501e00514060802182c07150791a080700040c00b4107206007a90031070380107800c10101a610f0401655550004030151920010351001c2c6074107200b034408004030f040004c9031941c0501c0c0ca45005900b41c407213001401300c9908014149858a03804407000308800d01e003290300710440c80045040f40100c182c036180c0c080040001207900d1105540210000412242c0d240304031512201220001c00a100b242d03980100703000f04c058440980305440745914 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 628157553 1250 628156303 628156343
    0x1b0d2f01170c2107020c010f0311031512060708070306050d031709030f1305030111040e1504090213050f060a060f05030a06080304180506150f0a0908190b0c16 70
    0xb101e100181507503d82c034900d80aa0029039030550681070500192019004603202c1d0700078010400c101d455648100d09565921600d0030920905001a60b0700c0720343d80d001030070392600601216010b4440350b40e03460010f1030611400740554000380e000304d0040740382d00d2010780843c0e8032101b400ea0320f10b00880000102d44803107142a1841c0200d4080580c0300070300240d03948a810381112100c1c125201680240702c201010080d82c220f0780906e1049140300d080c10000100b0740b0302200003c3c422004000c100103a861401d0b00810390741007070340080342100d59440c3c0521035070401c08004180e0240c0112520803c040c28905d000744009e081c03600d644240000480032804c840034a4204001401d002401c0b02d49441c1c0e07850441408864201412401707900e01000300b80f0500302800c8103251140718100051600307000c50f9001c0d60960007881d003002000303a145000310307011209007c044a01e11407104c1c40b0754a03800ea82440d041d40f800103409030700d03d03d030100812101514544070041410b5003060070500180c1c0d0039400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 628158803 1250 628157553 628157587
    0x40f0c0b070309050a0b040e09070e100e0f0c09010f0e12011e2a120c02010f1d0c010e01050f1303110f031b0d2f01170c 53
    0x40100808180000450403501000241544900a81c0c1e89100e150780e0f07001744070051007203005e000030040741080184075001c62102603030b400420303a4040310031a55545e01d418100d990266003080c86042d610104100c082c005008054000da202c115820313480c108081031455038403c2844031418030501c2e644542085006550704441d004e0040c180b203c46198030413025000b050060704a00d04900d030b069420280952a12605201c4688140d160f0b0000c5a0390310a0700304d58020144090401160440c0ca280c081360502030340940d00c1607600081400d40c1d01342c141d0390139a0004140b0810244611a0103d100140054040100b00003030070811805922080101d62900c182e032400c00300c141001500801000d5081050000c4074000d002c03920390401c03540c0410500d11851421517905900c82201c1241e91420012030031a000f0f4000c1c4241c1c0958031640c0d8615509540c000b00507015201005004914603800c110140c501c5001d1074040c0c1ca0b004040d4241c2c2c840c00d0090300340c0d68848000300d1900e0034040d01d040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 628160053 1250 628158803 628158833
    0x30a230d09060c030c080403080a022a1506011103030105100c1e0b281104080a06090c0902070f24110a0207090615120b0a0b0310050d020d060504 64
    0x3000d004104641c1058000382100c543d80e400040d280c814010021482802098041c5030b1503034a5041039100d0390907a1000e034000c04210280b81e01c65009110710300c1049008045071081c030402034810911402405029071200078401410f000740345d45040c15400000c02202d040d9030080362000d5030015820310071261041c1c1040001e101c511f010001d200001010240f041c201c43c4a03841854940d034400c00503604014a800c4203502b5a085000e01070481003942e0480032120803000f80050038036544002483c03a00081c1d260a6548543e01c00c01c2c602842204032101c005882926020340c50140c6660390b0261141c0044c01c00b80000c0200c0050960640920303408400c0d10158035000e0105616200c900072aa911041400c005841182c000140003c55070146000321100454000340c41e004929050b52840001d0600e811482e6803060980b4180c1c0d25080164068070038054081d849103020ac03d040c00600198000521070107a60401100690741c00040301d000690015000c180c0d43c989140020314080e030740c5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 628161303 1250 628160053 628160077
    0xc0e09030405040203220c080c010f0f030e160609060e03030f030415020705010903050c010b0406030210140421054615050603160f270207050705040608030a23 70
    0x140b002400740d20300c4183e0030303548c0d14420746141081c0d5000554110004944050110b0400e0560340d40450096010b00022990602519001c2000104a8001a02d0380e00050041443c00c44148201503100c0102e00c1000303801d600840ca0b0003250b600d40b000390300008000400c0c4070140c1030300c40f0f4000080d4040d180701d158000000d0000201618014107250066004d01d07086610b0000417110614140c02154206c0350043d0808402e40d0b49818200c58040304c280d030200b2a04020800096549003000e2208980c489101d204244503c00d4a0024107144441d101d0108500340b203084603440c0540c4080c482c071012141414034000184d1007120103a191030300c05018045a0241e02451020380050301300e5031107190210161280905c0e08840c280c45104140180c07410002c07214018880c102c84540f10501204120b049010350041d00c9000c00180d0b8002e4008403819040400c040185003400c0c02090302500440c000b95003800b05001005169200350350303012065004103410a62401114022540c250803c2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 628162553 1250 628161303 628161361
    0x91503190c0201020d05070c020d061109120f0c1801150c0218010e101d07020c0d0f021509130b0613240801030b040b0403030b0d030201090c0e09030405040203 70
    0x4450043c0c000d410002c0c0f0380007082c1c10140051950340c030071402a0502c99004026000b000687e8403010000c7c0683d107943c102c209030400c0391210030764520701c6540210005100411500140b6a100b0341040b440c040310310f000380c1040c18444050700383d800d010343c1074459062201280c072600520440380c001410034040d400c4a2000403041e070f504840651941a140609115926070726029201042c0344458030034001c0040c98101d82d0b40d9482101a80e01e034011800d48100c404c00590040015140110400200ca051030110701202c110708201c41503104003809200d00c241081c0c04100480c120f00c1c1c0000c46080c282d540d8007000e0fa402e0f03882c0d40684901e4000c0c0f030b062000054685041e181c0560001a00b0b00d200502101068000c3d03120b03000581c141c0f41d02c03070950709107900d4581d9182c10518018008070185525071a02c2a82625044421503006000b940045141d44a904003800d00e07110580140400000a40822001501c000211011204c5c251401a6a9640e07201d003078100308071040c01e5100f2681c1d1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 628163803 1250 628162553 628162571
    0x20616080d020f0901020c190605130509091c0201050f070c0203010906020406050702010e0d050c12030403050303040f1203110316050f031f142103090306070203041a09150319 77
    0xf500508003000302a0200d80c1408010f100300300444800c612550940c40f04003c0c107011041c4140054404084076011070340581b82c68000142c820001100c51441e01e07880080a600d11130020003e0140b05400c90000f08003a0034801c448010301c90000b070244041c052015281c0003103413002d6000340c4000c0d030000c03011521281c990400400300c1c0d1001c034080c0d0004030f102c01051001d01c1d002d210a900d080c4e10500800700c088040f0180107404819501c848580e010601c03000000c913000340700552103240f080203e81181c180920f021303100f4000e104509000c15160a00c0c0807145c00c3c0b04801c51f07170051111540080d201400702c03422030300e84c4203068002c01c2d21000031051050307a520f0301c0034181550000b42c907802c0109407550504030b101d15000340d81541c000c400c502071f090303a04415901540c0c4200c998080d02e19020302039000c28a080c0d02038a2120050340f0019080001962010b89541e02e0303c50b402c8804e151240043c001558841110700c40320100d10000003240603841003181011816503e00024041804 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 628165053 1250 628163803 628163827
    0x316050c0d09060909050f0f0405160b0406031b0c080903070f12051e030a0f050702040207030c0b0a021804270602070b160c0f1b080601090f0207020616080d02 70
    0x2c403403142a000c0b070f441c000702103015091800340521407c0e500030b01c0500c0d42d8a003841d076550084060000d9a081c0a200f000303101c44110380c0e20001c06441952245a40c981c0782c4240282141c0556092807581d916481c65092420f80c8000c2500c0d074140c010903065150b01d01440040c1c1000b00da0b912811603414154000100d480481d0510005240184240d030154020105401204078200050000540040091080140c060310398007801c00034502d0480d040540642c041400c030b80c80928242d020440e185006001c104800300050b522109015040d07041800c900c4401d0303505a40e10186c9841640c81c2c07454407540524a00c2125440b5007918201d242d0202141400c1d13009600460090b601103003110005940c0d625412941a0140e02ca599883d490f42d205840f492041f4849035000c80b99400c00f80402c0001400e030500d241e001c1c0c6980c00150205514151002048646064041314803d005105042c056170780c800950f54408402d903600344900321903183c0030780305108a100300180c01d0300c04038048134490 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 628166303 1250 628165053 628165067
    0xf0112050408221818120c060216170a020c0f0f040903080702010c08060609090a0b060a02101505061903021e07060e06160e031c0f230316050c0d 64
    0x1441080e513000301a6183d2154200741c9404500342080f04001d04040c40026804104030b01001d6610300d001f03a0405a199614426640807a40d00c4a01030711005526007840809001c00c00c00b1800303020911328140c0c98401c041d4035a002e01510a2085d02e48085004c100d0f02c0395414010f1201d4018800c00c894151031070042c001c103100f0388421006620341900c0719180c0340207140c080d004600042c001030900c0c43e50010003011240040c03900c9010350301d903400561141c4841c070203404808041d40142a4110302c854542c1c0456108180b828684a40e0382401c0050f61100021901e6050b0b98804040c83c01c040904168080e02c034503880c40c1801c08203081400006040100680007041c8104800d100b8101c0c811207040da030f464155605402d070300c1c031407030403109603409007040c07801c1c4800142c140c1d006150201c501041e9030070068056404076903440c95003680705038802c1000300c020844c80d00e4002007400c440700001075030000402c1100001c1d02031071040344c0c00303004005540195032208103d800503080c89800602c2c0f0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 628167553 1250 628166303 628166309
    0xf0f030203030420240c0d111002131e08101e2d11070501060905010f060c0623040c08060a11030a0902010908071706060f011205040822 60
    0x4402c1e02488214812610028509000c0c002030900c5188105a030410140f00300c10100801402800c1024050101e028440e100b586c203502c5c1c07903640640111141c0e103810500c0c10b050700d075002c51041211040d0610324169140641e009a21103181844490330a1a01c001d03842e0000c0105100788951011001980e400c21841918140f40100f52907072100080030944100c211065000c060320046e94040d02e56000350745000510181d808a0000320200b180e1400341e01c00e141c180d40594480e00140040c605034003445006020360344203400424548040282150720b001c5000303009503141c24408050050101c0c07280d03202172480b0f44e0310f091801c003440c10240d50301d510321895032680214000030f120301c1d03003600c50b1201c00040007400526554802c0040c0006004e80f02c8220b050125100380415414001c0000001811441c21380c0d00e01e910341000303294a055001040c0c10710842e07403191a20b00c030340d9003c1c1c12a115541400f40201c0d081c2c0f9586441134081c0508002c039602034040b080b102641c0c1c00004000011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 628168803 1250 628167553 628167563
    0x10918060b0c0f0d0306060e011206120b0a060f050d41073203011107050f0613080f090a081006031a130803040311190b060a1505070f0f0302030304 65
    0x21844c03091042e025100c03284550300c0800d031140141122540102c0382241031101c41240081c0380750b112124040a0040141b09842c08481c590410a181c02e803480f40d080940b800180540d07400d481c040c002240c21000e000700500d0b60900000e20100790350707041d80041d10a40ca8140000e2402d4038204266481c0a4554203500b60f44200500040c0c0494075804174022004040070010355002c810800c614401208603100343c15641c3c66020071000310146c00030706601c030710036005400240201100c0602d01103001d0601d07400014a2074807880011051012502c81880b0b100035180c40b00040400500041307003590180320b150160358440000e81c0b0b1542d00000543c2e1064418862190b031400200e00458400c584040031243c448003480c0102d040301c006140e22030310038a01000b51100307011300c01d800e11100038030700482001034021003c02c02280720080c561085040e1207000be40c5103010b0030540c00842d0455a101880b000251020038001108500c0c112282c100c591400380021600d402940c95200301c909842d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 628170053 1250 628168803 628168813
    0x180e01060c21121d0304170d05030609060f120703030f020d0206090316022103042c0601180909050609060106090303051206010c1a150a05010918060b0c0f 68
    0x80311040320240101951201d41c1d801c981581c198038000000c04c00066401c0b550703e44010f400b014264200020409000c5250302000d43c02c141500309450020b40003010824850140700304403203030b1500b03011641d101004540000940c80b1042c04512268051018400c0d180554580801810f400002000c0c0c0c06099600301c0d410380d0039115049850300c206482d4007150b50005c01042c41b0031114200c01c0495070780001c01600d8407116502d11180c030300c01507000d1500b494002103010082c00050755506040035150954044010607070f18610b01ca0544002e21345418000b80701036400c0c2d8a40c1c205410360140041503c100446840c0781001a6100d404403800c84103449844000300302c0520404000e402c40782c0c0364442a09019500f0214804224000c0102e410404a40b9084010404280321950300c844031811602c0b1606080d21455046802c41d02c10302e020b0b41520100b000540d0340842e005003100c1a920031600000c44031000c54001d01310a40c0000740136080071481c25840034012071503101954040040310 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 628171303 1250 628170053 628170083
    0x110f03060a09050f1504020904080f04061706040c08040605040503091008060f03030406050706240603020909070311040e060f06040e0f07030903050a110a08160308060a0b03010303180e01060c 84
    0xc0c5e56503104035111440710122030f001c540141400107241d60498480d11405051484070340360745440da006640000c00003020704009075508d6801d0b0341c480d03401500030f5034148520100354001901ca81070241c401800c440e5200002028002d0504c01d9030050740005288036864041080000d01c110020f0341e030380344192054011100d25184c00011581102c02985031242001181d0302d030140103100316102c00089806001d124021a00c503042d042001c3d1510b900e0041e104c82403001440b034242c0c0010301050902d8130340000341080344458015542261501d5080e105580c4d5043d01041180c2c00c80780269400140119000c542403c1e0030184134030401007034041c81c8450f500e410b000c40507502150005008030b4030812081078031510400440944820b01c00446d800c41244d44e840c40c21590003d240e00b2074030800c03040840101503015500c0d42e0040400c480c264801c030300380307084d0744030910062000900b401003200c08030003501e5407908090001e04e104101d800003580e581e44050000110000700300d5130001550056 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 628172553 1250 628171303 628171333
    0x2040218090114210703411b24030402030d0323181e0706092315030103060504060c2d0c05070b0901021c0c110f03060a0905 55
    0x401c80e500c00007094000e01406104144d42c0002104000850b54004e8101c0440800d4801900064014800c0044003448080381c1d074261024441701d11100702ca10408144109030580001c0d4034824900c0c0c6002155506003030400103101c0b1000c0000e210400c100c54210100800000c005035100303d0080d01602d041502941e030441c2241c8202040c2c555403842080e000d280ca5141c00c14659010082000c407419069818803030904e022000881d58101c000140b10380107041400340040402401e1504050041c0b81c10310065003503103188100c40024445550b25050040c1c0d5a540d400c1c202c8a02040c007181e501d5850381040400380c03104950030b0b20141d04108681984a11408401e04c0c1085000001100e2900c440e400328000304a81a890080091400150002c01c1d41801268024580620050307074401c00b82c000a41010400e545802804085101410043d40c2001580050907481180c03d40040300d03480005010740c212050305501441200304020107651141d011141c03660086013150300396100d403145 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 628173803 1250 628172553 628172579
    0x312150a030b2e0e1308040b071509140706050c03030a0b030106151e05030f060d21030b090109020406050d180609080720130203100812030106090807050904110a03020402180901 78
    0x1e1801b00300700f0080000e07504410107840350390701c01d0f0150412400c8980710141901e44400c2c0544012107030685a400c00503040188800030b01145c10102d04042d1195116070b01c80c04010b200708000c075120000c25155540a5000402610200d0a030f000c201911082c0100008048080f444220520303861841b0302c10701604c2a03911901c07419407044140d507070700008e03c4003803004244111350244260345074680e40b1110000311000000f00f55800504212440b0812841c641c040e405408414410042408016070003400c40b1007042e0551804140c4800c01122202d04e52241d01c4e001c2c1c102c41ca0602164100036041d40140889801005075000381d040d20348005600141120003540d0041e403000c0c032900c0172038154002c1c6a00072b800c000d00c402150f41c0c41c0c0c002820488400c1c402e1006c56070000040c440560461998070250601000070158281042d010505800000e00080c001035030441507000e0b0780d5138501468001c1c550141055444401101d8104c049180700f102e83c0e0f20411004002164002407510 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 628175053 1250 628173803 628173841
    0x4030506011a040302040e01140a09021503070c1e0f1203050a14060f120102040b220311010804050a06152c060904020319050312150a030b2e0e 63
    0xc0c110f440d141c90340c0e081000410f0020f404600070354a4203041400e040401c0c036010302c41c009900000ca40c150302071042101204440718400300d8404240180302505600407041405682e0004051003519480c607001c14825081200080c14070030704003004c80820003000c500b462048c503103072400d0040b0f13110100014191201c14030a01a6900a400002d0803840c000a0040d810400035040846020040403800d003a03900c990040d01e078540b0f00154030801c04603001c82401049002140130741c0542d046540c0c40d540d400315054002d040001ca4004502401010b00c110200b85900c90410030107001c81400780e10071007003c0e2103410307014400310704031034030354072035811298041c225901c2054240d9803424100104c040e8003038030681c0c25200341d10403441c0c83c40c2d02c40399a00c05940124010b549a6080100280f144e15000305005610f00c3c181c44420741a444440400301566070004d00866503944103056444a001652400148071050b0314031042a4082d40129100791580740180c5002555036201140e00d81ca0411 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 628176303 1250 628175053 628175099
    0xf0b01140312090103060503030d02040311192309100806011a030f0907030203060f060a091406040c110a030c1401020405011b0c0e070809060f09100e0705150403050601 74
    0x6510b40c86075421a80042c4403a5005060000b06940c60b80046891504601c3c0502282caa000809009015942c00c00200c80d1070304586d04800b28602c2000303240f02d690b49100d886401d805000038100b01208207030424038a49005885030407640b50200d002a080c400911414400380036200000c42c0701c0040000c03000310040e050b0510751541e04c03040403018094034010441046030242010100043c2d400303000340c50050328008010030b03182c02e080b01040400c2441c1e40c00b60142c545800001c2d041d00308440c5902d40d100d5002c640009185260000540f456001d000c00700300c60703005114004040541240660305150f00400900007a0f148045c090707801c030310941c090b103408904085507030414401c8c0a41e540c01e03c1885030144403401903641755085040316040c4d900c0d501040c00201040a0254104000b40e4032072081c2c1c14400ca18103100840c0b90320380c0304482c0f0803820780751100050381c840307202040a48020072024124185183d00050404200d8102d400200c5a600842000064012201c031034014061108 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 628177553 1250 628176303 628176313
    0x60f010906080606041a0c100b01080604050402040f050a0608060c0301140d03020a0c0e0702240112050f030f0a0807020732030a11030d02210c0a0501090f0b011403 72
    0x401e4040e0341030700b401030429038131020400c00894070045510060000c1482035880e00d40720406040f0280c18403805030074003401035140c1501406a80e9100003040c5c0c1003202130702d00241540701c90004c140039040002a0190007801d14041c461400026800b01007241c210600f56140d640350a8034402c2c46100c01c0c812042c09540c11420700c00c1529180c5401e651031440381c01121484040c540c0c0325413440e040703a030201849905d0001040350058041c48841e90070300300301c413a04c034001d034078403e150b00c0c6000b06025443d0b4040d000a210810850200300a50030740560008803600d59031804201c0415500c100c3c8003c00140704034001c212021b00020b00e11054507010550941c0b4640744183c074220480d070742d544000c1c1e4840050190a0b454a0902c0460b001e54000d031141e4030541c20740d100381450000c084a203601154091803d4504005070b16081e00303540340e66450300c10317650b030f0604c1c0003140743c180e07840301c060480d500e4041c01c04204505c5e8205200b045104820880c800da1b82e0700c10030700320034003000c0d10107415400c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 628178803 1250 628177553 628177559
    0x9090309011413060f0e12150601030f06090b0a27020d0b0d050606030708070b0313021f0c12032a1e020106031103120a050310031403030708060f0109 66
    0x800c81c00030301262000585080148010780350300310541070391040c404110342660281001d5441000003070100030550f500342110341c0514174280e5400601603c4800e07450f0f00c00210b5502cae0b12a412400300c10400c90401d028060320780e554038008010429802c0e12481003c4c074001450b501341c0282031686071520500d0360b903030008944450065070004808003c0341f030342ca0ba240070555a0340c075124000031f406403004180318078285017032601d894111b801140640d0b003c01810070070103030941c1c212540b01d84064075403607551a1903c046401d80c84140d0648841c6c02c045a03246050070f030b120380c0d030000d1031707000321120985414001c4040c2c00321450001e80c0c64003480c1c0e145150341ca02070790280003c00b03d100c0f40382c44a00d2100c02030502c5400340280065000607519128200184003a04020000800c0110003800780c100b003040035000b0602c5000b000900740301e401310004068410703401c03c0c80025034016020401c844410701059450398802c8071000042a0700b1004a041810555400040c80e00117071504120039003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 628180053 1250 628178803 628178807
    0x5060f040e030319020f1204030201050c04140607050a0c0803030412090317090f0a0815011e0e07050913060e0f040804090e030702150a140a090905060301020c150709050909030901 79
    0x4051450f40b00c20345d40811607015143c2c0080010032040021002003501402c10745402030a4420141000310700300d0f01031106001211202c0c28000700107908641d103581c1d0364042d1601908040c10100e015140b0350300c2400000d4200004802180f0440c82200814514072401e801546c1d0254039010162050255889184904000d04010901c409008200103100580d500001d0318080c502e0f040620a60445801f103403413001c540030418007405440210526a180444e1440d05210b6030340324801c2d26841c1400132a4001e4014001c079085004090983e540360102e1005d034034080c000300c3c801c82a98914080005000d0603450400501540e40290103a1500b0320b01f840c40c40141004481c1e1031401d000801c91b50740140d65000c80402c1401c40e060a49840c0d81d800980940496032024600b0030504080003801c089550155080e016122600c000145c191104030200380203008000307100300d4034441c143c01c1000d80b28281602c0740c490302d055540d08159039111014060003910940d0040c02c2c56000f48110f010640c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 628181303 1250 628180053 628180081
    0x501080706030e100f200f07021005070609080301030201090e0603100e0c19050405060d03020a03080703060b0703091a041d040201170a0b04050a09020603040221030d05060f040e0303 80
    0xd84404119000d0000c02c2c011041210607170000e50344400d5a03080046000c800d1103001000036086440385a003440368082c0d41c21181d11980c3e800034030130f82805070310340300c071a000304151a692038000380200941041441c0452240d0b0003800b050303001c52818080020851071007040035202c0c02e0058007908103c1524041c0c0c02c00b81401ca0b2640034180078440861040e17441790b4814010318002c2c904454122460001031104070341c3c4c003a042c02e0040b00c20300c5010700426000540701c811940d040ca4078880741e41c0d4000e0128024021034100c0f0079250b02c00100d00d000e06612120200a80b1030404107203091864401201c05036100c1d034451502c500c2034078000e1a0240d0b00c201c0c140c81c1e20900605052300b09030101c00c0380d44840c410444020820503aa40c1c0c3c58451410b2a1003450f60214443d00104103108483e000a4023900005200038400c51001c81c0e000c0611803e030500079084244241243e40b10010800c410001d4003086401501803030f41b40c1c5280415207040d00400440c07111941c0514610b03150928155510 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 628182553 1250 628181303 628181321
    0x60609061c030302190c110102010902010f050702030c0a090f050612070b0c0118030903050c030307030e1c0206180405061c350403062a0507030e0319020112050108070603 75
    0x10540c281711918100ba18150503a08560503580c3d1001244410729203050380b13040b00241c03a1b046a14010a240060b60841051220300300d03a402d1143d22803c044c03000901c0c000c0c0500e4841d400c407002d1503000401d00c80079003140743e6000c500502444250345101c24090a0700002c1d0500410358011001000403000002c000e002c9848680c0011802d180075a01d041425004c01c81c040b030000390785a60404c1031040900184280040c03c501070343c60505236440051000080c11030842c4501143c08003070031000e00d0000c100c9a0168007402c925202c1c1812030410080000a40d03005000301d0614002a0162600c508034440614260000c0047d55016071102c41070107024582e60304903200040100501b1006011243e420000307001034045d500c0f800c5160150684d0002c450311148145981c168410814140840d1108440145809503ca00395801c003203845400e4180955018028043d64811448984010405942c001e803114511410541082070442d1424480c460407a005240e091106030f119400400e41 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 628183803 1250 628182553 628182557
    0x1208040906030507030203120a050a1d0a060806040b030102070b0a0207020a181a010503040213240f06030c0c030c110621070906050c0604171303060c02060609061c03 73
    0x5103900d58150100701c410640080c1d4556000c1d90702041189001c100100044031025142828400d0050001e00306005051b0480117200030140440815400110b5449880c1c2005004234003156590b01d000e88071203001c0d40c000b40074a04000c0d040c0d4441c01d05000301c40c0740039404410302c076490b41d4101820b8001c0d007102c01c0881e07018200210001d211184555041820410f0880010b200f01121102003040b00c2d0182d803013814041d0500810fc00760f51142000d00080350b43ea00b0200d0b501800719804040d0000440c1d48108041c1207410100b940014002c034101510700c4c0d5181000702c1c48640c103007942c855515400090000381c2010b04480020b1480c4500b0312a00c00c0034021034280028500400f000008818109603003054500c200099035620070340345401020181490741c038041d40040d0b885d40f5201c0080001d410030303a500015074103954112040b1481541030b0303103044102c55264549074020340540c0c900a001803180c003021030b14900e020034025008420040c04808424841a1004a40c4030070f000c050301 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 628185053 1250 628183803 628183807
    0x503190917100e2a011205040503032a0c0312010f0515090307030b04030827030f09030307021206010801110f070f0201110d090e010b0310051309080f1b010908041208 73
    0x400d4280842c00200c5001d840703800300c01c131103080b40010107080018040d100c4090800d010300000c614044100c1ea00041d5160038800a0995007960f09a04d041c2c001f00a814410f001524620320b80010001d050108088915140c81da40d842ca2441c03042001805100d503c076924108e806503d0101d8002841074410240584101036529103031100d140004480503004100c0c11000c000e03c0ca020303070070510500502074603002c1c010910740300081d03924018100c00c01442940002d030101c560742d080056812040d402056401d103442d101442949400c420300c544030f01582018607040319030b0b0040c07090700d140600f91224903040184507200c80300340c900310312000d906115010400240f1044144070800d40c000300ba032120008140741c01045004108164418040d09009005001030325803402803590403a80100d44020380641841c000360300520401c0c50040c0307400350005031550030401c40005001d2510b1040c07002c0d6001d0454420701801e0703136150340c0c005110350402c020500141e8021540540094010720140d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 628186303 1250 628185053 628185073
    0x5010e130317010b07020906030d1d010e0a08070f0b210a09061b110321060102190b0f01050111061b090301050c361c0503190917100e 59
    0x49901c0300130b8001450307008001400c4815818054001500141e0aa008000d08000da08000709080c04d114081849032840700c81400c502c1c0e1081600d4490000c00811402c00350f5500d00140da91038100b4843d00b00f0241c00c081c000503484441c1c1055501e00c0808602e503a9052841814210848000415400b0015503a05c0014081b8041348141440a09522040d524020008101604c180034244035502c40b64010440304040020b640c00c1c0c4007601315121101141920381000503410080d01903281e05225206074096014841e0340d4441c14001e04011050580c141d13211001103070480000f5511002c1a4400381c00b20360700a100420103800d43c0308101c50340c1d0404148100003420b481d03003950907102039400032801c0c4110f01110070940205180111005000c441100b00c1c942100142c41c000070303c200d12181c0c07028504180007005440403640070041da035840021800e509166861620080c001507032020020540380001d032510aa09007080004201b091460181c00e0003820110241c40a540203803c0c03c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 628187553 1250 628186303 628186337
    0x20d090609260105070c020415050f061e031003120503010501021510050409050a120801150305060315090d09050303040f210c08070e0c1312030903020306090304170105010e1303 78
    0x174095400369490b02500806401000b0507115441114444034015020401080c0d03580c11088500030780035507a80c1e4071f030515030303061a0242c400c100075000b401400208000c860410140400160380c0308070404001000782c5c0030108d0742c9000c240203007400340e0300c080e81d03800b406584902e200f903010a580c2800404c0980314400315040c2c91349280e040f60b49030b21600401301041208030741c154000320f81e03140c481c0243d807403c081c0d2944c00880083c0305051640d941d0100300c180d1000e01501c02a013481030070250003800e00a95841e41c40040f800b034180080c4070b42d88085214680030085404a86802000d050309505000c844400003032078485100302c9400a4002200040308595040024024500585001032900f00d42c884140f000034407a15080c2c00801124103916150000c1405031020701c1c052488034210781c40c0540d2650a20b8202075458850b000811070700600000040007600d54610350111035408002981d820384d8002c0c0107003c03008800302d00045249010035440701c5800c0c000d140018807200d9500d04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 628188803 1250 628187553 628187561
    0x60b030c300303150607030203120c0d0507030c08073b120106050307090f021e0306100810151403010602010609060611060c0c01020706020309030a020d0906092601 72
    0xca40700552450060322000051441e0400d00350051030051840c40c41d102058040110400c4031441c80703520081006005d152081040e40c07960007846441e4450f41c100242464034540196460302600d0f41482d0005074003a219000c1c6041445030b64440d400f4540307800c00140e5070000ca0300c1050306458240246040c3c910000320141ca0b141d03450410f10301c0845550018418060300315100240c2d035030b0404604004075200091800300725440b0600000340922a00c101c14080c0c170869080f0101c16050043c4410111005c000860040d20101c0c6c2501100214101c207882c2c5d41c50450f80c1e03420444810408101790549011a1510702c02c41e45898184000881c0b0341020541080e00400b0060395650320501aa40452085c20301415071410400400840701c0360b0280d80740b1004019000e070889c045049440142c1c25010f0300c10301d950140c1d0540d140c1c03400401d00d41e0740760440c0d01c4120051080440342145c00e0f003c3c59030002035038003580e80c03004046d081c02005030942074450a416024142d283c43c0c10380840c400c2c45 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 628190053 1250 628188803 628188829
    0x1020109081804050906011811070501092f1c0203011119081305061506091e040b090105030a030c150c080f070801180f0f09030c14010513060b030c 65
    0x400b4600740900720b414802128002840e180c40c070f030f0001c401813080d03182400d1140301e0401d8048000c1202c0001c1d4810646902030580001d006601b0400210104080100ca45c00034000b407448c200c0140c5204036140c0703401118611003d4201000514003901000d0319000c1500c5280043c0011444d44003085007034005500c4034030307120050090754558000440d031004a440d0010076028850142100585840d501d401c800342c0f504011715034440c105409034903400260790005200510b8808400c4130200412454141020306d50f210b01c1c40c0149100c41c6160802480b17051300d5016006081294240e50252501d00d005401502c4484140b00ea030042a0042d001d000380c03100080c2d50340445803d2a040402c0a084c010304410305000d500c00045c0102000400d401d9500d00000f41e01140c840e0202e15580e00130149200c20799640d03400c00d2440c10605810100f14a501845112581d140f000020f611900b2108140c0d030682941080d08400d00100749690020101c0700350003400d65001c5a400c8002555030a181c034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 628191303 1250 628190053 628190077
    0x7030e0303280909020304020a0e1f06030f150321030902060301030602040512010902092205060907051806060304080903010b28050306060d1403040f0602070e070507030c020f0102010908 82
    0x107100100095003e0614802411081c0e010750450502d50700140541c2c400c0d00511f08002c15010029648003410740250468003c11103002041c95202d960003005000410651403080e82003c800021007569004502c1c100c1c0c1c0c104e4403410f4038260403054501c0000798512860200758480f42ca141c0540d0320240114000d52080d640181e940345440e080c0014084081c1c920403140e40f40166100260300c6941c6034a50040d805140c442c0c00d203d91030964094488401000b41240c8118000c00c04000000141d00f401d45400f1034001c5a2144120281d1201103411184075070400c0f418000700d40001d11903c05018540c0c0010b00214108030400c001c0b032218000030b04000f14040300c469455000031984201680134140540c01f400807807408401082400640140044c1001e44e6824440742010081c0180d5000d44101016080e00d140e40d581e0007035883e180da0107080480c0160310b002c90b940320300980440d001d0540c180c4410f4a4004641c0070040b50340004241c2e01c1c10765483d142c072040002c0c0381e0401001e0f500800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 628192553 1250 628191303 628191367
    0xe16080309370b0d2318030c01060e0403091a1801050903010c0309030806120601140415060c0209071b021210060e0412020703150b0301060f08060a0f0c0507030e0303 73
    0x50a1301c1403e0b40d82540d2054020356207141e40d42c41c0c90303070101c90b00f0750301070011041000c1c052000741e10301e441c1d8032a010ba01000b80d403030004003141c9000d203604024011030113a981e801504e51194011040da4646000b2060040f9041203118040100e00f1480d400e008014148181004c074603002180c250752601d0781307020019075121002d008150b0810b502c60340144c42510b0308182499050302a540d07449042c040c2505100e401c01b88281c01c0d6450303030030994001c01e8454400161660713520000d13003000510f2604a10400001c80003610b1180b1540f58007010076041e907410702e003101e0140c00b8031280c0040100ca404641c081d1051820107000a8000c1300c2c010030910f00b000b4417915041c00d000c42c210f030440082d1000c6400c803010400100300c90000c0ca00c01080c01a0000404141d1980000e00524155001c0301340850001c2d0002100900460154803502043c90107025038002d4842000480b0000a00e04d008250b082c0002408607104442e01c15000001070200c03454100c030300d15102100310b107640c56441c0a41038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 628193803 1250 628192553 628192567
    0x608161b080d05090d030b030a020d0f050d050703020c010509090601050702010908010e0f010b04050705040e09070e041415040b0a200708040609080604020a14060d0e16080309370b 79
    0x20480b03401c51110b140346c01c21501402c100003a8513a0a010340c0a0310030340c260707200e50060021040d09a111540d002c0210340ba51007610401502e181c011440603405030281049240d07036540560101e400c0010010807440083d6102001035400d50000407003a410403259000100f0a45001d1092100c5907500c0001401d0b0384500b40f48240c251594801407500a50800040c084400d4110041e13406407907480ea50641c0387e9680100451031308286500401c51118004240b005000e100f22407100520b0042003559609542c1a0701110203403000d5070010f002031030500000311220100d034842c9440d10b00c0c1c0c000e001b50107044c800e10100c5540000b00c0c11350310703010001000c000301d640040c0f00f81c00400122010744820f140c03030780000d0128401807160295030200d68030625040c2e640c031000c039900414104401c01011045100c1c460b07a0703101c0f4000408062241c0351000c03620b100000151181d06800410410a00e40f5415000440f401000d8680005036485800b044403040d8040c1f0f68400340128040143e11620 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 628195053 1250 628193803 628193821
    0x6030c071202212514060708061804030c0b07020717030a0306170a060902040b03030307031e060308030a02210103151b17040c090f02070c0608161b080d05 68
    0x45081403d62100820401c80e907407001c89074802c40f22910b900040850304101410410041115000094440c0c05814200114070390808002d03402078038142c4803001011004003203081940700954025010a00320408480055904166103500040910555000a41d105140329000d003201507180e039035800104181c4019607061207410300514a0110301640c0002d41400a91200400003000d41183e03103032074000c0250346480c7c00004a6400203022030b036592900a0004000b8101090f40a0b0403011590200f00414014060780040c2c907085260035141d80c840c9045400258070440d0300c00c0c44411502d50359100d010704501d446000390700400b030800c854107140c0e264000326103034400220101d2100c03c05a80c80d6603400000c1c030034090906001d100b0661514103261340801e16a50001d02d11a080c80c4d8101420301e8542c000c1d00e4420321500750b010100380c48400070303100c3c05c0702144c00313100030603d40c12002240c80c866170120084402c41c800300080050300c2e8440910660203254180c1c001619401030140b070103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 628196303 1250 628195053 628195093
    0x90c03050f0609041e0203011b030b12031305060706110c06160c120503041b1206150528090f09050c0f013903090f0914010506030c071202 61
    0x20404581c0b04001345019640e045100e50140c040450103c0c1c030010311011074400350305c9100000e40d00c1218106200750188010007410740c0d0040703903016885e10b4204505282e000030a2720030b400a0100320760b80d02d50909040c031800d50445e035001d0312040d0f00d4401550000c0b80003002060130385c94103c00340942d0301d4440341840303404650810711400c104042a100300425105024901e03140c5c01071400d40c3e03481d1500d007400340800b100500e4007040002d800b440022002445109101e00c0380c460f500070b110407588105100081d0340c00d403058030b4100140c151028251400e004010300d041d840c0100d207031211a00ca0000741c040b51040525040c00d990364801fa0300a0200400c0b104c1b4401500711408405101030000007002071803013a11040d5454505480d111a121414201461503100d4100c0001320071045d05000b005507800e8491280e88031800c0c1e0307022940071000e019810301c03190040c2c400f104907481c21050041e00d62006281e5140481d090142800203140e003517007000c490945600074100120350306444a001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 628197553 1250 628196303 628196311
    0xf0d0203040c1502071403010b040c0233060d020a08011109040b0f0f04020d06030b041505010b03010f0e060103020714070f0b0a0206160c120807031a01020a1b090c03050f 75
    0x11076983d52010300310943c00110325041c3c4036100010040500c004010078050840700034401d5000b400c2c1a91003514640c0001d03000000300540419500001619401c1a03c084440c40c0c0100b901605d20001141c6041c44801e600025201408202040d0b40d2207440f00d003190620801d14089840003e0301242d03a2070a4041e040d0700380d80440d500c003550b440e09400a50036001c04090140580d40214041044101d01d901c840c00842e0400310380c152500d0940f40104910310720741c2107280f1107890007001042118085003640e05846101c140005003a04125280c1e5041000401c0641056001c00c1000002482d1a0409400c1c600742070080408509007030355001d10f084590095482400e085c040d81c0501c5070f00281054101c4881080070000d1040e200d801c4509940101001d010801008000a012584406407500c01d0400ba9801c00c40207080b54408071030b40c61401201030040e8442c1d2800404154014510070b002e0052046040002da5605140780c251103440320340380c010a80c0c0e40d00308041c0380c08980f0741d01d0340 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 628198803 1250 628197553 628197569
    0x1030c1406070209101809020406060809120c012d05011a07140c0607120e03060403090b0d06080106060507020f0901081e150f1602010504080910050f0d0203040c 71
    0x244910490120301140510040684070341e80705000304400c4507000c80200003904144c9505c921692a1b2403446001d805509012070107149001d10000d00103106558260081403044080c01d401d0701020b83c0d40405405c44016811195030701c1c4110b030351403548250b07000541d1303415900c00076007407078404152803c071041680b041c940c80d2250301040d1000e0702481d08449400d82c2c00100c00500141180b4654900582401e146400413400a500d400b8441500503c2c00e04080507178480900030243c00c1415228a0180c400034085a8071107404d00c2010a01000303000b00c50701c01030f00041e10301d87d130350381c15030030b403a06540514003050000a4210960401039800c00e2684000d45024070fa41d45800000c0d03681e503500200310f84070001c140c1c9903102030482c180442d50981c0200340d444070707160905040030510040d080e1000391410760480c80d10001140180201ca2045810024060400e480c00f818000d0602d1240000010003408100b0000c6030447c540140008032104103005844e884e0614207501142c0081c0c004040d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 628200053 1250 628198803 628198829
    0x11032e0506060f07061503140d0c0336031b050d0818010504032103060501020a0f14070314030405030c1e010e0a0b0307030b101d0909031b0601030c 65
    0x85584803402122440140c40f8980c81c0d90348850b00340744005144400310054158031240780041480003285c00404181c81c80c10507590f45503680c00c4151102005a80d000b404a1581c120490180c440640e001000d064584221041d20b006c1e405055088251074000b2118114440040100080e8201c014405080305842241c905504c03919540814040c4519110441c1c1116102503150b910880a07540215404090400c20400000070401e00c000f0400e15040002d2400e100020f0642c0300149010046070040044501d40e030141e22502c54405500c4e072094210311420000000050179141040385404003038000d035844504000c101410820a42146441801309080c56242540314080b40e079140f9400f4201010101c16800108006201560180744203040200400200302d030150000410410125001e04158007940016200621507260b0501041c00140122150f41092040c1c2e030f42100b03880341101e003018203000850b100c1c0240d0fa1080c21b0f064000200400400c00d0040701e0a0140c0458485a4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 628201303 1250 628200053 628200061
    0x30b0102011a10020f0a080405040b0a0605090f041b0507060c08100905070e0d03030b0120100f0e0703120806060f030a2c0a0c09020307090b0711032e05 67
    0x305610400c0842c1d0302c91441d00d6180751155000300510601020f46405855082101381041076041d0030611075980114145a00038605140007443c1d1000c2d50603c1c2c480c24103014105003404004091201b6560300641d5403d5407450800d52551014030010b00340d03680f25600c040a140883c1a1182031000c4070a01c450305007844901c11030700c1051015103942500000d525a101002150115a007081d81c0e6006803041c81d0b58014540e01d0340100c4900c2500381c9031140107510046442100c00b0241c090000350b5084100c0c0244451080d8020f0b0310311a4054402003800542d501506051040c40d80c801c231a100045120031100d2600110565804207007107880c2820320500e6040c0407554400241000b005540e1210381760610301c007113800c2641041c0141e05200c0c41507480d0740e005691b02e240103070541d0084078108000030204c00034001c0324421510390340c445000030318001807240c06402c444012101c1070142001945561400c0080c0030240c1802e80108103040249000425503020070800c140810f81408100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 628202553 1250 628201303 628201331
    0x180609200a080901110a0906080f040302031b0709141603090b0f190608070503070b07020d0305090d0b0a0506040c050a080615070b01120606060206010f05010503041403070b0403030b010201 83
    0x1550341c921003810088050781d02d010f10030740140006110418158004105040c0d00c80e445003004041d030703500f0b880b000ba00d81c031143c4242d8900032013114002c0041c0c3c02040300c1940d6003480c46180140556400440708540d8a0f40001c8081e54403210590f0900d1030b100c0308000c88000c0801a5101c10285801c0030080c0680c180c40e0307800a840028190f03240a407404000c1140e90b402441c0d10742c280d00055204124840c0c98540c01e80c0c4031503c0c0c1c8103003442441040300208403d0080c904a0791402e03402045a2190640f40c1c1d41952150044401c483d4002d100780a04004103480c440c1d043c1c4220301e402070000385072411004001c00c903000e00e1800c408002081c8070b01c9040d65045010710360401e808030340040f014030304015110814450318400600256482000107034140c2c81012040c402c501c507035010b0007080e855076030403661610248684072910a240c2810899540100300850704240592482e540c44000d284c840b034503580c042e603811212046504104030a059046c81080200d200c01d01c02407007154034400c84 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 628203803 1250 628202553 628202557
    0x40f020a0b031509060607060f0506040e031c110c0712050105010f05090a050910060914160f0302071e05030924041a090d0507060f02070b070305070c18060920 70
    0x409400341303d0100200724150740710029288034a602ca0024000c280c5000340000242a0030f0341c0240c020303400e040001002420100c01e5076458404a0040703c001d000240c1d580002e4119001c04800120082125032110441403107400050030b06084c0d5041c0718011460315500311101640030300716a01c07840c01c041c0602c3d5907070980d01d5001194081d000c0307695204c0094040c10104a944480100c41c41e001e03002a240a1795080f1060f0350344480054000c40d61014801080e4440030410880003900d41c1c140f43c03503514020b5000e0984180139080501c002011400d0700310b00b41106003002e0f07178560f03c04110204c080c945254001c596180101402d0080c1c4001d044800b02c5005a006141d154011710300c0c9034807401d020100343e820068000b800034460100c10b0420300d44030700d5180545030000c1c1918840c813400c207000207058800c440464508030700d880f0071520b0407907203600456402ca540700e0f203080d000503460414401d58040403240100000309076182007001da080b61512310304503030324202c08480d8085070382c00141 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 628205053 1250 628203803 628203841
    0x5040312030923070302030c03030306010c021005040302131b030c08070c1a0a051b16030806030a060e03300601051e03040503090a0806090d051e03040f020a0b03 71
    0xc01260400300e40c40d12191092500c00003000100d038100703c40907581c1c40041c826044074025001d454448250f0024142c40344000c4400d203000c036444e00b40000040c00e00300c4a01c0710240305850000d08003501d070f60005200c5440c0c801000c00e02303a2903101c043e5600e507406480c5000c850745401e0410010780050000780902e5002807014040c09104400c0d901030140d59564030b034000701d13400c00c80d071030602d410519035000381000d0b40c5901000c114494010508004403007107980703003d240d21401200c0919903400b11040c0000424030368260041c1000b5600007202e07800356004469840028545850b02409400e40285001913000000100c1802c4001403501c01c40102e50003280a02e04903a450f00b60b512602c841c1388017031043c1420bd510002c00c00c02440b90120140048000c22684a0001c0740d07184e0030250745031001d482c8045140c00552180001d00e0060380100340044074035003040c0c407041040200140039003003160107581c813110340d010503411490500e0b107160140c01000c42aa065007040d284401c11400200c1f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 628206303 1250 628205053 628205057
    0xb090601050f10170910180308130503040311120604050a020f01090f09020d06050307081f0902060306010305040615060801080d050f031f0e07050c1203010503030d230c041505040312 80
    0xb00d002940b05010b603140c1040c008909110702401b041c0b2499141f50284419000980341e607000c5101c82c3c0fa842d0031403041a030440c00450901c0d00b1509d4110a0101d4540c1c001c1d88001255400150b1f030b682406024461400f03600684040059030052010343d82c03403503009504006400c0030900942c440070128074151662190010b0700d8200e51515500100650341042d0307072500c10000b000490710400104140224407400005101c0b261050050054420045000390301034024000a651940f1a90155501c1801103c010410210031a084a101807039a0400400560490010700a0160030021200001082c2c40e02c1468601c0c05131034980c0500015184980e180b0f2809000907a4400840c10307a00070703040048030f5180500b440c800142260b030059014540314010181c0d690600f5400000740c90484001501031450003014034440001840c9483d1018650280c01580024052045229a21500c3d40409140c0c0d00c50902484004903a0b80100300c0040290400c018030000b0210614540054424 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 628207553 1250 628206303 628206347
    0x703020a170405030c0a120f030b0d0b0703060b1323010905091812180a0312110f06040303150f12120e100509040c03020f07020904050a0b090601050f10 67
    0x20f181c01402c6100380908034969100f04c00140d424030145100403094160a91110b00000c0d64420f41907003520002c415480d4000c030b0700449140841d01081c0d203070394003010340e14001400948400440c03540b81c01c404c0131403003c860641018002c112407000642501454010080c0c90b02546074002802c145c5a8003440b0b01410218000c110000c82d610920341003490400103859070303441c01c0681c01a09800c040480e40b8601101c03110007080d4100b90035a001074030380102c5040e40140140805403521072440c198954548510b035280c4400c80801d000c100d010342d1195401043d00ca000d0071205011202c10380000000311116013003045243c3e8070940c040c103066440b00204004090500027174416400303403501c0c95006802c00025034000c40d407190040c40e0707406088600b0400020307140c0088003240509010604001c104001d07500c00751034040001544076204400321034000c0f04940d540050550252000507144d40000014450f620b005c0c911801c0303021090305e078200d075040c02c02d200810801c00c2d01d16006c20b030b01e00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 628208803 1250 628207553 628207561
    0x60603051c090e160c0807121403190e070b16030314070c110d060e0a020109080102090f280e090c0402090607061a100203030906070302090a0e070210180302060703020a17 75
    0x344170000941750000901030300c4201c03c0c24548800d00910101703000240200c401c6029103646641660701816400702e90808512142100703000800f61114540f86a00c030325880080d44000c60801440d5854100c250800c2c0d402852038050b040d0f50303150340c18020100c0c146042001d095808503020b441d460308251160703a40c000d2036000c21000e440843e005080d00d801d0038a0f0219603200050003040c52071007a41c0c2c40e03401c555101c031820b080740680c8600c143d1045840280e0911407514490603807400c0e52894202e182d0a10011101d0f40d41c00b9154450003000451034100481503009004d131743c5403802c2c25981076283c6424000042c20394030404000910b07a60391650038000e13103000e440c5113001d001009072900100740300c0200080c0d520b4104a501e0800d0384242800078514078070a000341c85082401402c0110050304120030303c0c50080e00180803408600c589141000c1e000380c43d0007200e04866160101801c4219241002828070000515010505004003e4414060703404410414090700c90104c4c0110b81d10307 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 628210053 1250 628208803 628208807
    0xa0c030e0406080606090604060f0b030a0f062d05101215090e0f0f06130614040c1d010f120204062402061003120813060603051c090e16 60
    0x280300324a55001803a103030011032460300000c0c405016107012925048982e94980412060311564040c010460300881020001482c03458040d6801c070207c00d40202c0c1d1000c849588030115841d80d48028101e24156510461203c410500d940b4405109a0426101e501700700100f410341800c004032070304200c031034a06500c0548a69001007501c0c0600141c0d0104559107000032030203030a03c0c040700e0b140760281c5032150749034142c0054044490100b01c4d014090700d40c1c401c071640169049440f401e444098460b8208050301c0c035804102d030300c250700c550426102c0a080c20982d072006494441340700000517140380140003c45001410800312040c010b41d054040c480d51001c14041d180e01da001d070060071062940c3d07078075030100c0300803c0c5002d02a55007181c1c4180d072001030542c1c00c3c4002e0320024100074000300c05030543c14828030050361b021001c1a6818a50b0f403466656030f04803445a8000d4404e07400001c1c020016483e21200e5a13031504031071804000103420100000310543d0007404400c03011b04074803000284a4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 628211303 1250 628210053 628210067
    0x30b0f0601020a0f080a0909140103060b0604030c150909020a0c1113020d05010e070c11041a03031201031101020c0a050f19090506031c0807030c140a0203090405010f08030a0c03 78
    0x2550158800105880a1421000d540c12030700c0104c0101d1f4a1840100d100340c010b04c03841c0c440341c0d84050710401c00d900e10388480004050010102da0070a40820011011500640054009241d41c4038040050b00c0840001001c0b000365810002009004104240c011035100c18003940041e0003c4076540c5e001c80b400002400079920520799103682e800450926203444150323004a04982a0001c1401c0f2551100380449030384c00f050398010b00c660044c080303400780d60403d548802c481d039123801e80b501c510940002c0021700d1074010071010b401c00070540c8018010002d000c403600d80c81500c20700060102208040002e02c1d480464003c040c0202e02283c420007440d40c6260820700c14000d41c5080e200d07090340b103c0b4040042c1c64115540780c024480e01031202107412070304185000d1003202d681c80400070f0301c8a50044000d44000403602041201d5004c01650800018000340b020030b031150011541c40b81ba9505000a0341d105038001101103285180412205002008654003880c15241852a81e14540340642c8c0c59 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 628212553 1250 628211303 628211323
    0xb011a04120b25081005040504021309080d061502010b030d120e10050103120912021f0c0b0c210906041410060905040327090b030a053004030b0f060102 67
    0x43c0c00f040e002c0300303641900001c1d0180074400e43d13420300300401d4031641404240c407030a131002074220420700620050302140760304ca01d1640384100c81f4940781641014140c030a84965802002a400769280b07a280c50750707024031a01042040075000780c004a904404003820404400951450383c43c0c4807410000490400e2207807100341c1105500c00c0055584034204030300307014042d0078142e004c03a010031000b0543c000c05004081c00a030b80200050b0107a824034088400890341d030039400301400800008140014603130380ea114031a032107036003540e5200c40c00d4410030004405a6451801400e81403c103001c5a81000724801e68082c1e0041a070030b205c040002c01f0a03150000c0303106d6010110345051800700f1042c00c80d070005030045001c0e90303d40740680131070002037030460000f59035000710220300842000714291030340200843e18401030580386041c4407a01c0b403038100f402642103008501c40750780c142031003003003036126001842130200c0910342440d045940f40f004001c0c0213030804620b181203c0005105038420004c03000300c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 628213803 1250 628212553 628212601
    0x181209010f030b03010e0604021809060408071a0f0a15050d08090307030c06030f0b040b0a050405060301181101020d110d08131a161704080a0504050d0b011a04120b 72
    0x20b00aa1b2003104c0f911004107650880c4150314014102115004070703c40d6074002c00e1548054016500d403643d55030215803080008441031844241800b00b480070f071020310b601c2954010511100c5180c10095032044500841c03078030240211030780c0300f0700560b240d0303501c40303840c42d45d208400c980e03200034141c000781c0342a074941d0000b0001d21000d400861000d51540003100ca40c0c1c9940810b01c01c64845400b04010784030000f9929421150100d400c109600c2c094120b41c0e009200a000001c0100c9005442c240030340c1c030f1880c20b803260792040010f1011568100000c0d07500041e9442d1000c031394000035a00c00d803101070000303000303080010680110761541c001502943c0d045038002c1021440300c01d038041ca07401c00c007011960b030b0040f41c100058080d1202d0140c042000381868448400d5429aa107039103018507a0071105000040100c107010110702600d99420210890380200c0c501e150035850003000002149644032a44078001080c8001c001041e010100460041d50102411049075922000014615068a07103000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 628215053 1250 628213803 628213811
    0xc05150106120207050a141e100c0e060a030f0e030f1803030a0903060504050319020114180d081f0e040b07030603080a030504111e0a08160b0313050303040803181209010f030b0301 79
    0x100c8c0000141540e8030308181c18103204107031081109989207519105034030341080342002190f80846c440c1e44009950104807100040c0c908102800610b550001c003a281010080081e00d055036400900c10200c20b02e108a00440c50710700900c600601d503c5180c8401461261594003041c02c00105009072102070004120301040c010610000a0203012030b0102c1520508800000c504072598200000c2c00e8051003000030200d15a80d42c104a84c1013000400102d0380c913120712002c01c5000010620b80c0000c040c0b0000e03181c07030340c1418200000710b0380000d42604107141c80c1510800003c0d00c03081c10344200f82d6140c20000f50994580c28000c0c01c000e500300b00703581d01c0601c1000305154440b601c03442c81c50204041da8204000e0f134640c145c1c10359480da0448052003c0442c08800c004118100000310361000d4410350301c24000d2000d54070640303160410b40d011250204013008120300c4044007441c240382058420010401c0880011281c08030344078000085042004424001c001c5d18001d030000000280080d000304 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 628216303 1250 628215053 628215103
    0x917100f020405120c03030f0a03060b041d22060902060d0e0d09060c02030606091b040807090f09030e062209020d0b0a061d010c05150106120207050a14 67
    0x340203601a01407644903032012400c00714003280010f4070310700090f4050011480c0050348154400d8a801c41c8a0000415480700d9001c0382c011a08000380000300b0349559400c807201e04040c03006451104c001c00d2aa6807007060b402900f2a0560312580622454210340001002441030000c50100e00c1200c0d110303030959007070000303060000400103148130441c2c5044e80c45441d1039485003800c0b5403400412101a40c15880a0701091441c03409501d41038108000c025000d111810703131028001c0c01e4004e9480b40c0030710f8024100800c4640480c2c01092a650110442042103c01030f5401500b04201070322002d024036070108a0100c0079a22501c4885241d03420a0140c40c400d5844111202942c41548014909400c0101c801254102802c1140503a04a80c8800d90444078050405260b10082444039041203078423403a00010510034048010882c0320020f0054080d0b0600c0c6001e40303410084100d00c45450707c108115408104003042c0d080145621850591705000aa000035240060b94440c404100350398134200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 628217553 1250 628216303 628216331
    0x30607020703140a1a150d050a030f05030c0a030507020c0310020c0c0406150e060706060e070f02030406020c15133c0b0c01062304060b0a091710 64
    0xca4100d0f03116038140c050540c040e681a546038012403000515181c0d10199000d62003024110241e882013105112010000a040000e02100955401520300c2d4028041036814581d0002c00c1e26103404c150306010380b540c1844000b40813944248400030040541d500041a0b030740d0720030320889026030001421244080c0300090001d009500613841c01d0214410080340c4865401e060007004103d507028a1840c40b004220182607a410094410642e4042010030035100000c84c40e11401c4060110f403800c2030004d16040b440580b081602140c2c02c015940305000c1004220390008029041440955000000c9402480c2c54220790142d500310390f004040c00e2002051081d9a0040000d1000e200d40704c8201280c10180e5540003140100c42440340146410740c24002c0c2c24500c0c004041010001000203000c81e0349000120f100d11100201d401d007200210505d036020315050042102400c81070303203401e1500404240c00b914004903485a100d0507899182009000d0308280041c41003c8803110050250400403070103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 628218803 1250 628217553 628217563
    0x140c03030307030f1b0903031b0b04060c02150f130218070f020618280f0b011a0c1504030203041a030105180730020d1406031606051803060702 63
    0x3542e07041e00d007802c0d80098145505e1030400d443d0381a261804d02c0c60442d2000c941c40c1060100e0380380c101c444a54210002486806000c0c4258010074000404a04c200c40007401d102c030050408219a150b8418810300b680a02141c0c0d070803a4901c220503602101900c00305d0f50170300c880d0030040c80c401610002c1041083c1c0147e0804408042a0b00741c070990755801c41c540c40410320022000300103501c00030118a0004880d8500071049148110440c41c280c81940d40340b9078080011030403615049454010030031140300c103210239a82c0e403d8110103030070520490f0b8443c0c2d0382c000d03c1719031142041c8400082014035009004490240841a01d9502c48801c09034071503407170380d100303204103030241d15102c01c400000d0203141a070b00d00070303045070340c2d01d0407800c0c490001c0e002c0300841072048032a001440060000300d00f4040c0f00405604644c00740100748e81c2c8115960f034404103030082c81c250190700110362907a460344480c0e000d0001d48801e81011501d41110000711030010204801464047c031901040c0701050350002a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 628220053 1250 628218803 628218821
    0x10224060a06050c0a0303050c0f070303060603050c1e0313020d061b2c0a090609230622090606080303060312040501020c0f0609190f0807030f140c0303030703 70
    0x1507060003596106400c50f4240315800001107550092040300e000640300b81c2160350480030f881412414200b1801e264645c660107840224042030b96480c08004c102e405020b0554050001c0700040e0524010b160544400020010100b10114000001540071800a0410500c003234000e0314100410000345012030003000c15031a40c1046079040c00354900080c2c85804084c000d0074911146c3c201e44241864001c1d4203222403000941d100480c00d00102c4d0000080c810300c4010602c0342000f00700c0040c0d41c224514030600b11301c0316042c00400e141c20890310b5245c4c090201c8010401c560003c1c9114244007910300285482180200350394102400051200c0001024602851080f030607a541d0711100c40c0c3c4072407a0b209500c210303809038021200b000000d180642070601c2d00b02018040500e85a40280080c84041901040101d1116070010074089056034030312100140ca4503100500780c036811625004114141c1400040440300a130625200708a000d00081c1424000501104c1e181e0a02020150103410501 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 628221303 1250 628220053 628220059
    0x250f080601032001090306051b03090114060a05010c120302040317070302190519022e020d08070215090309041a011206030f0308090f030a0201021b151501022406 71
    0x90310f5040103c44201254042e5070584906044600e5551104080d01c401440c107a48001e19101800c0741188000066204842e010000100034450128001600d400640885d00440e01c2c200140000e98101b03581c8000f8a411001d0f004200b001e070300e1b04902911481d000144062400c5c40489400001c60b00527101c0648a602690f0803c210301d00d120480040451020304158400b9001c15090031828a0001d030450000d01070180038940c0034200084901c00ca6a01d0080c0941c80d54813411040d41032250580c01c0c981741c5444a1315007003a40703000f5a03a900c6400005104e40400001c034040701001c20071100b8844002e48248541240040f108004101c02054117011941d15600202401102d210361001d070f0754002581c0e000741e02c983d14111079900c001000c03030700340d440742005039009c040c0c040020707101c1100300390f00150b600c0d07a1100d41a0500310100c0782041c4140c0c080071680c41300c0c8035100e0000d940114210710507900c0f48103550040740fa0100010200c012454650821003902180011140c4030346401c5e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 628222553 1250 628221303 628221323
    0x4050d08130b0c0714120c011b020303120103030f0f0f0f05090405040c090608030408060c0f0405090112060c050406050715022205030c090601080411032e05060f03250f08060103 78
    0xc17030510881000c81184008a034004601c50349a945c01141e01c8400c003005403400390400c0650340d000c00d1440d03000100b108184c1581100400806500400c4076940e03014a14100c6a04500c07100090003042840f910321341441141411008098850b03011760303070001c000400c2444981000c1c01c2881c0f07201c0c4a40151100c080c00c0c0b103030208200d08004201c404403090b03040148010350340c0d0310713200016070045124241c40c16001c2000054a80d11300621070b000c2c040c1c0c1c0c6510388207000c0c5458a4400c644583c0b40c0070090041c2030000304080c54002055400c440c0e04481c0c580c0920403101280c800071320412022401050040d0100a801e69000d000341c003d4550980484d015401c0c01c0040185045003103807068000f41942c40040d001640c420790b107001c40b0001500303c2e80149000403400c086040162001203241001c5890440c8402c200e000b542d400070429a10400184000808603440b40d00010704001c6448503070034000982003e50303481c800104017000e901110b1a4680d103556866400a00c8251189494 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 628223803 1250 628222553 628222589
    0x30426031e09011802011404080604050303090c1e0d0c0f0b0901170114120f01050a1a01090609260106080309010909060609050d1118061504050d08130b0c07 69
    0x105100d0700c501350aa500c0400c05110065004581d007074000144440c2c070314014840006c1040c1d08100d110b0190b445140610b0301ea1800b40e5030b2a00e44804640c80c0e0784201c4444190020007450030121080080003a42c603000440294107040140c0e41255006100001040e00c0010359101504050000440e00341d1340c0c802004002d60010035503842c01e00409140c0d040c80d958140c0301d03140568040000408120654081020342035800d42100d03011106144415115a0600e03c1291a1130140780d4020303003400c10100907810a00c3c0208041810300a40c00900f00414004409100a07045501c2d113020100007841801d880740c48480c2c0703c2e00003560403808550300f11008144a00c5900030001558519642c4642c0c1615000402000896540c42070719070110301c0c615842c1b00e0b211010480400c1c0344441000070681040c40c1800001b00b12040c484055190a000c1804690f6491a40c5454150400d100c6a241c5850307010aa200b01602da0001d407222500043c159034001001c03d0000031900011425014004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 628225053 1250 628223803 628223821
    0x4050405070608090f070b0304060e060405060f6d080d1401030506060301090803160e09041a0c0406230f160c1a030426031e 55
    0x10055900808682201d0401e2040500c6a01c2c42a442003640007180d414820100c0da080c1007400c1a0480f02034400000100002c4c000c40c2d00a07002e04140703601c01030125145c242c03100c43d21500054081850044040c4c0824480e0071548034900c0e43c0d01c24203522404406010036116050107440c203082c410f0540065800d0401c41c3d50019001d0b07200240c3c00311680f810050300e00c000045852503021100d0090a1060000b0b0f426a885030320041325004480464a5056007841460b00ca0000d08540c480da042510b0700780002d034000300b0750382c01114042101180056490051716a0100d42110b240c000074108104003d000c1000d4035001108100100000c2039240c08041c480548151302070400070070110a1300018035125124a1001507807448407450400d02880c07282c1003640e01103800360f2078420006000000740701c3d0312041e039002060b560380100710302d0f241c07040c4001c2540402030000d000703c0385241280b40541402800711b0a49108030b00c0040c1e403031503d1035941d2843c4e030fa0f501101d0144404c010002d64999 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 628226303 1250 628225053 628225061
    0x1510080727050115050708070804090c030e030f0a18031703100e01060915120518011410120321060806060108010e0c0c0705030304030b070f05090d0209070309020d061a04 75
    0x921012401030082c0c3d120b080648213513000304021192107c041160901242c6490050000307045120710104190094000007000e80c0c030780440e814402d810410580003510f80d0032044074607014850400c15120a0f45000c10705170352080b9400a03110382d0450b200006c054203004015032051102e020221308682c0c6505896031803000034010800443c5151000b032001856100c01d42c0750800b40c5151080014030310505020a50b002511054500e5900301004038529400b0700030300c0303071405281000040d0751a2110081883d030703403540700c0c400420302a61081014503104106000c044056a800d1600407000008240002e04d4144122180c502515010495661149041ca4104c54000c46004815110145410110b80c00f200d000c950300c0c802c01c240000e244c0c4060010344011400740c01000070350310b04903001404c00030040f001102001010031071000140e07595051407c041f074041d07442c007185a0740c44000360300410704460080c0d4488886503000c1c00300080c40d00b1200003480c149a174032903640c0a8000344400c1d9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 628227553 1250 628226303 628226309
    0x20102070b03061f080613050f040f050a06090b060f1e040203061c060c030e06240d0812040c080c0604030b0705090a0605090a0605040815100807270501 67
    0x503040500e041008001000203150030410080c1000000b505005203010b481010403985000708401c101003005078900280743c1030700351488120510903403510380f264847c906c1000308000e1411004801500c10302004010f0b0500196105900304030101060900242c042d404844040c4074aaa62a00c070041d4141000c040703000209180402c900030b103100d000c02c00a50002007005410641c41a55007040c0082c4d11600105d545c0500d0700024540b13940c030030080c15903218070b00e045901d42c403410030300000c49031032003014034108140c1c6107034a180b421b070100040e103420356400050249800846e4180d22400405d0b4828019407007104c001c84810741d035152903070711032803601001541b004051000f0408101d220002c1c030343c40b0400b0b141c401d00e402c000000245441c142e9400050002d480030511066604000c83c6000207008182803076400d052a041c5226a540c203800d0710148840316100126649490203001800600562030685140ca41c49182011048280022501c40800791000814186e1154403d89050b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 628228803 1250 628227553 628227557
    0xf050702040906020c0102120f0604230910050c09030c011b0f020609060a18050303130605090a09020a0201020705100e0607200a060c1112030106120204030c0902030f130201 76
    0x1808055000c11000380681d03503041e140745408000440d002d59003840104024034058a41030070500340003100c0d0f2060100104024000c0e8a003801c80c0d040d4407105030840c07103415080a0941459501d41c8052801c240c04562103a140e64104018082aa1110b4014010500040d001c9459803e554401180d4440d00f0049410407003c0a240247c0400c4c10300c0b002e10007150000e00590310300022000801c4007980040500000540c40524028100d104503064500a00c4d044004504050703500c10b0960a011682c0b14403030a114000403807010940303456504800130031183e00f08540300e20419802a000c0e41c80890112000c0c086c10318590f001110610401c9180c02400c00180696541c0310415503c455100143c103c00c0c103881550348501c000308100c14a841807181d1004240c032551b0183c0500b10345040040c807a0070f90003840031b1080441c2c1000599045403424905000e0540030040710900031b01c210b0304003411003903c2c85030203d40340c2d006030000c600840c103860001040c0d94801c140a16036100074400240 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 628230053 1250 628228803 628228807
    0x3010513050f18030c06010308071a190c030b030a150b040e100b28170309030606040b010c0b0405010c0f1d041e0203041505160219050f0303090c0a060f05 68
    0xb000c400d090380c0c0c3c180503900324011281380c9510519520b1422500764401c543c1018002051400c100c982c00c001020401683d01144003410300c0f10304111754103040140c4c040101e50703600010400d24485c0d00700200c4540050140d40031b07405241083d60f80c2c03419540400881608004030003540d410148079049070b0605903801351072500c0031400950050400c8203a5503900035042c030813181c1d80d0014140d0885804980043c00c0c0c101c03501e40151095200142a0030200c81e81044c04081201d4030b02144456010b002201c001480c81c40ca00300681e0a00e0b2038542c084c004225100400003040415480700741860951707162034500d0745c1c5400c07040300d0003008000c5804028030b0090b40d0840c0c0303081c03581100744130f6031001c520802c0b00020410801c4c12a042218151035181a14907200c5041c0342c11b100705600244202c1c02c92190621049000c0c0d510900207640d900750003898480501070010500681039404101c0060f2696401e0007220745a507118803181c4c0f50f01c15120103800041c1e00f80107100500342072001d915028 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 628231303 1250 628230053 628230061
    0x1503020a0923100806100506030609271e060126190b060a0b040b040b070615060f020708391c21081609091103010513050f 54
    0x250200500907140300b020804059a800c040700d40c2a40324410101c400d861031494050018905040035140e01070300c0d51406010b12a9843e10012681d0221003038501e9040c5440d0684201c2503100540080074003043e030362601080c20313900400c0c4110b4400224414407000366414000300d4945d5000e106201c4120311040e5000241880e01ca003a14501c0a07043c01c2d29082503070000600b4040b00700040807140c07076034081d003040314a01d0040a9800981500c40b50302e03090604104240c000e511490203198640c100c0480d0203c104083da4012010b804130714031410b9080380e078883e805040d81c58850020000741c0115000850700c1c01e80041e641c0701c164218410100b84540010700300445950b5030089017035429076490044c2c00b0f500c03281c50618010801490308201c925990525900d03000d03006113a00e0a10401120050006a001030200c0c4c11023042000c2b0a101c480e03482c4240d810000e941c1c8680e4505003070015920500d03560b00b01441c1211000d072002115405110648000c9410482e03985050341000408a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 628232553 1250 628231303 628231319
    0xe130209030607180e010303080106021917070804030f2f030a12020c030d050c071202030a060c170a02091f0c080a230703020106050a0f091e0903080405011503020a 72
    0x10001108202c48001100b0341724003181c4403010090b002a8045001c0b10010010300381d0401c0b41e20b016406017140d00c90820b015907203610034a261910109030061020030110240181007088500031680050701c8004888175150078a0703072144d60480000c08a4250540c107507010013800c80d81403610b0303000700035242c01112907443e10400c10f00b0b503001500310b20a44111640381e4908128401010055858058503050b0184803540f928041e0f0704280340050045681c00b0041e2400180d509825074004004100040b00000855204800d4411200341414031702c04d2001090107035000b00840c10041d80e07a0a040c0c080000001e01740c481c1ea036100030015080f0241d01c0041040d01000e0000c42c1f40b0341c0740c60f50208084446920310704401c5081100491400200c600c00c141c1c0920503071780101010b44403042071629180c0f284801d200540b062241c0c55450b25480d12320b03500c0e107005041007031480a804000d42041410014040c1c08100c5049035550b207020001c4140b0300822a800c2e040301d60007006968114200284 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 628233803 1250 628232553 628232567
    0x50c04032109051002010b03190203150a020702030a0b01060206010e0c0304110103020d021225080a022a0d0e1905011206080d0f0207060e0a030f0201090b0a0e130209030607 76
    0x1a8904110303000c2ea02003a40d070b40700e40804007800850ba00118500c480802014207101d02040380c0100910b48602c500010386021600c2d90300c2d801c900d50846c03211b640715030410020744200d003070095160040130311035420042c040c0c01d4076041c1c0f502c1d81c0c21990079a0b00c562059590719070036501980155418000a03002440154000140c00f40625025040c1403007610b12034240c2e04a403074009140610349007044012061001e0340780008842000024030104410805420200e0142681c0e102036000111410f00c03490348007881e8460030600503159a10310000d840d8a440d0340c5508035100015103611440f441614127030715070300c070005401444800300a16110054500140e03200c420206a9182e40c00055100c030b007070003a0000c074111502d80b001c4041c0e400320002d0800c082c41d0495010f000701d1030100760322a110031003c0401e880d841041c100010800740010707901c408842e4800c00548100003203480700994400e502181c055819030310420102c608600c0c42007640540008a80c15a2160740004c1c540b6100d412 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 628235053 1250 628233803 628233863
    0x6040f08131e030201140f1b160f06030c0905010f03020d110301060905031510030b07030e01050702010b0307290304020613060201021c090c0320060418050c0403 71
    0x2000c40041e80e0390b0150a415104020382c1007400e401000e00400c15941c00410320b00f551490b40b42c3e09403074101602c840000601850380e40c3e10185110a01500070300400700003c45441c82404104280f080e615000d000c2070741502d014070000030f401c1120402119000345041001e403441615004c203070120f9a00110000d4000140440203a0b84034100c42194800f1a00150701820309943c0300a6568100f00030b25251002d00c0d000c0e50320481020040020018000c82c00c0402d59070b0080c3c400c4007540302da1204030003400c0c11a40b00c00d120351804d41444171841d015400340751021410340036190210b40c1c800c19104180c2036043d03c40013410311038801c2000040742c54011030780244010503c0b400d00d8044499450321800e150403200140c1c0d03000480c1807070142521050a80c2c607045100500108180d80c3c0c0f0403003e00c10a00c4010100c2c12501c1e000b14071005000e06070000d481000d40340503219640c1d0b140792507008600c00100b04c120f07454000850003850a20301100d007901c3c2c00114a40034030a081d60341220b89001c000f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 628236303 1250 628235053 628235077
    0x30705100e0c1507060506090c1606020c190524010b031f030308040201080114180402010908160e090d020d210f02130b04120f020301150b0301061106040f08 69
    0x8840c049569441c080b0300901601480951130301d8507081d1522a0880d4000741c602c601c030b03006800400441003044d0341104c21990b2401005000120b0f5031038040b01a004442d5480c5040c050410400c0103201d0b94991180014010f0042700d0340100301c4200100345451180413007204131810401481218040002107411020300b480300b000d011503140780102c103031a003a00b080700010300500a12081d5a4400841ca02601140081c0807050202c01c0008818414123000b100026560900142c156809007514800901c0040192880c440c40c44060f620040c3c2d90340940820a02954042000d0b8400040c488045a0300d5130001d00040d900040b040d12440c000b201c17025a421203034001c3d004207041c00d00603003034800b500310000b6854096050011003540c040c0e400c0034048034000d000030001c20840c0e1107a10511034020310900900c0c100c5001290140100c040c80f030034804080703080040c10745016070007035049402036035502012902c625940c54480300262400703410f4070700d42020b03000403483d42801071005d96944 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 628237410 1107 628236303 628236313
    0x41103070e0f06010203090604270c0c02120f07050d0c0b1227060a090501060f12150c050316110f0d090608190c02030f070602070c0503030705100e 65
    0x40f07115000c0d18405041d00380842c00d02c08103004030a82c8500ac0e06001441e5260005040200d00340401c030b00680612440c10a410004982c2800741c8150390040e0540c107240c10100410050721100641d50705d001d100d000142420700000500d03034803c03c6c810b982111320300403030102d0038000601c0503060004103044228034201404100e00364002c494140c00580000c00b8100036006244641004501d00f02400c40420105215109006498031803074103411128503090148003503c91000820000c1413040c0040381d12600c0404a002c0c1100741894400980c60701d0b000c8840c41c0a0440c10040041d400c185d10300034200b035110f002c4401402240c00d000d00c007420030b4400001c1c03c0c1c2c8210180d03981155507001c841141d41c820300840d40400000da503910348a1841d414103a001f944560001c882403812000001224203011040e105070b00c0d0010040c1c0180b01817402958058020715480c11418007403 = true := by decide +kernel

theorem cover : BRFrame.Cov 628057553 628237410 := by
  have h0 := BRFrame.cov_init 628057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 628057553 ≤ n) (h2 : n < 628237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
