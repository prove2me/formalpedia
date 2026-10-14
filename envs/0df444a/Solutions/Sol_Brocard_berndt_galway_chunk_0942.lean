-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0942
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:18:43.302986+00:00
-- url     : https://prove2.me/submissions/80e44e0a-c3d4-4874-8795-3da53c1d0988

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 169244604 ≤ n < 169424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 169245854 1250 169244604 169244629
    0xa0603110d020d150305030703120507120509121201031502120411130501060210050c090d02090c09030a08070605130c0e1e0c0a18050603010b0c0a02270601020c 71
    0xe015070b903003a4500c3d0366002403180100d002c8071030504400c00f00c06c00038040000c1c04080d0280c0d6880c00725030108400d58044a001740c440d8000b01d20003a91b9030345c241d111038001070b61283c070030f5090714401102a008403400d5400404504081e1003201c4c0148204007000e440c0b04a48180c00e90114100b424201e10703149415805400030b090b4100c840a040580c0c4c0c1c450750403002c1803c03001402d00c520b59480501035643d03000c000a080c041810940082c0c2e01c1c29980054440b50400141003854801c070030340900000160181000720150020414030030680c40410200c40c0151280310403079600c007803904048044440107080c2e10707244148201303945d002c20b800c18482c1c0b007a83c0701e81e800c5010685410071040059003c245101c0380c00451f29042001010126000d013070983c4285c1c8415004082030704045060890b0703402075944c045000c0c00180014420f14000c1d1101480c80c070200d54095043350005400764000c0d000c44e810707080598200303007400900c4100070781d00300000380000c02c604d0001d100000d0a003130914 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 169247104 1250 169245854 169245877
    0x601090f1e170d020615090f09031603050a1b030206010b0c030706150303080f01030f060506210f070b1e0906040b0c06061c02030a11010306030204060806040209090d0212090621060a060311 83
    0x8011070340d09c0800307004a50f44d0300d0403004c9020341c060341e514028060f50004079566001c20252a034031039851208005018a50f43c0c1035000d0301c0341e60b090003015110340d0041400003d092000b400f202d00020342034421141400403004242401030310b5850010001034000f040354504404c507000400004101003084035030a9030064000c203507952640c01180702502e0100221000505802d000c540107013001c2003401100034810281c40c40561620680e4a20f48605201051440207802540c0070445070b41c0f01801c0a61030042c2114901075403146108078039002031412400b150407403006e1103810701c1c3c22044589101905820030b01610402d40010b80c075424000c102401152596828015982c0302e94401c0c1e0255030300800c00c2000b02c1e2122450fa40c0d59204440490040d003014011800b407450006260600400660041c10741201003200405190030480031640c20840500c44489080005003448003c08180705c0311031168a000f40800a68018a5000e8402c1c1890411000c070750070000412901c0b61001c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 169248354 1250 169247104 169247131
    0x80f0604022101030606090615140304060b060d0e060903070305070605060109080d030516030915110409020d0912081b071b1806090203010b090904050a12080f0601090f1e170d02061509 81
    0x101d04dc80c001800e82c0400140c1d02c007500281000d8048aa0f40c060b1918011841c11180035640f030410fa25528802c03004c003d008224180300c100009162600107613840750040c03500c00581580c4d10003582c40c200c40e158201012a1f110001c0200d0209034480c02220004c507841c080c010b010719903e03805005030704001491062521600a1114429500111002041c125408550703030250b40998100600009204465000c0b9002054840501ca020030700e00134046000a030041400f01042440c40cad500c120012a48200303180c04d08162004000d2900000b00fa03055103213a01e00407410042d0040b034006800c00c0031014410310041c0680340d04801683c680c0e00d000d43d0a204252034900f031032413411b001040c0007006840c0c602074400300070340d01041c01402102582d0322110740e43c441c1001901c11070018084d00e1b03100030701d0749010010a925506200840602602070701d065a40b0707a0454410106005403000240c2c1c80900200c1960354100800369000d90000300d030401c030844100000b811648060141001c2400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 169249604 1250 169248354 169248361
    0x140a0915031508010204080c060f0a050304050c0409030c020f03060f2202130c080109050402010c020105180a0602030406020d03060806131a070e0405010501080f06040221010306060906151403 84
    0x354890340104200c520030510003a40c0f01c02040c044d44c42402441001c6c00759041292007805d01a05860080304041076080c100860880129056000100281c440e48030710350662080791528811a01c1d450b01a0751500080100d6006000007580c2e8100298003e5101c40104400105a6941250014202c01444507501440d0140064160460401951000960501d200e040c1040d62203142c2544154903014030700d82e41c420341c1800326042160080d000c1030f1785c00b505900541c80390005010b0811912884c030702250040e008101c030006030390855030159000040602010350100004805107089217070902102c3e003842511a11400d01804149064041110f43e030308200d070300c040c03140e60700c00034201d04030303081c41d2041008040c0440e0050044c040c1c0d29000020455501c50300d42103116404c0b00c00d405481d070b1030b0740003404001c2d0312a0242c07169820f80000717612051108404040d00840c0038000c00720b074141c14154408101d66150b80f101c0300c1581202000c00d1019003050261007810b00c05030209490b0359 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 169250854 1250 169249604 169249607
    0xb06040906090605090c04060804030c080d0903020c0306161d06120c03011415121504060308190c020306070f17091501060203041d04050a05010e0d140a0915 69
    0x1440c0c12000c030503428401c000c07500320302c40c3d0b01031403c40794101ca040c90203484002c41c91040b44218014000000c11140004002c20702512120421520820007245004000c9282c00101c4900900c100c5c01a00a501c42b10200c2c03604200007074001c01c0101c1c046640e00c91075080a403407208a0f002e9074071001c0844013484110750f82c0301d00b0350700c0c03d40d14116072044524003d03186461541c02401083c5020003103841c0070015051800100c420a402d2074045403070024000b0350405403900044c0903c014502c028648600ca844900a58005610900c0c4040d16070b5956107501c11062540044801042001c10b0040c0269400040158118806041001200b043d5000c100c881010300040c032840180b0610074444c0000000509034900500c40581080c203903200c2108a03102d00ca184280000d20303641c2004c181c200e1043c0e00401e90041e2040086800c2c5040c1507a0b450b080d01e407070401601e0180c018540b0585a607421074107074084052000101d0f46020b8102c00e01900c10003d5000f62521070760f82a00c0f6903280e6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 169252104 1250 169250854 169250857
    0x91e0a021314070c030807080c030703020d0b030f2107020a0e040501020d0c0c02040c02061612060503010c0e10050c0d080a0e0604200910030b091e060a05010b0a0e01030b06 76
    0x2a0600b04840d591894900e0002d0309011508104600003204c040015801718440c400303550150300b0034501c281c074645680ca0201c01a40110440458043d0740742615200c6036070805c820080120148042d0130704501903802c2081d0155105078078076080008100303410069407204206016900c90791503200141c1c4036801d02c03500900074004914a603600d45400214a0707a000301c102c0d5007851084800b4400c1c0810040c0890301c484040c0d07000c55031000c078800302035805c1740203c008074241a0070400c00030b42543c1d1400020f09440d4070090078004a11103001200f0142000b080f0084185168185203182a0f10581f500d40d60b406244600001c00003801c02080700c0b582c280e0050282100c0c00c4048490600706070600560949108008030700c00c2030394120104003400e01c2d56500d032007600c00c108101e1100e07103161a80782e14550300400d080458000c81c1403900440081b4007a0043c0380000ba4014101885e1540c01e078411184180c1104003045401e1106064a50b446240d01c00c4110b030a02e00070820030900008220701d07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 169253354 1250 169252104 169252121
    0x603060108040c030b1302041d07150c20040c05030f0c130302060a110d090506030f07021204120303060504050105061b120c0a0b0f011d07020a0f03020105091e0a0213 73
    0x9811421050250851b51820210449402290104420308140140d6a4a1004201c80342d180e40c010a808120140a9204500503c0000d0405200c81a802d07640e81c0200b000c14004095595202003807402c85007401c1c89203840b00d01290804502d58280b44900300e00b1a00010421031100b840002c21310502c03a8522241d07001140d02400701078843d4900c1e003000d0241c21240c0421a803e100302404034041510034981e4408440c1c0140c161461030300c48070362403941607400510041c250301c80c500a2040801000004000030050600012000c010701d103801000d035072007688901e105904100042c80580e0381d01742103400c5880141910700b41c0302c650500b0706040c4544542d8000340300c02d01003805001d200000c00e9214110b481261124001d5a4126241c180310b4000c0c000d5900703003000207014403030700300b464035000b41c22111900403106012007540e10f04041c452005400c40042c1d444005020390b0040400c8507820b00c40f880c90501c9186050180040c1d65004d140b003003e4071403400f4550f0025012041d0740720045 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 169254604 1250 169253354 169253363
    0x30a0b0a05300102030118020c0c030a0506010e0a02030c03010501230a050c0717120c0114100608070914010e0103020d0e030304150902090f0405030d09030f1d0603060108040c03 78
    0x28100644003002e195592054400058910028101c2c1c40c1040c4210780c16104500414003650300d64089100094102c080d02050314032400360300302000d0380c04020701a202c2d8800c1340203000a60401e034503407004602c0900354040850060081c80208501c500071703070b2306444083c87e01075000c0d5032101e5155004881d0088a400304040056445c104a50080081c2072040c03c0b0340c2103803200345d51039556004d10041c40403029100e40003c000c11020803185001829071216110022030300f40c00007088160800303000e845442c0741304000c203000c000c42e5801500b2194050710710304022450901c0c09400102e0605407003602410004415046545a8082d5042d0341c1d01481c1d0801c200805400d0b064403541d2039001b5103041c0c44581080d048001c444805001e0071100c42d0b80a0b1520f0120748650540000414010b4800c8809000070300444806c0040c0f4413070402514060303540c00c21400310511004d010180d003900e06054803111904644200d0303d90104882d000700302031800c2d0f24560b40300e08200c40b140ba02d0340c10040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 169255854 1250 169254604 169254619
    0x6080603032802010c090302090103060216080309010b0a1d0103151404140705060a051219050f06190f0b031f06020304051e090f04150f0608070807030305030a0b0a05 73
    0x2e01c680c0114100700406900c0d40c0007088040d00480059441c2e000f6844000d60144400d0014000100075030050194092000046180071120741d1b6000000d07001200c0341c8015a43d14061200b10f80340208980005115410501c01c0c8240e1541c0c58182e11707041400050450b80c02c402002c1c4181103903030b00c0410750340e105002420300c500700382c500041100c0c000070701480030b0311403c0400309641c40c10200300c030055106511038600c0c0500d40080302d0744020005151030455048030740c1c50303440c40c000c60180354452151042214000c3c50302d081045a04003001c503081d00800040c01080c00044020f044450503152040c5035962240d42d100d03850a0030100300f095140c4d0a4201c10030002c0e40540000142081e41d10407101e00c01940c042200c4a911004100c1e4001d900000c5080840d00050041440541050042c8000301c4c210308a1403100055460310420516181c3c0c0c0d8240c02c100d07a04040c0320030360203081000040e200d1145140c40040941c04041c0120322202d40d14944000070390b0710303203451100400018181c0d5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 169257104 1250 169255854 169255897
    0xc030519090906090e0601170a0c0306050a0f060506070204020714120a1e200114010b0913020f09091306140a0507032a030609060807080d020a0209010608060303 71
    0x8000000c10311550b50001d0601c0000304000300140101081407003c07000034030051303203844010901200402c030b144109004611140c0c02260705900f005e006140a80c801060034248510510110365044921400483c64028180220f94070360040f030b0840364040764096210744050800142c1030301c4820000d034580c420f02544454031142c800203000c0c0c541840e164454a065a036078550b00362500809400d0007d01c81483c02e404c002107014040220030484e000008190280904485500e80c0a810481c41004041518025860980030034603030740811010550800c00c1c00b000c20a5a8001e517441c040c454481c900000303021420000e090410940c00c8082400880c0d80d00002a002900a4440f0100c4c0b504040010303d0943c0030740510301c28208005101d1200444252500348881d0501e0703402020075440c0d0400145642440c080d400142098402130070b0010300d40301e4201d213425041d041340b9040d500107114a50140e5109000141190060b0403e04250741d104c8001a0941c8926480c04440340606000d1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 169258354 1250 169257104 169257107
    0xb060c0706080702060108120406030c0513031115070b0105040506130f050106030506061e03130c090b030c010c08071e0b070906090503072108040302100210110909070c030519 77
    0x180b502411264003900c4030750740c0b183c8243c5c0d1144084540d030a9898020481084014800d500994060702c9130301e031850821104024000b045040c0c2d40c000d0310007419450354242585482002c8076a215480700d00c0714030f8002690740c2c00c00e4180703051103420b100300d07560400200940c840b4481d00c1d49401c81002d04000304000c04082000824080c041d000c0007903d440002100d5003800d600b00c5090b806921070308540141084164551644001e05c25140c006011004000059070304c602c10015091949010511146080c01d05182c40b4441003001c0c10840300e1451b200100f040b1100b00c42004e5004a022503440c8140c1c4c04501081010314401000401000f00704880c6561103041d01c82a00c0b01ca98418a5065032807041596401c814091076401e007962490040d0102c80000207805098410070b0801d0a00d039030380d000661454004450040940c100d4502001d40440717901c60244e2120820000714241aa8030700407482c4440018003c009014050150034141400f030000d032006d0101035144d181030400079840 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 169259604 1250 169258354 169258367
    0xd11030106080907050603090a0609170f07050c0406051305040206040b070f03031b020316020d081207090503031e0a030e010f020903010f0c0c0b040314040b04061107050f040b060c0706 81
    0x1000e81c80f40c0110400803400d03243ca8000c40f4012540103000340040c00383c91b207885004145c4c502003103480e0440e92500078141c00c080340c080c045031601c40065603203821160925074244142070f458240706910300740c000c0c0314030f64403c0d00101070040803020002d4903541e02c0c0301050017481190001240a4000320b0500c041011080442580c14465a41801948002c0418000310b0254101c81070260f00144060384204044801c00c00d20b05000a0000317010f8922900c483c0c203039511016801d043d01181c071080000140d000300c22440100010340013140b0302042e0b02c51881207001038415420840c2c8001a00044592083d080101070b000710304020400f80c40c1d6104200000d40c0301101140c06942846000e003c1d0400c584100a98194688c50781100c42c61250346503809100024811002c2c4144800c820076007652001c007070005080c0386100c165849082c000081c1c658100a001c0d49050b511281003400b4546652840f00d02015094034040348024420000940c18001c1c0d041960092194541c0001c41039444203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 169260854 1250 169259604 169259611
    0x31506050316091404020906040207030302040e0901050108072111030a020a0e070207050901030b0f0c070501020a030501050f030303070f031a09161704120c030309021c140c030a06020d1103010608 86
    0x80c01044101e009100758000b0003405c0320042e40c040300300c8000035440c3c02c1c55002015842d100e490b00524158840801208004003901d03010190303903441d401400420801c0041101900203014030366204a02c1c03a600900070f000d03818005104010840407440ca0340c900b00300414146500504c03589010f03458498a00c1401e1080b585080103204842c4005514202407001d241a20340014a804059856101c2d080d078030007018101e03180f000701c01c00c00b00c4049031080c40680020440782d640800d00d549400100106580000c28440c0b10b50010400e202e142178201c906000841054203002c036904d592802480e01096041d0102600050030000b0002c049180c11824031840040d5212202103042011400c86100002c88004000d03901c948801e580a074056445c0c081201d22924000ca030018407607020410121241c85910305d04800040944104001f03a00c0c240038200700740e0001c08100d495407001907940d6000784e0015082a5000072565460740c40c030b410a5012100900300103030359595981d0000c01d0901e088 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 169262104 1250 169260854 169260869
    0x6040f0f2907031a010e090705160501020301061e05030f090f01060602010e28060207150c020102120906150f0a0e070216120809010e04090507090213150801031506050316 75
    0x1180181644040c62102c0c00c4854180d5039000d404c040802400581f81d4050030840502030240f00010f000b900d2005200f4900c0e10940002d0380f01d51610a0141030b900d01c5030b030700c801801070390381e050340c0c010344d002c0162030348103020107042c0c82030307464003003580f418251341181c080155428650045600398054004100846480c0100c90001a01c0b0004130051507a130210003040020602516011500c9074002e841054014043c00c00b0050091700400c088030000030782c9030003503500440d050b8850300081c4620f41d400528039003e0602403411700c0c0003000c9410740102c1d0750b200e08c2400481c0d101e00e4444c0202a0301501c40803905855605018901950740e00010003402c204030701c0c2c407034041050001580c0f9039008950160456080450030401503522071100d810b02a0002c5d80c4622403408200c04000d88001840c0c03640c00182d9514a0035031a03e0034122a400c41d590034644914105100c0e40d201c940541103076000b0326014204182c00c14202c002d070609a20107645071180d5404d580e800840420380900300e4410 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 169263354 1250 169262104 169262111
    0x20a0321090e01030b0c0a02030c0106170105100e18010e0a03030e0d020f06060d1103060a0f06090203060a0e18061509150d030509010201140c070b0906040f0f290703 73
    0x16000b4030b4581c04000d000003044010f824002c1680c5004c0100030740300c0d8001d00c3c01901e007030600c2c184206086903030907403102a40801e4107000144104c42841000d410941030940343d60500e00b00b07100d8007605240940714500c0d50b03d0164100f003043d0000c2d071203440c143d0180c8090b5070580c05a81070050140c001c5400c1450140a030400500d29035000180303084550440002070146941c81d1010800d0340701c0c0001040c2d400d461600895005a81c080c401e15100302c140e403800081010100b03c0110403a5420782041e100c02d441001407041d141e442658000856060001d01075084c2d480d00c0902e20164443c4c0c80e140301d00d1013403100344140454000e40540b21a4801c3d1038182c80c80d0b49200e0041100d42ca2800c0640c6c21034002d0400001003440b45000700180b440c10300020a01d80644050900014412a58210240710128040003003090310881039401070300050082c080c605041d215000100c200701d034001d1000e041e464460007045004c0185d1040c0480601001002e0541d21800718150321080f035542002030716 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 169264604 1250 169263354 169263359
    0x20a020d08070c030f09030209100f05011103041e030206040b030609070f0c0209060a15081602010c170604060e01080318120c04020c0c10090603060504022104020a032109 75
    0x82007014511034010ba070345007200410b0503241a40c4070003100c208041001030300100072001d40c4030010580e0068480070010544189801100c20f00c08099170401410000b1230522403c001100100352415038400400200a1840303a00c00b4140d5042660303c0250000c401140c0000c80d01c0d4a080590711a00c01a501c4a8150f80c403080129440781d90180d0300b20118020214074400b505140900075170112002d40b1290420381c030381207034490000e1000d100e01300040c030350b0040101e2003100c0158191040340600003400880034900020784900b4540381d0008142003000c0c00201150343d2034110340c0c0140b00075800d209503561103140c02d944a5000c030354912150710804410107a1400d0040200d40e071402d014010f01340d40c4802808100295010400300601303882803e046100303030381e281c0800000754039484c1c849403002c0b441c01902070281d800d1540454411403040c80190035404501c1c0d00f407044002920301c403a070669a00d01c0042d503801c0d026040585075085003c004100c00c170103080c6003541043d0503282c6d04281503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 169265854 1250 169264604 169264607
    0x8010b0607020a0e0414011d0f030310120312050115081f05040f02040f0807080f0f03071416060306090b0604081203130803070305010f0b1e0c031c020a020d 69
    0x1007503620007504242961410000e004403801e520390058451502908079000c00c0c10a2401d441c2c51b240304503903205088440e81d08220080082d08181007084011b18150701c0c00c3c017001d00044010380f08213903400e100ca903403407802c0502c640340c00311403401004020003865031103c0200c1c6105072808042404915440c02040c0c0450310300070103409002d40e02c1d005010140c1010244009800801c41c5041c14640034040494102c0d401200c28000d4100340000745852032601c2d005914011b0002c07001d42c8103410802c580d0400075004011207024542000320480e00c41881544146880303550b4903a0340f85000102404601ca541c1900070300c04481c100c0c0b40c10b100080c07082e001c101c054440c0e4442c01040e54440112019030034a44005582d00071b242d0585442058080c0e102e0001e140c0c005c50706e04000a42d18001400103084a5640c10b02900c1700d2041c41e03040560303e5602018805072909040700b402404585540742203410001c8940d580160030403290340961500e46c14001c1d4106031054009030040040c03488019 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 169267104 1250 169265854 169265857
    0x1030e0307051209040603050f06060f0607260c0d18090e0601030609050a05060403030e19020906040f020c01090807060c020d0507080d060e0f0a14091b0d1b08010b06 73
    0x140c001d0041c02c0c91461400503c0420780c8441205900540ca80c00000003148060010854030500d601c05400c480c079084040005040729841d07114803a810500c10b1801180010524507412012014800714401c0851200e48040c007410188044a11410003484001680b24402c02d482e11101540c4905040d15031a0040545902c0c0c0340c000060b078003c02c010404113040350010080c0307034059025513441003043d0b01c032070f030070518111001c0d404281c4a500f604020042000314103d244c40b41c81518810140302d90004e210810064541840340c0e840c0c52500c40b1900d9540d0407660144440c0c0000c100240581c136265410350420007041e5a185c2c41c007000c501d8058008101600e00011560b91a843c103502a607954030250004041078440030f07558072001c1002c1084d00d03d5180114080b5549081ca440c044180c0b0080c3c4945031710b6008401da010045c0560440005000032111043c80100408544880040380d000c11540c40003409841ca03d8a24880c0d12022407030340800e980d81c1e00300034441509902c0902000b07 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 169268354 1250 169267104 169267117
    0x1101090603110f0f0f0c250501090509090c03190510050609011203120213080d020a020319051f0e0d020102041a0a0c061b030b09090303010504050702031b030901030e03 74
    0x100c0c2c1d08208403034518003007600403c82115010109801e2042c1740c0c400450f1034001392002c0a40358070100103880040b40009404441d1010800d000b4021400d00c0002400e500c52842010f00a0312048003091351404140b020201e1540c0c0602125a8a640395140c4220b180c02014140c50f9402040170107204c1980034024078bc030440000d06000c20366482d040b540d460210140c501a0104228102c452040018500044c04200340004c00050014105800799090201503a008825540000c04010045e01d0201e007020b001e040c1e11407017142d01896400d1040c1005e20752980b000742040815103041664102d41d00440305101040200c0d0354824607110140e08078840e84c0070b40703008140c0000320728a01c40003290041c402c240c102d01d400c2641aa00d580c81c2000d60360589990070803020014401c1640e55814410304100700412a990718140c00c02c41000b5860344018099035000c0c1c3e450f040081d50b66802003040303c40e0b94031401c1d0034200341c2044015a546907041248070f140003e00b42000542254400015101e1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 169269604 1250 169268354 169268381
    0xc030c0b0411013c0908070e1b03060f0f03070509040807030801050306040c0e0c09030115050f03030702010c080705011107050607170c0d05060316080102121b0a0c050a0b041101090603 81
    0x100449003400708131840700c8a81142040003294480403035212018000c600c0240145503d0b1111404c101a003504030520708642580000b00a10030084107030303124014094440402d846001003d008100401d00340714103508074580060300304050104021400004100490282d0381702441a40c0360001c040c0c0300d490584014082d5429800d043c04000f9042c500d0300d4009540144840c60660090007003420f4800c445200000b03d02141c03004c101906281640d5161250214003942ca00a034580c00608081594040901a000045441c01c1001000d5000b41c900d0110f0624868881380286010362752800f0488005001450960203100200340740d541c50b40c01411014515400c0149108480c0b00904d402880d055140c0304a01980c135807a4502c1404102409403a0000f690700c3d81c0440c03074a210b0a40c003034882d0000400a82c80e0300d1241c907a9405603800d6000700d1a0070403c1501c5414076a20301f100303822010b0310600d40780042c0404c0103070b0450300080750082270304d401e05090b588079030940488961070443d15 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 169270854 1250 169269604 169269677
    0x60f09010806070323160f0801080a061503050303010e180a020d11011404060203070b090a020105040e13061d0d0809030405100c140102040e01140a060c030c0b041101 73
    0xc4903a0700030b8011300d807605d58101da030280704108260501c140c15000d0700d10740542500320404a60803a80405401540303030780750801c01303029450804030681d10a0030a201030002580c80d03000d142568511580c00b401550032000710b1b602c95031aa50b803640703025000c0c1c0f049541440039071a241c2c298030011400b02542ca80003400c20086da14141c403200f03681590080c000d03040000880301e480280d0030020241000d0040340c0c0c0150b0701c07403000d0710300307025992409014420113600c40008100141c1c1d1100c21030b0182e81050096810710344a88801640c1c0391500303040208210b040890740c610302000810600f4004032000100d448440d003001090760105010740760000c80e500100401d01a82c201039540480c140d40c00d01d090b00601c40340e80c550300c50310404106413038856500010104400d06052131028054091800300c1d58817440c584000410500041c031546003441031000c0c0081c10315000e0514081d44c1c90700200391170881d00e01441c15490044d2131807401800f040102210700c0e006440047d0030200b19142c07807000e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 169272104 1250 169270854 169270861
    0x10903030503090c2d0a03080405190801020433090e0c0d1107060c1403010e06010c02060a02070602010513050a020d02030f031602030c060304030503190e0114060f09010806 76
    0x1c031841d5000420040e2a44200c0140000c280c50f600007503880748480c0c02000d8020460034440c1c01242c0f0801d0320309849031040600c241b000c40e4400e0101d4003101c00c1201c1141e00345941c07043c41000004160701c100125407010a0004000f041203030701e40100102825001c500c2400b1205d00005507440c08613000001d5802c18003030100254031141642c018039550310440c1000306240828050302c52554040b9019540880d01000300000e6005040505541d0308105040c001a010410200e000500c69404a603600c0030200e00e20364010312103803e415401030202076940c221120081c2d1344200c1c601c0f40400542c640400160780c65018440240c3c01d0360301c1000f5042c0c0350615005c000d20260a81001da905001e04640f41000d06d404000404445501130034600903451a801018100340761940a103000e04810010840000d030b2041c00c580c0d00010711800380c0c40040c1c075160040001c050021380c2d591030750b1030440000000d25031103480c3ca00c03501044030a000003010b030105203cfc80c03090038030400744554000400b0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 169273354 1250 169272104 169272107
    0x80f070c0f11100908070905060d060506010315031b06051c05040c050607051605180708041b06090810140601050a03020d020a0e130c1b0203150702010506030f0c01090303 75
    0xa4401c0c50040c0c07600c104855074040082c900d98482e41d42000492514142048082c0090114500400c1c804208110610708107011602079055080000c00499540d0001825070f070080d88a0a1825407a81403c0d40007912303403034200c50000c4820b08040d01c85a81c0c1d0340c0094050310074001c5a901101c1d524114003040d00c4150580c0260501500850303028495110204103601c0310030140040700d0085008020500da02e20000c4089000c035000f02d030149201501e010107010340c002603a500300c1498034000c44941d43ea41094243c00025a0384005800c5829000081e40e591005890094030841ca09840c10a42d0000c9400704481261081810105070708e03000400540c0540c000d081100c0850070058900003000315400120b80c01070303000c0341c0446c1c1864081d07080d5081809881c501480000410458090079500282c11500b60001054000140713843e21400c5440500c4000a2980e501080074440c0c1045039003c1e02038003085071041e00910443d842d203940c4400c000b0302000c9602c0c044c0c481d408500e0039501c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 169274604 1250 169273354 169273373
    0xb0609010501050d1a030609160902030403080105060a0215040b010503070503030c060f06010908010221150f0f0d0221061018050406181115070b0f0a06030203120703080f070c 77
    0x3009090082407032481c00460706c0a0180d2131144c900c003800341002201c0300841d810126011703000100720b24418004c020000b80c106c080541507074421280e0035100c01071540c0c00ca00d020351348500e2090b21402c1500780001c0068400541d4103817101142513a0344540c5680a05640c0d00075a05225100d40c0a480414507590720160082d030029018500000080d844070300c1c117426680203030078020360b500480d10610342e41d503000b0700032640042e6508400c0c401d100128001038840b8000c400d00c0c46c8103004015003d10706035903407082d4092495014000c1c1c1d41841d81b0456802301428104401d028a0003400001140c0c0ca80b610054426501ca09641c000d06039038609040c030080500030021a14a035481c01c0d201c181c0c8101c1c16406400c0c91107170196620340e4500c4414016071129007000c1081401040c055000000c41501500d40d00a410400c49a120760703c10791403070007038049548003a42600030402c1b40ca90740c01422004085040c066100c044e00c80c0c0300d107001007034034071811642040080d40c074411100001d41d8912 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 169275854 1250 169274604 169274621
    0x50a0204090203190807050606010507030e01140d110306030d050c03180d080c011e0c050d0b0604030605130642030c06050c01060b0301030308040201210c0c0b0609010501050d 77
    0x1421111a04d0001e003201d204943c030384000340da02003400304500041103030810403aa48128280f074203e04141496030090021b801040340c0c9818454000b01080c1590b08185c203440310100148424083c6074208418110564410f0303907103c0c007038000c1c2644003000500840490b200c00c00000000c6107050700320030012447c089a094410352010550041c030000c60b4404010b03103140b4a03048000101c1007880c558019000212042074000c2a080036040d1100d5a008001c0ea9080d070f194080204a03141440c2c0020f140d84915080204180d2404d41402818020840440402c520584040118000d9450311103052620003085000340010600310240210310100d5500140300003180a02034a52a07607200321181050341c11941c00a80017103180c1100d85002d01983c4005d14000c0c0311a8615412350b14014650345008001a0601c44070201d0302c036001800d003568080c4080442000c00c14040042e80041c80701044000c04d4510421300300110301580f820701c88060490310305031645490a10440d2220300586540c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 169277104 1250 169275854 169275859
    0x70b0408071b06080f011a0d02221a180d020301020d0c030506010e0d1703040215030109020301170316110402071703040b011e06140412150b0409050a02040902 70
    0x107100020010742c1e08484400c055140d80903000045080c010002e2003100c0c014041c40d1043d8013680100020000b4503290308500008203941560381e03031151b41c040c0c040d218410b02d10700d0800452003040b00241d0714141d00300c2034819090400501a00f0341c020184507000b0704a0b40b803040f6148450341502481c100e407281450a1004d0005402e00c5c40d00028082240c07000da5840001c2038580081211075a440701000d580e62070100c401d4207190405844642c600d10300b400300300d901204004041760956a8541c2d802d25682d8405210aa44c3e684500b55a0041d400a105994040e509008030038603101c8040306494244980784030000e0b02d0240c3e07403621404403e4840d5841d4100340e080002c8000b18946180c4c8808001500c003085640341041c1c81c00e8205010160700c210101c20703148111081c0400c01c845400e00b01d503a2460030f04011245580396002e01e215540c071000384103502139040810005421003004140303440d4a41000007203060020301091b64801c800051064014500c20740042c9803c4e4402900140003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 169278354 1250 169277104 169277107
    0x307090b09040f1d1c02071406040b0a0315090204050603240402040e04020306060a05100e031f20131205070506040605031609030b0402090405121318060b070b0408 72
    0xb2038600440e20311102c500340180043e10000d0303200303130201704000102403501c03155900b00303100c0c4500035221007031409002e88024400f50031000329911501074a020b03094080403550307030f005c2c6210007030018940807081841e103010381c03500011001030030301c250341c22200c0103031481e40380d030f55011814002c065815883c0d110401d00b560300c0c0c55103a02c903480a4000b50200c070105550500340703401058507042000380014820105c0500601503512001110185d07441281044681e60300c0e0000001d007484441d40c1c68034120f1000d04d1403412481c0494005a000880d801003452100002d29a0f600c840d100e00c0c407501903030400950081028903044485085000e004605a07501c490f21140000d46542c0603512080019101009101800030103880b2242d11420b14140001c8a40c650b96078084540d0b401000a03119498040019080c4201446010380e46075210301d940b6076410305164560300050301030150052180c0410b80c21107801c0e42ea440754205807903040c0615401d00300320b40d40b0401e60460090084488110 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 169279604 1250 169278354 169278371
    0xa030606060f201e0c130b090a050702030f0706090f08070c080c030c040518010903201906090203070801020d140a09350d0203100b0307090b0904 64
    0xe10490018007125924050500038410b0000c101d10340511003400c995a00303032034841c440310001070b20b60b0455004114000c0b62002d040d01e1182041180003005400801c0700d9034080001c0d4240c1c0c015011044210350b45100d40c2c5070000b00340101d0b41c045601c200075a0082040394241c07004500079080b280c0c0302c0c00b03002c00c600c0302995440d08c1c400c070215800c4030503c0740410700ba420072219000c104064403040000304601e01100002a80c0c400008992034000c0e55102301040d41c002c1d607201170540c4424031000074407006d0001c0c0f6008005c050b40204862402d01040d090888911020880115852035000c410310348808549400d401020054002c0740d0520a0200009010f00b080c006041e9116400000243c15094000c22403407681d4000c0c0200102e62800d400e034000105201040a004200d40200c84220443c0900088400120500d400e40003180440c081480c1e149640044d0310815800f51507008899039442c00700e0180c0400d4480314081001d00070103100c0c01461002500341d1082c000e001103004032 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 169280854 1250 169279604 169279613
    0xe0903090d022407060c020f1f020307090314100c0f080c0a02031c0b010e150a0c020f040f0207020406051c06051b0301030302100c0f0c0b06030307060227030a0b010608060a03 77
    0x2406001308488854a400e000303030f5007a40510040d9101030f04d01001d4441d0b10004449ca102100d046104030780055400300110b0380030352041070f110001d95401103d40803800302004100d03a80b1a00700101c20422401d00102407981ca20501d9150200320441e2602c251030f07101c12513003911942100301881c04500c404e00442800d00d040350b184104012980e030000808461800c001404103c45480050040c1c103074007800c0d0aa0700d030705000c40c0c0c00340e9a2441c100780010700740d20008618a8000c100300742d001d400c10750302500342180365000703101403813003110708000d442d5940051040c1500c0b94000c032101031155640240100d00340350003081d40041400000d52034003600480607090b40d0820781083d0300507488003440f492680c41c284a17060000f981800c0598551117091002002c04800e40b10007089500303c0d00104400b91030800c00d46038047d17032280007036454480c2e0240001c4400d0344550f01fa9045c0400f10609055400d0114010045030742098500041d60b082c44030030742e00640090045508003100040c00000314 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 169282104 1250 169280854 169280857
    0x120c09061b0601090507050a18030b0108031b0a021810080601030305070302010c0305100603021c0507051905040b090103020c211c050903070f03020a0c0902040e0903090d0224 77
    0x505031030801c04400c0003122405140450580083d10700e2441e141c01e006a1907001404d44030010030074a01242c4540c0840000c0000028550004042c0f08252002181282010000c0c120901c42206110f08000180380d200f5a00c4280da81d0180d040905029611070035030358a0030742171303000c80c101d04003103c00da41d070350501881d0540c03d034010780c0018004100d12040542c28040d684503605940380601c542d007410035150b80703510014841c800c00d04d540085d1850301c209030082e83d54054410070b04200f01d6403a100002a099904c070440d0f129a03505d1706d104000b015070080080c1c0f41942e17201900a8242020140190020343c0440d20b18192841801d911076190f100e00701d050b4210b48130301e906960b101c0d13607030f0000811010b100c000d402400e14182000c1180e180c800100399181c0c42d40158449009a54600b01a41001c0c00c240002d0040504018041100496500103100321486404252081d0f80c1e846e06058032030003050380705948004c2d1400300c04098a0702e4907210301071461746180502c8001c117031100720307846 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 169283354 1250 169282104 169282117
    0xe150304060506040b190506130308040f050f011107260109050d0f0309020d020d06060f09060302011b030c0b091c09030b060a030c1e050d05010504021e06120c0906 72
    0x1e50b1544104907090605004000a144064517001980d00c1e0f0800c80c0350300c603002c902401f401450042103440d40b010300d4a2441c0015034006011035a1247c480d10110604035503806100d000b40075429041e20154441d100604840c100200a401540d00300302d040c40402c00c0d00d400c1d4800d01e0050317405a5004050078441d209000d48a000105444010f500b806020496078003070120900d8503017041c00c0090b803158100c8000d900d50445040b0714850b981e25002c070052855402000c0d506940d820089101c0141d64417210039a8002d8882c42100b034640400c14030404030709880100001c0120b5034800014208640207500800300a066411410791100c41c005001402041faa0006c2c141c1e48040003880120002c0c4c07500000306503546015981107844105060065105082d0040038001d5280014604071082c2c1001d4507000f0480c010100e418200303140a401c080c0d905920429074440385011b50107040c0c6448080c0c100c0038006909002000302c6058146000a14555100d82e04000004035a40c0e00d8006105 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 169284604 1250 169283354 169283363
    0x90317071110030f0f180b13060c02100609020f0910090302060a0905041104080319020106050a03060509060603060405121e07060207050d180504050c0c0a08030105040b03070f03030e150304 83
    0x80007080c070360901301078410040c01c00185502d05103c40801e00300c12880b56030320071740160000e80a42c41d00f84040d0100301c06c001006c1c0489240010f0b65564036402725104c0719541c1c1c0c0201c10b000c46034a41004900b284641c0890710028017040101280d00e0421a01c2c02d4030801e4107040045c01c0581c2c94020130504c1d4008103084001034803c00301800a443e0504c2010301c802d01648480d03041c2030601895030356070b104130010361991101c60340d1000300c0a40700b5000b04c8081d00300607103031030303955aa2841d01c14003a03c41030300d5426850145000045c51340c1400680320f48690b40210090000103401e42194800d6881800c0120b0510250381c080d010000300741d00201209442204010b030741d6440c81c01c000d07091244080b041002c011440c0f14002c91f428040340307400141c4004a40000d00342e103030f6220007107252050104c241d20314090708100d001401a44006141241c2c0300350343c10700080c28154101078032280740723006842c2192105402807000c03078814400008072420103409130840303000007040050380c1c1e003003100c040341e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 169285854 1250 169284604 169284611
    0x9030418020f0a1404270c030b010801050603190908090102060f0c07061109040504050115050604050105250203071512180b07140403051c09031707111003 68
    0x103181041004589444400108504107440ca480c0e035031180c030812035524100045001e005040d50301c0201150001e14440350005460304040c4950007892030800304200d055841c0010040328207010b400350711200f030416524180103038201307010000c0c0d03500b010b0004880040d00300414540190140b01d0100c4086c000c56403941c442801c10002840c0c820014540141e06190100307001107201d89009a81c4283d600400c0440c00a2000b070310b08070107015052803d507005003410240005d000c0190701400d6100300301c440f5480103a8455061200c184154403400e070016800b04040715000e1805810700914015168003101d8181050300028582050f030340022074505540707803001840d1504a0150b21610014060078008002c081242c403141500f10800504250341c1180000c1c5094403410007400340060701035180b0f440b2600d03403d10701d5030342150ba1404400c61180d01000b90195014031007000880f43d00c070b00c1c3c0080d014120900d0391000d400080040382c3c00e814003603024083d90741d607501c6213a4042c0240e5000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 169287104 1250 169285854 169285859
    0xc21050106060504080604060f090215090306010b0313060b040b0d120201150f090209030c0909010c03050a050603060601140d09060b01030b040e12090a030b040809120607020601060c0f0605090304 86
    0x11800c541c00c9502c401d0a20404010400240074003242c0c0903071103030300301c440021540c6007018144064003034008025400100ca007001164042204051310241d403080d0100c404982c0c803440034841a2000f90348619428071949500d400041454002c00d41c458006032002c00d01009607030201313100740e03411082100c2810a078046400ca8560902c0f410b0001c030012810341041c81d140c803151101d20640390180c1c9064a400051000450710100260808003001034407514141c5807495466001740250a841720009003007202045080000f8080e683c080c0c18020050000d0b51640001500c0c04007a03940901c0444c042407120711204a614820080c60074010140400c138613540300300040850b00c0820556100340e16120780124014000949091521a1041442d07610710204000030803101e8198030080407225194204070410400c0c201800380c6400607a0141d2941c42451916912010119078580050344920010094580f03d00c1038601c1690080b04882501c10060b00d03418296542110303a400d00e9807000804 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 169288354 1250 169287104 169287113
    0x2040305061608010f0506071b0b0c0c0102060606180d050a03020109060c08190203100f180b0114030a0207062315040e06060f0a0506030703090b0105060307020c010c0c21 75
    0x1002c6003036140006040d0304101048011141a0045078000d181c04101d11003004400b090b100c400c10500c0006035075540d55402c1c46000340d4440071307600c1c401e40603040c0300c600c25500005409005250042c08541810134820708440c80c0484d543c0c60702d5000801a17000c401044050005441141c0203600208407400300341080c82c1a20310310f418403000c201c094801c20046540051955050301a403540c0541d07607403038074231360b13048140c0c0303290400e1000406418002544407003040d80100045100c0d80c052103250552b00054420071615540030408000800c00502100b41d05d50080080e01e10a00380020610030308030040155232142000d0302c9c8021403510078040741ca180a5083c2088901c00c507403d024040c00404401d1b1600c0c40501a1405040418040401c40e520340407110050310011380340541300d1a1003000200030b0100c0000031340d04d44d0136100020130a42410001c5a00c0f4541c1d64006004044080740111148210494190b8180480620224022810f15100013461411000d10503800729103082 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 169289604 1250 169288354 169288381
    0x80309060114090a09032303040506070c0203101503080f0c01110306210c030d050a080a11040e100312020d120902150f04030803070c1a011a0f07060204030506 70
    0x5010b1182051006926035540102194448818500450382000f28038081d103007071646038100700c014516081c1030b881345024080a10b1080d0700410840318980c40320081541d02406001c0040d4054014075506d207501462038100030804000400240101d6a498481d824142c00c0303000880011400005d50340100b881c240a0007481c032012000862941c2096400191003070794840c10003080e503241100c40000c03014280000303040ca01c40641070380c501848400d0300428917480011f4090108140d20003042c0c00c0c1a440c40307004d22141c03424240383d00d481d040c80500803090b040280040e10000b884000800040c0012807811020f042a170004c183d2a01140c501030000c80725402a100c040c3d16001c0e06c200542d8815581d400c00c6110203030010b075940132140800c40148140d4001500e0a01c0c000140105182d010101019060085c9a01000010a040b00503e20102071040b01e080c142e03400022400075460300004c02c102486460032503c0c00865941e034800340c1e0099032082e2400d0300000304008000a4964 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 169290854 1250 169289604 169289609
    0xc040f0b18060109090915090c030219061d060d0606080a0b091005010f051b0c01090803031006030518060103051509060106021f02070204050910060603020f030105040e190803090601 80
    0x202044064038100700002d090b02410300c1440341c1745440700215400d01c4820361403040205006041404001204c0c100000441024401240030314040120b40080800440005054803002c1d940c601e410082c0c500351400145120748020740c400030800040c12224003030301c2000c000b0311103910703904a00e00c0c04e0700f866801c43e140d012090b8000c6c80c030003003080740180e0340882c043c081e50400d08260070806440c1e1001c40300c07409404494044148240420040e190002481a0060200f40e07a0440c3c02900e40022a84a000c03c1d594000c3c40d01c1d1600060000c08d000350001a4041e40c14034403400b2100d00d031480e0b645000020b900549582e088104541000c1d405140310b1544084050000c0030154981400250303103400070700c8a4007280503208803000e4a0400c070303011100501d0b0000c100703000508110000c5e030340300d00d4054031206207989010000501ea900034000d6440c81141c1041d101c3c20b613842c0000707101c003170b058085100308680241100a4000c2c1076049900710300c2402405543d4580c9880f0400710319045c0c068 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 169292104 1250 169290854 169290889
    0x30c0503030a050f0a03090b0f061c030509010c02150409060905100308040312030b0d120315050d02060c0f01050903040305100b0a0918050303090a0308062b050c040f0b 74
    0x20031041c0003641c0c02004407100c1d07010300c04d00b0540c0c800101c0da003100108072260005000c1504c2c0018404e00c0c20300d407000039000b920102e0b202c60383d0321042c96046a01800c0c000c40240410b4003440b045076150300908442c440c160010340140000100d2810525250b4010b4200c4101950345203810f2260380158491960710a80404200039024110380f59140d03107020b40e1000500c44444104090200c52103a041400e200401138840712182d603e52a0811070341c0340c0300c441ca000092070320a241000d200b02000c0c840448001034000e040354240d513000e101042d44030100c01842d40c4211111055012424400c4501c920340c100090750310b450a502d88107050401c90300801c0802820f01c44558406d0751080b50f003030125401440001a11150210056403007412072001809501000c001c121145802203421403440b4800d80d00c0c60b500380da03100208000c00c8901c815140001c458a1a1002008420307200c05441c14010b400310340141c0c00d580c0c000343c20790300131000481545454020101d07030b0f814071484240202411 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 169293354 1250 169292104 169292107
    0x60206060a08120c0f0102070602070218010308090d020402071b030210030932070801060501140f220e01060c0c0e06030a1e0c030b1602070311130e0313030c050303 72
    0x905442c42d6441c0c040742d1141100010002d084000300718200510309048420740001d41d220800f6040c041c0c000d4100e40000e80c041c0200404044018070804080e0341030300e500c580d100e400d1152031000c1c0701c90b007842c11008036045079081004101081100c2c0312402d850740904003d60480381144144040c050040400100341030401841034005410b1201c800204c45030051071010741002d41c40c006200b0400d0201c03045150141880102e01c1c047c040d00218151602a260118040c031420203105075072040364600701d0711040510682841182400c10301044020344c0f0b4201c0d80c1c01f501d9a0110756646020383c480e2010032061401e4608011541203400f00810794080718142a18185000c40d485044c03400009001a82400501904403502001c01c0b08407600000480c0700d854903403414103060b80003605c10005545001c24a199020b20005041d029290b00596031030110b6580414402c64280c09000c0710b420319140e21040807072500030030180002070441003034160664914104904080080d801480c00390300b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 169294604 1250 169293354 169293359
    0x1080405031e04030f03080109060f1802090a08060903090f0906030c010c03140c010b15030412050d062301200c09090c09010303110606010c020120100c02010204060206060a 76
    0x303020041d100d2400380741c8009245076400040304010b0f8032664200400c0c205c660709114050540c8494041d05951260704200203082e1100e61095038440c2d98490041c070401d030345001c10306404094000e4594003030060080701c5440e45a85d102410b00300c088400031169840403e0541007454001c160b1501c404065401012600b07000000c00e8546000007078003814444483e90301c400b058810180031048051342d086550300d4052191540340a050f50115103072107054503400392401035107080126409194403c490030080000d02c101a9400e800100403141d10a940d0540080c90030361112070b038210407040b032800300111040c540015002c4911444200c01d0b1026070f8080c5003a2003000580009085001c40b40564556200e03629131f854501140320140d009400341000104064200803265186003a841c02d8400b5070313688000454040c01900c001034006900003031001005001c040ea21016a8411401ea643d410701b00c50a000940355000040e800503076000408000c6598140415608000100c8000c3d41e040d2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 169295854 1250 169294604 169294613
    0x2090901060503090a06020301060c030206100b09090c090d06020702040e010b0102061306060924061707030e1c110d05030421180602070603050601030b0d030e01090308030a0b040b010804 82
    0x410500031407041c824000f0228520f054104074081d800c81c1d0000065542c0e41e150080240b14410f8120300314003500c40c590209544a0100d14640165205070398000d040a030175a00300030707250380003405c40003100804116000985d1640ba001c409040d01481e0f0160765401c00c0d03c1444200e4003402d03e0881d0b940d1400d1400300c0e5580c2e012544503007080b1010700600d0340390890704118005000c1607100d2940a403910410703580901c50a45804050b00c17401e13021030021540c1e41c000b500c00050700b10600700200001c0d40003a80c094017980c400d40c0095034007001c540030003400e1030700b40d0000a904425500030603552110070200c000304115420700110b01d45051429424541d458580c01c22041c0040044078421128035001d40f8410510501181c096101700380c4002c0d40c5000281d02c820711405050006820305000071081c0d4024000c800c801d0402070413003041d040072510100c890100250352141006107030100000407a001102441c0515500362000410380d00140401c400c490281d041c450610681000300004207 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 169297104 1250 169295854 169295869
    0x201080403081b070b060f031b01080a020f12061014030112050102070210120f0612031404090603061b0207120b04030e040207140c0307230609030a0b190209 69
    0x550505002080e034982911250442c40c0d4840c42104602c4082420418090401103246c003800081c1c98075581e00c0e071003034141f545030b05402d21014440724400902c050a944075900c0c20798002c0c8a10b0300141018500c0d00c800c9030f1507124065103500c10720240e042c00410703e441005171101c40e40da4245072881466801092607640414428034100001d18400c040910800b0340480d4411540100041180060004081d0424484802c04041d95103804143d40c2c1501c03441c803814066035440098928654500d40d0129208552011150301064090000150b003c0e480e0040c400614841c1c400801d06001500c411215800641203030f07021540024402c1284002e0414000d840c2c85e00030328444225035072804c1c140c031070007800c490480e0480e1001a2210901a9280c4200c518800c0701c82275405000e41c0c602016a91201401030f1110b10042184117032184013410880c803a02131028180908002451001038103016460400f600d4210300c80c0304010b580c2940303c2d400c80e10185024811420301072070b280400d10302d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 169298354 1250 169297104 169297111
    0x108071202030c060c060f0c030c04050904060e12121b04060518130e0d09060e04020702190303200601060c02040f0921090905041e0206070c0b12090a020108 69
    0x1055010360440066403400c0c0070341c00ca2100050301079a40c2d08207401c800355940c00e04441009004d081d0101180e40d03075a034103080324005d940841440381070606200400c20300a80c0900300710f440c160748a50401c4034260910682075001410a10280c40e480003401c6840142e60091644401d01c44602402140b00f6074002500c081d58510718200c1e40769030040c00208200c0c02c4c40440690b01c0079000800c0c4000c2c1030b49402420000740d28000380c2e048400c41130000c0ea15190b0710300541c404a106550207035410304140c0e019015060008028080351480d544040945209640003030740042e60a91200102105010f01001500c2c0034400610301c541c58004003c004c00e000a5009104d2621140c21a40f088015004408202d4004441c101b484030b02d0078160401c040d881e0913241c00316407504000690780e85140b188c680301d0343d0046c44406680c000040b03142d41c422108503040380d10240a014039804100c06112500c040c217458000b850340e510000204e81c2d05448000d003040644e07849805140b0040c4d9108414540 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 169299604 1250 169298354 169298369
    0x31803030c1b1a270318122e09080903010b0d030c0b041505130209010506090d1101052a1501031211011803050d0506010504030f0b0402010c020604060c140105010807 73
    0x2640d118081001604c0011410807180d030404841140100640030004140d8401405440340d1017070300c104140004094840045151030300410910210402c510b00da4610010318110b031040007000f0110858101d904d401e50030b4807030b41c0010440c0d20f5642030034400c00b80112011111070200d00b8442c1e0b00100224083c2d03a00502441c803100c0031030f08101c4540019416074800e22030901031403401d0100303c0c0407107082d4981030f403142c4803441c00020281854401c950034041c001d002400140d090351181c3c4440700001c140e0320304100c81044071844810040040302c1844203a030241000288104404914211859030003803080c0c0001c000400014901d044480240341071802c1c020040c80c070020082e401400c041c41410024907003010b2040c1050b901000030001080b09000400071034940400445043c021130000800e45120300780382001060001c152141c0c0316205140201c5d80800c5d641c04113109801981c070090109080180b070b5010400601c150701e80c0f401080e002000258903040615658a02e82d21540b003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 169300854 1250 169299604 169299653
    0x51507031b02090702030307140306030a0809030c10080a050115050a0f09150c0308010e092a040f02090f010e1e0109080a11030d0306030302071401031803030c1b 71
    0x895a410144007151182d070000c1c82c01c0400e01d07110300c010392603500407507070840064098103200c0540364034070702560b0103190080d0007451450129550036007590310418002e5818403545182642541d9852032200106005943c1c0240c18140031101c2000c0e1441a00403900402032040034101c800e0b4801c0a0707580e4258585050380c0480500034041d030300c1c00216000040c03d8100003000d41101500072010032143c0307210380e0f200c1c88aa80d0307401071207d8445042d96444c40c160032901024002d0003000f8061114804860000d110080a240002d81100c848051203c07140703401103907907101868120154402c0207030a09140301601000780001e0201090000c0a103481c483c251300c400c500341d1186031a080500a20000c581032500c250803c2c04d00c80c80c43c989a180310340b0a212819004501c240070340c2048990540007001c030903082042e610303201c644e8912610304141d0780d0303204110403541140c1d90b603044500a490026015000e030400a000150034059603103c005810300810010301d518940d041ca01c5aa4400b12 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 169302104 1250 169300854 169300877
    0x18060d0f0f0c08010b0109061416050f19020111010209090105120c041103061c03090902090111030d0b0901050a05090105091e0a0b031603031e1101140103060605150703 74
    0x2222044080c08050801142c0746004180401d05510095004000f40c0b203403004207940305000c4580b41034103540070032810340c00d100c0850b18014130604038840703d2140040d02c01000c01c8a860030300c0c05180055007452000494482000d5503040746180c40604007010003545001080404034041d03403410300c1590700a0703100c2501c0480c6001d0902c102d1140ca5001001884082c000b49410500c0c3d400075075203180700340f01201070003810b042c00308200c0d03410ec0d034140c80780000c072403410707803260001e4002102c024180304c92f600e0300302d202c0441400100405507400c0c40015080c40108140040c0c01f8058101c98021025440140201d54415500504481c81115060115910f007194241a00442694500c01080140500c41c0352040c2d5040071000080c1601202c06980f0000b12a02e42c020207031001501240c81c590440580c102814034100442140d070900c0503009070040c0c00982181c0c880000f10454500810040c010004a80140c00081400302c61290400c2d00301c0000014501c110b01000b000e00000c280c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 169303354 1250 169302104 169302113
    0x17030a0c300f140406150501080c1e03010e07090509090709050a02070f0c080f0a1a07110601090606090906081c0c0210030905190c05010c1401020f040518060d0f 71
    0x10062040415820b0110071820f04210100300700a4404490681c140301036605c402c3c9860300e01408490059540301d0301606c840410500a034884100d070100c4815020f500624030f00d42200841c020090010a002e0a2502101c0280500030340d4010328898069802440402da50006046060707841483c03002415890340820080240f00b941001040c10700c91580d030343c040c0b102c248941001c0711a100161200c500c68540342e5611070214840050402c1c100f0307041d8840c5002c44400265000313020342090301c0b50441c080c07034541c6041401d90101018070f07107510003800055409801d00c001805038050a0081505043c00c007920b603601800d04180e1480d0709841c0c032403101c0c0300380101440250007400d60900030f010340200601900980c0342c20395162041c84a4010341c140114941d5130710310340080183c101d040c2000011142e102483d4429981e40c00e01c0c1070341943c1e1002c04e200602040d070410602c259924501010321140740004244803c103151003404010880d21031551290741668412050103140005160 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 169304604 1250 169303354 169303361
    0x50f01031101053103030801060f08160e120c040c09080714061608071e0f060209011403010f0501020c01080106020d030f02070501090507090b0d17030c0717030a0c30 73
    0x118a44c901d1a00c01c9010406100b800d03049055902a03924202c45a0301c58400b0b444100038910b071200040c40b0320b400540d03440d017003070100e5000a94514140c10200400400594015081b0f09070715010b403c106c100030272520301803240c4058186a820040d88261404541980b160a140f10b1000d4030368000d00c68102c2130781e03064121501e4040745083c449140e030a07130030060101d4001910407100360340110742003c1490f02520a000c0314507406034101520050b80d40c1c03a10007079042a51000e0500014000c02054808001d001c1d5010b03252231169070710018604000249005800d00095042c44900c2005001407980422550300702051802c01007030384020a41004003d2050440103060341d460b080e000420001c011915504a07030303402ca820f008258001d020400c0c07145d603803500101384a80d0703110a03546d0400c90307101541c1d1000c0002d001038144100350300d8075601d1703240c004d20324142240d0000c100400d0071400e10582d04d000c610b43c903018117081600050340407100c1120203440c650322411500004960050340 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 169305854 1250 169304604 169304647
    0x1020c0d0201200a05010515030c460605210403020307150b12011802010c021201020403080714010510060c0228050a0b07020d021203090d03080901050f0103110105 72
    0x51040900d00110b446031302c41c40800030032100d950a09010420781e006c040a41700300b029004010308021520101040b81c00c81140b01c01301c1c0c0340d0604905249484040d020b003041078142040c5401911006604061840c80340f54116200b40305050004070306107401495804080c1d42c034080000d140c0d40715424241d2850007240c40040808081c1041500900e0680d001004008416500317100203220480c3e2083c280c400c600304482aa8442083d01400356114000210030b090000d840c054044015000f40390999009801c2541c1c405000565402045103845140c2584541a4001c20460404032001650040c02e031290f4420032002d1014001955a809850128a02510341c2040c545080b9034104410711068410b0511804141c0e000207003c0903480308899000ea40100100c288800355420800c42c05400f44000715a8070060204a00360f4903a80c00000086001e03807516855031420341e404500b907407c02002d840c0114174500040000540c107840e400d4480009080664039103840c143c1039102514030341c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 169307104 1250 169305854 169305887
    0x40513020f03070e1c03020318010e100216090522060b040501030615090504050319090801020c031b0c1011010e01060e0604050c19120207020315010e01060c0201020c0d0201 76
    0x18421200c0d0488050301d02c440059a07990002c40031703840d400c0b802c085140000703000b5030020041d500b81c00b50300c4261603159607014108024481028400701d00f0705a680c4c08204c1c05a400b510310a81d41000c0c08202000801d00c0c64002c0c4002d241078901055110218841046030031040c40c4541d0030050903400c0040079134005041000310351703940d04285014001118050b1a9046040c2022403c0e0a0f54010348d1321454200000f146810140a081681c42000b000c411041007a0100045a000d00038001446148101802540c44119034a040e111025001083e054240d00a2b00804210f0301c583c104038281b20302d2410454014000c0788070040c050030982c41049110752030920041002c1b80250f8640e4051a001c0e2010082961600c0c08103025100e01d51001505101c01e400c20380500340b03d41400c01100000300700240c1880b5803540480c1c64a000b09016400001c56600144030b5620f01c2c00003c1d00501d154913004c0720001c583c1d00040d403949030581c5620f00440800b416102075902440307074a60781032200c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 169308354 1250 169307104 169307107
    0x105030604150c1205090c13020a0512040c0518090d36080a050a170301030314030606070605010605280504030809030f0304080307120801050612070908030c03040305061b040513020f 80
    0x360440b5220007100c103102d84614103090512340a5240f81c4240e800d100e08644910b460a0055007000810760030040089034035000c441000708058964000002c3d0381d88a038182120740342000b82d0b28900f4664049010001c20464208452034003014508484040c02c1c1e0544ca40851000d1a0f815400411b07650802d551a22400c21000104940001d841201c80d00038482c290082c0300540488030140300138131010700061400709503148441c141e000156004140100950700c0c00b00c0556882c000d1300d400f680132700d004c20008110004218111507228003214469480d03582c00c001a11005003450040d400017808040707000c0f50410050f00d08010032580300e144501126150750380d5160042d917a5029007411140340440b02074a100e601d01440c039160503960010001818001e03035011041c220300e030017420748040000b01c80001401d2201400140f50243d2100003031561542141001d0340f4199014001c0e00c0003040400d050f0003440045c1d000c1e14150b4000310748074200c41c5048007000c0043d014010030100c180c00c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 169309604 1250 169308354 169308361
    0x7030e1c050d060e010509070807030905012306041b0509031207050309150a021902030c09270c0607020d05070f141c020f280b030f0105030604150c1205 67
    0x7044400741095661244040c4161503e5003080d4200341c0d002c3c40750030f4018040c400480c0c441c50003210166804012450001010800c9884403400d641424000c5455529a9807940c1a8000c4540c3d500340d215005075418846040c581060701400081c00521200300b00001c52aa246a9410700c0486a400032070800e180c0c980c1c3d22402c0c15901d80d0f1001000034480c030406c23407507800400381c040141c56a64105402400c0d0000c0c80d80701e5201c0c5071040410481e45401001c404280c0365445006160084142c80340c1c80b903140f142d07061070621034141d4000c43c134440d501c0310741c000c1d01594030b50084070002681526000780962a514102d4a05110390f00042e103400c01600c004034680382911046946160101d507015254051303550491071100350100302079003280d001d405400c0f0a003440303951035400d960542580d0441106c0c0e00c6210640030030355000883c4130303031000092009040541d00c465016020841c040c1c03905047c10b0f41d9440c850410a00038030304d01c40e00c8000c401c0883d8052009541e8410402e28148540d28 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 169310854 1250 169309604 169309607
    0x23030d020408010203012c0103060c090803120106080c07020a1203090b041202010207050901050904061a030d050c0c1005030f040c090e0d08071b06020c03070501090521090907030e1c 80
    0x4009000d60303545003084026001e100700c7c0318503c51001e6224140c90954507401c0d5104c1001400b5800c170200244661030780b0025002c3c5040000340061001441402e61a5060107070050a02c3d001400c8000000402e002c020056078400c8460350445040e20311410001c0000c1c82c0c05d40300506194028603240c50003090000f07c0303200503d00601064400d80c2600c061984070810040001d40a02500d504600b141c1c0c00200060003075408030082c50126940d60301021540400a807800e0880d403100f03c00210007203050a0100c1d020409050312440c1100c4a203400c10315030b10014010b001c001d003c0d80c0c815501c1d00110341840341400590002d841c0c070f03e10030b0102e54903900c0100ea64400e01510f0900003840080041c01c1603115107040c0c0700070402018260007901054840f440a900401002d0780d040c001000001d00051091040e503234041d2280e00605510a2200c003403402d00c921503d06100012005c01858010350348403902d1580c08a07407402c00064141820310b52034a006045480038040101005a840780d80c2e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 169312104 1250 169310854 169310857
    0x30907060c060e01090c030c051e0105030601020a080d1406031504030f09030f030801150221181008041b0608130f020d0302010203100b0f0f03060102031e1308010923030d0204080102 80
    0x4238000c1c0c2c400e03c142942ca00a0003011011802d0b02500b807421131031440115803048000b950024014030440354440d201c0c2d19103e01c964000d441c592100c1d5598503a03009820701051005074800001ca000d012610f19044610251a100420082c104035462800f0009240036848807400342d0341214448204500340e1401500c0948280104c1003012090303068a41d100f84002a21038407940300180c40c86404030714056100b141e41007400c0010010401a15560958071464040c41c0c41c00d003d6a561211824242040703c529443c075601c0d4140c0d0742940c401800303005d4001d49131a03080648000003e80d1098035041000b80c000c0a03543c002c1d40011b240012038141075054001c1d50080c10842c80742c500c11036458120310800e104081640e86488801d12012804008090103541c0c04001801a241317480201c0043d1203881c0c03640000f2601110010907003201444403a010007003c0c043d40c10003080007464680391040d40d0b88500320102090254080741d983c803c2000c0c401e480c6d0510300324400355140c54032a0201c4e4080d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 169313354 1250 169312104 169312109
    0x1140c06150906031e07091517060903041214030a0804030e04090c051302120412080106080f0a0e0319030608010c41120402030c06030907060c060e01090c 68
    0x4408018011903010702e40900b8403030084074014018403440d50421011504110700d0398103202c041c040c6940000d990720181c0146007400b0604640c002c2080d04102d0480d00103589403a00c4111540000104420403200104440a840100010300302c150150714092501c0b10380c102804c4082d02000c01c180030b0b00c5030000402c501a62113600e40c0580e02c00404240000c80c0c1420101410040502408224074208085034200000e030b1014050b18000e010f401031080403409650859903000045040c4c005560711200703160141c0b104d40742541241c00c10703018940186802030003044040f6512018000c1000041048a0b62030f403031450700c0d5502006584015004106034443c410140d420003041c0d02085200e2400d40d06950080da0302c81c0c00780b020388444820341424a6900c064500c14900301d0b0501c121106e805048140f1442ca03922000b032800d4818941030000c05200c1500424090042c00b50010011450901741c1700540f5100140701071500741800900040ca00d00c603155481d01c1c4030001072005182c0d4400a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 169314604 1250 169313354 169313371
    0x100606030209240f07050a0507030308040c0e0709060e01020c03011a130c08190e0303040f120c050c0d020a030204060902040f0b0c030d050c0d0e0c1203091c0201140c06 74
    0x10411100020303e080381400c86818030728080403c031118180a01d0300c040c14860f0f000b002120360608456440a103401080d81081c2e000c2034014040008110306c40341c43c84041c040084c801c119a0510f4034000e0a940028020310702880143e040c179403c05d9100300030710908814010b00070b1026803c58000080c14151146600740202e60445202021455500628000c00800d0383c6031402b666400300d006a080740c20740718110700c0a46500b458140704d0403c0000c0d45c0600d00401c1c0008a9280728589403001042010154090018000d160f5000c030720302103204070150405135400c4004004c03a10004580400680000b0b42c000c1ca007180104000407280c1c0540199040c15410029191b181d4054032118050942c1c19085a80704009499500300c65820036500000250780317250a00401031502402e50304440703a1281e80d40d200002d0202145802c41c102004084810302039840d00d08444027043d90410002c403a01419400e1020007021640700d0300d401c410a2410030301c00c0d0340340d042040b940d0340c407584141c50020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 169315854 1250 169314604 169314619
    0x32205040b030c030304030b19060e0a0c080702060703020307030b210114130602130b070b070912080301030605061f021c09050906130f020a020105160c120809100606030209 76
    0x803007500b40000d00000d18a0020010b40c1014074554079071a03010401000c14460072440c100998600d103a50080d500600b0742883c1031415480c041c2465002c03240e405544a04014003681440400c9401180751a0452090300c0d01503501d54134100181c000e00100da1101d030b00206003240a84585c0309904c03070307201a00b400380024001c0f29803503e00d50b41220b03800ea0300d5100f441480f00e075480001e490342d8018841111aa602c2c0d02000d652560002030b00e400401e0140c1e982d031409810403800540c00881d8002415118058076282400c54441d2a03803030005010050000381daa001080103545c440c010042884905140b00d20420729016000703403142601440c104040c01c90003980c440e024003030700208080d5a0081d00f501d11650715001040314440c0e50907809109a03554400741c1e080e8031002d000804001c02544c00214440c20210114000c030968100c4c0c4030200145031130401c00040c41c144142c010300c05103142c00006030b07c401301041d08041d91740c00c181012600d422030000301c064058010300340042c0700707c5990 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 169317104 1250 169315854 169315871
    0x5220608060f0a0b0102100906090c090203220f020a08070303020f0102090f0103090c03060f0b090f04021c0c090510181518020418090203060c090a05011103220504 72
    0x41d076944000e03103096407921150b10004402c09040c0e441800c0c2c04c3e405104403152810f86460020498030141000da5045845461440c28400304800305402000500303000c510b54642422110601c1350303042c0b09200d014a81511003814040d00403032000c0312680040c082c0071b481d0307a00ca11003030351a1001e10040700940120300003200320402c10f10a50300280000780c07010301110515801103009001380e8400701c2c0c080b80d031044044040744140c8105010580c64410001d0700c002c6c87e00c104066080001d05290458000204001c01601d50b403d040080010074003403080100d04900d090a24480e00c1e40000505529113010040c043c0d009490401c1141c00e4008004500b01240b0030170410b5a16119110b02c030704d520500d04200d00380800c101c804005203a6900181819142c81c5400016413130b4000c2c20400c207132500105410740c98148440c039048002d000006150850784804190f880c14580710f411306010440c0007107003410700d082c412540c41d8a4505c903402100e0841d50034081e8500320500596001301d10b0702d02c14 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 169318354 1250 169317104 169317119
    0xc040614120a020102120a0201020c010c021b0f0a030209070504080307030801031205030708070e04020d021305100504150f11060a05070207060c030e130b03030403080a170712090507052206 83
    0x50141c00b6806074081e0820000c1704180341219803044e504501159402c000c8042001000c4c030500da0703040c0d0745d94003a00507007003081d041c9a00b01041251051048d040025101100d07a41d16644030100d130390544a0241d5596000d81c00d0700d041c01580d100c1007450000085150402da8400f80c11416284640051144903c40c400704542e0360000310f13036060205d803400010507071079809003800c0c1600d28002000540b030481c1d101446e01c10398001c18640c1000c2844c0301020300c0a4504016001070755880ca1402e00e040500d0320b06040044520840700303805000741034030b80040d2548280d00d41c4117440e146008507003503802c00d42e94440081000700c40c40350060050340382c0881e82e50f11890094036080e8040d910903092402000c02c0040813400d2110910442d5174a0105812a032020b00c050001180140c0d4160740301c030314940340a07251155484901d10640c201804000840e031b082407141c1315a906022002070b00580b2450094034141080d0401039100d04030185600b004148032912020000c80707101c041c0030556036401c0c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 169319604 1250 169318354 169318363
    0xf1703010609091b0c02041d0307030804060e0102090303040e0712090807050705090709050108090312010303090e01050604050a030f020f03010f06090e030703090b07080d050a020a020c2d030c04061412 88
    0x80d5100050170380503090302604e0980c00010b0f00100680601600031405d040c45455035010050490104255000b000305101552081d01d02d0079545800a40c606504480025124451401007047d07440e401c0c00401d80443c0b082d00031301c50b00c120300901000440c0d0b850400c0091780d00b00c002c044a40340301c0c0c03400128040c18603207203031070003100541c41e90141c150030a001034860400041c40e20400b0301c428016103041500400c2014001d602903200c400303580381031070210444a0b8058203c0d9014820801041100340c032544400801c480d084590b00221000c2c030301c0000d00c65007140b0038199241d801e1081010300a2030310340c400303c120761445104000c03a01c4465107454607030040e22009404290f0744141045400c0382c0300000e103406403013603d0300f030728020749640b882d0102c074800d071503c4401e0b070340c0422140324040d0100106411400b04580e10140380d51480f020441c810100d0f00076801d5208444206007458804210303039542910700038400d01201c0d0701d50204500002954503120f105401454094020040218 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 169320854 1250 169319604 169319651
    0x90302120a080412080f13060206090601080d0503130510050601090608010503060402010e0d06060806040c06020318190803070615050d1703060d3207120f170301060909 74
    0x25a082c209442c040544500707604d04401551883c6040225400303885d003003401400c1480100406120325418424002e1038083d0050264807154441c07070050096080024000c0000309084c54415500e50b91840711000110078404014098030545810440042581d0012441100c0c20b0780c079a64155038964046403052001e01c5125019041440400e0155104814040c58240040c0c1072411441c00c0e540c4490487d91260f0200800d070708880c06000401004500d401d00600d0b862000750b052426520601849076224401a481200e81c2d50800c1f1032007440e014501c00820140303080e02e1b04c40d0007a04041c006800728004401c50900c85c2c0d00041141c5c0707054403604080d90340003100714404080804e48455a94030142800e613201404141c2040080e450300001c44001344070721101c1002540e505021714400403620b81d1110303681c000d02c2080c8a810300546482c00c07000e400444004484038035007405070504043d805800141e850010001c102a500200c1040032140030740f500300b02070020448c80400301e1100e030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 169322104 1250 169320854 169320863
    0xa120212040b0d0b090903070b0c121810090b0f060d0c060f030b040f0207060506040b1c08070503220f0609260105072609060115140307090302120a 65
    0x740002d1040d54100005018500b000c1400011194902800540019021031384109290710001d102030030400d4100c1c085820078030b01340000c0e0400c40c40700c5100c0603103a4010716a22070080840c1c00f103c1c1d51082000701505004142204011203035207170070000b2a03800200c0348602c40100410116900b0b051070582140c5081d001010700328460706003081114507036030221000d001c058841410428541e180d115481006411020050b81d80c4490320f064000d4410060100703201e0343c64070051049940300c40c50081c506504800c500d45141d09549030503640750086460160151001246c0c580502000c103c0a0a040d0241100c0a528a96903031141e105000075025010004160038403c00095040001c00d8410901510301c4140484013240c002d801c45104039030f40000110181c0183e003500d00c1890342c410075003c0354001c4289038078003c1c420342c1c2e0f00c8a0602c5500800d010081001c40d41903c100642004040c2040702c40795030b42030070000280b403080c9901090307109a6440107500100900041c1c01644250300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 169323354 1250 169322104 169322107
    0x204110c0a11090c07080d06050612040302010f09021e040e06040b0613050403050d020304081c0209010905090105150901020a1e030305160c061d010212040528020f1807020a120212 79
    0x196039401d2499042030340c0088415807180030214503542d0301006414040bc41e045080c40c0c900d00b905009094410030310300340c2e080c24581310b00030000d42caa480540707441c000c0c00c91000b0445640c0c03c000c14018000c40312064498080c18090004106490385464050001202c811403414103000c0d450088800a40d8000c0c0440c5c02046450b22003041600555031040c043c001460405242c3c4006c020420703268054031400c2e40d40080d04101540c1c100c02c000307000c0c18040d603844142d50304080128042c41c0c6107041c402224900480d052559a10800035402c0c0340342d00c96001c0701841200d41d1a59000c424000c0202e011908241c0010324001d04031138039003544a80e603030b2b500b0500300300381c0c6609008224100e0005030003581c002406c800c00009000134200b46a008005040510349410040e081c621460384138202c00350441c030903280c0d8011a0002c900300a80403107648200d0b0b080c900000701d1420074041c0c5500b91811900401000a401080c1d07891603500820421303000035a8004203d8440300a0307100581d06420 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 169324604 1250 169323354 169323367
    0x60f061005070602030708070f09061205040602090604630608030310090b03030406050c1606030c0807080c1c0e061003030e0d110d0204110c0a11090c 66
    0x4211240d2009003400c1e0a010340342041586031941664000c4440c0f40c080f900b41c0b0207108131180d00102d902010300300d502e0507494440c1070590040c40040b804085001c006c1d01c038008a070500210342d04450803940d0041240d40d079107903904c0b0b000b0102311070002c3c030045a082180c160070b003c25410500c0ca007440030015501071680d5500b840c81002d02d03a00a00004200707009a000f0421164900c102005020702000464413850304003002c100c0d20429070003821089041100c0c80303846440010a0303c050f40c03080e0415603180c0132002c00300e81c6816202e07800d10b120a400e000340024199010380c071515940226a40c1c03034400d039507500e4003070b15040402c8d00c10900048041104505a2a00040981810440c1e2801290054502600518000c02580c10040e0724184640410401d5040725030044010002e5443c00508070658490503c40b940354601e1601503e040c000c84c100310340d1103600035115045810a41c0f9102c890040210703aa0301440881228601e40c0d42020041500c1c10f13920f43c6d0f1107a40c0c00c0e03004925154 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 169325854 1250 169324604 169324609
    0x40b01050603091608070509060301020a09050105070501091a060f04060302010914030f01050c0909010801060803040b220b1e3f040510240e130f08120702060f06 71
    0x1880180843c02c64003400c0d003180c036440362600844004183d0344000f0480c1c0d03410801004003910707002d0080c40c400da20401c1312a15540d04040c2c1982140d00c00d00b4030035190611403e1060141030300401c001d120280c1c13090030780340c021003d841d914015442910b02c0c1307041906900a01c8222502404007034040b845180040241408603051210001c8000c3c00369405038002041043c00d5807070a656100c0f505802254441603810400a61030040c050017000f400418500780d9415120312590103200100d0b00000313404002c5801ca00002c2010704401410200d4956aa09040c500307500500c150301c0030407406d200d1440340350241c0c0c070540301c2035907518040803107054031140c3d03003819002c000c4980401c07043e501074034000d668a2029954822406080034100004001305c50000b1982c00b08042100c1401c2c000041c594000341851040640b00300c085900915100e20130301003102d00200b04010321440c0c085000340100314200c00500340500f18141c407041d10b07071aa0802030fa00e405040b1092150031103c07034000340381d61 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 169327104 1250 169325854 169325857
    0xb01030e060109050a02070b130632070c080c01060609050609150c010b0a090b01020106050d050a140304050a06020309030f0d1d0f1c030e1903060b060919030507060503040b010506 79
    0x85105c00518051043d6201884c06104550b0f0f410030700d0000d0706d20300500c106030003a51250804840301200310b20500425202102ca15145404014812000070b400a0f008442c5109416042140746031100c0241c2c2002d40a000d540c01000002900c00380002070070706003001501e400341c4009000a02184034038014141580008400042641d01c520201609403142082180500720a440105a001c408000a425540c0755031003176000d40104425440440c13401b01c0c01041060b48203400712800c1800c226418554055600a20303030084c4400b80008610303800200504034801c003034054500d60410004c8103a103030810306290000ac00c4801104c46001c0728004042d4417110300c000c00f43c450025107500403c1031030700c0303a85408284c0c9084244260500d500119a014021380c2140d461341c1c03200c00c03201846503031010b03444018103840e150203204441d55a8007099501144028200000c40f04c00441e848103141210b2100359901e0082c2d90b00420084e21030400c99110b690000410b401c0c0381d00e41000e12015 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 169328354 1250 169327104 169327111
    0x90c090e1005090c0108060f100c031704030c0816021c02150307050a12090b04030809011407021f200a080c0f0a0c0321050115080f010302040504030c06020a02030d0b01030e06010905 80
    0x400400c523500113003660354081010741102c681d942c1118440f0140f502404428080400900900c801e008202c002981716023050f450560001c406600e43c800c8142c480c2c04900c0c20303d8020740c0480303c9104e081041a1100d0540d200e02e00890301d092107100c4012580016102c141e40c0307400007802c100891079050b0700030070100b0748006000200064210080d1590b41000b0b000391802c9000038084024010719170001d001c8c18040b0590381166068a04222401a60300e8a09018101100ca4502c42d030b1640031080768080318641c2004640b13207407900c40d03040440c00241d00a0701c0c41808110604045041e4008003c00e6a03461080b942c00a840e110440005842d2006440011070410805c0802040c480040074800780301c10040752808200c65040000a5a500382c00d00b01d83c0c2c0400481c54204002011031a246074112501580c0c00a0181c580d8207085a5040035040090260350001824030700300c560000c02042c1442d020107003000380400c0303903004405840328040c009115a00500044c0183d0b400d44c1d120540 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 169329604 1250 169328354 169328359
    0xa0f1515020a05010e03090a080312061908070801020703110f070b0d060b070507080105010504181101031b0804110d0b042010050909011403060109050901090c090e1005090c010806 79
    0x81084040d40c680d405c1d034180c070b031140007550004550a0000e04044c41004050210b036805941468492690080492401000c41d4801d0116144440398800e00d0111100a04050000e5a040585030b01c03019000c1d5204e042c040f0005911b61100c1406070310b02040890350030b210f00c80941111458482c0d0003000790042d410710070301d0560320300e000611242c036840200242c038070400240c01d03594a0664103c3c00c44105034087c60249041100b044c1030310310000039a1201540c40078800202c510383c2c600480045c142e030001e5400c0420030144040c0104d4102410754441e074400c419180000b20401c00b400000ca400e0070000b4440e1814a0216002a05070410601d0603a4000c284c40c804006142c0020713800b90141c450390700403c0300000c01c4501410110201805000caa64141016182d01d0000c203649482c148540040c80c1d5072080172411440084d008410070790f400c820422110341e04d6045400090000e049614150700c10010340f102c0102e464010b0a1003014418003900c6203855050064441c210014a440c1c0d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 169330854 1250 169329604 169329613
    0x303010f080f192f01030501080309030a06020f07050102040f030c060215220b100e1303051615140118090c06030b0105090904050c0a0602030430020301140a0f151502 73
    0x40208403104c204200010b0307803500d0fa410a04100054100e8006800c440c4058004000115003501c00040042e03000354070420040c0e0391500c50285401a009104009256500015000600303070100c9481e001901e02030320392800820307036415090380e0300ca0041c611800700140d010300181c035007181c82e00c503540c0d01c02c9503090010b0503201d40c1e41c132032002480441e0082424003401500788215400c64030315a909c17461010040501b9a1035440180490003144041001600d407400490100507448032440b1603000e80c040280215015450036040c032100034005c8220300d001e0003071040009401805805a0180c0014955440c6400c1171000c4014103a0241d40038140030302005141040e80700c400c0c1882c4a00c0c0036201034560b20903041c081041c01c07002a8048800c55100788814004074214000100c01c1c0200c0d01c054650100f507140e5002a1500140b0300a9031651a2841001407002c0040c4880d100c0c00083d4810801d25000d0350b14041190800040c41c044110240e10078090060f01c0c980d00d24040c0307072500485 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 169332104 1250 169330854 169330883
    0x160323030910180f082e0c0309030e03010c090b03070e0603091c141c09020402070b040501060617041e05030c0a021f02030a0c0204020c0f0303010f080f19 68
    0x15000d4001c603010000103009418905002d1944a000c400982135100c80b5040f00e5141812075a90351400d619010003040d104004003400201c00000c004c0030000042043c800d0304440c02e0701034000c00401d1000d03000b0803900100c102d51450188640440c5000c2c84c0c841018044c00d014080045420060032002401000e103040b4459a40740c0d009540304142c054006d00c002a0705110900c820302052080b401071001150007254000120b0041d01d01d4030903207080d9503040c0410440c10502400118401a41203440080c1c01c606014208058602c0345010b40020700c019940c5400480d00007034061800c40300c040a42c00803500050a0115a000f052303d148100180d0280741e0300c405045601c50f190b4512035034402035101c0c0850410811200710070010f08024901410740c0d1030003948a1050141503c100b01000e5041c80c21542e99505035000c404014003140c41f00320b035103108555039a20a00480e808440030100005240200045d02c0f402d011360f0b070014002145400b29a00351004403110100d48020448680 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 169333354 1250 169332104 169332109
    0xf0f02010b0409080c070f060c0813050a170c12030a08090c18010303080a11030106030510150203090102010612170d0609050a090201080603010c0f0e150c030306031603230309 77
    0x9079203d590040030032a0b600c0a10351803040c5801079560041e0511848200208140740d000782c540d24031140c0046045d561581e004c54450740c0c080040d00650750040724440046040381c441484641851101800c542c64070380c1020400480f494100c80c0000c059004208a41c111841030014030b4120422100319000c000e861780000e1907681080f9003038403040c29160b00400a040d40000100e4100800d091b041020107409501541d40340f105000c0c0105241d22000840c60940001074907100400c2d400c080d01014400c01c5800230b46950003000c1c0079006600f030181c042000d01c05130060b41e00043c0d07c9080d02260b1781c61242080400d030060449504415039890000071600000d02410388511040080044c01d55000d00c0090300225024058500980c50f00c1c0f880c1c00e00300e8008414900c03e98490501503a10008400010241e448098415144600100e04090301c0705000020f1030052a0460668019500340102c0300d1404026200140281c9031810040203221003c211211581801809403071074684440007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 169334604 1250 169333354 169333361
    0x70818120a0320071a010e0a110c06090d031505030634030b130203090703030e0f0a0906030c06050715020702010521010608010f030201050f0901020f07080c0301110a0f0f02010b04 79
    0x114001c0302000080c480080085e11122400300104d10480c4010340d5041081801004c2401400c103102503031349110190800611106031158080ea0310212090b629003d6419911108965034490100c1e003001c51001a10781401d039442e040d100060000e0981d139650600d1184400303000c42c2408958110b016010800c2c4034060100d034117184c8580c0340814100c00a10620000048401d0384c500d40074814070a000c00084003241c00c1c0201d03605031800d411010341d410000340b1000c04415035a5032000c203c0000241c51901500038000300c0740038214481c00b440d0b880805982c42e00c1030480083c158820484c0050518005601038008175006241c01800c10201101030049041e402d520340540030480001086a40d5004c00600d01505402c03a004000c21300d540e0002c0c2241c02524201c844c600c0d0f01140304042c5901c2000816103076107002080390220355a40e9121a1a4101894024025402d0440100d104071040c0210ba0000303600b5940c0c02c40c9103850b034038111101030780703c01203904654842c0780440c1c4680d900d00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 169335854 1250 169334604 169334651
    0x32113051903050d050a0c030f03390f090e100f09020c0106080c030c0d060b0d0804140117011e0b0a02030c100501031703090f0106030b070818120a03 66
    0x2401c000d41421410168500202d180350541004020001400d10592115881c20169414101104030b914089010307405400c5154a4464040c94802c46c188800076094050342c0614000702e11b456406004242150300010205c08440450703407140041220807007a00c62141e005e401081d00c0c12016446d1102c20030703541a1680116280703a004102145290001c0c0324078802401c101d0f0003401c6421007400071a4a6919108801d4480c1e095244850305000d0940c0012900902c011705001d1035135500d252284654000d0f014000c680f12008000d0000c65005581c401150b03001c85954601c0707a803900165036641f20000c03400e001c42000c407480c006051038000d8017a110010031500510389844001e007020340780440c2081d00b030345514141401000400c8030440400d1065080304842035903590348a00340d81c504075842121209c6d41d0300e07105000051204504d08a80221b1550303071a82000e881c0c0c030668051008a183c1c007040c080d0000c0100c0e015900040004100c10842400c011454034000000c200e80300c83d061 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 169337104 1250 169335854 169335889
    0x11040507030f1a1e060c0106030305031b070206030a090602070f05061501030621050f0f071d0910021c140a0c17070516050115050f03211305 62
    0x18000b41042c20454010b0540100d408081010300740400c90005000b048500200c410440c030138561501036844450441740720b00440e0009024855485c6402029940200c80c042e18000d4582d01100c0002034490843c0d468680082100341941c6400608500a000c020000c5416503420031012000038542c4803142d201600900c003a10031450850303061806001d0510300c1c1c81c1010303e0542c00b4482888140280d02c0c94024282c0d680c4401180c1d440c100b441c1421080700e40907144952460381c44580c000003280301c2a541018078030000840d1001c82c41c2c079000c0c0c050307903040000c0e00501c507100144519980548004a2507100d0400b81000102a403000c03118061900c9108074801b03400c2164510b6140140d8003105405d150594103421700d01c007000c01c0c0d07003009040b00b0204040015645c00f0000c102c045509100d030007000800106030140c0c505218810316200e034078003c0071220100031040c40c1c00f0981d010450307104000e41e40c0c0d11400125182c02c0c2d902840781d022051103098004903a80c0c03540e010455a07000b00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 169338354 1250 169337104 169337111
    0x50c15100e1003021e01050d0e03040503060c0a14120609190903050408250e0c070602030c1c0b24070b070810050405060d060c2307150501051c1104050703 68
    0x1540140580b0908191030016174120145e28400c00e0390707112088448034424200001049010b10b10840d00354401c552205503d80305840c148915004550002e0484003100c1c0ca48004107856004003140700d0145864070084000e225000500a0030400d001c40e030f121103407055004109414241c810100c0346072078025400210042012300c0110340402c4841c0b2051b0ba00140b0030b030002c0c401503078101e41611038004e0400700d06c03588000c914200c910100782c0d1511340d40118250340703038900751036280701c5600410650442d40381881070150040c103007441203201c0d1220103000b0b032410034203059401c640c68440b144036040192007040110040360760452114090241580d0380da040f4101595a821401056000f291046203000c003405255503900013107041442c0e01c40008649144030517002c1d83c60003110918200781040700e0014018141030600141400d62285800e030880e00d6900c0500821100b00740070710303904007011040c020312204a5040c024005403090364818208401c0c1c80100701503580c207640e41d202103606e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 169339604 1250 169338354 169338359
    0x100f09020c0705090f180c0402032401090807050402070203070314070e0a050601091403240703060801020301080a0f080408010c080a0c030e1002030a0e0a140607050c15100e10 77
    0x70500c085001008100d130003048506108002a07540703076024060840041120030240160502400b58034031286000707104645900e400c50409010f92010105880001c554400559a942c014009001078441140c0100382c0c1e14188010700009510441c4140e0b8940720301c120000008113400000115101140302800100340750402c0c0604440c0003900030300c00e0303d06040420000b641c4c003052400031101c2c040a824107040000c80480d05200c0c2c03294034101403182d10355901c208c805c4100081030084036665410000103542c1e001c010300700e01003030283c610702d90400704401c00420440713079022107185d000d204442d00e032964500a090031111444d004402140c01a400c200445080e84130340c80311002d050030244050189480b1042d00c0b0b11f0144550141e8503404070101c1c0340ba040d59407228424032040411160b222486080110040b4449201401c80f4421400001d4809120300160b071425010364008011511b1007000200d08210010001701c4650b4101a00103400c456881c006409000c0707051035042e40d0b90 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 169340854 1250 169339604 169339627
    0x9020901090b07051002070c08030d0e0d0c0b1305120301090f0b0d0305090904170c0102090901080f0304060804030216090b0f03010c0c020616060c09080c0a05060a08100f0902 77
    0x2280390b48520080b160502201e00491400f05203c011070f200b019005070b4035400e9141000500055410440c02440b0120f1641e43c40025903225000008200e0110340300800c203604215042d1071500e07c006c10358403920b00456441d483d00c40c00500c10500c82c0b0240e400d104903c5000100b150030903800109080e0f1500386450b400206482810340c10501640d03880070840c15600c010f022403040c0440103020346c5181000030240005070302200300317110501c1a2141d448504158182c080e400c0b00242901c00c031080307400018281c01c00540c1124403c0814065410946020010781d00000000e109405500640000c581603502040322030018015282000651840c00b0702405521706e0b9415005000307030324049640303101507000510200c0c50350381141c0b515520304d81d03040e9419001c2c031004d000400e600c0c1880c016213002078124541c1c0d4161018007048a02c013400e030300304000c003903403007481942d0300010108040c0020f9445910025030004240f055810943d549001c0c5a420480e19841801565030203d1520f080c030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 169342104 1250 169340854 169340867
    0x91002060f0901020a1403060a05030601090f0f0213060c0c0f0f030302060a06051f02032514070b120402120a03030e0c150406030209031911010806040c0804030f1809020901 76
    0x42c1540d4021814505a000c0150003405441180c010310200400010708983c2c1d40000c1c2d070b018180103401e807401940d40314900c20280c2159081c440d201410602a080500e115100340c961060861260007009071402d034042e01c1e0098cd170801501c441e6800c00002c61001101d401040c001c0003103a41d110481455410002d003030100181c00002d805003000010051035450600e07201c031034540100180c0c03502214540c164035500c107040d042c1820588002d480e81d16040540e1040c103202d4010512220034401c0061a40c1c0c80b120580601c0c4040407080c4018010904603480039580588054030b41d028590b40300c0710f92031802d005008200c0009444646441301d142081c00200003240c002d07100303481d0170488651010760a006074000c14007010360120f044d1106a0b0204000040d03443d981c00000c08220341c03420300c8680950b4000d541030106100030049565070505110300381c220b0f4030703030380c0d034401d51f521030f07a4048a070210741c100440108212070710380c03044404035800175000070100744100507a1580c05c0e00015158 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 169343354 1250 169342104 169342111
    0xc050111010c090e0a0e01050a062105030a050d1127010309020d060c03060f06050a14031e190c1205010605040503120307120f2004080c011202091002060f 68
    0x159040c00c084803019900000c0c001c2c01d4408119101490307585c2d448034100104100000040158200b20911418465070340c88079041d2440c0041c1d24545148c122151204e040307002100910f164401c00051003050301c190098030545018044c01304074540c1d076040e400d0a40d00b1045004e501c1c000401424450720662240381101e04500382800d102c981e442e900080d4200010307010240540f9217501c61080d807148030707600c400c02a14940340e2124080303803210070040c659005082c840000c81ca40c6a4064804c04000b03007500d1041b59610b01d00304100d803c0382026800d500002c2e01d2107003141400004942114510b02030541c1c850704a40d03444103400c03080a4120140c0f841a4480350500000304000c0c09039407070103c1c0b008902c6c51403e4019a807519a14012148180c0045e41c80e002140b0b84102115440c2142e08007202c1c1e000c02e880ba110000c40140f040c0c210620407403081c403490307501000c40c08080754098070f5620406401c0d90001406d004904c404545c1c010340c04402c840058002c401000711500721900071320b41 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 169344604 1250 169343354 169343387
    0x703110a18080c030d0302030a020706110a090614070201030c170109090605010506030f160c1217063106030f0f02030d0c0804051507020d05030301060f020c0607020f06160c0501 78
    0x80c6150f224002c640c4405085448808145d000400100100501e4044035060365100c07034100513681e202a8201e02c980c1214561400184808000040e5a03104070005d9440e0145880d01a140c903a00303500550090a050080c0d9040c420580803000c000e07a603a00950303008082003040070070745007000d00d049011114140c1000384070708401e10078010001012110709038818003002c40fa80703091140c0003040c0c46441c524400204030044098045a61070360100000c0d121071103104110440d030b01c4200c2000900c0184e080c00c40c840002c0e01c415045003034542000b40110000000740000c096440762900c2190884407541900c0d8400401c1f45001103040411690750511130230304d01211000d50f143c0d510718191096110715481101014401500382c40c104007140c2c0207607170041820109044174540f03240c482c2c109210b1040400e44212101000364004104501281c40061120380713826080d50070822401c2000301080d4102400384650310120440c440e43c203580b02c1c001e901001413545031000041000040815030b12 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 169345854 1250 169344604 169344613
    0x3061d09070b130e041a010501030c0e06180d12090b04240306050405070309050705100c0b0a110703020a060b01050c150c0c071d0601020607090902030703110a1808 72
    0xd211900401c1050544803440c4001c0d07920584254041c00c07094280d0840518042d10b10140700c1000f581c98042258180c4d81000880b2682e40d41c3c005400b264581140c013004520060f0310321850345000303c010300140800710542c0d00c0001051000c00c2460014050444080d6101c048680042c1c0d000311280c0003d101c0060082d03d03040c10300520100040716201d001ca0403800d0030900c050300038060b41110010301009442013183d13181860b80140605610304095400b805000d03004107050a00900905003500291224800b441c000d90303c0ea501548003d1064602a5036042c950b048034070404000d1046030300903402003003ea4500e041242c2100d2040c00c0b0681801f01c20000c0094100d0b0200f449654100c0a02c00700c00c0079074038500005941d1051000d401c5660040a40110328034030003044000718000c2c610b841c0c11107941c0d0708005aa55281c141d81d4200480d441070410003900882d5001142e105a1528002c075410700d5006c08510560002481b58000c00c0f00d90b0001b1801c0a4644c5604004060940080 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 169347104 1250 169345854 169345861
    0x8240a0b0109030303090203100c050909060307260f0f06150a030f0f02010201140a0911090402032107020a0303050a030e010b06030c0d0b09010305030901082a1c0c03061d 75
    0x2c0c044a00c103210013030505803034018031025954180005414075040e900705005410702900010001d42c407050061380b14903000804100e003406d000410406079800329a640f0134540c98200b0b0300b080b240b400d02c080f29141c80f4403110001442024840c010120304580c00505980c204a1145000110509004c0f8092a58043c0030030101d03004900142e030044d00900c84040203001800104d01418200e050010b00315450002e002c020705c0a03030300c0203a85c5400342d0f800d0818084d124040185180d010354020398942d024541e4900340c507075503088407010700c0400f002e6146001c5c0e1943c00b00341d414030070303500560200d480481c0320f0102c550513006956643d00f510000b041400d4100000a00600014104038408100403c071040d002200d64002001035100600541d4030307680d40c2ca00681c0d00e510228840e0300103840080490506400e403149441818101c0d03500f0051007c1c011b16030b0180760014207544800250b2481c8003c00e9408a03c910700030042203030b03000b080e8203003480d0f55000412416a006410800f195080 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 169348354 1250 169347104 169347107
    0xc0302190e030307060c031503050f070504200f0c060a02031005030604020a09050a18060b10090f060c020d1a09060115081501020102040b0415120c020604110a08240a0b01 75
    0x84a56131544641c000604d01200344c400c600901401030160340d0300700701c2c1c0400700600100280c0c0a000d40e54800443d1417103038580061006a400c1d06400c1c402c01c0410740d21880c80041d03004060411804a05011810280b04a0b011442c0c00b8054802a8074240d000060004000315425180094072085d801000b69050030340c040b030107400b900c0c4100701d503090384c0340701040c0140285d0f0401c84462140c8005980d00161504068000f085520703102407243c83c051513180d200741d001c0d0104800b259690f22301911240d01d0104140c80412800400701e07445200c602c000310009543c88c0f03c22001d8488001c3c001c0726850b100c44450316124060b042010210511802075030095400026554002d510030810708001d03a150780140c0c060b0049802040b9207180c04103000c00d00d110302043d180c90480050351042c0808855403038242c02c890300346d000000182c02c0500042e0100301d1022081c1c0c552a0050302c001c080c29600c03001181401c014241a922a107004800b039000e03044040e048617000b1300101410441140441700 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 169349604 1250 169348354 169348357
    0xd170d0b0f01030e101a0d05011506020106060f11030d020403140c120d0309050f03030903190c0c090c14030c0d110408060103020d0503041a03040201030f05010f05130207060c0302190e0303 83
    0x20586502c1d0b8981b45030150311909010008044040a840c08280300e4292070003901130b003800d103100030b5a902107203030010f02c10740b050060404031911500c0d0700001d61205201182c10000d9000c1400c0c003807108101c0c0b1074440c00c903031000384003d60084062141d40c04182461074144234501c10002e1082c0541c603441c0134050710100d1200e903c9a00d41c240001c0155051078414101404010380c06207030700000c003c01c100b0400101c024516168440e1451320b21056036001030343c010040040c050010711017040144400c00ba150700c4001c082c500303814440200ca154260a071003552088850b80e01142d000701c1d000d1000316190040392a810300000f2010709060508074800d9032001d0520001c3d115010408d001c109000f03041c803c840151681c68502140400d100a43e2072003503105650483c0040e2a006000300650110301c9114140d0300910408825640b4010401260580d1844030441d60b5900b04103074400980f0b42e101f0300c40380c10350b2901e0151302c13040502c980081d8654407000c0c09003441442070b000725980e80c0100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 169350854 1250 169349604 169349623
    0x40303050c061308030a15030f0503031f0317090f040c05130603020c10050612060f01030c0816050f03030d020301030f0c050907020601050103020a170403090905100b090d170d0b0f01030e 82
    0x8000141c01f00304e150002d514181e09a002030203080302c16540700103000f00440118801c3c1e102d401c0d10701d00c0c0c1c010211a6001e504180c8405041080480501c0c0c1d07030054860b0003050341c0e002c0140003d811449a0000604446010441c1804038030300185268107101a000d0145c001e084030f040450a02003001c6400707480f1400502c02c0034645d60b90301d0014406542c8d0710705c441d814130318210407103030300c0d1511080164031460300b0f0202b0344032a8102000010802400a800074140d0401b81c40728a402d40b900c030501444082008c026945400b0a20440400711b18600c0036500070750040ca61403106541a042448041445030091030140e015502009200381e00066220b046900a10340180e031a07001020440ba00b68910f80c0e004054070a0105000c103240d8041c0004082ea030100c030040000d6103a00003009120582d40c810002c0480051184160358a80b5001c0d403046180075000c2c40904035510031001001e50f01010030103013103075654180310039982400c0440c100c4184003800c3c20410500441c0a10342d8890848 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 169352104 1250 169350854 169350871
    0x305071e0b0d0b03010609020c0a0b0907080307061d0a0302060103031407020d060e0d09050a051909060e0103030908030301050a030f060f0203070c06050a0b090103080a05040803040303050c06130803 87
    0x300a1444120318005012000301241645640c90380c44009000c000f4260000c0204d10035820188007180409207842201c01c00380303131078000b020495041c0d0b4036a9295a4028658289406004400100300c10148000c020881c0b2403440000c10a0300c51500e039844507503500c0d00b9240c035401104000300081e00007980300c0c1034070f03094180800c995540710007080082c802c80700020342003912031582008200c02d0b070f084014900d00710019a6105031581004560482182c401e00d031340209140010810f03405c08810141102c410200b140000725216040c68058508990008120304906d9004205050f40000c03840060031081000e945554500000a51840d02502001e45200c030401481c204000c0b09a0000280d0b052503c01951a0316104402600e00c1080c3d8606076051810500010928426446000400e680081c00340207103900f03546612129070080100c0d00c0501000300b00100d2000c000f0005000254030a41c0d641d5560301401e0305141c201070000d0041498201c6007060500051245010b50ba41b20300300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 169353354 1250 169352104 169352129
    0x480403121d04060e07081302130209040b04060f08070b040806160201090506010605090a1a0d05070203070516090e03030603060c0c0115121b0b0702040b0a240305070207030507 77
    0x40081c240c00d00048030340d8032a40146070400009142109400c07407449012143c0350600640e0340d001f0b00b00342022600f42c0080d4443d00c240310605080f009540644001100503000065580c2c0d0440400c4c210344aa41200c8414100d046c42000621000c008134806806101d4032582064a81040259108805890384140d251107842c1010310724802d40c0030381d8600e42c108046481e00e594541d07003e81a0362245040600074401110f000c5030343d0f4400b000041500d50891012842d01c1000342c010b6000b4107010b40070a04601041010340c001c540700b0012038171404c140619001081380340a6000703003164a0902011000c2d00107004200042e6408212140c2c0241a01071f03d0741e071040d20300b000d640101140003410007480c10000000c02c902c00b4405110038240d1056030180b45c00010174000c03090321300040c840c640c0c1c2c5404c00c00c6080010305041c0c21a0707003610801761054828a44a49101c52007003d030a407410a0310104c50300d082d2803e54140079140e04804c15001070004c160564031400c0c2ca9400c540182041d000341c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 169354604 1250 169353354 169353377
    0x62b02010e0d0303140a110d021b070b030108150112140102190305010819020306070320030f0415050601050406140d05190c030b090f48040312 63
    0x1c0300c500c00452001012101010705629028005081c220159080c4010b14400540d84440c2032042100d100c0070000250b0505158901d0000039600c545000c80450307200000c101c1000d50104004406070400c1e0750083e80769810b0030081464094a000c00307481d51b814a41c0100008100025000c0307a66401c14020000c1400209040d8064407130501d060359103141c001e15150740d055155024506942c2a14184e8082c8200c002501c02d07803900120f006941034010401141800e4003075030000c290b4011600d07803401246000c0e504981990402c550a800c64444401000100802c2001540080200140403c0309052850000340706000d58045c0b40280b20342142c9038000000d11600707545407a440243e003031180f454011408000c0c11001c0e0101061181048035a000040c001c0c002d85c03500344805070020a6642e11484000c2c0b8454020300032034045401d01203002c0d100012100155070040f05070080a20111400301d04028072240841c05422145042c4010b1002038034400d17030282c3c22003091400d17529800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 169355854 1250 169354604 169354607
    0x51312020a0827040e1504061404031205160206010611030702030708070303020709140703020702040b030a0c0f051f18081c0e190e090c0423062b0201 66
    0x8201d5a0181805401091071628040d68030f032505600356036a818003510750982400d01c4195004280945555000b070305a10010143c81041c841d0f115000703520104404140c004007204444041e40c09a0004661300d42480070303181c1c0b41c09036641103080e07006111aa0604941c00030344850060141c0010001d01a140326114807082068543d025001000d80c1c0c14039035501d031105c5e40e5a55510044026000c0e5000016407820f841c8104d510901030100d160f44181c1d0b404030210003d600c83d0300100d80c05542d603172004c0030644040040303514032881142c5010710242060b4241c24902216802603129030f000c5051105907204003c80000d0581c0300d420300748403c50109149aa0a504c141c2000145105807941c06600324071213000880d0304011500d44051480b9054240329100458101164071204440810031211790395034540c6502c885a1803c3d07609100d007180c000340c00d94606025042158241e4007100c104e81c8240300003260045003c4500e0800c0070b400702c91024013403990304a1b45148460303c004181c20b59 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 169357104 1250 169355854 169355863
    0x5101d010b1b070b040602010e030703020c010f031d060a060504110702041107080703020604020406120b180c06040f031a070c06020703090e09010c090501050c0304032003031c050a05131202 83
    0x102c0032074007690036098469402c061039800ca031041e0001582031026154250b44048220b691140d0550302402c104079840c001500c4504560741e9403400c0558842c1d01d180b28036011004600c000a00744054240b908007158040140d500c0d03604400d119030300e4000c00c040f03424154001c6810b119030507640495404c0c103c00d604540d43c000c00c08054000380002403070714101039001c80d070745200c4e5208030380400c4200e840d40c1c40c0b2404494074140040c40d200c440008030300d080401c1c0000040c00c020000455000960308400700d041070700250701010089050203428001c0006078411503c6d5070705402c00c118035038640030f100140704150310070000d070040c0e6000401000303140c841c0310a00050607035115806060b0501e40038440c000c0501407100703c001900451701150640c480c0c41200d0441580c440254102411500c03204500c07078034440446401c0340300c45813500041d10180044c003414030b1f51150408c0601d0400c2c01400c192200104a8030080d0301d80400c010f80108007485a100b5680c1010a032541c58806100aa140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 169358354 1250 169357104 169357147
    0x91504080d050405070603180b0c2d040302010201050109020a091208070c14041a01201906020423060406080603011401080c0102071a03010303080606120a05101d010b 73
    0x401e0300708410030090000014800701191169a010840301050744500c480d61004090020032441c0b261003c14030445040025007100c8488078501142f40e0f80c546e0302c2c0c00088a41455a50280d00041020001e40da020b111b818010191008103602c3d01d00340300b000500e1103002c0c0c082d00c04c80700d0301101c0440505c500c3c40160362050b9400f0260f40c91083c2ca038000c59282081841c0d24910840c2031981c5241103618030f5210031000003043e110b5030350180200030310018100ba1007010302c580384903180030203500a01d40e0020360515402017000503599401c000407044642c404a500744010740c944911001d090700d900049134101e034203614042c08551180800240548104510b10003d06503000021925035404100c04000c40026001c0303405030740c2d90303000f5080101541c540c1d060300c080e000e000410100307019090f000d90041004056500d841221035140c0510a41581d554002658070801c01c003e508001c00400003600c50305400e48011108680d40b0501c1400500a002d540c0c80c01088040c030f100c00020b1501607 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 169359604 1250 169358354 169358377
    0x70c090507020304031106070b0a0b040f09060f140f1617150301051b04030602030403050f03040b04020a050616060b010306050301020a120506040504120c0312020307170106020609150408 82
    0x250801c50402540c0b0b40050000b51003002c515000d100c014036140302182c0350b00350301c00002c01c420b0703440c82503030001040c69070b0021f03030007546072040c40c08501804d100e142d000c540f080c070340007032030040c04059101110a2600280401c1414500b40b040111100031a43c1e8084000c1a5402c03580c00c030b03040202c4a1400c0203640601c1c0703c0c0c20b031062081c01d40e0540d143c40c2c0b07030240540c002c110542e252440540d80c4441d48580070b6444104000030302c0460b80540085500c180281001e524201140301500c075964400c440075100410a40144000c5182451104004007821500030341008544c000000d41014840310080081d0303940c0181c1003c0b64045c0c3c00100090000400841d02c400c82e4441c040e02c1d03540001d01c414482403401c00020000d241910521b401503811070600d080025440a082e0380d81c1c01c500e142039082c451228444103209210703000075449520140d884480d0305120280801844c0410381049066400990400c0048000081c40056911500d0403010850325541004d070502e1084031800c11 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 169360854 1250 169359604 169359611
    0x9060908070b0f070f031503020306010f15020102091f02011401060f0207080f030f030a060b1605010b04050f1605070b04260a0c0605060f030718140906040206070c09 73
    0x1418041520040d0031464054a501002c555688403020030780d150403250b140100c0d06840507038000c1446075015600c1e0601114030702400340e0b1682c00003850441c0913800344009414206003400a1248030100d540005a50f000a506101d002e10005004200c80100f140c1507804040c181030865100350884068000031904050040d6102d110003410700c1c040c07921010151003503960000701c1e8440000c0800000c5100700c040e500f44001c2590080b210703400074001d901c0a50721024040380c0400440700410441d0300840c1d080d00f103030f02d00380703441c500f9501002c1040388280c0c500b104022802c0a40010564462241100300020890082c0160390500414502a00c0940c85400f088104090406040145244840a50031108455201c10080d204102100f00021028400800000c4107034220f181c015000412200c9140400c1c0c012a182004540c441c01600b150f800b42182e030400103215604007201d2581b1541c00514000d196580c0e02c880103031000b40540e1000075041d092000c0d05e0702d03080c060b00e070f088800d1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 169362104 1250 169360854 169360871
    0x2105010b0a030b07030e06060f0d03050c160302040509010b0a030204050703020c030f04030303050105030a0309061b05010e150a060b090d051603030207050f010f2001020c0f011508070513050a0906 86
    0xa00c0f44450449610000c2450285034002c104030020741d051117075400610b40e0003c203040d40c1c18015201c0e04441c040f411b1010070b11520703003e14400d01c12500c1002c2c0e080c40c50b0256515600410080d20409454501d60b6450510b084d20070382c6449091000380d98040d1400314064655003402c41c001d1250760881101c40c080401c1184440302804c00610403603000356014002e0f40d07203480405455400310f0030001e02090214000b0802e160003883d00980d890301185003800c0c80022600e440b820741c0c0000c0e200810507003001c80041040c0c0c01c0340d0b1405400c004025420000b017400c1c544440d05a205024a5a21070351019420304104802000280c815901e16444858a5031341e82ca0082c2d500e00550199601c11107009106140f113520401d4100c00c241c0c4e0a5483da070b00c4070103990041100300c14080e201200c0755002c001e42103500404114044d41f00719000000900709901030360800301b401d0303580c00028542e002070004000344d079201a8025103440d91132900081c8e0351244c1200d000180501040246154249a000d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 169363354 1250 169362104 169362113
    0x60d0212030d06120210020613030c0501090222060e013f05030c070b090a0905060d020303041401080a1401030b130b0a050412080403080c0c0f100606182105010b0a03 73
    0x5240c4c514401d8500c000c1242114900341c0c2c68400c225024a18071902d4490b00000c00d118940c102200fa00840c00000d02401c590041903411500244800c6490748810000c142418244984001000b201810416550401449840783c011000c48003000781500d8014181e80426a003125000b01e01e1141c4100c0c8994a5142c4079840c0d411240400ca0180901031b800501c4503510b1088888841d0003c114141d903904001c2d404009010280c00a500007581d811481d0051318104004c0003e00100301d1901c10380002e84000500b5040c0040201102d68105a040ea4880c8048201e090540307900c202d4040c03071540c40c0310f85810318a040c010003500e820b1800c0c0600c18940001d0303110301d0107280255038aa82e0b078184a00c094a03140000ea0b40240011f0350800000c0c1e404100001a00b0003051520503030340104072580000b8986070148180c440e0060707a8100800031560008402c0d60b150b52440303d2031864030320b04090b0340107850703048141c540090400366409041250a521000c0c1d0762000a0046070b0982e141e082 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 169364604 1250 169363354 169363379
    0x304080a05100501050a0b030a0b1018120b0a110f071217040507180b03010218030601050a1406090406030b07020c040b04020405150d060f0e070215060d0212030d06 72
    0x2541c0d540148401c0c2586100c01c1e0040c0c505035030300640000440f030701d45006c40180f0307400280041e020941d509001601030340ca203c0c1c0a00070808546c2c41005030302e80c1d02c1c04010095440e9110781058080b9480b4a00000c0d031800c0802d62085047c1c0001030080c5541c4c040c05000e01c03400c0113141c9081d5001500c142000f1031900010308a805a59a40c2001d000c555000c0504960a41d0090f05a602c60305040103042030303203c08841402080307400821000c20240209081e604000404903541ca81501d1000c01402c0c00c01c54540100f1048994403201ca01d4020003128030400c402841e80645c07400540d036074058485411200045500100c03074201813030203d00007903c0e0308051019920890502099040c2491b160090300d0544a004000094001d0b06018501e4243d019050000100b80c481c0400160240c486a80c08c000b84511214480c4503c0c00a100906052030114103022121550051003101c0d00e840883e00c07010795069900344441c110341c0304194914020780f0780050b1580d04148001c0b40c11116510b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 169365854 1250 169364604 169364623
    0x3090b03040b0702060a050705070b07050d020409020403060b06070c0905130c06180b040b0f0d090210020d0f020304030309030809031e0f0c0307060e2716110d09050103020c010e030408 81
    0x1d017900d0381782d01c0303044115080e60030950b040c0001074418001040402c61007a98a40c00c58401e040c203a150108074100003060360060b80c800314501c0d9003c01c007041841031500402e00c8000003240c0b1182351101c1d42c1e80d071360301c110514011140c0882d07a07070340080c803031b5400c06625810180d041070102490640e9104000c04225030012003882b2034411040020300c0002c44403e803000c4d642140000707810001ea881d00c0f002d480c2c0010042d60300c40c42d00c404945015840e1444800503100182e4003030441101078140c05003c514000300109c04562007000f080011035481a109410f030cea1189010303a6818869000034940000d4040500c0b00c24014680c803049008005140d42d040540d0f00140c81c800c801100c200343c3c845000d0720455000c6485142c03c0452850005090420421301ca070b86030900b05618480c0b11a41c041c12104682e4850890b100881c0c03541e000701c081000300400c00c000706881010003d000b0b060550b0740c0301362418160045072110441000390090b0710360840310022a070b2101e80c0e80c1c0780d180ea0f41c5e2841c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 169367104 1250 169365854 169365857
    0x60b0603101509032315010501080c0a200c010906080c0403060903020a020a15020705010203120f0603030d020d0c08010923270d08010f0806130804080307030305160e13050403090b03040b07 83
    0x180c0f400300d11586041b031258100d6105842c0e181180e9502c4000d0b03c0340c0da00041c000010030083d4183e10018501540b412024440d80c9001001c81210240014242034601c1e00580103009032102001411444d88080303505981d800000401d04000a150581c94200f200c00c1c001e512040d41c0e0000f00d601c0c1c1ea125000024504154211042d55550341e00580e00d030710400d4a00383c0600074041c0010f44400ca001c00c507a4004d0340c090116460122030610b510104c1c0c10001d03600c6184c41e1180303c0003500c80c0d40005c48130b000d0030004d50100102d031025401e8100308509001c0e0501043e180000007540c0620702c020008111401c0c001c0442411040e40c60b803900c8101c4d103102640400ca0110000c81e90b1484030714181c040e903401e500140000c1d00c414401410ba40590501100c090100704400300d40340401384050001e841c8a03031400710307143c1018103007036009180d061443c0007002241410310006544d200c42c111106240c0a600043c0d50301c031740c14120303407844054000640851000080c80f00b0030540100040c0702c0d080700d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 169368354 1250 169367104 169367113
    0x90c040506010e010806040c14040803031501030c0f080a02040f120209160f05030c13062309011b060f02070807050c030c0f0405191503060b06031015090323 69
    0x7800015249042c18250043c000b580c00f400051440c20582e006041c03800e03103810582d4405502c05403400c220f034019000103507650404030a21411605460208000801c2400d06028801032040000c100d0100700c0469030402480350041030402d80780b58100c90103070860080e0703041e03100d440d0b40345000c040c1c0614001700c2c040c41801000030340a1000414522421100d42d0700c910011509c031104036100c0c2c001810350418544204032005001d158200340400600c050380324180078240300e070120b51140c0c543c8059400e101e0000c00081c3d81c5a07a00070321b0800f44150040126401c0381c0ca60038103c001744031004a030b08401d807001a4007420b0144150103032081d0751241080740c100301c0c2d24205140d100d210300c4000a4000f503000301c2103400352825130440e40c2d2041c02c0003505203a0b45207090100781a20000c4200c0e038240881000c0034010f000032800b82240d03506c02034860900e581400c0d004110000030610840c0c405120070074805485c0c900c00c003001c0c40110b4024990380101305481c03241c10b06c907050011842e4002d104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 169369604 1250 169368354 169368361
    0xf0a0e06160c12020f06030702010f0c030b0102060901051005060f09060304051513020904020d1505011502070902090a12020303130b0405040506090403020a021905090a0212100b16060212090c0405 86
    0xd91442035600d49601400d80000180c0c0b24046c0a40340e040604140d0565486098021034442a80300e4510001001c1d17402040d4155200000390819001400440c3d01d40d051504006007070340704072060b0040b100d05880c482d540d10f81c880400115409000c44030341d4441000400e210501a00052144e54181e450803c0d101d940c0710aa0b01241c070002c010b40007500445d260780050050724240302030340c2c100342c09200102ca0200843d51800102e4109801a50b40c4c817401a8010110a504000b022b01611146800310300d0444204005641c8000c1c62007500c0c6100c41518003041191020300a0701c0b1002d82060404101c2a00c0703a044071020b41140c0546805030346090005800ca10300b000c1401c5c01a500758020300154420740d000d200d0030080381544140040004103000a00c0d440d901d032080d00c52440303da00141c588280e03000070031742c0480217401389809400802c03060103003108000441d030803506008400b004100c3c41d8944000070340203000c03109116100380003c00ca002200401c200300e000da01100c04001a95 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 169370854 1250 169369604 169369619
    0xb030a0b06090c0903010903090602010b03030c0606100c0b01120201140a0813170d090b060a0b03071805040203090c1003051306050a09020405100603150b0f0a0e06160c 74
    0x151000006050400c00e080407030a1030504211a942004016020900d040c1840c0007003400c0d66480d071340880000e151014100411603080c0b041c003c52110840c007442c600403410034031a5903513034081d041ca481103801e42002c20000b40200b1000711001d80c072402c0401d2640e91030302c1210301607407400c82c10383c08034201e290101031903030780242110110442c0791103010341c58a840300e01c00b980046001e01160b08040d9141001501d030041c0e00070300802c00c15404045601e104906d41040340101c0900014059510070100b80000840e4000785c1780c0c4406180b0388941c10303511031601845071201c184c0c84250814400824041d040c24082828030001c0707015039141d20100900041101156000c41b200d010a0284440020020302140c010715080b1003881c8011446081c541c0016089071340aa607100400062180100111a09030040500384142c0c0b4008480161400700b03088040d201d50b80e07807211404000140c004145000348001c10740300801510345078503058600d43c9012074411402c4250741482c0206000121034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 169372104 1250 169370854 169370863
    0x18010603030504170a020411041809030509011809090b180c0a0b0901020f01020a0302030907140312030703180302030a02070e01080c01050c12030405060a050703050f06151b03040602010b03 83
    0x40c0c1d40340d96401c3c5020324004400c24211000a480150360207200d11020150b9151b00615084c0d035042110150b03035514110002200d600d602c5428907a5508100c810004650800d0584030b55039000c0c20108050182d2602903940e20800d6008550001e142c442c1403414800d201e07045600c90703400d455990a40249882c091655400d01210096002911080a2140c0d488180140c900340d801030040b11043d030000c071107060070398102400c2031002980c0441006a0880c04100100090141101c5102c00b680e640000c0780d00c9404620360a103200100101244503076100fa0700ca00121801d80300701400060807031800a480c0e61001c1405001841030620104031140103140850488100d40020030b00303132120000544541c0c100c0351140c0c440d4003485d07401e4601981824019445940704d5805058140780c6551103208036100680118201450a000c0040f1800b41c2401141c000500b00c5c1d180741804c4003070507260054410018001554106849100c0d000c2c10000003810544149400900001e018601030590300c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 169373354 1250 169372104 169372109
    0xf0a1806021b180c090301060e0a05070e0d03120b0d050102031303080709060e040c020c060c030a08070e010c061a0d0602180916050a031506081504060b0a0e0303090409030206180106 80
    0x26000b201021403450b5010a0091417a00380150010400741e41c0d030801d280c0744080c11140c4c054165102d07010840703000c0d1b001507082040f00003201e001b5001d07481d50703c0040144081c1d6a80c030407840c1d542c0c0a0300c0c80c143d0398619200000e50780300000303565a2404200c0380e006030030001d401320081607001001c11455400380900da01920300342e55502d0703040c150000802c8041c1120a00000560050b080108199128130006014040d0100003c40d52000301650080000500800c14020041445404002c0e60383c4a58201015904600c000c02c404002c034180600e10351025121030750000540468030104581900905030715401030307100102d80d2003a44240a07814100722805c0c88074600700c40030151064001c0001d40840078007458009207024a4007191800c03075a15811400c0403d040200304500704042d120b45824051007941c06000c1e45242c0390444805005922004080c005948024545601c1c10801d80700780d60801407040c0401c40c0107080c041d440300000d0700c2d1041a040c050302d200c0c42d42e00d414007544c0c04 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 169374604 1250 169373354 169373389
    0x60b090c0315040513122001110417070b03071101050a0e0c2106040807140f1b190b070b070c030e0409051e0708010605010c05030f0a1806021b 63
    0x11840501c42c2000000c01c0003d02102c00d01c00c8202c0804041020145050702c110f032680c960380c130a564a40030319140940a012105400d030f040a004a40404112044d40d0444600704060040a00044440344c1400341e190052001c0b10b10110401845690042c1044140e29001000300125103500c0042001d4400021040d4020b511146a00c0700f00d0600700d08441400e025800c420081c0d540300d544080c10220199010785559a000c80e4a9040c40034905107a40d503811408000d001801180702e0241c2c403405080f1061800281d103a982200c1c40d210541c8501c074680c00c1d8141c014101e0740781c0038030600c50f400100b000ea40040e04400000c0c0d0550103900182c0c8000e03050323181e00e031808850b01c00300409068000000c03945c9000720b0309200c0c3d0000004000c0503078809800c014000007802e040e1000c0c211034455108604102d003810710b01c1c001c244040202d07003c0b0056400550756485050034140c95455407201c030054410070700340c0f0003e0510f80c003059002c0d03074881d074041030604204004100841900b64040014 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 169375854 1250 169374604 169374631
    0x140a06080307081e0d060e06040c0e03070b0f09090115020127080310030f03030506120c01140a0309050a081909080303070309060f06170609010203070203040b090a050a03060b090c03 80
    0x20f242c240e164200a10020261165500d003040c41703000d00d03042d6811580038200034860842842a030303191900880c1070b144454034024404007078000000ea80c44480d440340c1100064005808011018260308450068a000d0a9400c103540e448084908200500c400e440041d4a010b10460907818030540007103041c641940c1900e14504070f901e6243c4207500241880d62540c5c00341000000007031003120f01c03864890098400082c07a00e40a001c0c041001c01e0685d03400304540203451400385a0ba000401d1241002e801c0e801d40340c541003540780540060203e81800340c02c43c03045507000410070400d01c2c010b00c10f000a9000d28078980e24001020307102c2018034021094a500180005010745202e9400380f41614011a800710f1550401c0401e1000c070391094000c0001014400345020456400b000f0490704015040000c500d14600014000d4490117a8001e030140b1100000c0e0224456271811000d50180400034145c112140e641e01d403010040c01101c042d28050a102c1000490010703c010a40744141085038402 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 169377104 1250 169375854 169375867
    0x50706020613080904200d0506060a050732070311150720090114010215040503190905040c110f070312050d02071406010501020f01180210030e01140a0608030708 71
    0x2500390f044001c1c9150440c1d1b0310080300000a44040c81e81480c0c040c1d07448010380e5441b070310a00906483e4014040c1e406841c0030044411165400b504070b8000c1078004110040c590300d280c400400340300c44003104941d1414800c0d003a050340b11001c5482001c980c4074070b42c404190341c0c1e98801d10244801c07200000600c01018013075a004652529503d1101c44a10b2100125000c0540c0024034407540a0300102840791284420b820b2558041001480d051403a10360200d503403520755102c030303901e200d40c1201030a443c0c02c502c0490a41c90040000c10050100108244008034049500804055a07030b20100501c1c40780e600f031610200c0010501d201038942101000b186006030a109440c598085040081703025402c100300070104038800020b07103440a030000508015450400024501405043c400c00c03964904540d680900541110705449103a050361400803010a04030160014603036201c9030000c55007400c00401d4012034405000d44507014101c81002100d8858883c2c2d81d60303000b00c1e0700090842c3d0040013007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 169378354 1250 169377104 169377113
    0x80906060616211d09061e01050d02030c190e01080115110106240504080a111203070f020a06030903050f0705010627050f0c07030e01021c020703050706020613 70
    0x8040000703019007030180758540c05126243c050048168540c001490701100980d401c41c00701404640513404940c48141400c01200082c0c19010401701000c0000e9860700ca02c51a9000700d003a00d0b0344d502c0e512000c41d12490314510003001e5074010504141c0783c03a01c121100f000c56004488981e95140181d507402040d81c03c007079000078508000301c20481402041e190443e03d0110034041d00c80a030900c1c00d0107c2d4000c080c05400e6440e0101c8025403000c0c0002031206108280740003c00d0288250454641019103001d9000f10703203582d0680c032559044d4000011180d050101081c00e840e40c5520035030300710008584c1e5070380841c00c0f241040b20040c0042c40410658070510229000380c90488e004a000040721a41c0e0015103015501e030f169007141d949000c241c1014044c28078419a075106005024180c01441d0a20481c05c0b20b10403110028107100c0c91040c24803032a48200701104113001500302190381071000c0c10010390303560450b1200302e806104544001c01c007a840030401c1c40c0904c901060100d203c1d11a03640703 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 169379604 1250 169378354 169378387
    0x60302181e04030318050307110108041509020a0509010902030601110105150111101d10020403030c1e0b2707060206060913150b2d0111010b060403030503070809060606 74
    0x141c0030141c0f21454060805c600e03c0c0c0000b00345100341c004544d28003203854942c0c0040601100207040c060740c44104004180010400012018050070000d40340700a44005505114680c00c07580c0c201c1c1007034001050a80342580203600500c3c0980741d00a486100c848141d090749c1d0100c030344140d03115500700d8010803540600c0d207001d80c40d94144203880900901004d11422204220803c1004122602000028410038044081a172295041c03e41c03906095890280071036920040c0103000a01516407078481c20444024003000c5d5510090205450515003e50401d4080c0185e0000b030313100c0303c06400c80045c080056101c044135065000743c1610340d101401c1180c61000140707411f020303085810b0405c0018400c0403441901507500c00c0000b0f4203c4440062088206882940641e840259900344030b0b0b210310b11104120a030802d00e0718005101c240e41d15507026080305c0b0011703604242c02007004020903800c94051031180a4030b9840303903041c0d590300333444036620041640c0d01600700300304210702c07000c9010511 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 169380854 1250 169379604 169379611
    0xe372006070203060f01050108010b0c0304260a03120605060909011203212304030e06090d02130212100f060e0406150c14030a0905040e150a060302181e 67
    0x3000141000c0e2160042400d000085503260302d10458100144130070341e00f10b04040e0142c03034561113040c00d020080400d85c0d40e9201d640034509049a64401e4440713000175040d00c404006c00440182c4210882a182c00f52010b195204500320050074030741c001c00d2509016081e0b540e0754200034444030304c82e40b0307280d0404040c40c2c648034194200700200261100034140700c689040581086940040c1c004107145801c3c01c0807030080c112421204104041c00003195001c3c001c904240030403942683d0381c82d02540040d902c503001c0c0500940101d20481901075100156010b01100134265181201030b07510300a40c2900602d46010f041040ca0740607a082c06882d2003a070001e10b140d0300c041c10004010f42c551201348009050080140700150042910030704010304c9040d0414400c100e84021402c3c01c8202c20042d2585845004850155036a1321202110030b0040200a00c42c00200a041d00c1c03a00b03100d18050080c020901080c1d019030500c2090100364002d100002d0b1107860b03100c82d50014405004001c02034010041e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 169382104 1250 169380854 169380859
    0x60c070b130b030907150302090607110a05040906140705070209010b0304030909050103060e0c03011a01080903040e090604030201060f2615010803071e02031207060e3720 75
    0x305070100d200703414980254060b0009070000d00080d8540711944160704400801703801010300503c800a00c1c0e49078081651400c1c0d03440081c10f02d4103e44040400c8154040d503211950041c02c0c5100c1e1818840550310118402c61a0420040e19640e951800e03605132240010094122413a5801081610320150185410620030310340003c01c075a03141d0b40ca6059070004c0e00f00b0380700c01e9030350030b0b0441d0017480411010004c13800640c000e0000880000102a8031b00e030754800175040c018008006800b01200744200d8001d862920f841110b1410300c0b40101d9540e40c0e040f036084015604e0044c000c203030a10212076850494118200c2400150f10720003580850b1510030904090070300c0b511000c4080841c9050348680030f040020011502e07924941400c114540340c3c440d02841c41c040c01c419903c0580c5022076200586c59010444c150348075130f00c0c0b81180c003c14034110700710a68000c040c0d0000d01200c0c4080400070044142c0d0320803002c402000044180b0741454807000b001600c504031030380c0c81817590040007884203000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 169383354 1250 169382104 169382137
    0xb0705070503070803060423060105071103030a1e0c0b07030905030706050702030d180503120c070f08040906060f09090c05070f060605090906040503030406021315080f06060c070b 79
    0x3266501440d607044504103c43c002d4000c000c12205003024426038144001c0c01d04c0000d04000b1036841300b101d48801400041c108140081d03220b040c0120900e0f61340300b0001c050110303544c030079400b90001c00d41c01108801c408034004c22080709400f03510601850080d140c0200856000ea01c503a607040d402404000c8086699000a00c10000803820900c501c0d44540d4082e000395981d10ba6550f5000f04a594081a103850030140040503404280c1c00411784942d05540591142c142d2101c1160340200d016241c001050501c55110b81d1080100c01400380c412140008010300009807921002e86a84070400301140001b40202d108100f070340030541129584904500b0068603100c0d064540321044445108241c8000b03440300010842e07810403981142d40585103001a05442c205070740c9164903484050405801c49402045011a1031400680c1034014601c2615035010f0700c0c1d07094400740107814125000d09007204801d00080c101e09002003214440318002e0040e0030a213050403889429a000003850311021002c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 169384604 1250 169383354 169383367
    0x60b1f1d030303070801080d020304030804090b0f060a0203040e0f01031212022a0d11030f130e070809060108010b032a04020a120c02011109060d0b030d090314070e01030b0705 77
    0x1070038001180540f8840d503d00c1d081d0342c100704800345856a00f100c41d100310741c0200000c00c0484c9408041d1130a8481981c000300303550401c5c40015400e12450051070703030300440028030300800c2c1f81c00200400c100c800a00319145141e41e038090f550490f0400748400713013200d2640381d401d091051203005214070b001c3c178038000103003031a1501c44610041446d000707401d8040c180030b440c1117074030100400043c81e10446519011281014080704941c41e8051903500a0307a088010508140b40903040c800b8501520401502842170314280400074a800019210000c1c980104800800d502c0340c18002d140c8040800340003445691417102082c0f100021006124544071610101e580c0503560754001440e8610762540c52000c02c0e12080e4900381240c0e100d00480302507a25100f405003800c4802c000707590140c2710445c0d0068950021134610b1000d0030400e181c940c0e142c0034090241d4200c0740c0110914040d24052440c494496148c03800950740d8803007900551141200030760041001030308851700b25500040c1c0d0301d8118105034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 169385854 1250 169384604 169384609
    0x330703020702210a0218010812030403020106091103060103200f07020d0b011217030708040807020612010f0f0f0513052203051207020c0d02010e030111070f060b1f1d 73
    0x150350104051281c0c100340308250942c41c06590000d0700114030701c210b90f047d51400c00c03216566141d04900010302203020000805043c000e5020710000e01da010000d00007032a4000c0040c03885e40c0100e442e1800703c5d1a00003d031468806105080c45052100d06801c3d20703141c1188a143c100f030b0410740040380d014440c6040100003a100c44030a600030108040000303130100c5980341c000c0e4407400f02c1c20070f0b151480e01841001503244d4000e00d11900640c011481903552030310381c00480e41c10b1055071590710307078a980a00001204041c3d041c0c02d404a4a061414504081e22180e100508210f00d1042951240442041d100f815665500c45134002c1900c40040031440350540186c9000f81c074901003680032980100c0c0c41d001c2c900100180750742c400c040d0b02c00b40110200140014074071107c1d542c0040d04020b03980c400001107460035880b40c000c0001c5103d175661504c0040c41e00ca400091401804ca51044c103150b0204118100246041d8036070405440c07201401c10121030495400d0808000d8001500115005a010380c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 169387104 1250 169385854 169385899
    0x14090f060c07150503090703020d031116030c120c0e060303130303050d0b090108100c090807030f02130203040206160809120c03010b0f0a06030f110408330703020702 73
    0x3607640900181481c1190752078180201008200030b2140c20003c00801d43d0300400c581c2c090300da04543c241100026414200c0d8601206e000b50000c5101d41001410b004009550300c0046902c43c0000503240c4d03490301c1815144141580008203a8501c10009101000564408561041010f0101c0c1d040603c4c2c084d86810f2440c956006402041c000035403547d03010b11500402c507030440103030741418403945484603090356000340d0501c2404090340c0b00c540364801c40c4120070780c000a20200c03049401c4240c4038145070300c052004c1c1c1e1040340308050148140d43d0040882c02501d103c2c507001000242000c05071301610380185164a0110f440000800042100741e48030f50020880d5840107000340300301030140041c1421101134415040c0302d0b20364047d59100326503900142c003054840d980b03004501c0300ba800d035480c1c0150041080301c90b11404040f5020482c26400540315548042d2101c1e00ba80300c004800f011800d40100d0860500d0403c81140080c0816000e6002040182d1010303004211f04880710f084c86040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 169388354 1250 169387104 169387117
    0x8060f06040f0e06030a110d0201030615090f08070f05010c060608100605090a050c0a1101111902060a05010f0b0f07020a0806071103090f19090c08060406060f14090f06 74
    0x310000da02c41408040800604142e21503019130040044103855100c100b0000a40803184c2c1c450100d00c044002164865009070004014002400f480304484980151108040e030080c001800c01c5c548001800200c000b1f0103800b03c900c02d02c0c0c0e07100400e05003401114101c155000c1034581b16240c0400107055031341040702000381860780e200043c14904013030810046501c080d050789069400e11080c04191455403084076070007a074a041082c1e800800c9049240503040c1ca441c900804040030aa00c503000078604c205800d105895400e485040e070b15509240c0c00c0b2002805443d20042a07081d00b80184100c0038028025140164005400d04440f6800a01546200d40000700380382c00c90401e1004064102003a154684000806141050b0325003002c140140c440b000c441d4031910040c4580310080202c0300080c03001c1e00c0000001d1090170078200303003e000600256650390049181c0180011864400c0c04411000b00c0070f03990751360000c2007207a8200802c0e00000c8030641c0c07044407119801d0301581c504004084 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 169389604 1250 169388354 169388369
    0x10303081f081b010c0209060f0301140a14010501080c040504021b0607090e07020705060f0d090b0c0712090608040605070e030f0c0a12051002220e090c030f030a08060f0604 76
    0x30404000404280740491000303d2030f0604c058804020016510300060607840b80b02514030000d2542c00e9800a40034280119940100c01700d09024401c108440390405400f405a552074905940d80e00d00045480c902c0440f800c203542402404248801e103082e40081c1012520301c000d2000b0000311034074950a181d026100c1c800841d24000c001c100c880903d04c40d10398400064000f030010586440d02166407407190301e040f001c06100015100184070102c1d0f0010a8850300101c0c1001946040c0c403e1650303940c09800207030b851070343c92030310300943c0d40c400c41c0300009039081551a0b200a80391940c4410280c10042c141d51f0601c0380b4044540e5003910104101241007403908010b000c104581740038068180025000602c40300740200f140004a00005110001605070300c400581e50760301c028009200d01482c0c20a2201e01024050002d540502d10001c0303401020240300b911000940300b010940c0d94140c05070381160641081c00600601c80c06850029482040a40b840f20301e10003440c000740c510fa000b90007414 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 169390854 1250 169389604 169389613
    0xf0f0d140402090a050c09061315050301140d0f030f0201090228090501060c0b040c0b040b0d0e060403020d0c020102031303210203070201080c0702060d0e0309041112010303081f08 79
    0x750301d0040c1c089038004e520941e0070007450030401c40e568064440c0d0400700f801a440001c6140f00031500c0c0c400f85005003150005040740002c00e41c00200160b0080c481c000300800c0040f118502460800c0a810405500603c01940100c0c142d40544e0800c800f031307510b20700395580c2d00b801002603140e0010229542e940c101c1d15403c0b11102e0758040f420700803c1c0d00700410081c9810010302290390000f404449050f0007240e5545075070750724900300705110199042000e142034080b40019081207001c02070f0020903c400804c0c070445201c606407641e140c0c2c04440150041c0d00902e00c1e9000385005002c5404114010f20503a03241103610440c41406224075442111411001c41e0240140c046002502d9a02c10891010754500307036103500002e108401c090002402000c0010b00d480440d911340045035142d0180760803d2101c1100308624540343d0b0415243c82e4040c5003041c1c0c8030b00011b10238804403070910080000c03d100c0c607401e40d2400c440b10500200f504928000c4065444203e0801140b0440105035540c01007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 169392104 1250 169390854 169390861
    0x9060912020c0117040f02090405030c030c030702090901020a09090f0207060518010506061c0b040615020f06070c0b0a0f0b030601080705030d080121061107060f0b060a02030f0f0d14 80
    0x602802210074681c2e444e81c0150305010004030302a02480307440b6011105266191690b003131003421807040c9003400c0150720001980d1414020040003038400d9600032903035501c8680d6141034031802e034400c800c8154005940f890050200304c00c1c0da131040452048003080103042c000240c2c3e9400c200d84054130348a40301c00701ea460103410b81030240142544a00103940c4a414960360070320300d0410325840355a00c110f40d6210507501e02c0b242c032130b540250018201a02c07078100080c44001c010391101c0d00b01c21003490741c1c040c1740c00040041d800740e081d0401310741d407141c01c8440340e545600e0b10000a06c3c2604040301216140d040030070243c2d504100c1c1e98007805005029040f030038034040c101441c00541c400032a0a100c0e041b80101704411984484020104890b080003195201c9880d086000b003403801715281003900003085e0f40013407241e20340c4084081e030b01181040001d003100340100a0709002d42d580e41c10043e4400c1103003001c1c4014140203003016059101c1d180e070518118209a009940560003017500c0301c2c00c0003040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 169393354 1250 169392104 169392107
    0x4020906010203090d06020c01090b010303050304110919020c0304050607080d180c030204090f0507090209270106051602060301090c0e04061a09060f0406080403020706080f0a09060912020c01 84
    0x1020340040d0240001e501d031034040004900c0c1820f505c0380180585902003183c14000100303400400300140c2c8006d51082544c0c60b841d020b41035030015201610400344040e4501d0450903c185600d01130159000080e1040b6502c000d4031020390701090007081c65010620000516885240107011513a1040641c6500c0c0e09280640000f11910001c0c8030140943e440451400301d0401c1d402581560340584011500366094102544502d6080d0f000401c1849900400540c6200315805891050800c031041000c8807480f0189006145580c0113507400741c84828010000d1a01400003405401e07201c4554903e4220140c0000b1003940090380500c1000c5d03204c66100b1011940300100c0c0e01c54170000c441c1000f2144c103040782d1010510340000400d404d050300040014266503941c0a84244895445400795a5521400000d0410400740c41c1200584100d8801291190041045910944140c81007420390741c1d43e250180054840a0400e581e800d6813840a000030030503055901e44400301680051041d40440c0c0300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 169394604 1250 169393354 169393369
    0x50c0307060608250b0708070f060506011d150a140d02030103020f18010303030b040b060d0605120a08030f0712090303140117070e09030405030a1202060705121902041203080402 78
    0x110b0040c21401c80003d13091804580b20351050300e500c1c4c40ca0640b1540759107044842071244101c0a440088012921800c0004a40085114030401ea0301c583c2241d10501366043e00307151600655601010082c64990014181000b40160888074a0268107190007000c121881d030b4000700070162000d80000042c41503091040da220f013043c0003551580480c6030400e02810701c00c0070602004041684803d01e0040b250380c2e6070041d0309000c100420f00c1d40e0310020801500c00402840c030510380560160701510321210004190000001d8000c02442e140d03030307508a0f500c0b1808000810383c6040c802c05c100c80940141c0380344035460055100b42c40014040741c184100107044d4905a203ea903c44002042c0301c882c002007c00c80a04990b01807290a250303407281c2a046003107020326044030750036114211502040c0300b03001c075031408801b2264098421507169003004480502c2840726800140c0d1200012a0103042080349440c8031448140c8014181a01c44002c05843d020240003600014601c00a100c1503282828 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 169395854 1250 169394604 169394623
    0x303050a06050a0b12090c060c060402030f0307030807030507022e0510180b040902041b030f05010f030b09100e010603060b0a120308090f0717100b06030a020a050c0307060608 77
    0x82c1c420f650140382c00040c00c068450044030f4600507074884049075031804d040110001880b4002c289130b0b119458507554682c2c401c42101c050b80300c0d110308080860070003000700c101c03045140c0680d5900c141c2d42d282c030710075405003001804481c118852015020480480d203c9503c02510030720306c541c07001d507903190030120a55a001c0c140c0d109100080c6820041c0d900350a1b061282d1001410300890000402c200081c014141080043e41042c00c1c505400c0300220010750018482c0043d4404020b4080005618000c5543c240101d003c88c40c1c1c4403105001003540e51000d543d004044070215810300070031300e680405807840300c0340c0d0121703680d16080d0a102b0083e66004001c0d0502042d41c04031886860104036031582d60b9410320103814400e288000c00c0540c04180035014680349840c044580203039507100c43c04006109010059481e0080030304080102c500f0340524402c501c0f005003a181103890700300c0704800a51003000802c1c1071020810410034000414005040b11a000d00e00000e50245807554a608102c3c401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 169397104 1250 169395854 169395859
    0x30d0903030815061c0b060406021c090506030613020706060305070f06030510090908040f030b040c051c0b0a02070b09240106020a0f02011418040b0103090f1203060b070303050a0605 80
    0x18030f00302c82e0f07111181a90907550f6144481d00d0040c0c039000114004200b0407140e6604880300240125101e50002041c024082504189104c43c03c8034500c11a0303401c600f4050958880f10800100d00d480c6004603068074045954000140f4081040d40c1d0042101c4c1c850f80201d400341c20181080040c00410203641d0020f201074282889039190020300e01e10124101c2c090a260f090b581c440031402c1c0b20302c91040d078016041600705c450f003031510313070038044a410170455044031a0125210007244604001d9a400e544c104682c1c1410804051591740f074000b060b001788150800c0380c1c00d001c2d06000c90107182e01d00b806200d800c0e01810058251030002c584040e0f0b0b030003141480c03c05081c01000f00c03d90018040c5109a00500f590101e400035100480d0795110b80742c04482c00364001305020785601d013481d82a00e0a121f04880411501c58400c0c015015298160720142c08200e2614595020034280c00000c001c403503591400041480c2c59604220042d0041001580000d6542040003038659880c4903550181804 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 169398354 1250 169397104 169397131
    0x120a0b01030b010e0603011a0c06040b19020901050a0e06130b030f18190204060e0a020a17161202071e050f01060f0501031d0f1b040204060e0d050705030d09030308 72
    0x4013008102d40d40b0043c860743d4120034440115084110150003076891600c0c400058890f036090905001c8081071054503001c00106400007514904015807080b5845400103855844c00d00b89954002e0300c0f07080c0340f1080c0391b030001010000e8440c10402c01c01800054240e82c000c00e0b407a0b0030700c2020100c408500500142c007044e1803c004000d02d0100040d0014441d9251403a2211000380c0c1c4045000f4104d0b43d408492000c0480051101c902110340141000003566541c04902e00c2c04442085601c007015601050044d009194041503184244000a86080703d954058a08410795842602c1d1000741b44019040f0b03641580700a04005091010242e80ca04100007800300754100340803c01d929105116560501d550b40b021107c0c03810400d013058107001400800d0f1086501001e070780b26100c101c40c00343d10151860701c11f41c810b101d1a280c4241c8d41901d8160340c1c1c642c0c4240c0d40700309216030581400e108ad603e0740318211000400340d0b401c103e1144080c1d01562510340441c81c40c580a49401c0020b042c0e6503801c0c05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 169399604 1250 169398354 169398377
    0x31903260115050c0304060818070b090d03020703020306072d0f0f020a0b0c04050103061a041202060d0203130606060201050f16030902120f0d110a0204090305120a0b01030b01 77
    0xe4030514641500c24420b41e54140350326185003501c4074410501001424040130030001760460304210000d2050843c20310101c00c07003440c0701e07016031074880900411401034800d01c2024500d0525020050606109004030b40e041c5490b50002854807008444185c0010034844504e0008814800e00000b8a01c540803141d01044400d1400350214001801d43e1040150a10001d000342d88204031441000c1e0708611a0303817081c10404400c02a903401402107501082c180540099003c6446020000030280c00e01e010b0700300307401d200342a42c2151010000717a90200040c409485910614401140510800960280110118940001519003d91094055914200400c0020202001d203164480c049480c0180803030301e030301000c0c0c1c014070302d25070040c0d004405d81450314141400000c520442229441c1200e16024034480129105040b54890707013101d81047d04010010308040d001111094800d0906a01b05101101081c00b00c0d902110785003e06500e80e808100d295070148200301031001c0c2031030f1600c0c6190 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 169400854 1250 169399604 169399667
    0x1103070b010e0606070f03090512030702090112060603231006030210120e0d02030306031506100309080405090403170708100e0603150717010608100e07020c031903 72
    0x104144500d600600034500050f0040c1c0d144000c40300483e6014070400308420f25030070010488e00140c0a030f2401800c0d000c8407801c0c3c844000040d540e4180d402040c250041e800c0c01a00207a0ba0395591048582d142c07200300110004031400148110700c1680c1c55440b41e503661759a551031400311000d045200913031a002c4140050385030310000c034189a0b86420110201c40e080c02070000106a003460807295800b4214540c01d01c4d40e4080002c1d40039940840c100c0310f20040344054030003020030a495241d40028500c500101c924004e400c001d207018000c0781013900306566400420341340c120460f8210f00094200303004e00810285868015040350301480c01c070304a03107000340c619407840489003c3c1d190422078100004081d5a010012020305841c1c0040d20078035810070f041c0c090718404045c40f0303008010303513034400209549100f4410540b040c0095503010310003500d407000f49844800094800001c5000d03034608101151802c10403882c000d001d05101036014901d5003001810000402018442c0820900e6800d06c000e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 169402104 1250 169400854 169400873
    0xd050f15010b3a06050414062206080d080a050f0f0c0702040605040603060501030c17030d0209120d050a020d1b0b07180801060e01080a02090f090703051c110307 71
    0x803640c28141c1d245a640c411a0040c8100300c0c0e40f545650620500403108148000b0740043c0d08440040d20188052200c400002c05014800c0f04c1580d000005040c9528111107c04285030095179a00b000040103078484021905203900400c10801084002c0c00f4492109980e10032940e1249054200b0080b6081c20381944c1002e0b03c01a080499888000c6011025999198443c1e401880020020890959249040d10103480248015542410720050010314405444600c039030542c1c861018515150030420000001e40040710f90613000003006d06241801c1c2d504000c030500c5a011a20303080d8030780d109413400030324203256068482c00700304240c542241d444841031070380404240d1065001459603201c4800711000c02c40c0380100070440580c4000000c2400042d44407400341d849a890198031030b0f0300c400718540d41d40e502a100035040540c5000080046410140254000d180c54065030309683e5a503c55070320b0221021040300540380c0f000c1c1520304084c3c0210040350a00d0000020758104881c03034582d6040d2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 169403354 1250 169402104 169402117
    0x61b0201021e010e010e1c0807050708130e0a090c0920030a1503030e031204031110030b062206020606011e12060e1605090d060b030c0d050f15010b 65
    0xb0658016000340702060a41040d002001504020014148001c00c120341e540e4800341d000911019003806040031600c5400818030039840c030b40303400307161240d02c2c0d55440c4a031780300c8020303580018810f24001c03a08000c002250750080300c140b071000c10980000e041600f15828a0740c04240c42500c2c000701a0659412901c07828109403070748000c0c2e0740713aa903007c030440c001c0c0c0105918032006050704c0b0000f02c10590064040c1c1407000e001d60440c0e00c1420b8541c0031074014422404080c00d00c81850f402081503150086992010700f4981c030f17011a0f5019150045540e075041a04296003e40e50b80d2800414040303e400100014015440140314038200440082c051b2212885040070303642e6558810500c80f401a003014818224210081141e1507681c00c04080c094001e4500f002806910800308071018401d4040d42d012071401042201e00c0259543d03000c009048042220750903004187c10041595214014001c0c80e0b402a0046c040110031189071034280031000d1030170b0649414240041c401702c00c140c0d065920 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 169404604 1250 169403354 169403383
    0x30b03010612030503040c05101107060305010f0909050f0607050714070303050307120603080d020d05060a0303050a051c0609060512010e0d0e060c0105010303031e090515040218070801061b020102 86
    0x25a43c4540c28040ca0003c0d89401c5690002050308881127000e60108030a40d038001c00c0001d0340c9555841d007000b101a11420700c5040da80d48c030010424030018009602044020340314604440b05015102e8101f0304041c1c049407880041400424600300344090702010035482c103403000250030006c4c150782d00a07080e40005071510081010608002181c41c401360300071700146402040785500c81605003184006580140c0b031480100741044007003032450824a01540940703515480b91801c0101001b0203c0e070907049145548501d161108040d800150280f01e110b000d054100400300d50142003c080c400d00d141c5840b58080181c1c50580703840a00c21001c01c2d688040c1215103000801d14034180300044046c02818003914082d40380900000c1016010351007034802d403207558a555000105850810100d940e680009070090700107d6000301801c220f20601303580300d0720080400e00303042d032801144101e402048039040701142d003800040c001c00703800c60480c1082c00c54402070341c0140d01407540000d4175602c12041c91724 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 169405854 1250 169404604 169404607
    0x91e0a0314070602032d16050c010b0604091506020d050d09020619180614030103080a05041508040c05040b0d0213020c0f0115051207060c0204020d020a02010b01030b030106120305 79
    0x1c140118104031050710390000700554581c03d0102071000300c6020101d191030300e8160201006011291140b20500c41d900c109030040e040f03180d2040075182d0b944040f042130401e559607009040345558440181c0701510403164001403820105042c0f91860f0b603035800c141d00b235603c142c80d00d00b06194002c0c119182c0d00c108210120b4405005d1001c95524000e140032100c0c00080003c0c02d0b150541d1103001100300c02207001c0c2840605694110a07503007841840c0030642503a034200014408103550303034010420180c0a1801500d003650b60030040319090b291000700760000c1c01c4c940030312003030003604203807040541000c5504020395008000001c1003c40242c000a000d0401252a0808510f5030b50540c1c040904090688404440301000b2600030180c0301d00348142520340d8240400c1034146401060091640b6000501e0b055003810002d44d54045840c0c012640141c00f0080c0c104c5055140c00a0180b00385550000f0540708072480001d001c0c1e6502c4000b80f4001c2e0714104040190003201007004200c1d54041c03d005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 169407104 1250 169405854 169405877
    0x2100f0b03061609091d010f020405030a020105070f0503030103030c0308060405070504140a090f150801050405070501080405070b0a09091b05180d1a0f15090c0c10050a05091e0a03 79
    0x2910013503c81d90252039135620700030801b000b944410060070918006030300208442d40055041104a000c2c03801901e800d94406144000194043c070300412413a405139031002ea803504550760f150301e55030003600102d001961240480c400c1640040303039290007280403a01404903291a500041c124051440381206002803221000060340310030038107a015001c1c01c40180a41c0e651611804054102e4038400f54240c444c00b13000044d0020103108107400703035501101030f100d081d2500004450750342e805001602c1500a4503000a440c86040006000340e071829103600103440d10700b074002001c5a118001107035944800101c0d41c03410540c070101715407810341d0010030700c0290440c900120f255401c0d80000280b482e07201010070900d810400c01d03028070580c042d00503014507030341b1000301e08000b00f00c240c24030313800009040124410b620200c1c058a0b00070003000480c0c00c030284008858069a40c00c3d500350041c20360710740511840c62000e110701c4009454001a041d00c40e412000c0703540d40d540310514003408004044500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 169408354 1250 169407104 169407107
    0x90d020d08092a0406080c0f030109110f012106090b01020312070f020a05070e0916030f1106090402070308250210020a05070b16080114030607030506040e070602100f0b030616 77
    0x42411803c0c024004020554842405964800780030708150300c24812003406540d00c1c80c050040103065a805049040340501d5041401504c419a604441c10300a04030401c850415110840c40c60342d90f00141c010507104d14085000c01114290b010050441d0030400524903201e0111111a400070340c02d203410031080e00d8903c4201d041c0792146d2402060360041e8400065000e1650b0021402211402c2c29118810815401c1e00300d03841d04d62100038a80d5401e00a070101040c00214003041903040504014030b0118460001030807640440011404580c001060100300c610100690b0400800c0400d8890450504040650340b040c884940748040b540000d032a01c10759200300240c03250030764000454400b038240071200c0b0742d100240481c0c800c0020502000003c00e0b2401018ae40c0d1541c41c068041e00c0d442d203c44c0702c11405490024201034105444910065104c4070402c42c00b00188211760242c013803d0340e80040b0005030703a405144001c00e80d0428034040502c0ea0003286e03090300031069200740e00d1803804d00d150 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 169409604 1250 169408354 169408423
    0xd0204031707030243080601050103020a090e04050109060504060920060d05060f030303090f100c0c0b0a0b06031302010e030606010e0120030d020301031515090e0106050306090d020d0809 82
    0x15000d15a104810391702c0d107a145d14441078015188508103031010b680e01c1302e0044040f40200a08040000c0c0103400030040104020040da4210380540000301d11140b46885d2107050b500103440841d0116a100500c0c0300b480b8240a0b40030030f82d0001c0326a002e0070350110300080c41500075130449c40b0b01240da0700c001c01c5441d0398100e00380300510310103403e980c3c03240703054041e10352640d42d03942d280a894018108801004050382c4120b81c2c1103961604c81c01301c9548030b61030700459030000505403200b10350b96001032402c40d51a400a140320b00c800d440c000c6c54a010b0703880010440350500d10341c0360090780582d090240603a041032040c40c0c140403e10b81190502e41d6070344540d2505511080f82956800006050300500143d41c00035030680713015410110340c07522200c00150407108540b905103001229520140311307172583c42d00b08039490b140000001ca48151901d0000341010350640301420240e00414601024a405004107840700c01035041c440d1641ca0080b075441c0e200d00d241d0405460b00602c600306800045900c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 169410854 1250 169409604 169409683
    0x60905190306090c05030d0e061902010b0d060f0c180b0c12071a06060a140318030c030a09050603070e220e150a0e03160204060b0d02040317070302 65
    0x1a01482010307083d0504a0b4200a240a414040d000b6007c410001c1c40c024491020f100c8806003030300e85801c502c101120b86040000002208654071039040d41d040d5a6031140781082c1d10b0250900158510009044a045a050182090500940c20319060321880b544182c842151420403000c0c2c0c0d15960804810308196500407140c11110b03000c40c502062180300031a040c580210b8004118440d160002080010b001e429210740c00101d1503805142400480b802464014140c40c0100e4801403075000b03810706580203207420000d2644045035150207654086210300007050103840a42c514140544010502d0403d551018014680500200e020a811000500340d608035404100315000d1100242e80d100c044540c0c624914010040c04200280d9451040510392074181006600c2c15004602a4201202e03c0c2000da0740310303588000c006020400d0400814800c20300704c0d00103944606614008003039401d18100441c841c0310a016502c0006d0700001c0244103050f040d07023451004850b20500e407089001c0d15 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 169412104 1250 169410854 169410863
    0x6080a06120b0a1404080901020c1f1110020f090f0d0c03120e060406030b011101180b0603210c011103060109030206132d050f030a1212150503060a060609051903 71
    0x100100403e01c031b402006004454401d909840344202044100000361015072030000b604c1d40070701060004107002e0944028031104140039241c0d0510b20303603841d90490708180c2080001d1711000441140501c1d05200c01071480e0340c1115802c07080d001c0c0303880f20040301c0313a9404000c0031b401080b4810706210380100c3c84d1402445008210325a10381e1210401406445108902804900c5070b4600b40583c14060060f0f410744006400700c0030000300540c0311240d04140c003801c2d8276010300504551640100306030340c0109071110002b40e084c3d070301d42d8141010350031211098030550074280c080c01400000da0340b00500608482e01240c106803079504200d00f0380201c984603400341f1050449580c0301c01d03407040c038040041504c60300d011008904a994005005002c0e03194200e490341034000c2c1801c41c0000d060700d04d118400d2021882c280b0400700c4034040710408c46c1d118400301038105420540800c45841c00300105a80141012010f0103542d03d0303d040a8000800c6014603803140c00d11003080c0c640005034040010046820 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 169413354 1250 169412104 169412141
    0x16020109150f0b150a2d020a14030f0306130b03011b0e0a0b0703140705070602030405040515090109020a020a151a01050f0f070c030203100606080a06120b0a 69
    0x3800441c002050401c4820311018105056a40c45180050000b03008455180302c4910740307901480202d414402141442054040e10403036000010200d140c5088049200e400402509038607003031071840d8010b00d20340d0b4003099208200002a0900700810740b604224160740c56208481407a105030050604030801b5a0550b1030200b034081c001500c240c50f80010303081e81d180d1842038041e0360240300301c00c0403501030711b260044100700380c1d00080d02c02c0009090f400d026000150074131082e99241c9003442c0d070b071754003440c0168804074003030041d45058820385400142e00b01c048000d820103840441e0720083c0500c6500065503000c111540c2c00c6009000c60f62815030b00c642403012a50100c00440018400641e20241c8000d024040c514954004e40454108106611141d8244081d0000a4134540c0c400304089848a0100100000603182044000300d00881c2c0c0c9000319082d410544c00514241d00280600c500034100482004651881d100042407a6000001e44000b9030384c0d0742d42203006c0c0c00144040e2104404 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 169414604 1250 169413354 169413383
    0x1005090f2e080a06050d02190b04030305030603011103040b13080d0e01020c10020304033905060604050f060a0302062503050c010e0303010e06040203090c0301051e0c0a02030316020109 81
    0x403240c03607107651a20315072075000c1540c5400b020380003141d042d40102a000711942c642e207400352800041c0c40034056400ca080e40052038071000c11180a8000303074000c902280c008030030b115441c902070046080600885000c2411460a0b4607041c65042e40039018800701c115031020807080c494094100c6945030804242400001d038000e001a00039404141103035458060013010310185030741c6000312801181c1580e00c0070160b07120074821180d1060540118188a40c040840c417000d180e08840e07994210b4004c270b0207040c0302e15101c0c091105494005210659091050003007113455514503c256041d241c0540307042e40c58103141c040d01c2111100c2c00a07640300c8100c090035001c00301135202c0001d04000382610000e02104a910490030f07502d010a0040403003c18801002625504040d809143c0c07040075182200c60790559030001c82d08450098030b44c4518124002c1d504894411841c0420b03401c40c03008214586088040c2078002d40364000074104241408031100c0061045200350801c1810300d0300242003c0890f203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 169415854 1250 169414604 169414669
    0x9030a05011a03060c0315011d04060f03030305060910090902040b03011401061403011a0904090c090b030f190605180609010c0f050903281403030708061005090f 71
    0x111106a1078801e00c145030000d1901c80210040d1b0380180152040709a030a400000155961000e0b40c5801d65440300031020070203156200d011300c50082286200b124400c0f429030034002c05458004041e180076611a40a010700e0140050301d003000c981c00740c040002c505846100142c080c1108400440d8590b00308404915601c0e03142030740c0b03412200c4c980c4803082c070344400303092a40031070009105140041c08150300d19010003d080c4020300307980344014400a4400616a61413030304034219040408081c0e601c80c45c211450404000300c2c41d411520030b0040c40240c2c0c0c81c685401d4103900c1c0d500000d09040c2c075100482c4401c4103204000903698491801d0302c015252084456000386015481700c00000c2c038841010480c0780c06241280d03048080036000e000008840c00c03108070f1114003198049804107413848800081b5540780d14000034800c1210142d682d81c201114000d14182c006480c01d031040214180010005400204035900d0000545000c142c1009040001e9901c280f941c5015800c1d00302e803081001c541 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 169417104 1250 169415854 169415891
    0x309091d0a051c02060f3601090311070311040906020c030a0503070818030712050c0a0804030c08070e04060509070504021c05012412110a110c011e0509030a0501 71
    0x288507140742082c0c0342c0c10817aa940003c1d0350f2246800c80c6036021400310200c4944c2c0c00043e0310502540129a0030080001100600c084111348040e50344102480806501260342e110072035662004010547c10358950003440c000c0d481046110760364a05c1841e0800803503405842403150404243d85c0c0340c90352803101608903442140c00c01c00003004840024441143c4203580c20034030600e48021802c1c41103550728240c1d9125080040d0301400400d12010072400010049000900d1080a01e2522903146191042c840b44c0542c0002d18180c02405040c40000c0310900441e602a402442c0400d041c0c5680781a0790410314540c0105401600000703240400d120001d00d43c10280c43c201c1810402a0ba9407070700301e10100d184261495504d00e0380d070041d0180354861298003901100102c0000740d55080c003012402c1c554400c6d00500c01254080c8100708950f9000d0201400d03045080c246140b030b92848900400d00070712000428420f006000c00c100d12551810081d008d038031030f840700c020000d03400d040381807240ba07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 169418354 1250 169417104 169417123
    0x40c05091306051308031f03060c0905011106010e0402011202120c07051005060907050a0e06030103050d1b050c0d0f020406030602090f040b090f130c0902180103090309091d0a05 78
    0x80d9410300340421840100c92138101d000c541c214107494156160545420842400014800011031080c0c1d400b00100343d03d0310400d0302500b00e0ba152200014900b400140c074075114162040080e4104000406c01c648809240303641c8203609280482171046442c100c04000d001c0e001d0400b40e078440820070080c400780c0300340040c82c0c00c83c028403c54008555000f10b000940d00700311200c0e40c10404c0d1401295800b8040d01c05000129190708000700b49002e811701089032600240d00c01c3d030740b1b90311000c0e00d520351540004043e42001c028881b041d45d1441705448070340c0e641c008050700724041c904a03100034050006a100d4100c3d0581e0060090089540c2d0b8108400a9080214018860500741134405c11614086c0708003c0c1802000e020650300381d4868100341000c0000815016101003081280c01c0001d0b00d40c2614400750403c8c0500507114048580c0b001c1151041d42c010505040c5044e0701e0f08042500955050103c2d5240d60b80407030040041c80c0c100b003c41040503195071140c490402404100314020481d08103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 169419604 1250 169418354 169418363
    0x20703060b0613030b0a0209041e0501050102060108120d0b0301090c060306050609010c150905030c030d0506090c1c0f020a0504140901030b01030f020102030702120f0d0f090608040c050913 83
    0x50100010070810382e4400c816141d12038038401007041000a40040103141d010408003c01403c084084012906071a40010280400d07030343d012200a40d80f115100f164050302c802c4c8014001c542c140082e0a5481c40e4091038000c8090f4086500842186c0315081014031030005130003808003080300d10348071074050b0035405081d0201c3d05003000811181444401e0b200c6491050351506448482c80d281d540c1c2c400d043c03025200b000e548441703034003000c2075041000b0450510a03200840c0c0e20102c2e2204141101c0025011074070800d20300341403082240c0c00700140c0e9a0f0b000b00d5051090f006e407040310848010241c0214502003030f800070030010074098202e0017410441d1001c4015019500c007400c01c00c07080c0c0c0400d010007042c40001d180180081048505050308071807043c01240d00e00b4409800081e150a40075501012aa101c55540b2442500c14013210080121508104206805034440078101c00d410b4000e05c1c1c00c003e04840007909120810003a0f20040801a0000600d41040307640c0c1001c80e4081d00040c0c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 169420854 1250 169419604 169419611
    0x91803020d052a0102130b1309050103110112060e0109060906050609030d0f0c021503041101020a03020d230a020303060918060402010c020d060626012003101502070306 74
    0x1e0075602a50840d8040f41002501e0580242d4009141808000f110081140c42d9801d2282c618505950350495003c2c001d119150741c0c41e40c5d1003100407043e2401941012920b2800c01c001040000c0305440200c828070402d08207524a07244800581004090580c0a914504006000001c2041e1607030f1000301525000501809083d84402c14402d1501c100c000054160703116040240c0c3c690311507081c06902c03101a10300f2081040c000d400158424004003140440f91000200780030400040304c194540111080c0082c0c24454075503140607480d00302d1120560140040c003502018441901120354000d203130550740e030790b448120740b58000b56290400c0720844e00071551a000314440d00c0704820542c03800b40001e002043c1035904e0750700444001b181410202c1e00b0000604028001411a0150034068200d040c46054150b146840c03207080e0002c007286404c070507403604208180e08041700c4007540052115640c0c8603520b44400515494503149a84010341046410b2120207d0560100307407907044900486060 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 169422104 1250 169420854 169420873
    0x60d0b240d080301030201030905150c0405040606020109020d02130906090b06180103050303040809010507020301090510060f0b031621150b0f030f0604150603090b010803090604091509180302 84
    0x200c24001d00c034054120b200600041005602c69001800724501c100240c0704101d0841d0441ca03042c01c0b0540380614040c5021405000c02d003402d206a20040210b88020700400c01150081400c0481000c0b019000740390300a610140068140c2001d08020b50000702000b80c0c1d806814207200014058401070322a0361003400c64205449114a003d0680c4d800c80085c3d80346032110340c1d9140c0c4a030b002d080d049040c05414010b0201590342071003004a51800b0f00301503d030000c20804840d04450030742d00300c000c00e41048603081c0083d00580341540d070300900740c40e03440b1044100850180d491004014403014000a2035047c11103000850b0060700280c0f0b40c1600c4800e41544070030400f103a41c001c00080035108141800091404904803102d10382200c400340000602040a100040c01e15503035800c03843c04a51a511090104104000660300408150001e0f40c01c2504860015099201e58440c3c0e00041e903c845c50441080d040c0c840c07400051000c0703d010488880078800400b5032400c040c4040e4054000d00d580e0303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 169423354 1250 169422104 169422109
    0x5090303070807050d2a061805010c02010f0507050906070501140c0406030513020616020a0b0c03090307050d0b04020d17040f17070501360e01030c060f080708060d0b24 74
    0x20300000590001c0c02403c09451000c6c0c00ca1101c5a01205a81c0b0585500122046a41001601c400103005200108112641c01c1000c1d0a491680382040c1c1450724207070401062035446400c0d0741c1a440100c030140e07070780c2d00795040482c007601200400c44907000f000303001e11850700c85201c0284201c40f026241440103940b6015842220418500040d420107800c004903100c010403540c08a007007a00c01071885600b60b4032103000702902d0b00f00043d610660351000a244100340380402100009200c11181c000c5003942507580c2028020000d0300007405515102c80d44001c21040d07501207018031202c000ca0f80c0d1920354a25084500302801c0c81030289040d060031848000140104444080d07800603140d8400200000c015600b44070380ca210407911100e88051205550302c0302c41123000081c100c42c001320780154114140001605041cbe072004042c401e18442404000341c120340e07115032018043c1800a0300e5541d81f40455901c1da0f8484004105480341010000000c1c048184402d209a900307048025200c006010b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 169424460 1106 169423354 169423367
    0x50304021f0c0515070e03071a13030615050a0509040209061e0d050c0907180501180305030a02060f10050109090c1b0b040b15090402040c05090303070807050d 70
    0x82c428229403083c105004460203c002e800c2c10b6103403012008400314041860112046d01281303074140000118200c400568110034180702e00589000a5370708201c1600820f4801c66549101107036500b000b95480d0302c40d42d03018004960315110101007010390009080d241c040303e0784421704070300c035070301da0710000241c01e48100000c1110001220030001541c10081040d020408880c0005410340d02200c9010308648080c00e1000e009410007130106800640c03a08007401500c000901c01d08c038180d0020344071344903104d0f2010b10015902c9000101c0182423292003075500040e0024402c0c441850b0b1540041802c0c075a50501c0080c001e00903020903c03121713911006940d12216002044280184000c402d54000048109150707a0310b85900003484100025201a000d036a0b80c21069000d40d01403002c0f03401e159402811240c98858a20742110340d0340c442c0008039228001c8001094101c2d010b1032 = true := by decide +kernel

theorem cover : BRFrame.Cov 169244604 169424460 := by
  have h0 := BRFrame.cov_init 169244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 169244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 169244604 ≤ n) (h2 : n < 169424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
