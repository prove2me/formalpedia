-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3028
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:27:10.025998+00:00
-- url     : https://prove2.me/submissions/952fba66-3f8f-42e3-af18-53584b85162a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 544424460 ≤ n < 544604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 544425710 1250 544424460 544424477
    0x21203121012030c260d05060406050a09021c0e1c050a05041404020c01090503030712050f150607140703120c0510050603010209040f0209090f04034b02060106020c130b01 75
    0x508008580100017040e40c81200c1c00034100ea6600b03224007459420680c00c807000c009061034180040c040c0311452061b41440c9401180c1e0f84c8101100190680c896800020144200781c88400003070748440c1d96032000400540f03014581241a8895015215405035548507070385403d0520054220341e1301c044080b558060380801c602400000d082c0142642140b10740000c41c1c0303a042114024050000c40c50484111078900070070001e0364581280c038240c1000c0b401c201111141081400706515205049014102c40c034071100010801c20300140c04c00440b80181006042010303017480c00c48a030207040c00090314550185401c01c10914282c0e01140d040705008000526003220000468161035115402d05c00d2180c2c042050107403801d01802050b030200350076204440515142e6400740c041c000d0702c00100e04003588080c030402203085422607030481300820401c600b181d111403d0461040c5900b0088503005000e002d000261140c00010f0300c0e40400402030901544005d002c0101009001810000f4100701c280e4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 544426960 1250 544425710 544425743
    0x20030406200f070c172a0a090b0d0812090d0f0f030e030c070e01050f0411160c0509040602030403020f0f07060c21050c1b011d0a03021203121012030c 66
    0x10010301220417014001e8403d002c410030b12542e178103100403200041c0c0e002c1102c020915582c0c1d0301c50788050381e0705940300240801c0840301240720541608801003d01000103242e5200e01a02c216403407084110400316100c4200c101002c503000e1a00200c0790000c6030803100c03101c95481c0a6040204c064540ca02240c0c02d084a8005040c506400e40d40f2040c0d294000310018003041c03c00c1541035082030000d032001e0041d180790070322040130b91007030b440201080003101c82c0c01810807007000c0250380100001800107807a0700b40350403d5402540162001c8015108065800c403c3c1c03180031405c00000d29442c009491001c0c40c106091301c0c5850113060484501428121385101480f48200440c0a003802d9030325592601c42a101803440c207140103d07603c40709544941c1030041c580e400007056828003900d80003580e11509070404601c207102c240d08021762203100307480403444084002000d02440740006c221700c41c0c1030700c0704960700018a2140c00b0b039040615040031103c010038059200c007207903944100b160101395200c5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 544428210 1250 544426960 544426979
    0xc0a030f050703090b010506031b0f09060708041d09100f1b0804170408031e090a0e0a1104030f030e0102030403060501180c020115031520030406200f070c 68
    0x40b074001010942d10580001444030702c0304914094a0151942841c42c2099a44450070068102e154800710b14009084a000c8000006442038a18080c0aa50315441c46260a49880d013160145c094007088450902c800e200030f00d03002034000c91204014003941101c00195102400e25480e102c8100c13501c8540401e840700e421404807882c400c4a0344d034400c1505180c074043c009148038516071250040240014000302d403010085502e0701b0125550740a0a9040301c0c100007080c020705500070303030100c800c0070300045003840c04640d10320400c0d0101e400c0000420000038210705000f41e00010300351180354a030000000b0f0050700c1030685182c050044900702690707035540300140d88098000112480070014041620715250203441a0105140000c2c0140110080c400700ca2018510010381110f4900c98101100082030b0302c60448910400c0c10344a407610415000340150b44141c0f8200c0d5164600002c5000400c108a8803e9030032601a100d50301d005a5080c0c204c0150f00280400d030380007420380b10005200f661 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 544429460 1250 544428210 544428221
    0x9010b130e060903182101090b06030d091a070c030b0408070201030f020403050d140f0a091701061203050315100201090c050406050d1b0803040602150702150c0a030f 73
    0x31103250118804408010786402c0410140109585a10070300080a0150211807512200c2c41c09071031802d0345024010513151041050b51104505500e03028055090040076440c6a105840030b41c2110481c43c2d440104460440e07091040101c0b00c0740d60202c02e8041e41c0b0003001022498010a140340354030b52291142d6111240907602100d40100010707408085503054012707044154807050045060510319241c0e540c842007007103103500c104441e11910550042088099403e031350900d058480d1a89404000500b480e602d600641102416000c1e42c0011000140204026111400c200507503441455505071480e41000c3c215480c80d0841d003111400e5074a8140036004150105d60010680030414181045002c1058110b54025803e00100f4810ba440760066044005c6d404013404001c040480c001e0124404980c11007a40d0340000a0b000400b05d0340021911101100341000341d4241c0c0701e02400785d81d51103071001078400c28661000080c56041d1118081c14109020342400f080f074034010089501140d6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 544430710 1250 544429460 544429489
    0x60b0f03030c030c120313030305040318060c0201140c03040b16020310060311030a03020705100e3d0c06020d0f06030c090606050408060f041b08010c030b040218060309010b 76
    0x388003103003040c804c02081003010b0600380585005465410038500300a110082514042c0c24982c0702d202190402d4404d46006440784d8000b401410956201e610007403028030045420f0b40041d5003004001c1604010301e084661002c002d00c021850700380780402081c06a040002d280300c030014014a02400344e1070600180c0c1c8021302802c2d0001d8094190315101403542040ca0129010343d214030705480001e42c0000f180c1e010b1701e80c120b034042860f040551301110550342e0000c071260021400c3c0035801c1440013003035500944040160f10030740ca44000584a0700c0b21054419030b80700055840f40150003183c0300d40c3c001c2007801c40d011400300d216084040007205a98096004451400300000d08001200b494811000074000c9494801d142510303100141e56a00e102602c28074101102034003213001c00c1f10b0300e1143c00f00c1e400380f500540245d80d610b8160600805502c02c981c2e003c07a0904000d4a400c1c58a842216400c1c01a08444008048000e0a12000780c0000340406865903846c4010500c0d5a107c898040207034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 544431960 1250 544430710 544430713
    0x5041206060e071b0b100506120933060111161a0f040512030c0703240506031e0f0307060605040f06051c2d0b070f0c060b0f03030c 58
    0x440c0b0701080d0040040b0000c01007401c00104c410800e180004030124000d545411045002c03d6807910040e01c1c61043c41d80e4040d99001c40c00168102c400012084518810301086003954902940d01c1d9a40307050420b070380400d000b20858400544507000240340b400350061030601d8402c0300c00c0100403501d4a007a09907180850380541c100010407401ca007a88450001524020145051408251194910780180c0c010f00d4800e4a8102c107200b03500104105440c0ca1040200446424542e02c1c14001c650300036010340c640a5804080744501040d5940c05030710301848002c0c00500301d10400d00c4044201e1502104008400e000d21810982041401c1000e8801c180c06610000703a01480c1000b00400c842020540000440c2094004c021035074803490320368608004502113885000c1c081c0f9040c8607055030640340500c600d040140340d519004045c4c000c504131038820511040c480c0c0f07413039005035440490302403210006050040c01400094480d0410300c1c0520300078018601050101c0d0010341036400c14648114075 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 544433210 1250 544431960 544431971
    0x10f090f0c0b19050f0c0304060906110303010b0423030607020c1e1c0501060b03010e040b070e09150a030b13031e0e0f01051c02040f06080c160305041206 68
    0x38400148501c000520303040b1203140c6041030341005449000d003035801c20414084040b42c0300d0803d0002e041120000d040b43c01c2070300d03615a103030880901728018902809002820282d403406140c1d100104881c1030364034614500381802c2c60030302501c40401160a8803c601c00b1226038410458408002c81401034043c1e0300034102080ca07040500040c0075a02510413054141e94040b0816500e0350950302950540365514822a5000c1382003590240090383d00181c8203020020001941e240880a0b003401103102e01402d500b1a00d8000044882655261302c80b0303070000510000c640b60310340c3d28859102c01000940b101d58035030f5603903c400c50303500c1044411b65403440280d40204101070303006c402a034a43c103800e2100d4402000d40c0c100102100071003103e2138017861442e141c11146a00170419514801c0301005485010480c85440300701030b401c540310340040014201c60201c1d146000c0d1540c540316060500002d070418a40302c944001c2003400210550a101c41008013062030141d03000074003c0e803806500007140 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 544434460 1250 544433210 544433213
    0x501060f060e0a0f030b040503041806050406090e0d390302060105010f0819060509070c0203010507020307031d0a031b0806060f061e0c01060608162f010f090f 70
    0x2d4000004240d100c2c0c150b5481c28409800d440011400b501e07000030002c0c0760760f615460403614500c80d43c1c10003180394401d44200f20300340c00ea6400520507924140d8042c00803558074011201500c1c1c000e80000c01580050400046480c840c240e801c41c060040d0401c521100ca60000031000c2d4100d2851701130502c0b04885100c004e0540400000d80140300038601000c43d2940b500000b0060b45003d0410072004500c040540744100303107508100d0141000604c61010340c144940058001010b002c1c3c201d0280d420480010402070000c0281c07044160035403285d60071003002d280c40840c40c40014050b10750000381c004010001c1601d82501450714444030010004203400e01280520300305000749510b00c5407218240c4900c0301e0700d44900303581c03400c040701c10711000b9440c600d14061308030700861050080643c038008001550a502000d0300f4020304924008030150b41b1304050454a200c10320080c0f10640400c911105c5006070346803404201c000c00b520000520b56816600d05c4140c5180a90648500c08034502c80030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 544435710 1250 544434460 544434467
    0x9030409141b0702100c05150c130e0601091205071a130e01140603060d0b0703091b0303170c070c030b0604140f061011010e0115080a0f1e0501060f06 66
    0x41407003011074040d41444810381c00174070074081c1e40d07004108008810107540b040100c01c201c041013034080700d10301c1382051800b0710004980d81c100b05040c0e08030700141c150000e0700c50040054a4042c01c4d069490506071070030b104101c802c0c071410794411100da100e01840080c0c8201610b245000b9040c009074615a030351102c0542c0904584550440b044901204004100d00c00b40c2d58106000e00d80207981d941d0701da03601e00380058410101c944016144504000403c021150326030b01c10001544195200399940a801c4030030200c100841c00014040b41034100d0540d20038181d990f0b2164444084009285003400e00c0c0c0c2c8004401c1c81c554011903103200c40074184059480d00340281804502c1030301d00c0200c9031420074030b0100340c808040d10b00c80c0210301c408078510015216000c00c01111481c0e1000344500400c0b00032050003005c0800c24442d03003400d8054040740b11100880c0300b42c0b50503040100d9820131603480e02e86540d01c154a01e03528508826620003100001d40c02e000d1440100311545a048006141000c040c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 544436960 1250 544435710 544435741
    0xb04090606090b04060e040504020d061e0e1b011808070b0909010902071a090a060e0607030e07030b040b13120905190803040b0a0c0807050f0c04060311090903040914 73
    0x5036580b80706120074402158407a00c101c0600b03500307d401080b076890703500120b80300c1350054401034502801e000c41d440003907810a0191480140081c0d040100044c0a0f10700c42e15240600c80c0c00c00c0c0d940e50580c0304031a541c4503403814021b44032000f12000025070794640c11841c18036140c0c0014144003001c1546105031903d8140f0038010003a0b0760003946010b000d561a034842e40c940c4801030078207403030080105444c040d04115910003503501850410003501ca02580030340e40c600c00c4941d480005d0a04903c6d68448401040304012a9480502c07543c240d00c90ba501c61458490040580780c58812401600c0040341300940040c1c000c14142d111500d040e0708002c10700c1801840c106c245504610705c010200320800b40002241d0445101442c020784130040b0f40c5003200c03042c1d0403090107000d0420200703580c0288440451214940b61140d42142c803003942180038881580c00e40d210161285940b070b003141c0440c1c100f030012180d00200803c01e80c1d1900f03494800010449241c42951450f10144004012070300d0f442e6240c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 544438210 1250 544436960 544436969
    0xe181510061d0916020304050a06120609090506040f032a0302010c11030904091704150908010b091816060e0909010b06270405070f1206080d14040b0409060609 70
    0x4070302c01c2d081c1e8400300e40e0445024200280680d000a42815018428002e80e8081c000042080040780d0356060010f02801c9035440c0581341c5842d02c000000c81700d62911552140c43d17030090140c105540c0300d807035403248090302e010203900340419905002c0704640b2154180b14003c00b8101d4011402c0030703a003002800c64a10700341020510001d400c10b000b101800009550311002c04640202d40c105d441d28005803101e04180441c0d0f140c58020502003102010917030f03110031445441d43c45540c0389a803030b60a00d007604d2546404682100740c000c0031610307800d001d0151100e5885404122480c0800c40d10300012507030207640c41003002480c1c200034002507251090b0655000010440240316000340c0c80f00050f8079200d502e0183d13141105038075100310f14202c2d80c1d0030aa44248000c0c0104141c0c68900406405006014483c00001b241c459046e44c1030362052251800f541c08940c0140410824080c042d95500d124281c0032440fa0010300001906000700d070018400fa008c205408210315290040142c541c0c00203820 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 544439460 1250 544438210 544438247
    0x1d0616050409020706020d090303060810050105061801020c180105010212073c0305070b0a0e06270f1b060301030b0f1504050708011404060e18151006 66
    0x404021294080c080c0c0c0c0582d2491003006036a05600e00e04032000b4801c181400c02002e090503060382c01d041e0107074030610440308094241c410a10b8a41614070440340d003400380560068050041e840c00f01c440c08981c006d03901c0b040c011102c2c00154240082c15000c1041809402070002c40300600c401d59042c0322014198ae044050385052003001d64840502e0340318140204402901048a0740001040004045402c0c04250301d04501a100e070400400b240d10541d1b0640700211054042800340c413403031096061050707082c4080c2c42c0c0c503101c911507051654040d1200c0c25801a040300902c03c1c600041c0412144e11303000c10020450692000302c200c2c5000016913401c0d00c038010030320040020800c1240c10a03440404801c4000c2e165503082da07071400f4000c0c2c481d00c0729042071500c4200002da94219480078140c54010410600d400550b0003003005079038082c00340e580e0a00400e40801c252003030610701e007260b0305c8600f802d4a03520442c4100c05448030030100c5d102442000c0c691800c12260341c103c0c0408407252020341 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 544440710 1250 544439460 544439491
    0x40606020a031b03030605120a060b09011413020f0f040e0906040f0303180f03030c0306051c08030c12071e020712030503130b0123060c0c01211d06 65
    0x110003814040c01d1203083c2150301100d8103503100301880790b4442e0000d4600140a00701e10000c04e41d11503039038280700f14111005032030000031141c00c0c50811078060403661512a1010202d02e0202484031b0b010f5450087c02c010f94081c8000c8420b07200001c084d00c55004c0f86035019490b545000305003240c031103000e41409019040341003400040b405107030580e252341d50541004030700384906070405840b000c6115400703405084aa0209001c00d50b0540191900d41050fa90a00085840b601003000e4000c508100c0f041051040b60b0132030004000e1806154042d15081e86a03041483d0105142014202160340d10006000100f52205104020180c2404080f140c03000300040d50070000c0400800e448210040c0501c400400016048402485004020796014a90000d2075942c0c203520f40c0954406070150007103c001140010311828148107551405290038000c1404a0601005551442807200b003110031081c1a08840e0a4a501e0b0003190111000c00d0101004003600c0c42d080d81c207024024050213101038098 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 544441960 1250 544440710 544440713
    0xb030a0c26010216150c0c0b100506030c090909060702060106031e06090c08010f050604061b050114061005031e0c040e130b0105090f07050c072c07020d020d210f0506040606020a 78
    0x761f07680c1042c0d5000c8400e8842d80c49400c0c3d00b00807550719601180e4840000001c200040e100500503100701502a03484400940300c2c0014030b922104200d4018005900000c010400d451183d080310790641c00c4244030707994000b203051a030030039a0b8954018100203512040041010795202c041180100540052124005d04000004000c2d114610402042001007450404030680b100020041603034800d00800c28060002208040050225521449140807041a2280c107002c0c031b040300e01c902d40020b00301881000c60b0010340d4506c00d02030001c024109007441b02242110306030040328043c5441e10080e038007164541c1742264640d20160440c90240c5a80c500307000d01200d118030040c0d0008840d060080c0c44000042442d03282001c80e0b48854601809a2400c0c071041810300c101101301410b17108011225070303035588180e0740c0c1d402009800300103038000c41810000c039200740040a5551322008aa00c1c48a01c02c2030404140d61711680b841c07113999a66018840d682c5041c0c89641c005002c180007601074001907 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 544443210 1250 544441960 544441967
    0x7091a0702043b06151c08040305060906060a090b01021c0e181f05010206010b030702070b120a1b09090b0f0301020a050a030b030a0c26010216150c 65
    0x205840280159101c2e255250040ca20445012070043c03164046081d099210702803030b20302500714403080e0640c021030000c548801034449001e402080302410341140c1d445001d850424002504401743c800f0b890500020000a0051000600039541c0c1c034024141e900381113003000044541507002d5000c403854040240b000e0f907004078610558409030f10040e000c0131801001520300d600718100d034981c804944405440201c440402c1207000c0e1102c1c84a04031b940c1401c407000e40d08621715009590142e0b11000041200000000082d40d002807a031068400555891004040e586c00c1030a0200f0039210410130030452011500c280c1819804030b1080c254144c400010251026042c0d0003150035040c1c80303503004249030321215810013a07100e0180085588811329a00102250800c0503440e00003410084040d40b507142c001502030000b03400202400d5800d141804808201d41d02e8442e00c801018400700705265081c0c03e1019000d10306040402c8284030017039250440c41e2041c0c804140303031082e2501d119040d00301d90 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 544444460 1250 544443210 544443217
    0x90109020c0715090f1403300301060f02160f050f030f0d0c1a06060d0f0e070e09010c03051302040c02030c16091406030a0b0a090c030b07091a 63
    0x2450400181c0d40c0ca400d8052a0a00754542c0008007035044010560040ba503205130140100d54804955400585d115109038440340d50842c1070640c9540904d203040c100c44a101000c140000381c0d9a8203170b08000d81c8100010701a0000da00c140b011038004400c400c402d58060165440c1102000fa0810310541401d1310841003807683e000f818010446084010070940307081000c500c038001c0300c1c4c00f1600500c3d4004001840d050901c4002c03651191a8103504040130b200c141e03001e001d01c100405450420215100d004014001710740842c090a48801c007010003800c0c1070200c00064100000040300c0c901e402064682903401c0402844100f5103054108010051024150610946e0450340401c280f4903000080703245000795100b80410340200c00b4145004078040c4040c00c1100d242e9441407088600144410310086001c560035905030300a069050005400000a150700603000840043c41d98003d0300c800030381800c11f030001c840c0d820044090280c515000b03150fa034010f0040400404c06a00ea0290107500ca01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 544445710 1250 544444460 544444469
    0x2031c240b0a090b19181d060102160b0d090204090f06050a1512080a0203070b0a020715020304050a021210020c2d071a0906180f09010b040b0706060b0304051005150901 74
    0x1000c0484140d1406d07030080507000514000030301c1c15030703900340161800f5401c0741618110301521074484420b01d4405900501000c485125080300c2c2064020500c0704094030300ca01e02282e1185ea148854000100044001250b040c0510704c0080c051400c140030703400b101c4100f951711054841ca08010481c0038907540d041ca075110b501144030f9807a51910341c416495401130b24401881600201e00b0004100026400303014410300815000502442c5a0b440c02c0c102e10050360041d0480d0014010f02c3e0140c10a010598002c0080a0854805510f1140c0d54001c9800811441d00305821100e4104610000b40580c08030349140000028082e102010b4010f55502d014070070181205032103000f100c2c3c80c403085400d0710306411001c1d00941c0c0e40d014540c09440c2e0031898012542c46103400960548003420f0a12416060303078207482d00245854280100392542c0d801c2040100d650680b45d4001107003003581e41d005140158030680c0202843c0c5114855401918030040c1150391030a0600c14004403503a5403401c0034110b5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 544446960 1250 544445710 544445717
    0x6040303050c0123090d0c031205060a03120905011107050918030409060e0402040c030516031104230a080a050a020105090316150f02031c240b0a090b19 67
    0x40d110860400d0140c20b803043c2c500c0c00c4041e100c80d00c180d044e4000a52521680980d030a803100b03580c0342c01040e1407201540e200a400607401d2002034840050035440542c1001e001010b110030340d5500d80c2c486c880140b10840c000001003460300c013003100396081040805002514806090814140310204608100c0180042c00641c0365242c404003554062007181d0107421400810300c20580c03a0400170304022070580d0100d000340e00d800c05200000c0c0c402d1041e18050096a41d005101520101003200580480041151300340c004000c00509490300d8043c2c22140c4603405503144c007141c034100030400c5a85c1c450313009403041c3c0c100721000b0002410200300c4031022542401c10b151508454400300303180c10b158000154880d22250800f00f05610061f8000303040c540680d070b81c40c03e081c803030603001c9840e03003e5615881030340c840e9030448800390031080e04001e1040c42d030905400c088404071150091423800d1035006e140c000d20300155551400382e002d482840640781c1c01191a00c1e10302c41d0441912405c80c500803001c1003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 544448210 1250 544446960 544446967
    0x140f0312072108041707030801050609060d02040f0510050307050f030c0904050a0f05060a081e0c03060c040e061503060f120a06020315091006050a120c02010e0c0402090604030305 79
    0xc0020042000038030209003411041c2c01c060740a00540401001d403800e99441000380f10845109500d00c08580c0d00b55496030310514076921307250174810b150700014000d03031340203001b8030904114108900c00351000f41024198400c0c031a1030310042c000b00380e002504607801c02070208104100c664116088446101e442c0300310b00c4d9a980d82c003d20818500401d140e00740d00604040600c10451166041680400020181004580c43d80c100304411505c0303601c2042a190403400e002c50100810520501c902514142981e200404030000a820001c0032070f40e03000e40d01d10208007406100b8001d180c540d84202d0590724890008021145111507010042c1003521502d078180c90b1500a840e800805d09115003c0c900b11641105140791590294104503a80c9002c400e2110000120f450300c506c0c00d6001c1d152042c56003084c64184003084400740e014440007c1800014094250100c4d03480c860311401b80c03130300e1b4000a400041407111604001c00448072510850050041d07403840d80d100811202204c0d81400c190380d5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 544449460 1250 544448210 544448213
    0x102070506061c032c040c0804020f03061512010207060509070303020d03050f040f020d0804090209120102030103030527060a0801090b03071401110109140c13020708030703050717070504140f031207 87
    0x8941c4170100c10316009403c2c41c3d161000035401041c0304d030080744221aa48040c071060010701d580c0b007100f120264102e10030484003c07a1030510304403260390945481c0000d4500162a01c030340e005d841064410807000c1d40a84001c00034140e044c481c040d01c48240b85002d000318182409605503a8801401c0031b02000b075519162411940c40300c1d9030401e02603203d0710741502d641e035800f00071000750807500c2c2960241a0b42030a215101806100b02c9051f2036042c2c0340c0c141441d40144034a0502219450b014220041d1036903c03207007941c0c408004c1c05594181b680d4a0003151704090500c01918032007603149000e41e0200c00c0601c044400e404851410b1174081c41d02d0500400c11101c1035001d003138a500040c2041140811034402c0703100104038400b1a402c2625012543c1d03900803090000c900c90302e00040d1038403000740003295210388241c000c15008851444d00c0b0100c2550307507030341c000640340c1078070807001103240054100b000c000401001001120100c40f6480d40451050110340c490b190070501c8007044c0d000140800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 544450710 1250 544449460 544449527
    0xb13180c0c0206090d060e010b03010c0915050c0a0f0b0a0e1906020a120203010816050a031e0303020c06090a050106120807081e0d0501081603081b010e0102070506061c03 75
    0xa07644c2d401000074809030b400c8484441c003c104602c00c0034000d50330075420508460103000c16400300d46000312005049020740804503119000642d19071441d001d81c1c903400001c25080c0840c03c00c0f5034021901a001030514a4101c0300b10340b03c442c007030309841c1c022151741012403005103408410150070500140c0d4070445983d049031010034665080c400a480400003044100002910410f102c0b03040c1c4040c401c0030f4403103040113000440c2d8803000b003640200c80e10005550b0f0035121801d1404d80f103410094242071403440d13002d0801004480c15400c1e03500601700c990a20009000b040001d041c00c000f0301c202c4054a4481045a225401e00600100e500041075030a40301c90f01c6844802c1d0030792801041d00c1c0c212044c42c00003d8a420712604800e44902202d484c22111414101c1044960002d546860820000d54000d085c0d070a51440602d6035613600c80b402e074600b0080c002008554800e102a048516018042100c581c500d040943c09130f40d008030200c00001c0d004400b02c07100701c40710310001c2e006d00904215803 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 544451960 1250 544450710 544450729
    0x1204020a050319020a1a0f0a0c0209040b0402090a050705160218010b1803030414040905070506031003031409011b0f0203010c0305070e040b1e0a0b13180c0c020609 72
    0x180c142c490100b40603071402e03c020300341503d54800c4640750026951102c00c0c040c1d42c032159181103200e900821140c007650032014010300c0c0e81041e07810840840c105035000207403070740801c1342c003511541016400c110851601803031081c2e120141040c200602d0400c0700000b00140524040240200c603642800d00030340d03070f644008441080800d243c501080da1244136a49003904003080d00c4014074900c1d032504100b844c1c040145c0701564020041a201c2d4046c41d005c00002e03103104841642d10b801107040100302c41c0c41e01001944203001461000d01d2303507440d601d0001c3c401a0040080a0841c1c0700b8031a0301440d030390010b02500e03202070042d0303d41c1000507603060403900c0ca100308000030b41c1503103880d084034046605138104502c922680d072030308084411958180002c2d244002e6015a0041036200c40c10000d1001241c118002d00d4090010b2034030700e40b1407410011903800840080035000501200f00049140d5110300d0405840e481002e104581c0090009400c40c0010b800c000e03c1000e0209110525444800c0309 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 544453210 1250 544451960 544451969
    0x60106210902031c170c0304200d030207060e2e12140105010f0206060108070807020106030206070507030c1d010302040f0b180108160303020303060d06180305121b1204020a 76
    0x2034510190004d0450902640000040c2000c1001d0851550210071450002403003949240051031139036640d991003051800510200c2d10717207500014844413403519070a100c4d0203190f00c20307001040710600717041c1c0207031138604075500d40f0703128092055103844405031180091100d01051000104003079007400302911100c0d0841c00080915180941031a030104078001701f80d04a44003a2540781c17042c0d2113040226100e000c00c8030b8071800700d503010012490581c030039240300d58000c100e0310000032800d48980c000b88982d4802e1409440c141e0000606100380304240380008020403004165140001c0803540e8081d28500c14407020348650b542d03200303003001c012250300400ca10320b000a280c102c48010040e00c91000303013020f01400106104184042c450342a01a03410300a03280c16400850031aa20341040107218a01100212102c544030010040035000041011a41920a032912610740d80c3c0881c07140c0d4044402041444c40a406180d481005402e82d400c8405403002088070030147c4e99030740049100103c86510 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 544454460 1250 544453210 544453213
    0x9010938060d06090c0c031715030f0f0606030a050a0f05010b04050f10060f1d120a030504061101090f06050601170c1c0b220f0c0e011106010621090203 67
    0x41d916044100b41d4000415254070441c1000021100700c0112101071071500c0c01804030341c1a5800c5c4681170482e0450039030101e2180103c111520010021a007080b95a00340200b95a0068a2013440918184480c95110b2002e9005025070368041e00c0741135940c1080000a460380c081480c0800c00d00c00c085d04a000d120380054001e00207400c215035444410001140d03503060301e400340403020424074030685180804480307a5981a030350261040503102c00c050710140503940301180348620b09101009000d000c0401d4083d8580d01e44407894000c0250100c95001c0311842c041e45000714402c0040d040104040055411901c001016900d0038016204994410039503148201c1c0c100400100c0d021207001032102080d0103521204001c0c0086018081c0c8042040322940210f003184c01101c0401c0d502c68019002e030001c40081500f83e001846a002c40e140000080009113451009a225580100c080d848048012000341020341c075102000300741c54102d4055821002c04008003a022254540114405a40080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 544455710 1250 544454460 544454467
    0x140c03070309090b01021209040209030304120305041e052209020307080f07050103020325172d04030f05030901020f0301150305010f141309060c020c0901093806 71
    0x1d0190030036201d4401d48500b00d0410700c26411a51000c58071840303104c10300c40300a080103045020400a90891910f06425220a000014500402649103466076019031a07003035503141401446c1d4014424842c0b900146c0f044c00c1003c0006444800700e2a0802c8a0a2840c8040504400000300540748014020b0351500c107003100403601200200741c40e846c1100750001c40340115903450054082e40412248030121440300c8034240b956036807031030725120640e94614060010142180b040584000f041d203214a0040c043d003884c0c032460f80320003002440541590340d40c20903440e141e42c2c002c01c00300c500b00150b42000804008940c0d181c809405503414003030500d8500f80c480d03031943c00400e0b41d034905d42d5100002909081c0001488070310200c200d800e481032000c0203660300d0b041e60288070084560004414100342d80d080e401001c6441442000209003e03a405000d09400c20000c100e04a44182c0107050704ca8581011425412040c40e05c118845148002d003450507071408a800c03420710700c8200b0207908200c000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 544456960 1250 544455710 544455713
    0x60e0a150501141e0d0b13030909020c030904112109070909050319120c0c02191d0901020d150911031b09040b060f07061812140c0307 59
    0xc5003908001441040402050303030388489142180550000c0290040500c4503001443c40c1c00b0751a000e42c011003d0405071884c0000e03600c10707124240413039800001d440510702c19010103a103c8a0030004015003041035003048c40070041103441c0c2c0f00b6801c0e054416543c0c1d161301141444160141d920301014483c1e02205c41d40707007610030000c0000440340c449031802a00000f00d000d10382441116419074000008500380700384101d410003201c96294090041c0145001da416481180707000340442c2c4141a83c81d040d030300090f40f061260b580c2c070362070004040007005801803100650240c080307a164034004091282c15200c1000d0780340244200041c0b031000906140200c8444155680784100300d421610040011034006000e406c0240410744900c501c240d22607900546200401003e0004800010700c0015112090300025072558028059580001c82c003041c002c3c1030045501c034000051a01400e11400305c0c0560f0f40326046000101101024494410300804501002e41709948600a120f030840e607642c2c10390b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 544458210 1250 544456960 544456973
    0x1120c020d030b060a05030414030d02070c060f030911061b0a030e131a09041b15090519091d061302130b0d030318060218030601060c050c0904060e0a 66
    0x203145818003003030a00b034802c0c50f103041c25000c55403443c1c1c01d603481c142103844a40c0d64a160701c1440100a4003440300384040d4030f10382400c1c40100306130340c0704201306d40d22149440009070842c03003006a1002414504150300000c101c401400c4007901d0b40c11204690349103001c0050046481941252424034030400f0442e01c10141c214584005000c0100c07162075000560701d0410041c0c0d120300d0041111521884402c82c298204500e00580051007014008004480343c0c000b40e0740d0717903100e90040600980306c00c075076032001c1d802103480340140209440c290801000b540406114451501c50350300b06a6072541c5030780c0c0011142400c981081c5c6000291595400d011540030b445103070101041c4d04c00c803074100b18440744071a2071150000f40440039143d450754641c10f4605400501b001d007110780006c0c45005008001410a10061040041c81c2d50700b0302090500c18140b520b40704058007c60180303d40010500c021030380c00100d0000e001e80449000e0b00d80d41c0c6034031b058000307022603c001c260b1522425070380c041003118 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 544459460 1250 544458210 544458223
    0x320f040e0f0a05061c030318080a030f0f02090603060603070c080c0307030e3f1618022b021303060209010f0305100b0c0c0303070311060f01030b0c0901120c02 70
    0x10b40902409540c403000200711014150207485081e8400c1798102c00c001034001c4d04400c0d01095140b010400524080c1ca0300180c82e84582d4002e4002692918929031000d03a41c81000c044d600402000c505003410040800c2442c4405000c9502c281c80100004150341d1044d81d804010540c007008450300e5501d0394940e69541e82041804802240c1d00c1c0304101c442c0e00313128440004599000101c0314606071343c840402d004030011003481c025184c44806003040c440b002c10090940d0750b08500c549415514114500801041c0ca542d00154a40108070300505202101928038034000ca0814a03030690080311010b100034401c0280804050051590005c280480369000e800300c0c8000b80c0310107080d0321461004070b0031990b0444584c10381c016003001c14068440800c02400c01043c800d011528001c030b06000080c59178002c0c500440c0010040c60a002540c2c0003485442c0e04283d0041500100c3e50455650b15070000000388080140e40c0d002c50850040c0e8401c508004100b803a0400c00c00c0000107080c0025151031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 544460710 1250 544459460 544459471
    0x60703090e01060302070b040209041a27060f0106050a02010f060605031509010b19030204031a040212030307080105060a0315181a06070605091e010507320f040e0f 72
    0x80980c00003d00c481c020300880310740c01e9209002a003180d0f030341d600b003042441c00908180c0d940045e61140000b0b100085400c240994004031084c031031544d0010440710211507400c0c850803550414010320101c0e540141c0f4140c19910b160410325110282c4002c124014504000e000c40914203110b40020895040001107000300780c2031070342c2103071380091406000c0b1494080c4590150824100202343e801509402940315200c5c031480c6c02343c54039030360741c8032a004607c0030030707507039202e040b200c0c0504c41107180141c240e500200c0f07500041e46c11480d16201c0500b09042c1449054010880050f1540e00305101e0362244800703480903d1014003203512031200d04603100516100072001894004902ea000c080d0329140c46119200070289840d10740340343d5555010704009400c0301b41a1240300e2901d1090102c00e100d20f02d1072b41d92040006614980440001e2142e81c41e03a8040c0b0780c40d5041c0a00e501d222640039168400c540420700b502e80d9500c038a415540d1644219440705403004203682c180a0500d0040f40d00c03e0298 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 544461960 1250 544460710 544460729
    0x30303241508130b040201030c03091a010602060f071e0302040819030e0607080d0e160303030506030613030e1525050d0e060403062016120f09210206070309 69
    0x50343c8500c504001c0016858014003071412020005005600c20b80081d1070b004880d01d40851840c51030364072000c120740c3c60030118000750302000c014401d496042110b103501c1032a50005641e00d0402c001c000c0c11004821070a10803d001c440c1c809000c2c14000c0c1c0480b4014407000c4115031038503030b0a2804c068142c440103c2200021006d0b82d1114151500c04240e03164150440319451500b42400100c2d03005042c03126824030240103080b0080c16240c403003005200114001c1e10041a40c2c503095042606000c0020f00c203812442030b503c1c03c00003095024003504412081518165040010400a550140140e00c40304034100210390517100f90b81050100025840d10480c2200c03922103800a055401e01005078403550020340901041002c50055042488a5030349081429103001551405028a90025100078598884891200101f00002a00c103010b220035190600300c209508030300901c0c1c000540301d0304114400520484054440151040c604180d00811107640e4010070702d005002c84040d4400c64155 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 544463210 1250 544461960 544461977
    0x1c0c050102010501080d110c060c070603060504021303020103050a0e1903020105090105010b031b07171c140c1e0409090b13050706050c0a1a06030712020a0303032415 73
    0x2650050107624141c6100d000642485d400010080781c0a929081110400d4400d210f103400903519444020311f5020760a074094a200350419101900f910741c181e2260b401148100440450035000030032910a807582440c0200710381e1221a1140c0140c442100d41d0400c50291000c2c081348032680300d080802c010700c2a00240015a25240c4260895400344142d0390502010000140891024030080d5903202107003880c0c5081807000e844107546024066101100c8420000d0800075840702c1d0000804117802c035a206000320b281c09c900210954801404880c0ca14101081c0c0800036417003220203084e9003202400b601e4503a40e54000c0080580f104003801e55140ca60315012503401c85ca503a8802040d66044001005030910301203048403154844c80f030381e11640c0204515040001e03a1940ba8180403030610140c08403908000b41010b0802c400355010010f03984002c510a4010b8541c0050300c011030303401d4140010003851440103944031000e00300004840b0004030308045800040f411245500e50a541d076401c0e60b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 544464460 1250 544463210 544463219
    0x703020c25061107090c0e0a1410080c0d110909010e10030201300b030106080c0a05090c04150206090d050405031509010e190b0c190503040609021c0c 66
    0x35500700c40040301c00303100c071551091000b20b00400c100603401041108407000c2641e17070481c0740d044a044840c54030001c2d15001543d003403860108407090142c950311036043c10044801c800100c10a8040f12070409000da003c0000f41d0450928060381c140c0e035841c510078080454482c541c01c005601c001c210b81d10444031200081800310030080034902c2003000180c504203850554006503003544403101c0c0141da008807090380714541000c10300101c0800314034840104404441004140c06d41c0d143c0d4000c80d08990103607000c3c80e5907507241e85480085079002e4400c40f1403a1107510010940348615003008040780400054045401e60029603244512038203000da5020090300c0303000722040d10581c4074899041c0d01510b4100c00340b1044002c0c2d95080810305000045081c04d1605060404040c2c9400c4542074447d00241018411040503c42d4041d501405680c5042c07070660f11080c500c115220408104000400020200041640158020b60700200f0400c4101505961050700d5034800d501103c650228030700c0041d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 544465710 1250 544464460 544464493
    0x2130207030c0809060d090b0702070b0a0207140f0406060809010e030703050a030b010309021203040f0503010c02031204050c09010f060e040b100e03030910051b0c060307051b060703020c 82
    0xd52030395065039400c1d8800c901ea1600d0700280c029035200c6070f010004205444503028030380b0480042d144500300c00186860800c5000c0c0c100702c0e11b54804002e80804228200c1c0482c1c0c085880c4003541c8890040e5480d104518000c0f502c40784030b2100b125003152400c5008140c168002d1a143d05c181b802800038400703c1c2990003c030361240100003008020800500c01c1014590080e00b188081139010714001501c111780e80c0000f6160b1b1001e85c00350362190800541409000010b00c000300181100740c0003484065040f0400a40d40e00c20385102c1e140c0d04e2011400700f0104441840801c10b40040200620600e503100e9140c07010000040c0b054401080000390704c03c46504040c012080034180007440f051001034001e0050302e081d075140119580c58001001070b506a035036a07800c800540301c81d590b110380d2141c1042c2c6207507201000303040c0074000136881032400c2c4141c1d0b90303140101d030750103810b500d400c1d44c17121806200008104196160900c440c0941c1080020940d8950301929800f031400084901030b05100c071441 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 544466960 1250 544465710 544465717
    0x14030f09030d050f09090612070e1005040501051f0210020408011a03060402090103061107081204050106061803061107060c0e0306011a0403060209010e09090f060f0c090904031b03030603021302 85
    0xb134804d03010034000b1a070b240c03420010003a40000c0203013554401c82c00d00070715a818004150420043c1d295a4401c1c04240c20900c1c2e00c00002c0c2c04107850412855041c00001200b04e104220f160400520207140321119a100384108111000301d444190b4a40751282d06080c060850310380071041354071407a0324112103403600045050042e600030b420382c217480c3d08580b02c80d000703880c01c14030010703c00d03100300710140c0001c2c000802401441c0b225440300c10903046c1490035500359003842e480300b01005484070340070290300090a100380489034000c40001c2d0228605d0b003210054002e0403009892145040440d4100302d400c09044d050481040341916070581c0c9032800f41840b1700d4a03410f1a10000700c00d1005000140c00e40e801050707050700c1414103045c030480c80d00024451450440e541509500108000130107404100032250b000406100c10801520742400710f01e0aa01035a880c0c3d6204007180030106090500400c01001d084040c0c1300c015a0f03940580c00c02070068801840100c1c0584160000b2441501051003038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 544468210 1250 544466960 544466977
    0x80601091a061905040b220501020715050903010b06210606031506030603010902060c1e010b0f0904020a080303010b120624130e0f1906050a050d14030f09030d05 71
    0x101810100ba9000f04034480b000301d000c0c103090040422022500e10b1250700500b900106541d9a0100065460b000786082005980928159801003405000243c1b0238030802651100c140b506031b44599084001902400346902c050390484000604800c12101c0b4804020801c1795981d00760003213481d0101800070303a101c1115500c03400780c18159104100c1c5040001507030810030040002c0b07203031034998000902c20f41c0941c1411819500100000b1007119201c403044d140600c41000800400d04290080b0340401141c60f0700c3da101d052524002411950340700302004c003405101341103170b44039a1211001100c50b403040f8922104040000001681c603d0407170b14061100c44035030407180c00d2010f0500400d0781900400c180803440494040d0210741c407580c1810b020300c81d0340200d0030b8100a050054440b1715103000110b54992490600d00c0c28030031915100711500449005440c1c2e0f40440742c190801e1104a070040c110030089000001e40780078030603280c5000c0d00203550304600b621180e4860700400e6455102d036158 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 544469460 1250 544468210 544468219
    0x3408030a090629060a0228020a060f0c060b030f060a060501270e0c07080a12050a0b0f0111010902122103160c0804080f060f06220222080601091a 64
    0xe6202410010081c10745401d5a00448000c6d006120400c1fa00c14a15101c1c644100352603500802941780c2184500700403c1c1c141820900c0c5000424020002ca144200281500340c032100c008546480070094030342a0924481070341c40d2030030003040c000c2c050001840340a00262241c00c2c0750300114100390710102c0e902044101441703034078a44513010018000007414618080c10500008011a590341c004001c11005561840c24151101c04402c003211000f1b0581c08405103498501c400d1501c83c440350115078102400c1503003411450550190261010a50080d00200003103d80700c1d0743c1a00080c0301d0a102c0380807100c1e000d000c505040a0010380011180d4100c402d5401004d480160302130000a410035006d559401c0c54503403038004291800d51030651814199101c80308011240b0342403080075803c00011100260030540401da0960340140d0268900561503002840b0301d07001554180d10408203840507a20503445581c5c08030941c03521000d21440441d14100072002a044012040840340c06400070b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 544470710 1250 544469460 544469531
    0x305011d0303061c02060c070f0902070510050a021c0b040606050906030414030403080c0d120b010c030315080109080d0c0203070209010b0904150803090a09023408030a0906 76
    0x43c10441c40f0b56042d8001d0012000c0004640d01684851008200316100a00200090380c03918000f40c0175400306502071140b062043c015400061030120740ba000990036070b0800301d903e49580c1071807030013807094299070020b0781c1d80720002210b0014250030030700000d28203d60420469030350714000e842034815a442c15501020801c009000680240b11900c009903102e006c0741e04041d00c1ea0344180260340540e06060b025401894802403090744203072030384111106034005000310502c00c030020f4050b00b008031004040c10b86034100b80f103560f04883d6410000f00b01c0302000b84601c1d5030905007040190b0102d444181c00034140758894501030b00010480707002660182072000c641e860300c060f200c0e0541100300140e60158460503150113070105400c090014180c4400656565403d0b0010000c0540301340d0302956246006102568440c031140c1da000c05c2e1460790036500038804a20400302040c505d95034030003d00f0117101105124404503990302982c1028803c04040103105000c0442e0580b81c0c02590050110f6503120 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 544471960 1250 544470710 544470721
    0x906010e010b070503041505030402090907030c090b01210903080f1b09010e0405010e013201050a110604080406030e0f060105010e03011404110301060b040803031317070c0305011d0303 81
    0xc0c8001d244044c00345050320300741502c505003803c840420003a0840015004810f000a45c40c290b050180c000600c0070040510a15554503d2a2102940710301c1244540d24540054264012004050540c41001d109641c0100d40302d280c100901d92904190002001d440003c0e004803c44911540540c1d08988003081031001d051004c0266480724140714100704c040c1191510980340c0c2c0c0035280c040d1822010402a5604010000d00d0540200c403600c03c041380340c404ca403680070144c9214030000ca8020701c1c0036a542c1d0000201a075051001c90807030380d034521a210400051182d000f01401c151041072341c040c4112103500542a41d2114588240c0600360420701c01000290701441e10112101d01c068004142a02c15140f200305e010b104032001e5a1440e280c0641c010185420310a48002d01104411142024100b00700d01d0303a03c2c080245544450905010010b040c02640303144514203884007904280d480c205450150f07036280461104075820760034a9000241041d0400385021070900c40b000441c215582d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 544473210 1250 544471960 544471979
    0x6011802090103060e040b040203060c0a05040306090f021e04050a0605030d0c03031b09090e0304030309060c031403240307180218120a0c0509040f030323010f0504050906010e01 78
    0x956043c03680d11a00020255600340a59104d2401284201c5042c03a20380185800c00000514018240c070003000210755064010007641d0640760091400100c410043c90204000e5042c0364002c1c0d4031040302210322a0603010040300480c4803000340c8060002c0c0d1580600441540c0f82c0340211039168126040d81c1c4040d5200354454812580a0f1074045844403c000401804059183d03030780000a29051051103110b030f050080704018a0081c00030340c0340034a541c500410003003942c0540303c10000c80c0a5810149441018200c0311181030380034499480c10601c1c07402402c00040003500642d200d9402d40d039451440c010961108603034140b840f2030001c140300710f0b1140095000e4076500340500e070240c3c00c143c143d0700e541d00ca0140c1d49155100401100000742840d01711044550300052181a0760810400000d0f04190400c240960504010075070309001500303030004070005029103140a0f01540001400d180200c0310500300c50054030100036641300d0050550301c448007400380c0a01100c140c001046403100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 544474460 1250 544473210 544473217
    0x30a02010c06020a0e06040609140609150304080d0203010f061803080a030b060c1005071b080f0d0e013806030114030f010f0603110f1e0f090a09060e06011802 70
    0x4c43c85c01894083c02940040c0242d00143c105d00d00145000346c0c24090081650309c0c40400c24000c80c0c006040400c400b000600682d840e840c01c0d00741442c044089001c1190400c00d0300e0303104400700429503d9684505401d28800c865126003070000344005c0801e002e01c5d50034118070040d240c0040310340f8078001e100182038016140c0260a02d8014404000c807034000c65007413121075500500341201240a0400c214014a0a604ca6a05901603c0c0307600c41c0f400090103401c100c0d41002000c4080a45400104140e40020406502480199400c06012840c11540e41014110702c43c6803c02614006140e6040a12030360100038140e50000c40800040c0400090031034000e089401c001c040321240a12000120300b921000e082020940340c07141014010800280304052614100b030b03400811422011002801c0251045822900311a11462240d042e844003403400715070f42e401a04005440c1020f02051006000080b01654228544000c0c1d40c404000402d03500d040361048035800010201c0070301480000c0d0f0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 544475710 1250 544474460 544474477
    0x4030501021c381e03010c0207080304050904060209060c0124030209040b090a050d030c0f0e010c060b030f01020c0a060c0905031c090f0602210a0c081812060a0605030a02010c0602 79
    0x1002c45844089546904240040e098149040c55011034004c06050030764040d07000000a5400086040c80691000420b40e1700700d88080b11044807a46a90070124000d11a0044298000d10002410095840150802075442c814002c5000800d80f0100070b03900342512900000707510041840105001c28200001c103900852207009840100030031ba91044d107481e19681000d00440e4680740760b520260703040400032140c40d10905182103951400000240b5811030200010320844d941e511640064500f001181081b8a01074008c550f50000c0f00c4038a603030741c602d107101141c0700c508043e0b0003c3d10364410f00c01c04084a002800134000060781410342e241d16058900f2071001c00c0302c201c40c001140402e8210314401005150090704854024210100400125406080f40c07000c0030001d400205a10020203100036400a41403a01da407064004c540155029041c8240d110501048640c0b924801049640c0070305540c80c0c04001c3e40d5503c07424561504200c803c040d02081c2c034010990080b41840c5c00500100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 544476960 1250 544475710 544475801
    0xf022d0426010b0d0302070f0e161b0821150d030c08070507030809040510080c0114040b0a08061c0209040201031a091f090203011217070804030501021c 67
    0x3a40c0f40c03030100707268000b2030500b81d005a214903010041c4e08a00031500c0003401d41c0841c00030303451409542c40f4529060b404c01e000c0400c02143e003110350341c00c00032203401031450348203500c0c90351401d508501415001c0e44d0401d240d41c00d43c1c03040202d02c0000c0e0100307904440290240200b8181183c5840607220300c40545029294058100141800203505100c04c3e0090341c414081070f911400c07040c081c40100d40004200a01d51402d4960600941c00001086460030109282044803440c40c176042151a01071544070074081c0d88041410204960021949840f03400300380c4142ca44201c652607484841c581000000c0d400511460110300954404e4003e282d1020b0045c02d04590201680042501008115416011f036440c0900c07411030004184000c80040003c440c0960665050a40d41400c03580d0200008129019000000c0d1706002c220081c1c4500c90b822039400c1c0c3d10f035a524100f41c0e0107940f0000e8035410002c410031010352089428410062204103610440685040c40b203001440301204030414140b1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 544478210 1250 544476960 544476971
    0xe0703050d08061f0c1502030f011401030e061321140d11120619050112020d1d0705010e180a1109040c0302070512090108070e040f022d042601 63
    0x10030404c0c001c254405400d645e65a801d510b4a05052410320860030f00f0384a500e00400620888241ca409410f0544860503000001100c1e00380040c0c00401801e00c006015008450400406049070f000c078588942c000e8840190b241c10b0082ca00d0094018800c0d40c80c0424220f07207604030451036041c00b500390500d23113501c0021000350903001110603400c0301100c24000e600c000d0401130315003090a00c4c0c0c51580103118200c88183d04002c0060081c403600f0a070b0300c10255010034541929006500454084004040212401080d110102e51519050f0041901141260f0441901ea00300010701040058184194100580390500d85101800380c0e051802510341040c440f00c04d1607038440c070500f800b0081e151801a41c501d064071b003081c2081c04825031100c10542c2407117a41d07240c0e40c00c11520b0303512a886242040b4901500700010700108951168011900d2001c03c002c111960321150b8080d5020520036220303e1009580c0440304030384101c1c01141650181e05001620314840c001c5181c800f102c00c140042031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 544479460 1250 544478210 544478239
    0x31d010e040609050403090b0f120606040504050c0309150f04110a0308132111061b1606020f06040213090201030f110301181b0f0e0a0e0601030e0703050d0806 70
    0x1942d0745600300011255485041c00b0805400c04254801083e0681c0a5400c0c070600169600c45402603001c501c20f290344640014109035a100104e401030003005104200c0b50504c0040c040c03a54104171070b222400e100f2941c201c030107900d800702041d1040c0720b90307c10401140c3c3c0381e59421680c802009407c0d0b810520000000c0005000304000d8580010384040384030180b85860240711440c00114400141d086c40c00948a011407010403103421a0382d01078900e1591403040a0b034440703e0078420100a0864081c014400640405a0b417110044841950032650100c4107500c4c1c0a03103850003a00e00a5011000a00c582505100b0384c11101350340303005040c00288030906166034015101006d00c40d001c818800001071100e2141e4030312083c1d043c0c08940c010030084150380880c1148008408184007445001c0003000941c4c0c0c4250700f5079443c2c00c800341c2800300660740e5100c8001814810f85009000c44e0501c00114541500001d51100704c9812000419804215403001c1c1c2e4070074000b5015540140514100301c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 544480710 1250 544479460 544479469
    0x3091c1101140709050406080c121204080c0f1f0f030b121020070222090308060301050903072a080d081006080402030d030c03020c0706170c0304031d010e 68
    0x1c00d115070444a0064610f40800700030800401070b04007520a6140010a014100000804200b4002c05481d460300c06075a401c4014501030300c1300728600c011040042d0201d000c80003c1000026003005848a201041c140000c01000c40404041c42c0c401c19401003025007024071440344640b0410182c04c000441a0700324020845071420b51030302c10400e0384881e10100700040584145480309144688003000c1203130a0708070501c140319128020b44903070141802c60401c071200200442d41148050000c110b01d2039941790192283c081104d240f0700c039518080002d4500070001c000c43c0c800315480040408403c2c6106004002c0032003010301d004441480030004910880d042090ad48004031fa6141c0701c3e01480d0008101e0200180d5401c650700308030551041c080162030009002d5204603440c1000304003c451808101d0007405403e24031b0b0518494020001403890708034080915012000c65080c0c956a00c00a106880d8070096a004000030484145805072504421401325400c105241803e840038507080041c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 544481960 1250 544480710 544480721
    0x1e0e03161b031a0a0e0307080a14160515090c190503030408030c0d020d20210a030f020f0a080411190509070f020709020706200403051203091c1101 65
    0x100c43c800d5941c0400d45000c00300d111501d0703100601c50001c0c0024041c041602d5101d000700c88008040480c04100c03818030714041e040c0415104281c0c4140c03615071405040191601204000964450182034820b41c4050101000148280c00d041c008103086800c11003032000852500d81004803880c01c50001041076076080c001007009200785001075443d800155019030600150b0f41c0b100081d0340c000a90b04800300c0d0400780f841c426940351000e044140701c000c0320040c1003070000f030800002c1045458440085500c064050000404243d6040006c10a4410201d080340700d2403c00314801341c0d06010780b01c0c9083c841c030503036540b0510680e400c00320410b560b8003080c404a900d1099a441d4240107505010605080703101d503622484e50f28000050f458622030280d160f040900514500d00d400044800501065400c08524800a405085080314010b403042c8526089070000722018001c51620a004c003020303c00f5207001d81c8080c0081d1404585413400d03004511501d20840084c00045505108400028401e4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 544483210 1250 544481960 544481963
    0x36012c13060e0403020f210c1f0f0c0314040b0c041d0a24031103070b0d0b0405071107140409080a0f0e1002030324060a031e0e03161b03 60
    0x1200000e042501e000ba0408028012642090307101a10700c1036140301f045106450440c446100c3c9a4075008034030050700307198501c0c220421034500d220003002442d203990700101480e00300000030801ca110927001107041e03400c2161612914846074000c01c0100d038031940010303004070725001d4480c07406948082c01e42c00c00803e0302d031021480303111400f04034015446000f0359062950340d42400003c801019401d10b003c45540c0801381c404009400c0d1041103450811440c0090010100125203450044684401500c03042c07441c04d000e1814100071401881c060140710200980303030b20141c81c5603414681841005102a4415503215880c0c0800314042a5a600109261103e0356100d0f641003140250141418901c2240d2a0060a40c075440300c1940c0c1d070120031303030f0780200e0300f2000b0002560036454001d51303504005008a60010001403c4907460741c15070b000c424498812500d81c10781901e5911140c00b1142d034503041880681007004181c410302a00f40031021518410140a003032501402d054015a82c0c46420 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 544484460 1250 544483210 544483229
    0x190f090f0924051305060703090201140c1f050c0708030403050904050901090605070206090304030b060a0b0a08190c0f05090a0e0a0605030f0106080a14010236012c1306 74
    0xc902c44140c4540030705980a040000f030700041e42c52642c1c1d16035135804c00078070340420103a4442210045a01c40c04810450404000410f901d40000340c0307066840c0c038110100442910040c0d8009042445140070b580d100b0405120028145889034540d4000359200034001c501308107041000b82c41d903940e00d00c5010301a46041c4000118024245010030494901a08440640d40914200641c1660010850301603960080b9a0300c000d4640c003000c106903000b2908034445640001c1640702c005075000139501d00c40e0341010302500304072042c10051402c69540084000000b40b109480500c41e9018100402c075025001d08072080c03259440785450260b03441500c059902d1911400704004e03510782082000300300d08212000308541e5107030618042c2e0720311181c0c000405407142e000200d0040942075040d50790028564800c115035000e80c41c01c44445d5060700e000c18049030500040c0d0301c0594410000c4001480420300e486c0350442c014441406020b0a10940903809110200c0c558001c0b200c500440c0004c05100d507 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 544485710 1250 544484460 544484513
    0x3030c0804082e06261f020306270c03181c02010c080f0a0507050c0102120610180e150409050a0b160e010305040f0b0f0402190f090f09 60
    0x103c2418040d981c00d2841c0040e00c0c1800014040aa01c41c1713000921210224100e40c2040000b80d4803600b0001542d100340c64085680d00d00807502c11035074000b50b10604003294003203030043c1402c004558400d852081601c91410301030000c0c0040d06040c00960304500c0e2a0600f5244141940d8078914010304d1490411005013080340e40c2e032480c3d809002da80c4070380d540760a0080c0f482ca003d86003810310650041c03450103400c1e1034101084a40740582c0444030600c0d01107000b907684885000401a030040144c4106008010451300043e0291190303584040c50501000da00301c01e2403620031640c0c00318202820814550201d0481c4c159195501d03c00c051316548540060000111641032a8407904401081034007400e91300100350780c07401e41c0007614500e541000d00f000181a1a80d04020688074101400244800702c2101406400c404026005108501c212600095040300103500b00c04600c2900c601450442518024000d065082d0862401072050403800255041c680d01c4c0c48000000701803290303001d8807103503 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 544486960 1250 544485710 544485763
    0x61721090105071e1a1305120904200c191505100510180b040e04060203130b04030804050c0102070f210b0708070e0a1401030b0a08060a021305120703030c080408 71
    0x400e030a80c0c13200030840512000c0c162601e60700c0e12040d00120a00d800d85001274540c2c02659a580326440d003542c100700c2d140803c0c2000c0303c8004180d0002a501480f0b21074050318108120030039235503000686e440300c03030304411181d402000786c0a08000303050740d080041003030800f1455841b1a2a00561002980d0302c0d112032012000030138502c0741031034111a05280e81003109201070710501040c290810340c005001139895440c4002203000c006241c4004240300ca40320706001c00c0c9648041c655020b107010300c003581d2408240c1d0005a07a1401644038011811304030075020050544400f496209001d48100c000b9100c50590b618603610100440301e003804500708406000401c0c1d80400024800d00e01aa134403940981001050140075000f001c07900c1c10192106844c0406880f6410600002c140820440e43c0c07130706140c20f111001c0e4100c655200301c0e005100c03500107403901d0042c2c0c000b4440c542e204003501e141821610100c40e08216800d06a4a40e042003000040ea40b40c01c10100705142100d035080501e0a600 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 544488210 1250 544486960 544487003
    0x910030204021c0509060c03340c230c100c050102070515090a051e0c041517060105130b010c0b01060206041202030c0601060e040b04061721090105071e 67
    0x41c03c17040380c0c0d0340701d501000385103d482e808072500203d0495983c1c1624200c0c91017003010701c00710401d1a041304000c1910044680c0c00001c8c0288091180748081f0744528070301c2e50340c8200f100030a10106a6441815440c0007814001c401400e92403040c5418030b801110790b103440e0309907480b81d00212010707030101c04845101410b0a190b6504101304101030a8182210b842d220382e908080e43d991300171080503c04941070800200846201e81c1c101170300c01e0102d865240301c034009003480c500c51481d541d1307692008041902d1000c0f940ca0f0603240d00810540302c02c264803100d40000e10a070306010b81404191040d5902040d00301909038000c005541c010000d41c6018035000e0920b0880b100003074203640c8140710381014840c0100301c107819580d003407038129100c84003e00010054030080e6540c5400c036203062404505c00c40c08600b0a50615010000c4410b2021101942c250004010b4283c2e10701010a2107641e00c29840b07000109109400703103080315244142004c9021076850032201c101d5008111118030590543c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 544489460 1250 544488210 544488221
    0x3200403120f02030a08190e1c0311040e07050403021e01021605100c060f1107020f0603010302060d0f0207020402030a020a0306060908031605070806041b050604140910030204021c 79
    0x2052402c800d844030400b101030741d40c0c024031180b40107124003580040d01c03060800c0c0d9940c144610b114400d00918190380409512818004001081d0b40440c60740812154060300400308840c5182641c3c51502c0d14108510803024400ba10420400c04200000030150351903500070f1a02ca0740650b1045103c1c0440000a0300d010004609022800c6980700c0400c242d66880102450607806400c03c003240320198a48580200b100200c0c03030513001e203001e180742e0f803a0792203078040c0140d00e10070784040c18100c80c203a042184500003448000e40c800313020001c0c944030031140d80003420016490103016051481c2d903800034003640c00841d038000c40d4541c00709404204d560b00d070141c54010080d50401420302400d1000458592040221481d42050a810908100881000010003c0000c00c0c02d45030300341821b1030008810444074071040350302801480c000c105481c0030390485040f103a840050100d4841940184010820010080100110340076800005601d070307800100804040b1150504410f101d001100e4102c44 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 544490710 1250 544489460 544489493
    0x60b041b030902010320041725080c1903080c010f020a03060e0606031005060f090604031505060901030209070c050705040905060106110303070e1005090a0311040e0105040206070f0219061e0c05120a03200403 91
    0x8420f82c1c9817124044000c1c2000003604c1c0c0190450780cfd1100a00c440394058222580c440c14282d02c000368801560764142d00c40703c1602c940e9a03000d6410b032100710820215020681c2d0043c0c0000303002c501084075282c1000140366041200380e1040c100f271032443c00628550080d90068920740400d8490114041041c45000d0b4070081c21128681c82d941035402003102e40f900184104140314000714120203211007000304038000c1c040100240b00c414502c0c80c00c035445100a10803200401c0c065100450035204c04003c2d20b1250703400d91790361020100b1039030805c0070140a40c4eaa1006111013040180c18a44848150102075401b0741c0103041980c0d6100140006c541c0c01e20840d41d42645040c0034000166507072000c4441c800e4004000712410400d50000074140202000a1958620801c80000cac0031a04050a004075035400b2000d5000603100320015208030001c0b5100910b150000f000e003030700000240c0081c0044400a20b000075803503203500303244660041c844401607a0b82c00082001c104010040c0800c0602c074 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 544491960 1250 544490710 544490719
    0x50901050d11130e030403060603111e0f0109033e03060406050c04081504050c180a05071b06060311030d0507060b041b030902010320041725080c 64
    0x3410a5210000030750880d0080b5803181c0b55440501291185a401510150303030682c050320f58030740d03692410200900c9548012641c0401c00d00003e0194941001a801a8182e000c405902c07a545242001000424191914140200d180010011405004061f4040022a02e0310409103c1b035244a070959816540e901c4d81524074074101d241c648e00c0100d90039401580c01840400d01e900c50b0100c107441c80c000c3d034015248920034003481040303140c020b000050099016000b5540ca0008403814404107001c2c03202a2481c0640352400304101e9400c42c3e11440d401403203494880c0071424802803500c4010103589080d40e0098482d00244107001c00d1008450b02e40d0011002803503990b0183d0790203040b50290110280142c3d03500c08142c02c0301c0d07c854102d4102d00b0310116026000c5c000c8101d002e401054901016400285001c80b003110a4104121010029403442ca012b07090903d0300c0c1e158040c8401c991202003281c010342002d8500802440c4242e226200340c0700a0707120440c00c0c00e17404d5140214070381559119 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 544493210 1250 544491960 544491979
    0x9060606030509060a1a01030f060e070c0c05180c18040606050d06091a130e030406260405030f0a0c02030601080303180c060403151409010506040b0d0b06010f20030405090105 77
    0x40d4002000040d07500703080c04682030f100001050000c00090b82f00b000201c00f43c40801610540c00500b015059204489516002da1180244505041c82205100d8410b0f01c002c0405c85c52491540034065140e441d030b80016134812a0f1001c20243d407220b50094010070000f08494265030722a00032040a82050002080355410a09003450b240c00f010100a002d40701c4165000b40d28181c03900045007200b201000c40f9512541c40c5001000c5084038011142c50410024240d000b0300040d041c05801950800c000b941030402e079a40a0020340c2c070084000042c09070b6031035840b0040c1c40c1401140d00915103840a107880f450194402c024441c866040710800b60417540303060132169a40703c2510240da030050a4a44600016415400142084800c503c021021601088580b840c1508654802c050550b001e2040b0081101800720341182684014a54852030001907030551190030700c2081c5000078900400c04442c0c240c070003038074141d88484110f0f09401c001340510660500d040b00c203004102c10fa510020 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 544494460 1250 544493210 544493231
    0xc060f23091e06010303050906070b07120605010c050703061104080109051608060906040303110c0f0109050118150207170a0504060206010f0821040f0b03040b0c0c0607050c0109060606030509060a 86
    0xf00ca04050200409129001c217510100d03413124001e42c4c10642d0b0100014000b07003001e8802820080c007401a0700c500c5410701078003150b607501ca440201d198641c403c004190f580e00355502c9002500e01e02405c01c006800074803000030202000d004068401d40204068828442200440d00c81c00d10160420201d90740140b00340031243c5400100160700035018500090b0340c1c0b0a0b08890840c920581c5d4040c8102c1c407030041c0045043c0c07019800303840c06521401c0200160541c801051741c14030a204800b40048000c2c074414401085503070010980302e0311039080905081e191494440098005081030800200c01240902400c2d03010841c031405415074852620a2900d4010b0840d0741c1d24038840340f1a802c03101032020100f201d140000b40c0740a088800405103803980c656801c2e190580048030103903440072481d80400c81d81d80640088402800e5800c000d0071303660799583c20545044c0d2140301103084c00e45d61044c1c07080100c1c40b41d02c543c50217400203981c0802d1a040c8040b0303083c80d01c1e0300581040f0103d07203004001d44 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 544495710 1250 544494460 544494463
    0x121807180e0607020d1812140d1b03110109020a121109040b2a04060f0212090f100207030b0a06061205190b010c142b0c060f23091e 58
    0x441201798601500003448001c03910315034000320707030002000c101d82c01e16400c10070000012200080b0401401c85042c074010f910100c45140801080459501d4031050000100c1e21480d035103039a040c1030100100d8441c1c40c1d070340894600c04482d4000b1140c900003981d04e6041008001c20351040420440f80361080e8180380e1205000b507030001e0002034000c900c148021381c01e40c464a100e25010403010565544660395139501800c1c45841c403810720014010a4103140d1600031841c10788424910103491711006101d070b20180210445018080b1095200e0300000000046541d42d003588100300d0700b20041480c910f08840503003010700c0d40c3d2010801604140803c016050804985080c5250036000800c1d00c01c2e6120042c0d45031025040040c0000744411980c01c100403001036000102d05803444404082503148010441181d0381901c805c1c0090398002d24607000c94100c3d000318ac8646407c0c480010302130318580300d03490040c940440b2001246110f500308090000c0600c0120481103e4105030103421080c00540e6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 544496960 1250 544495710 544495723
    0xf01200c031e060a18200a060314011517010f06080702010506181b0705070f05150f09010923100903021f0c1202010504020a0504020c03121807180e060702 68
    0x404e101c0e5501200b4000c09401a902d604e119081810100364401050403122a0040c89440038016a108040055143c2c400c0c405d80c896158201d18520481e42001e080c3c07004681030303901076010000e444020036a08180348a01a00910780c0040351003003031740f40440240c101e8800900050559140808000e000d407954040d850050344501811005650380d04c0201445ca124807415141c0d840004c6041403c101e4002010380542d80130019040e08181c0d07800030440c291020454280e040c0c034007030014464820781240540501c40050425010b00ba0301c50141c100440e0300314107c0c03d90680481940e202d50b0801e40030600c5c12141519001e8080c5080d030b004030700d69040540a1a1032000d9808107004000d11454030a00c01c00d82c0044101280341d02071200038040c002c282c8040c1d04c2450800e0000805d890b240c4200e5000c69502d00295040c140d6840da034442c0c0d120024902400305600d103d10b001c10002c02d029290180c089508804580404514040c04a8500180c1c40c0950743c0110180142903400141c0e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 544498210 1250 544496960 544496971
    0xb090703091403070308090f01020903030a0c050114040b150301020a0e060f090a0b040312051201031202120f0c060a1a190503010906020304030305061e0f01200c031e06 74
    0x31900450742d00d4000354500c031040041d0300d68080880d004041640c000203d50046010500721038000514240b03080c201c1c07103002030483c1c1c140d0080050046e000c0c0919198070803240940000940121300e820707610008a412501102c200d0344030020040501c40c54004490b8200c4158021800d1aa01d000b006c0d280070701144505100d44000302e16101100c0f504d8045a000c80030280ca40c0c0c102513030301d41208403150001d010440f0462000d0000c40e140c184150305403015140c0d00c1014509076480d5480740c01d44140c1c00303010442140074402c200010342d5101c50050201d41c80340504141da6641458401d410020007801201d205030401d10102608040445140c1c04204212600358495046a100700402005940020b4141d4200250001404590382c06148218043e85003400345603101001c01c4020204c2e01813601d9400f41000503030101d03041000520034146018184891100c241541c141442c0000240107611540b100b406042c250a045c4010450a4060900440d81d04842c01e0b4840d101e0000401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 544499460 1250 544498210 544498217
    0x303031512070f090f1b0f140a050d0e0f12031005090c0a0e0d1a27071502010f060f060e0901060e0d02010e0d03030c030e0a050606090c09220f0b0907 66
    0x24103003400c103684c4c6c1c0201c1e82000e00e403041903144a2410405001d150240b4511404920344020700d11000003401c040b00d410701d405694003460704800400c680005d03c81110104000d00ca0503010044010301004a00d00001030600307610342324039000c101c0c02803076030b800d802160107a0404010301c0f1405403042c064890b42550360038020200140280070982d8850324a80280401c02d01c0311002d40038400207034145020b10030001c10300d520010010051002040b82d5800c400035644011801c20074a105072103030280f540f1086c4004140846d5007801036090781c104e80c0040e9102016007804004071600300159101905007580c51080b44c4d803600b82e016180ca001c0c4411180a000d20741080421a8412206803c41c00f10080c540c2c00c00c0c0340203050050040c92868800000300c4e01d030218850f4000000200a440381e079100004224a40d00d010034400040005820310742c3c031500a10203a01d082c2d072039140c1034460a0800742c05107411108111018107550041c4003a1a50a1030412210629100e03200039950101d0301b0b04 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 544500710 1250 544499460 544499471
    0x604020405150a030c09050a0504050d1116090b030106050d0c1401020313060e0102070906050f04020d0207081b010b04091716060f150816031509020303031512070f09 73
    0xb60b0b81420080200c8415030103110754002004000082100c9400c2d0365007542c003001180d403000180c9003150410344020700103901010500704403e00c918400b111030b00c0d00f001503600769200c3e440501c0131100c45410000d851921490000c240d41024483d00c00100b40c00c855040c0e9900507519061007001160141110048540c0c200040701d074001c10032500706004090214800c41e45d541001040d0402e0ba100440c0140074000c400541030b006c1e80140c0c029100010900b490100b100000c01000354020002d07d56856001c1c1300701c901050f414400741102c3c029000314034122500c50301c00c03a801c552200d1122407040d49817806100200364903203100303604150900c1a1660390203400c0142c0008000044008102908001420030b690400f81c11442c1020980034912012039140e109071910f5904004007401040403140f001c00108110a043c91041d0240800c002002850354003ca821a8030844540800e490740d4aa40700480c00e100840107000071000c03020b803002c0e40c01c00b0340c0b03850f424525228089a094481 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 544501960 1250 544500710 544500721
    0x1050904031209380f04022409030d03020a030507171f0503030c0703121404150507021918111e0d0e0a020a0506070f021e0307120311031e1c1a041506020604020405 72
    0x3402720703031b440200101103803901d0340410300042c0a9405000c0c0200080d04000c04100b109004429800381800c0c102e50f042c1059580d5101c443e441c2890601c8100d40040e0500f000499031001d100611240c0000c6000d04840c50440c1400100c0c0604850000c0400403000c182480c070754100d80503142a40d0440760724610303028001404031264098554003030b6021074440c102480201c01c0d21034038001c450502000c9280d111250110404031a110326110807141d208000140500c212801810321b402c4400500e07904010801402c1c00c1203585510000340103602803010a07080d071038002c02241c01820200c54951070300301d6968548201502400b0000d000351507103126010002d09070b61409050043c003408454140f9501d07040d4182f14880703440103601064070064040039030000402200d44021414501c90798001f07000014294517070000c0e400692082c00704055902402d40d6000e40300031100c501d10305601d0381100004000484481c102d40024480650a081100c00d8011500d9940603404a4001442d560386 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 544503210 1250 544501960 544502029
    0xb07030c050c1515040222060219120c0503070302030408010605060c19140f0312070801061704083f070903110f04060b0a0801050904031209380f0402 66
    0xd1034016030340580041410307c00f001c1061000c0f0080740d058080c803840c0d540e403203905a807101c0071142000d0160000103902c0c80030400c588080c481c03610740d9180210002c80741c0d80b900e60454110500850051f04009010843e1084c02d00880c2c020b0602100c4441c0b91000341c2134001e40e01c00c2d0202140c5200d11440c003408043c000c41e40990210740909000303580034410714141035500d0350702c000c40e03400b0705048038008500072902c035400881c10381d50f80d41c45a6190044503071000c81000d20050084a00a07030400080d45154401c01101d035400c8403841c4440c1c044018801d41d40701a03540485000484c1c1000d00400c100c076940030342c680f41101d401c030303032040301401714000402d40c00b6941c100b0b41a00141040000503400c13050070024030f44004143d4402019989440070001850702c203440180000e400144075010b000b50030b600c8907802910516460380200c00f801031409185d004540b207a54101c10703824440350207201d500c0c60650300c011003544000551621703a0016082403541030b14465001c0100c00041c002841 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 544504460 1250 544503210 544503241
    0x109060f0e0a0603060e1015110a02040f0603031e02060a1e060803250f29090609070906050303071103030d020412060b01030c170a0b0d0b07030c050c15 67
    0x70003030841840c0300e40740c100c0074018020b02e201d130721082620540040d241d131081c003040303005850030b00407104209140c1000488903071075060001c4120740152900040142d40728800c4007801e1740005004034140d4954180984142070f481c100320001071003030301b8040d44550b02142e02507010701c0442c4c00144105400a41e009080384c40009101c015241a034080744206c0008040d100407015540030308125000a400d000b902c0b90704140c01021002c41040c14070005010000710380c05154100d44503544000980401d10600b0b8042e00d4565060300800103206560340107111000c064807043c1c0301844140c0c640700c0402d5892141120242003808500a50003e41e502401168031f510380e00c05c0c0a64441d074407a0200342d0b100320404030460301c1e14603000001c042ea50007806100d1107a0080e4550b510040f4100c154200c058030001c101ca02260ba40e40d034003001941d103815080c50760600508200c41c00340b410200250444a4032180e480500c403051040070100000000d10b00d1001412401076a0141c5510119040760342 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 544505710 1250 544504460 544504487
    0x4050c0702090a1b050408120306040b03010513060b030f06011203022a130b06030a1a03010903110c1210110405060406021c091d18010c0503010303030b0303090109060f 74
    0x24400180400038010b90004540404c40103c130040e0b81201c0e075403e45142c440d61094110580004c0c0e840a64051440c0c05035038480009440810407644c1440043d0071140100c40e40c070310350700036000d0b8001480307907a00c51841e10100c150010403420f10b10303507600c0755140014404c4480e21201c001c00139040601c01e005641d42c590701010240410b07040b03480700b03885058200749003d000e2908a8004890310300d090140c01030030000900310350301c2c684904241101808140d0308200d5000c1400400500741d441c00d00c00c100c541e500a54a00d0300c0c1c1281c1301591410050885c1c02d1900c24141e206503400660804200494007010442c400510085911480c4000780a03a03440701e40d005201285c0054020f40100c0d041038078101c0300c1420000104010402e8a051105028103107000c0480c1c018210b0600240c0301142d00115130740c4000301a00c01d000789450a541001e81d03078a00060021004000b0941c1602030751401030801c0f8061400c000215000800b0041148285800c006000200041c0107010315110040032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 544506960 1250 544505710 544505719
    0x1c080702030f060f07080c2b1104080a061a0f10121401050414100b0f0f0307180b03090316030c0f2303090d0f020a1706010311010806030c04050c0702 66
    0x1807821307108039034031100c0803600103011502c03540c00201b0800031072080380c0c078030b44041589600c02003d601501000700455100313106c20031b0351003043c8019203150b48003810052001c14010040314000380340940944521100c0e45d810360100c50000c00d0717280da030000a0380403a01d080e2007041d4060600c81085585c0c0c0c03003603920b07030480a1a0078003668000755089403541c181c980949041c410070481e10f94400000c1011140c80604108051080c05003d1500340200402e1078554685410041000740309211540191042404100b10500102010005601c010024001344404074110b150820601f0b0f203034803414003440100389001c5091410140613181c40b42000350481c4184031810094981100c0c16a84e50221035a441074074800d1900c400c3c000011140c00c56000343c8100000c0c1c155039140e40d1040c1c1c4401341268801c00000c0013050401120b45042c1d2071b00180d1000700420b5145040540100d82260b5210b4100822079081002c140c800040d080c01e00d5034180d070001510741d5005118010b41c000e010009502 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 544508210 1250 544506960 544506973
    0x1030221010e0703180201080f0a091406060f030d020c010c0f060911040e01110715020f070606031e0206120702030f0703020f150603070e1906080f0106051c080702030f 74
    0xb075104080e1458400c0310b50f0344040203080115880a4040320740d400000f400245014005201255402c000c550020104480030501c004190390399070000d03012610500e0607030b00c03c01c1086040d02c1c05c800e41f60348880c01a070107000d41c401b41100c0251280c0c081c00300a810301002c1c14001c002c000b81d520b0851146038010b9010450b1241600d02a14002c8420039518172640c00c0c20300d514401403040c4101d80d084001401d000345090321982e07070088141c5000300e8481141c0d500303000403a40103039400b00030302c0d80902c281000244903082d49000540300c1c6000ca6031040d950600307080140180c031084c080700c044c0c0c04405881d0307216543d4290105d01d1440f0b100504260300c40c0126110040503000a9500500c03032451054840c009808689504c0315242260980e0745980001020003402c04420859500100d00c0901c400600494a00e894107441a83d42b14403165440f51410f00140c1d282032240001918048a04048084140301d94011103680210068403660b40091404e0442d54200220294a80840151580e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 544509460 1250 544508210 544508219
    0x1f031502070825061d0d0309060e0d020f0105090705060703180812041404020c03031f0308030106090e1513180f0807020112020304030f08150d08091017060103022101 73
    0x30106480d0720845109040c050b24100c0f0f1407030170303c1c09070200c03850500a149000d103240f0100e02411800d401920016582d1400c40c0c3c8084080c44203000c0c01180f41c0085c07203840840c0306000d0031030790300911281041d00921001c1c0034990b65032044907001d03a00f51501151004011060601c03010195200610a2140211103120608010094411035524082040032181030b0004d000076442940d402140365002080007424000d111001340c070410b250704aaa81e0700c0342e01c0f5503d0014943c002c2c0c2103000880e001090406c01c11420f038044c00d902550100ea002c4408220201166508480320352609a41d42c8070b0105100c02030594025842d0b281d004445144060628104506e00c0d601c109020707400500b00c840d0940082d001c40c001c9078010b540c0340e84c5a000400010700204c41052002c1c00c40d00c03548000540785a5240c3d1080114000c050080300710b1070f030b65952103040100182d103901c180001c0c000d600071308809811503d16501c2d8483c10a00300035a41e080010380710000310300220241c07011142000c00224 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 544510710 1250 544509460 544509517
    0x100e0c0f012f0c0109030b0a021308070323011b050c010f09060f060e01031e031e09060e102007050d051513020603070e060f0705061f0315020708 64
    0x501c012000b040d01c1241100c5001100c980303181d40006040b800e5900f002c11103a01d0341d50b00500140c8510140302d1042d035158000c00741401032070761041c1c5510391450082d91442c41c122801507903d0f902031000f04196100545580c1001c45044042810312034080380308a0807140a40014902c1c201c0c0c130701304200c0c1921a15160004261000c0c01c0403140d4581200442e10301c4200c1e505605903030700100f4229800302c1e074031a007095079045000100e0400084c000305440a1114248444002c1c1042e15443c400c0c0342803c600070541c0004c07010141c0304649921014491a402c60140c0d40c0000802d160103c01c4001c030301c0d29924000c4103030f1229800040c28024001440804104c040202f20712400350319280d04c0f80450160100d81d25030010358480c40030400b00e08494000c01101310070020241c50f81e410b040c102c00d2b6120480e08044030640305c2c0d801c1442005040ea002c5200b484100b1a804401c07904541591119032044140d8021030030b4040c0c4c000794030800d020001050300c0700c02d140c0100f0100b1241c041144070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 544511960 1250 544510710 544510787
    0x606050301030605070801061e050f12150301060b090405100305240a050106050405040b01090f1203030e0307030c022803150b010f02120a030e0303070c05100e0c0f01 73
    0x541d2900c4c0303040c01040103244200c080e80c0c12100c075681c0d800140c4001d014142c90000603081030800740002044065001ca59450140110b10075042c410f2036545007004c00c0c000305200014800b40310ba4075110080c4020600c070030586642e03004c1a0f400046131380d121042030b40c60916a400c0034005119445c031074041c40c40d000300d115515007600c0103c410940c40790200e41080d60000c0c0030720790105505000900c0030f07062944c401c24400320305150030300c507103556641200b180382c0094006204a03205c2800c800107250701802600001030004e001140b0341070362602c00400a841c04a0700a22070300060301e40b5a48520880c1d050f583c44002c107409840825031702d25000000d240e03213070301c0e0202003030030701618003019030041511010340100350b000f030101400c440020305210303441000300906050303075001900d140c40320401c084c0d4410300c0e00752103803001140f007414030518010038804000c0c4883c1c03c3c00e070100d0841c400818a0681c9003802c0e9401e81a40e00ca080044e0740175480c2e10384030200c00c0964400140c4500703812280703 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 544513210 1250 544511960 544511963
    0x5030609031c1104030f060b0907031b0203090a14030304030501020c03070308090c03060f09030705070f0608180715050c0f0106030c0927020f090c030f250e03070504060605030103 79
    0x300140380d070190b401030b1080021444071000c028001000851303040503980b0f20b518400c03c000a507000414002959613401992136400003980d0342c01d03070034400d0b011107115030f01d0b043c03980010b5082440c5000007503106000350003400f656645819102da020303101082035501440d4000000c1d5141c1c45420486075072904441000e40000d034000021070784588000c24201144c050240241006640d5a1400054107038080c4c007815061004018003800b00d5010300000c00500302e141000003e1529081d0018441a8007800c0c4c0403102c1c407a0a003031040c01c0400a40841142c200d440002c00781c6241c120f05841034000c0003801c004600584c400041540300661101003560310441030884116103901e645022148140000d2402c1900305003122081c0d214003941004040c8000c160001c5400710304080b8200e00020796200e8080342000c014050301c0800c0100895121400c0344e0750310b00c0101007034035000e40f003402d00c60150300380050740101030740e00c1d01c0600c00307035020308805081444055646e0b00000c100c0c1e84240700 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 544514460 1250 544513210 544513237
    0x60706022808190501050904020f0a050d03110601050411040e0702030d1d0f0f030a0c1415090d0f090b0703091707060311030106200304240f020a15150503060903 71
    0x110640000741e2140c00e06a070f0014060800c10758849c3e0130700c0201d0341c603c3c00079507000c0c100300b10004032692112004201d0350711035034522a02c100d503540a145031442c1a0841c0344524106900369042804150130350301180e6588a001c4819155150160304610504249203046070814945000c5030b1210b414010191050b0400c0341c0c126a0805801c81e01c1c0ca50700384c0000d206030070800813000381d58450202810024003030b0328152102107803640f801c1d00e4a8043d11848910305d0301c0784100b2946200c1030000c01a4404103003002072010305080c0700100110180d000306031484002044d488241442803510070050121070910740d150940d10740d01c1d20f5a45480741f0030600080d091407404214505000142c81c1201c005842e0010002681100c1c00d05075080c2107840401032005101c000350511003c0c21904440e480c85510f090030924801c801085158240303210400d55103ca4080400240b180104141c403031900a0300183c00c048540006d50200c069a00c420791611540c000c1c480e881d1404402821511381020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 544515710 1250 544514460 544514491
    0x1b0e0a060512010c0504051207090e0a02100e010c2a0305072c0601110a0614010f05091504020306180a0b010e0d0308010902030a02220e01080c060706022808 69
    0x4101030f0994000a030700000145042c003040016050000c0103406911403101581c54154844201c3c0013100c224440520007036114502000c254104841080b5500300546007075103107021880c002810420080400500340722190400d4050b0ba0ba116003800441490407030040030440c0d4900f0069520f41e481d00460303010410210390a856030040d00c4400140200c044021744907076039003000544081c0c6081c941403031280241c410a50026000c1d1141003070030510748403c00300307650522140c05074511594004070f0085115900384800d060303507201d150b20004c6084074050707a40d80c0c603000800c00034038003440d8120010500b80c060004440e1140c00c803101e0302c04282e071000205100501040000d0102a001501142c000d1005101001d0310303400841d0300200790380d00035150030203184400c50340403003411040c40340c603010304014010055904080ca0050030408020101e83c2484c40018070f1604c41c00350010003070360740001e09034000064414a86121800400e101482900f071442c00781c000c1c40c00b160003800010307201c0e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 544516960 1250 544515710 544515739
    0x60b1204050d1d0f060f07060f0b040506010c231614010c241409010504110405011d061203030106050a020c010f0f030905070b1804180503071b0e0a0605 67
    0x40c080044030400380e0b803c242c51101a0b80910441c0c010441415070404800c201c1150305154035070040820600c03442c0d0024031821084a100304481140e03440d144202c0c2413000780407030390ba84901c9290115030406c60700c2c8100c481d0a01d04200000280780d0b600034a0154181094001103024000360807520702c0d213002008010b89000445000c01640c500030700100c541000c8554201c803c000e03104842a9000c030016040000403107241e8a50350803114040300360b4403001000108103150180840000042e9818004c5504242183c4040c0c81c01c0c00040340010000d038000b800da42d0303030815441804c41e500400d8070f91301d503100c003401000c1d03030f00c0f1505050240c8a010009501d9510031007030b0185170942603564001203104918100e01500d4032101c155203030322500c400423349010460040c4104000700da10420441031302d6085c0801e0b1030240c202c006002d28040c02c0c4001207400032003111841a40800006404550048030b18441345c0075801a0700700001c018100011001194084420780c0c1040303480700e003280c000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 544518210 1250 544516960 544516967
    0x20090418020d0305030c0c15041b03020a0909051203073c030207020d020301051005040e060114120703140a030801141f0909050408180306040b060d06060b1204050d 72
    0xc0880081d080b40a050352a40400e1284002c0c0d504400740c54615480c0c5501c0e0070100b45010b501e0200c0c401c2040c40c4405010810003502a000c01880105d6000b00d4441e10b1900002c0d61801140b040b404400e455801c6001049000d1140203060800f400b0810380f03c0c10603020044c441000c054203944250b03546605128030074030303a040c07031221340100184506212038440d0048000e50084441241c0003400c0000f072100680c0c0c01e000b11441038003078a00701d1019528040030003050740c1e9504c3c5444003e8108074018028003810820b0004485020740302211841284841246003004075400178002002d00e00d00c0d4407544d1004034088140a01955805100f43d8071102007405007141c21031304581c88050950507032003200410380d001e61710150f2420881c820310364070400744059410031201115000f00000701002c0c0d54042031007c1020a0054000b002c491600b0341d50382481034030103403c5134030440c0c0c00f40b10002004040d422541c06003484443c816140d50503520b1142e545182928211808d001d811307003800c3d00300d10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 544519460 1250 544518210 544518251
    0x3031b0b0a110706050a0e062802070c0b0301060e010f110a022e030207020310050c0d0207020d0f0f050c091e090724020c03240a200904 60
    0x304a030511105441d4a80c8103802002e00103030000001d00c0602c080800f00b0700b01d124084c4614842400814402e013901c1105080a40062940881c0703c0301105244200d2002810388480806054005998403001d041509200086500000d1041c0d0004008070704903078030444201d060b00003070b01d40d103080b81c1e40b214003901c10342c0550b01c1d200c5066109100c0315015150a0084080f402072410740f82000c46400c0104a10071310842c0a120003207600007550508508040102d0344e002c0c204c0c0f00041085091061510425110351a01a180a900820003c0542d61054101104507501c010b0048109415141004811030100700646207801460301c29a400d007040300010b4411082c108003090f00203091101c5116240c0054001c151521403101c000c502c141c0c408c0c02102c40f8103905030140c86003c5508800a00d8883d00ca03074054001e03000044003001940c518062808800d074844040055a41d4000200004043d0060400c4200218540346061114100c1c010702035580c0c01e81d030078417010a190000b203042c0f08 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 544520710 1250 544519460 544519463
    0xd12030c0e0f0d030e040c090314010614010f050c06100e0a15090207110405090303092109120c130615080405120a11060a1d010e0715030b060301030c03031b 69
    0x11904220b003000c0d4034050f80c01c02c0f030040c8281451a00d00341c0703a002040032074040c5192540440d141c90b50500900c0165404142704d400c040009000ca981040c1d10b032407080c50101400b038144150102c00035140c602800a480c1001304000898441d0700d01942c044081903101d200f01ea100e100c3c0e8101080c504080e074020646402d01d0540d00354020752400700c020009520881098607000c4545249840b295100d024550040b16504000c6840b0300341011503a0910758148000c0e26212a0111000d0900312404240c0340080811034004d100c4a6011b02c0309828941212151a40016800d00195070f0141d958005004e464090304140c80c2d88030003400c280c40d50b0b00e0568015016a1000e03549815071180540107250007007040c036218880c0d5080382c03800b9241c84400e5410f01a0161281000601400002c00f00c08481c06040000c0c00012403844400b5192081800750322040b5202c80c4505444c0c5d4042c0d0403601c401364001d0130903640d1b5a03490403c4a8100814082100000c41600c1e0b001e0100710505801c80c00c09 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 544521960 1250 544520710 544520719
    0x9091609030213060504090c03140a03020607120f0c02060702160b180d020a0e06100c03081f0f092304031e02120d150e0c04030611090d12030c0e 64
    0x380e0658082002c001526240403403910b485100108042c0c41d14011140c2d002d21030391114030403138190302c6c01181315480e54401e490f640c0e00c030a83d10004260300040780340d0807107203504040b840c62503412074100103048501d0030702030300c0c0d4280590545400c0e40020060701c100415401c0e00ca8498030408104009012440789051543c42440015889802d140300750000000043c20300d00000515030118038450031070781c00380e1507680c8443c042040600b0300f06a5070b40c0d0322885181c10346160381c081d50042c01800300071f0b001702c03207889003000c00343c1c10991f68001110203481001c099240042d17407061044064004c0e4901041848203c0c0450546038060340c201c00e0041c1da0544681054120340318030801501c1d5203030034100031032040050360100395400d400200310072030107d040442d04a000d4280402400d129a00642c1d40840070801c0021081c01001668240c0303910090114904919070340081540c0108140c1c90f030310461800700f60341000807034164105140d00300d4405001c22041e00d0010740310f44030384008a0350072 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 544523210 1250 544521960 544521977
    0x121b0f2a180f020c1606030f1407030e210703180501050403150f0501030305180a180903030b030d020d110c0f01030c1803080913090812040201020a050a050102090916 73
    0x59605400074031210402030001401d01e00c3c1c1001c02850803941001e800c3c15203d41030402e01801d5414001e02041c050007523170074060700b14411100e42c10503c0c01840740d010560742d601498002079090108244001c014002d1808110381d4081d5003940e42d100d8001200400d405059070030b40c24900089413000c84030161101401c10b4519121001035910110004481641e100e5400c0b00c500351f40d118141c0030318000d544240e180e45078882604140f40030a000130344900b224840400003100c900c000e80704003595014000c114500c407443c003540a05513000070b00b40e00d0b000c2e000320310800c2e55001900089800c8a41d44001c044450b5403101a1150569029603420608004040801d54002e03040030b150207145261410202d98807041ca00c08c0c584060300b048485200c00110500f45280c00f4a05505030b40c8120400c1080d500381752b641c03104a00c80c0c4061603050047e41d50014056a009104c44180d064000c0142e0b15011503a1a00500035440706440d1131050080c0004258085c0307006003405c00c0c4803000d441d854003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 544524460 1250 544523210 544523249
    0xc090509041e080d021b03090310181e0b01150f0518130b13020a0903110a0e0c04030b01060905130b0301060b07060506030c04020304121b0f2a 63
    0x100c800c02e07450164622002818000006000c01c0042c202c40c10005001602c131099140104201d5406820a81e0700e6801070003280b00315030700890010119511000e00141d00076682410254800c1d42c208040d00e210241d003000c1c6500d00741d0484c0700e05154412000045a0303a01c2e0b4a030032180c01c400040181c0003030190510184924099002821010070300120b030026000450009464101a1003003a01c5076500d50603408441d0030701c52000680184400015420a45103200040c000380d401e00c0042e0021001c409030310280e40719402090007a21041d101104030345040007031034840741d100d440304a400001d80c200010311144664001d4040d140000e01001c00054056129030140004854159065507900307800141c8003804002040824403841d800714440c07902c7c104141c10241440c0001e40124010800c200c00a154507540c1e0416040310b00f8513422141c21b80d68201d9904240300740042c021000c2c46602400d0200c03a13448583c0e003404602c0d140e021151451515955002180301d140c4401d2002c50b651003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 544525710 1250 544524460 544524473
    0x14060309031e0403020915101e0302070602091c0b070302070b0601030b18070f02060603011505090702070f0905240306010909050a020603070e010207080706050301030f031806020c01030c09050904 86
    0x740c480c82100c001c2d424035483c2d400184001d01c0c180c070b104030b4015201c00c501e151400c140c80060a00c0b002070030000042c40f00d800381079200d246400c0800d400c050f0300040103000c1010503030684070340c1b020142800654210908900d4100d15403400260740080c040400900b0852103402128602e0703600c10b050800e262a28001903014185c4040b82075440b4800300007801100b01e8101400744613400650720894460100f42010b410640040c000724084d0b41001540c5c0410f50010800740100c2d1401d451228585e40c9124040341003014641010028480d842e50004880710660056406905044c0c00d8031507000300018400782400c0705840321600740d003016004026041c0e0b564002c81069002e03034180d076000d00c0c0c942c0c00524260700c22104070001c80d100400340f00d070b1542e0400444000e048150001c01170f560800302d024040c0c0c001444010120403035000f4920415100d051800515030024540003413003a01c442010307484525008085001900d020f168107034070b0348658262801c131080508804c0c2c2e203840703030385504 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 544526960 1250 544525710 544525747
    0x50d0303050a0f0c0203090a05180c0f1b0a060b031605040203100317030f061002070b0a090909030e03060c0403020d060203040816030801030201020c090114010309050f0109030201061406030903 85
    0x110b0070981d032114608003a04003800b03030303c40c0c507003d41d40503544e101c0884042000c0c158a98101a0007441d132081e043c00448000a80c06170021040f0000c4ea45409844582400511801d001c1030041520f0b44254030292100041d41c071846c0b44203150510050841d14103040c4d40304e414801c56170058009a400b04440d0078280c0c02160010002c0ca141102c407603e0751118140d03035203d00030a50200308000100841041c94180306604050111000e58020b002c9110003550703404640206e604802c800591000c856000c1e041000003000700c0c807002d00c400d1a4606010b0704020480ca580c500074001c2000040b0000341300411203040c0d9600a0904504143c10f45070315009401c0144200c80142040110410605449421891040c802e50300c02c42e9941c103500c002810300f8400080907000303440150041c0070700108090000c43e010028030b000a08a626401c0503403038103900c0c541100b0701d54a0701102c20203165040d0000c0b01070b62042c10a088a00800074188001031100312aa15a150010302c540400c40b40d141441 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 544528210 1250 544526960 544526971
    0x150f0418331107030e010905060f030f10080a06052d0411101403090a06060b040f0b0f1803100e0705010e030316150b0402030a050109051003050616030e0102130611030301050d030305 80
    0x704400707548600100c0c2a40c0d20440c0c0c0003102c044007000300b0002c20607001105034010354144518440925203b4090303619400d003000248103546404c009146180340c002d000314204036070b84c02c0c020450600381c2204094641641c0988801c02c98a507201c6150030144251171070a9110307a06d00a05402c1741888811a402c082c08080c51801868111804501d280c011078000c0c1c186040055916485c1a581120001040d40103c806d82001e0105020380e811a400b40c40e0001d6440054002600500b0300090410843c3c1c10300440c40b6240181c49508103034006082030039640203032200c9070a180000704160b681e0158002003d01111031101d1040001d420302d091510080680c0800300300b58404800080581e00200c5500410b03a59400c01002000480e001d02600308910b900040c42c101e045460701030f240d1034014030840140b050070101c41e213540e01c203602c40c450750034820380215105c5044040b101031900f0288a020001070011140300c000513800310480307040361001400c42d081d240e09a034040d005400010b10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 544529460 1250 544528210 544528217
    0x1050105071524091a0904031b08090f0a0b0a0e1306030812010504020c1005091e0106030c080607020c0409150207031205150f0418331107030e01 64
    0x14800e02402c0c10703001d4180c0a2011007030441580c182c3c0c00804440301599400101d4541c00c044820f0108070880002d031403011400d03185100240c0d2a420240c50040142c4a003124075645041c24100307000c1c800d0301078040c0b5202110f0402089225604001c02c52146006008050008102840056003c0c10100001c4a8090710801d003120100d6030710421101c0c2c940c801d9a020130002504a01c0040071006a4003406c402c540c210700b410440103031940d0341c1244010321000c4075a65404100160740c1003048003001040c504100064410804020f40038000c14232044a421b101e244010078025408100148900380d03d9004120b40c0f0304075010400640503010069074080b00409001c0c0c50715209000804401e40262036820390340c50140c025408a0740001c1c08040302d000d64030301d50001565a50300120700c110003102c0114200e090b02410b40c40750315040d1002803404030100900450444040e14406510072010807005035441c3e6060440d00340d564000d04142c40d91010000b21000a0040c045007130b00c1d000616 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 544530710 1250 544529460 544529483
    0xa122007080705060a050124020705190905090309010c0f1e110a06140f031506041203141e1308010f060302030c06070201090e0c16030809240105010507 67
    0x1a4500055001110a0700c004200103500e2080c0041006001d03000700708980b0800c4998505140d1150300203080c0c0710350494540240c0d00281580c801c2054034040c02004084c8402e0940b402c20701d900b0b420952141c510700c0d5090400084407440b01006450f224441030315951804503459a55120111048078100c07101c0c801c9918a05841c5003586106602c41e114080d0240504105802c0140b0010143e112108020414480e28455038402c01a10b20b4003500c12019034407a25503801c08160740d11412405508841d001c80c0c00600d0b2180d100d240e03800799020fa11a52888460030380240910710035094150b951109600c02680c8040c1e10000404402d50621010034a09882d045903a09507440c0b03918400c80e180d1241c000b07209519052045416070341c011144145450102d0307001a1504095218111410241000194180c660349040b100700b1884c54690141e001c20520300680315200c02e0b41e0f542024841c540c01303401605010707802d19541001240503c6201c2c1c0c6881c0045440b5841094101e44055a50 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 544531960 1250 544530710 544530761
    0xc1b0d0b0a02160b060405130c140f13051b030402150a0e040501240c120f1103030103030c030813020d020f012606040c020d0c0305070201090302060313050d050a12 72
    0x201c0b0b004030441c450075030380d02c40d4248a406c2100340c50018101d501c1e41d1200c6100e0320005a406e02410b0121440304256106071070107a00080c41c008140341003035400c207410b4203500200c3c0e200755100038403030801150820034620040130203a01501007201e0080d080148604544040c0030002d001d41401c0c0c40902d01101101c400038081811703628281e0182c00c185224022819a01104c41c101040d0100680b9150103c031b100ca44642c01e2060010300c010b01403113950341c041103400d4440d030b070b4074540c24224908030b0b070ba00d50b56441d000f450950481c0d0190002011403000c6108000701b42e086079001a001400e11100c50659000c0015000d01160307150705210f1402010045500b0b03141c1c669030150710000d0b00d8081031512034107100030355000c44216030464000d00380303c5000603000f40035406195010329015865000c603100680f12185241c002030343c09200801003196141040c0909000244214181c0320842d81001066510380141c1e11141d0208002003201410310300710340d015001d085000b1802d6240d0341c862 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 544533210 1250 544531960 544531987
    0xb0c0d140d1d010b0402070c030210021608030a020706031e05061c11130c080f0a020f0c030a0306080309061e0f040806160c02090f09120f0c1b0d0b0a02 67
    0x30500b2114142c080d600000052000a110341981e4140c1610305600e400380c950f40303040460066020080c428001102400070643c030802800c1410a0403c20000b44280c0300e40b8641c1d0f6940007040f80000511481d0404601588030b4090300fa0782e040f5141c2c5900340b00b1030940c50356001d00001400507410120a04051009100ca913000703070000c43c080c1059040c0da07180c2e0024407668134100c1030482c0026007400c03000340450358021070141c0c2c07148100c080c01031551500b8400c000030b80700700343c144906d80c40b0100f04110b40c0d02c0044010088101151810884255105c0702c854590041203e035070352002003800000c45c010b00b0046c05900030802041950705d4401c03c80106003c41d00302e0f8001c541c3d9680300b0010400750203221661204000c090f400e03c1c6182d0110341e0300040c1540c0005001d00450b02a81d404500c0429040005c24040c9991500c840d44480420308211800d030021103c45442c0e10442ea850801c100096940c203280d040040e261001c911317659221450364120250090080310350030040050504103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 544534460 1250 544533210 544533221
    0x803010920041412030f12010914040b0a020f2b0e061b0c0a08090a0801060f030f08090307080d0f050c19020a0b070312050c0a210e060a060f0b0c0d140d 67
    0x403440541c85507e04041c4800c0640c0580064403000e1904149018002c405c0000650050340306030020040da903000b80d04400b0303005044003503065110210304800142000b140c1442c851101c4540e040d0164070401742d4800780d070680d44039440d090700000f003c1b5002509065038101c09034413401811345480c540c410100d24190841c00c09a4900e40c02181070205841d243c1498001030280b140240882c504100c403100810ad41440000c20711007034500744c03d0802840030300399520300800074299841159150321140c0c4889554410f40c0004000002c03600c482d9024030141e607041d18a0200811031080c901c9819510b43c0300d0340c44280d9100b02c8002c00010700700080300003400c64511039518551204442c407001d00a481c0043c4c40c44001d0032040c006c1103002540b09004524848140c101680e420f02002103190090064641018807030149100f0488a1701c8542c1001003240c1d9220060721040c2d58070b90b0100118000e406031044580c116009800c2e03100d00ca2500303000c1c502e04d010315840c40d0246030b0200900b140c0c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 544535710 1250 544534460 544534477
    0x1f1a040308070606150f09091a0306040c0611030c0a080307030e06071d09010509040f0c080706020f0f01060503031207030f1803080606030105010e12030f0304080301092004141203 79
    0x50700e440e0207200c2102e11445c000341da4060f5003001d03400660b51440c0509141124007032003100654808600035200306400c0c6200c3c9801d0003034159040b13400c050404051840e90b501540000c18569008c4008011001040380e001400c17440103441010065610342080d64009040e1804160f240c01104c0c0b0701e0702051041074081c810a0b00da8264119a1082d00400141d03032a820611640c05600101f041e80c0b00c801010341e00a0b0b010710303142c01d40034003881d05152091141d000002c040c89190740101e94150005102d44c0f84d402480100c582203a201c0b100142030301c50700d00400381c00da0000e001d00c4204625560070103810404505002c1550810307600c80000b11040e18010381501042590803106060300440c15540021050b01d02078915810140041d100d40da400222901585e80c09100c00b03103061090050307580f09010b07140443da42c0d080c01d0074881c880b90020b0040e40b03441450402c9801c1c507924200d2003201d455a060b010f00d42050700e8003840840c500d5200c4106034001c8842c0bc81d00100d5401400208102c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 544536960 1250 544535710 544535723
    0x50604051341100f0b090325060806060a051621080a150609050d08090d030903021206040b0403033201060306061b2405040503070201081f1a04030807 66
    0x2541d0480040c1014030003400840f90303090600300900c40d40e140320341800c0958404410060742e070050400401d20741440040a1301600a041e034088444100c0000210121842d569490220380c0340c203402c0000340e1007070408010101d40b08000c03008008102220805d9014007601c05040464103440b9040c502581038403a440024007900c04201c41d00c0c4591254110161308032070300f00070060403380050304034103c50150718825121003a8800c00c0191032002c03140c1440025040c2103a05446240c003500130721150108901c40c51002620740e0b81c9840003e8490303c119003011001c9440c3d12152002d40041040c0408070f003200000080035030000700405072070100034859052501300c039850294010100e030420b4106504004019590440455070b00f80d415410325000400d1820401143d0802004070940985172012141031804003c00e210000c409040c42c94001c1e2680c0d211681e4220142205904061103083e0315207a9400c240020440f65a08290450000c0301301880c00d5100d445034001a003001e002181c00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 544538210 1250 544536960 544537061
    0xc0f081206010f08090a11030a1e051504030f0c0c0905040b09010b0f0d23100209041b0c0605040303110c01050615070b0a0203070306030c09050a05010506040513 71
    0x155912040f260051942c501d00410181011540b050300e1700d03c01940034255203458444284569024090302069a901100641012114a07002001c00d0f0200e002031f15503010740f041d108a544d4842c00e030703580301c0da0b416500c0b18444e114220058542d1144d44400351061081800042060740c0c07984036490007503000300418140d40c90551001c500303440496158a01501c0305091016150301d80c200490036465205507030380c1c0c0440c0c0480c0c0f6585601c129201c00e003803034410100c1b0742d86064081c1e8010321003403e0aa406000c210900540600031120101d00e01001420b0300400c80003045042c2e0096800504c01d280100d42000c11054408564004044416460755a0824007800f46071035a055101d083e13000c1c203100c0c144940d58850301855176004144517012500000061041c41c42544800b0180d41e11642c0e010005444110034401030000300c6240100302d19100000c151480c0840a0314101d40c8010301440012000316501006007604164024031081801c0421003201040000341150403904071480a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 544539460 1250 544538210 544538221
    0x3040b040b03070c1a0f0a06080703080d0e0d0c1b050105030601270b09040614030c13060e070f020c19090c0302040317031e0f13080c010603030504171504030c0f0812 73
    0x1d0311b403005031841c1c0c20f8600c2e001c4c04010700000401c00c00d044170b8001b540c0391340b076407010402c2801074001d542c0c0486280c050780c0e255814240d080842c40015074000c900604e0300000d08882d20745825500e0140302e001c81c1d006d00000d070507036100e004203411070a80350384007a9540c480c0d0030a0006400c19074200740c00403031000c582e02d105400c1610855005025090368829a6102c02c40440d4444440c0c0c0d00c1c090203420740b02c02d08a4161100d410440080c01090341500940c40c000a0003405501500c810900500800c4110740551401003110139100c03a00b0100369102c0d501e0041510001d03c600448003040c16024000000802c0341060000e1001c6019988140c0e2883c2601603200e0703424080c00c4214440741d500052240b0340c543c084041e90312154580d141ca44400301c0342416040f5008400443c02c0035801c0a002000301580100500111021444694008952420340544510524504102000d120310018011038401c3c2aa01e42c418090304455150110701e07220000c2c2039000300544621114400140607 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 544540710 1250 544539460 544539481
    0xf0d0501091b05040b040e06060c0607080f01050f150318030d0b030631020a08010e010c021e15070e0a081b120a0312150801061703040b040b03070c1a 66
    0x142d10b07400c614095103007600b010404040390140d401103400040310707140020202e0301c03a03004880c4250074102c01c55003549001c0a000380958800c5500c0000868000300005e09400d02e40f4400503940310061100300180500c46a6008580008200700c8924800248403004003c050005015106803100042094500041410300c1e1030030191001aa490f903500490701c14113100b0b0711610040c2c0c4c96105225907000c5600002e4a05d0031940c02c01d585030f500e041c0951207a03280c1540245d0460541d9000d9030000420081110b11207404491080c4154000c030118ac8407404a580300c641e072200181c1001c90038800b01c8404260007200d290005c0050754815801d0385508000525000c03403844c400c0b50b00c01120801814070b41e4582d01e50020090502c01c0310400742000070031503040f640c081400c0d01e010002d0b40f40e403814500e000e40291300c80d2400d0320600311810f00180c035001c005c84041d25000f80c80c640c642450700311900d8881d8001440c00003003142e00035403580080d00840031402890060b014041c00703070a0810301c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 544541960 1250 544540710 544540751
    0x70c150c020c091503100c020709110306040c0819020d150f08100614090a06030209100f0b070c050904331a240702060c0d020f010203040203120f0d050109 68
    0x94100c80c4110700210813554001401c6c100c1030a07091004a040c2403203001c00ea2410a2582002100340d06008410112100d40d00145215503401c540600202c020182d06460700d480c192507012406101c000380c80b400314401e40007480304000e0001c001030032a6040309040c4a042850300329244003025500300b0402070368200002d10300c0e004e401004200f8185031000701c05803c03544101c021301450149000608100382a4401d41c011600500307240101c0c076080c4c0310f0403448400c2c0e010388808460742401c04520040b03040161009198400295000780d41440e00304001d034640108116011104048100a8204609041a030064080c0070b04294012400c00410035511411306000d15800b091200c003901d503403044c0d00d141900a0280040c501d0080241c203a4a043c0300ea8071010b50030100004d10841d0041001a81e540b94403156400d407071548140000460a070702c82614003a500d54420f1b0590304444403454010800c035140d010540c4e29204600318010240d81c4e00f40e02c604070166507454881c0c1c0211580240 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 544543210 1250 544541960 544541971
    0x11d151b0c01090e07021c03020c070e06131d0d050415050309060703050613060b030906070908070302130b310e120d020f18130212070c150c020c09 65
    0xa424140c1441e00020035150080c440d58064a4070318000c2100c0f14003e000c0140182c111030100301100701c4408001d006507000160784a510b12620f9030024080303a05180882c010b02004000303c0540903201040d074041d19100d0710b44940c0211548080403440d0b410400904000301944995480c0c6181015440c08610402400010722900b00204888800c000c1000e5502400c0e45c01e00184a440d002c0202e0004602c1440425034903180100c081022482e08014500c2500c10000b120b801c8d90365540e045800405c54845e00a00b035100800510041c43c14008010050040b00e5000402030b202100003451140c08051134102c03044d460496081c1071400000003a1032111003035082c0048400d0b04a007a64510546807081e51241c404124040030100036011112042c108107001ea8031084408403a41d0301a100c0c0000390301c500c0035142c00d00348444d0107009440c01510650040c095603503511500752100d98407135804541c05c0d08409140742c1403829034403c5605d07441043c3d0050143c83d0701d0009101414201905 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 544544460 1250 544543210 544543213
    0x8011401080f0414010e030706021801020102090a0312050f16030801150c0f1e08030a0e01060b070803070c020a0602010b28030201050f0c070e060f0406060806011d151b 74
    0x1c110981c0d810b0403055070003d81c003d045005007001c4072500750042c91044805c4886010002d600002e001300c07500504002010124102044054100160301302d00c1940401e54011000c80001c002040160b48014144980c60401d00d140170581003908049900a41003601304003c1c4000341000e040c0d12000d40780c05489815003945034000c040c3c80207410715429182c0145100c0101c2d05003401c225283d883c0303007140f01d068a0314142d1600ac61609580790f8108032000c0d09031a10b4000d042a01c0c91050084104486002c10121303c1c0c1003c07074413502704544c0014550418880c14090300401600d507142c0f11f10007004503034000141c182d610f20030482005018982d032080e00025043e0078600785801c00c0032000316075090a005581d0407024010380c08a0044082001d400e0180b1100050b6007440c82245600c0742d41c040719800080501c480400c0b0480b2061b00442e0700160b02071001a0f5254001c049200010f240d800c80705c82440c6910700082d0000d10700a510312a1007102143c0c03111004105120610031000000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 544545710 1250 544544460 544544477
    0x60e01020c1516080307080f090d0f03051810150b0405060d0b0d060c1701060513062006090703030801051203030a02130504051501120b0901030f03030b060a08011401 73
    0x1000075011010030a5040307036950340051800760f90b100c010128448107600690b110340300d2525880280990303c0c102d448824540c042d50000703d24201c0400c1d1110408000e80310412101c1100000320300504004110010750300414108145101c1c04020104c400c6141c110003190034812015108012401a40b010074540e10500040c0815541c51003616040c0d43c6400e000240491010700081584020900c09000540792403059519541c1c4140c061f80c150031800c6030700044e660786004c11501c500c5244219290300300310341018040796100c0c0040d500415003003418281104000c690941c1000d80550790040c03075512200c030401c10150440f26060040000721070654503004450121501c3e480f00070003511806074000351154141c06040059400307001d0180082180d40350003c0340314180a8400c0d05c00d4041001240c02110f25051030041502410014120380820391031a6511104489031b00f50440505441d02c0c40b43d403080c1c45002c081c00c0340c000c20345c1c1c90f00341c194509002042c4901c60000030604000030003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 544546960 1250 544545710 544545733
    0xf0d0605070f09120807020f12060a0c0f0c03110304170606090a090305030a0f15080102120f06010c021908030319060b040506030720070801020a090504090c05190503010501030804060e0102 83
    0x4203500c1245822510703c640c4d9480341e01c0050300080d40b00504a9010644013904400f01d040000c0d02b0f40303d0b0307100200070455540c2003d010b80d2419401c010f9140081c2c6804003507400681301e41402d0100e50503050446e410540c03114480c14208551003120400c41d07200c007040040074649202e0554000f9054402040950b556841c02041444010154040c0f03e854015400e0240c43d03d900000d0b034001400507442990381c5602e100c5010354000411100c5160fa00303804680c580c00031880c83e501544d016106d803003000c1c2c074550910401042011140c01420b0300c59200040c2500140011072207140d40b17000c014000490014800111b03000e43d0825404034105010520403030b02c9180850360000c6a030700f020242e5050b9191100700680384941c1c00c5115001d070200001c0c0820054001d02281602501e500d1b400742d03290300621003250008403025001c0e0314400700400050524401c1c8444a415185168480940317810100342520020303031003100d211000080400c40c07194030402000c01c040342403014080500700c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 544548210 1250 544546960 544546979
    0x90809042f070209011a03010e091606080402040b01141602130507170130110a03061d03071208090a060603050c04050c031b0a121503061121060f0d0605070f09 70
    0x5000d2407502c249d0703240100700d03d40340030040080f64a142c541849545904c0d01c500071701601c01910202e020340d00f400c5010080c1c2d800342c55000d9040940c42d241038144100801c6140350400d0f4400b0591b0080c1c04a003400500303004d070740249445065503440750751a03682070416203042000140d110b0290241c20720041d00054800540707030781004143c10701c0d0b242e200960381400d00d1018404500d90394440484480001040343d0354022200e1640e20004500c0304d0203692102540380c0c402c2d800e0040940543d8415518a9401070405540015405045410000942e905c240480b64540c00980d50740d401388007856064540b40c0191640405600c0415045042240051400c0c81d03c0f408005115000030582400032841340780c803030104a101c80d105000714000c0d90802c60760101e4a000507515079090203070203d6032155442c00c40707124050318141c2c08450848400c00d400d00c0d500250282307a1040f0600302c4440307580e0307030314038071851140c014080051a400c0c010000b401605004280e442030001403441040344201 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 544549460 1250 544548210 544548217
    0xf020309040c0e30010902031005040c08060f06090606070b04020906270103170a051602130507110d020f030a03111b070e0109090809042f070209011a 66
    0x80956002c07681000469080d684a00c6003075019030812500308104080e0900f8a102d03054041c502c5490340d2400c40614030480c00e8545c1c0e1320000e0340607800600c00035900da240f035100c00d030b00c140180d000200032074440105030b04099069441017540c05803035081c400705207006503406400050450701c0f80d2400110b07a036401914680204041c0c8100140e0f00002c405072105050b04c007070034500424201280d200700d641c400525a081c0402c1d04c0b000b207035485904031484002c0440b0000c2e03d6175100e242c10403070500601800d8030320844089800004c1c40205209503081405218080c020541350f140d42114480d2401e450315540300760080456001031500381300c40b10040f04803501500ba81c54042003186081d80c206e412813103000c240e540d01288005502c8003250002c1003c4058a00c14407528141d0799840c244902641c0780040d028044450400c41007002d840e00d64424403920380c1c031292420076032403103003040a02d04100506a2086101c0000e208086141c070b9042940901035468503c004000c9143c032503c051300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 544550710 1250 544549460 544549477
    0xb0a080f1e0f130605101d070905330a120b0906010e03190c030b010603060f14010e04050f1f031101030e150109021902030910052a0d020d0f0203 64
    0x1840300e001c22840050b030020700f0040c0760416418005402c0280c000c1d40164100d205040128100c1341d07280d902c0c04100b10005005203015680c1082c1107040c40100420f1442c01101c0301c1e043c0d1032005c444e9041c1c61403041c4400d6440c041c80349840c1c4841c031014000d09807054100250160300d10b17201c984080d0303580c0c1c40c0c041500000c0a02e098500c4609440c04030f803500c1a4004d6028000c8030262900c03003000f1100448101b031b2445807100074400d03681d0790015000d66000340185815a41c0c40041400010380c1001d282c40e0500c014540108007103c0d6401140440780242d62000702102444208200305040b02c80002081003046580c0c1540c0749503454a40544260600d09810191240144c2003502406c00110007040b055808d5801e02d940e44000420081d40190207050101c80070240091186002006030303420080054110003402000f1401264942d000e101455003036030152010f0014002c040075510740f88030303c03a0010070782520f07034640107031400006841d4081048114181d45000541c088107454108 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 544551960 1250 544550710 544550731
    0x50c280912051b0f0402040b04060f0503010e040312022a190807060b1914010219050c01200109031706030a0201140903010902130207140c06071104060b0a080f1e 71
    0x15000480010074241d0703281300181e8080d002250114074008104010300440341d86864043c47d040301000141e485000912941c02051a035400040c00709020f14904800442c2c1c0880c01894031080755184140352620090480807100c0300060305075000010000b0041d02010754071901c021560300e50b03c220a52040030f8004041544482c01081244c841c01140742c1e039040c1c844000c40380107858000c00350717000711407042c4140141300d42e50f1780710001003500c3e204100060f0440e02814112800138010761b481c1d1032240c2030000008445e00841060322083c8201a00e0030310aa8078000c05181200d4600c50941020301f680d442074011643c400010703070b0002c2c440801402e03d01c01c20313900c486100000030b0042c10914030294101442d01c0c1489501c8020345c1c01800650b100d1327851100b040e201c1001c12543d84120300740c510b0300004200051408265011325507a01c40c10000d002103205521a9001101600034100600210f10100140100d00c400e000e840f943c000c1c1e03a00d2544600d459400c2400c4104d40c00a04004104c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 544553210 1250 544551960 544552003
    0x1060b0f16020a0602030a080a0203060603060904140d0905011403101e0806040f02090a060b030703090222020307110a050703020409030e0a08101a060d050c28091205 73
    0x1c0d250a000801007942c000704607060300c5580e80070280d1030368060b034184400911960001542e885080c400e484c05880060112400e40c3c0d0b408060044c840c00107401503035107203189101c0d0241d0700307410440003070031a001d940c5603043d040c07818001414803800c202002040f084c0903c100b003000381100100c42d080300c3e11a440300350031418007460b05042d0000d641100126004800410041c0146038042c0001e961080d00c00b01c11640c1d480c4820000c54205010f501c04d0040c042000c1103d091094024021880c0010403101d107a15440301d40c030901400000c9501e8030f0315008002c0000c02904040055182c82c2c800e4003030a07500602d0b0740d80607168003090000901c950755480941d014540300e0b11055443d100041c022400c981d445441003540c5d070788402c0b0b240c40342e141802650b0b0101001d0314000d40000801a203814101300e08901c004014101c000d00c0080d40d5407051003400a51500f104103e0030202030b405a00d010000708090007048030140390041c008003148600c8039000101c00080c0c992800200603008081d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 544554460 1250 544553210 544553227
    0x105041a0c0c0f3307031a040f0e010b09040c06051e030403020106030b0604020a080105060c15040b0907061704060b1c0302072108030103080a0c06052701060b0f 71
    0x1c180c0504060206148101c1050035181400012101d0594102c551003480791807040c41081002015401070208001c060404201ea0502a0300120700c40d01c150020120000c1e075090102d01114401202c030400070340c8031000140c401c1001c1c85001c030007010640c2d05803041d10b850f0700c400c4580280c512a11080040020b00c0040da1500311040b07551460003070507010354a04243c00d0003030107400c0501003074401e40d0b140c0000c100c00e850f051084071103070b04c075640360144144e18042c108403440e00b0548078070359980103a04034421034105840c1001d20992085903c1401810074a500da850418250041024060120b0445100d14111010307d6031182e4049c5c004680d04100d01c000c01d41c0d0590001030134a405941c0c03164001095008250f10054940c0740c000b440c080745880544503010740d0310b903130301400d50300d01000188080f40c07061000301407600d5542070903480d00d0010b0b611a0100c1d4001c884190383d2551002003c29661031140e40140d840311050024010182800c01c8c1c04c60314852210035000030f400c0000c031502d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 544555710 1250 544554460 544554481
    0x9081c06120b0603062a0c16030f05240f04240e0c241e040308070302010c0f09150e030102030f010e1015080604090b0114040b030105041a 61
    0x4016001003550240611040e01c1d010001900640b1114032901662001851007401b09414500d41d98074044180c10203202d890502da9aa4042c0e5000c003024002c8141c903080004d40301700940c00071885110046c0740e400701c41c20580d0030081d80d8a003102c1d800b040c3c0000640c0f0800c11058640c0c202003000540421a201c5140840543d80d101790446503007014640130402104455001c0e5224009400a50364040d1010b01000000c0e00d40c0200d0450b00e00c8110b0400d80c842441c0000390100e81214000c0b44030380c1602c0c841180442c3c00c9030340104e981c5280080c440c01003580c2030080d032003e58000c0c10070340c4156051400141918116000d04042c658900c150185054403a04840444201c00ba001310750340d06104008607443d617424055030301d0300401007010914031100d07040401c046400c10207201c00142c01640044416000250243d6445615104808041400b80c3c070301f2802400d42d00301c0c0e4003858505009110507540144403045c4240d140004020114498801c00c01e40d0503203c994480256642d8079080 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 544556960 1250 544555710 544555721
    0xc020f0607060e010509150105030a0b040c08010203011e08031602040f090602070f03140705030a05130b1201030302190203120c01090c090506190b1b0705060a0804060f09081c 77
    0x1078281030800ca00382c6040f4006500043c040c080365030071b449051030035002d2400994028414107801d9801401c14074080381290a007070b80c2140c803c0c1c050000c002d555120040c2603030002e07001080c050800140b6102e0b100c0c102c6a103100109041005107052004034a4220600c5803c4200030b40101e46419180e2100750255011902e0b096104101315210030080c105409200040e0300c0c100c0c041652144411310107051001510003050b4444015440d1140005045803280c200c540242004282c01c5000701d41c01c00c4020180c05145075948610410b9803450900034a0007190500c0342c00c0c100d0001083e6070260700c1c00714040b0f0b403070302040351a03581e40c0e0542c4075400e0043c0542c00c409804410110030105c0c802103540c1045021340011154040030004030f03050744910007041e100320790707600e40204081881c0c03c2241600c2102c08184409491015a0b02e4001c10f60b598450b10070ba90000d5076400030401007120510510802c074000a40070040f0140680c3e640f0303a18803416144000342007209054852502c400d4000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 544558210 1250 544556960 544556963
    0x3090312020f0301080c03030f0304030f020c0d080703080c0c07030602070206160503030412020102120f04020d080310051207300606140127052e0c021905010c020f0607 74
    0x119582c560704481205503410a0082407800d0181840c0a100c0b40b03000400c0d40c2d102a408244d0b2031458440390340540b000c07803900e0034045c19401648000943c9a5494003552001c60250b110203543d03260703918005129070700080082d401d0400070312070b424a5441c000742e0403050366400100183e40e90b10900009119014a120518521104c0203280c010808003102550040344203001140f00c2600c1d1040903820f034020169042c24025003940059010803902d90600d402c07600290842111040d0b949030404194400c55589e501e68468807000c0041c0d080c00c403074002540180340c000d0031010342041056690000c0c2030f00c00c0d141001ea1282c0e000b1180c001c840010400710f91003001008000d9884001b2a90208007034113040c0030520f07080c40c105415413102d1550240d15240a4461482c604040411030081c50100d40600501d05480510042c1c0c88601d011181034a05d98607001c110300103a00c10041d0041100d036101c4940c40b422801001541d03044564000c0315541204c41074580e40c0080c02244071800380640 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 544559460 1250 544558210 544558247
    0x30303090106080d030b0619050c0604050105010f140d083402010e190332010501050f0d03120507030207210809010b060d020703020106440a0201030903 67
    0x14000001030550069040307414036801d451240401e04015001c0b100f511985680290b4100445a041d40307103009036078000c1d1200e040c90340c18907401c200b401e890300800b01c50855090707540740c0041c44203803c0090000018003442ca01140c803044410003094614140600091420f000814841d405c201a1643c40600d02608404140e800317070300c84140c1114040020007640400c02e039070180190b50038040004400d64198861940c4030074070350390b600c04007607a0402c00d03290300c030345003e01540391100c91040da051040481e50020070b0030b504002c10810400d800c2640a4030440c8841c81c8000069003026001c484e59442d4040040d00365201c1c9403e6010344140840206042e100314451107103c0170451901146c0503081e82c81e005203503105c01e41715080310503c0b00f0a90b80700c00c003031116000492194004000300d9100f88008254940e45000381c024071a414184030107507521144080325010021021022107104402031003102c03080c0700091980700c0a034054080e0400d45c0720091007040c0742c01035010207c6080c0c2d400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 544560710 1250 544559460 544559467
    0x6073c050a1b05060a05070b0f0c0a0806040b060d0b10030507082208030403050a09060e0f0607020f06040f03030e03011a010f0201111305040b03030c19050c3a031e0302090303 77
    0x6000403d640e000707d00c00c81c0c0541054000c00d040c61103e85400f88501101c0e40148c5c80c0100b40401915950070040440c0e600a0719440d01148507128803014103040301280c440410101c04190070050004040342c1d8490806144c5804c01041d590b1101e00144c00011760403103d04213005001d500f1142400c03045002d00b140d10300005100402d40d1081c010301c968915643c0e1600f400f9250348086036542c51059001c4d0740441c144c40250b40c0c41c6459402480000e10080051001c9007411001c130307055400c41d030301c480242001450100280750300300e484804035280c03c6000b0004940c1c1d00003041c00302040b842c0ca450400c03c040441c03800c124000d60114005620500e003240c0c0380c0000205641041c80140291401603003024400302c09410000242d030806050304016040304d2203c0d03045044003030041202a40d40f8400d2800080050701c0701c0541201500404842c17004020b106405a06c01600e03403061039601c07100c150705800105c1e60042080000204500b0030300b0721908110012030180c0100c2c0302c0d0652500000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 544561960 1250 544560710 544560727
    0x120e06270f16210c0b0f130b0319090f0f060f0905070501020f01020f03060127030c06080612060105040b04200910020714040b06073c050a1b0506 64
    0x100382c00c02250001d1181c0ca2440c6503c0c20801c56610300c0c50002448105880402c0c42242c00510250500100002010381800301c0c0d08154540d50080754025104280000140308a000d40f074411030600e1301d44070a003031010411503615601d000070710400c0a0721022541c0e10b107604000103074200c2d2800044200003403014071840c0c20050745032a4584101800340c030401030910146001802900c1c00740125206003030441cae40b000c0c0150b40301a000300100301500400342140c490681c2500001c40a03601a0b145003025a0902c00044c1c6001c101901c818410070600320f159030310101c001184c0381510410b0b14003244844ae40c00c042006008041c07404030307000d61940250182245540c0280a4502c3c0403101148450200041640c85d004c140c0942c0380780d400001c0b220101c600701740e0060f81c1c0e100382c0503100b0b502e48071030743c1c64585c0342c0c90841c5050000160300c10b102c0e120401c4220140d49105104804a44040c425a6543e580c0c1c1e909101c8000c0421018501c0340d00d44164005c05903000300409031440f40e03140c601 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 544563210 1250 544561960 544561993
    0x60605040f060f050f0603061905094609260c060604050603062a0c030a030c08010503071206020403050a0b090d181701110a120e06270f 60
    0x1d025840f00c1d05402c5a0000741841c1480100101c400003808941ca140c0700c0c9010320007075562102d083e104040504900186d2512500c8405115a0132088040d21001e003440c0f40c0780031103203101002440d01040360181c0301d850340360f04240342c02003400036400243d90740b55140405030b00c04036912004009203071440394218205440f00074803c080d241030556003183e558100b08021a84140c1742e0a070107503c01400544046015601d02c4015035215000340391a81d050421b1841f02c0d4400b000341d40c026040400c504901070340500500203075030071904000c07060358100710100b0703581c034914403807200350f422000501018024194112009903820005460074005141450302c0d00300c50a40e80c02c0c14912071141e00d142c04920800d240601c0030212411049818680403280c03c01205c06140314400d5542c0306a88515008480001c000701ea4268581e6141120780c54440001c0780d00c8404c031880319410840c00c0000c1e01428512a462403515241c04110200c0e09134801450000c01070340c1d501651041d4541000c0301c002 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 544564460 1250 544563210 544563221
    0xf0723070320030f03040f150912210c23041e050105070305091305090c0a0801270f06481218120201110315040207060605040f 56
    0x1e500c0d1021a0982d071807990b9000352255040c640d540d08107010344541c40000d080150b0f0054060038450300710359843c0c0c80d94481042c1c41c4801c01070142e66205950b080181c0714012101d0140c290031f145040e40859440702c0300b840351154416900d955614900300803a401103e503282c41e0f5141c00004221203201403a49032036a84580150090810410445c800034085280e1400c192001a901c4a041007080d68094585420400c041948540702021910360b1b10081d20400d407003400d10300020032285039140180034020009400010b116410310540003101c1010103040e206003601c6070500e100a101c2803d041c0440b03030503010018086400c1003040850610070000810000000c28202582c1004c0301114801d002e80000c8000b5011240d5807403815810301401c070841888102100c00708000c64250402001c3d0490314a084800e00b10942d803c8035081c0d03091007010004006191203c0c95802c0080540c4c1f941408600d1031485103800081640400c40b040d04404002d040180c014081c0c1000512101d0103040c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 544565710 1250 544564460 544564463
    0x1e010f050c0714042d020306040b09250509011d0103090b091b041a010809030408010609090c0807061b080409060305030711190b090d080f07030305070203040e0f072307 74
    0x2405c05185020b42500429141100f06410005184540845c150007010390002448a54040c0c2d880402c0c5199071940001140319580700954401c54040310107000c280011600384070700400c0810b0103c0743e440e0341c000b032043c1e205c084030340c0408102185003801200a041c0600006046078002010301003a02000200083d51035503440541c03414680312001c1c0011034420880d01000d440150501803803650092446580101c007400540703107084d80700c14030315082d50541d501c4000d0780ba5032440301d8414054000d852101800c000006410100d00e000d60003080d0721398080e50521584010000d07c8200510340003103a00401d6002e0060005d5966800c085817240c005140030f40d03105540090340d98503403901c480307681602d0000b003d46c611854144001f081c0d1035000250082e400031117a5850901068940c0050071000304040e5034503a81d940702d440d0040603244041c01d50815940107210600000000081d0554440c0034a03100384001e42e0350382c504503500c090b070204042d2041170144402c188500d08070020182d06 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 544566960 1250 544565710 544565719
    0x213080c06030c0a051b061603051003020901031218121406062202070f0c080d0305040b07300e010b01020c0d110303071505070306051e010f050c0714 66
    0x40000c090066500c01181c020000080800030200c070140103101628030b5510321490b5550b224100640307203240480607108034680c41c00c0f519030404955454001c965005034041c0b02980c0740c030710710750100300300000602009200b40801c41150800c5880b4869504807006103503605800d541d41d0b8030030498000c408010035070311615450740c07020405100050301801240054a110201c0790103c804590061150100d04000380c0c00300001130114400b41c1c8401c41c40c60080301c189641c1482d2000f03491809400c15001402e060800701040003051000041d6580724607182880564811607008034110170580314100380410b5140080541c04185a6011403071000000d0020840f10000c00016a620060109900d50058000c2070303090000307900a4041e0501d40000d0126810a11181d0742c11040c1241c0101c00b4401d80e07620800c00c4030160b454060040101401d840c2d440b40307044480804203d00c0c02051b5014103002d0380038050300c0c40504c54011034403004040c20603103410039221030888000846143c04a84034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 544568210 1250 544566960 544566973
    0x10e0102010218061c0515030f0a03050a05070c03020418020f01090305060c070503120106050d0c05070317220b0f10060503160c060609050403031a03030d02030a02090301021308 78
    0x12540144221031100480010311801c20b0201010000d203617021210b50784a100000a101d010b5194034016107019040001c003001c44010f003182407500c0c083d00c0443c940c1445c4d00c520034050100b0381050450711289401d02e40103903a1103c40c01c01301c07003004440d80001d40040c5029410039000c03042c0104000403601c01c81d82602a21300350401151b50100311701001c1e04580040c1e010038101d42c501402420b0280c401c0d0250381c20811304e0741c1213907103902d826406500407500002d0f1880861010740718028401c1428140b103400d012031a10007c01c00020040c111041c1c0103080c0c00f00c1d05d6401c1e01200c40300070700100107003002411094504141c0e40d200a440e014441d461190108240200b958029400d40700c1c1e607902d050850f5188100d0080004034480003205102d0285101000305000d80a484044d0003400c60109542c10f00f07240c003d044458220b51040705070380a00c003000165034048200c50b550304110781d0240e100d4460404080084c412080e00d0390345507100040c444440659400480122000341c03080d03450 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 544569460 1250 544568210 544568237
    0x30f03050903090102030405011206030f0b070210020415030902041b0c0b0c0301050913210f020f0d23040506160c080102030403090e130542010b03041a011401 70
    0x1030b2030069554160140e041400240074a5103e043c020300108410b00002c00c8255607030312120000c0b044c00105441071441c0108014020b6010882d4400c0030001d071100710300e014030707007a80c2b0707070300c45d811034103810b04041d02c0315401429913030785800808a42030701c2070310b0403034516180c3d00140c407254211508559250804001078000d14401c0c003035a04130748024280000c1640d070004008001000804216000c0d040034410b40c031002e0511055400d11203071501c580f50465a1140064548092402519419400100c5441d42d0315803000307040443d880300d0464480b5001101510150500031a0049500302e08003066168441c90480da40e03825540c000c0069604083e1191116402e03403000b1280980841c410b10400c121180791600300300e40c0210802d05140030326420303503111401e0141e202440c006065204071759014560f4420380320807110740d007609840c4940c2440d00d28420219414810300340e14250200000d028003003001804040100c44603007070b01643d0303118075030850000d80c1c9800b914005151413a0707800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 544570710 1250 544569460 544569463
    0x3030a0609050c09270c1c050603100f0b031c11031204110109080d091e050306160e06070302030d18080702040915020c071503110a1b080403030f030509 67
    0x90090f81680016480e00b0901001c0c052012038403030040940722800740d41000d000503c140920702a503a4008840c5d07541085080c1c10307509456045422111034074000034440c00b1707a0001113500d003280c01900003290b4004600290002413848440c01901802541c1a200d080312440b0700107030301d2070030b541c681580ca185502e40b816170380d0007039229100807101c000c0042000f0407815402203442403014500b50102945901440d07051a90f206d003043d01266805106129010300d0000444061a1041c1d00300c01c050302e803800007a990344002e440e031400120240c0c2a002c0c0c40d8450b00b900d8904280c09040706d03940300c0e580c3c81c0003541d941c0201d01a1f0724041c50003a58040d04444c082d86a118107801014040c14582c02d03808000042410101c00c823401400e041d100b0b000720056001600d042c1e200c801c05407000707500e40301c0c4e030010010a24500804043c50b242d6503410341032131503055036490706e424a0140130070351100340c0b590300079594508041d203c1c03607010500000f003543c042200140045982d03418400fa4450090b07c6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 544571960 1250 544570710 544570721
    0x40515030a1401020904090b10090e0a020f0307080607080f15060a03181407090f090209070c03140d0608010c0e01020714010903140d1e0c020d020d1403030a0609 71
    0x555058004840d01c41c0482d5070380c0320103003407a090b5400043c0b07003030003820006044424502040b181000002c08018114142002050007069192014000f4250958103140c44868000000340700b03001900d20144192420440b850160102c041200c002d0f00306400e024000380011a8402d401e01011000152400a01140d0008400001d03000500340800094160080d21036070002c800780c005080c1d400408a40880b0120070b05060080180c00041c0c2082d400314150342c7c2200002c04071a040684280050302c0d94540d0035445107452400c2d01c035105a031b00e0201c0b00282c00c1c10030303c2400d01e0040b4025502400503030180e402c03100604000c21840c1c1e205141690008040829039025810005e410005006810101000703020140b400c0204542c995440c904070b10240320800442d9031000c15141e0030700750404400c41154050002c41c6122050125000b02043c4400c2030083c010344016413240b0854699403070b007501c240c0c2c1c00f042c1d07482203082e0100a913950b500126401302006080010000d144001e1b440751 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 544573210 1250 544571960 544572001
    0x90506010611060a1d07090f0f090c030204020c0a0b0a0c090806100e060a08070b040911031003030e1c060b0913031704050304031b0302091803030a11270405 69
    0xe40201c0d42c0d280da51000400301c444c803011101782080751840e6207140600c00c4001429403103a00003808015044040300b120341803003c3e114102c0c81c00002d000411050081304049039811100941d40d011072608840c14a00350f00d00042c4485115018485110000e401c040b008142680c1c49204030707647e03001001d42d01d4006417543d5000078130066040c440701c030300c400e1890303407018020b88054005940c4031051450041958420320080c540802c00303100365002c500a4456118209043c6800c604007038082c98a0f00d0ba06100c014288026035407000440c1d1036100d1080f04503144040359600c07003c210304000c0007070040240c01c54812a6040002619140c4030f401e041c540940681e1002041002d8103c0300c4003200010300705840d00d00c4240000000519001910301c81e0f420382d81f0002c2800792a510520100c2000503020b01d0a180034000d801d040110000305503940003410b16004180b110b901e03c0e00240034800e0081d45c429019403c81c000000c0841500b003560011010b440800c07155480403030034603441e40346104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 544574460 1250 544573210 544573213
    0xc0103050f060f30010c02160b030403020109061a040e0f0a06090c0b0301081605040603121d0604060c031b050703172713050c2b05010801090506010611 67
    0x104442d410405124950100090000b940c024084007165004142810322072076072001e60345200c1d44500c0300307000d1011903045a0004002e400000c0074004006051409807280307802c0302200113014140b00b50895080385400100400c08008040351528031880e045003014002d80c14030810300c4880f0000102c90307500764404030240038403030703800c2d90b4403406010185411b84082680d65008621103c1001c002c60091401d030008001c4a200c414030300071408010380c07016206600e455030400c08108a02c052814071a101e1601840c424829001011040c0319642080c0e002030003c1000300394140c015000c0c503d824040d4030703003415082c02e003078080340c0c2c40c903400740014050341048030100f00041d007643e011684400c0f44840e0609200a803042010412040c400980c038400403111070404d00e0a001c140d08801d000140303c144410b28008048420921502010035180f500c411581400c550761864291030395600e505052100e565103050f0705021300703c10300e01985d00340909000041c0590103072a1500160003070b0300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 544575710 1250 544574460 544574491
    0x9290d0308010b0702031e0a140601050607140102071a010501140f040b030601110102030f01210309060e060403020d050705040b190e0612010c080a0c030e030702060a0207150e030c010305 82
    0x5000f9143c0c1d00154000c071b801d40304030b000c08844450f080c0d0140e031204031400e00909404002c0d081c440241042400c2c00081904071400601994442d00d040703400154002400d8030401101d004018028411b0350006480040c104c0c1540d510300946558042c100c17013007640c0d810f01c00e400b1786200e2801071184a05502400c0010001040b1519410000e15440001410020401c480c10641942039910841d22202d204403054014480030610007058007858918642c0344030504080c4e030f400b0300a540580600418024545d40044166642100302e402450340a04039408000c100d2520f1691103502d80161407095082001c20f50072410706501110881d9940202d4000781442d1035018520400050310094104004a00710707014100700740110742c0d204185d50f540340001d1031b00c10007510890341260000c030308050a2a0324207820311340002c1915152a01114080d50365103010030147e290081030782c0071088003a0441110300c03000b07812030300c40f11207150f09038103882d0020350030030046003110003c46008481c0440314 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 544576960 1250 544575710 544575719
    0x108180609150108070f1203020c1507050607050a080f0907050a08011a0409020105030a05150618040b060405010c02011808070608040c050f0d0803040615120606050301050f06011809290d030801 85
    0x100416061f640240161100104c880c008180b03d52612282d00050010000c0c050040240411040d9031180007480c0407070a0040303030740c00142418005881d4140300d11110011072002001404a80f00410b0001d16900e20550f65218140c080d200281600b03003180b0114088203e1384c24a80500034000794141d44040c81c60b5980c040800080c440540090034000b2090912400f5842c2c14008000034004070502c0c1c60350440080401080e10034011040c0c2c0601c00500c410081660822200d40001790b0900307143d456680b2042c00d50b841910558060fa295108282e00095029000702806010f107018102ca503842d9030300c83c4280010a1100e19006400002c000c00041c003041ca290061500320340705000124200c858900865103003d81e642015031206050508202040380510841008240035402030040349084540d010070380c0030081026040c400c0380814100d0381d1042148c40c0020340860f1004101140196428203524407175040821252900090418001d20704411a0303469642c1c1691000c0c156800d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 544578210 1250 544576960 544576979
    0xe0f0f120a020705060a030e061315020702010c1b06091d07050c010f0903080106090e0c091903050f0c0907022b020f01060b1213110108180609150108070f 68
    0x8140c1c41c4118003c445001c01e056a0b10002050306400c1664049010302500c0403040c10a9405401000301002d0b910f0f03401c0005400020b5500c02429a010042e03c0d0412800161419080324000408226004c2c0702c0000d80c80a4001210640b03c01c1c1e40c0b010f030f1440c0c6030300b03000d108501004009550403032100006038480c6d200f07a0042161819000010801045410980341078940d507810450104007c90010b21110398005e074038100805607807413165000d04025001a00c18414015102d014903142050030000c402c48004180c01180e100c0215450007203001000c60b1504201203003203200d400c02502284441d03200103a808410184103000070707071800c00001040300001d03c00c1c0040066003d0030000150003c020301c600401040002c104c40c2c1c0c0d0300320080d0340001080004110741800342c0302c1c56404000c50301c4c50088810240e000c1c01d0a20280d1683e1140c001042c1030300300c4441c510b01c00c1c0c1041100709140854807110144003d211101c1d00c2c0d07250040c141c0c4596031401003907000582c10b8400c024a065 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 544579460 1250 544578210 544578217
    0x9010221030a0e0a1515121202010b030706081f0815010e070c020f010c05012903010606090b2212081305041a010507080f070305040e0606031b0c0c03030a030e0f0f12 73
    0x1000c0303048003000d647c50101d0380d0140b40101003590f0920b201c034022000d194080c0191030b56841c080300900800b90801308050000e000180130f49424641c8030740c00740d480d5017116602c0e601606c0000300310780480780d04d109250782e101000d00541400480040109603554091000c90514039401041980940213110046409541000042c2c81a40d01c80b00ba13078284281c211010003c242a00d40c040d5807007200d00041c1130a40c0c0b0740354801010481141c00801428a60b0b60982c1c0303108141548085511407440807542d103116180c0c2003103621000c98001c0f0403c00c5110070003024220145240d25111650321002c00c0200d0396002c0504816240c4513060303625a40c0305400800c801762007031100909091081d8a0088503230030010045001c02c900050600480340040d1f4015800101199940e2943c0303003403110584442200128800900d0300842c40310401d99082c0300c1184c1c02c1d00054100ca0301da004c41000100902650241ca64480c090440c01c0c00c3c1c01880401c0107031841c04090000d110160104a46826660 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 544580710 1250 544579460 544579481
    0xd020405040525050a0509090309090c0909101409060901120302010603050a110a0b0903120721210e1c02120d06210c050609010221030a0e0a15 63
    0x81c1e405441d80b5100740008003a0f442694118028001d400d200c04e0000b04c01c10313038100c244100640d00800c14124400000c85036221400e46030380085448111412500340034030072055034800130726810480e00d081e40c1c0325280200d0760280810302d0005411000d021204400f40d4a054014030b00d0380050140700d002c107280c0750700c5030306c00c1c80000f03155552601c803c4e0030184218400c60311144045102c0f0f00d40e00d0800300c00005815584a041e20b0410b043d00000c0e5a818681180d0030721140215407641032060076510600383d1107820800740c0da65074040800030b085100841603040001416030546070507402ea4031a903e40c2c001408024602c00c40c03004102c28601d4004040f640840c40f0325040c0401700e40a03600a0038801c550000c01080141c20b00c82d5540b00f480c66104800000304180800c0c00215890040c01c40841d83d050350346075900e4540c0c00040b4103140006282c10800e14580a4000303510a0000003544103040000d0304001406444c039200d0380760f142455000c3d0159660310004072401d602a0701c40740f40034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 544581960 1250 544580710 544580713
    0x30e0a110f040e01050603010516080720030d0c0201110c060103060902061e0702100e01020c0d11031902120304030b0a020901031d030d1b120e0102070516140409020d0204050405 78
    0x4450740700000c00b5180307011031011850351148107004c0035060901460740c00000705600d000100e06c9201004180341c0000b403910040049502007042014130000d20b1040020120003a2a92103e80c2c0360100090000009200019031030304050018152141e020348640544a4026040036480c54071410050312000009990105c2c08104100c1001c0c0740900410010100c40310881d102c401a0041007046160700540c1400c4c084014001113480ea800714940c00d9100045030700c8050000241440401c020480c404e058041c0f107a0304021400c02050108508014401c82d140e01001c0b0b40040c80b01d44a010740d11004110201110200d0107850168014080900d018540021400803018561600280e00d000b410356039007001603800d006a56501449103843c07500da4950340d0784c0400301c500608507100622020011541e40c0c0504003021420340482d0328a07a001011240c2c01c4021641d003000714901d43c861409200410980003441e820036000d03410b516500100750b00004d008940a00c00503000081088806 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 544583210 1250 544581960 544581979
    0x180602010545160312090e100e09010605041805071a0304120e0d030504051f080705090d0c030c0612090507030206031909050c1e0f040903020a0606030b060a06030e0a11 74
    0xf40618070011000758050b111602d030010b0b03005c801a01201441d0000c42103030b002d240c00c01480303010015208048815a0070340d0ba20698851404d075004100b00c0d08100c1e445810440403d404080c84c4c0c090b481414095000e030b5803400e50302d2100710f51400d29180065410f00b8140002808161070302100894900c907802d0450281000c2400a42c51030500181200410004501071265050062482d903601401c3e030042c440c42c103103600000c4c140d42c00c0200418204070000805282d591280c80c0400710055000f0844844a912803900400030a568014140001c1c010021411508100d018200060f0340040141c0811410f64007407101d5640b005042d00c1400e0070122280c051040d251140c0060a40142e01030304180340e407842000b40710a00820f4082c0c102079810850842c2c1c0da90781803201d14800c4110790006403074410785400c1c0e04240841c10040c0c80180707400d02c0001400302a8100718800c071811034501a00c103072070f25401d4045400343e40700c0c40d00c6a8040036800d00066613007219000c116000602c0c0f00031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 544584460 1250 544583210 544583233
    0x30528060204060906030e0613021201020f07060b041410030b040303060509191a011704061e0e12120f0601030e010f0615030506030a03050307180602010545 69
    0xaa030700983c01440007500030281088119418445c450300d050384280a0882414013100b015209640c030000a0701c1070b941075070641500c0009504880078101150a059104c4090f428030300c0040074a00151400780c5d081c40720b01a4a4003402c050948140007905240316410f0441d181d10301d400c20001c008905055862101054036a80c01c100584212416030709280800910803011003902c510404210b2080c3c600d11403900e0a0b038000102c0321340740c13200b1a1040d2540d0b076242040c8024000d5484036082c003e100a2000b61100d00c585c208a42100035101242c000f01700662041e000e030f1044443d00d1000d021028041003001c1d00c44072156400c031005150124000c40440710060845011401e07448040f41c1d00c1008006c030741000c0b10101120403281c2820042d51400501180d210b04107050300400304040000024402c034007070491a800402c42e142c080401071b0b12050042d000340f000391150049042007008070090500d10740c800c1e0f4068102c401000b1400303510400d050000151840280c040c0e1f0151001918 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 544585710 1250 544584460 544584473
    0x4090908130308030a1a24040902031015020316030c05010617100e070b160305070f080c150601200f06040302030a080a0b100c020f0d120e0a030528 65
    0x19501520740c0568034102101e100d8103c1c0d01b401250f1200705080710111210390f03281c0c207a0100b03504031080054580021102681c469119a41210f8081c034804020f10101104040c0c580c81903402c140d0b848101d12540210070781e940d0050001402c04018000c0e040000030f0720511352000300d607203d50008104c1c29125040c64070042c0c014260221151702050784040f03484d855010b20190003141c82c01a20216041c0040400544540040c4412819044560a0802d440341c0c0031145503e800007a84c0e42080303800d01d000e0750b00e41e11000d0343d81128880c909a0750402c00305176400901440e0161a000d0900c0c00203600740b40b14682c0440501000d0044e0707000c0c000d1090b0144122031007580700313501855959008940203805454003038048240c440c58103441c65851344901c0c4281403090000d007803441c6401030038070000e1040702d5040351058000140c1d104540402402c00f503140300002850702d032030342d800201c00280041d403c564070015003158444045040260b0015a1140c480184215601c50012041c1c9803074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 544586960 1250 544585710 544585747
    0x20904020903060c0c1506030604030f021f0606090b090d0b060103020714060f100f0b0f09030a0309181401090b0612040f0308011508070806030715200705010504090908 74
    0x7075400c0710015000445205c24042407101c9118880750240504101002c640d85100041008003803012400455810500030050a004440000c0c1181c40d400c41e40240680a8a1540302e910045404120041040d412960a0314582d01c0d002d05145a00c8440342c42d00014008003a20300307070501d58200710100c08142c01f101c244000180d02070061045051141070b10301c10080051098640d4007400d2000d200d0b88002e1403200f402c45008150080e260303035144884001d54801c40300003661501c5402d21002c10150003440c5101207580e07801c2d00000300c40c04070140308150b481c0c100c42c0c503881111400042c040a02194080400e000c809000e45017440c0051030071540380001501c0c2600c49800f01043c0c00205030b4001c60050140c11081142105400c2070500600003480141004040c041aa40028842e880c10050000140019125008a01d500c0d04000e48030001c10303242c0c002c0c5e5a0540c8a0125040c00002c1c420086a0040e500c0500d414a0940c500004090200301150714207001c100b10b60744c11070400480c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 544588210 1250 544586960 544586971
    0x702040908131d07030603050d0e0a050603071206060912021201181407050d0c211205040503070b0f2a03070309060219050706050c01150e1012021302090402090306 72
    0x1814502c50041d80f05010907600100f00d02c081508011090000603004155080c01c0500340c10103a440000382070008421003da5000590007a402008000038907900c28000079000c0f2008004208860b1164822580d4900c90700455001d0070340d9000301401410501048003103084050b00014000c000315520185222034400b06903507180b80800d000301400710602001c40201021a18052707030303198640e18400448564410030205111007a483e60315101410301080380750f94030409c00050400498800750050304907001d100d00a10595a01103907000081c0b089031500d1850008042c2800d40b4510005080700d41d10710b0020120100c810400d505040400241802c0d501c03e84441c00c8003800c00320000e1511403078030405035038005c946031300c64003041d0041000320540f1600d00d0030715034035010700000c0b60160040a40000c600201618001080c1c42e000c00b00e14010300085c900000c2c1c00e42d0f82c4032002021021301001035403200845203840c107550500e9005195040c0044e002604004407000000d05000b000c681c03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 544589460 1250 544588210 544588229
    0xa050f040e0907080f0c180a0b190f1d0121051f11120f060414040f0209010501020304030503040b090f04020706061a07031b030c17070b0c030903070204090813 70
    0x401d01c200702080c8020080584400014000000c038000002c000c2982813005038181440760b00130070ba680b005904090744000740900044801803039400d02040b5807500744180f913440012f11401261003c010720240c050035482c445001241d0342484554603540c0101d09a0300355118004e4006000104c0034000c222440f40000c2d818104140140c0c0001e0548403d0760780725403410300400c40000114410105a90419175140d090445540c03800c02103802890666001a90103250707808020403c1300351140008a540300b6194070380c41d42da031030006907a0f034052030000030055003081c0000c0c8150714080000c0c0c002c030180100100040350702d000100b07013261310145c415200d05480b01824418007001c841c81451146011488500c0c2083c5078800402a83c008403183c01d4140c204007422090500c964000110740750001d941c42c1c01a802c51030340480c9640490822540b10715448000303002c1c0c50031070083d28031400b001400317545000d04550800c80200a00d0208070703003128080c410a00c20780b010b00799110160101c0d90 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 544590710 1250 544589460 544589473
    0x4091704080105130302150405072304140403120e0a060204090c11070f09051305011409060601030612080901021609090510051303050c120325030b060a050f040e09 72
    0x780e02d0940314020843c0d4011980c141404000036400902881d0f8840c400d0034148441d01e0f01e2800e28100307641c0b50702164152840d8944180403035007403075982101d240e00301c408202007000e5025504072400200d50140100d01e0030000a404901c05401502c0780001c4041504c400003400c0e950716049030090340200107150754800189942e5900b1210140c7e130518808010000d040c80c00c09019042292400390103089901c0d00d01140704140f8000c402c42850b40e120009000c3c03209480034400310008211031612882c414030300440e019500074031070002507808252080004099503142c2c1d402079488003c181d41107100d0200c1d01552118400c5190002d0424040089406c04450038030614100880030200545071500090040c01c000544a03440c2d61907160504075160300e16580f40e1410a0801d00142c1e0f03954030004200a641c2203a00200c00016010514004000007040d0040b41101c0a41d42c10039006042045008180c40c0960040c00340a80c52401141c0303000d882303603000d2808030b1041da6514955071024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 544591960 1250 544590710 544590719
    0x120a0b1503180f0322030c120308011a0304120507352701110f01050105210a060203090a0f0c06030608210a050702090f0115032904091704 61
    0x203510750480240e4030b40c0205044410303196203e4a03485810000401c44804400d686600c982d00b4010100940c0c00c10a00c40f00c4643e101540551566421012400501010000308900c600380c542c00104034010480c5a0030369031142e450072000312150502c40d050180034061071000404440240242895502413440c0d26a40c0041c070f0105400d517040380f2018518180715649916000c86108904004103c1c0b18081c00d407038240068414030b40440355242240912035121003410305c15001241240d83c00e0b80c00a070540e80c0501082d072a06101120346107607801031032111020071425005036402a90000c20b49820b29429600d071030101c884039100301c0b6a04001401044401d405224900c01400903074060000302201d2040b085240303c110726049100b1502240000086108030180e0715076580c094480030441c200304100d440100c000740708070402000144001c90271030348070b8040c1c01c500e010900740c0c0d81074030b40685c54030000d00d20b45914840c0c0c2240d511040032011580700c41244542025202c491940c6a050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 544593210 1250 544591960 544591981
    0x5090d0207060f0203091516050c0307050a060e10090803040603050118020c07181103090c0a17031c180f030e01020a02152206020f010f0908120a0b1503 67
    0x840c0c1c4400b0a2040c050350596500b0307000720460310011422150381d83c1200710b1403009005030050054691014054400440030031100045501d42080200c00b101d480c030350380c1c800301304541c0c01c02d014180011b0b015a2341240c1505260040e642821260308181c442c031070725801000c1c03854100d64004000a80c50b480108080c0008000000301082000b400f9807800d9000503c80e65a44007920901034800030500d442001c0c1e05080c1c3c0004035054181d5007182c1e0300d040500c45c0d2595200500f1025101c0e00e0244400680f44103500800010821128080c5040007201c1d00040e9070314001844119406442d046640314501140403400719540c0b184070008408481c0e41030003400170180c00c8029055500228540c0c001d6511400003070014801000c040395500310aa9003900c041050300c00302204500c00e420007088654020404041d0880c1980c020003034415030441715010384400c0080980240001c000741218015820b41040c1d004100c00030106810500d8000702d40d84c611202050b40c00d44002000780401e41c01c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 544594460 1250 544593210 544593223
    0x61e0b1e16030e060f09060711030703030e03190507050105220b04030c1d0109051305060103030509040e01050112030e01091203080a050705030708220507030c0603110a050a1d0405090d02 82
    0x8051303410500b4a603100b0049000351041e1001540706802c040f0700c48003080ba250109425068000c0c040d03c0403140e40c3e2a002c1c0800c5100c000c028803a0107699800c40070320014500300d10120b0b0b0004001c00304a0300c0c1c5001034515034420b42030404900c0300842c20001003da0f001c41c40c0000d03c141880b031b80d40c0b83e195040088403d141c6401c001d59240e2407280402c00307501c0100b43d2a0640300d925900003450744a207050151503020f42d4000500350f0062100000c14590440c000c0e0a5111f0140d6003401040c1207031201500301c0742d00740203400c028134a440c0044040b91003920072651007507040c14540c1420ba2214103844024440010460000e452802002118034850082070b0300702800d0308106045003000c0401410050740280300c00d0900405100b1743e03986810841d804682190001d041c0c60805031242030081800503079021702c2d000300f41489110403e20041004075001c511440c0c0c4c51a0404801031012101c642d03140710030f2501894a00041c508035582c6100e400d00422a00000300b410300c58410000c2c3c107081 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 544595710 1250 544594460 544594487
    0x6040f050a17060705130302040c1d030a2103020403152414011d060c030c06010e01050105030711031b0a0212070b040b3406061e0b1e1603 61
    0x20900c11071200b029900140b490740298a0303060060b2144500c5540c83d032807140300e1b40080d52250600700440b030803941003104030401c0d00c2200590249001048141a651810020001d024002d400c1c1611900120181c80e62007091a41c0f41c00341c60700e03947e03071a07500c5800000512602c1180e5112070049141c8907413984038944019688454001d0351900ca80d80b8545c000c40060103040c0151911303da0411070440191100a02d4010f14403a25403840c005101d030340f43c010382c4841c2d180d40700c3c8100100e802c1d03411481c518104c6205035959403039562890b5045890a0150179a01d4541c8000c1c002d01c4200c001c40b90450b006640c02900500034864240100902c6074081c80c1c201142d50007040051044107072400032a4140c960000c0c80d159074840050180160b502c841c1203070862800030000718588041801749030b09045005040902101d925820b030543c1da9409940c20480d03900103080e003049940403a001418042001d0b015206650341c40d611f00071201e82c04041c950281c00c024100c803008060b042108403030f040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 544596960 1250 544595710 544595729
    0xf151311040e1018030e0406050a051306030b16020d0807020d1d090406051605090f09130b2e030f0201050702130f0507120e06041106070206040f050a 66
    0x203464000a40380c66144450055071100c05401862004018248024800b900200a13041003501c0740030500700d03aa2412000501e02e500e10001d1807070240a00307070903140b00074540a003841ca400108003048000c5c82400d00340c20388452000010038802074030a0310071030171a842e1240c24651603070004c1c1040c0b0b4800d41002403085820a0008099001400e40c0681c802810050b06c1011440d214102d010b00e0303e01c007580c1c030001100802040202540051b409961744909040303226441880070303280360156030344460300a28001460115880c007911542c0e00070101018020142c00d958441d20200d1204a401100354408158100340c60601c250141c07402c504076800c1d0a441500f10f5440c02d040c40218040039040050201e100b509550325401d44000220344044200f0100e22040d20300400f0b810202c40410104603017074181c407401403141c069a00300425001c0078101d03542e6982d407201d49985072026507075001042485400d0050303c820340200040d01ca84040740c06014035260801422540c03c0e0000c0310745 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 544598210 1250 544596960 544596991
    0x12020c0312090d1d06130f051c0b15150d050601090915050409140d030c020c2e0e190305160b040303050319020f0a0201052809050f0f15 60
    0x1640d0002c22000380030740315034415090409610018626018103a02e1921b489803040300000c10710b0b02c0c40c241400310b030425100c41100300501d0b05916a49001582d0252a102e8039400140080e15009503140c0c1c4080d006001030820004080d180c2001d4200062080b4881d5454040c00401e6800086d064000c01d20658284030790004480c01c03140300a41486954007030317501c5056010401c44d190080000c03201000044409e99451024000c1c080c011980c240e8000d4090703003580100ca81812040c04103100e88010b102101c0e52800c209420041c80c4500403242082828403010400d940c51040040314445640802054241142402c50400072500e04001c003078070b00807104100b1564003a041d0713801c40f034142c01e00076181c0c1d90b240500380b0a205c1000400801600c000b40b010b80011660002c0d0450828990003000a60749810f07041400310302996142c400132400c0c1c20500c00031003154220450b40352043c0f040e109034040d0344003042e14081881000081c19005405000c40e44150940010f80c050316100f0035a14 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 544599460 1250 544598210 544598233
    0x203030f061903060506040b0904030807030c02010b060417070506030c130503070501020c010804140a24290f190320090105091312230903030301090c12020c031209 72
    0x79168010f1000034503040d20f0f4000030703034079607520790143e8100d900c0546076004915240c0f40c0104204011078000700400d2030711103000e03002841480394420754100908014500740c20310607007511100318454000014855a20045516203c5402a5002d40a0241001e2300d8101d06900810a00610303003002d4042d074081d1208001e185e03400210b64001d0362080c00d00c81e1160310383c0e051010080b040380560001078424109060100300b80040104074984910f29108101c40c00d1151401c142c4a000000c4000641ea07140403040c0c440d8100e0312100d4180005240b03400c4001600c011404400c001001800c4e1012411403c000f4014101801607100d0001d5204045104180c40001c0c00081c044c02828040c818240004400d4066024108640341c0c0040c00300e910584e050301300a001881482500600805280300304611a20540544800302401400746045a080c0342c0040000c02d1411039050400035510703074100c8e29114a10003441903448140140d0b80e10301000f60350b4903102802034003400c9150302103001c011 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 544600710 1250 544599460 544599499
    0x80111040905040c030f15050f070e132909090a150f06080303100302030c030a0206030c0906250615030f11040213060e090c0301030c060f0c060501060203030f06 71
    0x2400d607003070400005a16111828440b04182c942e40000309140b41440712817040c07003903801d141d65144900b080180b00d01e603903080c164581c080082d00d05801180741580103034554074160380600b80c0c60300000c8000464103080704419542c603180300e0017001c11074040550503006051031368001d640312500f40024400101c4a03070300c0c0c11401512000341454160744124031a0403544603041341005100d1001107945038144400c40601301c8903903110480c428400d0701464502410b020800c88500ca4000b004a42551383c3c14203103140c9640084100e81e4804030130055211066100c00c58280c84060740021072801582c0e51034007070202d80c1400341036084070000b5441040060381c040301c200d1103107500541210031444240003003030280c015850004d042c0c0b10b1002d00494020f6014050366040b80d401c890000716501c0d400320300f508511080c00080d0034000f8202c01882058012001c110031030000d071400c0405400d05480c1d400448100303820020041e04004248400d40c2d00404003950020b90427604c40c421042040c0201 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 544601960 1250 544600710 544600717
    0x312150315140403140f0a110705090705071104060506030403020a05060708040210030c031103130c0b03070f0f050f040b2a1b042903100603020114070f14030310080111 74
    0x1c0030422400b0b40360400c045001e090700e1b00ca0114030171458640b0000075015001803891820300c1c081e0711428030001003907e003a5041758002d0f2601d4440a05d4266113480300162043c4910429420a440c3c1c40e0004075922484002c502c603034000c1d80540311401c2246021410818090f2410301000b841400303100251b80c1c1d060034001c074242c2c0c60400087c16a82050141c000c0c0010604000526101004000e040001450f0142c416480b0304000d016607926010186000d01054981c040082c48405503c01c4136030280840000b14107403410500d041c82c03d134960507007036544590860b03081c420000c198180800c1000301d0000d403803920030042e614003448140300280d4a410740040141e564101904580998803a0791000350b4485280703a4024150100d40c50074903140d00c803c01203c8c06407058405030303500725020b449030313100756a030584d44d1180b910006107010240c0c1e048810161440f000006264001420250f2a010000600c80245441e4a0f2000c43c015403990b4950041d5001e90400401214419038481203 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 544603210 1250 544601960 544601963
    0x403021203070e220605010215010b090d050d090932130218040209060d0b0705090411130510091a0d0b0303040f0905060a140103050403121503151404 66
    0x300e03140c0d620000e0854850341d074000e0980d08074451041c1d18110300c502000c1c03850700b840350800900c5a030380d49200480c0d5804c0706903c801840105e6500501031007081d54000c011200c001090869204995107039030b4106840c00c2e0f034102c0400c0c62030781d04120418060045200d04549080e007800004424011151450311b4440181c4403205080300013002c0401408000c2d40103a0054421401c002e1100e02e04020f03604251002c0e8418850100002c034580781c0101450301d1268065446140c94861031b809a40a070400c4e90131560240e00c0700c0900d64014020000313090391105082c43c20211034500700a00182c00b0301450b407042040703d004001e001000b0180760f150010b0304044041c1c3c1d5129404c05d403050003407210300c00159042c007000600080da2610542c0304001e440b100c40007001903071558070802030800b400344114110546610751900b121f41c042d501a9902500030b08000024002d03030240f800480b4000c026502e11080311000500c144400c1c0e4015111702c0386620380070442c268116408022001c0004c10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 544604316 1106 544603210 544603243
    0x723130b0a1b03020309090a020706050916050d0521040905090712111801060504140a08060f10230321040605090d0506040303050f070305040302 64
    0x484181501e1030315030300c0c402c0c10403001440030306004880503001e6000c2400803034002c0c0c50300c00c80c0b1882040e91010060f034a40583c54003408032900038045c0c3d1300c6035200c42c0f041120340614075415025100110340c0111031078058a481441c100f50110b4401c00c0c100c1450b0603029480d40c202c003400680701628002d00a985c4c810029541c0c440c2c0c3c41c070502c690380451004035070114421516040340c1040c050004240b82188400390307602054207030b000100040000800300551182035507100f0f48030b2402c8880c400c581d07180221256560b8006084040d0450950001c66000e41c004003041e0000c2c4450701c0f181007150865207145805025040c1254064000d98113100181c04401c9019401100310f20030342c504090800000315100e810004480d90010040f81c50480800d00c1001445d114520983d0040f8183c40d0403c1c040c040c4141c040c0962051606140030b01000940102c0c201543c403440d00c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 544424460 544604316 := by
  have h0 := BRFrame.cov_init 544424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 544424460 ≤ n) (h2 : n < 544604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
