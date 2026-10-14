-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2123
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:42:12.292777+00:00
-- url     : https://prove2.me/submissions/c4d80293-a02a-4d8e-b910-1ef31733c47f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 381654676 ≤ n < 381834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 381655926 1250 381654676 381654697
    0x4030f0507060516032a050d02010c0504121205130824070f080a060f0801020a2003040605090a150206150d170c0715090f0501030603031d060d02 64
    0x41204005080c0340d42841900d601001c10720104024000c1001c401082c410000e40e81800e00c90141700c4010a480d0b54000200103110210014412034414424000b500440460f0103500034800140c1d02c0b101140c4500882c8100e0078098100184c02c0005000c0001000c00540945001800c01c0b00c012000c115041c81c075407000d503084c1c11100d4030502c2889124002d00368000c22140c0a899401c0c090402009880c0c484461803c110070040800d10301c0a1603001000141442d02c40c2c0400d0689134903c15000798014110780d0040b0f04040044d034255418500b1041c40c10040002440c10540b030a001994641c0c05507036019440381c488140801c103003d00c54a80c89114410754000c00031490410810341c2c5c000e049079036491180b4140000340300003a07414141102c0d0300400104044d01d40680e40196440c00e1082d03003152103c040014004580640d00181100c122103130b040d42c80310100e076510015422669035000181c0000c41d100e802d0391800c001c00389030620f0050302402440c035110003e0301c04c1049030000c0040e03d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 381657176 1250 381655926 381655943
    0xa02090a0f0303120603080307030b040e0f010b0901060807120e1609051b040828020904080a0206070905060405011d031009050c040e0a0f050124030302010e0105040c0b0d110403 78
    0xd00c145a80903c5040112850711810003200d1b007141c0350034007280801032900e400c058403030030300d0403082d01c40350000240c0f820420121480b4203020344829000e80700b6588981d0142a040d0000030301c803841414440c1c0600c1c92901d40502d41d4042240c15009045070b1a4544068840c44211030b000c400d10060341401090456000509404c0840c10010410503008030030000780000d100c03c1c030a004020139144844c0081850340c041044c0e96420007010b01141c03201c00380d0321000e5981040140038010009018000319582030f20700da40e484e0142550364820502400741c01c0703882488117115650045501ca100300d465610505204684200001e18003004841c40704081ca032240038100800004100c3c031000c1b00b504503028450840d4040f002d41e500c10100102400c150344034400d00092140039445884d0348a00541c3d003503014181043e82050742c29451100320019840c1100c3c180a80d4010701c40d050181341c0c8400705007104c0b803400040300340f00e0300209040350701c0c2a0b032200a010961010001480114404c1601 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 381658426 1250 381657176 381657179
    0x11b02061803011a0a271d060f0103110d150609020c120702060307031107082113020d0b1005040915060605070b01150e0d0302010e0c0a06080109050a02090a0f 70
    0x605003940c04070769400c1248880800164040d913a0280e844003510b0709440c088079800d0388038107449000a01d0b154072840562038100b1920158120300d902980205281d0110350003038540020315049c00000b444040d1034800b09103d040c01c1c1c0e00e0089030b070b1000e886c010950307071151490070703460310b41121450360080880c554005002c0100701010700c4840030411409003102c0c02c017815500494000d02c0014640c3e010956115920b01e48184e44800341c0f404103802040068490316502c05c0d05840082031440004843c1502d070000f603540c990803900000719907029109140f1822503580300141081c019118109107561044081595241c0d41f08106c2800c2c00761403040c11172400c401055003200c400ea0001c02c00c00c6030803c80c0308003284c1002c0301541118039624490012840d2101c1c2220030310b500710f44140d8000211010705c0c00f4580d05400c030441a805a40030f6620044140040000d4441c0d50b225003030104000b800104407400ea00d40c032480d030101141d0405450f10420303500290900310b0640020107520640e00c0d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 381659676 1250 381658426 381658429
    0x41404092001300903050f030c03010311090402060a03090501021603050d0e0c0307030807031707050702040b101b0c03120c0b010f0f09020c0a150204090e011802011b020618 76
    0x26103c992a04100d0045905440502149988200040e1450009465006420401d48283c04440c0340301c0715111107a031a41000700c01c0c415554401c0c40265440c041c010350711381c01d51030321404482c05190700400c01407070701605c0c0d0019070162031528401d80711075600b0b2050050790721920f58000074103442540d81c190b8501007411900101d80302a1006003940e400b80e40e00312800e40340000d5880580750014402500c039905458122002d84c1c1003029250203440080610042542090180250754402c60b4144a8000c00c0b00c28414421040c03908140040d6200b8000c01c1c100c1040521651a0b500954411031a00c1c2c8a07210080c0c01c1c02c8112010000a46180109040c408410000b5000d0448205841401c6152607554540f99000b0b01684d03c02c19070000c0c1d90101c50500300309020381c0951004406040034048120302c00250014031413030fa80a0f00b02a91080300b6038042c0b06140000010b806120b103050740d40d070011600c030420814a4412101701c1c1d8000c0015a407540c0c06400080000c040f4103100f01c070541c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 381660926 1250 381659676 381659687
    0x6030b010315050f1c080a09090e060603032205060c0a021206010803040312020c0901081e19060e0703061b0e090405060106080615070c2603041404092001 68
    0x4500b980d008100b520180641d035651412a02c01040031186440c045002c0c1c46407501c003d1501380c0003420610300258800c10180c100728110102c0d080c0a13420042c2c06900c0c0c0c215a1141c504460b1103074076400800000c684004c500658011148030140008000e40d12000480c041e907101c0e584170509584440e203080d08500d001c0c2800c8e5042002c102c00350400d54034050146035280901e010007800448060540880700d8400c200c40f04503154010004002542e4070642581c846010741c98455000c0c001c404178540c010390004141810206008241909284079124000100742e003500a04c2e0a0044410003c045010740c0a03108540b034224203c282007404103030018101c40079440000d801a0100c400304004107030082840da044444c1400c003030182d5900c840000304213640340e03440b07080002c43c08640d0100b8400d044011000352886001c1c250f0084500900c25100410a04c130303070424686c0200002d200c00d13290b448031300c003007028054004120000a0340d50025450345403032950b00002d89202e400e036219a44003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 381662176 1250 381660926 381660941
    0xb0d05160206010b0f1204030c0312110906090d0f030908100504030e0d0c170304090f0603020307120614090c03011a06121b0f03090d050a0c0b040f060606030b0103 72
    0x840389040a22102006500d80074148900b40c0c1250021514480f40707200842241c1070072030040d0385c08466140501d006400c6410b132941c1500010b941030382e010880180b6118441c1420100c01283e82028000010003d10754054456070f074100c2c034442d40d940c1c0000c41c4110901c0c9854800d4403003202c041d08155541c3d2403c1d2045210340c0d15142000284070104ea001604c5041c40e00080d02c0607851003020f810711200c81c04d0b06600c4008007841140b0360f120311100110103441501c500c0724092004481c41500e07081524581d000195050704400010000c0c611003030542003541e0702c108000b0038000c00c010151040c5140440c0d0804950b0000c0c600c3c900d80e40350a100da0080103442c105078420038101c0d440410f01134021700042c05441400407001c81d072007140d002c5c0002c3c0c42c3c5d0a180003156039000041201c1e201c40c0c00c15540b00601e80704103041207220600800540d0180d50050390340800c0e074a80c585424481c500064015035001c0c01009860011960764044c49010f0401d54801094820500300010300301e4824 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 381663426 1250 381662176 381662191
    0xb0c120306010f030b030a021f020f060c0301050105130e180c0d030e040b0102011d0d0818100b1f020706020c0906131e0f09140d0206011a040504060b0d05 68
    0x42080203240c1c1c0c3c201540f9000e1481c1803500044004030311011074079201031904080e60208085403000d100c0204004190300b0040d040e800e88a0421903034400a55641094402d40d1405000f0710041c0200d510804c00b41c0500c460380c0482d49600344c0d991141e200d007100140d550382000f299902e20307034640001c2048a840140e00590301d09038046400e4034014070000d80b03000c00601c13903a00d0328000c4109070b200b508103104440f0701603141c0006100c1c04040075600c011200e881070114544100066a4503c4103000442c01c1602101402c480000015240010a51382c405154080a282c20121504100c1405401c8402e2285c005120503400c044001c0d00c1e2003c83c48006120b0511141044215103501c0c0129080111405000c1164000c000d44085000c29850201e950140381034002e000030b5503940c00903c41039016a0a110062413019403098550110303903168005648404c00400c187c42100c800130444112104426042a4a0300b00003020f4510030351083d9032811000c42e01a680138180c5c8a900e4000ba003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 381664676 1250 381663426 381663463
    0x507020a0c0e07121a0303040902070204060503060f070305040311060f04050105060f15031003020d080403060605040504030507021002120c01020309010510032117070c03020d1b0219030602040b0c 86
    0x200040000d00d0400e02d00c1481c5032841c2c8800095038180c5d550002c2c5112603500400396600d90b51079544910003500802010f0b481079040080005590401003103580c0104450404146141d50316202074000d0a00130f0000c0b0204401c03034180e104214800d000c0c4038001c0800c81140425424141411401d407040500520321485c00d4206a40041d1b4903080040b07140c5050028040d00c0341d03202d43d4915803003030b10390740065003146540c090042003000034001841900c0c03280b281003207034580714000d1004070b50040f603005003ca10100041000741c60034980051b2010424070469400c50245804205160846415203181d81e40200c10311040510a0048550000c40098580d0200c0d103141c40c1c550218510541040e1650790700300300390505a11a56140342c050244030340e60007542c01d28660040006244580540060080703503c94610240f10f80072041d4110002d08424030111a59001c00981c9240391105003604085501e00000184c80f60001d44000d01d442a0ba9035240e00710f81c1049818260303003203098480c0c100c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 381665926 1250 381664676 381664681
    0x4030f1409041508060103150c02010204050109050d11060d0617030c030406080a180f03080f0c0a030c020109050601030501090b010611121b01061806081b0d150507020a0c0e 76
    0x102403401c0d1041d0440c101c03404600754203907005141c1c81d1400d54110480900400c1e0000c41400301010303c4840c42071100c17500308284010024200e080740214041d41c0d0001c0c102d11030400051800c0402030780c3c01405a030b1a044c0051080300000c49640c401900300c0440c5840741401c10024018860752040c42410300c025515040480300ca00d6101e1150340242030034041d014000c29060006079020310840c10150381cae00412104a4100b08211801c040c4049000811400020b107078041854085805400031501d06400c004a811060700a8999080b01c0300031596141c8402000c08c8042114034025801400001601c52079030800d40384495058002105001c0c2c000c005400307106000840c0080c90740c1c0030364a203441d0004c0303a0008410f2006151440d46541c200540804d59501101c0e04800400c00007804202c0550750b5a50706854102c0700707500c854032052121102856051505981e000c1501c80c0380e51982060311050003504a079001d64900c2c00503404460b01d8010007410140320005882c1e592803010091 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 381667176 1250 381665926 381665957
    0x62101140103060b0316170910060603200c0115030b0a1d030306040903050702040c120501050f030a0b0705040807060c03020d4104061d1c06020705070b070b04030f 72
    0x38071028050417200f8a44c510356010341882500070f1800300444a041c14500e048c00080d603940c2d40320180e1040a50382c908600000e5140c003c5c811440f07280d01544030054502500340c0f800300140c000410b800c0d0295280d240388071010910988241c0614440c03011140a410194180002c1310700d01da80313028032039060008040c0d2000740001aa03500400031640407030f0100c424901100c59006104009401ca4200164604800d0704410080600007145104008907071b61001000038920742d001009070560800007050700407c1c604904580d100d00c45040c200d04e090307502d04a040c80e0071895800789001402d01c80038a0704040d4140000c003518200c40c504034024911084c1d6900e0800182243c441c20382019082c10070003051070042c400c0c4240a511a51a10303181d50b084050101003414046412054003c4441120f03803500d03c66142102d01200b2091181c0c0007d640c40100030b5125840544c0d00d80314000000800450b03c8005010441c4151101e40490416250240505645405080c14083d00900c3c02d020f4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 381668426 1250 381667176 381667199
    0x90607210306031709030a080c0d0206070f121109061603020111030f1314010c020a020a08060106051213060207290f0a0f020c060726070903060b06210114010306 71
    0x203495202104e82c2d44640d0400080c1c80d00c3c0c01007070300609111002c00c40c0301200b0004101103404d082141c00380c1e0410750301c0407000c58000d006209507901003181250303d48204000c50380440180c0ea03209440b0381c40d08480b500029203580280d00c0120000c0940301c2d100040641c2805514048105070303a80d1420f43c20284200740304040c00400003885c00210301a81c00c00e00905d10f08484a82c140396008211f41032003020000e44442a240003a40111102080010540710019119040310b000b543c0e19410010740004403050007070098841103129100c0704080000c182c2910050400601c07a016003c9404041104145c154281004500306010240200185c2c207003848907035603100801c01000500e001140e0314a0b4020f00420b14100c51071310803042045281500080c050081d001001e40c4004581d690210500d40040200c1d0072200084400c1c00800018103160000340240c40000d100d1400c02910b080700701040e0ba40b242c22a0090300c60740e03004008560201c070300425041d42c20702e01404082c0c18140007904 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 381669676 1250 381668426 381668453
    0x180102040518040618050102040609050d0b01120201021609020307030c1b060b060d110307020625142205100309050601050904020f030604050a0b060a0e061509060721030603 76
    0x42c0c2000400010f810004a60700400151903150f28060700c00710709003000c9000350068007070400802e05080740454146021082c0120040c0d1141241089a0900000c0200e043d01044100d0541c400d0200c050020003240440c140908800900141c403403900d54801410744040f1500c66007070026a0348000c50705c410003106054070603044500030810603003500124a0300d1042900d407a088600c0c2c000300b003922035440300c0258015240d40e401c0b00d225403240a50441301c80490315006002e000e002d0030981e90640690307842c4451881e01d0003d03605040341f59034500b0342d1005881c017103203101c07841c01002d002901d844400d203070102003140750420402e480f0fa42c0d895502c4c42c06006083c412403034640050304541d01d09001021150001c1c1c1502c0340c0d41082c1c6400341e6a000010011a12140d2103400101141030408075141150100c60f03142d10742d900e500c01400a03004a06c0c000ea44200c00821564821351508401401103e00c00c07003020a0044900c00300600b45c080f0301c0100020542010000c00c0820110001d100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 381670926 1250 381669676 381669709
    0x50309060f06061b0303270303011202030a200a1514070203030705030a08040c1208030a05090a0203012408070b0702150405040606030b03011a01080a0b010c050f01051801020405 78
    0x1600d403207a0b0b0006909010f0120f40c0001211061440191000d002c00514041c000c2850480b0302003020103c1c1c1201012418000512584107100400028051503140444203000ad002e40e00034900319142c010f48078070362000c0c210100420b0100000c00381030502803d00103103a940d01022405c542c601700140440300c15024034440050200308001559818422180b4080d840340803a991002d501d43c01a10101c801c940c00d0f222654004000142181011042291603510031081c900c1d6039a440025001041e020b400300300340f4414a00c1e00c80040e1002d10502410711010111800c00b21900c038091040d4250a070000980703900800f1f01048084052800d60b01001c3c1d048500d40010481546544414011a48420383c803c0c1491000216141c02d40d0100403c0c0030150007e002c0c42608c61111403401f051386444500245040000035914642e40d8008000410140341541c4802c0d80c684445240c0003041e5480c080c075035512000c1c0312001880310700e41030490400c0e2009605051500c000900005441c80002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 381672176 1250 381670926 381670951
    0x9090c0409021f0801050907090303140325030e0c030c0f0f060d02040f0603110c0d03020309030408060118140705030a020d0605030a0510060902040f090b0d02150a0206060105030906 80
    0x1000c542e40c0c03c5440c0580300c10b81d0320300c044844980c840104a43d0080c42281c0c060024140400c1d0413511551880b02aa81c0644402d2185001d003014404e040c0e000414915140341c2d004400c0c0c908080032a03c00c200d11031b143d940032a004403140311950900c0402240b03580f085e40402c148000302c6c2c58403c200148014101d50340007035050800c000c24514428801d0110340780d440000e011446000301c1881c08203945050741c080107a8100640c0c1841240302e01c228009140c1d00c20715681040d0ba02c20380045a100c541031060f0384c2415902c80315146041002e0b04101d01ea0500300f60f500403103400303503c10001100050214524181030210000d0890f100261001d0000b0342c0000ea103d80d8842c09070003150003803030003a040b103950418500300b40d5101c403040c45202000d941002e20000b48481c803030098a040e55200704149011030305c4c2210600003020151345030358000030080140b901580d039400aa12100c600c4101042e40c48240c03000003820120002c001c03905101d002e1083c0030402c100001e000354080c4800091 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 381673426 1250 381672176 381672191
    0x60306030a2109050603070503061002010b0402040305010b090604050420062515110a1112070305120a02040315020d090b1602070909021815060d0e060609090c04 71
    0x2080c1480c4071180d000c0e0541d62001e071003078a55901c10064200c541c0c01a6141000c260b00c0300d0401025100689007900001d106102144652900c070b10340404d000454000050800c082c0b0b4041000c0c1d810942c000d44050755501905409410465600790344040101c80c1040320749015035500001340e00e501e6103c10000b66840c8403d4007622a2021550000c40c0e0024038102001d0354504031b00c079101d2611040f6181e49400014001440d19801035504a9a070486980c2c14006c0c0070000325065081f07242c1c1850b6611a0004601c420401e030701c000d00740340c0e000317583d070036620501c40c400380c500000c024011034911841040704001140800421075414801c609001da5150322406501003d840c840b00040c016043c02d406020f200030080351245000030b01a0241c0c2e44a694610340c400484111000c040e41080140110346956101c101e40e4650050032240407403611580c21011511a421008d51000345c10743e42c1e249905501c20400c1401da01000440e003021480c034200c100a5140d141803c200707400340d0f0b1a0301c1c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 381674676 1250 381673426 381673429
    0x506032b030f1d0d03052202010201022a0f060c0301030809060c061501120b03030417030417071802031e070c02090f010f0b0a020a110604080f06010905010b18060306 73
    0x12100c01c02c000402e042c81aa14180d40c42641c81c10321000d42d604070310401c0402919a4003d004640c40340c54000ca07114689031001500c0e034403850016004134115582044640e80c2c20b411210005110407e00241c440000543c401071031400152070a58401c82e841801001404080d0104990540368410541600c890012011403158003032041c48408500441c020070002041c0440c108445102c01d82e02c032501034080c03074014800c95610b4050710b07415420801c404e2100c1803003886030b840301045070002c4a00d440e41c0d0340708079010400b51142005044d0072041d0100302c0c000f0a40e00d03540002108001c02c40c55030814070340c2581309040b080200d55071418180c0001d18028011010407a415801403c229203d150000c201d06414109005001801312014004192070a110043d5010310340145c00802079031000361114111000343c135900b540d10100070000801c0082c01484420703118403c81c07000b00720300c0d414000c064007030390016040042c0a2100340520b01c20f9210849001605c0c5900360b403000c2d541c0c0c65040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 381675926 1250 381674676 381674681
    0x91208090a080307120e0109060f06050d080711031c0905012a030e15042405040303021218060a0507031419082e0306050c030411010e0d0b1006030506032b03 69
    0x6d000c2d030103a51a00c0040001d00c0500d400000300c2c1042010200659900c4070300700030340c0035101007015103404005c0c0304a0000642000c01c644900031300500325464109851520000303030302a640e41100041c0c10210030041540c200c95a2552041c50301c09921010003c904048642a00300c80003030108900001c9411141e01c80103140401f061400183c03a685588886150810031203110f03900701b990700c1c00c0750850030503480351b03060790b058070340c15405400c4100c000306c070b41000c503086103601d0900b00c2903211030b440640d60780e41c0050480032999128103840300c4450030081e0031800d031640d42d00c20280703080041e0290b01c2540e0b200d00600c24480e09040d01d19848902d1032031161045030038020910080300030350501320f0b04900c51031390480c0d20500044c016a6264289080d0b9800103980013009561074032040307181503000c0d078113084102d080079080c0e0020b21190749400010181c2983c0c0108010398050b020f000440d0301d8055698003d400b80c0050403c8181686042258a000c10609807440e0420000644881c07198 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 381677176 1250 381675926 381675941
    0x6010317090a0b0307020321040c121a072c0121150303030204032f090c0702030a0b06030c0604050604090203091c17010909020f060306060d091208090a08030712 71
    0x14020744e00d0303103445a4060340d2544054052080c07100305c03441d5070f80f0b4450000712062140c0c0d480075450f0003040c50075a1800302e1401c4010201d9607480b1800342d80e203600c00041030945c80780c081f90355036003803948031541c00810518030308902c0b260446040d04004100d136001070a10a1245003408100c2d200300000a4200c01421184140c520030007102d8000002c0c5030f071580140081d81d010300c200d44528070090707900f8081032100c46e00302105800317900c0f01800145003408019910a46540459151442d9540040d007044144402103402001420901c400c0d0309007089040d608003020f070b4803940b030142801c00140682c005c40c800e013450389800200040f00700e08280040d04030f000c900c0026948280c01a1005021003481480b06441a08003000020340c94480d405100b14164002e4001120029058144500380d4001004980c0004041040c00344110130781c49000340c90ba0052260031810301c55540010500d00d0040c28007046980300044850100d170548c42144c0c0c10000d11305007440d03451041c001c4407002d070829 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 381678426 1250 381677176 381677189
    0x30818040b100e0f0f1509090c030106021b0d05010c08040c080106050d02040b0102011410060314061309020a0f081e16140a0302090115031d030a030f020408070b190206010317090a 79
    0x4200c486c00445107660041d100d410011100504155681e00030801240000d01c12440180c1c007031030540300c0c401604017a800e00300001504a00c2c01034000d80b2501e0179501c03d009128001454401000207003c42c4a0b2080040c0009034000d000329440d200025a0b031986000010b4850781c2c3d0382070102203c1e03000750310210482c1170f02050385840745007000282602c00c0b024800c00c0046030034584140480005691b046200d144e000342001d001070107000780800109250402286c1040c1c84000c0494000c550400c01d000515100c4000d01030a2741d2413400c048105c1400388031001991003000c035604440c03111903d140a80302030300000c09044102c40c00149a00e1641c0e48042c1d003100300140081814010b90805588134101c549051201c2c0340700c0b4868807251a1800740208440d0000d1054102c407910903007010000202c81540581040c6c2c40d002e140b4140201503020340c00a03000000c2140603800c2c0340c0c00c640c10040050024009961440e11090702500b03c1c00c0003c104603d001801c00115554440300300c001e02070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 381679676 1250 381678426 381678439
    0x60e0109060507021b010306050a060f030608030c010609110a0c1502070204050a05010501020d020d0503010b0a030917120703060305100203180d09170601140d0c030818040b100e0f0f 80
    0x800f403402035110b40e01080c040e101c200c8181c6510082c3d500034000e0501b190006003003040f40030724104c01250b00c61392071042c9404140c4c0f16a00020340d8034042003c0c1405500d0b030000080c41c1071600c0d06032421580700446004600c0707400c1c095000d8403074101d0b0707840c1d40071900300041903e003d2181884800911481000030361240c58501400140921607103c0d9042c0d400a03001c42e13821100c0e101040e41d440900c92030440001d28200010710050700311001400c50024a401c0204803412165104a41d030320110740800010000410381c090f10300049030310550414041d080c10054142107072a8540c0302c3d11421030550446e0717000030200d619800d4014091808007070410aa0f01070001c80311008000c00ca40c1e103c1c088105088802031504980007149450407180c0001c550300c05400c040092054400d5010000e8400465520002000c21010001040324a0308550410b40000010003048101c410320146640500038010389819110f0f080a021840341c1000c844d106016088440066800e800714442d6607040071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 381680926 1250 381679676 381679681
    0x191139130204090b10081302010f11150a0c05040303020d080c2703061f03260c0c0405071b06050c040f03030c02040509150c07020402250c140a03060e01090605 70
    0xc101d500c090080381040704e2a07103401c498417504451000050310070481c004a0360030150015030050440044140181c1421640345804d0b541c0c00341400500407001e15071801c40000c21036440d400c0d00c038142492080b07007001d9040c0b074110740740295a54414040b10040c014910045a0307401d0a0005441440e281c26550042040a4030b901c0710802002c290743c0d074000e20070700b0045040c6201000c441d018030180c00282c0d04081c1c0c59034481c0034031000314482014443c1070170441014070311292802050100c903090010085494804113000c21600014140c5c01000f440d1002c10362644400c045204841e500940085038a4440f40010f44031440f0b41c0d4003882444058860010415400c141640081802140e04029550321030492075207883c10360400c1180011448001001c0c821036001800c1d5450014000604190b041c3d12020f04030744014525860810f00286c1c1e040811040c00308000c05410501f50040b210301c2c890010a00e03030030342400010644e6072289890f00080c1c4003540b04c50400d540014092140c0d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 381682176 1250 381680926 381680939
    0x1170a1a100507031106010b090d0204020903190b070c151d010e0106061205040b04020d030c080d050103050607030e0c132009090f0c030f0c191139130204 68
    0xc1c0c1c455401140419020751403c00c5c25400425410f0490f1400c0001d24030f01440c1e102045194400f50030100e9125a00380295549920f00700800300c20300342d00f0b03255618010b44500b0501ba4440004081c02c003008035000b20341e4002420740d0314080c22460f0300f04001c911680c14049145151400c252040c00c150719200300554039000c15004402211181c0d00c031050108070440c0414203440e02118040c2089042d140410018103041d1440f049581c080c3c640303000344e0035403951004480d1b800300242855030f0351244018028400144600c03038010605040c204280301144030360300e07100c4185101240c81450f0b026003801d5240c4194000e000700c01d0007071501d0890b04048842a050075008000d0f0913004024140000d508031101032907c40c002c20360150031030300715581d50240d50603480001f0030261503058188085010221000c45020084409403640700146100c51786941c0340c400300c080c10313a808610340d1488100aa035140044520b4480020f40c00588404410110741645103100004000510009002413034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 381683426 1250 381682176 381682187
    0x160308091c0b091e0c0a051c061a121f0b0f060705160b0f0f07082205090a1401031101031b081605030402031b130906050a0b01170a1a10 60
    0x40c003c00c4446818010a00603115500d145c9107040c950040e000c182c05021700c0c600a0340f011600801a03c005444100c10b43d24902a035030702d4640004c282202001401c2145041c11030507490941040017010000d41d05600000440710b404003921102d6507440c00c000c5c080c0c43c0c81c0d01c81503030000017500b102c0d518001c51070710a59900516641c00c420321008040410200c0d0034000315004800c0d240c1c010360034003420401d1f00e603032680680000c5501440420450700d0b0300c1a2040c403c403000c10304510756a202450402400100d8000809000b03c8501e051108501c0f0703401d502c10340b0306680d00a00100180c942290040c1c0040070142d10000b8074640e02d01d5292045640222a41d00c24070101e841010000c0d0f00800a94680c00261002541034102e800030f4900d0403403180e4488902c1000800424150740640c3d4400121900c020054031250348690401c0050400760050344000c3c0c50030720700724081d0388808580c0b00803030102821400196444e521a4402d045090307095442001004201804660b100c2002401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 381684676 1250 381683426 381683443
    0x5072604050c1c140a02060f0309011e0203070905010926030d060e01060207050a0e063307060501080706050906070c091805061b040b0f121305160308091c0b09 70
    0x45400c0845181d00c0c13941c0300891982c0600307602070310726818060020000180c1d904024070000c0d0715903071000031780c0c9100d00b20758901c1854900d40ea001650380c142040d00600b5061203401403814006001810809103401021030140c2d628a40c11401d0002d800070401415441640d50700307030750a03040c8070020540181c200d414904079404c60b02201c1501da592424400c94000d24895480b42040a500255460822018800b180021055010314901c104025030300281c007415800c0e035941d00041501c404000c010702c40c3754050701100c030003032900c1c52500c4c4008100748982c076840e500448000ca21030042106401c1e04c1005000140c00a12100594040740303c0356207174080041e00c1500c01d83c800720320401c411003420340d81a1a103042c40c40c601410040107440a03132000f1101004c0020401c400e200320207805824a00420f02d155954906012038101540703040c0d251103d058082001e000b00304000ba00312030844400d00025215000b501030201420a9194000d44020301a00000d004008400030f001c00c1c00007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 381685926 1250 381684676 381684683
    0xe010c1b02060301091d0610090c09050904061512150f09030906050c15130606150c030c06020f0316020d0306050901090f0213060c0605072604050c1c 66
    0x900c1034003011054200000000c4080d400a40420040c8940b1010350420492000c444e410110014003458255141810454060542e48406d00051088140a0180e8080d0032451b150108045041c040000c020b100080c2000704139507500c0c080c116407031a001c98500014414050b004008009605000050b000c5801c0c105000b1440d003078441559408030310074800e40a030196500307508542404410b8600e0350107042481030504c200c035000c0440006940c40e861289969465580c404a0305113460003d071103081c0c010803802102500100e052650100d221070b49683c0600d0a1501700046041200c000d10510350f9042200c800001000b420f4200007200c05080900303a400c4400041060340c084040310028024603900188240040200d580325801c07959650071101001490f14080c3c80824541e010107030b004901156010700e10758140965071060607400761190070000900607080c000e00200a1084e80304400030034500c0d000c036080c00740030461644213040280c111388005010f00f1b0b07841c128010450b03084 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 381687176 1250 381685926 381685937
    0x18021905030d08010b1b1e210a0f081f0303021605030f030d020906040f0806011814061c02060d1409010603021804210f02010e01050403020c060703120e010c 69
    0x48202e41e208988150489504400841c144496400e01c4030300540403200c0c900c8944521040b103651055030065a0060105a00040030f9251109500b0ba940590390703107143c861160140305c181c1c41c2d1038100554802500062502041c035a0b1003004116000310481103191458174501e40110405400203024580a125605107518031944c40b820582d6564004001940c0c542040c0054502d074940d6130041e00600200a1903d0700307141d00e809019840030319aa00101141c4e101703400401c495240703504200c504480d500c6040c064982d41701105200c029001c1d000c580200240d0175604102405a85551038550340104101d13555600c0200110182040b03130b9285525018800109088920500c250011a64080c00504480108600c1c519141c24000d1060b0b0f801106a02c02c6100c16441086204c40042d40d52a0310b08845880c100007403c4070341c444d04461080c0e25090510002ca6000102c12910001c02ca8a05580c3c030343c41e290440380801c0f03550802400a00342042e40141001c1900014400707180c1d035484 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 381688426 1250 381687176 381687193
    0x40b0c010e070f18090b100509250f03021903020406030b01030515190806010801091a04020a030209090f0303040507170604030c0210111501030b06010f080a1802190503 74
    0x11a500e80440b481440c03d03010f010301040001070720004130701d008900140780000d800c1d219070310f0316540c061080380c2100c240710102e0011b1000c1e2401c1032403950004d10700030000e910070600f01c1418499106a150000510003805000c6600c5482780c0c04451480c04050001001041d40c450040c010b50070901403607002c00d090003000c04d000e510920443c3d1045070900751311816100b40406000c0c100c501741c45242e143d00c10011012401c507404003e814001e14489000186850f11414805000140003881c07100c40c0145a05220160369042005400d80e60101c8032640b81d034035020b81007841c103907021104c03d15034000030041205020001c10702e5011a8840e1040d003100c0141580d00d1a2500003c640040210384400320300005410320703d58000416803e42440981040303100d01c25403910b0b4036420b0721801000c1c10b4005000300f0110380403c076004002800d203901d681200f07001c007401c1c0b114024406501d0035075441c084030885533804289001160080c1c80f40b914040b180840035004001402802c0c068031800c0352 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 381689676 1250 381688426 381688451
    0x7030f110a0503030f0705070203070f0501031a090708150307060203030f1608071101020706060b03060a090e19020301060302092401020303060a1502010b1f0909090b0403080403050c03040b0c01 85
    0x49440c07480b640324001d94503640d100c074a50303841840054242c50400c00180a8000141c07010402000640b415022411815150100041c10340f03062405900c0320030700082c0d02c501d00352031721501c0603000001800e000305255140d5203940c90301104413010702d90610540b18001041c81d00800154019144040f01c8516039070b5405800c900240d03a0459807002600301000903031420301c628003400c0300c0311000c0009403501e030403a00d4000989140380c102c8580480e0002c1446414581960710000601702a00107208400403103402c541c4981c03944403000740b4041e021151408541d02940240099580280b01440e142401c15040100011100c1e4039040d03541c0c40780082c0115070000081da8414080141488062824440716a661040c1e400011056648070110f126041d03603071090b1340c11002400c840c10204140c2c50b05004000308060b80c0314426042c03500344003a01081c03900502551168242c00e0240d40c039112864100c6291280c510b681c03d44c0d010216000c03079081205001001c208100000902907200002c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 381690926 1250 381689676 381689683
    0x110405091f0b0304030915120c0201290a030c031406010f15030c051c0e07091103010e0705070f030201050604050105101e091205030c010c140405010c110607030f11 72
    0xc01e03a50300440007035010807040010a0042d58028460320b020943c29944d98803040e24104c401034801c020800c030072401c0d54020110b108003d4080701e584001d00802c1c203114014520b41c2000d00e040c01c001c0b0101ba96401042c2c44100f880001164820b0314456035907940d0410443d18212103401203400c1c01041d000085c2082c59100c120180e50a041182c202203101c201d0a40040140c0812002884000c1c041070b8001200c003049002110410390011480c0c10212100034184030f2150044000586409041102510090180c82c19135020032422942a100d030380003901c2d98080d604004260303c800f042d850b0200359041d0041802400709480a04c01070745ca0310104980d0020000d203610014801400440d00031417543c0348049041d025091401045485e14a03015000c0741540003903405500016108140c40703001d01c180c0c0344050702d038541850482405070106002c0d210728807d03581000030050181081c0901d429140040c80401000745503927902511f4003405051103160b0100100c0d58900100c0c03510103021 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 381692176 1250 381690926 381690961
    0x70e18060c181c0b0109020a051602010c02060301030c05030606040e0a020910120b04150905100203040204021c0c03050106050307170c0904060b03010f090204050a03030c030c020411040509 83
    0x400688140ea903500341c415501e4101c0007212101561114a8104507110005400c06a02082032103104015103410100b01070701040e8800d40034a4410402125259031250990701801020001070494840c02d000403250b08210030b101951220002000000f0010104d907107500700d42090307050340c12580d0748604100440d400b44c2e000b00065007000250a00510308400d0a030f5100c900400301c112040c1e143c2c07035131070b20360780601000b1542010340384140300500205103a8120180d4541c8000c0c03010304066a074030340d2250800c500500c5620b40100204045680d00d80544480c001d40b03150b007404200310201c0d01d001400c07125014201007850100041030841c80b5108a03481032203541c0700c0101c01d42c0ca58903000311007070b001000749594480500030364001d80c4e140e000e81b000600c41c0d4180b09440394104036841044c0c10320356202280e146d1041008000b0341d12444000d104403034060814010842c184e08050b00d09080d00880203500c9480d10490241d0101442c1c05001900c40980384040c0d943e581940c80300f82501c10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 381693426 1250 381692176 381692221
    0xd1a090f101104270c17010807031109071209030f0f0806010e1309080c030421030804150902040e0619021c020703112d0a150e03040314070e 62
    0x400c0309201c1801040452a0a4401107090714613028a800858003110402c03580080040c203001c1c400d45242040740941405001000c000d400c0c21031440c0e40c2c08541122004402d4080c03555480024000c0e401040740441a60114005119002007464003c0c480804402c5007404601c1407082901e00504c1001268030806040e110910009045e00030000440420502c2400703240d160317920000021180d130003030140745c4030400007981c440b410692405003602000520b150580302c441c0c0e00e02d0110380c1c0541d0164001e90000c03068070204156105000c094000c40d507002c1d40081c1401c201c0031101400107042c9102c0e01802c0400c00c841c52401001500741c1c0b14a845000600001350340003604001191b00411010b482800d040f60381c001003185032400c100b20030704480c1c7c06000c1d401d002484464002192125030082c580581018010b07642d86142454021800c02c602a039200c012a5070060100201c40180d5001405028446180c0c0d1006945107502d00404c200000103a020035045000d2601d02841c0070714 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 381694676 1250 381693426 381693461
    0x309150914030a0203032a0604050a0305160209040c06120902011403060a0e0405150612030a0f05040b071b15090b07060209040501181a0a03020d1a090f10 68
    0x740408000c41c51103401c5420342c0c107008400c1018016039080005002c8510724030341d1488001c4414050460741d8000307000141755604000300b00170008101103504130206506080c003030303210500680c0c044000b81c15520000e4204106006100c2400040100c0e0303c229049541c500120032850b106800694940d400000c1c0419481145010401501c0c00078540c4680054204d002407541c403c0404035500c42540d003510740c1d402001d2041160044000c00951001d4180c074458004145009025524407903940d03800200a401c1c144c10056038842c8040708c0040403a542c505449020368105211440c00b11030241c03007800c04942d40001c0010b00c030216000300c45015111440d00c280b070305402c1c54413a070050404807842903080020144a9855108282c060003644107100115203400000508807074244c5080110025003813403001e46552000012001e03a81d0695003075080035011704c0d084040a1a4100c0e01c030702a260b0400f0408074500000d0038403c1851850121601d6445001d1a202110447d4207001030f50030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 381695926 1250 381694676 381694679
    0x51608061f080a03080a022208011415040c030b120c18060307031401180606030605070806090c07030c06091209061d0120010e031e040e040201080405150f010303091509 74
    0x17800ba21081c0e52064114001524000740c01120040d9a1132540011f044e0110f40501400015024814282141481400342d5014201180c0000300700201c000210300c00c0b900c40c3c050891175807080e0440170324454061314002076010122441d68659450042c228040d003a48146501c01d90b2900d480b040c01100007070050001c450454490120207a890400303035081d5034940080130b4955020b0649100454001c4a0000700c081c21403520070142c070340c042c10120400010205000980d56180340860300104421140f540d204074526064900c25072011020340218900040c00d010300c60601e80300b294219882d61004a0543c032017000382d03022a5006000d0070030100d0010318800c0d55000700c0c2c036240181d510b120700c9001c0b502d030544503d09607480d00c1080035140e0008200d6070030703158800d0050325042c01900034150070b0500700400d80b220450000c202030b0421559002281c18004c0620040301e0301d0a8805821400d483c04041c4070340310010a00c003c8001810019002400e90350300c0e25103c081c0b0025131788910100703 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 381697176 1250 381695926 381695933
    0x14190302091f08030408030a0801080303040c06050309070b2701050705030d051530030901080615070b0f0403080604270203030d060e04060c03060b0a0c051608061f080a 74
    0x16000b04591100e07001d81803030040f442107000c1001e0401014420021640c89000b02d81c000c1441c84180d00c16000d990061082c000014082c0b00308200b5a101407408544940d00c03c95583e10300940c40d1f0080d0407070180021083d820051030704440f1180060300e00b994a84280c0e4100460b4944034801001e8842c0c0c100b0f0090303202d00943e94100542051449400c3c3d06001c01c0000003c441d00d10054007600701d0002e1080141c00000e50100c212040040303c80078504001d10000043c1c0f003050700519451003950f41c03c03521040340750140300307540c03005802160000d10f5240c03000c0c505580c0c11055400fa0049801c481c00207070145428014000c0c81000e91a074443d0302c80114100107040040800c040382d05000900c00c00d806c5815038450302c0010f0003003498085450800b42485000c171906140303c0b604260030b000041c030213259a48200c40112206150080c5802c0b01d070b082040c01c0c101400a10b04d8141001e000000b068100028110f001740480c10800c5100401034000a4a220042c805c544154201c0300144020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 381698426 1250 381697176 381697201
    0xf01051606090503121302090609010f0b030c0412080703230708360f040207050601060c06020904020f032202150f040806010e101e2d1419030209 64
    0x10b1902c02c000300c909080c00d05030b103c00c0890040381c00107012080181309209510b400415107400400a41d03403d905541001a04503220002d400354000c4280300102003840b002e4840d0441c0d00419622070707402c00d8407505141c01c80850f40010000d40010b94104680a0500c000f0100382c04000e13050040f0500d8a03a581c3c1d9040c150340c104280c4a842030540c0d10442201c042460501403602000200c110340203101d040800c0102e9290b420f140b4000c910600c0800001080090a607054074103d08058440c01c00318940100648288e1150a40090001c80d0100b6501c2c0c2000285000320f40c030b606001a1802e80f40741c0300401d0b9000141c0a035100f8145102040700305480f00003807042c0d02441d4200d5281507240c285140c9008001c0e0f20071028003820300308020444010180c02406410300c03801c000c60f140600e0101011040041c007402d8000020301c8100d03e00070346851100700211030003180c07900000e07a46200c5045000321800d0294000c08038143e10300c3d060300464071010b0540e0b070b0007410b0410365100d09480504 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 381699676 1250 381698426 381698441
    0x71704050619050d1509181e0c03080f030a2a050901090f0807050f01050301080604320f0c0d0f060e03040e160e0f13050a0b120c0f01051606 62
    0x18402c003000a215105124010306400b480d2804003c140c0500c1c0c00b0031141107c1c02030807078105410190003035170000349211105250585082d800d000007811142040c003c0c003030320b40d48000c048280020341c440008039000050352140d00c00c1074041115100c1c22401a04480308500d41d41c208070103490079052907602034000f40c0100d80045c94070f1a607458503400200d088100c80e410900c0c02d503101150400541c50075010442200034203103045401d55140c510582da59400c0500300070444004c044843c0102c0e1410030303010184141c107465540c0009416200715403922081d12904501d4024400c00a5003802c106030020380241d0b015a056215075142d441e80e9000f460360f1b900c0041c85000030000001c01b82c5110031414003403200400d0b912002845c000c00500b00c43c19a0b1842c501612002e00e11000d555a42506002c813004010008141c641e01c001c0c0b040c2c000c00385180381e250b00c04001100d40c00303852000105034071a10030039600d491140c0080001074800d401000480740520351940d07022400618290403500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 381700926 1250 381699676 381699727
    0x100f0f031a060406021005060105070503070f080f032a0a0e06030a060e040312050108010b0f0d020109050907020309030106142107030204110304020f090c2d0705030717040506 77
    0x480540484001503583d8040c0e8808001a4000321100d1845c102a208050704620300342802445c1c01541c2e55900d4890080e40c00150240031420b5801080c030094004946c0350414030000a540da2a216009038003042020058030304401c4000c40c9503210401080803942d00307a0541d100c440c1c0701c2c2c510004011603940300901e002a056290700001550481c402030180c0154400d0f12030700304161088018104640b01644070355a140e0400c680c6d20040d480d14034200c40c40a13425622900d00994500040c0c45080c2c04d40d00150300107460000700440d4503804000780c285058110000c2c04200c1c0d075024200074032900c0000b125401500c01c10741044400f41c00c2c10000c46007540905882003aa42d80d000601254114980000c0c1090004104030452401007091075510100f00c640c0d44c0351703003440c0c580c01d9400e0040342540801000070103003000300b40040d0313082c02007502c1010f82c1d440d40e50710b0940f030605d40700e81000008540c0d1642c0900c880701030b004040260f500755440581450308091580000e556411035001c0c1d2070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 381702176 1250 381700926 381700961
    0x8060f01021b1807090611030424030b1518030114011401301811090c0c010612060b0d080a0c11101107360e030307030902100f0f03 58
    0x10b40c0e40c0092280f490740f003000140c80d0380b000f452801e00d01800c2c030400b840b5141080c0d0010007082c0a000000090600381041704505000050a2554150010591450219880004882244d00c00b540da0740061105505da81d4154200703e074a0700a00d82a2a00300e58240720108003400148071080c520142c0005000d014035111400348015410032403030a46004514050706038003000302800c0d5106004080a5000c044041812104680c8490941c03130780913002d03d44203181c5c100c0420130300868501035900c2e0400b118001c0107041d43d503d0703c600410500340030880f001410001c80b00090703c2c0c00041d0006658014400c54540340c01e01c07200700d580040b5064200d0701c10103040d11062840c5c440c0082440302c03c0300c0d503c44a40740d00c0700b8408076140c5075840c2c4c8820608401c011848200c0c0c2d08a0b410308440d810400c80f030391240404188200c015190001c51a10988804000c011400b541500f00100b81c0e4000c1c1c17480790841101f00021175440c043c6030303001c0c000304006100c41c0d41414802d41c001501c0900349501e9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 381703426 1250 381702176 381702199
    0x30b2b02150408060403080705190c0302031b010f0b0a060804060e070e0705090118050a0306020c07090504200102070b0f130816080609031806030703090807060c08060f01021b 77
    0x580050f00064000d6003d10200420150020741c25600026141006800c04050300e50145e214000c451181e005c00c260500200d0800d03000700203850fa00d80c0302890300c040c94822406854001c1c103600383c4a443d000d0034075641103c00d04005a8900549d01c2981d200321490750340d601c2d10b0001c1c201006024150748604d81c00051188040d80d102c0f8080e8046da43c513140d84482c0c0d04001400d00b81c00c268024003014030f41504200940d42e0841d09021a540641c2c05a12040d081899905010702503001e0f16426043c002040200300c0b2050b070b124a10021700ca44d07002003441140049036590120b00a1080b461320030032034245840f01d110090f01c42c011f40c4889030030b882501d6144003420403068140104d25403105850034807a440041c0310140c6c1c4480d00200541c00e00c007140300d013040c9100100640e0f5001c1c2d0000008990003612981003050140c0e08580d00ea42c2d0341d41d1a103890740007040300c05065030020b02e40b41c012490b0352034080da0815076010141c2c0100019041560005404407503040c81c0b07940709042c041d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 381704676 1250 381703426 381703459
    0x1150302240c0102040603020a080619051201020403050d02060402100507050712060914010213091b081012030e01091d010515040503060a02030109060e1006050a0c21030b2b02 77
    0x10310141940340d402681f43d09c060607000d04400c1000d000c0510401e00031a16441404001102c801292030498007a01c090800400c4140280300300d0300f01902d14015400b16a0750650001107140c0124801d840d0910000140c4d20200c07900c1c05905401020b075000440c0401501d401c20400280c040d001d0200040e0914855582c0620002c02e001800041d9401086100c08004000103d90051030a0305e414000800c00e40103201054801e040014207025507040440c03910001407a0503406840c84960020141c042ea05016000c07623180d4143c0c500040c8850800308282e44e480040902c890000c020a110a03403c040801402030b2040d03000510280003840001820340c8c00300007860040e007441d04016605d50405007250280ca080c0d40161000200d86010f21821410140450003158480e02c0d14940f524284078003100c250f444504090008804003002c13010711031440503881d060500c140c604100a09011060011200e54880400c042c5402c82c3c0001e0741089281e01720000c400d00c0104160a089400072 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 381705926 1250 381704676 381704681
    0xb1b0d090215030a0903080a0b0105040506070804080a050c1509130f020f04030c09050603070e130201020c1503070305090d05040b0705033006030313050d020a0312030e01150302240c01 81
    0x160802e004c1500c820a5a05240e00030001e035070030180c0540b082c40742c4204440042c06900c9540b08032402001d0010b603150074040300100ba500505050016101190b88071704000b0340d81e804202c0c07001d1040300341c0f000d40390003140c1440032640444000750800244003800d041d100010411a03042ca61001c0c0c0030000c06440c1110031004001440c070881072000341a0a0900e4001210401426a4005d5120700424410017030801e64a5901221190320620030b03128501c0101d04102d4400469504041ca40c4440303641042d4000203184540d0595038100420303a83e00781215a20401c3c40054004108100b2081c001d441407100204003c5000f0710889180c862051841d450480c00380c00140c649440c0f6054864094903218411074119030220700644c14042c5d401c1c48107024440c0340c4241d03480b40a80a00142c1152a281c10441c010754209000c00100781e5030b81c01c050003800300040d09000703d51800450400142c0070b148901c0603650041d001907244c801c1460340324808029440f03640c038000024400c03440c0800090 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 381707176 1250 381705926 381705931
    0x3090507060c0606301721100501050a180f080a0b070c02210118080a0201060806092d100c080a0e0615060f0706090b1b0d09021503 58
    0x35aa0801d512802e801d24030116003140c4c000701c5011004c00700030030011400311103480d078601c0b5091036149002861b01e4416008002c60a0140c1ea00d2408524062406032800c03046170180555104c40c4440d9071480400343c442d4505000396408101c050088100c40f81c401c10300c9440c1d5030014042c120b0203903203d41c2200250b0b000c1d07612a0031a03910074900803040240595225410158a080000b617140c4c16071700162140201c41c0010403c501c07020745100400400f50001c00d1502e00c400881c1da4110480e044c0030149501000c0c2c80b101640c200100040c030b01f04005111841011030001600c04003004413641904034040401001105405001d040d0340300b401880107018a03004110001000c500076a8040c00c0381d4030052905100600d0503c01385501c4001040c0e2951000d0300311a4214202d1100b8002002d50044a650001140d404182e0000308001035104d541c0181c0609004812a502c000a044178901c00c18410000c560041c0189600c0c20030325003007942d0f514801805c2d00701035540001400c0c2c141d0400c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 381708426 1250 381707176 381707189
    0x31509041a310201020f03040b0d020a030908030a06030219120609020411030f0f0109050915061c0c050a0b030907061d09090d11011a0d020d060501030807050c01020604120c0303090507 81
    0x2c240590119038042000b80a40c05592014600f088d02e0315641c1c04550281420030700c50706400107038a8440d07178401e07405417031101d034020716442e120b0078040701040042c101400101e015041c42d64400c011581c11000d918205c481000c00c00882d89119904c610142c200000d003242c02603156203040c0d0303070b421802020350702c0342c2902c00050000749441906142c807078606030300c07500c0399615003800d00919040104007150b910181c1c0d203032001e483d140e00700407814a02a02c42c04044c43c402854002c0100640300700e09400b2034000301c8002200544a00187d404e80c403003034402c00703450340c0304200420180d030151482400f9030b031000e03050441d1040a1070105541c00c204448210b0290032407403100b042550005860f964428488000b00b02c5646480d8040c80540348464242d4455450740003103e0441d03542c040e0b101d1840394800c60600880d40e5902d8941215000710004031698040d204030b80381254800a80540b05a401000b440c40c41801a242500c0c2140d0403141541019181c46264011890800c0200000e001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 381709676 1250 381708426 381708511
    0x1110a110a1706160e06030c1c11040302010801080c0a0e0a06050411070201110604230c0d030f021011040e091009030f0e0d0c061b060f02031509041a 66
    0x40c0344c0780d000002c0d51240505411320080c41e1082c090390f192002500c0e4003241100000da500d01620030403c41d008400d03646080c103e410103000e102c000716a0006402224400c1e01c0c2c0d08030b180d8840d003d494a81400c12201c2c2d40003040d9030020400d450841d00c0007900502142d400041c0d454440e00460181c440401d90b10b4490340c0c00052090855030311084000440d09850054010780c140b69440d404804c450044001d00300c159145809000d04007031111060110340101039818040d0360b4640074204080301e04000740940200a50503010105a000d208202c41d4200802441c003400c0c10180104188054694243d510032800036440074030b864411f800c0d901d03000e80c40c4c4240003040070700e0040140010b07599081c0a440b00340c0c0b0000025024002900c11b40c1c40d281801c219088900f541e110b0015420000a840c0b5814161040740d111204d9006601030302c000f040c0340710403c80407000d200150805650003401003c400b01006980c6540c4040f00c0d4010800f01031404001a0699500d15102c00084001c0d07080c60 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 381710926 1250 381709676 381709681
    0xe0a090c05010c020117180303090f0c06030919110d0b160512060d0305070b07090609120203060f060a1a0903060a09020a060c02040f020d0905070501110a110a1706 72
    0x1021040800207040074680503031000f00a90000305041500310a61240c070300c0d100c000c500755140d007030760300c1c031407074921717008417500c914102d0341841d601d04007034410700c0942c001d40c900300003035042c48822288246241b500030500708100e2009a5020600101c05403008103400c010040c15070f441611020295010385610246800c014040c82d03202e090800e015402e00804005015803403140e886a10303800941140d12012a110a007802d84440c4540c0701300038a030316202003c001d43d0a402180010035202d0541d603114540e500e481c0c0004007030215000280d0700d580400300164100e45804015035000c00098001941603070b442d80d0700152960034032050030f03140d10082001141ca0400700003103603100e5050030301480b10001a401003001c410482c02210100031f0750100c170340c0a54a841d00035211380d1005030710071507481881800c1c203402001c4072001110a4003401d0310005030707903100b03810ae0060160074034060400355005503544850350b980025600d4201801c81400200112814072800150340458064800d52 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 381712176 1250 381710926 381710933
    0x504060b1608120a091101020601061d06070f0b07021c21060f0807140d0c061101020c37050c120f0304030501021b0d020c01080612010c050d0f110706150e0a09 70
    0x11b119021209045510a9004010b603951240c0304505250080a11032900e5940c0c0000c9001031154110142040c00141508001c00c03906a80d494400da4a641c2a1200401c06c12400074034005444802800545001c0815007043c030b81032407401c18070b0480c0c9000130390701d41d031114115455001c0d588081d2054110b0002040f0203c6803544144110b1811109441881e006699010458130309005100403c03010885000c4d501400758121056083c030b000c21030301c103000c030b0488464041c203100300f044020004901e0f81038180429449500010359221010700754050590301449a184207094610400744034421021001d400d00703000400145010340300169031041500451100c418620184030115032041040341c03400c540c04110700d001c01c1400d180c180055110385001031498a60020441141c0d4038224281450903000380c018240c1441c1200e052100d05102d5007000115000c0215059030088100001400a102588540c81031417164985100480c0c1701c1c0c4901490324400c0391000d40650b50b505160040c0b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 381713426 1250 381712176 381712193
    0x1f09020c07050301020f0406050901051209060a0c0f0c0201110c0d0b0114060a0203091e03010c170907050a030b0604090b010b03101a1611030f01090204060504060b1608120a09 77
    0x2510b0250025480c01c180c1e400901031a00c44d07489a01c042103008035404d4a10380c86501102c6d0300d00300d103c83c04030346130414004ea0b0b5200c4800340c414800092900c010b0410903030040283c3c0588030183d40303c082d540300c0c0580065030741401008150a1a01921011580ea0390310000300d0b5006501402000701190304083d0855040c0d486660418442c210500020f860a6400070491f10203640540d018880b0444507003410b014070948030803040d0306500380b42d80c8a10042e4031001c24060104d010306144a40d89072003070080d4880e2128041c1541285045600b8000700f85401e40240d04000050300004242603582c40d02a22940c080e0040d03001801c0c000f007444021420240c4500142c4038140c07219454012250324409580710f050344002e00407191003083c10903c8456030740904e404401400366941d43c0040440ca43c000e14900034128400c5140140200702410b040c417078038003038440101d0080d07e403000c070f140000f0501c03011000440d42d260b0704110f079510100c215a8100d0145211000105080d4841d282502d034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 381714676 1250 381713426 381713429
    0x30c010504121515060201050603070603061d0903070c0608340c02010c080c01020714010510050111072c180304051c080a051903020705151f09020c07 66
    0x402000344400c0c040504103815850150380e0141c0c03d0300c0d2040740c508440014209054800e40011000c40300002d500c0e80640200b40b28810850039500c82d1030b156601603048640c10301480d20200140206480c1c0024115405900440144112401c0484c26a0f40d1944911035820080c00101e44400340110804240d95903000701c02d01d41400c2110f0b005c2c0d50b0301070340802c4001c0f034004108144134041c00d06590281c2083d2f14843c0c0c000d80c1d2591f50302c954000c2036010394000007007240d403c001c01c0e841581c0c45e41d06108041c0280105004000c000e03107810011aa0101c90091190300d600821b640002c40e1100c0c44031303c4614072002d14a203038bc0f04c200c40040240030500103048403010302200c1d9032014102e50100c05c5409840c421181072401400c500108002528804401049403600080701004690807401510389940c045e01c0380f0b9803000c601e0030300310f0903030081c3c000050403948040d50300c0006c200c0541e03c0c0350344005074131540c10444083c9030310760041c801143d0040f40600c1d030000c1c80080200040c040b110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 381715926 1250 381714676 381714679
    0x504031709030708010c17060f0d051b01110a0b0c16030c030f170c0310030c08010608190b0609150d0f021f0905130e03070c060801060f081503070801020f0306030c 72
    0x41000c2008402038910247d8100748004200c40000003403c55641c802440f00d840805425903010303800310720382141d0341c0209008011544103210504080d961280500011004005010302032118460359500c9070100c0181884c0342542d0140560640389c94440304c0042000e01139a111707240c1c00003074100a4803103100318220760f04110003100604080c42c14408400d42103181c1c006000e540c0d660b40792900e030640c41540c000800707031b1030807400000c0e036414150456803d039140401030301c400300081170800d200e882804000400c4602050002801480c100b9080ca030301603500d0328440c10080268000440e00c031149401120811001342d40b034425070501241440310b95144e0704032201ba5512984025204180c2d070700c01e462041c42d4520520f03000701a9a0072034034001c806041102d859840b945090760780030080d8011a0f0010307291070700004803140705a440301842301d80e036105e003002921713014503c1d2111400300c82c01641500c40d103100000d0000003440180542c1400c00c4005449040101c2014204545042c505 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 381717176 1250 381715926 381715931
    0xe0a0501050f0a2a0216060306080601060f080a11091f080108011104030b060d02040c0804170405100c03170a09021806030d050a03110d1d06011a070201050403170903070801 76
    0xc0004070311141c000841c40d00c8001c00f0810500d84c901285480290903508200001965000501700c6d05900990142c3d1351803010790721070380c1c3c8135101115003403824100f24000501c0c407030210700d0100b1140d10080220881d0a0742625000b00c180101d44580c0b500252006c010000103081052154004c41c0c40703001d0010600240218409603401d03a000d4040d6004c0501804070000100d034540c0d445244007100b40341e01a20900601010280c090280201190165a5011021400b032800c0d8140e10032542640c070018600c880b160718a41c0201d440d1501310714110203002d074113019401c04040356400300344180d055040c082034510051062007903c441d00400015460004400e01203607507001708122002600703a107401c6441d88000c001c11400b0302020800c2200c01000081d48100c030050507001020341c4000c101c150b02e01c58034800b41c0944e42c2e10b0248249000030b188200f2003042240201c0042010600515025003015101d840d20b07040c4008583ea000540240050040c1c05410203016010003005082d008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 381718426 1250 381717176 381717191
    0x19030e10031b0e01180e090d08070903080304080d0e010b040e03070803130c0e0c090405060909060403141309060e010602070f0b0a0306180c110c0102150601030e0a0501050f0a 77
    0x70b003281500c201455506002d1500300e560082e91241c4015a0075500b000ca0070070500e0780d16103030310482400c00d440c02000e6004801c104121140a500354500a1001f542e55400192554491488a810203130040300d0840d01000051030202142c06440480f03581c280001414441400810089440d0f008c21680190001c1c400c140100e07042400b0359078848064010ba090684083c0751031003481700250004c0f0040c1c00280140040b92407010042c0a0081003030300e0030059500c4203c1080103e100840d103442c400c0d8461000980000d01c107118a0101c1e02103000c50038188001604248100440382c2c01050405654040c00c100a84500c072146005100c40c1c0058039201e800c00d10307580020b200c10f005840071108009070412000c2c1c4607601000080017645446170114110081400190100d145e02d2400564407220b40c080a001c081200e0482c1c10051f0002c00c1a440d00f000500c008040051000703060554038078040780c5048081c03040c0e03070072103120b1400014286040d107240c200d03c80000e0900ca01c002e241516 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 381719676 1250 381718426 381718451
    0x60d090f051f110d05070203040506040e1b1801030b1309030c050d051204030e0a05040513021905031506030f03070b0f0703051605130f080705040b04091109040519030e1003 76
    0x3c444c550612004040303070b5a6a0311000b03030319510035580140d42120000400249034140345840c1d80c01400501e15905040d100a1742900c91802501d071001801540d501e0300c0d50340b542c001da01240016602801891609042d40d04074400c6840c6030030160081010164000300308502401608400f90403410103605104a1407100408000014402018440d141b002c0c00d01607038a0041120051000500c03e010310f01e04181d07144021007000b84101c0c003d0300c4001c0c2c0c0001d4007a12601c0130081d920090010003206890b0307061140b90300b101804468050040c0304c0a6561103500f8002480c005000c4d1484a01504210754192541500240350608044c6004288203c42512000b0301007524014905076848007240c1c07c440d0580b034229404402e0401c90038000184504000c9130b40012200304541c108030203030001d01400217403246401300a003001202d00030340400d40380804d58075410074064401c0701e442f040300e5401503a1980d0550380070b4000c900d0340c24000310240703001294540c0f103200510342448658079101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 381720926 1250 381719676 381719711
    0x60c030f0126100603060c14090d0204201902070f0b030a0b09250201110706090f060c03090210020a050d05090303130b0904110c070302060d090f051f 66
    0x511031803041c0a20307000b00c59042444045400c030914600390741446210040c000c0060040d44001c5800c1070400c00c4494400b405001215000003034056198603210070181040300303a05040074101d078407d0fa540d02c0340c1c12101c6440020400f04c10400e1a4903550f850740e003a11000142c0d0f421541c000c56000303900130302c400b00603400c0030717011100c0f10810070740c0f2034413001071071005048001c007260341151642040200c0b640300c50301c04651110036101d40c001c0806140c070b030490a0b285003500300c0784244030811000300002e45951255022600031401d80b424410650740307040580c0c0c20b2011000020341c0741c5c1101c00940c0740044403803180e603030540014a041c0ea816529240c03101d01e481d50105c00d1000100e6400392544060007201c080d840c0048207803803100d496001d2202150001c10000d4002c900e07001c521409a1703400702c00c988000c40c440005000e070614580c2000440d03801049020700481e00e5003c03403000641c5025074249120301c500e01506a21184034503101e816020807220105041c100595002c1e90811039 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 381722176 1250 381720926 381720929
    0xc030a0b090103170a20390d11030a03030f050c12150a0b07030c050d21050702010603080711101d0f030f06090313090b0603060f01140c030a02060c030f01 68
    0x20104035201e05032920260b07001b450148140d092a04000d021030a0400081000c46160b4004040307421000c4207a000c1e8200e800030050060f90b03500743c0441d95001c1d40391180010400c14450380b810260f5140c40000b081c141200f811084000c0794407195500003e4809010302a484105092010300301710702000d00c000111000340c03c070b04424994101c0303c1e400c3d8603072121060180c0900c1c050140e960b042450002d04141c0c0406060700d96010703600e08482000e1096101c0c401e000301c55a03940750800424141035000b08070141492055640c0d0300000400070790102c0c060441c084c09444450482241e0b802403007115440100178030200070030304010085541c4440503140c04988141d45c01d80c941e1080001080c40c108401c1102025441070808200220798004001d103855180d04048440e0b95548403140000d558140b2800c503409001403000440900740021139040d6202c05244c513400041320441003003010341c02201e1110140c3c0001502005d074940400225400503441c1c800640785203004d01e9281c20480c0f06 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 381723426 1250 381722176 381722213
    0x30a240303031406010909180605010b21010308040b1b190302010e01140c09030c030f03091801060c030503130c030510110405090a0513080d0501050f030607090905100b030c030a0b090103 82
    0x2514103003c00c545148e10003003402a03201c0010820b07940c40b03c9125039160070804050724900340740020f00001c4411030324040e048a40c4400c0c41f03402c0600b4501141c810b40c202215105901c4c15203a20050011006c10400d0011424004846002c1916040007401d69510319400c0d4030076810311350b008240c0d94480406a5200454180300b41c1c540241c1d100207810980340089050b814855024111800c00e000b000810740c05900b00d5000002c2c450311201c028061009204000224000c122100c012074010b200031030340b120003848010004406039441200b4500b2030f41095400d54021200c0700140580c43c4904034107459101c2e2000d043c10701d0000095403005000b031144c10044d07190408500c00f90720340c00118030842d5004603420788858401401d90300801003481201d1262089120042407802c001c80c06600451982d65001c042509245407074000d400d0190205041c2003c800300010441c204201070350196442c0511b007652400d201840318103a0303981d042241d12564031a401040000c2e450f01c080c00c1c0c242c9a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 381724676 1250 381723426 381723431
    0xb0904061d1005010e07090e1303090308130e071d1002070b0c1005070e03030a08040201021c09090609020c0312060d06060611060c03010f0b030a240303031406010909 73
    0x260384114100081c0c101e51204a407080704041c80307030221079811403410707280f002d480104241e48082085489000c0c610500b8040072482001c506090104c08020b80722a00a040501100b40d4a13540c041d0107500c1000440d5482050036030074401c5420981480f40c0098181c5401d0f0302c00c14482d0703180030682c2c10100105100703045c10001f0b0320038140284a058020079209550383d8803190403008054842d5140003503803000d03500d0040012446801a0300c103000c80311000c6d00071800c040340c450056402d00b401801c180c3c1580724041503407580c075049207001d040001b05030b078500b40d0391494444182d040d03607c80e4000c0e41a480c014848106803810001c240e50348200040089083e81d00d40c200400c0100e10190000b914807418050b000c101683c115003c004030107039031000c442c103a55444040c007400307000a01070b5131002d403a0107004200d00b0f0600400395402100b00000014044e40c400c02c0c2e11001c11a0707180400d000780705000100700f810307094403d055200e100003d031100c5030301c0c0180000b010441d0034000c2260640e0b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 381725926 1250 381724676 381724691
    0x705010905060714030c03070b010501080c0d0b0f0619020613031e03060503031204030807111011190c1a0415050901180b1f050d030e03190c06030f0b090406 69
    0x1140d00b540c51112400744c0c0c240e9a8580c0603402c55a207951010703805440c019030000000503254810340c40e4903c03ca0040201d18146599800d643c009404411481d83d444017191030030781c10079900d1800030150949038004c842d00514038810f000e810010001c1c2403004070140c03200d201c00442d800c00d0b41c010204c64001a542c0c0c000460745403d9004003403d41001d03400d88004240c541c075400c80003210078000ca00030b442d48500f9980d40b41d02192030300003614881000381c10103000f260300341015420841c416114107840c0d41c2000c642c42d4100c1c209103200d0707002c0000644242040000d00c00f040b02c2c0301881c98603a001d840c00d1450143c8655007003100402505250591b41e00005516080a6201240b152000b41d90311001035058202441803c00c140c614540e00c610015600c064114080521405c45402a10125000d02c0e55281940d082d60381449a41c1c00d401211a4000801e50a5210101c020720810b411f8080c0e40c2860070040454100718680302c2c01900c0c10039103041968501002d643c1c4a5440840800e020307 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 381727176 1250 381725926 381725933
    0x30702010c021c06020304111f21021309110304030c170c010207030807080612070504020901180602010609050f01120b0c0f0a270506031506160803060a050307050109050607 76
    0x84581c2da4095051541d140102c00c00c002c1950002d5004a0003001c0c1d011907010340802704203500c030a072840001e11800b00743c480300c1c0e9140914a1302070000e04a210704000061010342040913613010891400d402c0c441b107907003130011042e18860b6140c0c4807001e031045415480c0583e4090240c0c11880400341000b20403220b07058a46103120102c0780c075964258002c0d07490380301516010740488029202200858070100019800b030400066014060403080010580305103886d00340002517009140312070401c020084c4200e070f503400d40502c48000749808d43c000039003645000c091004659005c2c1040f40002c005800410000c881a0f11407032065402000341c072242d8591528070b030302900c22805400a1004003040c11030490760042004100412055251070302030316541c41e030242c01d08481c050154410424000316490107d204182200301c1d0b0050042803814007601f45075038058000000032106c01c20004208100742c140308503001c0040009500504100c1c0c00e000005c4e00d0b501c1c00b80695800350310081180b01c1072 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 381728426 1250 381727176 381727189
    0x306010c06021312060b12030f0708090d120504030c050103090f0b060d0b090a02030c0303032e0e0c091816050c031b0a0201080c0a0e01050c01020903010501060503090d090503030702010c02 83
    0x102130340030700c49515410300d19044c0302078103120b42032070b2244591015003000c2c0324010003121740345001001c80f03a18010241c0d079620016001001c4c5550000c802c0c12003e40040e03207411103000150481d4907083c0c1c8640c07441c545510801c80350f420950405040041020000f80d48165401e0b003954040c04442036035640304003294104229490180c105c0044130244071a083c0040b4140041078001e0f010f480c20400c401e0305140e542c0c8000d40711030569800d02d00d8007815585440001c000c50088003116010344d15134482c09020182c5c025150f141c0c800c440080d598102c0e18018413610504d0907a0001c1040c14540b070861005404010142d4806204c4005286500303080148115200c3e400c0780400b090004842d0122607680d0802e890049002c01c0c0024003007a802203041d4291035040100e41c0e45c810881c1c192100464594208082103091503400340a00c0b51140e50070301842e4064140c41d640c036901c0b40b81c0b040a041c40d00d05054840c00900003105014003454a010080740c079485d40a02340708060303044e00e1010899 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 381729676 1250 381728426 381728429
    0x1416030204180f0b070912020609010c03050c0303010b03010504061d0c0a03090606080f2401050f12010f0902010e010903022409030607050c011d150703020c01090c0e010b0306010c060213 82
    0x180802e100441001c20107405043c0e40501d00315a02e244030540c0b545102c0f1f1080a203518041c0d40a201441038441c998810201095414864508281003a040032072441c43d5410130f81200140b400044018041d500701441782000404a84103180340006030020083c85068000d00f80503000701c0c000901065a40c001d03000400c0c42c0740d01041c00c101803603942240740e8031410303240c444400e140940b030705200140424003100340d26400843c1d00e01025074078040c2004645c2d5a1500a907802c180f9484004030b24500c00e1150581c800700704a40843c00e10582e100042558080d001c0301c82c10310444210910168980e080a60b10741c4180f240c05814141c1741254070400e900803c840f00341e25102c3c100c104503149903c4006071056010700002400780a00503020003200f460704406104040d4030406000882e10001c0c0f10250b0843ca80303080c01850084c40f101e13854251004c024090310000b4500d8030410807440c480442c030b030050000c130031700038150b040410000348105070500000d090a60042490b840c51082c04c0307070140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 381730926 1250 381729676 381729683
    0x90c090a29060327030f040807050a05130902150a0804030e03030c0c040902030c030d050a0e040522060605190e01170703031808010f090515040b130507150c141603020418 75
    0x2502e60b400c2c846e100344a5072060103400c10030b000b01100010b50b82010800c400c16140010481440c0030483c02e0a00028207808400b0307a8880c0000f8800e000c0305c09914003c004d148001e41d0f501542c4d05d020f04003d80010201981c05019078030410030803005803030101d074150400c441140c0100b0710502c0c60001a03c1c2c46c0706020b103154940500b8404c0101c80f50054010080280540c489101030310101e001c010440d82c04a461413070040d08180c09080d00c91601503510b513418410100000c00ca82c49502049054120a00c00f0841400a040a00040200c2125140180701040e0741c03202c07250400340303580e07102c80319440001e00748250208800c15404100c00d4100c0a040204002c011031203001c420b00d000b1300a988002c1d03896000d10b8903411894042c5c0381b019441150003100ca020681c40309084107a0b0b21002c1442a5501c1c001d4a901041707100440000d00141d165590740c00002071030302e003890401300c0d1103083d440403542d102452201407884d08645803000c407a0100c07030019000952035001040a070465038002e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 381732176 1250 381730926 381730933
    0xf12030912210a08090c1311070b01090b01030b03060103051908040308161a060a1e080a05010e0d0801120b1b0a020708240f090c090a29060327 63
    0xc1c55407203210b0000d400e9860041e0780e4011192110150f103511400c4440035207421880d01c0b280e2006e03007200c40d08000d02c0c005401600f00c0c0b8008603074989807102c8400b80c2200141c1515000c04418035a494003803000b8101045002d02610b525503980c280d40c500b0007031000c1c012a4040f800e030f0310900403900141c40040d80c0168a1350f9851a0060703141d02220f01e50381c8100c1c3c8049400c0181c60300250003958007481010003034a5500001c1c1400b00fa801c220111884509144100f01408500120140300c8a80351512540000c0358400b8500300241c20002c41c114694100300101c40108544000c501500e80b0091f08040d1100140d180da03425145a08100b010858100d01c0c00a1042509640007510030101c0c1e800c203041d600d00c0c280c01c2c0001091499200c7c0340e000ca07074991901041d5036000c240c24464100d90007200311402c00401784007040805800321940111180e441190508030140700062504018104548644070080c203400100c0e1400041c050f549041d412440280500078419481d003002c19051086 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 381733426 1250 381732176 381732223
    0x7021e060d0c0f030207230102130305011a15030c0a0210050c1c1806150f0308040801050f13150902060c0109061a0a181401030c050f12030912 63
    0x1007101420720000400005044140c1c41c10a5910a100751b880403a80910a07448500b1400030103e590002c3c1901d20f141550f08020b4103490b030100320210030003548588004220300141d1f1120807000380c0490b0f00035005036240000d0280711a07001c400c030717a07101c4820240140ca9400c1000100c0c548494840c01c00007803032400091014a414980c013601d0000c0d540952582c0318607800d03080105407400968040c000c0a803c500d0000040c1654000c681c40130765150101b104540d859407040740401c4554425a40d00d14009418003002100303000c2d130303548444519400c1c2054107100304080003403402284040e0400100620410184120b41c000b06503c980080507141c4400041d241c850082c54406011500306103400c00b4a500411210030500050f4401002907043e00d01e0842c500728022101a4180d400d80d41e21502955105000e203000c0d4061801152500003c1d4102424403e0404450b03100f0f13442200000e0300500f0702c0e100081210300c00c0000b9104010300320386a1000e03c3c680b0b40000e08224412000040c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 381734676 1250 381733426 381733447
    0x3060f0f03050c0f01091401020f030f1b0c0a030201121404030806030c0111120c1009030c03030b030102070b0411040b0414060306130b0f070507050a06052a07021e06 73
    0x1480c02524020419074010307040000403c61035a60350190940410089517082007642500d1420040406060068800308000301d9512030540d440360000354401c030710100d85510399449109950f4100c0c81484000d01c0101c100000003201340ca400d1100030b040001d03c80281c40d00869035004281c0912000249401c0350426203409407000f04110740f068080d10a40c850700a071b07503100b40c1c040c04503407203000f025050b481c158401440e8240d0182500281d60f200e400300c1580483c400e4407a210005000f40c0e100ea4014009150003801d91760f6010885109a0051005070003051f4100c0c6655042a4080c84040d04104210702007009004040d803010f501034a0607404081c425074109045100c0c00040f02a0b4845503100302d8954081c240e51003000d4014040f41c0e0024200c010002d4086400070400c1c10887c2c01c3c484181d869604d4044013a104680f400c1d155000c0c0400d00f5000f540c111140c0d006503154094070f51020001501601403003e02a110f20924001203207c00200030500e94407031b0001c1c00c2199641c413481c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 381735926 1250 381734676 381734699
    0x6040b0c011a06041a0a0207080d050712050414040b0a0f030b0f0f0c0313050a14101a01051c091b060e1503010e04020f030105100f1706041203060f 65
    0x2c2d804124241000d2101098502a002c440991310b1112848030750030f080710703810b60f443e41105080c01c05504c62020040341c2400100510354445038243c2e11517944ea100b500e818096018400348030010300c070040c807091100702c00c481400050341000356800500003150a001581843d810707802004404127400010080c4106c031504988501295110207406850354150183d914600725038140799074030140003003140341403a52802c020b134500600c111603034024a51529102c00c204006441140d078405508000960540d01401e4041e11452090725024504403001820070b114241d00c002524140b1034861000c0049580403000307064004203007010703104001c0c1c001c1c8068401405080082000c1007040b5100346000400f08155002c0c0308087c5040da445c08110049000e1301900499200701c80c9030341101349840c01d03c0f03640c2c8102100d0325400081d61500c08000300c0d05800790040150780e440120107039003101e00040d829400030f601c0b00d1001c00160003500304a0080040343c10024540c201207000084c80c501c41c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 381737176 1250 381735926 381735941
    0x112060b0d2405060c01060b04060c021906050a200607030212090a1113020d05040303051b030c030403080702070f0308040612090c15110102030123010c110f06040b0c01 74
    0x1100104400700b00034110302804aa4110032145100420070180840e041c070501070304d04841301200101c1c0703031501c9240246060300181c102c03c00050965040310250324001c0d460740100c400b094541150796080071801080341c410092690140869101c200f0100740445406d28041c10b000c0040c0c541505050a005010754810032008060a10369000708001000115944a0066004550526a001c01000d115500500e4441d000c0059420f0191401c1c040060050610441c46550001028603046880416481011000c3c1d448641e084c020000c03c51071800403650410340609180d6015501e04504038508000d98000c50101c2c0f92090303000007081078075405481583d6081d12003011103e96200f00c00f049600c1004c01a00b140c0d074030401000600032a0400c280906814680031740510000d007800d9003079070720030392110314501c0e00200002d0240f0a1408540080d0b00b0910b400700c0606042e84a80c1c80001c41040d100c0e00c01c0b08100c0c0c001c000c2d6514001205d0040c0280044c040d120f0940e6502c660003440c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 381738426 1250 381737176 381737197
    0x409110405160f1d1801030b0c0c1002090f03070b0307030506060a0219020103020d020f090f030a0f2406080d080a021e0304060e030c030a26060108060112060b 70
    0x2084082001e5490701802e800ca094850380d80c9500c40c900f00b010031101e80e000040383d19000d00143c903510308035880d0f11340030317040d55210a800060b241d491450300c550032240080900b4141c00d814031000c1244070010070510541c0304500009600c60400400040145441c0b4048a074103208400000030b001e90070401643c400d110f10f450401043c0c1d510010300460b8400c2050140c01600250491004048030900649101d401894010308100d0403443c2d8400702d0740500407c10003450041405889071507d04131501c0c2c1203000344c01801c0310313010640d03e8400c0460b15160007481e00500d601d035020801c1006e04440c0a82c01070042c184915a5541611516120004051000500e41e000015502003190003120030030b00f400d1454007072034024140300304030701d0304050002c807000f5866503903034909190304201904000d003140014569a19090501608601a4101c0c00200710010070008150100038051503510800a0030400d88959481c00125000403900c0e003401080303460708801240700654100640500d40d007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 381739676 1250 381738426 381738431
    0xa020108041403042d06140a03141503010b04020403020a05060703030f1401060305070e03060a110f070b10090506030c040209031509010e070e010f09180f0305030a0f0b0a0b0a0e04091104 82
    0x2480c6945d0044844640503410104844800c0d8550340c0011000800e0300004501d80000d24048410074100c03886025a0b8842480000b036011100740c0c582841912030a41c1c04460031480d080c915070126601051078031510344211008212601071501130f8000540100f00394400700f100f480203c20b02030b0031010a0007001c0010b031500b800221140d002e80900540da003001001024156a04450300c0b02410102c0e2142c42c0d084410302007820002040000380060b24458440001700303152600c800c80951803d60310036040d0508280c144a000e0301c1c003248413542c004058502681e1100c0010201e40b61019451850326060b1170b803020000340da0019484105096440410b03100d0303a035030321b88015001e22002c2c0118001051030740710810510f40c1547c424001400c0e0451740c10721000b01500d61a00e50004040f003035010620000802610941a10440619034212802044001c103401c0106520780402c1c050503030403240000d520080203020b2850072202c090001c00c203004400c0030b407415501c40003500700003a00990 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 381740926 1250 381739676 381739739
    0x190b06030303070212181306030515040f0303271a01150e1207080307030810240804020a090606090503060a06121209090f020a11010e0a02010804140304 67
    0xd00441124010a15507005142640e26540070403855030002444400380c0d040580c100300a600c48016003800280026030019920b0302c1c5007802410046d0342565203a0074403249040000040c1103c242140c100d81503d000102d8004007503495150500d410030b2052510182c0741c0d610100032a150307005100c0700840c01d4428581e41c0c0c400c1014070000c02031400c040890080880c01050382002c1480c60b100108860881b29610360f81d00509085a22421090b00002d0140c0200940c110380049440c008001d105020001c0d1b440d10121020702008202c405410881950045400d55491001100151000d21020082150b64810203442048540703c1d0b2400703030080200040101c0030030f10441084032240040340d00c510003942c0e500030070841a2450390341071210ba418013041010311881801c10600140380010307601c0c08540f07006400080e01088801c25a0b04000c100d5010402c0840c2c55000e160b428200000b850f282c80c81c0c900d0100443c444801407d100100740000c080c050300c4d00d4541c81d80c2c40d80e02c4c0c44121340b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 381742176 1250 381740926 381740929
    0x919061809150618181b03030e090f0115021c0201061a03040807230102041403100507020c01030f0f05090610080a0b0f0702011b050a0914090411030f190b06 69
    0x220003604c1074000001e90400030207039102003a00000c500003d05032005404e007040e591360040915407201e040c0b415410140d401c1c010541c11080917101a00c08032481000d40c03500c11140781058205006148903220003a0010401c140200004425030b03034022400b002800660030000c0c020803081c03141e900250a44040440c0c00f105c2001201d005d41d400000043c58400310707807245102c04d01801580109a4901c860507091503d080c405000682020368040c2c41d0080c1c2e1008061604402c80c007688031440c5040300380501c151700096000d000840c2824007080e4254024090380c000d0140f2000c0410242c00c00307040090120022810b28451545005900d91441e254244103545090740724005102d141c10101003103106000200c9654000c10b14070002c41c02c0024122480450148188001b020031404035440d14680d8000c02d0071405006040311014500c0800400150350210245c4040d05103000214a440c240d1400d1020f41e9039a0400000c40b80c40f2520010302811414880d40f090300c1c100800d40104010307 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 381743426 1250 381742176 381742181
    0xc030e07082a060405090415060306050a0606020609070323060a060510050a05030601051303060e06060319030c0b0a060f0b07110105030f0a15050a0b0c010614091906180915 76
    0x90320005018113041508003414440746580140c01640c001c840d0210301c803041110780c0140c3c0b02551081300089a40d0810000d4401540c10a400410554014104011800b2400241c040440350020504040c1e40800f1072800800c000ca1003000500e4055103041112209041d0010002c85600340c806503c0000c1c2c8002c02c032024040c10694600040003003020030095031290019000300c8884c1d240c0ea0041586d6542c4a00171141c5442001100343c10000402c8503618080c40051074001c07100a8402c084d8869960040c2400822040280340b00c40c40c9001c265048820b9025601030300c090660002e042c0d41741c560450507600072607811602c00c110701d4840600395100b007043d01d00580c284001225030b42c542c003801e1000b0b0100c001d2500100b900e410720005082e6038840400004000c4602103a507076200725804c1318250303044c0e42c01c0004407546110000420381c0743c4002c000d81c45649400d40c50720a20a03002c070f0703001614083d4460060440840b03820184107003d540460303d00342c4202c40c5030144501c1005224107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 381744676 1250 381743426 381743503
    0x6030703020a14031e061f08100e0a020924060f0f030a14010f170d0e010f1e0e010f022a0f060a050301030b01120f02040c030e0708 58
    0x1001a010b1008201044919003003a0051100a064038694000e5500c103145104c40d64200c0007140d0b20410902146401c070300d094007036200179000142e0301d10782404505981c48410010003001c40340c0d140e6044035a41d40038420404100c0e401040d011550801c45001001280e00068070000300003a0240f46955203800c00445c1d6100401c100100d041941200302d00085800081c080301100d07449000d880d0290a440403018060046100180b0105007040c102c440c0000480c04006025400805640c903116005031410b03141250034030345580c29505051044030300c0c62a401040e04400040c8a441042582010910141030401e03641c64524455034407089030381c0c405e4480341c1100e000200101a403582210408071600d400050b10302c01e0010031102c0030036803a608c121580d0340008e801100520400c006194424010703c440964514600b40c151a01c00c5484000c032002403107190b507040c0c48000c0b43c1c0070390403045400b01900142c854150352004039517100c0c80b40016184d25802c042094a1806101c03116040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 381745926 1250 381744676 381744679
    0x30c19020a06030903050c010e030408010612022b0c06030906050a1503150e07080a0201090501020a0314090d06050403080603010c0315030b040302070b040605091005040e0a0906020c0a030908060603070302 90
    0x10304251800c0003c0d00200f100138002c2c0c0822100700702c684589242406107030b111698100003142e5443c50700d03005500316403594001011074a084640c2e0005642c1c0c0443c10788441e04145124030000b00d56404045001c81501c200805405402d03c0c0061200d80503806104014000c0405100c0350740e895504100301e0300c0720959089109030715101403011070444200c0503880c4500c050b000404049a0411601d00781c601d03405503e0580c04108c03240700f15640300c50208000e000a000410f0144a0717640d000d030002c503c203251407a480300046044041e6030f0741c0f0b4030701140c55074001d10100051700307040c2001051035031300701c44003402982007a0304820914808e1003084198844442d00414650035540c89a2443c00d0142c0141c0861250803008a18895560001c1c4024442030300c03010754803420340040c0003400a031140000c1c2031207024080ac2081c1c14111758680d41c030400508002500700c03824509038009000d841803e450600c41c16104008060b0041c0700380f000d40300c2c1e03117044070b4a41c0d4810f0101540d8144ae400000e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 381747176 1250 381745926 381745939
    0x12071b031a04021c0606080d0306060203031513090605060108060f06070b1e2502030a08061c080a09080106080c0f09150d0f030f030b030714130509030c1902 69
    0x3500700e00c030700281c000c1e00309200401c0700c0c0f0700000301480a04c09003284001590000c0e0345d24420028040704201440c00402c2505050100c02e281480194803808020480e1181c440c4484011990b603980304503880042c40b214808000c01b42c6141001ca0007000d045420703030301281100d00441d2903442c10446901310304000030422441c12030147e0700c003030100c140940701503824044808110b04841155001a21170030350040305e40340c40808030411004503000c1c00f00e0101550000c1064101a40d40611229840642650700c0d009403040c080ba00880d120362910050444240401d11403161a440b00715003080320300103002031080c4c1d61034506480e100c1841841d010b0b80907850005802c55400c0054000da03001900b25650700c00c14070f00d00041884e04000180444100429001200c1090380100844808031038500c1c0070059481030b1742c0407079691304070ba0041e400c0c2642003d524400c2c990b110105c1c0401904041410f010b141810b4101559a0b0030091944a45000e40c0000405844e403800e491014603400502c41c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 381748426 1250 381747176 381747203
    0x303231305101701290c0a151802010e061902030c0c0a0803091c060507260f06011d04180c1a04140d0623100b030c0f0c12071b03 57
    0x200c0c0e20700d01117450f83d0100003526035031001c0c0c82503010064402ca0b40140c01601c0700c141035103000791400511528070b1102c1494400c08406d4040c070301e15801c40d01d88c0c0c2130170002c001c2c0142d0b6000880e24024180710a81100207490750842c4241c0c0400034101a803000e0046680026802c41041502c2e072141c0601c508550041c40804003500e0a910410500c000500c0701c044003807019103461060399000c46218011962240400105502e101040c00000da604c07145c105550038a41d0700a011004050f103a10b0400405a264000c17000146402c0710044100030800c001028864810100c0200c2c0c41605444072203158100090000600317a204072400b81111103640751074240300340055500f0305c400b07615401000001c140000901d0394400c00100b03054410080e0012290100800c00c00300d0000e0034403a01001c1c0403801c01400c01c820301541d8002a20102460302c40700d1810301c001c0f003030080b0f00c00122148151b210312410301990700d000380706103402200c01d0850200c81d4010025002d645100c000d1282580e96039 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 381749676 1250 381748426 381748439
    0x16050a15091e0c05100504030b01170c010e0301020c0a050f300d150605070b060105040b0d0f240e0f130f02030a0c090213050f0a0303231305101701 65
    0x107200507003d1150860103d0310380c5600120300460071811248022610008040c001d00121220b03003401000e089140800058903d80341503150904080c54605201c02e250802c056a0740a40590706d894692904a41d862800d07801d2950707440e0f0280d003004c20a0300038841c450490340c0d05080300e03080c03a034070000c04042c0744030345611000300e13a5006008070144540e0340c0c65200d207109010703400580281000d545468840803a41800c580804000d4241818804100001c00008868005903100a0026100001c012a00305524005003a2550701282a45140490410301c4910100114140c4440e0507204410381d0b95107500040240d0182c07242d42055052003103150000340c4000410300c41c940301805940c2050500d80c1e070500140400c2c1c0080e544960041100715020000c4e00890700201000c90341c03410300022200c08030b001844a0b000240400403075180c0d00201032041100003020803d43e041c665920741c82111120031403005409034074032524940409070141e80c420141502c1c007488540758400305918042e07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 381750926 1250 381749676 381749723
    0x120d0e060309240105034c05011d070c08030f0a1d0c0f0406030b01090203060a0806070513051f030507090f08031305090c03071416050a1509 62
    0x10300700c04141c824442001c1a10030f0b40c00120008000300c4841400d154148010103003062030310300c4a603030140342c1810b2400100a40d100d60b05451503206075082034444c2d1240e51200170240021aa488660505000141c0f0020001080d40240350028582503162904e1134100da2090303500304041c1c8460301c14404902c2540f954510141c10104018000800c07082040d0b1800006005054100711340d0009080c110603400c1903000d8030406841154108521400c6030b41c0c40c0d840800601601c6e90155002c00000d082d80c4070300640d0805084514101c1c0c11614169200814070792101084039100b0121003000200f50400080c016201165211480c20f6070340007070002c60050100601440401034030341000280c410042d41c02d03d0141600d070700078540e02c090030b0181c1242243c40b94480c6005010880402c18110a5003081e607404c8210b900e45425058010301100056003e06e590088500501c141a5003c1110000d0384101d220701c207900500415443d15020001c8a00e1210041c1032419240086103400c03880c01f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 381752176 1250 381750926 381750931
    0x8030406080a0f14010f082817030406020c100203040f020f150409020c190804030b1302040e0d0815030a03030b030a06020a1106060f010905190b0a0e120d0e0603 71
    0x520024076070f414508040c041e80c02d607444026441c0c1c01c510040c0701a0078401a0500981001c4008040140d50007162031004202c0c00e0071100c0074011842240d040051000c14141210f0b01c46180549a00389030510760002c0d88a0100d21505c0c1c81981c00d0f00b15010441e00030323284a1500f250f20081d40c0035464003071108000c0e0031000e00340c5c0111a1003441907018058000b400140210000043e01d90f02e030b0311407080c030700b003c200180e841c462184c404a000080e00034007180c0999038094007041054aa41c01030f03400350000342030001c4d07100e800c000c1c0d858600da1001400d44807040d140d981e207086070381713400c0d030040001d1680305105073701034020300020001709009403c20342100070003504a901d00ca00d903440b40c10803608480a4200010b84034010502050b004128054000c602210043c050300982000030385820018400c650103001c00041c4260865100100c000060202c1040c8594412821200600e10501c5414051145c0381803901c9403444500002d00b2500b0041c02c0d11069200e200000c10030900f070300300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 381753426 1250 381752176 381752191
    0x2010c060902040608010f1503080f180916031b09140a030b040302030702120303060a171c050903150115111903031506080f0c13120c09060f0803040608 67
    0x20788052000503122846564018086800002203d000d0181007078292900410701c03888041008005001081c0308208440c43d50090300d43d004e50700c0321101c1703e2480787c02c00c4600d60b075070100440e0100610f103420b05002440c0e02c125a074040244054242c941a608980396104200040e0804c600b809a54184010110025401409503241590300e9441510820080b1400c40041c1c00104504086042110070000030380011009103085240420100740300d11060f02c55000d200d0014006514480c4003441240e2543c0cec1560244006189102c501520310b030f00030702c170030340c040d00c00e900d0303c40305a121000d10300f410b0391141500f404180c1c01d00c020031904009110061030f02800360360003d130441c0160703480c5c1c165114030944000c1031006004002c11001c0c5425030000c41880145420031031240d50640040f64080b1001310907548820a034015011040003503000f00350034500c8408031005000c4e21016031403c40c2c6054405100303458035244c207900766205a21035600f09a01c10b000511401e801801071541c804103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 381754676 1250 381753426 381753431
    0x518120f060c04030b013201030b030d03050906010902040501021c020718050f130803041202100e0102090f0a061b03051615110a021207060609021306030e01050403050702010c06 78
    0x140103089401d14000762000120344200040410400050307550b158010280e05000720307028100300d07a07142c4110a41c1c140d41154109810080c02d4680e001364000c02c11441e015089031070741981045c2c0030300280029181080c1d079101300f100009040340315000300c8069802c10307800b501013400050219558160022000300540c000c0e24000b080e400c20b2100515100042c0c2e80d800300e881c3c144501648600d69019051900c403403942034052000c20040310803243c00c03903481042c021011080c9002207083c4002410390013426428160740d00c400300300540150a032000c0c12202c0104220307460707041001c07402c00c9119000c0030039952050a000348104441c2d00703d13030328028103010340762910308020a582d880403120100c07000d1254452000c003607050341c4100006065040e06907844c00700d000c1c80c065035500005d2800c860360040083c07041c2c04c22000383c000303200070903003c1415511540254031100381003010380141c070002440c100c200841d42e10140101c900890700750712036500e0f000b5540c004458181901c3c409132103068 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 381755926 1250 381754676 381754693
    0x61f110118031709010c0e0d05010b030607020a1a09070b0a020a050304060c1505010f170a050a0f1406010b160318030605011707051c150e0a0c06051812 67
    0x8164901c038960051203950f61183c1d842c0c0290700e0700d1050070080e1031a6039a0f0701d0501c18000040d007049000d0a0110100e0304030b9801c4103145001d9014118010600d5010300070307a811301000e2500025450f100d24402c19803842140801c201c041c1c0c243c4001c54070741c505e940c880c10781000909003240003068400c04501c15100d0000c5d080d1911407655000d94000c0d0002119885a0b9091041c0c0725988004846201001d1140354502442c04040111300d0280095802d907444040088160420007646d12a0b445400c0d5000c00885090511105100100990b414803964520885026001c00d91506850305050414100100206213404181c4040012014800c14500c011500040759100c00001e610691012407a9814140010800031445103070318410340c0712110070f001c1070b513078012010320b80c0760610603e03400c50200b070a004542e0b0140d02540c101c4e092504003030282c40040070902c64404c600403180d00c4545030780ca4004171446e105052281c645250402ca6001d17070707480d00714400d22040012800719078080 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 381757176 1250 381755926 381755951
    0x61b0a050a03030b04020a170a02090a08010c08180a0f020a08010510140a08030d0902060f0c0102070308060a080d0c0c0b040602030403050d030203060907270e070305061f1101 77
    0x104118505036000d91108415500301a403500490200f550103850660415989620150542c00105c10110301c140003000001e0614050307030b055034245840108410b07c442c1e5907043c09402400401c0400d40064001c1001a07244030426038004201100c0704010512540d0a4583e40d20489602d18100d80c13054400344005800d1409000d45405080420036054840746090110041800c0d180c41981c0901518081006012404015a801c1e04c00b4100e0100306541039200040913481003407003100181c8400704002e421120154040e180803440b0303460303902190f03c0e01e070200314000342d0764814180c040d8000c03000105514865401b210301c1504c905260484251290045202500140c10810059101007410004c0c01070070024540122086d0804502d9400d0100204226420082c100d2091211407200200600102d00030030448001150800200759188c140c034220300310060b601c41000a003040d0200c0c0d05d6141588407100a01d081145c0303d2940305002000355039071076200d85130b4000c9550320850041d00707 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 381758426 1250 381757176 381757183
    0x402070b07091401200a06090c29030a020a0c02040c170606031512030c011e0e0f0316060603020d030e0907030203010e0112150f0b03010608030f0306061b 68
    0x603200380300e15000e600e00000020400d4110f64000070003642046900401070342c100115184200340c841e1525010102d40e00d0f200c0c17a1000c48400103001510304800c003014010a40380c071310241c9820004c800c0d516040038030130386456150300048030206a0b041004c0344011980b0f50050564100030f01340f40524042c2600028203c42e5800ea80401050071036850b0306641160100350b03a80140110748980c114105403d41c07000701411402c03031500902e0b0b1429030545881040080c0c44981c07a415000707000806c0100312021001100300d8004940700c0c285282030954102c04109081c40b100170100035410316690b0481901c14181c15032080c0d5046690780004409600c3d0034500d40803c0e402610f030a0031580320312041c4104000c004120038200340c810b0006000700031031070300502e0468800c0b40300c0d230001c2c440740c1c20303e001100f200300500708502c0d140201c95000c042140c0c0015000100460080140580d0340c10f10356128030400b0117200510004100003100c0d803500740041c0000c1d117410144a10340ca070369401154078 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 381759676 1250 381758426 381758437
    0x9120303091a0a0c0c08070b0c0705070609050108060402160201030b0a180e0c01020307050d050702040e0f0109020f180a15150e03060106030e0a0201210c0c020310060302130e0102090402 82
    0x1000401d40204200f40303105016030300d102d603603a24018403c0706884d21030016600401d00700a01d060020350115240000580c2a50742094011096602203036558401401800c05031065074040368a07900003d440746014400d07500c141d0380c01c02c10001c4440481d801100106664800250f011038020b0011844c80b0581c552880000c0b40c1144c0050081c030f40301c090350301d0039441d010f40504640c01000340000117100440c9281580c12a0300307040e601c2d01014800140030701403c3e03004038210301c0f410840101040341500441c0c01c0078029250107007511074090900c8500d82000c451400d03006144408141541850f5020a0300e0b0f1407190b00d000c2c034045d2070b20055004401101003002c0005c0c5010648051450305100c007a00429040c02e0800c2024800000075444468a034800383c180001400060002c0100311072003c840b02c8903090800c211a10000d01803c4c07000c0c0c0380400d03800b80c840d0741011812030159104450649030004d0021041580140c842000b6100c050b4040860395020300c440c2c0c07481c1d16140050070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 381760926 1250 381759676 381759713
    0x60f021908010f0506030412050d02070206190f02010c1722051b0303090904060e21130e10150e2d032a0a170304030c06050a0912030309 60
    0x2507154945600b0500c02c2c0040d40000e4490b0314200709000000707640c59042110740f081030420380c0d02c0d00c60701101350303000b8060014081d422000000c0c000c011844110100038001c992501c41c520044841c0200700c3c2200c08036400d0f203000c14128450322074900105200c40751f00810300045d05400b01e41183d03a2880104c3c01d0f82c400c0782c4e194002c207a03201041050524980c440300b415030041d130405040030300166032000080d10180c4501ea85942c41c029140013400103000948414004908007000d01c003404180c1da100b2207114020200c01100480c1d1048070041003809550840c0d4080e10107400c06031190319030b04202896100344003260f0100d40c416100c0020780e004100c4210103081c02d80c03200305100001c940c1c3c400c094a100b41c002401c0e041e900c81c000c03802001107005991103032010b0700317171a00403a00c07a00641c0c000d003d5682e4000710660b04010000300900a83c1d2098100c03c082c3c6942d8070f020b8803507000f001c40140100d828541300344000408881071038042d50181c500030444101648030103625211662055 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 381762176 1250 381760926 381760937
    0x1e05090a051e07180b09180622020907050a020c030c0907050a11070b0a0f030c0c06020f0909010e04120c0302030301182409060b28020c0907081e13060f0219 69
    0x4080ca801c1034620385c00f03000740100c40b2102d680c0034001da4403000010841c18501156462411b0300d400ca0b4440c44d031901da40540441d04a060081c4037600c9504100920801440707604a244102e00300407498100c542e90241c00c0a1140d25003a606940e07c0d04442014000c12030901981e81000300c0070412000107001c058001543c40304400801020386031980025818141030102854545a100102149503a0060f000688911540301111100d01c9030f408c03541d030b008200b0300020484070b07032051549000700c1c420760a0400848403072000f0390b821828944040c025800500040040842040d0745489407140c4541c001103001d011880c015884d06041444400d0ba0646407042c420840540720b40c401524602e08034600300050600d503290040181c0c43c1140c50b880000668003c1c050003085220072000d4014100b8180703142600c1c0040821400320340701106a0240d10304403008081c0016400d000340c00002c5400340314082500c07941c01a02040c1c01c440c0300640c0c00c00c03a4211070741e00e8003440b4142603160380e00e8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 381763426 1250 381762176 381762191
    0x2030c1006050916021c050c0d090e01051008010603050a020d0903050a030c020105011a0714120d06050f130203040f080406180812160807061e05090a051e0718 70
    0x1400032002008200e10544203025980100064000a038100503043c0d4201306e00010811800c00c69040c01241e15010052240d5400e00840300c0d0007001b002d0503a0b1002c10803d015a0362142008990704001440c18040b4800b00d0061040d80d109070841c6130f1080d8444009031408e240450140f040b6258030700140d000034804038507800c1d00c0364580a00004c950f0284001d00c425410074514154512246402d40406d075400140e900400007a0340c0040080b45800d42580d1200501d810000117a0b400203030000100740c40d280c3c1c04125407912403c1c0c00d42d046000341c4040d94098140780060000d6001802c03d40368812120b02100005803030400800240c0001e607600381c0000d00c440010690b41f0541c0e0000201380e0051401e03425246420300580f5217084481a80e200c1254140c2400c404900c01c507800900040d05000c494603419240d50188401800741603400c01c010b035100c504a5480740c12145c401000d5421401034508a803003c4000c0010461216003aa100c8954030411785400e004010541c1d280291620307003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 381764676 1250 381763426 381763429
    0x1e150102010f060f050d020111070603052203080601120207020901140a12050316030504170102041401080f0402060a090b0c011a0307080d180803070c03110d0503070204050702030c100605 82
    0x5104080580302d1052021034103260000a000b02107000380d900030801d0420100540e0300c602e11103c11a03040109991a41d0340f40c400c001d001d03007800c50300c0b04a03504c160311540d04407041c41080204199050383c1d0758102030b1590001101c48540d003800c5d0b55400b50f000d221a2001d680c070010103600810003c9125010140c514041c401540750660200c4018140d240003030000c00c2c0c001c0100c5010032401088a80741480e1403a0580e010300498212500c02a001c15440d45c610741c0540c0100309559410390040184218400116507900c0100e90002a400d520004140181010f00240a025141c2c3c2400040301c2d17110b016030b580079004440182400d0303444480020400181c0f619000010b4003d0303002d01a5103091502e86a51511841c000310f04104031040e4186107041c41200520240003500142c03075032080c80381880000000390340000c0e2220150090031800d42c0c6000050030017030341e40c0a8051424010142c0810001301001000c40080d400104040d040709003092040706226202c0c2c03103002400d14201b00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 381765926 1250 381764676 381764681
    0xd030609061d011403031209060106120209011b02040f15090c030606020607050904090f080703020708010b01090e060402040e04050a060501121e11030304080322030305040e1e15010201 81
    0x50024401984152003021404940c450603810342e14003002d40c0d2078940c4c03003202003482c41c460388a8000814400200f8003d030040c0200d044e504880f00340c1c0d06c5900e000c00714180f240c1280300d4650068045910346016210511002c540956403900040c000115050040c41d0507007900c828424146d5002c0c1200e0041c840c1c1c010f54440d80c00303007200510701040b8840c00c15401075510b04001d0714080030705c10041400c00655889802c85407201390b000080015000c3c82d40341030103e54001da4000c5000d80203001010175503070230500c61000d00d90700c169500c1803034614141210141c00f0b40541600d800c80c2c0c08120105005144030300b0355029503c28401880341c08480c1c18a241162810727086a140b005004504134003041424010135808151480b172201107402920344001c504201c03055954042c040402e00188070324000c0040c011703800d1494051011002a1581078203800154003006010807414802448940741c83d03155698801100e84180c104046505040c100b880412160344602002c52640c0f00fa69503070a0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 381767176 1250 381765926 381765929
    0xd21140c0c1209061204060603050307081801030b010f030e0c0904141002281e051305060313170f180a05060c0a080a0309080d051b0a05030f040c080d03060906 70
    0xb0300d1800c14203404002441072141c014000302e0401981c0110303041c000c60360300c284011a03000c4110b0303a94480e180341c0140039800ca084941108443c01e541109994080c0c084c3c95000340050317440e80070144440d07a09500400c040c92010401c2e1046643c016070540b207140301640140d02543c840c0c0c2c80701524070400e41c42e00e0804903c84071150b00600c10050b416006110100952103030189540380d4400c0c0703000850b0741d40340c005221504003091011000741c0540000040200305070410354030721078035101c0c400d00035603207c145d5441c01c0014146901c10041100300d1408849a881c004d030207440d180030154028815040105911605030070410031907540d140c10329603074004107002e43c0d4140c2005980e590003078540d01e5000014080150001b0040000c80c4240d01c5003184640c0122003030344811101c51054010311085400c40c04050000240399080610a41510612400741d624185140d48100d44400b1010001d00100c42a911540d0082a020814050342c105140700d80e50000e5031034500b560789000d0f500b89 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 381768426 1250 381767176 381767203
    0x50910110a05041511030a030e0606010e2803150c020c09091c030f0e030702040f0e03070f020d02040203010308120105060c0304050f0a03120903050f0d21140c0c 71
    0x1000a044502d40003001d86007250741d10b0310800780c00841d0342010f4800e0400e2440c154418040001d24000302d030380641c000c25030240c13441d00311002992424010341d06a0030a6202590103841180c4440d955030a08000c1c84000d500708006024041d030365550f200b50034a000b02e0000030507460340c9000b10410f6041000900e150700c220f80e6400d090400352285170f1200140d1049809040b002081d0702585402601321410450140703504000313046207100543c0d10f0b900443e41c200e21941c200400e48450030f01c18026131200b00201c00186241615076600c0110040d018038040f2f8010705116901c00250750b691001d0340c0214001c0c0d44043e6940301500450b02400b40580240748142000e0003030240c541d03c00016039007030310000d95500e0704407a540c1000070209041c0d50720040a1414958401003070507400441c0c1d600f100d2090044030039080080441581b07a1403001d510b41c0000340e0a55030302400016042c44140d5010b0300100004503446d001d07041c0070407118111401140c2040004000c440307a1420080124038514 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 381769676 1250 381768426 381768461
    0x60906070206060f010f030903140409060504060906060509090405072601050702120a030e100603030c031407081e210105030c0301060f090209150a0e0a0b1201090f020c01050910 78
    0x103013040041d0500044003500d000301507640341203404040c007442e469061208114005511143e64510500c0503010b60b00505000b00c0c200074000400c1c100034050790054034000c0d260381e400c0540642c144108124010402e80d81803040042c00a8045000b50004501d03136030035403031140e1107400d4445442c290780029203d00119400307401c081030201e1080056a075440c0c0e21f4035003c294903002c07140080c54103902840e00c0c4211490520004205074111501d00c080520036240d221a04407003051184043c010810054900b035400c0110541303403201520b50303401c00c9031f020000c5810044411113030214540024003c00c000c3c0310b0f5400500482c642041344940201c0d0450013800b0481c00e25a00c1c40084116104480400e600404c4005041e50303190004401003250403a0f007500c2d1040060000e008494641c00a17014a81a02002c40d60300e06010840b000b00100446512032030f4a00075204005100c8215281c0610f0f90a0001140180c001c0c09102c3c02407070804000c0c5113032800514104220b503407101800d010302e907 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 381770926 1250 381769676 381769699
    0x41508070206040b0a0905030310031a01030f02010503071419030b04110712020c130b04050106050922060504020d09060506011b1403041508070207051002070b07050c0306090607020606 81
    0x640c00504141c3c002d5002c190340c4000d40701c2d010290003518030400001c04078003011041101200c7e400e0040c0e011280100141324001e0110014003910302820b00020b011490414a11360141d4000c50003507030405041c2c6040314200215451052276070f00003c13070612552a515000c140721940c9801000c0401e0012a01000381a0000100400742d20a0039030081c41c0b0000306008095582c001c2c8003940688a000d002c1095103811070892a0040c0496844107116610308800841c2c001d00ca001603801c104006407659008884100c0c199481d0341d08844182e500c02e8a544001c5020f03152800a003000c009903020210f1a1801860000242e03040141410304100a605218018542c1820080c030040d400100000e06500b20b0750b031a40c1140301d0754101e003022003051016034549a9000c030071a48202071560a0390991a00c450400046d04000303c90700d001603200e4902403141925220042495600c41c004032082242d410300400e00b40981150f980c009900003c0c01c0194068041c081c840c0d000e1802c80b041c21520703 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 381772176 1250 381770926 381770941
    0x4060506030c070f020312030c13060c0807150902041107060b04050f0f071b2301050c1b0312040302240403121802030f061008070503060406240b041508 67
    0x60040d69006020f080340c02c40442d0654800b8403204190040c1003103d2a9a07241000c1c042027198800c126400c00314603003400028520b0711a081050031694000c50480ca080141e4032580e8000e000c2462510400fa500d840f0380d40140e54a100e081c1e462026806095240d0050341450070031140b5a409860155040c00c04121140c3d03400f4140b56401008812180345546031321204442c07a2180740e4800b42042c2841070504107110920748800c050030515040014041c07400040729082c4c643c1612042a8400d00b848440c01c3d070360025468003041c040203c201c81c1004100703000c807000c0301c0090350190301503045180d00394214841e608003103224a40c4454981c809007480d035401050202114000001c00759038000c080ca6407456250f019040540080440c2c2d8010b503403500c01c603116282a1044901c481a55000140d200404150402140e10040c0a01400e030780c0e42c1c80d00405002075030000241d0001e00307400c00400c0d40401c0d007c0405424480c020170b88a41c140040701c0c00b4000c280c244c4a0a0119880802400707 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 381773426 1250 381772176 381772201
    0x20106120203210f0c01062409050f03330c070317040206040905101815140a0e0a1b11100e030c0327010c0305030106080702120301060203090406050603 67
    0x5414941243c3c0c840f204096140f419000340c104c500c122010008508200e1041500590191918410040e4a840540040c82d0b11819045c06820100c0c0d06100100007510341203041c50305600e40039040d603030403081184016050b15000504900800500048000c8407000c28003901d500c4009540c00300d14004203a103014141501400901c1054002d0000140443d00e424040d58024660280203000c07500b004000c0c015140300c075004120003002c1c100d10071140e404a40c0030301d072034029080b120302922034109060f488414081001c0c5035000101c0d600005140001c3d216143c1c416003201070000740d1115491062031141e02c0800e815010022038030188854134602181500c0c014114400004502440162035415401602c01130146800042140c9480c1180d51034000b81c258198080c0c1400c403c50340e801921035885151014000034428401072101034000e8403000d4124150740119100e00203001d1030301d490b07030340b09800680068001042d0841e0364100340c0103140c09004115810ba085280c510500d550 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 381774676 1250 381773426 381773443
    0x15030201080a151703070506150f120a0f0b070219120f020106081014010920070809091003060f0b0919020906040608010e0f04170a0e130606020106120203 68
    0x80d60b501c503c8000301d100c000994009103904000c6940c807102503c0120340302e40025001b130790035004400019100c0107030a88103249940009020000924030301050102400b402541d0f000f2901c600e5a040c804103091104c00300c3e800780301c3c1c2c03001840c07880c110f07074001d0400e42c40c840c88000c0d42e0440300b58040001c03641147c1e0581d40196182c015402180381400703c0c054266a401007246001c0c03440c280407005119040703070410030b4001903503a01e242d036541000400c81c0c01411200b502030745a0410150503410030002840003074050800181004d542c0303400100c9000f42920740d504082c00d071000400c01c01040d409400d00001070001c0401c0302800c02004102c00d401d0040c80d4040d50600c12001c0c41680c0840d9040c0c1d80310020290020b41c58548074000603206071421701560325803085901c0022542542004250b01c200d620558140a0044000d50340e0555004800c2c0c400602255001448641c1c854100c6030030045051800443e6151078410060308440d01c94003c90b080403038407081c00002d81c400144404d03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 381775926 1250 381774676 381774691
    0x230709140a180f0813120b0705071407090209040e030a0c080d060e0109050403030b031b19050303190e01020c01050f0706020405090c0a030b09130f0c0b0d020d1503020108 75
    0x7811100751501c8010034490410040107050008010001d0012201c00f4022200344000d5a03251280c0b0b4820301403000e21b803803200401e81d600d4100016845c9108501410030240314203543c050120361100e146003892250b400c0880425404905041c00b1326081c024070080001800107180381000d00e40b130082c6605010000602510000030b130301c024007807060380041300602e900d80040880303503101c400d80e20240006460030350009003000441d8250b894040340300c103540580100280310720b0440d00207000c4076066018500b1890503400000180e252018001080341c04030701c0c0d001c5000041800c0002d45064665403050381103500c0900e100040e641c01c402103601504072142156120001490000040e10998004503084075010381880f0310303640100d02403e000c000c2078609001c00c803403030001d00101c403200b0bc8150000700d12420109020400741000414824084e03640150344a41382c0095081d40e41c88814940c08050f4009458105840b651094080310600d141a0444141c07030750300000d2201001034a600c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 381777176 1250 381775926 381775931
    0x71a09030d230603030301270b10020321010b090d150615030606030234291e1f0e0109020c060604090510020c0703230709140a 56
    0x504488080007561114910340c1c00c1406a8003051540d0102c4a4141154007415424040401e02924010040d28107a4440d0315014101c4201e6801d042075160f12415100300043c1d88201c0001d650711129803080000d04940c000b1a9204640060400d1580343c200403403204640c5080140170405282c0c04458080300121081c244210351400d00b40403e8250629405101d031814000213030340c0001240d800e50007600c50b1802c101044d9100030940591180c1d10f0000c002d080381002400640381e00300318001181500f190b407105240c02075030b1802070004415842e24085d071201d40d00b001c1d0540c21007681507801034040e034080414401c0c032000b4003040c40001d400030340c220b0b80c0e4010610140d030410748203100400800550403040d503590705200c00203520038070484445004880c0040d019050500421a0b141e9104009001c07000481c01144000e402c541f02a0300d031800340c0c1c0e0001000c1030250502c02080d0f444016040f80180045114a00d05555503000c00e4125003041e000040c0130314420340443d40302c1b583d120702 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 381778426 1250 381777176 381777181
    0x3090607060b04020c0601051810030f051606030519110706050405030c060f07030605040e100e010209040e030d1b08010e07050714060a24090b191202031002071a 71
    0x200300640840500540c2041c40410303417010152001803664121002170300c400c000c8413905000404448412a000b410720301d08404201700241407440605140c50144040d40d00501603034525a0515145910a40029440c0c1d07082c0107116683c4602400040c41c400c008214241610840301c0d0640185400681100c0d52030340040d090090902c1114a00c1d0012010f030b1342d02d40f6001e0b80e2004944005c0d00c06a001034600100400c207030401d48245101550a00700900e1041a1080000041d15400d003c003416035400380054281e5132071714000c0e4440742005c20081e60309c070055a80307241b048a400c9403d403103c10f9403242035103440c0360700305100a054500d0580c1c00e03003890f1b0f034000c425501071040002c01000d000d18082e550342d11400101c0c0041c000c00d84000300b841136140d05008136809044640c0448082e6000b8074040022540c0e0303520483da240000340c802e001c10900f142071421200d241c1e074011680c080c8009204004c40c6418030810303d0314446030804600b0180642c56200c1da0303c1f2a0045030100c80f49004c003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 381779676 1250 381778426 381778433
    0xe0603030f0304050105040b16021f06080118061104050a0317070b0f0f0108120f070f050601150207150c06050604060e0921121f090c080612070803090607 68
    0x2100c010a0103035401d95034a041030701d810342c02088120b0b01034440713000c040c4c041003888141030240040302007070741d0040c40103000c495101d100003000102d0400e681c0c0e0f1313524400101403800b03001e031107920080e486a414040e140742c01e2400990b6100310107000326250401c400d00a079511101c0150030307a500038203102d05244005003d00d116100300c580c0942011288410050360500c0c448070320b881940c4102c107080680c3d0383c41d9200e903650342882c0400d0550b50720a0102c5400018080007a0030410300641044001d84029190541061820703045940a2001c800c00303405590b8041000c1802030071307010280f4880f40c0b0b130034000810000e06150000d100c11b0301e91000c0760817603599400890113060361008021160178a650721680d2121f02030071502d1082030208006500c2000501030360b00c1300340d020411418554440c051540c0601c1081c03000d1000c2c0101030b03008903200307140380704444507520103441710b00c003a042100c1040b103902000b0245504c10b0780042024800204080280d0b020000d05494007900c1c0e01c549d26 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 381780926 1250 381779676 381779683
    0x106050c03040f091a0307061b060f02162a0504090311010f270803040204020a020a120336140a0203010e030901081008030a050d09080c1b030d02070e0603 68
    0x38040310705642c0c2080040344e00000ca900a03c166001100720080c0340100b981403580b80e005521031000494103511260304e85c03000d94a01d14124501c20f00002550018194401040340c0004034001c200c1a600304c00417080160044134015420811000d002c0700000700c0d540744c442c41220f802294011502d0384007070420580032307042100a0f07080d070600911074180100310301c00080a4415503080ba56410508860340300e215801c5118203540c01000d5a40746550f15001d1102952068081c9011440f034249040003040100811070b0325440c440c1e401188040041c4001d403510740c0c00708031a90301c000d90f0080324860340340304041c40b66600c1e070b2110302000003034035103503a060500c08185c82c042d400d0f50030000c040840c1c000c00310040400781800d0704c40e0320242d2030341004884403d0340c070b00914400c0d6004104501da658003400140c0700c2d42060750b2011448040507030741c405003070304065901c000315405011100307124040342c000102e08581c2030300200002c41b5500d100075a51040c1d44120110041c4000111b0200c0d1403d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 381782176 1250 381780926 381780929
    0x708090301090b0708070e0303030c070f0f06050f01090b010807030e0f0706030504050708011e110d020c0c090c190e03070e010b120c1306030c110d0e270106050c0304 73
    0x9000b0040302c2810b00700a42081000c440003000510b80c8000140200d001d110b80c1c603100000038004500b141d0b14400841c006a11029082e1400c000301140240011000782182c840a441060041041e0500c81d0705001042410303001001c0c450708205a0f40256688140c0595000f01c2928001c01d9030304417901840e04110b5005080ca00c03d000784031020980da501608020700561007a0125240d881d601c501e100e0072101c0089941a50041c0700d04501c1d04007c4e6900481045101c40e08030360b14203a0a01410012a0b100b40c00030840c60300a0b00c070402c01072400a400c1548402d81504542c504444007000d400b034403038030341801d0080c820f00ca03800070b0041c0c8040041038041c16100740c90b03003d9543c55950f034803140c0e0000905940c800300751000040c0c0c514a42e0b420364071030b200581002a00340303081080030360141c1130400c001010400c040b034010138450420809c43d441480300c3d80f142944200c8440901c554403112100c0341c6554501420f885010918910003213045400601d041521042c485002d00d0031403045 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 381783426 1250 381782176 381782179
    0xb06190e19062c0306040b090106082a01080f010b07030e1003020304021509090103150e16180213050607051e1606020a0506010513152d1a070809 64
    0x4001c80841c4050b0005420340015440e0107031606641c41c410000c9181603016110240c168009201040c0001d6164400e20b4108407640d00100700340740c9401102d032400d05626040121181540b002e282105213454030340303041d50001c0c607000d41c192600303031701080951006101e1012007100004100040c9445140b500c42401002000c2d0006281ca140b00200603400643d003e0b072240b0311528449100e035140208685070640080c0200e60243c0c40c40d213841001200c424602510103071100d9000d04110303018459050b80944a03004a503100b81407040300164907501c41168804984100580035100d079044c105441240c0302100e21035550700183c50058101840d00605450221a00c041e4080300e000c0401c02ca003c00322014112085155644030032030707841c4012503025200b030b00714100612241c00c0060011000f150054404a500c0401500c0e8082510459008001c00384c402c80d81c02c040c000c001c4420f10b6040ca031401178020303039906000322601c800b0426288206100c800041c0340080141c81010398484660 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 381784676 1250 381783426 381783469
    0x311010612110f030307211103030a050709150207092f0304121d040b24093a03030b04020d0e2a0108040507080708030408010b06190e 59
    0x11600c0d00340181d110b040308580c4101005072188001d8140002501c20141d00188142c0f04d03072413204854912404040b421608100300060100b00e120410002035004081c11a800242d40c900100c004100c0b003c43d80014880045060301d240312294001482d2043c0c0c0c0480f14002101841d0031448030800d0069048800940824195000d0400c80d41001d188070b1800b030840056001c002c07040840300c12510074482d8001840c1c0420808442c185940a001111070241c03200b980c0e01d80100064110404075001d010a401d00060003070004d0504e580d00c000001844071013015483d0000407a04504d0440c10500b6418000410245003494420f0704070360960100070f0300441d514000e031900300010380505131301c03400240b00e454401040702c01d091081c00341302c120000c3c807511032503500001110300ea040504181c3e513a12455001007081d140a0010030000c040700001541e407645024046400d41e82c2e045409803056409001005170301f840d00d0a4a40c0344205441c03c01d198982d10000110964484041e000d115003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 381785926 1250 381784676 381784709
    0x18060103120210020703141b0105090d1d030303070503070302070206130501170415180b100602060705040608011503021c0f060915060804031106090307021e03060403110106 76
    0x140c414a9070407031800d070b82510040d11624554605910441000400040c2855a10160480000701408022176540c04908a1003842d814103030a55078142c0303160426410900d0f004460a40103400d20030032068001101d80031a0030040081c1e2240401005d81c1d044c00f400100003083d0700c1c461b80c1290f02180d402403030503854a043c4a5050141580c0707002c0c0a010030751303040450700100d00e4040100d2049a1041105880702c0007810954050040d000740b01c0b00301c000029442001900750043c244c400c0440c8004101142d1a150000307141c554040c00110512400304000d10526900c41d00c910306403540a0b0307904040399400d5208a00a104055440a10310103030703104001001025009042d100c0350b080001c0c82495190280349084031803034038031201c00c6120161b04010f400e02032441c4a0340306010342841000c01505c50b10060600c0070440e055002a00000380000031483e015812800c10f4100003a4001068180c0c00440d540381b00152024044c4000c6051015500c88250440c0020b000080002e51085 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 381787176 1250 381785926 381785933
    0x50a050703150b030c130e03090a0e07030b15030106080627010806060a21020a081506040f0902011b021f0315080c031504050c0a1710180b18060103 65
    0x60000100aa0b00d05050140042d01c0b80b800180340764014000800c145079209241034400020440d24001800c0743c0402c0c064411035682c0c106409004041180406415252141c8002d0454a03504040b81c45080c00070549542090b00e5810f0b82c3c150717600c60410348226128000002e201810400751088503070520700000d803583c219001c646040391550003c444207503c841041111403c03240c094882080e84600b011088140004a203940071800035004148641c0c5071494035040500c590341d68000540510140000760a01303124101c010300b403190f820009420b803540024560318004004201d0944421841c40c2555290100041400c074044150b131041410b403000600a80600c0d002041c064041940c00260000701045020b22140000c003e0302e0070301031344260901150005001900c052285d506000070300d4580070104006401801d007203000f180700d201c0107103103000c0320301c0003551030301d82000c103003141c5840c02030b18075802a9031000f040391890340c0d10b402d50f226451201401100c58414000004281b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 381788426 1250 381787176 381787193
    0xe0102070f08071106090d03051b1c120908040b0711040507030e060f0412050c1f021210060905220606050c06010f12060b010201020d09061d060408090904050a050703 73
    0x740340c8140d0340961200d20784803c05c2014001d44031005d8000d621000603030b0009109100070041401035000e90294043c0c04d4607898502500080c0c008851501215011401134000e4000c0c025403e540c2401e005400302d40c0e99405d1180902d2241e07071240900401c010f41006607101e140320024034068820060ba18021000601402e0a20a0100107018141c0414080e11054511610403034004404002c10408440111082d41c4102c2c80d42800d8000d100d54108020400c0030310341100404c0d040c015894140d90000c64184e0300014045e403084141ca031304c00300406600189460b085442c211500c000238900380c100603183c0d41d404001003030402d242c10350203c0d07001c2d0450050918200301004644040e80c035000a8918011310f8080d50300d00d000b0121120300018a660000e0140110600c00581402207400240d41a5040340801302d40c000d8482480d203a4000440800d8081c0c0701c03600000f01103604041d10340c54491b1040940c0e041c0500f144900150a21200b045a026850703401001c07142c1840d80d80c02c0440d513 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 381789676 1250 381788426 381788437
    0x60705100f020d140c040e040305041503060504060b09031f060b0c03040905130b060d031101050901090201030c030c09090b120607110706030605061210180207050106050d150e0102070f08 82
    0xc3d040c580901d41410254450301e4602c18002c04510301e28080c2400050014420000e00440821401704002310b0110340d41000c00c0746c0740d080350700d0206006080c0720800080d50b6440e000511108407e1111045680d00003900e4105190812495682240c80c0d01d8008050820764002401040d800100440080380000c01023003101c0c141c40041000781c81d5642da6555091103003101506890501000c507105291492a00c580359100b401c018007a1200715040702e003922002c884012159640c1c401c1801996014015440402c811f8a420410a424820003401c0d006075030046002c0386540d4030b0a405981c039100101900408080204d800b6031618a000034015242c4e0304904007a405440380000e00c186c040c0c0914829114020005801d1400d43c0c3e81c0b11041032401000e24840c50607507100010b0a0300150003035104024224800b5a0f0780700705c1d0a10742c3c2501c1300d5034061400740c40724111030000301d003000f0003448800075484004120150005c0c01d460290050b60000303007c5451044078001040701c004000c09 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 381790926 1250 381789676 381789697
    0x60406050109150806010c060f0519051b070204180c061803020a031b0332061b0d0204090c05040e0f0606160f051c0809011505060705100f02 62
    0x40100d840300c0044540e0780b2144545107451140e100e0505a150003000716507445032043c900900604015280c0301c0c140d803045c095581c142d039035480c103010420048803c201e11941003440103004a00f800468038004059101d4003104008003c5a0b4404560300d6030401c054041040c450064189024141030302241c0c0544614400b00e080b86421001420081c4440011030b50010100c040083c03850f184d41000d0000b04000406c5003501250110014820f40c1c020326009000303074124050403110400b4003100c04500c0c0350440b070541c006010092200b0b40b401204034081460b0758541d4690348280e00c01c4019029a0b0498112182008480108564081c01910032610010405c0082e5260306400b240313901426200503801410800103144048009000c1e518000c2c414100b110100b481500c0f6581450f02c00d003403003403000070a120200700c92a488101a50440c007943d00030480f03500b03241900140310300c01e4894140141c9010071020300340001401040343c2180032000030b01909004110b0000258000b21065 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 381792176 1250 381790926 381790931
    0x610051003061202040c050702030d020d0f021c05160b1f0509040f020906030a0b1801050f010602100c12021305090907050d0f020d02030f030c01110304021e0402090a0e0604 76
    0x19640d0520a000b000304030344801a4007440c0364215005c0c0401352920002440603c1010804000140c8081040b1000008281e001e0891115854070013070103030040c41d80c01021584012048104800001e07040451042141001503880c204121004807001060ba03010388603074101070401c80454000c0c0e100000c211412a0342640c1181c07900104030000e4000c1e40c010f81060301c0c0072070040040c00c210b00400c2c0c01082c002d04481c1d407226942d030303032070241c41088810140d080c1d40042d0603030011109006240d0402810b400b0034419604251000313540716510310b030314003240d0345410028802501442d1320003898610b5100565543e28985098025203030703d40b0a0728094405070300000c5400c4130215804042d14001480c5240c071100f0f0f902c038842d240701d0182060368800c17401280180165030030080700c0e80e5a07400340d010315281d0030b90b0103d4070300b11806481c034a00c2c40c9808004000040e0707516030b920318810b0021103141510b6a94100410b00138091301c0303541900000c18100100744520346d1405035219130700c2210207 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 381793426 1250 381792176 381792199
    0x50102150c0a08070e0d050c130e190c050d0b10060207050105040b0c030f0a1701090209010e0108180613060b0607050304170111040b0403110906030705010c05030c061005 75
    0x800450001ca9070581ca5010074000c01c4909803007519191340020851500040c00b0019200040c850b810600c0121020b901648070f0010600301615160450f4090300e0041021599254030342d500d50088469200052030120f0751082085440e440b85405418003401c1d50611040600e0f24413501e85c03007690410fa05200760000007461520005211301a1001a525281490f00c0c100103007180e17030800e401c1c00103a03000c207101c0c5046001c905c4019200d840140d594050860240038000240010180c02c11b603100d9004101c4241166000306600d045044213183c0058141c1c0d5085603149000e40c40003404405001300b00501840b580610f1502c50740d0390244004000160751042001114440c41c403000700329030420b001c2003084100c10214030103c26000c0c400440c40150541c4403005aa0054100c04a0001d001c10f00340144482c4c500702440c0785c0419a010289030404800182d51040144600fa040000009070b44041210034020303201c40726041000c4900301c0c2002c220010091056000e2240110701070000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 381794676 1250 381793426 381793453
    0xe01050a0911150d0213061103040b030112140a0b150307050f04020f041809031d010c0b0603070e13210c1502190309022409090403030b0303070606050102 68
    0x9070701c001c581d00c40745910796800a034082c80042149080e900c050300c4010301c4071108403200b90000f070104100280303802d02281d041280c040c001c035511044141d2260310a20061080707145450869040d01c0b5080184e4043c89524138100b5100e1405400080040c000c000182c0100402e808015019800d800a240c29004071030062594a0412784601a4041043c00400d811400c181e402880c0706400d0040c4a45020b8071403d21041601b075050311110300c295100703060800e0540c400d881030f40759070910303021140c0324603190f00081034511100300142040900383e001c140d0343d9804001e482c008181165540e80545041e40d10480f03c0b11102005480c0d40c1e48400c1130600d42c0c0e40c03001c5030101440c026143c50f001c40344140c94101c803005c15500c10000090b030801c0b89450504441c40300004003402682c0c00b00301c2c4101403040c008101d02d0040340d104c01c18040300c1d5002120141a00352412003406503000d0031250380307509044001d406080c5017541c2601000a0801c00e10240e03420540550b0800c1c0c0899001e03102c0c503070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 381795926 1250 381794676 381794681
    0x70f080a02010c0b0901090210050301050a1a030402100315030317010504061d100b030a0e0c0105090d241508011a10030504021f0f0201060b04080a03080a110d0e01050a 74
    0xd00280003403001e1008000080b40c4c4007030960010f422000000d20714640394042500c3d0840024008017092020004200910b441000d60024203030300a07000000303000c0c10030b0b00c44503030001906c001d1040b10701c0450b054110b8401d501400201440103604c1c003060382d490401500d8000e80226902041d00c00000228032410316000c0e1004403041c402021906d07801c1002426613886000d440700100800c2000b001442d0300041010f5070240306240c50000d40b640848070610301e02078440302c000e81400800c0c03000a100b95213010702882041e800449043d1500c001ca800d004c01c04401007010b6503a10b2600d1428805000c000b440340c419600e068000300150045180210840c40e4806241c540c426510140600400d01c80e421190f0018805491000058003a00c070f5071740b8080d040c040341400544203905080302035509014440c01004009409c038035041c1495440c5071940024840a81849400d8010880887c0e41c2c0d444092290200c0c1c144940744d4041c4003d01026165101c0b020400d5030815022580c1d241c3c161 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 381797176 1250 381795926 381795943
    0xb0403080301050603040c12030305061206010e060105070c180b0108070206011a0721050d1d0d0809030f0a08100914040201230c06061512150d050f070f08 68
    0xc80741160f01e001c04106082d03100401c204e58150841800180d6130440c1d280b0781310194403c0d1004a018900072052100c0c14030250008259580070700010016000a8040c80d90001c10a1800c182e503151181040460b0440c1ca500044013401e40c10994142c0b41303074551051401c95026a02c3c21510348842c801240e0b100028011208054080085d405100c1c010301c0040c115144180700b803201d0420a4203800c10354001c60b9140102003140065a82d0480280d845000342642c41c80c444211b00111000d0b040d03076209202c4440c3d0040c4110f0340085101e00c1d4041003540c40440804108543d030b0341213410001c082c0794007a503105c8500c1c04412000b09006486005001b40041425441400c5a440f50011622103054030100c0c01000008a0200c0d45607040c48010300b0448076450003810682003a9041c01404844c1c000d82401001c2c1c24418840c07004682a503150300040f10081c1c0c45e101200080000312050b503105d600800c00d104560101c3c0751900e000c11820300319201201c507558600e940304c4d80c243e05c1d810803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 381798426 1250 381797176 381797183
    0x1324020d11122811070504090b040b1305100f0b04020c0307061109040e060f0a020702131104090203190501060311040501080c130617070c020a050907020a0602040f0503070b0403 78
    0x3111208107000040d8001c2c000c940f83e51000c4800c0001c0c0e040c0301c119030107500944007002540b15894001034000400a010040a054034204081c00031a02c8000700c401c4050130040100c8603000200f20b407100449203124130365412a05030b035904911070744220000d2448003200f01c403441c10408001403a00e064402d0392804a05070016515015180c4d03030f8500104241c1e03c08901070f00060021030340540b100d129003d280c0c0404030090029040c80d4a80c0d154190b0014030a450581c010040c0300c0050300d071920241d0f021589a003000c41c0e05034582280e1034040c06250000d072503551010040003e0001241c0344c070180d64010007000c00c0a40d0305c0d500e013201a03c204549000511a0400c007c20455102705001131707020820300d08203424514080046043e0041a03031020700060754200f0034900240003400700c1078000c2864103207529106c0840c0e0111740850440c0c400c082c82510441b001464442c028000da0300d4a541c0030b0011582d65484840e001420310540c02214040c0c41043300100341440800121401d9a42 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 381799676 1250 381798426 381798433
    0x318030607052208010c02010e06090102090f220507120b0109080d052a010c08071b11030f0a0b19140f09071814060d0f081324020d11 59
    0xb003c0a01d40d40e070141c500d01c0b80d984040ba030000e1040c10a115450015410740c0c004681c1f60110803840e46004005007804040d64410880c00e00a5900c145012040010581d9a40c0511115400c40c00c1f0b0415030f00345d9084454204010481e03616809825401568080c030020454110307101c0045481640600858002c0c3c0d1140206c1d001407809200580158400c0c184100003010140d594611707011009030034212503039180e4507000d0072035801c5400103a02010310f181648254401e85440c00f010003c1040150140c3d0460080c200310b41c5060241030004081c0604a030f0f5840810700c0c2c0400882001c95010011202d280300c0807507010400d00941d0100c0002c0d10040c00e554031070f040c2c880c21820340605016802e03c5003010000b0002c1010b03058170b079407900c06000012502e640c000403c000c1140182400c1c0f06031888664400096102825060034a40002a6270b80f80c00e4180d25074665503074190400c4203c4c42482c154003150400d11114551941150740c20b6a2074584501810743c1c031300f03204c0500c240301d541 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 381800926 1250 381799676 381799687
    0xc0806090f04022116090501030b0c163f0207090b010203091216030503190504032103021b010504060e0606180c0f0a110708071406070203010603080408031803060705 73
    0x40c2a5501c0101343c5410042c2c0310101c0070b0107801c0f41011030590044021310349441c01001400100e00c08564031030444006646820000495406601088407000b02070030100310002002c92524800101031000c4445200fa004142c041d94080d04034040000f0001440780b4680800c000505008a940b1640103030003c6003000d0085c401c20100c082d42481021441c490340c420201110003044100e03004600480140d40d5850007203500700c03481c242c1e400c840018032104110030000281c4000c4001c00071409081441c5231b00c0803003c8114041d1069100c11130030210145071038249911b0640c4214000e600c140307010403826010000c001e0700c51004940382e95000ca851104c1d003024144440300d09610102e54501c041c03414400c80c0342240c0b1b603000f0040601c00541c4201442502500030003100c000b40034480001c00000f4a0304001c14030307081510038400e0140a01044560441d10b094100001865002420b5901c17545c854013410750300e8104001a20710344c0b82c0000d0411130303420007045040c098161035451f6840c04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 381802176 1250 381800926 381800959
    0x30a09050d021201110703020105090703032a140706030b2e030e07170c240901050c07060e0108160c110f0d080a030c03110d1104090c0806090f0402 65
    0x9030494405980008116a03d15074414083c0705044c0400130a1800c1901c1c4c1416090080c01c4480c014180c4065a009001c00e20119410a1606060032900225a0442150081c0d0342001007441e40005003d1010345d4100c0c00f900e000401d461056038000da070104540d501c00000c01412001c034000800e2030349105000c01403035408047c08900c008416040218900c0d810311b04091900500e940000306d0059800c00c9401025400d02c80c0f400405000c236141e4049000141003c0c40440101c10000c1d007004001510300300b564002e205803800382000c5002e84251a43d100800b902c0490703064030141c0001e00720701c0000d841c40203d407906800c242890361740c0c0200d800c09607200b84214850f035504c3c960107401d105810310250745086c01e00312624458000c60b44c50740400078000e404d8440201c012024507080c84100c000305240385052710222035980c20007045142c2000412545449a07400c41244141040e1060b1030031078210503d03901840701a18211090741c1c6040a43c0e00c461410340d0025800030090b15001c099 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 381803426 1250 381802176 381802189
    0x60f01030c02070b04090605010f020c091f0513200a0903030e040204030f050c0102010b042307030914030711060a0f08042d0b0603060f04080a021204170c03030a0905 73
    0x1d00058011582580d49420291640e80c10aa205a10f4191a0102400256072080f801681005d040c00103180850031310000600c050002011280400e07001003807950360a054800710b0004000c09001ca91400e042c00c81d200001d407013215420610504250722101080364071008440b419003c3d40d0f9950503c90447d50101d0b0190060059181d02070f0b020b02c07012010944800b5125007440c8150000e00c21200030f100003900b0364120211a41c850782c501040c1010301004401c00707503121303200007a0050381d9542d030350b406500600c0407000c05090741d035001c10070282d8018004020080300b03028245c6000d403180108200300292186404020001e0420000000b2840c010301c1000c0d003261046013801da051002c0c0b50300c1285071440c03c0166010b00040300400d401c1c440440d65a540040080c1c015048500d032910340d140d402c000c0584028241c8600040c200002482400303100d00c600e450000c1207075240d80d2004040b401c164880c01c121603038020701480e40b4481c030300001110440001903c2c2c40c100149090b040040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 381804676 1250 381803426 381803441
    0x601031e0804120219140108040204150602071a03011d041103030c030406030501090605060910020a06110702040f0e10020f0d050a0e100608031603021c081905060f0103 74
    0xaa804001580c280020107080c040c0c406011a28032043d8080707114010882c4051921402010110308003d0070303c540150304014940001d400e003400d16103034695101103070040c14a4540000c0c1100d0561010403d6540400d84d041240c0c0c440008c49140c100344128078410317110070b100304221890184600a00840c101c021258464000c00481c130709400e60304003190075640841c04080b1141c20000b0305004040d018803525016001442c010005141054013140e83d81c0b00c0d081042b40314514881c10310682620030000145000e43c4001c06000c0e5030440300482007560440d8008a100d10f06241c00100103802a200d40004a010300c0014403c40c0d00d030344006c81c001e5202001c14000444204400008010140107017401000c0d0f40c031000502021820005080c0b14407000e104401da03040041c00c1110300030000070b0b94200360718000001c0040c0540d10302646414409104940782e03a6000444040054200380d030184035440305001855a17184800c00402240e50132294142d1028181c0030003041075100b07074803104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 381805926 1250 381804676 381804713
    0x70201023405060403050a020708030f0a03150f09140609040c061202071a040303060e07050f0d020918060f1023120108030d0c050906030a0915110301030b011502060103 74
    0xc20000d450b16420710600311030035008680c00007007101e01f1944c1000500010044e0070090340c1400c0b480c0d298050a40f08140d0810100740e11064000000c0540b022020001c01c042d41108035400c2d69160044094161020200400c03018100068060b0a1800340b291046900030700c2903072000c2c1404020307a184001241d04c00d14071a404c1c001c1c90700003161441620140703801441c102c10f1a14003840d0042c1503d0042d00101d60000b489418000b142c2d07044030a41d0700801064029984036458880218024041c0982090340020344202d00b44800c0f200c8105680110429120308904400780c80900152041e00101100010303031800b80041118564100c03c55042d03040001d60b8a04007010580001c00303042a000761215070030018441c80c081d940c5114817032085106050160030320041000081403130100415030507000d502c800b003060800007d40400842030340440700c2040912940d4041c4106504240000c8500310b0341c03c1c00116000706a80b2405000a2582c2e00400c980c2c3e003103aa0389050b198404c3c1418 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 381807176 1250 381805926 381806017
    0xe01090321050d0204030506010e0702070b03070e04020f042702030c0906180306091f060e0619091112010f0308070212330a0c0f031505060301090c0807020102 70
    0x180e102c43c180c00100019405031006080039410460300f10515040a040b440540d80400c01c100072028107141a00d500071142c0c10491600854900498060700c15848840003000c00001d02140d140c002000700ca00303030b0810011005048030f4131300d41d0b40d04a103c241c0c2c0d0601c9106c0c0500141d8068034201c802003044020800100c5410011600802d14085040d40e540101d42c000e0103051844c0300d60385e990040900554541440381919158003500b90350800b618150041005000c1d81300301e0710b8421502300061044113070810180340281420304c51900103040301c45075034001100008422075002180e4054035045000f40d454526a58200449240440144c2c04180904c01d007c00242041f061265441000b85039070103000310a0114801b0030440080c01008100d00d03010071400200e502001c0a08000c502c1d0400040d001d007145804482c1b6040c5621995100c1000000400c140d2042e40000e03045100a4407215030780d441e502c500b07a0a0380202e10203c110011031007004841440c450903a030240008841e0710 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 381808426 1250 381807176 381807187
    0x90d0504052431030f0210031b0f020706081006030902030708071e0909030e040c0e0402030a020c15010b03040807020f040c0e09010501020f10020904021b010c0e0109032105 76
    0x4800040d000783c1c25443c0242140399154482d082c080d40044484282c800a020348541140d035084085428400085d004082c50825064290300135484030b10340b0032071403001d0444041c501c4801005d00007690105401809a003100140180c0035100c0305010340c007510702102c203490504030100d00901990700b003640d140c4102500024846400c0c0321000c00f9100e510407580905064003450025500f480c0c2c00845c03640c0c501440c800221fa0300155031000c010046a02154810105500f00c6030503048100360340d400741c8004148000800554001c280d140488016190516606002212080340920802103030030401c0001400081e42500200402c83c40142a030700c0401580002c1000c443c0d0b844071904c00700c1c20111020115203400e5481c9401040240700400c410b86c0401e080e19180d076603001ca540300c10780d00842d00010565594064660f03a0746e034020342e040c1365240717100d03018040c0c203c42890201280854050080c01c2d4450200c01055941002913030111010b4030005603040f1490309007490030013405001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 381809676 1250 381808426 381808489
    0x81204090b1c0302010506011d0d03080a02040504060b04051212040b0705030f03010e06040e0c031504021f020604211707140d1d030a08040b0c07020405041406090d050405 75
    0x521a202030203136000156601d000390014000541103d080d0005512441008140760703600e04071140b4440c1d242c0741007441a182c0f6401000030340035030740106a03c1420041c01140e8540d250001d003007210310480d142e21443c11615201030701c03041c41d00040610710800b00814480f02082d907008015142c800d90447e403500783d0610074031074503070000e07003050184440b10410302901c1d1030140104034441c02c41e0301c0580001c5074910002a80c420000700da401c4800b15220000b4290340c2d540148a42400940681d032320f1140c1c080034000d440d400115801ca50180c5000c002101c0c150b010b070a421690360903070710307045a1101100901079200c50002d02800800040004202e55061440003a01c510300410901207075030124001030848298403120740240c2540305101c402440d584c010925a0003a4201e60418000d0303c81001340070b02c51041c3d10000c5d40103803d0030180300070080c0701140c00040c21a900c0503110280c0350100425260310351303441014001a41404140b18518100303080d074455030300c41c005030a400c030711000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 381810926 1250 381809676 381809719
    0x120c03100918200918070306020c060402010810060210020d020d090804061407151d010e060708070804050a0b0a020913050403080c03090a0b070e0d050115081204090b 73
    0x4990050408049845000c0040981003141d00d040111406583c03902c2d0080031404a290081019100865000154480d44014001c850245800600945d52098400300d007036510f0000351400ca000418000000e001c90881094007030554031341e540a45100b06590701c0c180080d400a1451140e03155007080780440d40503c41c0b0406d910984a440c2c003680700c1e483d01c20003800d0b803003210072581c210020400c50600014481c41410b120b0300c40b4036a0004485131519480302c120b4040b00c40c085031943c81e000a4074a1400d0014141d40308491035502c00304203990f91501210140c01c15140104190b00c1404124009642d0210081d0301000714040141080c005130001088880c40034032075420559500c2c184420700d0b600c0700065500100c910030403490f50030700c2c000d003598909425001612060640000c901000c1c03068034482c090301130003000c601403200e0a050150007821403504c06441d000d405800040c3e600c0020902d19803100e4400703a40c5080500d0111094040c2c40300701e800e140e0010a00441d4403170347c092070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 381812176 1250 381810926 381810941
    0xc0b0315100c05160803030406090c030b010f05040606090608040311120706020c060603070303090311030c0d0516090b030703031b020901080d030c020109020d0807020406031401140c120c031009 85
    0x10b94070040010018101141800c1003142c0c0000b409005420078001e990001040341d0f002940107070005224000c2d03040002d04954550401045040709074000a608008600f000c0300307440088400700141076450701c0564580c200c0e0721511002c100800c000401280c040c60b0400c00040360345040d41c2c841e04140507114480e40c003030b00084981c280c1c04203d02190038020031481d64000d100307038024003603241180c802509440c1c203484028507424811441c004151401d008a4003018400380034041c00010a10340f05844465801c1281c0250780f17070f21800284030405001e40e4404503406070162012178110b1303c082301c108064464680340cbc80402601c1c2c0c0f0058648018560082c11400c02a284036480c20400a05030341054038214110380c10f00c081c60000da40c0300303d10311020980c45000c2c142d540c0c081d4408240074104a80c0040c208a210007124600900b040d0020341e00d1035820400a0210b64410665003014040c104040d000283c1e51400581400000c130021a0402100c2889002144e502c4010300c0640300607 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 381813426 1250 381812176 381812209
    0x40906110a120b01050f0f0f070c03060b0301151802070f0b1e0402100302030a0b04090605151c03030216060507030902150715271b05030601030c0b0315 67
    0x641c0307a0791694044a01c20355030214030014890f910368480001e010b40140700c2c07140543d460014084000e0b000d0030b0101d0780600001250f164a0341e807103003003000d6008028481619020b08103810f0300c00c4e81c81c042c4500b868007120084003007021403c15900810180040000c9c0310420703404c0044001054800c8030a40845118243c01d00c05840e0101c0e02c1c44540075040e00c08003c090021091100580c0c41d60701c2949101114580180c0b41e0f030b20308422002422500203129009807400e10b404091113002d4200901c10364070505050081a680c0302030042e0501c0c80322044000e0304111040c0c00c0028402c0d002440d003241e07080400a01034550b9212101290700995a04c8080f9076183c40c903608500389a901a685014000c1c0d00c1e80c01c101480d05d6005ca100d00303054901c600c05542e81443e501400520308202a001c56840c400300203500d03645461104121403510051310b1000302000001c044c94005080c5e41a240c3c89180c0d00c6800385404c0740c0814036000a020310300441c030700fa81c80121540f2111844801c2c40031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 381814676 1250 381813426 381813461
    0x9061d1f081b0414070219021f020601030c120503120403051314040c0503150f0621010e0a09020102210d181a060d0311030c031b010605041404060506040906 69
    0x100d4000c200841e040004000e240d4080c003001c0010450300424801901886100031f111448810700c00030b046d03807401c4030302492150011000c1041e15580001c0d218103032480345803d03d203580d440741d00302d070f1303a01c001f032100100740d40d10400c02201140c0e02c11214a4002d44207003449070130320101000b000244146070304504046c02991418100a151500521129580c0350408a1660a0131010543ea4a542c01441030142042d00000c0000b500c8a60858099030300180203403ca5400ba511407824410083c41660700c5011042c0100303843c141184905000c2c00c2c1d0580090060381800380c03004000e0882601c0c02080c3c0402072203919003403009805003200a40e0104040700b803c01ca0b6180c000c40030900b8031072001d011281101006640d450b108205e071002034050620404448800d141c0030302d50321420035040c8050001040c000105445205000c4205201030024490030b44c236203050108a4548070420718003c0480d0000c2000f04100d0761050750040000b038004115444251165026501c1d8240c20050103138 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 381815926 1250 381814676 381814723
    0xc03040504020a2105040b0a0c020703021306080c06043206131e050f0f03190507080d0f05030703020a030f0c050315091b0901020a05120409061d1f08 66
    0x90388401001000b04a0300c0c00b00010b0406e511920a0317494010510b0040b9581e4405200340039008104040056034000e041c907405610a06103c40504918442c11380740d8845c070300100d40c513480c00740180c6081d2103510940c03004016504064895090114900b603941c001c04070268070b2151904401040b401400484001c84140344c01d003164805100159410300c4008800804d104a9a481219619200382101c960104510b41e030002400d006940780080c400c0c00c02c1801400800c10041080812118800e0980e05160001402900d00140b12040040003039420400201c240380a6405031181c1c03c042d18001900006d0781902d9412901c13420b042001213040402040100807159106554484068800b450306041000094100540c15410141c190b81b0114034888140d108000c1091502c1d00f1500312100092070780d03015032043d4041e0113000196418880049048400c4141094000d10345060f82407840c0c3d105024178003d094221545080c40030444000640d4850030403050345081c401e0b800300507092 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 381817176 1250 381815926 381815957
    0x8070f0224030114030c0f06210103110102011b081f0302060c0c0307120302060c090d05030a050406030b040513030c0201020f10050a06140901060503220501050402030f060115050c03040504020a 85
    0x101203a511641700303a001c0b00345c0248a407119545403451b1081515030b692100c462481c10042c2d1080c2038681c0c1c2201c403034540000180b1000710114520351000382c0007007010170540e5600e1064034441c1c040d00004a190500400c00c9400920301200c203100c0b890110f031194684075030010b200750b0720012880f442948140c00c1d5100c41d140c14446071005000e105414000f20483e90307000307512040c0061410a08140c0822021480e807182d0810b54802680902580d40e10b03e5455001381080e0405e000f0000081e1030319100c26038500701441042d005007071034800020f1402c2a640c0803615800813a60881c118003d0442d10480c4c00010404607414050121020400b45030400c1510304840c850b030704c00d1441000040c44140c00b0386444c500345055840d03d00e8002c2c2e0725510200e940b00000544044400a80000c00818003840019071002d40114800c5055030007120a80b100c1079070b910400c2c050311940340440e030385081ca030b54042c074010444501c581c9c003070707a08203036517900000c003281c002d1000140425030505010404 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 381818426 1250 381817176 381817199
    0x20040f0504081908070212090a080a030f03050c070b0a09021318020f0411040b070c050303070c1805150d05010f05010b0405120d05032706071e0c08070f02240301 71
    0x544243d454280190302e040e18000b981c035a034840c8800c280060004c0c030004030f070b11059001006440e4110840d4800140e6103402800c0000720840c240c00139242c0300119860b5001c000c101c5854640040b0715008603182e5007029401001e500c0380480e1300c5070051070794505440240c003501d04403a040c0340d55802d01c101503006000ca0281050304045c855480d00e100b00d0b541405200035034040d50b071003801040e2507148a150900d404c03084c640041c2e40c944004a0844100615914850242c51440c0140848851942d20140640d0b00035640214809094100c0a06a080101040320003a010b07100101719003010354008011501c080c0c002a1607004000340034000b60801c007080001d47c04425000749a21a55500028402e000181811088a00a407103007681c180e04100e80340c0908a00c503090710310701c2c246400c018001d079180c0300300200d441c8550b901c1400100c0c061550420f643c1e4222503401d1400364266580e04088a25007000c82c0d00c119150304803007081181c0f8a440c41501846005a940e075414450f07680351 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 381819676 1250 381818426 381818467
    0x2150a0c091a0318030c010f0b13020a0c081305040f05070206060303030702281202060106030c090e01260d0201050709090506030d0c150c1e0c20040f050408 69
    0xc9054032032240c022449402d8040765400041c0c2114000c02c0c45003012000e046109648031808190300f803404c64004000c85901c001c03524881281ea10b00c0034079070070000b0400da0080b945000702281700741000601107030260700180a96a00030315400c40c62074944001500703c52260846809481d80c810030070842540400130b9a4100750708400543c107500e00180020340c3d0b8901d6540214802090f2100064410401250320045a520000c02c1c3d00b104124034000750756000c24840c0718000780c100703200751400c1401003501109807940340119561581c20041c890904035030401f5031078410f0264882c9520030200500c20343c09456185d0307002048070308014030000c1104030b060304020b2005150900340491030b50000760710700101510b030404000350031003410000350744d9503403162080350700341000e0f4030002e0305901c07a80c0e110004809000e980c026903000d4030304680b5903a004000500700d01318841300c20a001c84503040c0c402c0e02c1c000100042a82c03051040e62405488084d24120f5030781d03502050100c01306084145012 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 381820926 1250 381819676 381819689
    0x30c0908100f110304020904030e010509040216051002030c0d020705031308030d060906050a170c1c14060c070807050309030d0809011d1209151b070e040510020a02150a0c09 76
    0x1411400c1940015030707d224040e000400340900c288480c4126406002a9003040b10001c204548a040384900020b840d0000c0341c04031503034014110140c044e2245071003601e00034208580700904021103503401030001c6d0b0001c001981c9912003408200e114540c0d90f8007800160850f0320140d0740f940503010541090707a10980004507803506050f428070260f110803113400201c9405003444c00302c1100d020030715402d050344008020b07000b91080c00d034000003981d600c1c800d40c0814802d200f141103400c00c1c1110300e0b840790300544424107c00410803034000410b028030041c200740c0703000b0300580b80350103048000285003000401c03184000c16040810406104820320074001c01c480301000c03e141d0500840141e03038460304540980b60707000b90081008119602c070700d138172880f030540f42010080e50b4959004803003104115140311041548234002d40480c0c940100c4050704e0045038003000520203010140307074103030203508151680000c6120f28144011544010b040040c0500e10380078001809902c0801d004000c0030054100a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 381822176 1250 381820926 381820961
    0x1060e010603270204140109270b041410050a090c231909050406151e120317040f0c0807030b0f10030213060608071e030c0908100f 58
    0x700d080342c0c0c410301c1c1c441c60140d01000f242500d900c070700c0044e00a154039000c011201d508400045200801540712501c0401480301070642c1924080070131b18036140100300101101c00701c5022800080403008107080b450040b40680e604900c40046440803130340100c44200480d80c50304205014400050032040182c81c07901c4000051070262080c1442200d16829104d008403c12040500c4512800d500c503000f410380040140824101400d241c006020600f81c0c0315254180b2080000380c1419400c4000c120b0941c1c8148800e4982c035180b8002e070401400d00c402c3c2c0c240080b83d101040f200d05408480e5100d64420780941d01c0c00b10a500f801051050140c1080045910240c000e1002c100c0d00d450366a802601600c10f2082c035621010b03920600d0a01da84025040074002d117502c50780c5441c030f41200d8184c441da42d4613074000340d603103e10480309204019100e6031492641008009124840d8014000c161614144180e4069850f40391510f0003071003001000c0d02944d942c1b80700043c2e0300d0301c1c0602401120888400e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 381823426 1250 381822176 381822191
    0x1020c030a020a21022d3013090e0304030c080a03030501080d05270a0e0411010203041401030b04060b1c290108070c0c1d0604050405100c110106030501060e010603 72
    0x81e6a40742e162a22182800a5200300f600020541b08441000b03081a407d40710904006408004c492411010780300c0b1a41450400e8215081107030700307862000e0034101c5c5c000c80403403801d68041c004000c03159803403101e40000c00c00480480c0b14000404000c0220078001c066480241c02c0003812100181c100410a800480448200c16840000d64002000c0c2e07180e1140c00c01841103058400c2c83c2c85510302500a00300c00d2002850709400403000c1d10403405495644000c800703d0004903140e200b24040c0a00084001007501041c2d44240d00045202e1409800091000d032505003120701030304060080b0b28001c0010b440710700c5074180e074061000d0b22030508215001d50300304810007a11003c08041124104861800000c41c10341c4504800b181c40307500000e00750748140d21004250b94080740442e0409111b0811130100f11641054801c4074403c64107d070260100000c40305001d005080070409000c1000901560059044020700c01c0d14000c1d81300d42e00004201d85031040c51b04203040c059205400740340c60080d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 381824676 1250 381823426 381823493
    0x20a0b07050903070305010c090303020f0a02030a03030b0d021f110a110603040302031306120c02160e15090f0108060708070c06050705190f08010f0f030803060301020c030a020a 78
    0x444a8125089052070358030340d400c0001003868403006a20203442507003007401001d03800f50808035a006480c0079500351000716a15407015075491184500007034041c0d010f2003401c80400d00c80c0c0e108041b200302c02400114001d8580d00000c0440d100e0324954030700f11004010803140d0300e82101c440c45400c880c1c90f014103551005501c030607141c0c001c421800350048000000007000c241c030034000c44600000c03020340000010b4507000c1c02041030b20040c076508442ca19200f44003140c00e00008420a0005c004940d5030302c01418004117151282000d007400200c460a541000303410355070790000501c0b803032800d4585001c541c503098510386411405001c800922082c1c00078090102d5000c140d915025810030702c080703600d40380c5046c101c41c079120b1140b66140d24540c10300011030b05980001c11a51480e842e80d20540540d884001d032400c0c8001c5480f495048501c0c450040002030b8040025503403021006000508180d1080011403d56014030800d80c016000410207600300034100090701180c0c009480c071104568000d44 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 381825926 1250 381824676 381824693
    0xa141923040311010915020708150603100b0f03010207060506100512220b0a050f0916050d11041419110d0504050a020a06050a0201060b070803130c0b190f020a 70
    0x1003e048444583d4407100309034002d254074001032403090400703102c184050400940302d1aa60180152500413401a43d81c0380402d401200c2c050725004020700030000c1801c100740024003044070115004002300c00681c09581d020b10141c0743c0c050140c3d20225140c03900104000d56038960b0794803c82441020301215000783c070362071030a5500178840d031101000c0d182854000c0440780c0c00b00c8002040001608100528040729411840c0200c650180650f5642c0b540c02c10070f500c500000c24910f40005101c030041201e46410051032201c94000c540021000701041d021070151126003030f90301d41d03880082c81404480900c240a04100c10385940c81000708041c894158400b610601e019010303030301c3d02c0304080ba090200622078802c400340c0c024058800e5551b1441d016002d42c0100045401551801c4000116040c80c24100c410700d0b41c3c030105c564a103503541120640e01a000c0903042e10110004074000c01c00036002d5004148400c003155820320200c40080380100004481c190032411500500d140000150918 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 381827176 1250 381825926 381825929
    0x11107020d15060909050610060807120f0e0c030f0111030a052508010f050109120305030c07171e070b040605060f1806010206100e06060a14192304 65
    0x111090300a4803018140b0340d240d0030b040180403407154074040300041d480304141c1c002d280d00751146040da801656980045a04030a40e44144804104c140300000c681030f100300d005040705000104001072282941400004440301c4100b0b070304030303588012841103031407500b082445a40e10060000307114041c1120303041402400054000182540c4034004114003000f1298030f600802e510402c0b80010071341c2650000d11811003840381002003161000302140c1544145094401e1f1003101000d01c2c4c96040c240e50440703c0d580010b08200201805006c1c040000740c600510070084454440800e881c4c036a00b801d03e00e42102d2104090801e11000c000349000500408401d81e81320b60000000202565804045160545088000c0307038000c2c080900240403441e0003071458000c55082c1c1c01c984a66850400020661119028503440e950354000050103034505000105140c0304980b1f010b02d40d4070795041e81c094158102c00380745118038611807040308032554130505a000404101101c0c00f130320081c508660b889840307103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 381828426 1250 381827176 381827179
    0x50a140106150e100314151903030507140a1b08011815090507090212090705030a020904110a050d1101020f030f120a1506080a0e010b01140903010f180203010e01110702 74
    0x610707100040145c065030143c0c000645c814038842551510b0140030400007a00245136200e619280c1c501603c251004001d81f0659a258940d149000c4170f5464500b440720a503007080039244101248580003462424440303042c40c1c00c5c6146208030071300b000c208a0a441405000002c181c0c204445100810302d807500031208112600b900013404d226078100541028081d0f000124864000170300621030900c04160148035110640507a4005625401010b454910314407020754040c0d00d80000c24045504282104001c40008100b005015a29070104d4200340401406458408481603c1d03000c558051108030312a0060101852500c048441c40c509a030103070001d0910b1400d04000000c038180400d603c0480803030000300c50851100d40c4c42c040142035040480381181e00c541020018120700405000e0011b19420503100c8200313034604400002d6070354015030165541903403182c0408060708402d2281c245418480c00602c40a082140107140c02c1d140300314000301043c1e14107503000c2400b8a00d82d041d201415030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 381829676 1250 381828426 381828439
    0x160302060a111b130c080c030a020c0105070332070e0d0f081914040501050c010b0a0e1e0129070501051302150702090601080c07050a140106150e 64
    0x440d00811581030b41c4080452800b40300c0c01000c60380d4400b482010002038401100c0e4401695490302500b010340d60300d80045000f0a640c0e10200f1080080d0344050f551082840c8001418a41c40c4440242501c0054417a800880d80c3d510419100041e14080300307041d03c211004244500740c00925400c620704008021100b0000d0f44ca60869580d03846843c2c02204c1074205251404041c40b07410444119840100760300d1132617294490942116004610740109500c00b654030a040526280056030540e0066400c1039081d540c95102d0220742e5908060a006402010b043d10f01e14584560440340c1c0d030805840403031004281c41d004000c140320610394000d103044d00c02081c507a10100c00c4804802d5002d1445c00400030b500f404c04110382c01455018184045000b250f01a5030548669072441310782c03180c0080a50403030b40355070014000e54018000c564118082042c1e2510744115612a02d0402c1c204040840d8200c00d090580321518170240284130140024942c49140d2010781e0302c01411140400d14a42d00461 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 381830926 1250 381829676 381829687
    0x3020a061a030303010b03091c0905010c0c18050402030613050604120c0c061106060d03120b060f070308011502071d041a010b030403140307090b09030307060e06071116030206 77
    0x480081c0d60164a079400750403242c40e940c45080480741d94008480c100d8251141302d0724200300030700b014104602c0c158a61240d02e1603509050046603c03d03000d410650782c944080600203441900911100c0182140f800001181d04080c0b0400d0300b070200103402502021a0610840d01046021440503003007684042e41290078111000f094410070f01580c409403421400507000504103411070300e04007505103000e0541d40c48c5d541d200104241320440b0400034000400070b5840c16001841c1d40c0c419202100c00038541810503490403001001035002c103200f14005100140100100859100d078a400c006540c000b40c01d5940c24860a400b0a54450b04150040822200490181300c2c030160203040420020380da1903040d41c0c40f5000d0301401e501c251421800228450041092041d01009590107500159115004185031050414440d0090807119030b00d4001000f4003000602280302d008642d1124030090500303442c0002000d058022040c412400c1d68000c41d0001c51103010f890108002e880d8111541601c51 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 381832176 1250 381830926 381830951
    0x1305010b04091503021906030e06011208090d05030d02120a11070f11040c08070e040606022116050a17130303080901140124020102040f090903052203060501050d03020a06 75
    0x43d5041d8800394103c2d1804802c660084100c0c1036142c1910200d840a1000d01c01f515181035030f81e1024400c5425002c19044090f00054507800209074800004100580102e0faa071034040c1581c1c4408600611594000341c503459500501d20034035400b4411000800c444500f850a2520340c0c80750360001402801b04603000d0342048440260160384180150080010b00101c00000d001004191084404242401c008258601d094018401075070b4844d805060300c410740d00004250200003074410b0032225002d101c008074800c80c821203a0f031900d006200800041b4502d0409104011503d0070460480c1c1c000c210403410100401e640008895152070829940c1e5180c11150340100001003000c526600c5903000050400d000707404195400b1255200b00c1640040c03d04281e080344202d03c500f0108450545c002c03c0400c003540e0042c803616020b81045413030a4041651201d061454a041d010145010182803040c0030981c45130602401064035094205246601d01955804102c40028070183c2c413403034565070a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 381833426 1250 381832176 381832211
    0x4030803270a0309090b0d0209180f0601170a1707030504031509120c1109180d030c0906030c050324030f010e0610030b010e150a06020109021305010b0409 68
    0x18928010011403805a0840030151150b050b0310003603000400701e407808200c49045105074581380e500281204005004c1c0d50900201e1800102440c1c882803101c0d85003510800c06001e81c000b489100c1001e8480c6604054402400b4000141c50240d541d1080009500045c42031580444031a0b6112103903884610314a02190507101d150030081c6801031a003141c00d901d00341a00400d03e840d101d02810340003074040c0e031070443d0803c40d600005070106480c4019000e640c2045038000b0f420501d081541c2051050b60442c2510b4070348900003210000740c2e0f40c0000d6201c0d0794445042000b03040749240c20721000d0440c18008040c4e00026240c41c004013240e83d050342d001013035942e10b580d03540d20203401e031218200c0080403580244195400c000c018010b130b200143c0065641e04010064940c400d0a0f121182d00303082c01c8035020a401400854580340c240c3d80081d071641c0f09481074005014560020400d841d6034030512102c001131421240f50302d810f100c01807248456610070782d0151260700030000354942c40402d03416078 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 381834532 1106 381833426 381833461
    0x2130302120a050c010e030d0806040905010923120f0c1c180e0702060f1504050c0903100b010503011403070f0b1209060702030304060e0c09010603060602011d0304030803 75
    0x1008d9001303403203c90b00040c01900014101d903403540d440c0d003128030b076580907204503e8002c0100164500c1040b006e004440020203444040b85854407800f0500070489244e400e800c0214034440c00080030000000750350007987c80c0f094225070b0310078090081c00381e505094010060300030011410301800e52156006107150b500801440d5035070f4541d5440316001030f111543c1388110b00c00c1d03541280d8940c010303103004001d0028844d0b9200e1828041520340021030381c0403484541002e031909510b0b078002c41134a04540f214000d00d8100d088070740000f82040403980019803506880300e00424008602806800b4030701c164658501c0a850701c3c3c80190ba2810f04640a00060b4001c0000600150082d00700c818101044000c03164074065034000112060401d13040038001030f603141010009130394240904508074000940e5601e03920100c000d1980c8074452404042c0c20000d000010503403141c0c80d40c05061 = true := by decide +kernel

theorem cover : BRFrame.Cov 381654676 381834532 := by
  have h0 := BRFrame.cov_init 381654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 381654676 ≤ n) (h2 : n < 381834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
