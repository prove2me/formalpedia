-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1954
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:17:13.132988+00:00
-- url     : https://prove2.me/submissions/b14693d0-3f69-40d2-b3d6-b21d0aae56d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 351258992 ≤ n < 351438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 351260242 1250 351258992 351258997
    0x8030307050a0f050d0f0e0c01032f071a01060311040303020d03110c0d09081903080103030e2d15130909050106030b0717010f030c030201050706110a05180402 70
    0x20000900c200b0104000c2d0b80b2842e140100e200403854810f00d000100a80c5206a4007810920303085c50313540c0d91240702210402c02100400003001e09051240c00d42c100c20488042c4100c407006541c0032080840c1c45040103200e030440348140e50000701c044520302a195001070a030424050100801e251190608084400e44180c070708130f0b541517005000014044008030080d10103607001d4034108400740306128156034144039601da68841a0749000c4102e16000c8018171740580d42441c4000c54840440c20000300740d000ea512415a505410a107800f0a00c04021442005d440c520842005009040203480034079a080800200380c02110500080380b40300d00ba010301c2c0d210b50b01c07082c2440c018a54041081103041d0f0080c01c006400f40000140c01541e1b0b44a440303411600b241c401000640070b403042d022a000003580140900741c6400c10900c85401c44d1768040c0d02808500000e410303c4000310300102000707903907000302d0b080c0724003131500e641c803503610300c0f006801c0c0d421080716030001c000d642c01c8811090500788203 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 351261492 1250 351260242 351260251
    0x302250b030c0d0f0f0e060606090901170a02030d0903022107050f04090203060703020715020403050a14010b10050a020f03180d0813120b160c020108060a0314010203040606080303 79
    0x10152031074072280240d80c1664400c0083d4042c458441003203401d110318078403802c178110041070320204a10b441c880700c9900b40b14000342054882ca609002c441c180b41c54114105040d940c1c43c007280900b41120841b46031510760381440080d072601c12414052002c2d58098400c0d0201c9200762483d580400e0710404064000d0681e0464421651000390b0400491038611648852036001400008203410650040381c1400b808903000c0001c250001680010052444808000a101300004501b414107603a00c498407031440130000b17409141084003100c0b54150a45c400c55030405c00508101c1400000b0b6405040c0c1c2d0071500206000d4000c0da0b16400340c0c0c81010049072076040c004c0310b00018240071201002544e03501c082080e41c5915041c0584004420541a61000307403038001c610003a164618078042d0000d540003070552040a203d01a907515654115040200782d03a82400d01200d42ea4400010030304000095001505014401200101d6843e041d802980178500481d01030045685890300795a41e44030654 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 351262742 1250 351261492 351261509
    0xb0a080901090209060f0f0a0b18030a0f080318150403020c060a08060d0302120c0309030c0d080a0305061306030b0a140601080a0903020709020301090c020f010b0117060a12030225 79
    0x50014006181c42e010038201b000c002801843c08a030040040781e01c0c4056900314150440001400d402c004400e00502e80c40c801e4100c00402c1d03c505243d40c4c81c03c80c2d82c51054010107100c00880403400d07130704e00c0c02030f94518540c1c010f044550070548003034a100c6203d0141d6041d0090301910304083c00034101202250450700c11a00da184054403440300b40901461a0541641103028103000c1c80780d41d02005c80280128107664004540300c0102d07508140c00c000983d60f1880c4200648010b0301e00045200042c0d928805060a00150998603100414034040d00941c0719028035181407170100801010b4800c45000381140b84080081c4030700c01e04036800b40303841a17604c207002c0b440a00001d60008815088031028030f10070b00c19184196507494036801070b60401e8104440c100d44a048424665a041008070510300b1000c00901c044152400040d042003201160503102e01602e000003281030b101c002c8108021704030a840d11001031140c0c01d00075140c034203012050700240c840507070211140c19044001e405454103071 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 351263992 1250 351262742 351262759
    0x1206280509090f1501150201090b010e060a080f03120c0a05160c09050f070221040b0a02010e0d05030103020a0f03030e06071b08030d0b01030204031106030702160b0a0809010902 78
    0x1000c001ea8108001c1901100f441490420540840e050103e0704040d401ca90741200343d541010540f03d030004040401c481103a1510303a00c400890b034107034940350455036108241c0340b00382c0341d001c0858061181e940180e14184201072420508190000c001c080e04e00b80e011021105403216104003084e4419108182e00094040c4503c1c41442198000c20140314801e4800300901030303079541c1443c2031b1207040f500840200c940b001003100d119014002400c0000c142e44003108003d03c179003c40180350056004281c9c02c801c001c6002540c1c18000d40c8050030300c450501c1156200031012000414940c003d000c00c078000c40001500080f040d00f908001c1041d2681503d0706c240001c0c015062221a4000c0300741a108034607038012241d1140da00c104101d0150800e20059966000750005c0d42d01035501d921601810140304020800201d6105121016013001c103c890684d02e8950300d80881c6400c00e100940300c840c210b000c100288080c0e010004005000d03a6440391650780d030303400c2449402ca60205030040d400c51140c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 351265242 1250 351263992 351263999
    0x10207020a050f060403050f0309010e040902030d0e0d0c0f030212072108160f0308060d02130c1106070e040506011422180b04140103030f050a03020f120628 69
    0xd43c8070120000060b00071414a90349441c1c1c2440c1c030101341c00000c41c9401c0042c0313028465a00212407140f001054906000142c4580e0200f69a01e080d80560b02c01c1240002e1454000d40d51076000d0003100360040f22210600707403580030300c0f0391000051008074031500384805110300020001c56160201d446c0c40c4549108003800c4a103e204903400c242007215056410000070824210204213010003d001e801c03890085101480c7c0900340c0308c0c0107040301c2d2044410b01c18100c011b980d100308645601c904013801080703015140c20107951086081c09802d94501440c020030103503c1d032007005c01030402c07804c580500c0340352120001510864000b43d1040b00d40300c0200403141d1032940c1c0c400d044904802910241081580e20509410103181784c0e6031034054207442e1500008286030a005096003900b941520312030551444d6009481c01c0c014104000130310030049111103c65010307a050b191020440c45503e56200d59035402c04060b26800c07200c143c42800d5011462002c80301810034085082d0700c1c00d104c01000c608 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 351266492 1250 351265242 351265249
    0x60c03060a050a030602031b04053109031101050f060901091a150403060e1b210304031518110d0615030602070c0602060c040302100c1208070908010207020a05 70
    0x4014602070304820400800205915049035520085016540041e201d062030601d0074107c020100000c284004103000520240e6504013103a05204a2031121043c540a5542c00340419400380003440940c6150030a080f0a26810204079000045440001c2002d681e0f2140c00d000a0402603030402d8000c00f1010050044245076030040b807030b40e10340c100508500c0405000007401c01d80c8220301c4440c101ca010808004214282c06902600c0704800d024100121103510100940c40140075190f00c20078070400040301078a1000000002104101c058030350356503c82c20070000180300c032100d403000549856010215103003a030100741c016a80c080d13880c1303100a40d20401c0080004c1c581d08180c2d08256200422440181c0c6013800c0300c000d500c554030142e203900b02420184407045045c0c1c030038015508030340100320160796a0011a41900d42c1110030300190f02d41785000301c07102085130f08010000c00d4411000c11800e604040818400c0e01c850f9174017008583c031904002c0c282e00078041c009400c401100c10500032440d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 351267742 1250 351266492 351266497
    0xb030f1603080a0c0c090e01060b0f0304061503060c1806081506180301090c0e0c03040b06061303200307050f03070b03070212070c05012a060b031f0e06060d0302060c 73
    0x483e03140c0450b0011351500c0300c9000303045a03400724128075035032400c2030a01482070182000404a00c030080e030800d0f190038414010b1b488000c0000b40240c3c0d50766006501e401080c09440c0c007660300440d00300304810600d440074002031840d0101d940d540302c8a41d40041d910384503400d4184540c80504282a41503050020f100003504002c402900f0328401c800c6018407600d0910445c01c2c0389004000c00b2290a1900f100e18010150240441c68490000c00801c00482d04122420381c02040c2558001d0b074075064694800500000c030f0300010000140c0500e210f000080c41d14a145440504801340d40303103107903603900b00100201e0440c0314541540000d10100030201e41500030b141d01540d40d00548410105000300311070190f00030390007241e0203d0100300600c00c95a02600705100d410745000200e50300b007040700b82d00518180695004213042d0315604524941d8030280110014080784022601c01140c084000d1405413820b0030482100c2c0c821003000411624110030000c0005826801030601e07602c030b100440c0c5203076 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 351268992 1250 351267742 351267757
    0x150309030d0b040b0105160213140f010603020a200705280501021f02070606050604080f0d1b0615051c0308061f0804170d050108010510050f01030b0a05060d0b030f160308 75
    0x100484a549510300307801c3c002c4ac24200e1000030781850500d0108402d0500b1801a08058101407044c00702b03c8803982c02c4402038001040c22029550920404c60201e4030308446504040d03008110b0421010b0080c84028045001c64500002c1c602856255001203030b84400440e501c00e000d40142035408141c110950082445500845021803140e8490010580f158403c0c3d00c94609684201055a200501400755001414192070031403450301d00c41510760030703401080a01910b81c660b180c040f81a10b11008603c2d1000341000341c201422401c0c000c000014044075402c2c1034003c110460002642840d01c083d90040c0c407246200c800484850320380c802c40d1440b038000c02c1100c0c806040428110b135070700e400004d4540503c2c603c82c04503582d814001458217403540641032401440c0794502c24459640c07820304003680c0309002e10f80010b807000c8202c0041c2d445401c03031340a150807260004d00012800c0c1640c00803110241c1c154121859000d4405100395918012500752640110b0306405100003100e400045ca0361 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 351270242 1250 351268992 351268999
    0x902030709060e04021804031e0513080d0f0801051e12030706021306022b031d240c040923090c0102060a020a08060906150309030d0b040b01051602 65
    0x28140c540e140740c800c80b2100d4002114410745582000114030745582614801d4043c2d000b0002c180c00c1c81d64000d421100e0700d44084c0310f8140d694601f4040c0714428010f60710000508441c80104c255101c03081e9884000035201c520004072828a1007a000d0702a03110641251000740c00030304640c0010b11014030b00d00990080e280e000c681300002c003085070010800b6208142c0112001a90f07201c0400b029122090550721140564200f0701c1810b0402c4400c0800300349080d00340201c200c10200c0c8030310490003401142c4a4032031301c2100380100440f0000001c2c2c0c0220481c0903440c40070811180300e0f66400c8000080b641c04c401240301f00003c0c80100c1040d000302c0c1803100c44401c20160329105680504005008030307401e2016030702018010b070056a0410285030403c43e42102145040f110410081c113010303004007142c0c0128044004a5001d480e410b964840344007801c0e01080e00d034203213800c000340c072a13001d80c10310048036060850b004c4151070284220071300050161106803400d010050310340040d1907502d000780da0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 351271492 1250 351270242 351270253
    0xe07092c06341709031c020d141801060f080607031d030a270b0a0c022403100614040924030b07020c011737090201141306211503030e0d0201050a03090203 68
    0x1c1031131848027142d001c0d0b051030080d003410607810f2030f000303084900c298805a440464190200120711010408a0708141c651a0100d404014030908a9000d144011700061511001507948603d65006000100f40c039012074029200b40400310400f03800c0c8405010b44200307000100400ca60b180e004600742e0719514406003101c44c480c03c001c1148a4204404c5070800d402e04000003c000700704120560381409000b0b0760404460f61041c0c100c03d00001d020354003c041f6996a00d0b541081c245000c1c0c1411040c4241c1084182071580c0c903490003014086041d920080584079503587d9035420340c042d107134103c1d000240e9020a0000e40c3c44090942860740c140c40c0c201e800f607240314044a003424400b041c00c10040340d490000300d20823859100040c10208490800384c0c900304d06000c0c1702d0090900d1806c2204030351140c64460b0f80781c100c028000040c140d00c2d42018401c2450010440740210600d8541001c590003a01e030071000111003024040100003d60303000340040d60030410003800324000c1e40a046901e0018003102c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 351272742 1250 351271492 351271511
    0x1005090105211905090105101203050c0336100311090d0b10061b020d0201020f030a200f10050a0e07092c06341709031c020d 55
    0x400c48030042d20780c2100f140c0600000c84041d42240101e41d04060110020000740c41c120901300c8a103502c80c09054504621021284141072150703042d107075201d804000343c998411420000001c903515607241c054035603542c0310340c01d0390502c03040c4e140d5000c481015040c2c0b525202401303011002410131107401d400e1244144000c56968070b820303040d04030035031044082030403d00b4400d0390801d042c0d42c60f038040400c002d4580e41114a003071410207030f82280c0313070305441041c007a06141c80143d051440702c511001080c0b10129400e845140d00c40c50b211207040102c4025080d09102c54501c40d182c550121481c00310342e10000c01008000c4180c0e000aa001914000005550310041c04090829603a9441583c1042d2140031840701a080c9003003a90098950f40c02c81400080da0340341e4a07071144c9001b0500c108003c000041c071101444252224040c071b0040d6814400c40d625906000303450701c20102c01008101c00404009403040c18004100e4461050900000c00642442040312000e903200d00940d014040d2580c03040c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 351273992 1250 351272742 351272797
    0x50c060d1b0306080609070612020c010b1c060605040c1b0c05040c02060604060f150e0d020405040818010815090c19020703031101050f07270605181005090105 70
    0x4211a4140e0342d004140300d494600d02c10328282002e0410f1015400c200410080143c1045488202d03c030000b03400340e125691181c205004100c3c2c030710140d07080414010500c1c1d4a4240001124105100e00f0302000f042d41c8500c28801203900e5603103038002290800e000200c1d001c031441d0785100700a10403118110140c0d04c031000b08040d683e0004410700513030300010500c401d514103401408050104250b00c1410240b400240c03001c002c00e60f003115000e10902c0c5200420380d440320041c0ca621550060010700035070400e441c0034030041d0700a2107103018901000d46001d000b50301c1160b04d240621b403d00220820341c00440100b00650314082c0200800007010000349045104222194075030441c99005000c40a1550802034031800035038005500c680d14020801c612001803040c1c03950001c141d4640141480d401c000c2030b07100d451005c0d520920f80315102c0384c00905164810003c00303600541103001a550320804040c080300d5200c01c0300b55800b0840900080d80a0f5215002034800942203403203858801300d401407007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 351275242 1250 351273992 351274031
    0xd09080d08041b0816090513050a0311121917010503120901031508070501081006080a050411041509150f0303032a0903140d120e07050603150319050c060d 68
    0xd60000d4018400400c22071605100d07181d0310881d1001c200308107088c1030703139130584801d5262070040074032820070480700541300208031030300100e103622034400da840008501035120b1140410b1848000f40126400102d0055801d600d01e040740e2000c2c0c02002c404089001e00171050700070701c000e07070704260f03a81c000600101000c0c0311800003416504080e1200e60b007888001409198014488a101034484100b044800d600c131141542c800410540061591180e16141c0c0c0030b40380b4450700c26441828030b2400c40407941d03030036608011501e41c19800c0010f9000182e04055900c5640304160000701c244000300086400394100101106000e420303040404090a003908400d0103444408001840044003441000f43d0200d50030f5807c1041001020289250705004100ca54071440081c40d00e612065000301c06c0704200801800707013400410702d0340c407403500f81040050030a4000d0440d00c0f92062440b1807282d1340308840c50802864214000e807040462000620015a1003010020910b566810800c1c80c1031200d540f0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 351276492 1250 351275242 351275263
    0xb0c0a0614040506240f06040b1c0c0c030801030809010302041d160e0d020f030708030a02010504020310090b1323010c0f021c0c05010b120d09080d08041b08 69
    0x2801d0240c1d007401c0c00d0007860603400419003d80014070030200782401c60b0840849418640c21070302c1040701e81640020030311740d00031580100d07a2000041981070011180c402000410000b1040410851545507411500000081c0300507000ca003c0e0340041c030111724510300a00310003006040242c541541c2d41301002000b141a407901b6260300600c4184000005102c0b0b460f0b0340c44500746420131000e0300d500c0001e8a20107440c80c2c003c0c81503000c0e4081040030303102401400700404c0d9010643e511800301c0940039003e044120b404038424050004102071101c018420704a105802802900160f0345503200c50303a50300440c2c1e80a82d0021040d03c0d40c000000c9102c04030240502d810340c00440d594001e1103014002c001000b085005640000c40c01034528487c483c0340c9010154280b034040b0051059050560040280c80200c0340c0221890780c1c000ba1070200043c90308c0301c04e0815510000032a0f6101c40c000d8958141c040248009000761001c2800310b0140f04019241c10100002c108110b5960312001d8900311402c003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 351277742 1250 351276492 351276521
    0xf0c030421020a05040c170106020f0606090f070c030c0204061202091501050d02070c0f0602030c07060801050f101b030305100911030606071e0303020304060c03150b0c0a06 76
    0x605111507100414100d2803801c1010a203245141c0381e40c00186002c80c2401202d02599a5442c002025446200726584241404042180702c0d40c40d00d00003034582c849048441d50b00d02ca004081103950810a1401e0721a014840c6040c0564072002d00494019600c0c40064040052001c030700750159885106500082400f114041149080d81c410303c00740f8a4000c0c00070015440403580c3c1c0c1c1150360800202d46001990100c01a51100309181c011030000480e0071038000c81940c10b00103d40c042d00080100703464858001114a401d41d500c81c00c59202c50300f4044c980c0c01182c414048026410211010582c03410281014405103c103c1103443c2003500c0d907034060b0b000a40340c0c0188140410880c66100140c0343c4081c0a002459003c1300c0d034100b510014105c28014031000400105122810142403041704441904150101c4242402000b0b50801c0d00c099038803070301e0b2502d200b10780c0b80240300301c054070355014090b030507070314034210750040681c0144a00038582d010300310011000407058843c4420310350903007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 351278992 1250 351277742 351277747
    0xc040824010306111207120606020309010c060b0a2711030405150414100b120f0604230715030515130f020f220b070b0f0606040e0f0403020f061611030f0c03 69
    0x4250042c107981c8c15520034015504200507092490340d02008000c00070303811920200d0020700302400b14240707140e9907000d5208040c09c0181c10030003201c1820319500503080e0302d1041c89140c152100c00b004034442514014016071241041c015414980744050307504c03130301a40e0704000c3c50341b0134910039040071080280085502d03139030088030400b49460109980c8134180180108040c01050f00b800341d85000140025040880e030701040300c110b5821780c410307c11401183c02955880e6981e0300150002400d400803c1c0042420100004c8034820701100601080000419204254502d1101c1c100180190844041e096408014140058140c0c1000308080344e02100c04400307030b80c020144502e4410a6810a41d00c80c0410002940821400c0024903000300c5088110b46441d1504000100319204a50084159900340010445099042c5010b51700c224083c0e000d075071400310881c48864440b0301c2214840d924400e550000c0b020f0500ca4030305d114210b0003480469140a40f4000001ca6a401403140890541e100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 351280242 1250 351278992 351279017
    0x3040605040c06030606140c0309041410050609060f03070e04151706010501050a1107030b010b0403110d02031009060e0f0a051e070603050a090b0c040824010306111207 74
    0x14228104003c010300c0c9800c02c030060422078000e003030010605100200f20340200300c0905860080c4100c810780e0790020f004003d141c42c0750140040d54082100c40d40200c160760400050715003456006c46124600003400280307401c2c01001000819040640894200603041c8002251510749126402241d11002d100401c40c1e490844159101000c401c410300c2d5503000100100300c640d03002400e4400f0074286007094900007040000725071912100368805411015001e00015a042c210302c011700a40e80100001090700898030140444200e12200003034040d4441703603e00c8440340e0707154440d205107881b030b03000880c0408900a8061804209041407031541d0401101c2c40b0801c40200955420050000030780c0c0c000880c030100490300c1d05d480d4803882083c16103403c00104520f006600681e40c541d40300080300c1e5a070401500c10b03202030b00603000b0020036214141e062204c503070b4a0007003803a111900c2c00b925600360782540c1d0741c8000ba112a21610030440018486d44c81050b814517000c40c80380042d6610419400d05 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 351281492 1250 351280242 351280253
    0x30c0e150712050309010f0204030215031918020f01030b01270f080d11060103080415050f030a0b0a0906140409030e1302030702070e010e18120a080f0105010e060d050c0d020304060504 81
    0x100d0b0400c9071f460384100000c00041e05e501034941c081485480c8103546942c0d8000310a602c407039288186191680c60800c1078002c03160503440701c08065000f0f82d0031003c030002310001542142c1c07400340c44901041c0d8903c1e191034010448803000346c8860a480014110716501c04402d083c40480e9007103c001600107901081d040c95020810003154007202c001450301e9450350320340b091588180c0c00b0700007514100c0100340860b18020400c0710784404024403100d40e42e16014503184020a0800b0f6900d21403901f490700040c81c4c2c0018012081070390602441c01080c004002c081100509902c5000c03018400c03051040000382d902d504000da1168544480507135030389402130009040500c40c0e0419034209040b4001404a4010141c6481e4800f00c0c034910f01c111400d004030705515002100c1c003650407100d400111f00080542c01010b035405159509004040c82e40c0340c000654140440315500c0e41c000c10107005080d01e40419030082ca40020025146030314010549020200b664001c0701c0aa03012616001407208024 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 351282742 1250 351281492 351281501
    0x60509060910060e0409120c03121104060c0c03020a1d090a031b02032509060b09013204170f150612100e01051006030c0e15071205030901 61
    0x1804036818909490031006002c10407070382d4082c0c6001c0201c450703182021601d41780d00051045420122030309144c10a5600204020b801d46411400105402c22088251800c0d004004400c106e000c0c00b00d0070a0f0034240c080340c42d08111002507840c40032005c4004007584445407020090000050760386035400785c07074009181e04c98002c1c00f0035a283d03100740003410106c0d91001d5403140d403104150782c903c003054140c0002031400c022401d40c07400c0c0c241c045042c00084000e401c10030048500070f0307806100460b51622081c10b903010780c44a0305c3c045401400502d00d400c80d02c03002040601c0300c10307002c1c0400c001002d0303080100f90000d801024103050701c03c1300082c082130204010003000c5454030081442d202c1d11100c40c80d250101400c0d142c0100c0c6410500b000c0c007030080c0601c4814003000e4800308401c007202c0e84501d010b440c054507408014140342002091082c03280c02062900c6006440750b00c555101c000900c0484002c08003044541e00b014004400060000c0b40302000c01c495550350b070358070b0b800c10f10702c0d060841c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 351283992 1250 351282742 351282751
    0xa081806040c0b0d0b0405092d101512030f0305090c01120b0102030d02070b252106031b08070501210e0a0813060215040503160201110a0303060509 65
    0xc0d401038080000140c1d404511005030394811400648645141c0c0401c00a81041103400e54480d0a01040142c0ca0400040e200f04a080003030300e86a00000b102480c0a000140160b50101030704641d0401c1e0328000e040c1c03c04036004080704200e1114658a80b42c4c55030589080310205d0002d5041303003500c56a00d6140c050160003660103406050300030410301c000313420404103a0052424540302c90344100c3c2070303009009850920300c0810302556251900d02e80032000d410120360b80d002c0d05031b40003d40303010304080c1c00d441460b4584d6a1924404103401d510002d030800755080400040f1511440084009040f03294900089079070a051484a01c2c20040c40a0034101c2d690132450410260003924940e0404000301d818040b4510f6800142210721440000d0902240d070300c000c0c05183c030000788201d4112031221802c1c2110050390a0740d9200680d07042c602e880c8030003500c000d4201d600078010006510b22284241220345d2050600c004d0640e040b54030b082c2450075407242900420340c1c03100c0401c070f82c0c1044500c16520 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 351285242 1250 351283992 351284041
    0x30e0a150921030e0f040c11010e0a240b12061015020c131103010b030118050402130b010e0a08010609050109060602120d0609020d0c02010c030923120a08 68
    0x41204194465003260020b0001c1c040210000581100f91149002c04401c0306002d0414400c4e0381c000a0080d120741d00d1516030740b445619001c1c00c081e6215010600c5044035900c00001c030301894003034400040010750300794500b12255481031200031b156100002260b0307074607200c2c01421091a190042c4103856403e42d00450a80d0056032410151560204903400300010840c1e0392102c5001c0e2804680091842691a1200920010011404100c004003950403111240c5a8510319500a007810040d03032025140250421642444501a40c8294001456286062510401c075011006c0080c189000070350194007142d548031000c0c06030070034501510b0b014091940c018880d03c0c0c60210001e640f007100507500c00c003070400072614600108050b0811401014441010340d255214098034000030311100f01807101542c078002e554034440e4000d01481c00c1d12508424075284040c0b408051400700c203d5070300d102080f4000c5401e9000301c040d10f00c014104541c0d007962400060f2603c43c050004e40c00c443c80f030100f039 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 351286492 1250 351285242 351285269
    0x9020315040c1a130803070203060a060605030103060903030e06041202070608060d110a0b19080106080603070b0c10050f01030506130c0b0715050921070b0105040504030e0a1509 78
    0x1150281d00070008070307041a94a10744404000640a0f042d005400c80082c5805944000148041c40000640451340c0200c0070384081d80c40d071083c40d108442c428455180460b17004c0c00108045070413507000b601c84074004d00780440c00c4011040c59a003440022107048032490250310840c03c000b80e0402085001e0005070814241504003a000100308254682000303100d501d680e0030038201078071810440002083c16050007521800480300101507480d9110800001801174000060f00c1032050b540d450140348090040c003441400e0421a1841d41d0103d10f80048c180310344040f482c40c4100d18850144204400c058040c4154114a000d5017010005170040d500c070100404000b01280b0100e200303900300c54002c048070fa40d42c621450009035006ca4408400c401c03900d0001040002e01000c912140f81c80c10b02c4034400301e41c0e81da40d4105052801100e902524000e0341c03600510160805034040c0750014028140b00101503503c1c0300240c840c0c0c0954000450b0106064096861544c214030400007400f000701840a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 351287742 1250 351286492 351286501
    0xf15090f0b1c020a0b0a0320071a060a0b040821030f01170a14150106050a020307030509181003031101020a0e10211d0607080612070509040609020315 66
    0x2000790004900a082d4018084840c000b15659109030000900a00c08610349422403035170301034018000120f44480315034070380c2008a1107504a82c1140e52840c0c0c08800800e407200300041c01c50300170034000c2c01950810010400410220350a40181c0014454070b0024105040c40c0c100d019407000290b004071401e48001e2080c040c0d00c1d409880c400e815141d03800e007610500051519082d16100c411000904024282d1000d20000e880c00704454452a086110105040e40c2e01c0c0d0084403944201c0d003080006800910000c00060b11460081030140e0b0010600d00d285024980007039410760f03040d14444109404500c04004140e085400c404060100000860901160000141644468500107031040300700c0c5014420850052103014201c0c1c800a40d00240140c410b5811001424007050041c08070100a101e66482080020007500c100b44540d64046107031160000c0c80545110b046045440380140c9401260945609007098811070080c030300811005214014541000c1c1c0e4400801c0403030030000b0401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 351288992 1250 351287742 351287749
    0x18020a08060d0305070f0602191103030a0c050403021002010b01201b03010f060f080c1f0e0105040b070302030a0908060f180307020a030b010302030d1e120f15090f0b 73
    0x10351040040d2040d840d9550985022134207032203034a400a00c400368a49501050100c903a001d003400408002c00d210210740c009409590300c4550840c0034009a10030400691407201640203526100742900f400b90409880b40d000a04080403003845030010f0395100030104081da0f000750703105003002002d039070380c0d401c0451036200a4490100040c5411059100390b0030201e1620250301894101d80c070348004101d03403500d461241071948040c1c0b1034107034240328250f200f1100d4541090128011440d6008260750701c0d0700c618081d10152b0780c5441090501009100002e148210303140141070091103540a5540c510100d28040c1406189421010481d4480d0b800c0288290341489000e4115109003075a20020409690312031030340c0f08500c2d0003900f0150802002042000180156060764800c4081d900c1c1e21427481030803680d58045c6c26001c0314031240740860261060059905012900e5070140105480c0711026840055038440c03034540c041000149005c00c40340200d0f01c02c6884000700c031a4180160250b10001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 351290242 1250 351288992 351289007
    0xa0c02120a170f0d0941010e060112030504150f02100204050d0b040c1805090f0c030706050304030924020d0e0a090b0402040801090b070801080703020108012601060b0418020a 77
    0xe403003540d0366610020a1100f100c07603100030200f41c1c148411b20302d41c0820500701106008000d0140305243d001003a03640c2030041c010300244010030001405547c0c82c0840c0620060310074101070b02480002c20010807202440025801c000540d030b10b4174400c4003c20341d8000c0c40c00d4800c0d0360500040c0e01c10b100c00e000070358036107094800c09504400d400d100d07610f49040a084030780090340320011000004d80414a6012281c00903407140ca00784003a150311125202c5401d450b1641c6a1204e036158000c907000344081805030010f107801c42d0007403915a004945800d12001c0c503140101e10700380d1010725404100d200d02d81c10000c06c0d0b000c01c1a4500310804009840c003048544000740900d20031342d5194000c4240c140c45079810f0390300400f043c50007804040c9080c10007002e00714003568903070002685140003140300a8002104000c81c1e6060f0350702c000e1030b807a00e540070710b28140440481000d62508030b80c68480e44024016071014021022960340d40f64138003c031002e0411800b1144810440c010f124851202c0c2d0000b94 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 351291492 1250 351290242 351290257
    0x606030c0319060510090602070905010503282906010f0206011215140106090f030b0a090f050703080306040e010b030a03030207020d080711040e060613020a0c02120a170f 75
    0x156a801000000344402c0074250784c0d00007075042002c10310049542680109140d0031102c8507000c2c4c428854442c220707541925024001d03180c00d1f51000e5a10181d200c44501002c580301d07001c0f244160442c03001c1e0f44100311180740300559402c444001a542207909210140b00360810000d00384620410340340300f0081d40712541440341e0310702000e03000c2010f01880410b2070568881c610900041040442483c41c060180200703000325000180d048801041d646e80010b9040250303900110a18456524044580054031851604440390303079044107445c1c0060003c0003c40d02640c460f2981945900d0410306020403a110b1080401d0a80c0c1041c94503907003600c001c80c002071801c0d018640076940c4c050b0380c00400c2d1010b803200001425a58002010740911410305d5404044100484080c84101001c42c2000e40d07412081d5055a80001950040c91407803009074003d000c0b4460320308200c1d01019403500003980744805802a004150400e8205804100d515151101c030f150010003075601707000f0389100804941c0116207 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 351292742 1250 351291492 351291511
    0x1020307030e04051308040308040e0618010b0a0c0204180b0a1a10021c0509100f0f080402040615170604110415030f020c0c010f1b020904060e0102071a0606030c03 72
    0x18040750084179044086091180c0084034641c0c1d9a50320324007028541c0c00351049109401b07501c0040b0b0580d14003c01e6a070b460740400340b184400d59003070040741380080d4400320341041844200b03400303000180c0703c0f0f02802d0602c0007141c400c020040300500340a2154203004050408d9140350800603001d089040da0300301c1481c10180c40f12024000e4900043c0c0c03410301200e07001c02c0a0060110f50460307490303200700148143c20041c1c8803178491801502c410f4802036154400600810358001d85030b41c03024410408244d03c540000c20104241e9911030314210710142207404000040e0f1081e44491201030205045900328109803000c011401054180300c140d80600d0040000208514480150080c400e400a01eaa176a81c201c0440d900c40c0c0000202d0f95800101003070078042101d1740342c10b001e890701540741b60b02c514400381f100802402c030741d508011094000410454500d581d03460040c030000000d1000d4890144110900920302a8208658550640090005108250810400c540c0c1c1801000380ea0300034040c02d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 351293992 1250 351292742 351292751
    0x9050f061602040b19030309091506030b0a0306020309030d0b0d0221010902030613031d011b14032209050c0a050c0a02030a060614090c070b071202040306020d060501020307030e04 79
    0x1e02c00100078042d034035030090f8011200c4c4458244007035811400800c80b4801d460b220440b5a40d8800201600c9494020411440301c8403c2080b41602079009842031010040c0f00e0b071025031700c0e81d40c2e00e012600292080d6810740d00110708101c021035284101c4010300f0b022281c21488000303a070700203202e40303181000c041610303803802c607840340d0445003504202c180580c010b043e41e845151003c40c1c4511840c07002000d90014246071811822502003c4140d0200035060391002d50014580c80030020780b0a4400c012600e0a4440003001c2c4d002200344042c051182102c502403500c2c112484404c0f100300d0050b04999032081c540024003030054020003ca9201c0038180c209207845550522140d1304102e0041406501401a811031000300303e883d80c0070b44103a400107a034448404074200180060810200d9185d0801c0004200c2c5001240c034501c0001d9001f92146418140b041c0400e40038016608160b104491554011886980c5480340e4041c0002034082072000b5401e01e00d940e1130042001480005890003503a82c3c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 351295242 1250 351293992 351294037
    0x120901390c0c08060a0504020405060108130b0603151009230402300f010c02010606170c0c07090c0909272102030d050f07080703110418090309050f06 66
    0x44038200002442940181c03130751490201508400380804540c12803103a480c050004030158002d4210a00451608400058109e440c1d0b03a00480440003412259140c400c0302d440c00d00707a91200008c20704c5207045180e420081c130f180070340100541c1d0509000300d0095080c41580b40d00f0360038600c00641c0c4250101c0b540c520582d080e2449141d238101c0794500780001592401d01d8105c00d8000104091805091802001900a5007404900300d0f4050300816000440b0050715040c0c9801405113940c00410700c0c420349141c1840d0000036490451154000b03805140c481685614894000002c90020001902c003480076804a0340300280740c0c40743c00c2100030403a03051690101405070f45071644549446240c0034100711405010060f540e604030400c044410303402d250000d920445602c0d01203000d44840d860f00f00c00e17034440460650207455940301000300810280800100e0440c1d400b900c0121040c1c55000080041d11070800038948442604041c2c000c1d0103d9200341000d40310b5404a074038060a030321070055a03054 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 351296492 1250 351295242 351295253
    0x6030510020306040219201908070206121e0a0c0f1b0204020a090305070b04080c06031f12140601051005090310050c19020c010c0209060303120901390c 67
    0x75070102000c1142c2a00020b5060347d400265810242d10100380c0d0780140c0c840c03072680d03594a25070621820070000000740c2040019480502070041144014082801c000c0c985103c0180e0007801ca500c2000c440d0800c0c0000300b103a01809000d500491011000d00c0103034144600130301500640b46052003040012030300c0400c0d05505038552844a68010720556485140840c0101203100358042980c43d030250758000103c0000d040d00b01d408880d148005405200000c0c030808c8550780004084403920080d00b0044405140408107490140c01d40310a091a058a141050204640d040d12140616481000107000a64030760032000707402c40003403415555951086000c213041000c12030100410b2070030507003448903a14202010b0310091108005d44207130904458003c0380c1e908003a0301242d0104005209a4000d41000b20156a2080c000b1f42124903008811103400e050f0207081740c1907509030750340d039402c07001c0701c070491420a22a00c46401c0c04910b201a110751095803144078075804040c0b02d6110054002c028 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 351297742 1250 351296492 351296497
    0x70210090503061501033e040e0601050f04030618110d030c0209070e030a29100302040b04020c0f0106050907050f04180b0d0f03030b1807080c090307061107050301060305100203060402 81
    0x1400000c85d0110380b070b0700c90301c40f400247d4000200000501030700404100034014106450813a55000e00701105600e0341e2005450765400305040c402c58210810010010881d54040e5a500d20318140038002c00d01001d051121101c80594400fa00c65440e03d58000042a0702a000762913041e01116400e01039140e01009a80f21030100c1d40998048c020700320b51406024500407080c41814508aaa001c008070504d203120911030304599034a4401c0c00e2a8040c0054107040d8810701c0c084102420043c50020f0007041036141c1210f0001d40156a2b441d10400d0080b8140300304125044141401d2003400c0c8800078290302460700813405414090340b460a04910b00c0c0f002034010750a0030f0300190200b0048446801e1074031300001401020f0b80401e0a10405043d00d041441b84031020180038817594501e5201d50504481010014100c3c0310000c0050048420780d5409205901c002c054a440b17961844448a514038140300f155401a40f00b039252040c108007061002c217956881c03090903200143d6031355070800001c0090 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 351298992 1250 351297742 351297761
    0x6090b18090a0f090302030304140d08040f0606090609020c070f1a161a0907080a1e050c06040b0903100b0303070f08130e01080f0c0310020d060e040807021009050306150103 76
    0x3e50410541d081407580110045014902949121485018004c40703140c1d1040da01c0840400510000c0005020807400719955042e00d1007090701040c070b1740d501d0134098191680303074000c50344050740000c4a28400c80100500301c0201175041d446210381c0c2c9001c2490001da1100c2081e400381000010701e2003013070f00320f0f51442e45c0b80e0780d88054808010300740c105003481d44c06030440e082c840c5485441008912107400280903240309910135049680f424802c0002100341091680450b00b0b881008085211556403001a1028100400150781c80380d013a43c2c10140b4041c4000240d082c0a45800b11101c12034401004503446260080c03c4648005550329207501c962050240c1ca501107500d07028081862441d01d10818101d840d034600f265440c02d400702c19a07480c0d04101c0065581a448009100002205900a23003c055550b80c40001c00a0780c40841d4007041d0310840b000c80350500000343d00700031454055100d81800c00e103071804845041c00c00012903542e50024020703101d0b200c220074072100507030320a03040341860 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 351300242 1250 351298992 351299021
    0x92a0e0105090d060203070c02010807092103030f090602190507171c0f05010306241e03060e03031f0f030f140d09080d020114010e06180c0406090b18090a 68
    0x12450881c60023072100013102030490008071020081204d56100c2c00c580410380f81210080c04106c2c454407503072210701a81c0c1d4000c030103240d1942007000d4400803a100d001c0c032040c001c00c00960b803210342c1d56028101802e02c410150a106090010740e0204030405d0107140f2103400d6130b5120b40e403035065a040d450440140e2010380d040ba420540f4000d0000c0c0d80e0340105048030b128140a00018103409000d4020f4070003076035420725843d242001001100c1c2c0101d400c100340d00f10b00101442407900d0351204c0b82951030104c02140303240d0001043c0550044034044910880806402690b1041e0424144900c03148080c840075052808040403003003408100c09907250a8401d200803518005805500504902401d1107803031082d01070100c00da0300700c60041c001c441a0402c6200015220380c00c2c003210001c031203800f80c5129007144416484139081114943d1490040d40700380070480d01d5610f030400040c075040c00364000b4041c07030700c0601c00350020001c102ca020600c910110381201d240da84411001d40202160f107c6803a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 351301492 1250 351300242 351300247
    0x12060207051b0f06030f040204051b12040b0a09020102100e100e100606030b0d020103051b0c07090b0406210f02090c070201270b030c040f092a0e0105090d0602 70
    0x3600080768451800035064404829a80c1e1040400c019800111401c07041030346c109000600525065118550044408100c0801320504110901840d001100340101592074041840180410100704030761048003d1803e1061495030f50000b5100c1c40341c002c0010003d511048001407510080c0180c254081000608003c0d620b0404511031780c40704041d2948414524080011461030b00c2801034010b901c9001d0020680c40029900440040a00500c02003554040201b0342483c0055400149a0307034168000508615041100420031106a016141d100c3c03451312100700302041c09000030808020368041c0c060505101c60401070078940711841c009600600980812041800700000740028034000e83e201500c45c901b01c2c1031a100c0c90802d105030f10072014100d41c2004014040c4000395842080300488508040d50340009141074051038012484041d1074208000d503c00d00e40ea011010100452400c00428000e128050040041031a445040101c0018556180c0c1c03035483c18030400c075500000171035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 351302742 1250 351301492 351301513
    0x50a1a0418021801020c010e10032408070f082a040609050a1103040b010314030d1a1005030f011e0b030a05061809070b0a11010518010c14041206020705 67
    0x2c3d4010700d00c00301c2d000590000c1890755480007844003003082041e103803800024024010050b51040c040d0346e0008140e00d90034611303d042d0306010700801302103045501c1e11441d801e14003814280661500110036088144000f040000310018000c0409051050010516521050282e10300103008400a17001800c01d00d00050000980e8000c0e4451585000100300108440c1001045880252406071400c0307d12001030005c13426043c03580d003a03a610401201d14010000e034103802600e0b02c2e9402210050400c0c1d89101d0302d800c103040c0034032822041d85400ea00d14034018043c40b42004060041907084142d514040c0c001c1510408480301030011064405e4803880d11003089809001c0032201e540c080d004040c0d1411140d003422840e1402070f0070072400752020701c0c1490038883c004e801c443d21200c20000101c1b982d0b00c1d510428814540100c0c4100d0169070000302d03512483d0f081d03032001031900f07003086080040d50403030915620503101924500c42e0345404068140c20448060300608901601078001e04810307a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 351303992 1250 351302742 351302789
    0xd0c230610080d020a02060403060b01020c0a170c040513170903030c0120090108010918060203040f020102010b0307050d0b0a23070f051c090212011a120106050a1a04 73
    0x1c8200c580d035004442c2004100d10040382c40d15249000250804400d100c18000a1a190805030403d8818811100340b40d240f0300c0010580704d03c0d98003070524291422190b4440c1182440020340310203060301d0038042418885580301480f2142480030b40300d24129140c0003640f42c14070040b6100705400504584c0c483d0314089040d4000e01c1d02d103804191b1007840c03201da02c1100c00c040c415140d0f0400c0c16154105940e00c1c0c8280440036002d4410611410050500d0250006409102941c065400340780180901c0a042c40003a007101c04c50300816219074481d1808004e140d8440b007440e8401f541c010406803260b19020011005404050740066441c1c00c00340c444141041500e403582d103e00741e19542e0081e240041d12040e2014816410400b803100c020060740380c8142c0880c4c102080d0944007400c01007000000461907400c40d0001030021032000341076540b610441c94002d07210140800760030020000c103450301d40000c4d04203c2500c5a80d03e00305c0c0501e80008568041e006480003410385007220071a08044e0300b0300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 351305242 1250 351303992 351304021
    0xb0309030414030f030f030c070804031202060a1b12020903030c0109020108010e0408040510020c120106061202040e1501051b03030a1a0904020f0d060f0209040606020d0c2306 77
    0x3000a02202002050010318000407041381072804403016524104442000e0129584010040400c02c94100205000038070401d006000450281d01040050b9030182c00c0282408809800e80c0442c5081c0120100180103c0d400596803402900f4500d03103004607208a800a0700884200c541d143c00085208010720230190440100503101740d947d6002130b82c96000703c4400840a1f20083c0006105003c140020306081c9600b02219920703004580c560440080020703503e8642015002041e51200000c020454102c140302340140c411580135424513042c800710200480e8010490140c01061960400700c99008004541c0c0c9d182c0c203681c03031a42aa0f020189aa03484e8016030315a10318900c1e00110140c03081c400c159680b52844014419000c3c1d4449408000406151107650307039009021101160003c1c195110300720389040c070a100580c440c0107007810842141c00c5548072005641107401d14401a030fa02c0041ba600d43c546c09419401003592040000b02c1c800c40300360542007241304050601036141d004420 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 351306492 1250 351305242 351305249
    0x7090216151b0503070503040b1b030709090f0903050d021b0a05030a0206070c050a150f061e06080f0141100e010f0c050c041b0305010b070804090203100b03090304 72
    0xc007075441940c1010101c0d0603100403241700700058000d00c08940000c03030802480350410283c04108448485159194000f58020380c0c08c000840c00d1150300b04100f20302406201c2554030002c000f04100255510090201c0c46038007101d00344282e0019101e41c030071041c0300e5090755207003014007200c0c402c482a251013666a40403040c40e4000d44513090024504511680706c10030260750000180c92001e00c6035551020700280d2481c940d40c1035496480010b100074284c490b1038010241c0c100d4055580e5032403641180714800e2038000e502005004400c011300714808000d0300d811980042c5a5030100341d90100200994a4100b1740c4410301d001c22600302c011030400842c3e100c26007004176401e6803401024081540c84030b080300652804211b40c0c0c50455580c1d0701903d01c102c9000d00503403d50340c94024041c002012200c3c140030074024110314151524581ba890f20506024041840105103000001c1c1c8400500e405203229001c1d0558000000800007528204460f0041081d0082541c40341804001076880707811501 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 351307742 1250 351306492 351306521
    0x2030c0d052d0c040306064203050901090503030901090c0e040b060118051c11030106260f0d020d021501180c02160e090c0301051311150d06180c020709021615 70
    0x70000c000c12182c4907402488c07040700a180c4c40d5080b141c03c0c0c080c0e019190050008d01907542e41c1741c1141c082041400194030501c012000002d50b80c0a51170003c80c195081d030065240c070a682c10410000076181501160440c00c2424140c1c2001e603202c00c84d4580520940006070840100413000310302c10304c000c6040000502c80c08034080354584a0003414202c80301d5210b03101048806542041850700340721410b400741e91040c0b040e614107148441c8007524000401000c1c80059101c103104110f4a903061104841c103a05c40300300e4050951400201c441c02d03441c00c130703284450190344107103400d4814000c00c140603229220f035100c0310205a0f605080600c856049400b40c246006154040045140c184501403103245448030800c040a010785a030500034552084440d046000341548585112011014003c0c84c0095040810b6407810132086100c1101c90344440e594a43c24604c0e04035200d500072621105841e0914401a1600c01000d0b82c101c001d0124a005042c0d100d40f28650700c4001200e400c415007014001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 351308992 1250 351307742 351307799
    0x18121b0503010b0d0b1909080a14040e06100306030b0f010f0501050418090807080c0a03090e061c0302010f020408071e21110402030c0d052d0c04030606 67
    0x9109050982d00f41c00702c0264080400d00d8103070002040c2c0300c03609030460310ba03030b9041d00b100600c14042c000b15100240c0945800f00f010130b8501c0304651003d003040c0103003400c6030900c4c2414a080710401c079080700a060103124400c0380501c7d01c203140c0f080c0e11800040d50050f1660f00d05040c000b408211106082c0103c0c0c00100d00c248012840e94000d20444003151a01f908000c00011003080b050002c0010319002c952042c010055000400c0c0c051024000c01c0f5400c8001d40369076542840e01910850060b802002c11584004c100b040e25610804a0200b02d041205d00c0502000c00d850700f2401405005448450240301090202d01d1a900207440000c0c0c99108011800c1c0d9030300303501c11000d00d00e51845001400300c12800c105e0042c2e002c0c2c0302842415403080d1004258554500000307010b903041150602846040403446030b040100a004058102007102c20748003500122500960a07080315503201c0c107080c200c40011030100c0090343c045900443e0008010031031b290319000c41613682140d401c0316a10040d4030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 351310242 1250 351308992 351308999
    0x60403030804150606020d0e1c0b1519030b0a0906050907051302040806040201050c03040305100522020306070e0315070302270105041719050105061e060a18121b 71
    0x25031156906841707954000b401c1d002100102114500c6a640300150066002c1c07040c0388107110000c203403030384c0f080c0702c0c0b01d88c100580703409035035416628240600c2503c00d507484014109840c6200b8694001e0741d0304a40b4001e100e6940d42880e501624902800a04003441c0804128842502203107000a481040341e2800d02e00786200300311000d0740a03600030080746810a602080041d0b0081000700800c00c12001601e0820f55281c4400f81041807000c020001c4c00c3d01d070010040244034120080c592181c910541000d1403036560040307a03488000a10040a02142d03541c8091155410042c2340110000c2c140a105586005440280030307400a40c240800c508062500792052510103014442041041c0d44460030180707415201d05840e81540d100400e82d0141d0710000080310703213014100921a0203480007144504014080c04003500003131181d90840c13002c0d290451b006a86010440b01009240e05d03004d02c00c0d071081115910034051541c0a21141c5000706030f040200105040c012420132001e00b010440c103640c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 351311492 1250 351310242 351310283
    0x9071703070b071b08030106020d030b031f02030a0b220506010c08192d0807020c180601050c0a052d0a060e030c01020a0309060609060b030f15060403030804 69
    0x103541030090801039881c0c00203c3c00b0340f04120018450b04c046003000c0020700c3c2611200b19a40c42a007103140160400745007103064541501840865580950007880400e44400c4960a5000d4003ca40c040c507640000c04510030ba212a00201c00e078403401400300007900c4031390201c040c1c1c04140003d4500c6841c1003000003012903001b20100c1c102c45800c44002440c1c80144010222202c0b2960315241c2441403038603400f00c5414600d9202c0c03881e40900c1c04006003448060002074440900107000000b19405281a00c1c072585603500e20903141400943c0302005515110b005071800c2c02545442e014a100b009540d40078403500007011450298010b00401603118142443d10914882c107055241035846003010200284d15035021600d40c003c3c49003501e0606a035244842e080e40d001d100c0c81c200003500c8403507100c18050342e03200d644005c00d00c0307400401201d0b2501e0380f015102c0c00010501400502c0c0c40d00000e549082c000c50006905030020015592542c8030310f405000d02200391426035403115480c0851a0031718 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 351312742 1250 351311492 351311497
    0x110903070e0f0f010e0403050d0603120819050606090f0f09130618030807050309120406050d14040f14100213030b0a15090e0f01060806012c150f0909071703 69
    0x172910b2401e421540c1d216101515150300ca91000c2c6c1001f6a20300d80000818030441031120201b0607540e60203a5400d00034071161410100d240c0f090045481d000c14000a55a104100c840c80c88056880080342c1403000c001a8514501948054020848804005011410700c82d1410000c0c4103100402407503100c050710281801c0003540c02404102141c0c08a54143d001d6005160f001c0f0290f0101c903c80c00001701d601c021a005030788400d010950204040c01d001c100c0d8000d00b0030f01d100250048003946825141c0c401c500003151000f4120b130440101c01440010180301412900303000701c030103560302c000786030140080c04103501c01500c00c07201ca0400f04501064038000c0013400205c03003041080d107d0910f10038100800c2060407500262164039060311190000b8006d00c401800a01e014110942c07406460200c440d011006a0000c0303403200c0300402c110305813520000d80040181c030094400c489588049081618901102039000b1001020090740303a0000a0315000d94001140400240403002038459490 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 351313992 1250 351312742 351312749
    0x1103030903031819020607020f031f0c11030a050f0d0608030913020a0e060c030702041d0c030a1a18031204150b0603060607021f0905100f0e04110903070e0f0f01 71
    0x20413080320b8560152408101030100d603070004210b0a40ca0424a001900d0f2450031041e0050f5404101544031104000c0c4c441c1f240b506040d41000303201d0010311104a43c59100341002d802c2881000700d0387d06481088501550355480e40c5000c20011580c1b036500c815600d03001081280d00c58820380c850011201068001e5422a0721a912030a10201d80c600801c00c00f501b01c1c10005030244410301841c40541d465001d19051a402d03910b2480440c2d2502082034180103000100700d0081d400b0588400020340e048004404d940c801c844049020740700c010010311149200fa9502d16580f001144070307014081c64410346401203200b00240030400308080440d50940d541100e00369030003641480000e249041c070ac4e00400006100901d1544080400c6040c400f1840c20880760f0800244148401e00c0302d4100942c5640503c020790511a120164001000740641e8520b24554041c546842007101001e0a8100b40c6800341d60040550341070350380381c2c4240c200d0f0744802c403000820702002d2030209002c00107001d0094140d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 351315242 1250 351313992 351314023
    0x70b0c132102040b040b031204050a090912030207030314091e0705061206060417070810020322020f031c021b151815040320091611030309030318 64
    0x1c0821a02080014140210304680098035145959080c0d0340612480c2072280c04110a070761200c0c01d2909000080d5101c0d088020001c1c5000d4040010462501504039540024900540c0d611664a402c0380170300b0804d0050034692807510288031552001040081203003a415808140740740c20718070020b80c1e840301440b640d908210108420034905440103032103075100101034030407460503a60380c100c010042012099412260400081404003220500c030a40c1344481c0640d0a6085082180034070010340400c003110305d8110b900e4607481d000c645030804024601c50004042c0c81108a51081045040c44420b611070010b0080c4500c2c001100b10700181c02d81a59009002c0e010b090119890302d0206901410780300a0050180c071a2110035035030810007890101861601c644c4030340c81e5240c030844041210f510606900080710380c0922945480e400241c2c0140902c03500421211070400960348485c0200c050519800f00004010748100004001d40c000e1500f24030001d0350440d004442601c07122280610f005 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 351316492 1250 351315242 351315299
    0x4080307152a18050a08030a08011a120403031b0302090f01080405070b0306061c09020f0409170a0c050105130308060105031e06010e0603040f170c0604021203070b0c13 74
    0x19080d2140a21403484101e01d0b5200d043d441c2c5a8002805896681d1b0201115a10003e600c083c01d41c0c3c403401281c010310000d4569091a00e0a0303150400501038000400c4042c041c0500080505120b50440802521b01515002c0380f055148402000384d0f008401c01030140101c50941c182c10352203401d1107482070380c100000c2d02c00641800801c150660010300342581c0a54140610441102c050345980140c4403521000200c0700748504c1882502d2038005803071407007107241007000b1000c1170114900401c0200b810000307565411a004050720261681030015009628200401403007004008a206620f406500d5110181d990240110380701e10046030b804211b04200d002d01d500200c0301420ba01c1c0c0110050503c04204640300011802e1600100d40030348980c00c4941561013480711010743d0000f00a600c00701c003481e0881c507401d40760b40c410002d00001d0003500c1444400254078000d100740da80d0154000e081c41098240f0b00000311840e0010303800c000c1c000c00048000a2442d01090b0340c42e856800f911443d06 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 351317742 1250 351316492 351316571
    0x120204020a0311030a020c070906060509040c23030402120a081207020304050409030503060108071d0f040207060216050d05040501080f0712150303110c03071a0408030715 75
    0x103500200d86250626032240869800c045580f40558800e881140005031949003a09074280b6110540d4800e2030740340d00d4464140101ba80c4202214003400051303901159840c54120122070807507103459100a440c00440b40010f440031040c00541c0224021038071002d400304c0b0503d4007a12250a003000610148040082043c144544a02c55a001044d40192418140e07078001160a0b600d0f5840304a0000e900082046400c0da0080640c58001282d46040c410504d400e10b1550280015101094070030580942c5401c0181d50f250112054103601c50006d40d210308400d17000070540484500212414020404044541480b400c19074044800580d64005161180307140050a100d014088000300204007410104038001030142e010385038051307502c8080c3c1e14911700f001000c6103805900030406400004000c03900e5500000c04200f03030750303140c104080d00d28005003280000b4422a40908414040401d2803414880c44032150460940707100c0c0148411040d810107a601800e02c00440c01003090320000302d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 351318992 1250 351317742 351317749
    0x6130b0a0522060e0118030f0e061b0c03030a030c09090b091b091020010509070e060d1e02090f04020a03061e06030b010602121303030e01090509040b0906101202 71
    0x10882038080e03200010300502000c40c0e1130039110411b40207464132002110351130400da4040c8040d07010102e00e250138140101c6040008a192203900700d440d601904041d4640306803c010701140c180198010100c0355110040b07030010707000d0485400504040741080390b00040815050080840c0450003c1035603007181e403046180b02c800c0400300c65107400d0007020721400032a91a0b00031300320410101a15050b8880c03100048410040314003503540a00c5074108018001840c400003404025a0754061020101c2e950342008120fa110320b0550152496041c0c080c040881c00078004c1c1307003010600965101c0d11541d03800d01c100e0034880703003981c0017508410243c01c1003000c600c1580c01401c070040490307400590b164406000c001640d2031604151421a116001008500c1c1c0400c030010580d002c25000c9030500d0705003510300041903003e21000c0e050054941c004026070380b150001b0805010300500030f503070500702410a44d014840031501071071580f2521000c1460801c0c03140b515011a024180c000100c020280c2c20b0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 351320242 1250 351318992 351319051
    0x90b0706050a0603020d06140604180f02010c0b0109240308090f01030f061410030504031b02180c030907050f0a091508010e03190f05161406130b0a05 66
    0x402c1e01803640c0b100040300603501c1d4400c013440c0e03e00491010824920046200036201c1020340301502c1185007403803d03440010310300d403070b030000b1904400c2c0b07400b400d60301d8001641c0d69031721b400004000500245c00400c03100b4003640700d8aa0840c4213110240c110052400100100e485c41c00041c010080c20700481e0f499250220042001140c180340c00301d01d6207001545417007078584a4000c0c649007000c00003038046034101403440d0352180941c0d150600030782c20940c8024003c0c0115007110b52490b2500e00702403007991a90b981b100000300310310001001074a401071010f4080d4100341d81e141c040c0c2c0110b12000406103040b00d101c0b804c00400030010a801468025484000e20030805110081e550314100082e96280038800c581c0034040907000340d0f64803a4620700d010203042005000e501400080080021102da20405036981204000c04140c2e107540c21b402d00442c03010f00d00c20f800105220b90410491441c440c060018092413107501070349403944621500728181e41c030883d030402c4d0562400d040d0400d000c1d0340700030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 351321492 1250 351320242 351320251
    0x504090e2107050c0607112412010611211303050d1808030403080a0309140d020304180b030c0126010e100b19081f08010615090b070605 60
    0x21150450318040c0d0307003080a0101c5031511811280403030b88606103c0d003480300e03480060302110030501d0203580ea5180c0000131074103084103004c0da4848500c402107200600c0c1d4090708090440546d41c8640c00110880c003404c8003401801c0000f101e0140200d0500c00000c1c002d4600755000c02c811054002c0b40d0203840300742e002080301c09402c8a0500000001c14401d01801c050948941c0e25400307212500282c4030740201182c1d0103461b5a5108000030004101648161850b41203580303004031f40682035003010300d03042488402c3c1898900a08100c00c5110340c001001b402101d00417030b0a081c001018490070001c4400301501d45406800c580768003411507119818103580b0801c0e6002c03800150740100e00713119054409070031090040d4120750034000b0016542c00380c0380040000da04031034a44100020342260404a01302000140519500414003074604010501c9009128000c1d41b64440c2d940c400280c0644514031409810041c3c1d00008003415110700004026a080118003d19141c4507a841400070300c0002e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 351322742 1250 351321492 351321521
    0x1202011431050c01030e07030c03060b0f0612011404020c060103140a050303070807090e0105060901110f12070c0e09072306030112050105010e10090209040f110406091203050409 78
    0x10002991507014110403081c0c140504000c1c51400c125000142c125070b9003103400491903100c0d043c1000041c1556000e08180ca511400c049600e24104012400d0b0585942600f0b510031030200d40340c0c40c02d20400302e01703070b0480d049d0081c44142030380f0400030b00040748201503281049070802d200520204868208c6201018800c004aa2050465032522421747c1c0060741da040005880d4418800940e030300600c800f003e420310100e0114694904030000324540304040d42c043c140002e5258484640740280b000b000700c80304010594030b010b1001900c02d10503a01c2101c00700d4200b4000b48000c40d15610079510719126100c070710014000142071000784001d8194114130042400c020520f41d039113585501000e54000c10303d141126071285a146480d500b900e005811510402c45080104088002508015400c170b41d0300300001030f0340b4801900442c001e8021756010403482030821003242010880513000348112611951491a6241c481d8100e00807807100c00781c090001601400284042c002540c00b4002460485 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 351323992 1250 351322742 351322801
    0x40f0e06060c15040506070305010f05040507030b0405070201270506010b03090a05010c080109051e070c0201030f181407050603061309021009080c150f0c03040b0403050a12020114 79
    0x81e2440b502d40741442801844500d8020b06000030040c08201258018006007400c1c80203605000c24042c41c42018440c19110315294400b103104d0b24000d034050501020b000c0c1c410702c002e2802900290217401c545a0310390010a010032800384000781032002a105035409805050282d1822101401c0c903080580901d8040c0100080000062030900c5200303c400e000c1c2d1129056989855024403c40b0300040074101d1585030b2103030360b200d218940c45d0210fa00151300e08101481c0c007041e0004170010111020301c401d1840c6803e0b1111041070b1910100c450041c0718646500081100091041d182e0689108044d0031480a002050703d900e001e0803001001100e5000004e812199600041c0846118800c0d0a01241000d441032080038014400ea422102c020b648001d0401c8544280d007225200d40c402c4059001c8000c03622040c40081842220b004005038003105444a03203a0400c0c649032000507030229107603a0303101c4007140342c03031f0040c040c030900f107070001e9809042907440c1a50031a40c801d4000c038040c01c04208 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 351325242 1250 351323992 351324007
    0x4020703090b13051c05070302150d0f0213061106010302090a09051506121b24040f060305280e07171027170906040602060a0b0402040f0e0606 63
    0x400503261402c1140d11002c4024580310600140340380013048001c0c03908103103c02101040c4001020400c8070390554052b280c60340d510401c68a2030003901682c02400341000c0780d0703080e00052900034180400c0240140c83c3c215946000c2640c0400a03900b04040c1500207070010009482c041e45600d502400e90715000c280000690380e05802c19484070000703022001c0c0700c41800001c0c14500391024914040380e00806100000000c55000c209648075514402c2400c400061161074029101d160b07090300310040d01d6100d94895a011900140c1c03170040f440082c0c500750016007951000280d000c885013051144091a4100103000c00c09030126201c2c140350791003055800100c1450340301842c8150541c040140924108174440302c4282d40213001f9010301d410500c030080c2c00d18000440000b020561080309014280140742c042810740c011001000c0d072258010400240c2c090b0040781301880b40840c42410031080f441c81f01040100d0049005107107400980c54000d01c0100709058400380c000d0700c001c1c0305030304000030b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 351326492 1250 351325242 351325259
    0xf0c081603080708010503060c160f020409080703030f02040e07030b01140d0911040c1e170705030f07020f280606030f050d2a020d0c0e060a0b180402070309 69
    0x110040840c00030302e101c0100920150301c66001030241c08100c1c060040d50406000c100800e01402c0243d294050b002800702042200412103482280d45c0504103200000c100e0034400e03a40e41041809601080c20700708207490ba110207200319030558500000400e10341d107070710f070f4200c00511900c03108a042c000281080412460214054140740c0b0042201042c10304880c40e01101c4000c000e43c8284c015802c01c0c1e0141d0b2540d80100000401d040700e022030040e00c0c8000701003200c1c1d48800e440300c4034441602205012003981d004000b14496500c0400803191600da1aa04a80d22a102c0d060550150049040070526420105058000c000048449581e100301510740b48121403160b0700031034143c0d58903244c0354200541440803508281c91424640d44005213984203c0c0c0090200144e03280381e0086a296a04650b1041c40040c0000e4002401441c01501d40303c1c8500e010703406480c40d51191420701c5001400a40b803808640040040c0245411250b1001007484040c0d003100008801b8417a10440101f0b2564 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 351327742 1250 351326492 351326527
    0xc0910050d1415040c030603081b0304090c020604030906080609040b07050d02181f120b2706240f13150c0201090e0c090d0201030b040903020115090603030f0c08 71
    0x4803103d034035000c40c00f000810007040300e52451a4506260a00c1c0741080420707008010356003102030030b0013655802041081c140e42144141d03004142c2e01071030710b0345440384517a0004586104500c02c1e2143e000042e241c841c02e44045034201c60769a0300500560002c0d001900d980000c03508900d090802c2d50030b000d10341c800101680c00401040c1c441c040542c00f8030b4014540020040f40400d084555141c407104d410600a081c101040c0d00000d6250303c404d0b800c2100d89a00c444840781110845001591400500320101c0c3c0d4401070b9103091190703c03000b051344015254070680c008201c45560420f4508101e004080000d07821414921007000c1160f500000e40000c00600080505100d54441800e5030851002400d080407582060395000120300c200f0081480280440746c0c04002150b10050300c0e15517100413409400680744558001e42481500d10030550150451606494414840303540b4070380741c00c3e0040c05c8401510029000446000c14001428002c5481103c001d002d422860f05c2c1160304049003103811b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 351328992 1250 351327742 351327751
    0x1d040f061503050a15020a09030609030216030f02090c0301050609210a0c0305010e0604020a060c0f080412020f1507120c060606080a0f060806061905040608150c0910050d14 76
    0x540001e140b400030030585004001710140d405108509003669110020020846404010041d5940c1c45c02c8005060003006002511136441c00a04801c544030301d810310b29031203807000c02c9001c3c500b4500801c0c01c100c4483d0559040c0d4202900c42400d00b6094070400c644c0700d5415210b14081100c104140343d4030b203c14080011582c0c040c400c1446800d1540c544642110044e80d02c030b42035504144140001a0f03524154001101d07900d01d40302d01f14890f03a0400000d804601200201048000900003903404060307416038080074000c80e0301c80d0740e1440c03810030301001c462401c44410400b04100118000078503180c40701e6010500c245468070711244c003503550404071015500700d0b50105410300d0030480c004805004441009080d0013050090b05d190096050307079008094007082c07184103100c41d002c90040440040f14020030006009000c85a91400803039101c00d4089116201510100c0009102240030804c0320a0003402420300d01461003d55400c607195003206c14000c0f0751984070355100000242a0a800b4000d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 351330242 1250 351328992 351329003
    0x1203070f1a040b0604020f1612030b0d0b040210050714010516050c0703080a05090a0f0603050c12241807020c1905040e0f0a0501151d040f061503 64
    0x3910480d050009400101407011841019400100000a26010803c40d0000c00035900035072608a10b000003151400362080e200105d9180114060a0029116001c003030001c1c140c4040000b925140103000d0380500d80f14018014000c8580410010b040544e904200c0c001c440c134045d030400b00913550b1900d41c1303106800b0610307081e0344403c140044845070305070800d40e0180c01d081c0036181080304107900c1e4442185100180105c0300c042151036400d4041c41c225504140020000110152580c25010310726a05015100c0040d1600c000150008548001c446079400c1070100040c0c01d903142214208a4501040403c0340e020140340d41480e6074843c2490080c041d0303007040c1c0c6802c9034680004001c1c600141c10101d10301c02da5484a80304900c0d50031160490954005440104099014502c403d14084c000d0f04441214800c400e0100c003804419405040f41d03000710b00d4052041983c1e040180b25046240400030684900f4a001c01d001503420900001d02600c58000420106007101812101401e00d0b88140c8a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 351331492 1250 351330242 351330263
    0x1b12070504030501051e0613200403060f020c1203060d0605040f020907030c0c030c0c030f031805010504060909050406090203030d021b010509070b0d0609020a0c150e030f09120307 79
    0xf002420b014050303009a0280f2101010f42d01c04840d0b0044d07500c0641641d0207402180071000c0480d40640240d4007030340550202c070328180050101602250b22511003681e140e850600303071a402038a24021154885c200350001c1815465041d100c02c2c146d0b00203410310343c4c00209240030600003585030003024819401000141d00c03e80f85801401405400107000001701481c1100103000d0540101c1c11000403600341c075142d800e191013890701c1c480140841d0006082112030726002e000b0964018500c40b60030580101d10080e455131a0010340e510b01030340c040d503030104011901c144808010380d0710a545c018050340020824100e6500802c0c1940e1080c07041d8071001341c0018070224100c07429000e49409070751940c002c1183e41b80124949807a86924003039a110300500040b8020080300c1504444041c0c0b00782c0c88215640c1000f035501034440d202c1c4160449210381540000c41605246100314500900410b01071858030030048440401360380115055507102070092442c0c10300b10420806040118844d083c00c10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 351332742 1250 351331492 351331499
    0x30303060512010b0619050909090a050708030702090a0c021c08090c01080c07141203163c180e0a0509120f0906071b170d02061b12070504 61
    0x202809041504580070f070b05010940030b9a4a8042c21140301100b4000c1081001900c6032013210341d4420304500030340c441054024020807480110320903404a10600885042c0790390303040851346901803050060341c071074018000141c880c1165084080c0504d000c5c415226004101c030382051340c449403046010005103d0310b0411003403010420075603841030401d003010b00c2e4519205d101f209091141140050043c0709000190780a40001c0002200e00d04540e010715440e0300d403954400c1218400103101a00089100180400c406801d82e40700013004a03000c180b41e07105658803040c1021b640c43c005078104202000307001c08000d41c00569201d0203020380600d0720019092858058040d100b014200501c6034001d00c205001d90b00c0360a0858203400d9005808a49035405000064218015190041c1000c0008036960440051000d10718040e01e40100201c148100d50822450350744c0d24444280025901503000300e13030700d280407001c00d403c2c9118a500d558035003960801d041600110a4a031000495800b09060 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 351333992 1250 351332742 351332749
    0x5120a0302010609270314040801020c011a010215100f180b0102070819030c1502030421091e032f030a0f0209102301020f0f0303061e0a0303030605 65
    0x600103021400c0103014218000111150350002443c5000240c05c030030010034101070240001030001c4909040c440d441e03d94803030b41c25000c0d510040d9007076225468112982603044c1e40024002c004078043c0e004040f0200160406590040082c1400c29002480540001c00781f01803080e000c003038802c40034204c240e04410034428090341c0035280d00906542203240c0070f20011000050000c240b5501001c001192080c40c01d040e5540881408003070070020210850381d2802006400440c012803103240c5d50194601050301083e948206100d00200142d07940d0b00800948558900281b03a401140e1301044038aa520754516140c0805541782d88808500407048031402001c14514113082e075400c1c0c000d80744000322940c442c0307000c140d81d91000f44103145040c0890802d0b2403043c0e4000240c52003224001c20305044000342c0294011032a01140144142540f00c0c500207800708049820340800d030002c50964680c2800c0140f0100300050070500c901c1103041c1402d49a03103d043d418000c500035100060851b041c0004e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 351335242 1250 351333992 351334001
    0x10f020a030b15041505130810091e02060d0f1b09030308010602070806010b16170414030c0f010e18010303170c09010207170a0b0f1f0602030a1805120a030201 70
    0x11002510074801002907500c04081c83c4000410386c5481d42e510380507103244050300c0038141c01c4065075120303907407205603008000d510050319140075009440e0028403804011a502581120080d040203090090344008540c50300402c20364000d822003c0b80c80c0c1c0b5001c411842c1c0343c0103041e000e00019038000f01003003459000800140540300502c09002c1e003e0410b08500d0381c5400612600b503014600048004011456003844000356500410a24404c1c080070718401094102c2c2c041e03103819040300e14030101c071842c00007914282030102a241ea0b134034117402c030010744034100c41d84102504200780c40d40406480c041110140e000e1842134403a89104016109000303020352006000d4180401e00300318820b0a6131300015040e086070040000c1c908400b55040304c01c2d040606c4000002d04810b999024021650310000a4a10644010200f45000c0340070202025604000f03108100141c0c0003044510b1140340f140341c001c40144100ba500000b41c1d81d8034408284602e03803071402010660005c2001c002010340c217014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 351336492 1250 351335242 351335269
    0x91807080609040c03120e10030e0f0c03100203040606050d03080726190e070b030117010c050403080c01060e09011b09050102100e1005070908160e01030b0603010f020a030b 76
    0x10007814a00c2d01e40ea4103503800784c0c240000b4041408542440d2102481f508513691506409001c801c2205d441d424080e001d8a03400740540f005004045040c040007a00040210440074020010000e00316090702401c0250701c0544140d6144c0e46031741c00456030380c485003516182c8610980d00c40c446803600c0b040c003c10412428032901455000c0340d039640000c0881001c1103411946c1503066405004807607101000a100d840d2401d4050302900c1400030700060072a01840c101c8072072000401e49088031003405030807200701e20403c40110320b043c8024000f0071116005010190004c0000042d015210768054222030070072a40e054080c2e44404002c0351440c0e50100c9035185c080e81e410b00d2034460b418180040d40f518400385201240d80e50320040f41403003550400100c0154032014000304031504240e8001000c038100b602030b9041038410303404007452060b011030201c021244629006409642142d588400a0700040d1540344d0640d04c442e080180c00d16684010010102c1d41e440002d0104614400e016a001100300e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 351337742 1250 351336492 351336499
    0x1b0d0f24020306060304020f011701170f0f1f020d11180306010302061b210a09060806010c0204020c031e1e0403021c1a07080f0a0203060f0112020918070806 69
    0x401c0c4103840c0c0704c600c15a500946e04031080282507450000413100c1800c540d121203071091501000103a4031038800c4403104201c0d150000e9800020204000a65601e41c2c000c15400c194051007080d49042403605095060041c22400036140071114900340080c2c5510120061030751000003100c00092034114400080340d2011b602810380d039807460300080c03a18011040c0904440d0b50301d1091b1441030f9418071441c5461583e10100000a454a40f100e05107a0498500d000210310258804500a4050240d0358030850050755404d01d448419070a001c0031b0340140880381c5440c8418054400d031072030011f21201030041010301c0c40340c48a0b1200c0e0300c486909825522844842c0c801c01c000d00c05a283e00c0345500c02e4080303a0391500b8508030146407082c90582203218030008503a907101405a62a0b00c080480c0c000c2c400f013001a035154845070103030030484c072050300c80c580d206200301c0141c10594014100c5050504101e000141041c8070b00d0b000c120050040c0180c074441f16a0305040000c11900203031035640141d0180c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 351338992 1250 351337742 351337747
    0xb0906060109091415040e01150603180c1e15030b01030b01110a08033409090e06070305090708030406020c030601080c0109090f061502061501050c1b0d0f2402 70
    0x40c08103504c910806070641c0040b03486030440d0110341d144d98200d000f024901000802071402000e2a0141c858024001c0d02c000070b08049018501649503240c4040c11a0041d907003001040c60103da028100c1c00200c00303102e040700702810019280c0d5908001e0915540140c4010541d9080705c1d000400b200e080404050602a80f240c001d5241e00c00095a010701d654451103c5549459014030201c590741199011086020f402d48145610514050440d81948050310751182442d240c440e84402e4a0118a604485501000c00110024481d030040d03500b010100c81a507803543c0e01c94070341e0342c1594425008a00568007402c40440c0030708040283d9801400d404ac09040c0d4070b507040c00000c040340c0d95403103290201915201c025101c0d0500790b12120081002e105182101d400441029447d114100d5001c0b105004041941000e5401a000c031404000c41d10301410080e14a99035800104070070315841c94010340d59a00003000502c1054461641a015491540051500c403e4040a071540a1018100f49005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 351340242 1250 351338992 351339011
    0xa180b010e090c0901060509040e030d1e27020f0f030111090a090b030d050a030b09191d030f13120309030506010b09010203041404180c05030c01050c06070e030a0b090606010909 78
    0x40c0c07100788c0c3c07048802280c441c02c010003c0d4a14001c10b04601c0b9050315007072200c1d5800104195500ca00c4003810001e2111050303600324602100040e03480e400743c3d942206009070041c5000140c1140c4944014001800300c10803002007070848681c01403040602d2400280084a03240401d00c0900070044810140910007034040030940380d003100c81c442402d00001103075134042c0500035045281551800f812280b0281b0f007400100000c4513100d0b24080c5001d14201140c10904942c0b890300b55044041e4004600e4404241480a100c0d405051241c5c1039000c000c01c0401c500c030f281c0d8218410140295240f071410350550901d1070a007401a07024041080040145c5040b590b00801590f080742c000303140f0719900c0300004010030050901120502c180f00380000e982010080355a44907804c0c0c9030143d040300c49180d170203401540e40d132080c0e81d1100d40c2640008002080548154000c43c02400060306945c0528035076611000d4201b01035800a039650400b10400410756881a400c1c00108052002440503021 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 351341492 1250 351340242 351340247
    0x607050c0108060a1a0307090e160e0f120606091e06090414101d0703020a09090305190804030e060403030c0b070e1207031a0f0a180b010e090c090106 66
    0x9040e045181841500700000d081d5039280c3c203a4400401d002c4150101d080383c5c00e01c903918268812101c0d0310200c0c0103a6004038070384454401e158450300a0314068070250212450a488031850b000c111503000c540114401c105880300c0b0078585106100c04014815420320310300708692032030003c103100c0a0342d145d0744005901680c0940401e03008802940c8400180d1a103080040301500580c00c100054881c40442c45e81000e03c41e8000103000c006101400c80d000003103255507480700003520019500108000c13040c48025200c0c3c1c00048038612a04109240607280140035141802c0400e8100101e4618410030041c141c000d21034a100e00c8040f01c0b0980345c20b0031950060003c44040c10f024041c00300711000148864001c92180c2c070041d200a1a1408103d408400c55540320028001192021070b00c101c001091414041c0d624007480392480c050a0980e607a4100a00405000e0203542d20310360380598110103d107262000d0703400781c844a212407109140c0403c0181c0780c40921440c40e40180c840c4801040344c6179 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 351342742 1250 351341492 351341503
    0xc0102070b0306030307211d0d020114040302150d060f060f0e030a1b080c1c030c0c0504090c080d1403070324090510080a0506060103050601110f060114060705 70
    0x40d5100400d81d2070340c032003001003840c5025001000f815112450707003951990764a07c6101c11800e0043c0d44003016150b81e009203802c404022412143c000202021110040d0b00540d60304000c40a1000d16605041e62500081c40703451312640105403000000401403020b880c14041d003801782c000504c4821500c0d2034107000501482032a00348004001c0034010b000c000d690709001d4002040d420104903444481b4810000c40360711500d100e21143c1e40300b003120740340c014240484000000002c201d080e000111190714103507800d242c51041240c910111041c00b2807644e0b11841100000c60065500d500404e007401b81300d914243c6c0202c00d17003090140035064005805003900490342d100c078080c0703004110450720740505410324450410701d41d0140d28494010640b00541d900c8141b103000000c000029080e921034440703480d00361040010782160001000100c5950181e08045c0d081101890040c0c441c03822034075541d06110f081c070881849074202a00400604900301c0c00b41d080d070f133022100b80f494490142d4030140e441 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 351343992 1250 351342742 351342749
    0x1030b01030f021206270610030b0c0f1914130510020a0b09010219230306011e02010515150d0506040e0a210c031d03011d030d0b030c010207 62
    0x841c8001d03010031525007040420386034100b5400c90b202d6041c250a4505503441b0440d9410502d00c850040e11000d07540012081e0080c0d4040070071480c00ea0450f20b0b05c0310024401010000070101c104060714429003050300030700e0021138202d849403079040011002454841e04c201855051041800541740a02d4080c1600c400c0710710071202200b210207090020303410030b04a4600603211420860800595020640083c119409800d49101c0c161026002c1030340d11520030b03460740440c83c5100000b40d601d00082d1004503004841410000d418007002689000c09004c080d0a440050751204240000154081540c0d9034940d022190304281140d0032408001600902d508035510a484102244035912990300061240d0400002d80340d18514504001000e06400804102c1c80b0344004901d8507450f102e2008080c0082e4141c1d2110560448004125081e5180764803696155680303401d50303140d440d07c00060030026089a409180c4625160340c4600440380044c1009000341c0010361101075a80e801701b9141c080c1c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 351345242 1250 351343992 351344003
    0x81c02061e0a090c0503030a0816030501030807080d110309010e0106090e1504110a0b070c06020105060607291006020c060f0a05070c150e0f030c0f0609060706050c0901090602010501030b0103 84
    0x61081c281441c0000c0c84c09603108541500000500c8a50b0640c4140700784e2040d41c0c11001d4009180c04840100c0c2203d2091001500105060003154000340340f00c8010f29440d0703401100450007694039090f01e03002d640f0a88401c00c1e0750f9035860885910482c280102001801900002c2000c20441c0134529199031805002c049103415450004082007480e0115684411020344100d411030f407540e0f11402e482c0c0c000d81041d01c40d4140504006805032050282030b106070300191000d4100b42d2181c3e00c128804121140032205c0704140d002017101c5103250140c82d80305590001407280c0180c54810003a060110111403240140010840707104a0701600084401c140c2d0940307449681d44203070b1304101c082070409800100700100c04200cc81d400942c041501000208200d41d103110560b5040e08255072035a1a84056400c42c002c002181c5241c90100c0143c03040c080082c10702440c01000ea500c80c011100100e074203100026000c030701100780d9640084813102901d8640000c21443d41191501007040c201480002d00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 351346492 1250 351345242 351345251
    0xd09080d11030d05100f08190602070f050d0201051e010f0b2212020a090216030503070e0d0507030b1803030109020d020d020c01140c04030804090c0306081c02061e0a 73
    0xc03802081040750840e60800408001c5424040b0031550b80317200c9803180300806003c0c504041013545000c1820200e107404820a203400d10240d56451010303403c0710030b0a40322040c05d100c40001003842440420b07103841d483c2d03000050502d0001038441d540303400144218070055500006100101c0601d402000b80d9103840716058841b080504401140148455a0411102445030010350011590304c0d414a040c8200e580041c120349444075038080f802080c181445000d1010700c00000309008200840e0000c04a18003082a01070f00c030045160700d401254100c40c1c55205a60400c244030b86098419042202e441500b40d51010039990345980380030601520309085e50001da442d00030070459044400d08080c55400390b440b06501800c0c1b5008200910b845210003540f040018850000f13001103c094992011100d4200350808031004000c0820a00d8901490355814003c1115681006180881780c954200308154200f269070003800e0407405032079220b9103001511b9038461040e10342e481c1580070380c4141d00000d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 351347742 1250 351346492 351346517
    0x9070c0201200c03070f03060b01030b030c0d050709020c06090f030306060a03051005130c090f0807061812120f0516080703090b18010e101b0f06140601020d09080d 72
    0x80c14840e014a2a80c4d00d482061703c0060300c1e00101250800300c0380110700c200060b0f0081d10040d02683d10000030981d03d5000310002348820f26040307009a8200b40144101c403405600c640382882280d101304402451940103008000b01c416003000405900103980003c0d50560415030046000da00451554005060302c1c0c000042901c190305a05800625004110100401e14450303e60b00034000c044280000a1240601190f01c60414058404403414400206002031502c002112034481101c1d490340c04100361900052074030250160007080d0740c000c2e4262405041c03520006010740c1e20303182c0320506011003840700105032808000d80c4508203030820489030b500c0703240d0f180407540d429485c0c028524061020922080751010a6501c04145074280c0700c4485e80c1c4481000c01c91541c40c80b03841c49c3d0004820303022942c0b82e14013246001e41d000707201c0e16240d654100b85617900c07410b9030b16030380040c2e0721440c1c0c0c14101b000319a41046401c681d0110340c208217600c0303828802c0f029150a905500c0506000c071f09075544 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 351348992 1250 351347742 351347807
    0x318030136170a0e031219020a020a140a06030b1003180f061512110d030c120f03050109050f06040b19030803040614010b03010612020d091109070c0201 67
    0x11038050741c05805101c941500b8120000103030000501c0b03000280e031408000032141030010341540c002c20b44022607070902c0400e14038507000191420400c011402600c0740800103850780300c006d20145c8040c000c540c001031300210921518981aa004000b09400c1c80d041039103d4072030000c078a2030a4501d141c041129280f04c20502024031480074001d1401ea4070381c000d0014059a54400381032491142d000d00c4096948940e400542d0b80802c801501040003219030f050107107000c1002160643c444d06120b828040c4070340b2120348a45002e1080404100c41006038854268948242405000c201c03500b00901d050200c025000000020b2505010356540c10300124940da1b1024a03507490803051364500d000a0326440c151000e604107407403c40d07505007003074621204100713a81b020a041e280c01c21011400e43e0318101080383c07814040320018050720b500300100d9001d88024041c226506000ba100500c0010004061100d0410005c201c80704011030301340b00e000140c0e4842c4900d2312014100b60880150941c0c103a01 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 351350242 1250 351348992 351349091
    0x50901050708070b0702010605100e041d0604030f020d050c100b041104030609021206130f0303021308011a03071d060a0906080a03030b09041a04170c03180301 70
    0x90b0036580e0100b001d104008628600500c182c615074001e0100030354030000d02c601c07106608180742c04030341d00e107407402a0340c1880e130300141810120b0400c440c007140d61078441c14101901950290b0000b1002220040c403690104041e201c4084c46140607440c0404103000b154485482810030380281c0d40300c80c05601c0d107540e1030f001150365100c2042440e654230361343c5c80c10100404001d0b1089004a1105205499550020404620402480c0c00d04d10911140c0d945404070890582c80c2182859403e05c903052211182c040c2c9107000d0440317a800010041d86500c000d0180440d8a1910b510a030310548080c0025010040007080e42d40e8800d004100e80c1e16540000303440c50310303240c0003031030304030320342034002858010018900c41958040e40301009441000350501911840842c1c0141c040c2450f0148941440c18a00407581c2c0701b40501c90036602031218403594015030740058100350b190380c40440e003042c5104503e04000e40c0032500714000c11402501e02c8001104401d03400840d10074508002a481e10b44030001c05 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 351351492 1250 351350242 351350257
    0xb1903110a14032703131410050d0207152a0e040b010c0803070918140613020d0504030e041409061b0408010c0915210e07050a17010b060a090605090105 67
    0x240712030050301d136a41440d6613800c00d090030700e2601080007000401d13803810002542c1824014082c1d803908100c2030003e8a843c1d00c42c14001d02e04950070440360000c07070349000e0081a409c03002640030800751b51258104500c00003442c1c42e1100384d10041c4605c10080d40001d41c004225000f9070740410524002401642c1c200512200500941c9000040143d038960200b902c1c0180c0d0707000d40304071182d410165946800c86202c0300c000301400c1c04000c0460300d503140c00f1949504085912401524080700c800100040d505d00741c1d81107020820b21000301080d8500b034007549104000c11721040100d0724002a24554805c405040d005405009034003001c13000040c04215400b42801e24000d118000301510003c00f031655620580c40f82c3e143e202000c800e114441c400c001c0104000d04049882c200baa00c02c0f140040c280000c0c4503045200b2181c000995440390442e200041c9524498040f0390210f40401e84c0c06c3d00e5071440800e1003010100816030f0040d400c0014101581c50701e280264882d2841401614039106004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 351352742 1250 351351492 351351541
    0xc0c120c060708040f0f08061906030f0501060e0604090c03020d030314010b0301050f0406060f0e04020d090515010f0e010b0c1e030705010c0201061a090a0b1903110a1403 75
    0xa141414060f111006004444043c0d20b040c0005070b0f1384e120408010214025104203401c841c000c191100d01002c0882041d21558000040e03240d81da90301c2d8151006000c20480700f6035142d400801c0080c00c00103156500c480262014807500f90075a54802d003c05241c00f000388180c540040c40c00905210750302060655030700300100d050b0380d6100c03504445250000d00c1400d00ca0000e044800ca03107030501c0c0c0954821240701b5180c1011000106c8d1054501c44021580c4a80069080c0021007074504180500101035000b2400341140c0080044080c0c8020341c160010000b4014038070b4204420400f08456074116030000c0403aa0721801032881041c140200c2d9100c86280088101100e5820000440103009561141c0000c01c21800b80c0c6100f40d0a0f905d4911440c1003103104d21750040002c201c60b40c02843c60304002004079410945403001d1a1003900003541c0035541022041340341114a4140c41045550b02440d0641d508042022000a08c0030346842074800c00c5e10f01c080041011600c821885c200e0b02c403000b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 351353992 1250 351352742 351352747
    0x10e090d030e010b0607030818031206040c1e0909060e010b0403030f0302121510020c130c02031608090306010e0114010e030c030f0609100501120f080409060902040504110c0c120c06 80
    0x5040040c1810300a450450600f44040300854004400004482c042050f104002404cc1e0740d0b00f08000080180440240a002ca500305044030a8203007400b00b0115011510317168421410000b00c8000c4551580001d400a0031034801480400310000948003101c2d40b43c50027248921440c00200c003c3c0c040c01c40034161f01c19480090050014102d9020310000000350703071190803400d1400c4102e81c3c5041945485401800c1050000f075081d20039000b030143c00515004aa02c0c000006001e1035400100880903121900c4c0440c0311012403809200c1303a4018005000d80300019414103480c0c1081c450340d000714a040c04800003400107140c0702846004045200102034600c2c11000c405469102e08080700c070f0526601030308440e0004422207204d081d05071b0b80200001c0180320420b030f079003c4899080e102c058a500e14140400030350001640105005041c40090140c1c0701d6140009100568050116464000c40d080c001e4103804980010300302e01c2d16900b16040841c0c1e282120155041c00346042e01c154200100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 351355242 1250 351353992 351354007
    0x19060306060f081e0a1413050c010f020c0402210f0708011a09060706110d020c010b010507151d01090317070c0b0408090f0d1406010e090d030e010b06 66
    0x154001001c503029a1100010b1280d00441100e005404031100300c14140d110b071036040210060400c41c0d501680b00c240005114450a41100c2c1e84041181e141460080800812081241c10300c01c0c0b030442c1d102070901d0440b05c41c90b940c0203034803840900d80c0503014690100303c0d001008409007440c0031003d00394040c41d00b0350a0070201d90210700e400b101c1c0031010806440001440242c5041075044004030040440d040880704003c00c003043d030000da4140d640315110405040c105c17400d00028240c1e15042d000c0160389000105409007502c04848406042c080e0134490039000c10701090000980510860b00024140605800b9200d041c0c1180203d1042d580703850043c0c400c1503005151804050383c040c8001021303a0780c0ba08c2c226041402d1b2500100044c0501c00420000b903d0340024000c518402001d8a203240356144c089490800a0030003540d001c0310800804034425014881c845c09007004a4103c4050f01d4075407a000d60750310501055008265980204000f6980294414480e110b801080c03203640d00f44 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 351356492 1250 351355242 351355247
    0x61b0b090312180703020d1506060c03031b0e01030b0a091a120d050f070c08120706050609160e0d0b040b07080f071b140708030a0f0219020603061906 66
    0x30400e1102c5440410300425039103544118050403450818008003807481c210341c24020404000300c000c07242540707912007a40ca60707240b5014000140c00076a40d9500649018240101946c640307101d02c107080c1401214a01549a1040c802c02c5409000c0c200481c6083c144408242e421446910000c0b61911700045110790344400031f645101c1c4c90040f40c91040402c401c0358802c3e110001a41c503203021079804c11151014074240c60103080c1150185140740c0406945034255424566a40c40001281c24002520f0040040c1ca100e196003044007901d102d805440d1030310100ea01c40b000b4600d03180902c82c245000e03000aa603141d4800e030300c03903174031408041c82400c044c03901d074003884c10903034442d00440c20711740006c0d420340480c0c0c2017148600095562081d240c1c84c80645d20070100c0b4400b4003622454015150050318010401c422402080d448006540d0b810b003104001344100400c100140841d00800003084030a81e14a4409201c0d0f0b330126a01ca64980314a0300091540005030000110003050100004003940c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 351357742 1250 351356492 351356497
    0x3170d0c050417030c0a03300b010f0e031f0e0109210219021e030303130201080108030a0c0b090a0f030e0103060902040315050411030f0615090403050301061b0b0903 73
    0x201400f035420032001c1c10a5206443c1d00414850240642c091502003000c0303882240f0508400b282c4142c4480d0481842c645500c089503c03031402110281c4580031110700f540d02031101d030710680c224030740194031942c1000041d41320400c524613201c241402c0c0038030103000040765004c85d0b030201c00000200720620140c0742144031071200496000e95a039002c10052141400401d07403040191100340c0701e00e80b0741119401c00450700d4040500381c1e400c810351218466551010002075000c4c1b40140f079448802441c5100040c045401600510215003051008540c01c90b048101060860b6000800d85995900e20f20f20380e140c00c1500340050852001c40420303170145904034a041c04e0104003a6130912041e501c544c0b14400340d01c90792200030004184210040c01d0040d590348066000741c03290a05031085c40340d0b400000c2c60310807846120340403a0081c80600030f008000c50030080422102307582c0540d907403506071000b0b4443e0105101c0c1e40140309404000c0d490711859a40400b802e50b5020340d094007241400040141d4a4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 351358992 1250 351357742 351357749
    0x30e190806062b0b4303180b161110020c0c06070309170a030c02060a020c0901090605091806071d03010507092306300708040213050402090103170d0c0504 68
    0x40c180340c40300042265131901103181d00c05c41c04080071002c4c0b500801c510410340c603040e42481090707030b02c0b80000310580314490076000c400e000e407954191038202060085554005202c6030010712480b170204111040000c142c80c0e580320742c203220040e1504541102d0030700700109546041c0d031001001175031004254004503402c1c1500c001c12101300c0b0800c1408465603541d000007c028010910f01048400186000c00040440032400d04c15070b031042e803e03071001c02c1c8000c0080c0c024402e12030319800709100310b06003009115072081102030700314185102005a541c69450190001041004c000743e039070040c01c004070b05001c1d02540500200020b18040e0002041013891307010b102d01041ca03146981c00710006101200c40001e0009012520b040d00e0140306010384004464a03034014403400d20f620000f16402c4c85803c0c800c0405803114510f9280900c108600b01382031080b00402c540c900b00511000d0788580c254981503d41c042003215000303141007800801800340d9514500c42900b405102c0038000d0f800360180088 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 351360242 1250 351358992 351359011
    0xa0e07020d0f0c082b02090f0102280807080a0302040905090c100e0111011811090c070807080c031b07060908060f040602090607030e190806062b0b 65
    0x40c1203456100b290700c044080010340c0050504181e900100d070f2500300401c25605540c03996204030400210002035003688622090340c80794040307031034025401d0014602202100c2403000c0c21240c444020303801ca5500c40f800c1c14010441036984031408010703c0d002122032075500005040d03261113864000801a5005001e842052401c1c0404a50400700000d1600f034040b03c000e10446140c1082d0100b214510001d0640c01c0c100301c908440089085000e1050640411001e6000e030000307151030800180041e0117040c4180141086000c004508001d9004d4480141d03100d040e05a944a01e0b040507400c078019100154094040000e0643d0980500701c400c000340701344002034038100c6940c0c840c1942d0300742e8944103512403038000c000040c0a5000b01084190300602c51507006041407503000c04501c0c6604142e0045000c0b4118000d880540e1401c24840300403103071507607041d003403182c1800117135a102d0902a2086000d0700000c504009800500c03c40c0040100f0910305030046180c0300d0404005000040e11008103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 351361492 1250 351360242 351360253
    0xf03030a0207060b0a05031b0109210b06030715030203060a0308031f0603020c03041e08011b0e0607080423090a06030201080907030c05010f0c05060c0c1005010311120a020a0e0702 79
    0xb03130707410190341800071604000c0c0541807040f90040e105030710590340c0300c3c15410030040e00808039241d49007542181d00810b1307285624196006070700c0e09509102000d4143c0c0e1190b0711160080120106c0800100c084030355500d0b0140c0c40b503e41da404100a0b050f643c00c0244001c0c0b0220030014140a41503130903403500e4600711000c1259550f840b081c7c1c101d03c00c21000d21640d40003040188000380c2503070401c060f00c1d44280c0a540103c0e50710901942162615611b842c0c0540020008007042544500e20b1800064200d0742140750046c0c5660745c0c03119100d01d01c00c1c1310b0040f503c401c103421300401a184100017240d01a0428403180b03406c1c1174000050505003c103e000c5802000420b504074000103041c0150b9920904889000d4113020054030f1490341004c0500411029886200008806001060045080866058451a80b0f0b25030b1401c1900c02c4101079a118a81f00041022540303072045640e82000c1540c540040300540d00075503080207100b850180d00150403003800121020b074050f90034400d003825070a451 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 351362742 1250 351361492 351361511
    0x82701030c08070518010207030210020f060c0901081603020d0627150909050f031908090a170d020c0a0804050f1002030a0e0409050607120e01020406020715020f03030a020706 77
    0x42d41c001d401d40f00b4000140c030601201d18640c0c0c0e4051084400c0301d0500448000381d50302d41c001071000407002412030061304600a0188481c03000c000480d0821090088941449802c2c8002440504014003100321030043c902003182c3e25000361704a506000c0f000c2e00502c2a19154814003400f07924001800a03559410040350030200e03810310138200345003c0413280c602010b181075074201c081c2c5000c000580e0603001e200441d00c1013980400042005140e03c1c6442c1600300904c1c58050110940203011800d03513040582240002005030030f5009080010914080e1100200c0300004000e00039a042d08415204545030361303090000003809030049540844458081307840600620040c0001000c3c13810260303005000070720829001ea92000c01c0003e020b0000698145503458440c42d00d842503400b44e0109091a486600c0c1c3c0f0075034002c4441500e8000c1c025441d1501d000c2000303542e910f092182c030f90060400348590305c16a00c24001407540240220840351242000c0d02c003d4000d501a5504441ca10325000080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 351363992 1250 351362742 351362747
    0xf0507140a0b070f0c170105040528240c0e03060c040501120504020f10050304060b01020d210905010e1b030105010b0901111e0f01050a0608060112082701030c 70
    0x2007040d10002a4200d041281d590b40c0d1004c980341403101220041500d040200302c80707039075000031076066240d0b500210303484c10f10b400c0031030a0080c1006a01c0340c04400d071081d90840401090b401c0031190303204014400349014000050321680c040c0011852050034207446882c01c0f68010344000c002c5070102c0c16035840d511405000040c505c11481100c2c0428401c0c51000c20005c1c3c1684680d5010b800902040c2005406400181040c43e88030b613200041180842404140142e0340b24a40c4100402e00003015410007480c4054025494040580c019606412000c90300c2251360f0000b08100e0f900c0700003030080084000d4120b888000c40c180b545448024900403003400c0c03405001e038034100c0d6200c2c64654a40008540115070142c2c4100000d50103119801e0040c5601d1803c40c0340703400342c1c01b00320003500d41041d01c40744082c00c0d1080601990b000d1410f100e42401401000b1509504441104001d0100100b062401e0401402602400d4030710111282902c0c00b500300001090a605109a03400c002d016030fa00c000307 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 351365242 1250 351363992 351364009
    0x60506031504030f0309020d0b01060e040b03030912152a120f090102070c030c180213050d21050d050106050c0a02060f0f16020406060c050d0c030c0f050714 69
    0x1041d11408803580400c0c0464000e03404107400ca03a041c900031035044410340102d03082102810040301c83c00316200041200e01c3d030000001e0703104d910440c4c00744681c07546080007a649000c0c1002e8a07100b94036202c89214160410030012001c0b20707400c1010304040c0b07803111600c07441c0f8486040c2c01022101d52440100d034031400008a4603803544c5d8030b658200503210202201c04030b01004089410640d802c2080c1400300d04041c10040c0114401c1c4041c01c0300303034113000b21360407884181c5501e5a40700b8010711114032031803000841e1800f50342c42918851407104450525503400da10820000340d811289040e4803000d103900030010030441c02c5170a0240700d0b0b130340d840404660074031034461404466040001503500525002c402003841075583c250301c90034041d1030301d06c1d1002c4d0741c008800c029528486080030403c505084c0102801480b00d41400d00c01d5035803607100d09484440c8420301000300030b140542030003007602500c485030100d50001c08190002030b81d0700d001561406280940c060761a01c0303c84055103440c00302c1c2c0c13 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 351366492 1250 351365242 351365263
    0x140c0a170c06031905040c030204020d05070306060c170a091d0403020c2d010306360b0109060c08040b04032306010b1b0c0d12090f03030e0f010207090c02030706050603 74
    0x2405416940c00c1c0b844130040401801c202c3d00070260510000c050f91b20381c00504403010744c2100000b0a1708211101030121030b03160b8020710501281813100740224100c030050f00407a403443c1d6003013959075910010072a140103058111038004168269040142e03200c10107000e01c550310039000c40702d00804540801c0700c01c40741048454907208030010002e41d00c45d0030348294480000e060402081c0700e0341b070340c006030601c0d1540400c89a1081d40e0f500340380380342c85107000300c2400d03420721002c01c201402c0008002030080840c1e00a040510200007102030800c65508101c0c0c00604080703161644a94480c58040b810400c081207102c00145118184600e4400200f80c050480c2c4c000840070303150090001040350450248440da030080e01074004200c00940b21a101415068031038500704070340d00c1c9095005401201c2d190050500c2c032004e98030600010b90012051078125104880d2520000c14a00040740360000e0381d08098901801c00384c031500c403103400001810042c1d204507028402caa443c2010b02d550381c904001d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 351367742 1250 351366492 351366511
    0xc050d08010302130209030a06020c0d020606040501030c0b070807050a06470f040e070302011101050106022a0d1b050d3203040e04030f1b140c0a170c0603 68
    0x9420b011840313280c0d4020100d9510184c1502d000d109030740c03a6281203801c00c11070401560020003501ca0040d6060107c0341c0d00a1003103404011079411611890780341101401100304203e4005244814841d401069450b086e5100d000c0300c4036034070a4a0084041d000d503c40e800d0300c040d0034103803404101c6d9a4075000388a2001d280741d220b041880c07516002003154046102c05804c95011070100c034082d05d49005109001c160180100302c014030f50b2000500d18840c6490b1684140d161000500c181c2c0c0d800325007080381201701d1590490201f11006040200c103038418a156004107801009001c00c4181c5214680729203d0742900000d199a40301485855507204500811407000c0102d0002c3e02c2000b42200340440418450550440700c0070b035901ca1555000d60820800120380c0005c0000309035002d49600c80640d8980307080c218030507890b0405080f0050214004091811803218902052401c01041c80c2904008103944070349980c0301c440301c0c85405811085607160041030b07140c04080c1810000c41e4020710700c10 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 351368992 1250 351367742 351367759
    0x9110127091b030b13020d060801020d020403110904110d021206190e010b09010b0d02040305070803070203160b12040311100614030607080a2003070e01080601230c0102040f060c050d08010302 84
    0x1c0003514002d40c000680305c2c0e030307c2d585c402002ca01043c0910140c403d08002403401640c3d80e003142072144c0c464408a00052045603035004000c005003c480706040703051802e650b581002111413000507480d01001c20184050700c44c81c0100080400030242114459a286e04100004d44020703042078242c504003500c542d0004078100042003140d003a40020000b032001100010f0400b034603030b501d050801c0e006a22a030700d19400802c00c2d409500e8144160742400c4203512220051920f02080c182c140c0c040c201c0e500c940000d4440005051601803140004010103110948945e120040300160040c01c05000b10704200700b04000002c294100050840d000b01d4968940e8004d50f500c1440c1302c0054449128140501d12218140b07440305d40755a0091030180c010f0791242843c1d103103154001080044001c1a59041010041040500d04a810440c0759105401c2407041c3e6181075000318140a4030549d403182d40c1c10701d122035000940c0c03603000b080c2c40c174194403030b0003a2400c0c4051400c048491782000c1c00701a5108005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 351370242 1250 351368992 351369019
    0x39030c0207060e06090a030b010f050906010e040c031b200d05070f0f02090103030e09070212180a05030a1209080c1807030b0904050607110109110127091b030b 70
    0x1500701e140700f50001444035140014100200b29800071650040f100300d4280c1e00148568014608040043d010540c0d183d1550320300000020243d80f892000580101e90741d1051207940351098100305004541a003410500e5508600003c041000301c0312040c3c0c400a000082c056070341008240d900702036503240e840c24200440d0344c40d10103405081d0b50048910142c0740040c8001612006003031402140a40c0321a5188664001130000700700d0021710600844d0081117580c140607082006550404000c01c3c148080054040c01040d480c520310b82003590f140c4111304003401040880c4409144401c1030740c0c1c421802c955150006642c0e401c0c1c2000c0702d5804210681c0c3c0c0c450108216070010390250491402103502c047e814085500b14101383d5003902d49800010406c06003603005100100c5220800c4000c000a00d040c1d00e41011418143c2d5070b03141003040c26014205800804002c088006c00b00c410399481c048e54414106000f044810309282c1050034420110450394001d00c148280e4150180c5210706481a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 351371492 1250 351370242 351370247
    0x6140609030f1504120c03090311030a0203070b09010e10080609070e0d03030605030c010c080d090c030516080d14120a020d110d0f0608150a39030c020706 68
    0x82501000d400d44a600c00300329642404200107950f41d0307551203c10b002030510b400d007039001002c8035580000b0300c042c400c144000a5800b0900100b26074124141c0342d1030501d8000083d0500410f400e0107903046c0300e820070210348205034400820401400f6202c4030a40c130181020301c1207900b540707901c1b00017141c070001c0011020300f42981a1030b84600b440c0703030040040f6070240009504010140b400d4001030398400d01407104e820304118440e001e400034248458042140c1e601e401c010701c03d03009c580308981d4444e1b859400300104a1243c02c042d40c0d020b000d40f64040b51041030a690b00c0f00c3c505c00c102c400d00c10206409140741c01401090f08448101c8030540ca4880c44806a40303040a000d020130031b291f5800c2100c000e08181c580f18135481003c0b40511070f6640d07868005d03501c0c26510310600103042d4502d00711040000c01d0f400038800a20b203800d0f0034860207a55401800344001c101c80d0040e800d071964000401d0300d4070300600c08004003200c00d1075082c0c801c19522a000328211040c04107800d025a001c8081842640d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 351372742 1250 351371492 351371497
    0x30921051c0e0d111608030304020109061e0c06090203061e06010e3f010c09090e1e150112020907031401170f160812090d080f09030a140f01061406 65
    0x20362074048960141200b003400b8000c031740b9a1301031032154001106000440da80040c1b401d004248500d0300c2039006030303210f604402c0180e000284c001403001490750740301040741503000f40010710340080039034480c0d1401c41c00d411503468400d14203d00d044000b00c00203405601035804a004d07410042c1c21038415003400004518074500d0191040110301311844696400d410309082c1e02e40d450021400410301010980019054851a0304100b4807d82041e00341c604600000400301c2800600031079101b0451446014541018207410024520b100e10fa400400d0b070711030398004031244030701c01d45d030210032940d03102c204804031410a81c1d01140d041d0044c2c0100002142c24074044850603d60003550f411030402c400d09803400702051440724440084140c1040b41903070506c5180c10180c8070003035944c0b52401d40c2d0700003501030791280d100910115000c60304190450313803101a502c121001800310f91804609052a1348200d01c0d07192910300901c40d03507068409590303060046200300c80401c001c030034200194404000554 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 351373992 1250 351372742 351372767
    0x801020c0c060d1b030c0e010206040f060203180d05090901061805090601090e150a1203090612091202010f0c09031a0c090604032402030412030921051c0e0d 69
    0x390f19044c0c01060712406a4800d50b00b4082c0d0f0300c0002e5180c580b548042d12036a0180700503819504914200004070b0415210080d03015409100141d13a90b813444001c0321205807414134407005100b0000c001068035000350051074103c000310340b404032a80c0d03981c0c81100c8071f07403120010301e560b02c800c0341c01040b55080400c0080e40000f4141040c18000c1d4488507030400c0850304a880803940c0c075051a600251b41000b240410140c440743d00401020702d801d403000f070400300f41441450204094a008000100303c680c0c0501c01481d071110000b0010b00460400902801e004104d560103540b07000507028070a03001e2200e100807240d02c00e00d00380e00c1c03110501404407043c00c0200801c465100400c83d600e401e0b601c0400900c060f41c070032032030751794803034038252207030500440c145000001c06204000f80804583e074100200c2000641c2e10780400d0300c046d40e00e000403c2820310160211800f000030984801c0341d400002800b04010424105d24080c007408100d48183e81c200303580016280c100c0c5140c2c0c1c4900b440780c0045c4404 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 351375242 1250 351373992 351374017
    0x1b01020c0d060617010b030a260705010504030f0503130b09010207170a0e061809100305030a02070501030e01140403050a0e0d0b070e03060103020a0b13030c0f0303090801020c0c06 79
    0xc466600000c80e00c0340707841c290100c1d465540c07200c00b031198080b290f20000c0140c00c490000c109810740100402d03a5040745000140a03100041481c0c50211010b040141c0200e0204045588411142c0303000c034040c0c503080e01d00b2400716020081c5800e03654030603003d880c80742d01400705039510111942c50340740448602410b003000554007001440302098810380c81c45120f081168000791b903548038420050070007900d895a2031140404200c80400054403400b44c51064600300c440e0501a1906d010300400941554401006800085040030310f050300800c0c00c20403182e0a88083c4268044e01219038202c17144059507181c408803103004100842d102c1c90161008030380301d08181d5180c00c0140001440f41e103081b0801c0b070b006a0b003074003004038060b482140640c101405400508413541542d000480c60807182c019100284c10104080b0304000035407006100464202d22002c25440d254011403580150390b00040e80482c5a40a0000c7c4100341442107a02c200c0c0c642c4050455900e4a001304401c0341d010080c003144 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 351376492 1250 351375242 351375253
    0xa0905030f0315030f06131203140903210402060f130f080607090b03040f120302090414011a0301150503060a0e13020111031c020703030204030f03080403021e1b0102 73
    0x1c02100c0c000198003d111800c2e491680c0010601018034003c1040c41015140d0016401d10441048906080c41d1580c2d1101c00c0c4409aa12841c08500800c481003064560000d20300504c00e180f100840289007002c05825604000c8402d961f010071a2070003a500207400403006c10a448c481007640e00500744001500d40305030440b9544510300b03100760060f5084501d15802100a11151940080344607008098101002d402c501c0c080d210480d40710601800501250100070043c14031030b110394121602d0150051041145607840e0404251a02090041c516101100c078200356070101c446054a04031028004c0704e0340349041d840c50840b000c0d000600641d0300140c880ca07001c03600d0b07515401d82034818094404203d0140030180001018404150a080450b4004000c071017100c1c1c0442c0900401e681c215800541e5890641ca400c500074440d83d40701801400078806500c0030160321150040c02a0302913401c551005049a411110848030060360000c143d0020541c8011499010207492850390140161003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 351377742 1250 351376492 351376507
    0x6090402190306360b0c040902160507050315130305090411090a06032007020f030106150206090304060c020d02120609030c070b0c06040f17160201110d02060a090503 73
    0x10301c000c180750012103145407039625007860001c510001045652500000b0035050803884e5203020003419000c4060010320390b0300700180c0b1903003000307084034001c0076607100455541d007950304564910222844101e0381c1d4020030380700064a2400081d80e40007200c44510204143d11044c41c80b280d03911440078214103101b820b22500740b269403107116007181c8001050016559043d00030411001e9060b82c1c0081d001c0c1498407100c0b0b000030700030840405042400303044c06551008030340000792803002d00a940951540c202100403d040c02c4040c808594040e50390211902602c03030810441e00c90046005183c0000c0c0482d46203400340c0380090a0346403480c0050b0102e4081da48e50710019040890885e1052007a40c00004d412000400401c0503034001d2800e0703801c02d4100404064403a4682d64094409459107441003021424030581241d0320640d00e10558040341d1fa080d9101c20103105200c001002c2e804100510302590300801c1c081158212444280d01400556071038404050003420042000d5070648070911050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 351378992 1250 351377742 351377779
    0x60b09062203020904030c02040b0111100c02190321110d3218060f0f06120d0305070306080616030c0207050d0b0103051606051602060c0a060b100507080306090402 72
    0x135008500941c2d842030000403a00620054664a0707040c941003041201304683c5060010403140c404c5016980c0200380090100000c0380f0b04800036020011a00c01c500c0803a0804d50001c4528031500c8401e00d07011064200068440e040342c1c0b0551160f0a84003007081440b2005110f6840705d02032404984e00358044150508883c1c8203500000d541d86010401c1c1800e0041c514000d48641c246521101d00400c15840d0107400200104409410104507150282c00f1402550322161301440c0b4110800403510700c0308000d880100506401d031000300100c0c1c50900049800c11003c9101440b400c958880307045000c4521400720010b19400da04034045001e9100c000c10305544a11001d0803c5019020800366035046040c280e040c5a02d118000a01140d03001042108a420006440c01a0140142c00c50464981e00200300d40e0b01c224140710340f450050601800c10450780ba8880000d14405036900ca034160140d080545107031080d13074070141a804003440050b803946080203425a000d031002c0c0c48401c0001d9840e401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 351380242 1250 351378992 351379009
    0x60f0305030d0b130e1b1002281a0601030b0a0605120a020c0f0a1109010f150c0c080a060b03070f0911070b090a061503080a080907050a0902040302010201060b0906220302 75
    0x8000c0c0c1604000e229604541d400106d101900b074044558504440c000580a50f50300449481e10703410042c0194500647c10a00025002650300511680d0b00040400205c100c2080c0484545000c81d03d0182c82c40442d081030502d0b102a10074070f8807240d140031086280d2225480000308162403480e000c00c210a0254400d0180041001d6480c00a2510032000d1078070321341e00d00b04054510300440d00b0300c0040190a03028102402100c1d4282c103049070118000000b211607024140000d4545d40708410001640000040c00703142c003a004be20100071418108080540b0340b2924882d40320205e40c4d07480103010490003a4800192040d0071000780f4500725607035690110300d5104070788510f5550041e901d0002481030f0f034012070140c000301b214000700880c255074440807640075220350001001000ca001807a058001c00c80391020b0321008125803002d9903582600320103540319002c1240103500300351000542d00d00c2e0805850340c0d03420041c11142404e400c846c00500c030b54401e40301d03401e0082140710b0000258458030344 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 351381492 1250 351380242 351380261
    0x503090c130b2701061d090f040302060a06030c15030e06090a21090303030b0d06050103112e0c020d0602120117030304110915090c0d060f0305030d0b13 67
    0x302d05410b00404011001d1402900101000440d10031900011850320510b41518424200a0070401c91040007510300f003c1c0d84075190b0824285401c0c070240500591160384641d02c41d9080751400d83e5071500070400e81c0c40d6403000074801c041d10803081c8400c440c10f00481103800c080c1e03d400079940900d001b06510b00401901c203801640c00000d96602804400e14280b0180c80d4099044003010b10075071001082c2c03096030300c005400c051f1b44284081840e694000c8101e580b540051040c000c5503100e041000340348103c280b0161055591400104460030800c1032541c0300d101d0705039156406a41c01e038060310150355000007207074481c40043c030100009110344054a8070f480c1070312204140b036041c400002c490030350110800034245d0040c0104000140718862400242c2c8050721b080d0070b01e448041c00341c0006022000c20340c0c2e10003500c9041141c05c5a840024000d0324060b25410701030700781c5c0e451800d107401d08280405441500108820304500200b078011042c00c20340a0501702d481039070344450004450fa40712 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 351382742 1250 351381492 351381529
    0x50c0f1b0705010207060507150e0a030e040507110a0b070309150c1202090d0f151a03070e04050715231c0b0d06090609020d0302030408011503030801060503090c 71
    0x15000d54044008000020141000307000405900b410404041d14500407103600030281c98203103007424900c07640c4e504411a02d89100c4202c9aa1040740d280140070308004091082c02249040001460144110a010b0701c581c03288016140401c1c1d0354803407030001d0100404000916488888010014451014050051221b007c00044151580c100108000d41c050602c5240ca8014412071009a0300d01a071800c40303035481a50381260a541c2e02c1c001843c2c0b80c00d0103600020a05e48013510b21107104103404980714200480c01c0d5054962a480c00f0004140291000b4140740c0c4101400e004c0c200c1007038064401d121650410f4003059848a030154800c5500080c441140d1001003680c5410a81c00101906d0459080c0010301000b034a08002c0352115080600103404151102c511805010700340d80000c005580192441d6100c45075400d020b5a41c0d4070a12807072049620748071380100c01c4802d18882c9026a58140e4503450f05900c0c0060440d84e64002904107006402640346a85540d618110854800403222 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 351383992 1250 351382742 351382777
    0x150303020a110103020a090b0a0905131d060705091012050403090e0702071401030902010302040909081e090312280906090e010f090c02120d060e130c0603050c0f 71
    0x82c40c051545880c8941101e05060050040382c1089030000c2e0034206075000c07842c0c1e0b40d8a4511105040b00d01390390592081380c001c202c5c2c1140007020b00c00c1d600b000a0030300c0102600703080d4140941701c050f51080304841d44c0c800500141710100544c64203601c5d00440c18036902d0403e0225241c0200700e81190010b95044002c03407007505c002c003c2405407051041c0e20180310300103004801d2800a502c580698811000c034100355544007480c0071603001f541940c014240e0321104200075951031070b00c02216070010003c1d104886008404040707002940c0700b22080c110000d00500116031145250440301c0d00240c40c41c40c41540403200b440d01500180a114024100341d40d0b50fa01d0703080ca0300070003802c3d880c501c1d0040c1143e401c02e8801400060b09e59003100c0304490100100082c80014184200d080103d511a00b0304080c0000442d0b99224031190012415100d40c61560207d68840130030a591101c800c0d01c004003042447d40d01088101d00aa1001d5480000e800c603107481e104000d045c40c8010b03486411a40d1441c07450 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 351385242 1250 351383992 351384013
    0x1b0109060b030d08220605010b07050c0904050a0803190e1b01030b010e24191209020f04050901020f0706021801170c130f090507080a0b18040615030302 67
    0x150003510008207069018201d5010881d8005001810060407150b00e100f682244600c028000c0448000309074001004000550311400d040186611802c0140c0f8075101d000043c06040c6401c01da42c6018035132007001000f43d004c1300d965015441d00004d0442d100c0b80409186240600038501034030714981600c1000d0045183c4542c1566190f035402c0c3c0a6904061402913140d40c10790308500100a0414210344003404840488007218030702440c450b00450b00355002c6884004128050700c60440500f00d81ca601c1d10040e80c8110b40c07803c5404446029501052640703044800f81040d07409150000e400710005032401024481e502503035404208102c1e00b031507002660401584041c200d04248000919010481c140c01e4074840080410242408060440000c1d0010903204c26900d070300020401880b6003090180d481c032100f00140000c8501401103100c42c40060020800c502c00d1803003145000301011034882c0b4005c45407204400c003c204540090b552074210700c2450210b00e100004500c01e60041c8814042e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 351386492 1250 351385242 351385253
    0x30309041109040501090218060c0304031205040602060915040602070201020f1906050a090314210406020d0509011b050708040b0316091202130902030a061104050f0f0609060306061b0109 82
    0x4140d000e1006c9034030621001d000070328000b00b40144890304440705a200e00d04411400c4c20361107240d000030200b030310412a1480c180e402c50080c0080351210703000e80701c40b50fa50303203070041e1100c608052984410320721a0008000817110b5010b0024030340181304079640c0388210309801d480c1c82d11204c41404400c8465510b8420040c103070040552106140c44203002c1e11900c0d0380d001c0c15400c4440a614480c2a000c1001c006d03052442c98560031906617064a84c80d5800d150810300020b500813401580c1c0c4509000008405010500803803803400e84803480765000301410350040720560014141240e0a031402c000000f01d40b010300b000345000d20340b080c1d203c1d00e8140b002d49018000100c40d5204a0f00821000800009a0764284040c041c41d03c0700d03a4045144082c81c130000e03007408904400109407c1c6040342c1d1220307507000c140241050340e405884200d20241a4000c20849200c040d0787c85903c21402c12180c1c0844c14618099a0480b1015003242d0400ba68114801d40d04000c0c040341407003030781d9140c5a84082c0b15 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 351387742 1250 351386492 351386501
    0x120702060a0c0e030703030503060d06021206100e0d022719150f0b030a021902060106020c030c031c0329040632030f070608010f09140f0603030904110904 68
    0x4030103042003c200101d15002c03a8a0b800c10340301c0503051010100c0001c10503280c0c5044a41140e5100c04119a591800303084035200e002d0a40f03840b4000c5031195401108103024a1025400c440010300d1000c244000d5820006030303410b070011002001d10440722507001c2c2ca00b0940b4046c020350996600c0803446440d520040100c42e00c100741036002e500709210400c8039048a08040c4250750301446203940ea680d070b60343e01101910400d844042c000c81c203200d1140b51540d0104819060314910b50030760350b810001c002099900c848a550859140d0443c9125407015600c4001410b42910f540c240850110058031a24071601c3e0a0000812800c4000a0301c081034940340c45044007900c2c1486000140d401c0c8074101c0188003c02101c0040d504c0081990703e0142d540c00c00401444001c4002181c00c0d00ba1034070b00c01812854284180140c2c04868140450391403207030b0180040d00382036003007410070954648002c000ca0380320203007201d901404100402da0007030301e860007014807240d11220020381e1428003205000855 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 351388992 1250 351387742 351387761
    0x13021e031926040b0301030809060f0a12050601021b040b030f070f031101050a0c0b0a15090c0e0d050a24050a0e0f12030703020f13080f060c071a0c120702060a 70
    0x200b0104000e0204100000c00c0d03a040d01d030016225a260000c0c0b401003211489884505990301c0f00214280111951000182210107040f0f02c042c840340d2120401a669417040c20980d002d11018a0003110b6a810a940140c0c101c20008048641207241d1000c4c441c10016260091829910f403aa020b0091040000300a108403c00b807a00c6844e010103003a00900c18a11490018a400340c10130200d001001a500201c0800140a828002da191360f540c04900820500b484103020a2503440d6243d0185001080040c2494001c1e0207000000301603941c0761000181c01c203c040c1940610001020150b0061003880d00c0ad1403180300024000c110382e06030600d00611b080c1c202c11151b0002c5c894080805a00c0c00342c2c3d80020707190034050b807214502c3d5036400080c09894200303880c0b0b0051400004020a00207000c3c0d851403207090036258103840b101003d10300d5100d615005400d0301e0301001d1500c0c40105001d01d6660001e080601c440c14555640100e0722000b4050f203407100140d00050a00490070154412003008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 351390242 1250 351388992 351389063
    0x105070c0317071e030207090908190203220b07061d030c0307020a0e10030b0636072c01121b02060105040e12090f09070206040b13021e0319 62
    0x1c1013902e41d03000f0341c1d80d0300502402c03d1a41d00c0c1c2210340c0030400032505549040d85141403030300760002d10510082d620f42000d0300910700140f8901306e009000100c1c000010075161000c044c1407403c1843e4982201400030020482c40218003008001c91495040c400761624a405101565842a00740104000c0c072403540c1101ea1440c405106001c20311f0140d00740c0c2003c0b240d110300cc0250b25650040000d040940484900c10718900d0300102c0300d0003006032496403c1048800381c14844507112050115006005009142c1c4028040f108262000b01c42000d496842c4e50145011030301d444100d4405003ea464113251404503810b05200380f2407603501813000e14094582540e040140d0540da42c00e0036039544c40400042203007200000c9090311511464065030b50071001070042459070900c0b50000b556140100c030300f9200f000c3c981004c03403d031b081841180040180c0052070100500b8580c81e90740c04e401008440c66a152107010035282594807032181141e00030b80100d524003051a460021000307a5890025028803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 351391492 1250 351390242 351390293
    0xe0610030c05090f01031b02030c0f061b0d09080c011a0f033007050303072d08180d0f140c061906081501090b0901080c0105070c031707 60
    0x115581e000d4240c3d1581801107907a420500349000060380108549100798040d136000700a00202a500007006001c0300e0b40c0b007070483e881561a010f0468035024250741d000301d546400204184540c08500c050f01000c102c0003800102080303a691200c2680d8050700d031040712a5181c28404000c2c600310200203c03d808151a00c000d05000c410000b81c41e4070030328082d00c150381d010903084522000240703080340200d130000c0c0c8036668070980b50411075901e4200b00d40c100001000b640c140d6280c00f0b01d61901e200c0e400c00c401100306440c0303034603c01650001c00007082149080d5000f610380074218002c02c501403458805881300c1106281103500100450f429584c600d480b40f00800051144c0c40780050940d9009003500c00440c449282001e007000a841a54099103103131140c0380c0040c51401c0000c1c180d60485003030250410240f8040c00602c034100c4004d12500250703410240c0000c8517540502e006100b942d104035203c1c0b02c803a40b43d075140390040c4140f4401c0c2d10302c103002141e180100003c130011060703050503000e075500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 351392742 1250 351391492 351391511
    0x1006090c08071b0302030c060703050612030708030a0c2304080d0809100914060703061d040302100e01020403060603060207032a0305162028090b0307050a0e061003 72
    0x80c9105076a10032042c442402c840d4640c20705101b401901d1107900744000741e40c080c0c10100002005400c09951440c4500d0207803240c45591400041100c0c080c0394020826030450b511101d044c40149261101482030104860602c2055480303141d22007044030000092a4071a800c01002c1d91914096524040030302030120280310954100251aa110540110300415030408a10348075960070030007003a200c0c0354803500341440310907509900f0038000d480c8400b101303901e5645c1e0035032081300b031040984018025800c070300c10b02000351807103820101040c81c4080015141c5980e80e81c4100c1203e400e075006036050755011406604241d48841d0407210f65010300700c480d080700d440300002d07820100341c140001c050010014034080603428410003041c8541d0025404070400c014001459041c00340d200c9081c0c8070320b0040f090b030a500030340e00080051910313010304d40c0d18a403402c05908000500700905255418400c501e400103440e5560111032300a05490b0b45000d010b070502005018000d1201800c080526050480c3c4a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 351393992 1250 351392742 351392747
    0x903031903020f030901020a030b010c02010f0c0c170f01051e010b0307030b040914060612120c030403120216090b09040609020a050402030a1508010608070e04080c1006090c0807 78
    0x312466000003611040385040800d00754000e204100034420481d0f40401001103900040d4083d04100300f032501d06000c4109010011105400704c41301c024081032021020b95a000e100354840d10ba00c0e486501111403c81c0c4448401c24a0000040c250344950301c20803910210303813000c0c040c0b50342020f9551100a0440200c500302940c20505001e091418000400012803407446500001c0030010302030003c01085201b070501200c0040300000426140c4a07920104050742000754403054000125030181034080040310203000c2c50b50040c0341d800036502c401e00c80400801c40008609404612a400030400900003665044506584d035201c1150700c4e150481c010250b440c0c0c000040c4e4801d6100900240c9000b1520009103946019009a038200d44040100028400340c0d5000242d046424003424540f280e07142c1000d400c0e2046c2e406220104c1d0040d40301040703005003021100d034200b131040101c1414560013820382c134078250b80050400b15882d150401004071101c5880740a01c2c4410364a400010b904c0c02c000302 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 351395242 1250 351393992 351393997
    0x41d01060503011701150f0518160c0302100c0201140c030c041401020a0c1e05030307110409080c0115061d010f050a050f1305090907080a0b06010e121b0402090303 72
    0x15031500c2c03455410403011840c4c080d03101c0c9030640c841c41c090b14509034980c403042c13581140b00c3c0a00382c02000b0300132501d00c1c2d00202c0054035104d2500d03103445419050320880100c424900007d011400d40c401c401162718801624040d9000c103000703650002405640c9807010101a04003e07000509410080061080d40d4002800b100c040d990409400280c0c000305900403803500400860144c018001074001040c01c01089204042d81c7c0c880c180410011380d01c0783d04140d1207115041004000844040800b500b904064000140450096400c1424400194041401c1d40c0b51a038040c4589203981805105581e00100d050012800ca14411003e600c540000a4080b2440711038030000d0103404246403441c1440b40080314640b51101d1141c0e629a211001029024021406258403584a03403000402500b0005000011200408002c2c2030290650301c0e10300018a005e02a103040010032019402c4075158a02c145407190b4010b001484102c591884060740e0702c280e0520a4802c82c01001070700307044d030740c004107 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 351396492 1250 351395242 351395249
    0x913080909100806090c0306010501020c03190602091801061205040f02010806060f0f0304060c0c230c0409110301050f0702030403061a040c0f02161d07020a0611041d0106050301 78
    0x1644030352512600d1500140b88119840700c80c5a100d002c1c10443c10703000214078442940b40a80c00c0b107020780d880b400160303143c4c40301495042d0150300800303501d4800c1c9070b040340c6000920302815005280c50248000f10b00f142c1c546005481d02d00710030300c0c0100800c0343d2261405100071503003400ec201908155446c03c2d0366001c8140b010b810402100c000c107141d603550300100c50001208007031550b514015004845580d410448d4141d0303100d4907180320700c2080d6004410f41a2440d6001001030665244250841c0884c15026030801052003030034240070090311349100328858280642030400c68071400c0c10800d4295100107140e00900303025a814000100c5e0000140c0741925401080843c0c1c00c40000c040d0220460200d100960003414154050b010b25044a0f510450030320690a1f42c41412104410803410400343c420070001d00c402c00903039000b801c40705880c1d0380c1069091041d20140d40c003c2c1c40d52010798040d100080b5800200140801c118844035120701448102c94981500a614000011703061780414030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 351397742 1250 351396492 351396499
    0x50708030c1b0f01060f08030c0606100905040203010e010e13050d030e010e1519050f15030309032e18080c190309060306081912030f02120609130809 66
    0x1c90304400e51418110781c6a01c681d0008403038082074503e0459020340100e1242000c1038072010b00100b6488400701c22101d05000e8040203000c1a101c01d818000109803480c01c20042004511007c42c0c10780e2180000c0d4020004402d8051055061011900320803402820406006444101842c0082c2c000300759980c4800c0c3c42d0600003043e00d0b101c04010f02401609034003000b10300408400c00c0c0c800c00e038000c030540140440d841d980c0203281024103000440d581980e40080c0b00c1003d0300010702000d03a90383e454a510001a042d682405030311030101b0701c1c0003403500c007100300d10400c001504401158842101c410701c0c440c0c00c040c4004815003103100d88045024070043c040c050000340082400c0010404051200340036184544a500c45041c014200e83e058000c2c41e000904100001800c42000182e040d020001901d0381c071007140b80c03a5201c0603400701c4243c1001c24103445002c0c0010315120b6101404d03880310740740810001c03440e0190802122210040402c0c000254001b02003010406503c151030680c00d094 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 351398992 1250 351397742 351397747
    0x30f06290a0519170102030103111206130f2003100b060f07020307030c0602240105010f080403090f060e0301150609121a0a090302070806010501210605030a0305040e010501050708030c 81
    0x1a61425050f26650054084c00b00028003015521105500443c1201c0c010482030700c039a4902c40421010064040002d40c0a0b80440e001c208002038089000298520544c0d220100b114903035503103400508005000782c001d610401310540c0608040c400324040c10240e0000300810f00788040007403200c0c001d0071002e00e0340742d902140720001c40d01d003000340001640d000f004100c10540d071001e0095540d1803210f09840c50b01c02c2d02c220b0407900d5900106090603980305841d41c480e0910412001c88503058000c01c250100482800001609a9443e03018005419a5a14010350741e00c00402e0500750340440700606030b4110208400c0058952150445080d680b000100802d010094203244400840f03110001400c03900c21424403c80011646c00010480d109800b52804550781307180543c1c55101c02d100d030a0218202980d140508079881603d9900c21240d03010000d8040d0b01d800210785090031b1a5811408244002010700000e4409695a40180170900c0e10a24104180c0d5640d611400702404070f13544107401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 351400242 1250 351398992 351399019
    0x7060c05010902190914061003050403030609050c0403031733031014090106060f180b0a030c1704050d0507050c090c041706060a120804030f06290a05 66
    0x7034000c00302c8960000c0910030300000c44003114100d14078a03c150f900d01481c000c4401110400088002e120394002840117642028102041e030160100400c21002c142c2d603210042400b070990300c2010700600004102980310340c01d5241c046c040c1030310544000c0440040c2000c108038180c214411003010540348060000800c040c201140340b080c40d00704025031601812060b004c12601e41c1d44217250b14880340c0c846280a4442c1c4c0744a500700c80840c040e401c0019a144074048046016400c1103401b006400c004c4000d0b655900307440c1c0c07810741181c03581000207500c0d1410fa11126500c0020702e01c0131150940e0440302414140e5803240e032600e20f40400740901c1400300e5803106205081c08041640440946100130364588517400440031b0f4058051140014211a9000114400007400c0d80c8140006094004841e06040d04648200c40070b0030304803038007031301088048006030000410800c4e0074450341c07002c00c60280c032110000700700c1ea25480007881e500018550240031754501020400720b070402d03940402c04406 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 351401492 1250 351400242 351400253
    0x20307020f1903214104030204051e010609060903061a041d070b13050906040905030c0c031513140115060207090b06130e07031803020d020606040e07060c 68
    0x503640d1000c0c00c4000c0018000c0c1d450049540502d1342100039969284c003660803901d1201c240b0b4450300501507820f15501e01100c1d0304410350a0440c20f00000300c400d85c24180c0d0b9500060a8400071940e81140031040488080c2c5a54144222405454582440c00c4501e00380715004000720710901c8060040c0791242c01b01d5814428422143c0c40110b4058028021007903a00403080c10301c00c106030980018495040b00040900c290025a0f1000f032015503040036941c5000b00308400c2010140c55194480d13501c298400000d001007001f0841214080090940d1500740746c10507007002d820700800041e1041c00020001030b1041203074040c00455008402810918128200301c0c01401a8048051800e1714070f50040f410b150001601022518007413418400e50115006101d80c80c01054800c800b6030881d004244803410603c1d03816035001000f443d001485441c2c0702c103460502440d8102c141c0258101c007842034036140e410b01c00d41e81e0120043c4d505004026209184658584291152000700115800702d00f04000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 351402742 1250 351401492 351401539
    0x604051503130b070e21031803010204090c110c03060103120c240207050c0f0109270218040e0c09150a0506071208130302030706020d0e0f01050a0c020307020f 70
    0x190410107070449440c08010141060602422146c850408000b403d422080c1030000300c1c825004d100055420414034030440c50200381110740060f031654090101142c5441e0511030f1900108590f40c0d440c041914518582d0305080c0f20503400e41c06600714500610110301c00c680c901c0c081c0b4095180c042c00d14145d500b04102c54100c01030118450f9180300441411450154024002080c050320644802c0c942c2001007164116100d45598041032210307208100d034a500400c41e991540200d61158410000c01d00820203d03403006c0e0030060702c6a41d50a0048042c100343c800c400380000e03140c0060880c00000070004400c04001401056030009821390850b00b0780383c00885800030f10000c0c4c00703252210b455184c5450f00e07031200e07108440014400000036580b1000030041d1a00c11b9015000f66251810790340b5040080d6102e2030038580403a03161056008944010441c6443c06440f1000001c0d560134502603120075a50440c0310741c01158070500c02040540e4882021030880c000491703800c903041550401c0443c061 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 351403992 1250 351402742 351402781
    0x10e0316061503150b090f040201110304090f02070605010506090f060901050f03100602010c0816120b030a031701050d0c0b09010c08070b04020a0f081005040c21110604051503 77
    0x607042e22000410410001c1c2c02c50301c4e800e008042030062509040600440b035404a8050301502036070703004074002d54043c100c0d03005a10b012500384c900e010b45030703c0e0200980b0034a10705012075660018402081c081a442078a0142004a644602c5c00b0f408000084d05121a01c241910130349000848044580c025800c4611400c4040340f035075180d241031180c0c81c40c01180c600c1140059402d00303681102941c81203139031030720404840040a40c0c82c0b581100840b024403408cd00e80450a945200c0205140c1c2d04010302c44130702c0d07c03039692481400c10100e209900d541040e03004a01030484070322502c000440550700705080e240c001d1107054a4018078401269400704030350010b810200005420000d11401658a0744242e00a0303070110b0000c1e64400d00d4000412403071190762050340140d9040d403001001ca0b0480d64202e4050031072406a1510b03034021480031546800141c4610915030071034000c06c12041c2050046050854001e41424902404101c181880740c0d00d0080280300000015000c0c903211030701c07500c174 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 351405242 1250 351403992 351404021
    0x105091e1315080705101803020603040803190501050303070b060f0603040c03061103040803060f01120c0504061d01050909040321020405030f06101701020c0105160f02010e031606 79
    0x70805035940c28004041082d0b00b411a00307802c01e80030450000018041c02194030141003c0d00d60707000c141d003c481c0c01c191031400c90702180d02005c000015941c1e100180d8026405042a2075481c1031000803a1400307401265401c1503582884010000c543d404070a40d14060341010703155802d03644140c0061900040d03807003c1a8081e9000c03092209104a1010b2442942d1140a00f0403511070f4503940e0116901003160001c1a1240800009106003025003c4a543e07270302c10b040c03280c0000b440c0842101a50040c0301c285001442c082420440300c0d922200c2c00840c240100e0301d07101c0006600d40000d0252003903003245405242a41c0225003007501c00c004491200d10350107000c841044100900c44c001c0e41c080d22a0612a106510048d001c0110211725140034590480320a1203403850300420602c1d9141080110368903560078491110303030000030b000342031240f0032070a902c661100b040c2d80d01901c0000c4541000f402c682c13520207502d030000c1000045408402c01c0788092611202c0f903281c5800500704140d0400303070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 351406492 1250 351405242 351405259
    0x190e062e0f08060c0301050901030f06142e240908010e01091505060306060f12160812030f070509060904090b0601080108031204080a020a020d21030b0105091e 70
    0x181e51200300c0541c0141d035400c074151411500e032000e10381405d000a0242c0356004c031240c0010000110250b001000151186502194416112101b440006001c4403640d0b040c9840d03510610b055a01c2841708044082a401d03c0500a8140150907054600800440051400b20351412144500034014040100301c154000e2001d024101e5440f400b0300b006880c100c685400d4040a080c0d102250300800d486070030060003d003115600c1a08102c018600c01300411f800c0000c51680454169040c01a1042100345410046885144c016014a44020a4042e071188081881071040c94007400e00200e401550502d803440e11a552100040c805214880b100c6600503e42042c00b800c004451000921a0400f62501d822982c0c0e075520254072071150050200c11a00d440c0300040000b002c540c040c4c00500228411036001c034030300b43d01048410b07000c01810366000c0c50302c1182d480781c8441f0701c0583d21280000c4c6421701009410ba00041c22500a000c1c103940f04404009240c038143c0c00d500204005914010650f84 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 351407742 1250 351406492 351406499
    0x9180d03020d05070302031303030f110d050906070507030206071112030a05090d05040f091a09012d05090606030601030905030d23040809090405070906030308190e062e 74
    0x4000354800c20302d00c200c032410500000c080714040c1c0300b943e105101005034114680900d6400706c000b80030445441c01680e81d611070b5100020718110244c110020300030b80014040c00d1118038180762100080040c4200001003180c1170000343e0224041d5007190483c20011102c58005801d03609101803594003428074503012007044000030aa4000d20b00500141c0190f64080c0003c1104035a94400c0d40210100c0c240c10000030040ca001560040c400890030301100f45a0f2103000340011040c403c03c2c4d00841448000040049003000e84000402c40300a5564030840201d2411000c40c001d40f034010050f5206290100001d00d499020b60483c482c803951000035a0350301e030305441401c0000c20170b40c03812810110702d041c10121607200400156003d03a40164000703043c9901c1c8010010300050041080b5881d02404200044002c3c080c0900400385100e0f48643c9558540201441c4002e0581101440c0b41414105190383c00b032404290540c0058000340a200402036129240c84044524103c03c04011310185001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 351408992 1250 351407742 351407747
    0x907020109060903030c0806010c1709040207020301060801090519050d2f07061202040803030f13080403060515040b090118020912151b161110090305010f0207050c09180d 75
    0x200d106d000151a691061f0b207504004550746555000c0c01480c0701d20182501d600009294094600540f0060002d880d042c1c41c3c0d8003184c02d5a65a03403103c42c0e43d84d190b80d4020101312062142d9280280b541d484200609225121281e86000b485d54280c14482c1041020034004080c007a0040f222144500800002c0d001129050341c1d012203124200c001030f0706d240c8591803409580200d07011691120300a50035a1038a41f1070380b400d540058130784110f04103041e030f12100064001c1c010b4002540035680c005418070300aa07c4c1000762071000c034600d2090303251000603006540c0d203805503419221301c640c1d0b111050500240540080c41180c03410341e40322018100541014800045034015900c00344121191a01c440c40201c540c0c60000440d40184107041c071000e8880c0c9101c5c55081c000c02d006503c40d40140e00d0a03170200d070581e04079080a01c00140b1010382842403150034002e5407020f0300644011407610100f0386a881e152000e0340001489000c1150100c0c00242195240b2858822000c007030320050000d00501 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 351410242 1250 351408992 351409001
    0x40b07110103180f170405031506090c0720190f05130b22090b01060507030f0e030c0409080708030c0d06060309020f061b060106020d02010f0515090702010906090303 73
    0x6032030001e428840104104514050000001c1d0b90000f04000214603e90303601110107400208810500414400050160b50401081034140d0000e941c210f1141040f13400c0c80301c0d03900024400e0400050420480001035070b0b085406c0ca1a80880240c00200800341c40001d031440311003607030a20402a0404085852490114130504454044454084045203080200152000541141d500101d00c01805507406400180170b9141041c80c000060100c1c40f0b80e440304d0320f450081c0c02507000580081202000c05420542068121009003001401c0c0d0009500081c1d5600414444030701480c2c03154600e408002e0920191012994805c1006e501e03881c1c01000c0d034000b81c02003140c0310b200c103003000070003e0103901074810711030840c0e00603023021001070710002032005591207640960069070320001c5c0500c09000c20b100c0d4a000e040f050340a00300005640c40d000342901d111941c0048128900f00c10f128884071164018407424005032041e4a06035201c0e582a401005921805040c1c2030070b090f035900800d07600d03038407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 351411492 1250 351410242 351410273
    0x152502032e2d0e03030103031d0a0b0d0902010504030f03020a03170f24030607110d0905030a0f03090b13170d0210020318070f170610060c020402040b07 67
    0x4811050348030700c21416a460b0030803941a080060310b8007641d03120960b2440154a54405010411404940751949568000d034000c3c0c0000d48541c100c002d0010414804008052048460542943c200f0b40ba50b180351040c0614842200d594035070600c116402079080e83c0081d030700102142e080410300d01b8080c0d200c29010134100c00041102607036150300c403643c200581c0140503941202865940740d450107140300c4018070400486000d445403640f91542c0030808144601c40580d140e41c40e04498141062609100749580e5041c4032100307000307011a4400051002c28142c115444038400302c1e40b41029a05021242c01898031601c000403500c8030802c0c85040340c0111500d0000210850024a41c03140d06c441809402c6001038000070741c10800c50749a0307005150006ea400d940c2c1c02192844120540c0b8220b03642d03000701450404400c081201c02c0b030010a1f44a0100b025000d0710343c0340b41002c8030b00340064450055406200b5104003d1055450310b50582d4042c01c142c245c8247e448800e800c103140f00d45820366 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 351412742 1250 351411492 351411553
    0xd050c030124050f0d060c020a0b0610021c230415210905100e06040c05091e0403020c1e0a0609120f021302031008010b15250203 57
    0x6a56000c090b0440e101c194000c01010354021030b10341458104084402000e40e203d9204046090180c0850503900c00c0401289858004215540c000e152200076008000c120512664040110290040c0c0224000e04544061024030b0301e00441c2c00300a803168040c941085640d00c0c0e008803200200b1822000503c2500d5080b200031943ca04003120441d914642c3c2580744000300d0100341e006403844a641c002a1a0510980984414111034a10103040f1159410005c4041d40700000740410300c19583d003460040d000940b190100c2e454500d084404401c400407803130f181100080000f400385031003408100c1c40300320020981100380c0752880b5000e01b80c0410032910ba12410760b10100280b00340c0641c141404881c014110b03074501d09055110070540f0b23001130600780d0700a040c1300b170040511402440114818140d141c05140a107050900041c21078003000704a81c040c4940c00780403010314461000b9079450183c11460404c147c2c1c615202c0c0b4400650711840250184a1408078001103090300b40080841d01302031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 351413992 1250 351412742 351412751
    0x60e01030c0b040b0a05090307051c030801050303030907060f1b0b040b150f120307020604030b01030c08010207030806061b060a0218010c080f0906070b0c12130506060f0a03020d050c0301 82
    0x20240c002c070b544550302c51809810020802c2a007581d01580103403185600050070b444005545401013a003805170200040303071420300c0405030740806400c201014058182600114198980000201d42c1d5052317900405041c00100e541c2c0d250b00718807680d82440390050000000140b90860300d021036040c00c06035001c94011003d6800030f030b09041c01d1070000c0070040c1e005043d20328403289401405020007002080c02e00c3c9020403c18a00982c83c0c0b41c2c02000118031441503101c81b5031541c103014400721016040707400641d00401005000c680d0007100550030160880d01c0580d10414000c03030220754030390b642d250701040c00380380304010064810307a025040000d180384280000c40b0f0143c0044030b400492401c004d0003038005001081220360080080c0109907c00380c0998505007040d00c1d8080c00510444058075411000201040181d000e40b070030740c0d00200421068501e8a8956451039100c00c4020032403070040c3d01010600d105a070303c8009800045801a00c0c00096030000d0030000d84403030003081c2c402d02a6080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 351415242 1250 351413992 351413999
    0x40b131e0b010f1713061d0d2c04060312021b12030f0703091e150e010e09060301020906180f010c0c090506240a0206011403070603050415060e01030c 66
    0x4420440c802c500d9540c8820403442e10900c401e0508201401490a1500f03512170840001e0311842109880d8140c0c0043c0d4000c4000808145d1805c18214161010000880368070010301481e24000d40050000c4580301540c82040c0c000301e80242103a0b4400f62a4800d41c209481c003881d00410740800000f01048210b102400c0131060202c92a1040440003043c2d1040007680440040080031b0680d052103441e1145290740e5688040e0110000180c1d8080e0b030340c5a8101c00c1124124004154812840d02e04024541000c0040040c0c4140e002445580c02103900000140c860f41c0e00798122609030340d004000d0b68070740b003034003001c106030f10b0807803031000d0284001d008009141c0d8090000d066001d64403549860305282800c1290014001c040d0650341c100341a035a0b01c10400d1407450f0b0310f080c0303181c0f848082c81d160112a00024900303881230f880074401202c103000b0902180c07008510304091711210f00380801d45484500c0d010038040c6500350611980e501e01071001c10000a400b050078100c2e4012000d55441d9501c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 351416492 1250 351415242 351415247
    0x6040b0a0905190b0303040915030c06050c06010602011422020306400206070c0b12090114040c1505070215030f0106030209010c1106070501050f060411070f02040b131e0b01 76
    0x2034503584c0343c1c140d200b4081045017080e1500040360791901c1c02300080d82c0703590700e555402a8620a400036404100c012810381e41094081101e94010312903840240013030f20781c464001c424000050711050340c0002d8055950156001076030b1030305090381d0141c105c4050b89003a101c031010120904810400301c0005d05030694116003408403003445e46015401c6521501c841da4208201540101d0080710390103000e1781d000034642c1800d4080e106013084c0c0328400b06240341804109003100c610342d000440060684044c00041989012100181c0f1042c183e4600c4442a03038000f500c0d1070198080007580000004410138014070315a0166008034030f0020300f009140d80b9881c0540c02c1c0d008101c3d8550006e450038203071070082590841400e1042101030075851a1401c140c8616095840485200b803840443c5018003100b410144250003498041015140c2080060780c0c8100c0b4004003050702a00c25500c4607645400b0355100c1084c40c0000029400400481b07100300e003c0600c1c064508128049a881e14070035480a50 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 351417742 1250 351416492 351416501
    0x503071710051e04030302090a090932070b070b06010518060906040302041811030d08010e060f0a0e09070501110a170f0a020f07062606040b0a090519 66
    0x29820081c040d0a039540c01c044004050051a00010040c070f4460015032044100c03480c0e010700e0095a015a41c1c501003400c1c031400040f540d00c903056051030140c004e8003040302c0380340260842d100d551850848454001440188001d0036000d40c1c4640545c00c030001d444003c5034014403000e44103103d076113403036514903005444501170180d080c4001c08d820f11040f00c0d80e01d00b0600508002c04001c025a041c580c681e0085001c80380b003002580708040b01000b4607001d00c0300e017501042e2082401c030014000d1102c4100014881b003030602c90415a21403070004030715540d44840c1ca140140358080d2500c2903081d65441c5090608205640105840c094010302141d5948251848514451050000c045900a0f90340301e40035241c14403928000d221040c05000309241c1484e00400c02d00e402ca50040481c240c1440c125030030000c4070f81c0800140020702010b0840c42512581060240107510f4034000c0668a03100400c002e032010403131650b4842c11081e4003081c81d18640e0300a5014851b556020a1a02c5204600030201c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 351418992 1250 351417742 351417779
    0xe0f1f0c090e0703020a0314070c05120c030a0c06110c07030615030f1101021002040906050109082d252102031c090305070e0603150105010c030c052104050307 70
    0xda04400002c0c3d1514000e0b00100329000e054030740001c105040304260680c40c2c0e4240c9100e000100a0190f0b030080c050204140c03c50781039814032042c03034040c60304019a40c3c7d201e10b4480700180517152000c80c043c00340541c07140050642c1485281e980b1043c105401c3c2c2c4940d40d1380070842c3c4081c500b03218042000c07101c40103070042c1c0c2c0e0700100a4503181f0181c0c0314909596130420f44d41c2d0441c89082050f05071006540041c00060039000310100e4224240390024180c0980e030f400540c00c0c1e60144901a01c1640410b0301500c1100c428010310b20b040d41c582c0a40750400074020825599802054410181e120301005548122402d1245140705886440080100503180950195141d4000d800103d41c45562602e82102003103581400e1150542e0799981504046982d408103070701040751410450541414081c00490b040904002c600c0c960502c1d0010f0301004072081c001d0100480302070103d08216003040104d0381d010400b040f000041005184800560303025004150017030040d4980021003c940d82ca410410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 351420242 1250 351418992 351419009
    0x6020c0f010809030c0f16050103140a0e030f0c06060a080a2102210d0c091a180402070f020f0a0e0f0403051207021501150c060e0f1f0c09 61
    0x148440303a030044940d084050400d5005000800c12158103138002c0241c41030600b0b0b104060b200d003e941122501a0000640c8032a040c50b05024510424080098085611440c014000a80c0c5001009c0300303840c1d400b0b81e20085503940c2c2c000030b070b0100c0b01c54000f81c50f40c1f02e100112101010f036521907160944602045000070a460586881881d4014042c0300e000d600035400c0c0b049885030f01d08094900d440340c070341c1641c50601140001d50b404400c00240a100e981d50b001e81000000a843c205a11121140b60261210441c1c1301103600821803091442a0513039800061065449400e181000740c0c0800780424100e00c248030300d001207101c909006034204216008040c07428107070b0741d4110100d42180c81c014800c8082250400401e00310031180c8100c41c1c00b07090716070300922081c441d110500940340c2d8107030030151248503190100f100d031503480b407a00780649a00c075070301051000701c6110103460507052407003041ea0350003540d010203c54182181070500c2c0100400c414401210000c2d410340c1e100369240180c600 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 351421492 1250 351420242 351420259
    0xb07060b0915130f0e07030b0a051f0e070e04140f0a0b10110f030415020d05120a150f06050a021506030d0c0f081303110316090f020c0a1103060106020c 67
    0x21143c4244c0d01104080072250340204204203900704450a1006603003040340e8100e040020711122145d140b2800b5030144805c0d000d82d100404144145104900e14403c5501e4400d948001a200c0c5102d01100f41a00401410600c41c4ca5610003240302e05a000326079640d00c052001000903102402401030401c0c8200c090702c03000b00031000601c1118802c1110008110601c60003d01b1402010104020001401d0700146112050040301c3c00a0030002006001010000e05125082d1050381c58845560010907542e070014001d111507541c510034150b90343c0183ca0b86130154900003642c1c0d8000c0d00408508480c3c1d0f01783c1d00387c900c6c0e44030394950010080d5402070b0541d02c6401c0b010f50950140905c541c920340038018000d011555955581200e6100ba400138003c07100608e400c10401c40e603d002e480000c18100d01030f2030040101c0400e0413802c40c0c6071050144803900c0e010180320b007004590484c0d0604010006507000d03000e4070f003800b5070806c40219145000b44261400060424030124440e02001c0c8000d21902 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 351422742 1250 351421492 351421519
    0x1a010e0402070f0506090706081503120903012c0c09090607030b01171e070804120e0604030501060909030809071505090f18070801080c0f060f040b07060b0915 70
    0x30094000303040480360b000c600c41e00e10b000710b03100304602e03485240760b48004c054840c10044010b003190030140115001c0013400d0403420b0700380e4020640706a040030b980302c8591141d840d100024090201812482000e40c901d4460b9814070440c5207000b442003268004440095038850148040203004031034461054101c01d0208000b54400d0b002901145014940f400c40300c00c002e0041200090203403005028200d2620b6103c0741007040008043d804a10707810310300c080e8030f03043e03c03401c1c4140041803021081280748800e1108039a0f5038010b4401464215000300031040c2c46510f440000c00010b1401c0c0c01050124000031a8107400040040581d07443c0c080711310201411039400d071115004502c0e40f9900c005001201400e50b128000002006120040a5105400c00280103024224103822024a9030003480780701401d51a012424403141c0d0040d0340d0507913140c8820300002500c0c00341d50031111702c0c154000b80860900c401900502c41c4031800300c07841212502d40340d400f00004802d030241e407500040c0e00712001e03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 351423992 1250 351422742 351422749
    0x70207120219030b0f01052d010c0804090903120f020a050738160201020a091e03050105091b0f0d02061305031009051006060504050d03030608120a02011a010e 70
    0x2c0d00442d102c0a03580140b0b03403240d8550b2640320341150485488085040100302d40e1618180060501490030344039000038012002c0d12180000b07c416007414009280b0030442001004d5040b90010103180c1c00c104602480d03441c00505209c00c1c409884a0a800c0c54001c80030040b01b882190518100c580b00c1a14151a907910407484400d0720110f440c05031501c918a042c282c1c04600c00c0c214074008248145000e29159511500c80c189581c503035030071a0301c10b11014800702d0704465441c0980388903010740e9105c8a086401c0e100c100031a03400003003082d401d00c42848115500050344060001d500300a0040303540c0e50300140441818490080c5920401c1000400b001d803d0801c02000c8441028003034600e40c9482e000400d240098485142108641e140d14800c1440820700c8034082191940005028462800c0320040850280d4000c09210f20040b0400710304160090b444140240040425900e0244048180f550181c00911050303001d5424202d10541420940070407650629058641c0207a0004a0050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 351425242 1250 351423992 351424009
    0xe01031b06050a08220206220b0f34030f0810030206040501030b030c040c02010e150f0c03041103070605090111070b071e120203030601120c02280f08030a111c0203060406051011060702071202 84
    0x40c8bd408564800850380c0001c2c0701032903202c1c0e1030081c0c03070b49181200003c40090070020300510398a011407040c80188016501c00e8121801c4034024640030940030204c00019041c601524101030b0321500d080180c800464041d00311407800d40d058410f81c2c01d008600403202e0f62040d41256065421030245000400c481046006075400c54003400000c540710301120042482c040c4583c2040300411320229811049603440358514101d204510041c02016103805001d0b0054000c200d402805103d001e20a0300c20040c02210200429820032250740ca01d02c240790317019482ea4815103005000540142030314011148501415100e44000e47c004c0035592103148030303a242c0c0600d202100c0180c00c0302c11b182d44041010100342890319400b5038200e640e60704100e40c02c0b00071209000d501c0086d480c418070591820101e12180d424010380007900142c0e6980d0f4a00c0014024a42504203031360104c2c90001270701d6856401041d41c158680800c04444064403104421b0340d035050b1500c95942031103c0b21200c43d00508200c8603 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 351426492 1250 351425242 351425287
    0x60708090409110d0c1a0403030e040f140a02120f010e04030f18090e0106080703030507030c21080f0105030610030213060e01031b06050a08220206220b0f 68
    0x10b108143d4440c42c00500c083c404030702c058500c1858080c050205140614240d24021220282e20746843d01d150b8000d000320362120b18651180343d8078031001e080100281c2010718003010408994086103002d000e0f800c000d401442c0100c1c10103942000041295003440c80c614141c8483c48104180c07950345a5048980c5141000132104011b204030380c0014031200c1500602c05081840c07400b150700c80e41b06100a007140d8441e0b103e003182d07501041c002c00120f03401204681c280c503003519080d510300416040240c0f40c160b20981c00f0f40d0301c030a4140000f20083d0b208803da406031a0804085215076650341c01c05a0384e5a007690000304040c05c2d0390003040145440d80c0c5810704804103640c04241715907180303403040c00140264000d88814080a001a611400c80503c140c0908042e003460b904003c5070120060003000300818000990607076112035180c0c51070b0404819200d42c3e006040681d9010b00c4201001f814080301040180d002905a000c140070780300509450000000d09082070400243e401c105403140500074 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 351427742 1250 351426492 351426503
    0x5032d1302031e0703150c0905060a0513151b030206070509030c0405012916031101090b0a0615030e030304030e0d050303040828021b04060b0c0615060708090409 71
    0x403d641d041d510828101098070460350050004d5910350304054079603034603060a04c1005440e0561a05031660040210003e0352010f0303900a403130300510300c0f068070030348a40500900c1c14910030700b00140504034200302414480709035441315400150304a2441d0801265440200503800510004204c42c0c8250301402c0d1250707006040303800510840c404542124006e801152907410740004c0303880404008c4031000f00b0724044101c401e2401c2d02104034051a0000404010100700000c01a0f17481000250004d42079a604100084464203140c0500d00c004c15042c841d981e140520210b4a03101c8500a115288101d9200d201852075541c4540d0104c07121900104450392010102064001103902000594820742c0b03c0d10349240d66944035500044050070103403000c00c1c0b003c03100d00301c2420241d02082590000e180d41c0307a400c0e025030f456000030340a007031560005201543e001c2600c0018a00018107a80130340008055006521210030620200f0300c80c0c420003600302c0f6020064000c1606003a8004a0040d0080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 351428992 1250 351427742 351427753
    0x5060118080109020906010813080313051e010b0402070503040e09030c0a0308240d030309080f0d0b1e1809010f0f05041202060123030307021005032d130203 69
    0x80003221a4460580c004411036955440f0303107001c504045810680209003400c0110b01458010050090384d01016030040078848084040b034100c1d240c13011590703440c17175208095940c0e002c00307580c102c5000601c46410492945c00c0c00308045942c203040c400c5403e11500200510b01d05130906441181103903000d000b034100f610003007258918410741409460b551512036610f20340d01c0d061005100c4400814a00c2083d0450b16100003422b003039a805a0800480c2c0d8141000f044291560520ba0100c2c004c079011a15a41c00c000b90144081d0113990220900c110111151008802040c042070009102c1090041e00010903000213440c2040702d00d0341583c800b07072420000c1400c070381400080301607400b1102000301031074845040c04104403a040c0c2050414440d44014211507140420400d4822901761003003181c1da8074000601c40c1034500740126000c294016041707070035940c0d589030018a070760720440340a0f060014140c0b0107801c5ca180600d421074239000140200c10341b91902c00c0e20a0b500c04084c407040343c0c94402c0307 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 351430242 1250 351428992 351429017
    0x70506150108070e041e090b0403091d1617070e03010e0601080a0f050304050a0902040302130902030d0e0a0b0406050a080c04080309040507022a030c01051c050603031c0b04060503030a12050601 85
    0x29402008131f007a203c0ca01c07602e0b5a05080c50040c0c901c030101d411264840034080d10720703120080744202507030340091015884010081030360400e885821070403011214207210030b41000301254102100c010711201c250020048041c0c400c0c0d40c03640300c042c00c1c01164181d4100300c042401040c411114080003030f00500560303160681e42e6001504828503980181e11054000c5010019443c080d0750420903524401418081412941d0001c1c1e111159020700300e0500480a2403410192103020b0300c00e020f081c0d0410303000e5a450311010098241d2704035050000004519500041c05258803038150390840b1500b000540c100644501003101611008081908601c14981902c1220b184661404981108030250f0580483c1030310900d824000c100603131030b040c810100074900400018143c2928040607030440010135407034074400681144945942c011b0070040e01203002c0070194a0f5405958a5801110100522030f80c60003410307128080c0701c0c2800e003c0b9522600041209425410490340140149480e9005154 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 351431492 1250 351430242 351430301
    0x140105090604090609050415051501111603080d06060f0c080d02120424140c090d1a060405130f1203060b0a02030c06010b040e0411031002070506150108070e04 70
    0x800754400c45c0386540360824001403012100c20607890710b103490011b021500d059001c18040c001c0001c001410441c0c8030b903511003a8803082c00300204200c80a0310340f0004a46d42d081200c00c0c0d403c803030b58003400309250980c0090102d000f5003810303003d0902c0340c0702c04407001d0440d01c4024190308501504044ea50b001c2040030120401191201c1c440c91158aa1402100907880038510100110350410041c0380313860780032208a10050012940406061811070b038591900d00820481d440c1d14800405210030140c02c0d5210344018080d841c401c56041c1c40400050780c95a141d4010f1001c000800360039010341046243c003060030411030840140e014140801c4055880d6000030260744415031940040c2c1000c21030ba00c000304140440d90042601076170a502b06070504c0b0070341d80c0610000c2c00003008110903003441c51043d1014058150b041c2d02c0c0c51821512a40c00d820810348941e000c0740c007070450407610461030700558000c00c46280a00c003540d82e20001e00d200242030100810701d0f07441620341c0e1001011400600e20307 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 351432742 1250 351431492 351431501
    0xc01060e010e1006030905072c0901021c0b1207030b010306050f1302060307032d0f02040506090618041d010b3a081902070b120c0a030e3414010509060409 68
    0x18403503a001007020000c1960101c2202c001e0400b20899004100f41040c0c0cdc6808601134108203a000320003d1196240c90001e489400d0560120199004400001050288030031000d4101ca0043c5414003007a502c82e18156058101100c40f0b054494020714460094101040519400b43c518240001c00c00203c401a20f02d400c0481c116004c00d02c45c440d62054420b005001c0c100402411041c154101814500065624010ba210581c0224404100100000c44041540d21080d0f4068010080055110544c203090050349040703000302e6007800111051810021441a103c00b00c10302c180c621242c8192201603400203140c21a101703070000105180210f81848000c000380803111200301c1d4080b50f4004040d003841c036541d02025220b54280070140030084001d80040c6d01c100e908007070707590b154a402e1080c0c00409840704c001d1814418803040c2d20010113800035000c13028011010002e80340c940c2c24800d0b55500d041c2c0c050075071007040b0f00c040f400080d400b48001e0104450000d04050516444012034000c89 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 351433992 1250 351432742 351432779
    0xb09030f0106032004050c0f070309090c02010b100203120c0a0e03010e030a0306061b1b08030d06030c050f0f100c1509030f0311190e0301020c01060e010e100603090507 74
    0x420350104005038407148489056504c2c2402c0d1420b010516040540a01030301a8003540d0300c51200005080003058420440c00c805403178224410841c44019450007070003404c00b1541d0343e001d09489880300c08114000000d85d220f51080e5565a0120303a02d8003280358147e0007902e005002d0101c20f59030900d0a070360a000e4040c0d034032034203001952070300c14115009051f944254010010b0082144100c10b158000c4400002c4882d0403d11011004a10002d0035130041c1466001001c9800003103442050301d00c55800c580126402a9199030f0903507200c500300f1503000d586002c0d10340d100001c20142c68043c1001a6144031040c454105400d000b0b5003600c03440250702c401007030284410f42e100380140416800500031441c00b1030390300e0104041507040810700301c54403909a084e13030544034403000000740341c1c45035140e000264000390003035482d0308005100501a000c07a00407024504002d400201c0c0442001e00150b110b100070360308101409150050581c000e0040d00c409907414040d0341c202082030700c410301183d00790 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 351435242 1250 351433992 351434003
    0x8160b0706090c080111071109131101090e0403020307050d02010b030c09090c0405130302060a02070206090108060a0305030a20010c0801030213110a2105010303021b0301020c06011e060e0a0b09030f010603 90
    0x5d40300b0a00c0c0a00c0404012405a88104400420302458010f01e0001c1500d044c5c0c4200340a0040640c400141e40d02c0e18dd580c40756002c426207004110804d503002c0090524144158111080303407142000c00d0b03080c2c4d160301141c190583d2104485040340d1400d050f5460300003030148259074018280101042c1a28012542c007080300d400120f0308400c055040281c030742c1c4500306030f42c2103042403c01c0d070000e102880791100c06e9042002003004a80280d813074410500096a2241c02c0b65560201c20f200074010900c82080040705080c003440f4180e4085041c0104644000140e03110415030b0300310303400c0140c60101d03c2c0c84030b10100c1c0c2e900b0044070408440c0300244643c5486456001000d119040a581c49141000408610a08041c01000000d030009503031041030800c2d0f0f540940070401500400c4c02805101158821132240c0c500000e282c2014508451103000c1c0c503814902803588a83c0180c0b00c18001101c80c0390000042103007000614440e00162141c83e400806803000b42502054850a5505c01d8000743d56 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 351436492 1250 351435242 351435247
    0x2b03110705070501270b0d02090310060510080f070f050415090f090b0f0112020f030109060e0106050304260f0a0e09060d1703090a0f05060108160b0706090c080111 72
    0xe5178200c11900c00005c0e2601e42d2114903c48140c907a01044c0e0341c0c0c8110900c0e0240401c0001401200340c0641d0300d4008c018080b200c00070110805800075040c28030802c0c2c025082a0202d05880f0300c02e05003644100382100900c0e880b5202d20000b2900d031b14005442001f000020301c0301084515000e2800c1a28981603501e00d030606091110148017400c540e400b1030260f03894100f03051079503200c1c030031204943c030700908050300c0c00c0b902c1e80500000b07031041c009880d415120020010038403418551200e82a00c2d00d04420042d203030780350001520284010394019248100c0440700491002c031041010621691140f0f1503420710040403021220b940181200c000818a200391143c1541802079802350300c4042200c0015120080d030b1680b001c20b00b0111402c003c40354000000030380b5017800300b120b5142c0c40c0c3d120040b044000341904140e900d541081c09401c4070381c0070704403494629110400c0f411090f910120a25458105c2c265503110040c001c0d81c2040f03d40c11030b2104009021780d0700b841002c3c5078103400d05041d035 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 351437742 1250 351436492 351436499
    0x3090509101a03090d0804060b060f07050f030310090504020d15021b240a0207020a0608040b0903031b0a03090606290301060203040611030409110a08092b0311070507 73
    0x100c040600d81d400c0c18079400503c10404090000501c00c4850041414245440c2e141c3e42000409008090500d5400000001c2c0000c42044030800500a050040c4169452212081290f079100c0c030056401105a020b0280107004650301d030786c0903503007051000385400b250066a544100c02040c92600f01d541556020400b10640e410400204a1b10f0661002515100300e00020300807141c800752101a00d041d5400340041c402220b0f950440382500d1b001002050940d0ba12000245180d2007113a080782c3c2e8507800e00115460110010589010381008516445042040440165543c100c1c0c00c009041548036407402c004100144500c0003d0900d04d1020f00e8181742c500d45952034940501168940d0030810401000056400301c1030f01e050301c01a03d8441e64100e40b03034034032524600840e04155004ca2420100705201c4039804000c00104070141c9801100356121800261a00300c05010342c120310768140d46440034040c4803c0079515001d103a00300010802402c40d4000265000400f0458981d03001640a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 351438848 1106 351437742 351437759
    0x2031509010510110c150304030f1b08090105122e03052e0f0b0405130b01031416030809010831020109231c05060c070309050910 57
    0x6c10450302010301c0d00d20350781c02070fa01100410540c4500000081c0909131b003050094212004003811000342d15588819405045824100841004113078090460f41510341c0c01854a841c0c081e1920f00c0b0958200c890600c1501c0000c049900d00e1030400000e039000030140800a01c8214585401e80003074908011820301081c0304d60603504021000544c9603e60344030042500c000c4905014944a012140318041482c3d440905058103080062011482000c507100c2a030080c80c0c203c41a0900710b01d90828210041d4004940c91100052510b11542e40842119001031040e001d0004008042c42040c0030a5948444000404140440102568003d110b0b0400801c02c801001500c42d048400840807900443d5038140301d11060b00181c000f030036682d540101d16a80c46002050720340c1352444122940d400401d800c0f0204560840701007917685502000b113001e00e151000d13955030300c4d00301541c5 = true := by decide +kernel

theorem cover : BRFrame.Cov 351258992 351438848 := by
  have h0 := BRFrame.cov_init 351258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 351258992 ≤ n) (h2 : n < 351438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
