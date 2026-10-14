-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2262
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:10:30.946653+00:00
-- url     : https://prove2.me/submissions/9b8e4b69-3959-4eb8-afd7-8f0adb5e4987

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 406654676 ≤ n < 406834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 406655926 1250 406654676 406654681
    0x509090c03040b0f0c04050a0303080619260a201302040810020912070b0417060f0114010c02040c090306051b0a0c03050d11091c050d1101061a120f 65
    0x3044600031aa000c40a15210102c64880000f11035046c022508841d8006d82c000e1004800c3c9904080118442e44045607482c2c06600106604040301c940f52042100c0d07200012044010325483d0300d000032020700084101d540800442c2c4a6203e08072003000c1c130035103800381c0c801c9020460900b112702006a502400307096103424039001d056a914015215403030101503001c1103000c0c0607601d170440945202030000c203c5051589400b113811266000340701d414604141d8010f00030031240049115481040742000ca15503071382c41c3c4019103036621030740c1074054104461415540b005948611580780d0030310417030b80c6000c0100c1c01c40c504a41141c0300235200c00791110f0224001c00d4080c0e80d0743d044034100c9000307190491111042c0d1409881d1030040200d4440550305103405031411401c8d41c40a05408601203800850340040301d0b0000d010044810005051500400d1b810b8454900035904860300142070000014041c3d13854078014a04e90782d020305015130400005070051a42c00d00c2c281142c100780680061103450 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 406657176 1250 406655926 406655933
    0x4090c02010902030c041d1014100506030412180e22020a03020f12100203240312090f060304060507081602191401020c0d02101509050a0e0a030509090c0304 69
    0x39172603105c40b2071140303071140c15402c1114013408102c500550030200701c55200031240c0740b0601600d2241503500e11080410002100390b82c03803982c00310446a02038181d030700d507450780e4950071034002020b1806001d010620510040701500e064944000b800b0344000440c06007401ca510a90114500c8074081d540e9042000210269031354041e07500c01c81e603048601a4030141340001164403131001d22007541050041c00040041d204007500290300c1703041101840c800d4294a041e0146007a00029050307901588289001c107070218911b0300030601e00d9801442c144018001400190440d44100c60032103180ba1660144002650003004054110b5614034050000b401d04050003940d5191952440d00404490140130044c00b031003403040c010050b0707800001e640e281500c0060b00e98501000c4c4414006106113451450051003a220340e0104e0010300700061115480c011103032015200260111041a595001682d10a8000c00c0b8008a043c400e40760240c54401e03070740c204000203000a1410036121410030811002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 406658426 1250 406657176 406657183
    0x90f030801150e21010b1c02090c07050606040b04020f0711041b14070809092502061b070206040503160e0703060e072d03060f1208070b0a090f0804090c0201090203 72
    0xa8074000c49441c03521002220078178054680d80c846a900a2818a00c041c1c80034103c90078508840c1c000c2e6130542142c0c451b00c000c004144551440504550003400c0414480d1032b294000120039003000f48050b0802c14a55441341c00c1e980f00c16000c5503040d19041e03100001c2e09242c007170703001590081c0c480543c964800d10341c0a007120030442d010032201d10780001d031201003048500a03220a072700d01400485981c07600300d402c080ca421060300080608015000602d58035440000c01d540b00b0383d580a00c8000c584030b00544c540d415001190101d0f0f1002c03040c0004201c507141000424032000020000d0b82d0a2486c0ca0201402407030007238981d0041604081003800000c11308011181c200c182d601e400341061a00e2505038407241448441c03010f011400c41054540f096250b00704005503019881504440e5540d00c034030702c5003454075840050451800344566030104036400415503011000d2000032952232030702d581b103000f20251454112035241000ca81804462298030400702690400d000810079a222134000070b95 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 406659676 1250 406658426 406658449
    0xf030708040309030f0c0518070f0e0a08010513021005090109030f0f12030506030d0e030607050309030d06030c21111005040515070b0708040f1203090f030801150e 72
    0x103100401012404040c4a682030700021030b00310f02030040e4a0304510780407840700081d00c1128031a102c4c60301c4c0720140348110501103000c1d003540c5c0c03075543e000800d0754801c2d60b103541c0c21100190310962401000804034030a02500f8412100580b6a846d111494410081d90000c03100c0c1d500c04005041c002030700141d80140120043d80d0b0040d030540301003242880d0000c101b40117464000c01c10710300652040c02258150300654081c0c20b088094035007010796110222074840380b5a00380d95040d4412030101718460f000304021a00502c826090300c1c42c05014964150554540c0d030300495021050280800100c43c00019440105000c48528645404541c4131078a0200012082d0b0380300f140604000c420040c02130045400904001e040740340b4651486d0208405504811400e80e48548950300144400d40f01d0880540300780e074090409025440343e07450f903102001c030382d03001030701450f68600b011400310355950206080c151103a580d83d034066040010003000c23030742d4403004041442000c0040c80001d80c1c5141e180f40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 406660926 1250 406659676 406659691
    0x40e0703050604110d06320f040e0f0706030c0302030108030a2a110f01050306060a0e1522081207062708030901060509040c0608070c1205090f04020f03 67
    0x1402e8035050006401480111843c2c0e41400380000e44040d5540180c00a40454142d01184d05000d0503451405401a148602c944090880800c24007410303e030051903020070050160001401d00c3c000141107191194003144600c040d0321600c0c0821969038513004d1000c12030140d11b0154215450440f40da585c0b8080c9240003820b026500d0070800f4801032581e44484040b84d0b1001c071110700320150130103040401d070b600300c454043d240494502200e54010003c49000310360140c88949000a110350403900b00620100d080e60214000f190107425414101c050300c030140c0000314945089190070485101c00c2c0702a44500c08030b40144a0390005607100030140e5070440d4100701c02003000b0300b100d5040d882c80b00c0744440071040d400c3c132030a0300018003a0080181d071007030714000020040b26444100b00b00500c202200c0040200c0700700b20081c8a100d100301101c41c1c1001c114140000d0026090381c1d1001030b4401d8038403203000200045010300407850485e070300ba66004c0054a085241c004c09040030102c42c8402003510 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 406662176 1250 406660926 406660931
    0x2502101e030603350a0909110c0c0d0c03050607081602150a0f0f050a15080703020603220b0702030a02070614121305150f01140a2312010e060c040e0703 67
    0x81c0f81c04c07003010300440118031032010200d64940c8011000f44c4a540c9502880ca040c6141c40080350803181e0b990200d070442c00c1840d00400340c1c83c11400401c0f413403403032080c41213980620600d030000c0021000c0040501480c015140d03907005282c801410110b1500a1385442c046510600c003070710219294000064105050345000b107844c2c134034482c90f1406400a9214840014607020404c254018513a00164244489a205400a50f96040c90710b035503020501000c2c2d070000c0c080001c511813043c0b84426005001040a01d404495412307280d511002d54103c03410000b61b0030020320f81d00c49982c14052500903080504018102075103507485841e00340140d20758411821300000c003042c00e409a014a00b40b016138000300720740e040202491080400d14055903821000c89580c0c0021488001c80f051440c52420702821541e00740745400300f1080e03d1801910750000d4035200d00b412805686030096402d24480041c0004100009030410f030703500d0701d0340007005003203060b40c00e100c103024a03240040e004c1d82000183c03801 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 406663426 1250 406662176 406662233
    0x81312050f160f0c080615040b0a03050109060e010501060507050309040504050705120a03081311090408091507210807081b270f062502101e030603 65
    0x40098403802411005032105071008800304071906a0f1850b0b07040c07003080554542e50742c45000c156544804d881094071501c1c035014228880c03c1c00d9010030b400c268001e14154000741c0c0e9490b00c50840707100c0c1e107090710480e8581c080900e80071024002e05004115a03c1d28500c0c000c1130781c035040d40700e000314601544129107c102103801d0010400200010b00002085400907101c0f003003000d0341d1032840ca08218081030700030002039000c0654000c8a010a41c2014454515419001c20459441d000403c104ca40243c1404403103055120807406a10700c0034945500d40e80c0b02c1003400c159400502c3c0c0050360b4800c0d68024501d0450035032242030180c01c60220700b0042070b1a00d544403d181041011407040d64060030102d00103c00e40c417542804801002c1c139003968000c2d10a1902405054070340381007001e800c0700d010041c54410340c2604004d41d2507003a042c0d80d201d45c1a0758503030002e42e50862007010240080d0a401d462130020445111180b00c2c0b04290034100b0110b8a981c2c0c0301380043d03d0007101c02c0300344602c2c50b21 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 406664676 1250 406663426 406663447
    0xc07020d060905030c0303070905010201061421030c1014061f09080a080405090906240126060306010b07050a0f0807020a15090605030417070c080102071208131205 72
    0x740c2c811a0380701055940721010300028a91300c0e0011030b0001c1c0000c2421400044c0c40d401881200292200d0800703e49405c06500b06010162001840700703807a25003131a035681d6140001b44041c1c082000c081c00035054171595581c0ba030045d120001d4803002c40c8001c0c030052054540d11496015001349034101c0190207442c8880303043d46c3e11000740d4801c265901402051008110701000104282c0b002142c003043c89803030b6013038240d40c1c400c804c680c2c540d450780d03400290352403901c0320342619040c4010516000c16285403208182034900040c80c1464140924401403088628080c04070501409001c2c00d240d0a040c002d44410b81d6a25415070081c00f1a1010a110b6040c40190012680e404e40c020308900d00156540c161041000306e4290f00800140b071842021400600c82e004a9008503000049075420010203117940ca40e82c0d00c4641c0848010407030071000625503100f800649901405000503507940380144c50060600c600082014030503820310740241d0005407891000b4402c5941c5407406c95145c4a0054 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 406665926 1250 406664676 406664681
    0x10f0201051006230301030b06090a0e1b0f060c071508071d15070f03140f0403170c0a0c09390e04090507031103010504031d01122901080c07020d06 65
    0x2c11301203c030310000c0048248486030301030501540096524a00c02c0c0d07540d040790f9003160690f41141c2016000030b140e0a0300c1c101081d041d1107820500400800c1d40010030030016146a001c030080d14116040840100060010720210300d46800c0386091107191460251320091959141803031a01000094402d05015519046482c40c460740e120707004250b03542c845040c080f0f04c03403440d4401140042c41910510024a2006082c0ca400b1140d4034420b44c140b5003181d442944405410518808000043c025561042801c100c0e550403580240420034500342002e11107000e9506411652000090f280d402c44c060803820000380780c0c2014400c13102e8661691030141181c603120072985559025051007801803e002c0c0110b2690100c0b845441c83c1d075400358014042c0b6081e00e4007202c026001c507414806050ba91301d00e50f43c210760850700500d8030a900b00e1000d680705080703441210950759084040400311201040111242d200b541090901c80203074940007191200300e01c40c00400078050320542076400c04000c2641c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 406667176 1250 406665926 406665977
    0x1206190f060506030703092015030901140c1b0d08010e1005030d0f0314100308180406060309110103060e070c06021c1509060b310b09010f0201051006 66
    0x700708a80d81d0905c180c006028000c5c107082961510694120301b200e020715408402e01c58400036280d80300c0344040288d060420780000348102941c0d5290841030812511240d9114450540c0e0200360f92103034001055000b00c0443c05400020f1640444c210910590f0440c0c901811103030607505002c40d603a5a40301c40c0456400990045402d40319901c1c00e104401e401040040700021227030741c00c03c81110700c1800f0b034040b404140e41d10f441d0f0700c40200e070520120303080f20005e1081c0b508900b40480d12180321400718044075003560050780000e6841581204005036007042d42400e07282443e062188d9405c042032101e0005000c0d16260a116101c80c17081c0800c106a0161194030201d41c01c081c46800030b080111002d464100542c40d4400446000420010485d11034401a41e00501038141402ca0541c030440f20071041d00c50b000181c0c1603500b003070a6181f2041e0310302000b5000d0079915a841c4c188100014021200c004803000c11340e41000c2c200000c080071030402d18103c996600e001c0c0b0344254441101c0c8408801d6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 406668426 1250 406667176 406667179
    0x70e090601110f010204090b06160303020901091703070c050603091e0a0212010b030721060b0f041503060f060602061605190f022a0111011e0b1206190f0605 69
    0x80055400f51a80e0640c0640100c44a0000611a82c6081d9040081520a1078640b284229030aa41440801c0c0700b81c3c040e100c010070605150040d03984900544001c45004842003149910000b01c0ca001c21451605182c003e10080e50440e0640c10301d280c400f0b403100300a00c1c0c0c11b0354106000d030103281c042000300028038100b44c0240034408080124285107001e0a1a060118000d1150350307400503208c10918244491042d40b90080c0060465558900014100c042070301039000343d04c0d0881c2e00c22940c861042d005103002c80711615551a1451030071005680003140403607682441c15001b00081500400e01c3c5902c284002000c000203850030a06482034011100c6d400d020401c3c810504201075017240041c10f0074805602165007280700004040040c07210544100d028030500b10a42c0d005500a144541c2407407a117000103d51a2120f414018072641c51001e1000042e484800442c5a0b0610b2034009980303441110203041a494288528144680200410700c1c41c2c60352080c4005001d00b04d42c0c00080035040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 406669676 1250 406668426 406668433
    0x12020904022e0914030d1d03010204090e0c030c060c0307030c061407021609020a0921150b0108060307030f02062d030403020d0809100207030509030303040803041406070e09060111 79
    0x608040144402414003413149212128a00d412440c580026062801802c0380d45c1c070400c910780341c00740c800c110f100f00d001a80c040d13400380400703d568011402060800207c1000801805880000701403910103a641402c0c00f60780d0405c1091140d800c007100701c401140d01400c2041c81493390b850071100034000d680e1045c0d200e645540502079019400715110340d42c400194000e01121344c03180c00c1e43c8101c1c4180c02088010071401d440400c0030300c0e0025a0000c64224880b000d030148180c9441e00f04000c0d000000ca00b05d07041da600340312100781d0b8108400580100041d0000c103032550566a031038036604003082001e0700c10b440110703a017168540b490484201c000e0610320341e03111607145a40394600580060350100c02500411036120300b107512503810240700d02c6c40075005104000c200700d034000007903000c0384080d410010200003109a98070200001c500130391041e450255a40b4160420304620382c8201c0907045580c11202c1808006640480e4070300c02040b00f15051501130b1a240010388100d0408a5911074901 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 406670926 1250 406669676 406669759
    0x204030605190b10030b0315010b0a091d010605070807080406030203011703090108010b1605031b010b010203070308280e0a03110a05070306020706140c0a02071202090402 75
    0x2400d9002140a00c0c901c0c06014011048005000c1c159045100103640258840302000d078036600c0783c3c206403072086000e0180c488a840702c000c403450a0800740c2001d0704080c000106403000541c0180028020400300f12101a02082d95050385a101410303c245000c2101c00b18417441400f50b2003007106c50256110030030958840d540c25001c1d0203074109100f102080400d1425002c451480441113440c20030050391900301681c28040e04003043e400036960641c82280e9040351f0070004000300000e00ca01d0b040c4640c900310410080c2e680034251404840e0503411500709120880019030001c0e202c40e0001c2020190701e98000300c04a0035441007440312542c0c0c4070103003005102c6e941c10101060482e034072030007540c1f080914480c01d0314555581001840080c07050348082800c2020903405d602410310544220300114030046400701d0740580010955030003801240005030110784a404200c0840106240d03040c0e5080488140c000a00040b0020300190241d20f495010f0f4140c400c0c0786818010740b0450044409550303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 406672176 1250 406670926 406670933
    0x31b07050a02090a06030203031c0e0109050c19031511070204020a030c08150a060c080d1e06080c090105040207030909060b0903060a020313080d140a050f1311010f020a06020403 78
    0x1120040e0050f4000c032815804500080524000c500959030003030010f601d00003059a200c1942c444450145640c03580c0e03a402609409020300403121402c0c0140c0040018040075401c0190007007031719480e01002418201c0800c0092540100c501c071081a002000682c8020855448581e2056280081d0b00500c0003800303028450b0994040c424410803039561051955880b070a01c1000310213016459031002c100801000014803420071528003e108842c2182412594002d00c0140c0d280c1c40b110890004104480444902c2c0078401c1e040102400001003440d5003540780032903060035040c043d007802503400040038030600d4020100c003402840c1d0210104a0941d03581c0d40e0700030541180da220f510030302a0780007103045244507000b40c0c0d01500700c0c1c403a40c81a250059684090540c40b5240807484d0700c0c1c652030b0181441c02000d001910641c1000c02c00300d071a00d0401c40500c0e0820000304801c0002604900d1340001c02c0c0750401041c801d171000c1c01d00794582e40350070720268504801d0160050a40b0700008020041 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 406673426 1250 406672176 406672183
    0x90a120906020c0d0803011e08030313021f0f0509010216060801140114030106030209030f06042108040b0610110109050a022d0d230a0302070f0b0d02031b0705 70
    0x12a070081c0d099a0b4000050020425190a16180602121401d000500208030f1440d258a042e059007050408200c4d42d41c03c000381507030400c1f9083c00d01600c0011028042d8144a608102d8041941c00b0309101d00c20b51075006001c0b40030100c008003c20001160381c48081e402001030440b292031064600c00456511040180030800074028002030880b2020084025400340089021542c4042592805c3d42c1c01c24504074000e400001c9269410b00c00d200c00c4c0c883e1000f003400128042c90050150b1745c11180e60608070307005040581044010081c1c17040c00c000104101d4441d25811a000b101d00104441100700c00b20380100558100d07403c25464a0318403010000c002940029041c07003500e0000c1c1e0701104040200c0c10f51a280b80c1e401291380d6032800343c1480e14021143c001e0403071150030100c200150500f1024407000160480080940c09034254005254042002c1c0303000300000f80b00c280072070703003002c6410110707002f20042c040c5203903000700109440501810080c41204a011070b15511081c40341480ca95 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 406674676 1250 406673426 406673429
    0xc090b040f15052a33071e091a040602030d051f06090509090705130902150a03050402090109060b09090405010b1005032e0b0c1501090f18021008090a1209 68
    0x3040c2c400c03075800c451005581d61071096801c2d0480141941d40700c5d0307580b2035180c4280042c4031408016a540c5d5102140b031413540340d102041c0060b560119058184910345420300071150301100141e50600c130810019500004075031601806000108035a11744d00200044450030400690070462107890100d8032a501c54882c40031160229040480713a04da041c10241c039000c03540280340d0050100d0b619405010002e030001c106603413014108070700041180d9403001c010f40107544040b0011752100300340020f40c40c02c540c5040c05004145400c122203464800d14443c0c03840340040b507a010341d1440c400a8280a070a42c4213007007208000d001407200a8030454020b24642c421114403642c0d80b00301110380703070b200215a41038459002034005511030b50308101c0000c1454005408030345c1507114a803100305991003402d030014000c14400c03002041042d070040d0ba00042c2d40c602180f12942d1003e98041d07401507900e100700d03491181400c2c200b90400c0c0c0c0f5180c001504080c1c2c40d079000303000c0385100b10170130350783e076500c92a20070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 406675926 1250 406674676 406674757
    0x1401021005010303170403050d02130311010e06180a03142a01140c1e070f0509040803010306200a0504061115041101030e0a060c090b040f1505 63
    0x103105050450151040324070070300003d0001401c804000c9154114842440d400500904040d410302e114162120181d038080304d0034054042e9101030403c00c00c05450111710a025003424a08090325480001c10803c0c00b43c552a0842c00c1c05190611010362170700c40d14003001e90b4100912103c9803811103855565090100070051403505014501c041000b442c044c05103d9410582d901d4190050b5102051000d4000007800f5116025000e441580001c990100030844149180134001c0c40f854420954a0000035910842c0550048000c0100042c41602103d05480e8410030005500081424034603488c03140040802400c600010354070301c40380d000000b40c004c5442aa03581801c0c00c03650141c2949652600038901c250303005020105001620080001504020602d000280c80d005a00001c1c6070425841c41070314107940d90703148075030030951102c00e42016081c40e00000b85014540b605085082c1d01a22828a00d00b0003c0110600c0d10702c204112488020b11a401d00d080305613410358160b10651103003003030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 406677176 1250 406675926 406675933
    0xc0a0c0213051b03100b090418030903150e0309041d060106090312090b031512030a03020d0b09010b040b03090c2106010e130311070f030305030709050604030b0c0a030b0a140102 78
    0x309400b12040f002c0f41e2085030603d1920801e14a042034015098000050040d0300544510014003040c461524002c0318500944d40c07a0b00252a50a142c8200d08401240d00c2016050040506c00c0d40000411201e80d00e40075200042c11307105612900900041155421001d030007020000a011a806807510301030340d0107044011080c203807114080d50000740324850803042d84814400100c03d82007200d20a14009c501507c035040c450000f0a49908550014400b00301280d0b012401c005010a148142a0701c0001035601c040c2c01e5040c4070325520940158801c11100400000c001040d190007440300c88901031010300711402d070112100c1050701c580920810840c2600c5840000180f05840e254000d000d00741e90080c1500012031610100c1d018042c2030000500c03803040d03c00000325080000f400d400214000e5564585a040000c0014048a21544480d00c200070901c001e10119010f46a0541c0090228909130f5a40519072025809440450030640d80420076800000314904143e4080310107100076400d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 406678426 1250 406677176 406677211
    0x170706021609090c03080d091a060607200603011404051f05041109060a020f15010e0a0c0c02280504110d02070807060e07030c0801020a080c0a0c021305 67
    0x101d81d10403907641400308078008032404111011507a4841d0f200307a401580b4540649840391038088450f1702c08158000a1640c0381c00007030a11501c0400b0110768003902609202d2401c0074000140c030350003420400380c40380d00d010b603502c48006003240800314038840140086450750b81d110b544522500900d1400b6005905180025090300e120411180543c4c202160b00c0c1e9080c0e003800c041c480242107500354001c41040805c00f1503000d5803064090300c0924400e5000309402c000441e11070381008043c46030520003581c0c080062103000340956480754003100c00c4030001004a0070311012540c6000301c00700030390400c12a0510ba00800e00819005030003903011010100215950741c1030000701c0343c43c0c0c0c598103850002817003078050400300c60300100748881c01810700505000c07450321148111140040202080c1d8001c8204000f04152500b01e04001c100040003142031000e400400f5020040061200e1745064001030301070011230003988026000ca4001d0040c40f403849104540740700510060310381c0350340051038421 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 406679676 1250 406678426 406678439
    0xc0201030501060806010801031113060905011707060203090103020d1409070f05030a0512030601090f150807030903020d0309140327060405011209020112090312052413090b011707 79
    0x1c013240070b00010b0f501c3e0740c41a0b195803a8500365140020205030300114507140507034004054011400a00920880022107514060170b03d01081c00c00c95504641c0c0d04008020052280c01005944040f4400c0c20050390b85c25008140000922036101c0440140020a0074001c10090000d07000040d0345400303182d9413040e43c60303108242d41d50180307100060003075018038230071404580607074041d54200c9810304200703542c8c41e2507041d06810f14203184c100d0850010f020020100483d4810030680d0025041d04003000240c0498034000d490b5801007928105050320340c0146020000c41c200c06600890300c0609880d120740503a988805071494500e9002d0b840310205403105401d00c0d11a0445080340d605864000c0f90354a4500f01070b0180804681c203a0603c000108450940c08150281440d400c6c0f190740c9100c7c0c84070000c1c1301002200d2000d005503040440c144000b280b0209003150140032040c08498400007041c024040001500c2ca45100404e9140140000070b040380102c60150700540b00b03442500d032040c0c0c4642 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 406680926 1250 406679676 406679687
    0x30d03050c04060327050a0614010b0f09030705040e0d110d0503070f120903050c1911010c0f050703030908061f1202031c020607030f0902150c15070c020103050106 72
    0x100e201c415254100020403483c0e000e40c2c01821a400210320340c1e40d445500064070303c40c502030500300307813041c2e0000762480c010401d0301d200c3d0306248520365066203000d50604514042c107026402c0c1c05c1984001c00104000705a034100102c0d001048001c00134031800c190599100d880e2030741107a030000800e00700210722112000204114048107103e942d05811541c1d159003c5407000d0002700c0c19000d22101401c1510380c280180103c0d5900d40c020b8a4103661002d112540500d01040702c00c0d00201000c2709490311000600903d164081d168092812031840055424a00c42c081124240201903214500e40002015000004001100c509405445080d940c3c844440320306c0c1c1003100c454514a00b5038034144010f281626840c0c4c0d0321800582144c00300e00860000c3e80040d0002440e0a000d80c2c0310004000e145a4580200510002440c4040c0040c0c006903020401c107410f0019481e50480f400304900000e03100130401062064500c2005031864102000058480c0a4401c4181d0009092200118235070b030056 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 406682176 1250 406680926 406680931
    0x212011e1802030d08061206040305120a02030618270d0306051c03030515031506030106140d062003010f09051819080d110423011710050607060b030d0305 68
    0x43d01510188690600440d0801c2005007201e41c008030f01003440070843d2003000024466442034442c5c40e561030f01550f500002c90f000405031540c5a004100304010760300c0b55028810760a040b000c2e50030440d1507000007215980d425a20003150103850a114a03107800b070008003000c0603172054078100046600c902c248001900e81090519042c2da84d000d804000038400c0e8400d95200540000e03154404104600003070800c0b1902c400d9803680040b407001e118040c42c080c815500148211110044414424000310f28458400d00e03000d807059680380407000e00078100046171405e441c2c0458404e6500d603107401c08203052024500401b00101d15040000f01401c0c5e038041e1032400c48150000900c00390b100032604a00f143c001071001c4680c0817042c060b084007848035028502c1d85120102c401c83d240d6040c41c050345803400d415040c1441300d04000c011101030340d030014802c2e100c03010070718034000b12a074400c3d035161425000d81e400f0304c1d00000d000410509100c1e144e40100c511443c00c80c1560160482c00710124140c4409 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 406683426 1250 406682176 406682179
    0xb091f0209120d30050f070e0303090a09150b0a02100f09080405120109050319080c0a050906030c04030c0b03060f090f010918021005030414030a09030f0212011e1802 73
    0x4904d51030490090040340d0300c40c510840441d101d08031079603032252020b840c010b41d0603a2605106506104402d50801d1120203440415401942841d08081c0010300416040c800c98031440d88c2c1d011841020010300c500c4a001e0050070740501e0b52044081c000075664001442468035642c0740c03000d001c4804400f0b003c0c054805400811303803424241000b04100c05001c118000d000c1640d40c4000050010340240060f205511788a5004400503100f00b0018044010007002101249410404441e060f07402605a0300842c0341030300c403c0c1d00c0c0e0b0b690f410100c180d40710300e800203008940c1c408400103070b1020b890000d5200700320549072840b034410b6100503c000a6000ea8940d06e00c0703031203a00103000e951040c0e8407082c0c443d039071403000941c50596034020445003141c04e1901c50000300008200702c244480140ba200d0000340e110011454030b455a807000707250703614502006041e009540402415940d0700c8030311030b9000d00810300030031842102c000c4c4010200c880d2680c0c0541c0b6800c061003d254411071280c8000142e80 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 406684676 1250 406683426 406683437
    0x408070321050708090f04061502010c14030a051003170301141801050108190204180507020f070519261c020601140a0e07030e070e01080a0b091f0209120d 68
    0x80c40c1c4d14101e058222080e030a0300b02c98a400440f50071366440c0aa00c0082c01c00112441c464484058000d080d07548858002c402d20400c0c0c021381da482c000a60407030342d0003140400c0010f00390b110390003654419022a4000341c0302440380041c009070407480c0d80086d41200d001d1002c0400c006a41002c0c44040c040c4a46040c030808a036000420007940200f00391544180785050000d900c941c000c1c529412a00250040d00720031807200c101500c240c501c8d1207002d400506500003040072982c000b00d215610303160340c0219070264940c10390381c8001524045122001e841e40b118802e500940c403026520111060f03107480307003051040300d090061210b04580044a8441594050300d126820140340c1150003c0070049180c10101c0c070000060a45507100d8545d02544032039070041496070207418883c0c901040398001c18034243c546401000781907000103c0107403843d4030a502c80204e40d0795654040c00e0840d59111100c400d43c1034109410807840341d500421501e40101c40c00e444410750340c0c505c956950302c8004080b02044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 406685926 1250 406684676 406684687
    0xc010606081024031b0e1e03030a031e06060e0f0405090312151f12020f0a0e01030b091f0b03061014040801090303050103060e3708040807032105 64
    0x19007049a42c800044207040208015402100000c800400341c0b13244000212103c007202180e18054103404030403520100c1800e544e40c4807c00003130b220720031417041000f456030310004e4200c2403401092022280030b641000f01300c62982e0318000382200c202c01c81e0307481c0325890000ba01d05031450141300b600d00409910000b0f40c20301c007480f130400008080282151050031000d08080000b41d8580d10318442c2400b1000441241a0042101610784180c1980610705035005100001260406a080d900c0d142c05918201102d143c3c40c03001a0011300d601d03030125030010a40c400b006403001da1150a4400e207404200c030504520f0740c9090108250100fa1440c81c1d001c02d8210465011030b100744000c2c8205074080b241c05290a60b01d03054142103903800c031002c40209858400400510080e440741d0707d10326043d9030180810f5510080c0ca01400c2007500203840501c041c0341c04440701c2d16460300746640020351103011650354036268001da598640251000721100580441070440d422150401d807604d0305c150b03866403410320 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 406687176 1250 406685926 406685969
    0x5010f090905010b2808010618090509070602060703061202012f0609160e0606032809060b0402192604110f0d03020613080909041a09030a0c15110c0106060810 70
    0xe9107001420620014403901c040350030320700c07407040bc0d001d107007001e008215442c07820001a040c4103005121400745803400104100d0386240c0d0810103500e5909181c20b140c1204004582440b00110040303010341c41b100701210f4007994000203807050082c8809012102d000843c05000f05120f0514041d40c500c0a0405c004605a410144091504001101d42e0f4581d4115400c5141324485c2d0508400400c075030311703000c210050000610800c52100d100751070a625051029190440d00d911002d044d034100a149050140e0003400082d0f09a00b010000403402c1a5050a084c0304a0414034000c40078440c54204401c1c60302345c6070040e83c1c01e900e1541500601116035808094610300040e458043c0c5603031404004050035941c41480e25885075100e07030584c646088003031101840443c0000c4c24841240c0c81046801c1040e40c100083d4401690300a48034500783d8290030f064406806580c0c95401918004100070451042c19000403050303520035075600c0700640d217000503000034007058846c070070242c0100f25482c6480c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 406688426 1250 406687176 406687187
    0xc2a05011a0f0f12060f01060e040903080f10091e0b0a0e0412020307020a0b0a0f02010203060d0204020f0706060b0c01050a0207020105070305030603071701090506060a0f05010f090905010b28080106 87
    0xe0080092210b004c1c18624000039081c500205ca1481001610f82c00501c80c1c160048103880466500750390401000440e99800b82000c1d130050103207500f81901000080380c2104962a03113010701303015101841301d89030640385c5d040c04040f0005600f05403400d22042220030300300034100e18200c440c0e4840012081d11140c84445004044056a5045000c10001100561207903070b400c80c0100780700c0251995410b20454010119000e01d0720140442e4010000d1182664807441004426501181d0059440e207041c0740b03144951040010040c44030381005400242e0100c4a4040e10a03616140001e10141e070b1200307010307800c900c1903000082c08a9000d0191401082c81000659440034025086462807500e848030401d003140c00c00c10300307401a0744502190b41005070500c03d1715086001600d03400d840c0d500346000355682c00301900500707042048084015294a00c42e408000c003d00300b2110401035940c56000e4030000354413507a0341248240710500d120080104101450b202c242d2990740b0009541d00740f09003100c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 406689676 1250 406688426 406688449
    0x303130b0a0c06140405010c0801140f03030d1506230a050d0b1e0f030619020307090b040311100815060903010902041d06010b0703020304090c2a05011a0f 68
    0x802c8000c0b4100d0000030302e40d100301c1e6004940da50144101d40741501d01542034504c203840c50000c0145010041180d2170341d6459030b10f031061084810014180000d40031070b14600810380d94401080c148454842c01000340e01050042e6165550364030814001c050604810703103c4030b11582c1c0001d07402c00c03c04051a20030390180415175241000030800b44030b9000081d01084c14540c0500c24140c0c0d0b4080c2d101a454904400c0003060410340103040a8a072854000c09a034101d8144030038015000800078000503c2140c401000e051103a40d401c3d100e030f03101d09208208408803890640207824813107560360801d00800745a482a00c01a00d061400d1408400340302c110b40086984c42e40564a55802d400165a50302507400c006450702d02a400e091064509103207406ca040e484010402010481580400d074040116400c0d11003040c404105c8055583c07007101c61180140d110b2038024040c25103094002214512140702c94050030083c00030010180540d940c01e4981b84600780e10512194843c496820400410039 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 406690926 1250 406689676 406689697
    0x1030308071b02060c1b18130515041b090212131e08030402090708071d0d080318010b010302040501090522110406141c051503070915050303130b 64
    0x1840031942d50200e10550400ca145c02c81c00d4020100b98072224558162090105100700d4184440c8015680c80d0180c010025003000c0c000d040e04c80d0414144401003010070b100c05150036a40d006403625080885d40d4159200205102c2034181c0f000140b4041c03240203560000c41d400801e411242c941c200030000152490fa0304840305440f04c0b04000ba190714001074855683c1c06400f9042d03030b9240920410000c01c01c010320315014000504280540d1642c8002480358505000c1c4209003410030312000600180f40c00440141402030000c200225500401d48150030303000d15000a010700100d1030010350583c0114060540001d150034003c014a00c2d000b140300c402c45400e002c10b580ca03106102c0406041d595001003c4006980c0020204866503000c41444450f80211010301d0410105128180d91080607088007400d184e2a400401c4c20b9845006220b49070060080859080c29580d844100180c0300014007681c040c2020500084c00d0700b808011a00c100591080100c0c885003002c00d00d81c0c10f034011581b200d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 406692176 1250 406690926 406690967
    0x307110607050711060721230313200409081804060501120f0b030706030915020a120b0609090403031d06093a08060405061c060b060c0118020a08060103030807 70
    0x50b150f54202c0f02d42504080025648d00c2c98a0f80e04c0300d103407103000f1035100304800d800c0810020400c44840c1368181d2140c056000c46204108008405c444030305a421408040c2d1007132500e80340340c0810040200510041d88442400e031601203c1504002c01c03070360184205404600c2c1940741d218150f48030303440150340b80c040510005807038050101003440c043e682c1d0042130100e640d922907076050013a001c40300301c0c10242e4140103624000030301900034030300d0210584146451340c44804d05075469a4800030b03a601d45c18003a00401040c9424180100601594180e4180340740001d00030701c010038400b041c0d881c81000c6000c02001044403080c00403a40ca514076960070082c04040c2c00848451070307485241c07102a110303a07850f94201d06003801004200c3d030000d00034a11130451403151403065100c0c0b80502c0f00d01e0f86c00100c0000c400c2c034041c010036528840c2c0000d030041c5502c0c0c001544003061444424a0400b03009588140036980c549400d80e075501000c1c0070280104140344006600d080c4620386002549401d003401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 406693426 1250 406692176 406692203
    0x905060d060b030118050717060c1617121605040506071b1d0403030b040506130b01032d11250c03081c0b0f010c0b0a090803071106070507110607 64
    0x12545000c640101b2a10364004007130411005035100000c640c010b5090f409415141040d414000c018410301c3d84e20a4030381c0e100a0580140109021a1104852003000007991005140c040d003181d00c50407210700e8026420595121181441751055506031500a003c66280c142252243c80341710714040010107000c0c0340342c9404114601c20002448001c0f2401410113003608182c5405000c1e10440083c590240d4900f00400c2082c1c1d82d680811030741070413003040005040101000403805040000880c1e0810303181440d83c480452103585100e03050090309003040081c02c030342e0b922404151080303c05006585000807840390b000d4062200e51590300b8851011110780303c4d5207684200072030f000311034071140c00e4086002c4052880403d0050b1400c0c06070445c0c1070240301840e100082d04140040310007405080c110400503c01c02e034254402503042d500044c4032500d914141d90001d10803100d480c50748c80e0500070344010030300c1140550190740c81640d02010718103010b14400244860f60b0041482510482141c904 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 406694676 1250 406693426 406693451
    0x2040906030302030307110c010f030c2a05150708010302061309051008011b0f11010b04180318050603040b130b090c0a0503060906131a070c0303060905060d060b0301 73
    0x38200085229401541d260b192182004e48501c48007420a00345402c60000b9017101c0c0ea05c428441c05450a600b0001003041d60510704481960b1070402040c0d1686c0c0c131127095480500003280c524455481401142c10240d00c07256210117802c0e084e0707560300c045881d4000500040c50040098054078580c8441031040c2580d40c044601915016221000034100101d070500c03416900b80110740ca0341542c080d1201c00520700c80402007601007071441c10b42c20821003c1c40d00312400030a40000c3d80c1044001c0c014802c0c0c150440b62406690070355841103011a2420100e00c0c0e4102d4182c140350704a980c020421411079446803100c04220000418580c20403850080c90b03000608030540070360140310101e00030942181c42c10140414080b403038000b1032095010208002b0f001d00c002401590000303000183c080000103615050590f4401c028003220b4a0750850108045564032549940b6024042d90742880180c1d5500c1100c0c0c03c80300c059440300d82040c80004030f0408207600c1c0c0c016400e0403901134000101c0303401000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 406695926 1250 406694676 406694681
    0x50a06020f0310121113140f010905090d020a0305070f0b04150b030a020a151806030c030b1503040b15121e03043b010b090a170705040f020409 63
    0x10701d405035000012090040a0885600d51805000c07000901d03807148030541c80700c91591102a81d201d00c591892800c00d462010a500202c19441e0054034840791070034000c1902440e0070017400348135402490f209c00940103103000200030341c5050564018200c02c0400761012501c40e1300c241420341d04200c4507013080000900400c0014426030241d0b0001e09100307104a1088103484801088038800d6000c0108440075903502d0007140300701c030586818241141c080c20020796100800b103000c1200719443e100700145d5070743c040e040070a141040b07a600f00007084401080103015111140c1e02c003c1014248009000294540c3c04140c102d052040240380c0446001c00140f902e60040c001720106401c4514001c4a1080140c0c00080d8011044045c0d030503c4e04203081d07806440c40d0034186000b00201103c00440d03110341400504040190100200d0084da1603841c503295079406103c286020f011030110005031000615455548918840c0282411501d402c08000141c0400754003c8070440e8200000580e008407032 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 406697176 1250 406695926 406695937
    0x70501110703050d0c0201020307050d020c010609152108030c0a020c0a090204061701030f150b0913050d1805040905010b0306130c140312161a090f0102090f0607050a0602 75
    0x903541c0a13601e101400002083d0f0701c41686003002d683c0107005000c4131541000540c0d945500d00c08005844520200066014284170351022102520b0301c02d03410821824240f114060740c2c1c01e4038089610300b04c10141d1540c08805040f0203007080c042170001c80c80b801c0c442d03030084c1445e402620442e031940080e0000650208036680c04100016030001c0d04220082d004407030f010551405078490b80681d8074580f02c0705c21401428000900d048101c03c051152010b49621850010402402c0e0b03c030a0328010030071a4162555000c1502c5501c02e00c3d62020085205102d40003501505520384110640340400b804080c0400b07007011200d0703540314031600003991400c10940c0d00c1905001d80030b48030181e40c1d04181c4242011a00004d9460350240030030760b0142c41c00a0f820f554841c82200703050b03440c8c070303100c0303d049203007940c000002c060701c0140010f0b000c500c00e40f12101d4001c40c0c43c0420b4807005000081401d080b0b00c540000c0d9134010082480c0d458052074290041c00009021b1420782e6070406903a070b1004101e03400ba = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 406698426 1250 406697176 406697183
    0x30e190801060f09020415050306031204080c0a0510020c0f0102030f0315090711060408030a06150201050708130203060f06041b1107090507021009060b04142a0307050705011107 78
    0x6411041007070032041d0303181000400402c803007181b0741800c02d40d0821040010312a24018044000042030440e2820051810303807a2a41c00c0c040e880d2a201c0a004d529000091a0540f050488030404962031030404648008122244c009040400300c03c41806076407104400454103600051011740400c90742c0b6402184583c0c4034641001001c1d641c001081030015000d888107040002108800d07140c160001003645d040358201d00c605849a85241031000604142e0300010081e03221050a0043c10303405400c05030146d00e203070f16600140d07039a524412554080f4a0b0000c1c1d031607488000031400ca042c010b15070640064020f072010942c006040656280b171410010380d40c000880301400b41512100a000100c0030f469408014040c50425940003503560809014045000d42c1c4e43d000c002c1040029480285400b40c06402481903007a0703d90301107000c18007200d02d44035080c0043c9005845d0042451000b03004100d8030803990840d1140231088410750030084040301d00d5176032841511510b0900f00b01038a40b0922 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 406699676 1250 406698426 406698431
    0x30412060506040c0804050d0e06090406030303020a17060a090207080f03041202120304031d0f092701020403020a15110712021306060206010902130f030b161b030e190801 75
    0x20118284030840d130611841800b0060094144000640c0205003c1c10b00a12481c1036540300740704800140e010300c2200303e4030b90700500e041e0380001050703090340140441030f41c0d5132150076940e0104c00c0d001c1d40e403030012620517903c400c0701c042c00c3c003042c2d001d6406410014081d40c0c03541e040240c42e4100344503683c4265020344120341d034040101d4420340d04110005010130070316816410b5040903503019007079140e02030408880d54144000100d86850b40c251513000344100915a44603814502143c2d51104140b805a224590f10301e000071070110014021113003160b50240a030300c441413074420601d44d0900c03108101c1040254989003500501c1c0104241d101800121001c0c000e20310051041008a0807424080d09030b1904141003005299000310360b1604440e03000030050b9440f083d07241c0554211149400c44c048075010350901105010041c40303060f00c9064117049401c040815454292100304040800f9040002c900241d580082e200e0034404100301800741c80c0700b80e094080ca52031100360903150030200c45a175 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 406700926 1250 406699676 406699681
    0x32a0504020c1e010b0109050d0f020a0b0c19080d0209060d020304080a1205150f030106272009040f09050a050a12030b03032a0d020309090109022a0304120605 70
    0x8540f016080e000220a50003080810f48002c0007070042421072040d10300c220134200410090004261050f00611360003052099215103c2d2130300c40c010f411603880c8410758802e040444201403450006ea201f0345c0c0d0003448032414100c4005401c0d0183d0320456805070050401c4c01035003800079050010b180902d1140c5485a01c0d5600a00d000708281d12001410041509080c01e0240035824007803188007074482a103c2c202d1540c4900301113405080783d5070180399011071503140e803c524161171107009002c40d000c0a050014600c40d4034800d03843c2c0b076404c01080012a0030007202003130749456032181901c84031f405008241001d050702d5050801d000e0081c252415013240280c00c0410540e0340350400703c009541010014160350380d0101e40d0b0390080c90611020a804e5940082d4119644041c034410340c8a4442207606040050700000e4894104000785801410401300111f0400c0180c002e40f0415805500d850080c0030b500041841440540c04074440c05000070031001c82c9445c1c50344404046240280e501040d80e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 406702176 1250 406700926 406700953
    0x3090a090e060714030f040816030c1403040315180b090d121b0305040501240801050708060627090c0c15090d050307031e0f0b0a032a0504020c 63
    0x2490040500e4100401380441e80883c60107070b801d4940080e5080f205c545a42d07607500d400340f01440784089502120704900d00c49001c06600800d1210001c1c820104441c0030341c142007075582c1d40d020340c2c0401007016001c190122001056a40300078152071003000751145041040c2c540030404c401c01d0b140340d240c0360008800400240d800080d00800403006d0207040011800d40041c1d03040c8200c0c10300241042588800201d002c0c40800d41000146203450781050180301d004160012000e0881c1c811000c2c15400d1000007142e040c001e03005244039410280100c0d2810601c40700031845410314600c0521030340c00122440050381c4465411134840c1884a00099946040c83da500340f8000f680310034a10303140c0e200c20802c22002c07008200a01e100040e030901644a4032100810f40c040d00c03500b2440e9402410403404189031801b242c1091042d07881c4c00804200c00c4003600306000102989000c0a01000c1003030b001d503198641200b00c201c1c03a0745400021101c809484900050a0740c0c0005c64400c3c00b0b5201800703c8000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 406703426 1250 406702176 406702183
    0xc05011107150e0103060e090a14010209010c030537031d0c0f0a180f0b010c1214090909030d061211040507052505061f030602030903090a090e 63
    0x10380d680c00615465140c8140744a00a5404005800700080d00c11842d00d6640260410380c046d02c81804c10010a00d003450813680e03240440e070710a030381281e100da1240b580454103100f01c440c5268107070b4600701380e088036803010341d1aa40310350307002000070380c5000203024a520083c8900c9600c12240e03140c0800341c5503c883c02015219024210240c88280c03500015240c00700181c001c0044509079000d0550f030182200041018140303901071000f0f40140001403840301043d5102e05000007003500c0c1000016110801103404a80d8240010f00c40d0f40c400100030b9516000e4011407030b900401b032401900d0060410f010880044003036424140c10b900114a41051022238003c2d040038160440024440803220707110f00c1400003120540d0b42c0196551030118100d103101c0c00455007521401c16450103a44801e0f142801c5042006130291202c2c05620049624105540e40681c6082c043d145081001c03400d545444000350700246c0202c91300d02c010068800c85490384086407000f000e02d002c0009403c809026a03508 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 406704676 1250 406703426 406703447
    0xb090d0203030a08040b100e0f0c090612010302040617150405070512030d060902030f0c07030203121510020f030d0e160807080105060a060f0f09090533062b020301030c0501 76
    0x2400340d100c0014415232286a2007264021400d40a64895444450300f051603442456181900100000780e0740c210110201c4c4900c1c1240e00c01d5070300b08602582d80605245891100d0380324210364102c001021204200500705a030411f0082003614a140d940d0000030340b001c0101c1b0b800a4540d0004180300700742c0b90309803080100034814807000750710318a07292082d965007610090550a440d0340100f2480e091510800c01e5505040c618001d9405074144805107001c001d403607455981c46805d1490000c41954400f080200350403030381100440c100b0150304140e1020304001001600d1070b111701080c1e4504c40c18101c01440090444c80c0103010b2160403d4270141c00e4620007000e240c0a036101c1c2074100102540882118100701d1286018034450b054964226034940385980625101c604020a0110760850b10880d00d178145201031440070032070a080340e00700b906042c07001102e91209091000000158000a80c202c1c01c80044040c60203407076001d2254022a00203030800c0c0c8150015480c02c0c0040e5810482222 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 406705926 1250 406704676 406704691
    0x212010504030c030c0317130212120328021602030f0a02090403080702010f050c09030706080c03010b0a050c0f06060f061603030e1014060103240b090d0203030a08040b 74
    0x1016203000d89003d071095003085002010007000c2261502410710a0b07400c00303803011848201c020b44d130411a01c000d8010b0b03441b84c0d040e407140c000310b10340400c18400010801d482114a0710341c1425581c4d101d10666003c1c80c486079102140d003c4004003140264644024158144040081c0c03c150401e0f0061515044040d1080745d06c0d948010385040c0903954030494142d00a40c10326144c1201d80c2c0750902240580380c288032040c803c5090905215101003198042c1c540d81c001074084403400c540d2031034115031600c000d403440030001200700011f1281c11480c000500005d901810302e2454100308030684c038540720f00c0500140755a00080c092000625082d01c541896040c211095414080400301501400d49488001000c0c9a40d8241110385100103105100106841001c100400028002d842072884002c99000c0c6c00a0f15029060080040c001d604c3c6017040502c3e0352903042e560030100c01480643c0451013007640300d40e002443c0030060ba0204000c01d2602c1e5950742e5003809091514000443e000c0160028 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 406707176 1250 406705926 406705931
    0xc030c01090b011a04091a0904111201060f1412060f06090c0a0e010e04061d04121e080705120c0c06071e1d0303070c061803030504290d0603021201 65
    0xd02c0c0300f421134401d80d8141c444030240050307071010381d0100e10002d95840c8a010303000038844042000303001030b558020307440302e80950b1382d40013444007500079038201c1d031050240c202c424020100a00c40701071940c03082411352001a02082d03107031340440807181c40c24a0444083c00384003120070070080d0a0504510294100900e001c40c1800e009441c4000341c455140003c0c0141040500025a5040d42d55074000c08014687c016603c04c55402c100d08084c1d04040480301030710080710041d04224000c1c858034200c1c01502c2c0c00040040b42c0582100704a4841502400d14410418144500200409210b216600981e221246507a03140c071090342807820404000e041005000c40108000c2800e80441c030040c0440e541d515041040001c8644422070080070700074215018400030a07142c0805c07075030f05041401c0e42c0c060b0f1105d0080c600c000900c17002005843c00000c0000d03109220030801000d0502503815030ba50f070300c288c0704001c22201020024036001400401e14164079840b0402c03d50030f10b81945c007071781301081e00207 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 406708426 1250 406707176 406707209
    0x71406102909151801080f040203071e0b04062705010801050d03050408030a0503240d170c0109151d1b01020f0609010c091508010504110c030c01090b01 67
    0x1589401d00d168010460820000203100000760b031550524070254400050040c0c03919000c1819640c2055a01c00260104601e0700c0402c80b9940c10503440782c0700d030f0b50003001040385509100b0100c9114003c282d9400144541c50400309100f07445d0800741000d03280d90f42c0d030452007002c90f100078000c0006400c0010340e0080307500c0052140c0d076403084400b41034803800d481040c22100c540c03604446520441c0d120354154040801c1b0007003615882070040d4010b0824107241036000d1070701c40280d49900c42c1e041c541a03004144560740c50000f80c1c4004400c00014000681508003880810b1143c01e4903c203103400c0751170207505d0640040f400200e204080209000750b4001c1800e101c208a080d6a501c20800440f204c242c918448910a80c400c2000070804100e890960310344d030920b5854140039007003050641020508054010074a28441305070840c4544699070303040003903403a010502c0000c01006641d03000c0070b04c01304581503003444100001c04655810343c1c00007d80454505040d21281d4060300540c0c101406941c8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 406709676 1250 406708426 406708469
    0xc01140306101b0c09050108010c140702010c0201091d01061b1109091207060e0606040207120810150921050601030618020a0b071a130311010207140610 67
    0x5089040310182d0802d11209000b5401c40030f0030a1071110300a04202e110440414a90643e07081181250300f024000c1c4000a2052000e40d80d800d030591524915080501c90300e4050343c41071460050303071070060400780801030311103061811040907410800c00c2030000d10010003e5a41c4100c1940c10421140c007140d0f980e1101f07a40f4844010345007192544200d0b004000b143e40d04100b8410180702d4a0200c00d100e91716001850031a015000c0402c41107110f010b86c100144d030700c0c10240202c450381e6902c00c01403a001d6820307150550f190798000d4408205c640140d08046014800306110034008070b01c941f2260710340c0f031804400b070b800c030040c92904c48e451000304041d00d00005c00000305036055a51154000c034503031a55a045039984420298080d5200c0d000348000117589802900a008042c0101d98001c0707a05a01740f11150103100680f0320b000c0d8040842c01d8403012903c2101301000d18103400f00003601c2e0000c1a12454592502d002c41d00c01d003600507500380000ca000c0381a0304001403d54510b04100c0c1c911410 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 406710926 1250 406709676 406709689
    0x150708060a0e090c300714040513140a0506060303040b070b09010207051c1209020f04091707030e090a090309050907120501030501051506040e01050607030c050703050c01140306 78
    0x411840c9803080b000c040341c1c50100502c60500c0c0440003404c40b07004400000f2441140c0585400c9800c03020028051100d10480045155019620400d07824519111048144070042400030480100d05d400100c02c1000a0402c00268019080a5000300184907140c10600c0c24008050005071082d8020842001001c1e141001d540c80150400c19030051540e6280540b40644920702c0010014019100310030072100207002d0941c0803424a5451700181e0762540101421260210070182d400301843d040d81c00189403540044039640d120307107408030310741c054070f0014241608480030440100d041d40e50180c1c042e0400060250348100d610409106442145d10090f02490960140c0c9014060307040020707049602501801d0001550f0241c00c10496a43e82003450081c0b10030382d01c000d090754542c9101401c915144081d2400d8031441030082c14035074600340030003049a0103090704070140710040b40300e9408100e0920800b00190301900141c036841150500041080303540c198058000101441800040e03241c00707 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 406712176 1250 406710926 406710929
    0x20c060406020306032b1e1e090b04080c100c150b0a2d05010509090a0c0c0b040b0106080a062601200409060608061005160c0602150708060a 62
    0x48010b0f81c0b510388101103400c024100281351102010070b404040d0400341031074494011131350740d81c809900140101e44484050901d40d1903d00040080480503021401c0d4440b60401d04054204051183c0c1d468194042980013030303100401c04d0704030361500340700c44c109603c0480a40d0703810300e02480701c5940f03035840340c101010303ca51f40703011715644035003411b01c035103032070581c00064510f4039080407002a04150001d8003030700f000459503003086095400907442d40188142e8072054030050408000d5aa4000d0f100010860b45030741d0b0082010401071400800c01d400700f0740d80690300950f0103410f150f041000141000703002801d02c0c0c20151401500300039846200e07110070104041c407042803958801d05181076000d412060241c1c03148910b00228900b05000505c000c008490301020f0a110345940e0f54020b42d507454049544980000d1601950014079200e00001d01480b4400f4402404038203007078036600a108482d40040c4003592101302509042580d100c403560f030040a9152000726480d0840208008100a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 406713426 1250 406712176 406712183
    0x200712020c220b0d060906270311010207080f130501050301150f02151303110d08010b0c010f0227120c01050c070905070c150509060402010c060b100908010f020c0604 73
    0x4000d07000c0d0002d002c2e0040311144070000c01c032284852141c24510010710800e0303000c807545c615060386002034489030700d4081826040710b02c020100c44440e0301c0645019082411000c160b5508200d0100041c040c0c20260200d01e20080036170303489440c60070a140090f6115040181840410302c0100201084070080145041040c82d214070a8000d04c4001e07450704404200881c9a81244010801e50005284803050094003da032000781c00440c0f880c5281d16180c15103d5500003031800e20041c00390328800380c01070401c00060000044c0c40c01501c807800c01280c00903000d001d0121981800c0c211550900e4001080440044907080d4080c15900c403402d42d00c00c0782d040c2c9503050040106110020b0b031310500c01c400080082d01001e02c03152614580041c02c060003903008440c1c007030405401488801440c0314a920402c100c2000b84801d03120b45e001520104641001280d43c56154021080581c03142c403203817196000d075500c600002c1814080743ca820344031140d04c106100303841070150700e080c020005602a00301d1781 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 406714676 1250 406713426 406713469
    0x3020910050a03020d0f050a06051c120504031b060f021603020103110c060a090302010e030a0219020d051606091a0313061b05091801140112200712020c 67
    0xb403007000d4010f4028215108851803420640f40003240094111a1003040700350810400640c507402000100c812203400c544d2032007620111000080d0340d04c4a41042080359050050405540303070b0f40c1700b0924a60303458400403c202c035034040003210740015201701aa0020300241c10103281c000a241141c0ccc03000d110190403d5150700108400c040c118080340cac000c1c980350341a90880e1030041202c03000b03050b40d140114010340c0381c9140211640302c040141c07524184207602a0a203000c07062207200d0141c49114080c0e81c0003411011501c009541046082044e00d2a481542c44884ca054400b5140e26962351010f0500d20604200800001210041340e034402c098000d1000300140c0d50904000a00d4440708403e4028050600c03005440d800101400c800803080b18100c6000487c860422000c0c00288604250500603208520103507026100e0707940b42c002e48400014070019140125070b009001c3c40050748071000000b99031428440004084804600c00d400203014203100140071940800340142c0c025080d59 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 406715926 1250 406714676 406714687
    0x1202030a12030605031002180d15020a141b060907080304120c030b070c0606050a120609060e0712031403060906011206122d0203121b031908070302091005 68
    0x50090340400701a050160032079031901604200c220095020f008d800514007400c0c403c40c68203140c6850b40381820340e44811608000010701407c2c8020350030820685040c44100c80030854191140d0700a8074250201d125290480ca04562646040c400054400003068100d02c40601ca080783c000210b03022a00001230140445c00c944c14046d141d8020b03600000d145640081c10300c512170b54401c0d0511115401080b00b045510354035001c014540041d4410307894070051080c04000443c00359440f501c002402484080354030809000b1550400c00950420241c00d176242040b08181a880817404200c44440803002d491030a2040010703161080040240c3d0410124038a00041022160000c034014002c4002048052040e45410a4a000070713080016000c8c1000c105080c13401030020402d1081030f0041c0142800b211f071f241005d456a170060aa0241c1c0c00c002504640550f0030800c014280050076119405800c4104080103042c00c90141c806020980148103c000c1955602e8507082c07280d2440c10499500c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 406717176 1250 406715926 406715963
    0x71d01090503030c010b10020f0a021c02030a0b1806220503041802042c0708100e0a0228051611100309020103050a021c05060d0f030e0108011202030a 66
    0x40070740245815000c003082d2401d00d0001500319043ca00801ca0b041144060450000c903951190850074204603440200c8441c05401d140150348070210141070014040d02d210f40200703240000c084000c0703c0c8221400e00700090701170007241c1c265140b0130301c6000e1f0040781071003401c04000c00c241c81008000c0703200c0400c520041240800489004103040c8034001d0515104808160094005204e40362410390914080c640303030f0600080381e6026020302551a225500c0c0d92100b2507485400404801c1d500e0748043c00484c071814158840e501c01e1594201c056601c4911495101415100020781c88000680c000e5416040341c00034240d6019032406d9001039110522414480301d81d0324120301e1207420065041410b04940d40c10b0f041001818002c1e2401d00541d1140e8003500102e20500564403a00902d98007450300401c82508001c1c0c00500040000440000720785410040d15020300c000c03400f00c0d110468804441d604621090700600200607040308003250380d0040317500c4100003d0000c0101c03050290f000c224 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 406718426 1250 406717176 406717187
    0xa02240306040e0a0c080604150924060b0f071505070206041205071719050405031f1401060c050c010e090411030a050304081e06060303091302160609020117071d01 72
    0x140317401844c00b4503120b40d68003103543c4071041520140d0746040007008540014600e40200f1142944c03002e011014648201000c0400c10400a08100001d071185070001d54580c0400c040c200300303026031548035038521151515442802c1542400c004060400b4108058180c01103865603000d5000b01040d00e401d00c2030300089a1503c030703070740b0000e08480e50000c07540d2090465001519039040c94404c0403d4048000c030092720700e030056200705a41b59121440d01d00303803010305034804d001040d050240410130b81c401009210400303074260481800174034100310341024480208400c18204000b030800176a0b4807d50808280c40d054001e02c0134043c01141c4030340d4a42c40d1810084801c40302c1d000400d072900d072615958495111f100345250f080300350320400382c428032403400400c03428003070a4010000c5141102c02c1040c003100081003062441d05036424000344d0181180084440c0807148500800620114140b00140c0301d941c80c2082480442805000c11010035043304030307020704100d0980c1d444090768034880125034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 406719676 1250 406718426 406718443
    0x1a25030918020c1c0e180115050f2209090f0809060d0c050307090617070f110105130b0a02030709050f0a05030109050307020a050d0c0603020a120903020a02240306040e 74
    0x4900c42c1351380042802510030180341300f940441c0d41d950600380f114010480b0b0aa00e0f20a407500c904c17034003070040040140e00340c0075000c1807541c0c0c10030f076051a1402d400c0b4482a04003800b00a4000005003141080400941c01e4101400c1418400c00101c030040e242d1214202a40000408900001509c101c0d25078483c0c05840d84020051010301a1880d9148000c01c0c0c0e030030a0f101800802c030141c501103801d502581034141084120560f802c50380c1d941c01d00444421812104180901c41307180000c903400a004c1c01114030030802d00c00c204544c000d4500e48019490b41c01000300030002c0c814418400a20f031311402450807100109c4074009588810350005000c1c1c10154270413981f662a10310038000708003001c006815038900803500f01e003600d0741c0e4100380b11101510440081c8000c01d0700030b0030b002c0706009a001d44880c030003518180f981d492121480304220f0f004031a00b5800341c0d104451030811440c0c550310f04d80b4200341a2089802d1841d80030921101d13400b020304080d2040b41c5424101504102c100010fa1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 406720926 1250 406719676 406719697
    0x50405071e0905071101020313150603021c1406090f1209010806010e15121b03010e130512070f0b01050402180904150501170c011407110a1a2503091802 67
    0x652300d05092016090006144008540e00072101c0d444003500303d442d04c1148200d0343c010f0318604442404003d180c0c0b0140140340102ca0403481d00000a03008601004520300c03884006006006826000030118544558202504060748003049021700c5a6400001150410310a08003561075038200300000c1d2017002800300c420010701b030200c0c030710701401554015035000d41100c2100b040c21003240d039402d100b00e120074051071420400010110f456401c5a6104101d0107000d21300b9241901201e54948801e03500c1b600e0300340c0b50f1741e103554000e8041c84038080649004120445045142070900c00c014858800c0342c0503224441e22107d000a000d10440e8801c50a440f1402c440421a56031102540048203d061b682c1410768420006a00003550184c0c900f00030700301068880a003465002d42c0d9400100c0c0d056880c0942052921000007240410941c400b01031071040c210884d16481d070750b10b202d941290668150f10001880c2c854000c0800d8000002005894030704040000c6541901d13041c0d0085d208002081 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 406722176 1250 406720926 406720931
    0x9050105090706030b06070b07140c01021c0b091b0a02010b09010602031308031201090f0b040e0606010e0d0b1501020307120f0e01110d0f02010b0d0501050405071e0905071101 77
    0x4511060003185100580700e01c4d8800308610419003040c06454010410024890343c0d0190128030007500070760388010700c0201c01a44034a843c41306100182643c01441d116201c000c01281041c020301450b00034101200c40c20394145981c1d05d492181c1400b06034050020780920a000904030f07802c3c41c030130340182c0c1080f40b010300840c00d1540d5401c0025030300e5200d8505002d140a0390280499694008001c803213a000d140201d0075016400d2040305801882c1d14020b2040c600e0b43ca00c144030b8180c6807400b032410311007502d002802c55860070000241440c00d075084490b108100081c502c03030024846144240e0401c5544031107240d49060500140e19600c292030028245138003404509500562004a01c0402d00ca250303100d034040907040d00107460078810b05400070b110760000701200d046288944a100440b04643c400851070341da1080c00b1941091800b1403e4800b651641c0c1004140402080113100500c10014a07a491909100d0032086465181c001d82082d00d40b1070010982e0b0034460316940b0440080f82008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 406723426 1250 406722176 406722181
    0x8150a14012003090103110d0c09050319030215040f0803040f061a010c03080408130807050405090319270e0603010515060d0b0402070506070207030510060f0b070609050105 76
    0x1a2045528100101400103403001c41140c00c1d00e1501d03100480300c42c40c1c60700941c10701c85941c0040d0003614140c414400020018080a41604c1c0c060107058009040c0d504c50302c14860508042c1420030104123100300b480031056000c000001d5000802e8a00c1d02d0701c48005956603211762504600c8841c40c1000540804008000e000501000304210400e9500c900000c000c642c0c0c0c841c0c042450f4907022209107010074651208240803d010340300c07550b406813080c40c80c2c5140103181840d840340742e038407900104c0c000d40c0140720030701c0141020311500d500301910000541c1802d20600e00010f01d0701a1010040800100d0860303569020003010070b4400303150350400c48250340f0b604c410350340c0320a400840d0071034883d600f46130110744019002c1c030700720580b000702030714007441d10031011224000342441c4109150015800c20003800803e402748072240c042d4403164060a0300c9441c5040040c94130400b40c0101d20917520300002040308101d440481d00881d000c0200300364980c00141890001082070303d03c09003455080104 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 406724676 1250 406723426 406723439
    0xf030c070e1003051c26060d0c05040f0213050301060f180e033402090c0903120403050304050a0e150409020102030702030d030c14041a0702032a01031a030a0308150a 73
    0x45c079000c500c1250340703014040b030b443e20b801d880b04446511008a080507500104086080004100c8403090090001c1c1c40e030740c0c3d95000814210744504141059070369000c03170303000c031049441e500c400020071040700203000b040c0c20b000d4102c400146510400c00c950070200d03010103200516400c084c4402c4c2d05141900d4540c500100411800220504854041100c00c0c0028000c198840301ca84891a00500044895952548d551000340e02004440d541b6101e0354101000c01100d002c028400f135481007010b5901c03039141c0000e00940c41441e80107001200b81160400c0030502255000c4405003c00b154045240c450600041c1d06620840c036019405005202d0712410094258102c004a59000d9654000c070341c448030f040c5100340c0180c0c0110146148111111210045401c1c0030340304075070004042d900e4203101115400c800f584085117010301044030b81041d628960b050721804807240941d0b01c0904010000a001984401d0004001018801e0440c0807490300100c40d440d4424094010b0300003d001620b554 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 406725926 1250 406724676 406724713
    0x30f010302120619150308030112050712241127150d1112070f090611030306010f121a030c010c2102010f050106110f030c070e100305 59
    0x7680100b1000c81c40c00c010388400581588500c8602c255560b500103c0540140074080c400d280380601c101d40c3c58088042480400198020700c2d002c10b800c542c04489103880c5003002500e41c0f02000b80001c200091000c14107020b041d840145d405100207010860403a004c10041050500c00c4171070140101c1d40805100e104d00e01d5104100c40400100e960395465030801c4030114a41416202140003804904403194154000000442d035074000c1c20300b810300803089501210021034449000070303a841d0300c644c0902d4210800c0b03005400c40b0700d0910051002084242d90324400540300c141008484130f46004d00307074070a412071444150f0b0594180708180c8a5001c6143c4136a0102c00b0b14442d000300742d2a102c0f1580180c810f0382509a202c601d0010050804890a141415030700155007036540321003400340041200e20034140a41100d8603014400c17010400c46500d031400505512079540d1040052202d0b035800025014120f4024107191240d9940d039900d60551416554030080c0369200340845002c0002001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 406727176 1250 406725926 406725929
    0x4020913052509050103032303150415120f0303050709050d150e010f09020a120215030a09020d060e06102103020708030d0b18040b04110d050607052703030904090314030f01 76
    0x5415040080007080f1523490703500c4151380320b540400c00543c1641c17490515402000118404100c10103e450b5116040a107045111108071019481c95040e8000c06030184103803600400b01d0b2920074029424030011501a0340c1c2120040c0c041200140309800804d02c64200720701c1d1680d030000030b000c020140c04010014001d001000ca11641441e85c02083e01419241c020454540082910302661200d030741546031075001038504404651169008800740e00c809141d024101e11401c4005104003110761a1401c2400140031041c41e80c0c850242001050200c03000641404048070310481c1403101460309030b1400502d6448038096010201c0d02d40d511000550191181c00810ba034112180c4900402e4102c10707241c2103c00900010520020034046918186042d0700c1d40c00c090703c0440742804503102d082c5051421603400c0001280064210402a5888910000300c4034003e1529803a0310000002074807400b03041c1c0c0c103500456403070380104c0516205202008040060300c903110307941d0400340361801410009 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 406728426 1250 406727176 406727207
    0xd1202010e0c031002090a2c150a030b0c0409050c1b07060507061508011b2007170307080a110123040b060f040c02060402091305250905010303 63
    0x280071900456040119030710989050007006408040d0b0040c0c1000020340150201c0c5422482500b400f04560b001c2e550101c0c40303140b80c200840300c00107100301c102211a4000f00910541081e00200c600b00d40c440c1038000c000d91350301641c0c01c11240c1d11003010b420745000e1f076402000054185010710204000d110b0003040000c420100a41520521101590f03554110740302d0303080007941c1003141c1404113881764401c000800c9940700c5464450303922100c150a450101d04a0000d04241e404e229000781e8005036400840c0a00000000d00f0201f070181241e1108071511038009082e0005840c1e48000c5c5044c4121250660310100c0303d80c489945041c0103101442081ca510515841d100b144214104107400355446000c025401d05e000c1ea55070390780c58002a070003600268102180c4010000660f9640c000c10200798600d5004104610342801001160103001d8907200005001d8910040880d5000c1504035501c00540403440c1c0d02148100e66190341c421507403001c10002e10301000403042681c071500111b120700a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 406729676 1250 406728426 406728431
    0x5060406061407151e0b0120030a1202090a0e010303090e010311060703020705130911060403020303040303140c010606080405060f010e13140d080f0c030603060601050c0c0d120201 79
    0x485400c2501c4200c048200350400d50b1080c00900e0002d1300c84060903182032900e601c08140d180c2e11113441600841d40d01c1096886584401c20301c80e49590100000c500260300c40c4040104c1d00a500c1c03115202c0c81161042030402401ca030400d044500c2e160101d0b0450f0001038840e90750680c4e00c1e43e92040083c42070104800080440340c001401201182201e41070b203402c00c620286080c3d0100c10418503600440f8114150b000f030134400141030f612001c012601c01d00011011074843c13113518001c1c02d8072242c0d507a00780c403a010a210910158a0000c280d9080d40d900d400c210105075a620605800e60103062019201582440000715889034402803450050384110120350711600c9003d04282d90642c24002d11600c004660b001a1207101d161a488000500419000d44c118184800080c1080c80c0c4490355000304240c2e800380b00302c110310b6582c0a980460310310352850540c103040000944845003d400981000703400705544140d40400c1c1310300010704200a00360040801145420a041040c0e000c00502552 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 406730926 1250 406729676 406729679
    0xb0a08071706101418100602010c05041404050606040f03030c0b0a02090d0206090d050f03031509040f020d080903030c0a0204060f03020a03200604080309090c0906030f0a0b1305060406 81
    0x2000014410f0040c8490b040c101000ea0408a1a000158525244590041500c540707808070b981c4140b4080d0040f40070485d0103182d18244100642507406049055040290070041084641da4400303c140c0302e440202d80c08101a254440001c08900440e00107140380d41900c1400800c05402146c06c01c01ea0344207280b8841075a941e422032508034080c880707100f508a8400e104440052030b20324014451002c00402d040c9651490351102e610b0182d821480e03150503400041401051005da00701c10a5103003084440308014a82a41d40000314008858000d008442000100c810003064000f45c0358a007401400f101c0c0c0314440d01340f41690320212084242c1c011841d02e080403d0b001b205c02c000e0001d40c0e4015141c2400310340345070b80b1084480b00b0b0a101240842c40ea03150344810f43e4400000780018105003004544641c1310780200842880040c0c400c008140d0104080003c6881e40020f90358070040fa01c140d11820750310080380c0030103000e002c6403407903009074141000300d04c240030b035441540280810340302085005d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 406732176 1250 406730926 406730969
    0x1d0d05121c110703081801090311060603030408120d09080a1206080105091f0204050901061205010b092107180204030b010e06010206160e0a060503010e091b130b0a0807 74
    0x7202c4640022424820401083c00403030b0159448a821031960018031401c038001648035421035001000c11400100b0b4000f21681c2601c04100d11a00104210041c501d050300c1c1881e560f070b85051030ba9900c0324002c00859100e09520381070340b084869680202080f96900d119001c0106200c807a80c60744040b0910f0a035001c03554107014171a0500c03a200004c0207040669030b2410002e43c4080c082201c900041d02000041950303100c0c201d4880c02040c1c6621415204c04500506c00251072058002d80d44560051144c9a0280e8a060240f035002c50300c038503540c40d100e44100c015810000c55421110b035080210301d00800c0c02d070b1242e0060086902800000407907076203c1041c07281c010416580680103a000e000032807042c602c064011410013006c2c1c00c01c0c600090049000c140852f28a5000d1000300300080010070800162691040d4840700040c05070640114803810a40180c3c41441d1280c00343c81a1400514100b1280c2c0c450340d088034000b0b050308900c6a0b90b160704c5039a400780d405030841020011608800300c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 406733426 1250 406732176 406732181
    0x1b03231507050405031c0206070f0e012703060902090901090506010506070602120f0603070605030408040501051b0613060b01230a03060801020d0c0e030303040308060402070804090c03060609060f1d0d05121c 91
    0x850520362f146081000404011a070b1042d5100c04100d811910200440103075580b034941174010740c031031040800c1c220703a540104401c02100901565003070341840c840c1d50000d500410840d05403003044650703a03102c4070a410804c00902803810050f94250000c000e00100c0a00007480320f12540e011821680200d403181400c8809001c10782d00203041c04420302003840558000d8015003051b0704a2507a1613000c5c0030503c2554a002d42c161440c1a01b0541000311000340002405080708012003800d0100d180481240a41510062030503540490600070480b8241c8500c242c002d48010801e45000b50b444008440365030005081004a8401140040c240300c11582400700071f0b00c2c442e542640b00c107005640d840040c0b0010350b0240400300c984400800c004520740440303100d25618a21103a6000509a0400d00c001d0100c401035042a010302c0007610744200065800382c501030480c043c205401044850319404502c2034100d40c90700070b04034001c0e40c40c1c0402e603081d15000380c11650f00c02c00307182d2541441807041004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 406734676 1250 406733426 406733447
    0x70f0b0a1a0303071a0403050702030d0302090a09020a0c0f1b08031c05090604080702040612062004051011151f050d02010e040e0a1b03231507050405031c020607 71
    0x50b00602c2c600da1040160b05502584503010342000c8e4905100e0b070b40020704003030b084140366002c0303680417460440c18140410b480003c0c110420003180360007480c010150102040c0c0d50000d20007070506002e0700030004e40345000980415006200c000c46611071f41c02e141c413500007500f00d4aa0020b0700701c076048012464062130307000d0341e10326001c1c0c0b2842e120f949070060307030f603115000907a085a180d840c0050b581c05461a503407443c0340100700000342510403068203c40001c17000c9610501c1c1c0000d120501c001c1c0d6600840d202008440d0400b0500e00150412807801c006d02c0d80c485414008055003004010190307105424404210b0f8200701d0505901e9508000c40000c1180010380055114010141c00d410035600071040c2c503041c41c00f1180303c00f042e0750700d8040fa01002c11181107140c904840400411a03070905054003210310505d0780710f0b03101e00346a90540e1481c03001c101001d190a410081401c040c0550200c602404029099030024910a64003d0345a5901c0c81013400502c1080c00040b01e00e8496100c591 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 406735926 1250 406734676 406734683
    0x606030411090709180f0c08091b030c0d08070c0602010c1b080c2d010908090d03140a0801060f0816050a0908010915060b160206070f0b0a1a030307 65
    0xe807803045000601001c0302000303040c030303050008100c0f000c14501c0000d1902403801400e1440031840f10b621401c00000c0d20b60107000d0740e090002031820300c040c0c2c941c081100c205802c1c4600745041e40512401c006840c00c00c0b9146540d800c0b1006480720740500010100601ca07950043c0c403101c00c51076486508902701e409180c01640000d81d00850b5580b6490942000340300c89000d0642941000000031826041618600d11480a52000c084d2740001c01040c06018002841080081040c501c0b04e0300d64140600c1010061803141041300d04c2c180c20180181c2c0c020540c2039401118035201c030746400c405850f160081c00344801040c2c8a81e00c0040c2c03944540010303231040c0b8400c100021b907008000010342e010b4200c0209101030001900700451001c0702489501d4246000740042000fa100440e1120216210f80d040851280c004012103243d224030f0080c4075a0b41d560540e4036560314025410400b0310034030305000c028014044c000500410b003155070801d5850b4140d400502951903082c00030542c2d244a00b08005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 406737176 1250 406735926 406735943
    0xc0509061203030c091f2c010c1115031509060a180b040b0d06090c0506031623040311030c01050c0c0d1a0f070e04060b040302040f20040e06060304 65
    0x3291001d03600d01400c8030120180a45c04220030414440c091101000e00220000d01d003100000e154858003880c02c8401260240100141c0030309500085c00c3d403627080c0c0050201c00c0c8244603882d464490503e80002007207141c91090b180e0804140c4e01c4409001400d002d4810031012002c90000c2c545102841e0840d001840c0d210760001050780a0005080f034400840e42c00f903566100c017078042d00e818404490a03031140f0320018906000d450208200002074010f540552828400c00450480c00b0424400c440c6131810b081140c107036200c8a42d640c2d035550a8040680e078501280c0041004140181401c802c0c000f01d064a03140100b400045403a8011009024056800852428410305080c0340803040240900344003481146080e0101d801d901d4140c0b104030a44142c542080720807039103d1144010300c1801c0f103003406110700d050401d40c4140074030b00020744503d50b610302d041d065090039400520012802e04100c00240081403284100e0b401c148900941d241d2031034001200e62422104581c455075000829 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 406738426 1250 406737176 406737181
    0x70b030105010c11040f0204090e0f120306060f0f04030c14030111160302031e03061e010903031d120304151403040b0c0c0106151e0e04020d180c050906120303 70
    0x2d4064a206403241590170030b5883e142e0200c0001140014005840f03800c00c08180300341d80343d00e540e150200c1c8211122140e04200b035100c01085507941240c0d00240c04076074813078071000884146c25242c0300340030b9110745074040042e00004206180302514100c803024400241c81018000500d402e0391110032682330222800c01100c0d008007050492000d031603000784100c03403c05414072400726681a0203a45440e840f0408410890103103020881c10003c450381c88401d000c4418994001b805c808030500000303043c050b828442004a10481c40c40e034000d40c6000781b6465001d1141511551a80c3c064007400c0080780700c03020000c02e6113004500400b00052a4000d061a60740d032600c80540450025040104001c003c00c03000541503402d00600c0f020300303200c401e06040301800c0304010b494050302c184040b20070b02d0074132400a40190090501c003848070007070700d0140e41c80d1940c82c004c4008140d4108640149494180ea4009114010640d00103445080d20790000300e440c5c280420580c44c001603507040d890ba004100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 406739676 1250 406738426 406738433
    0x120b010c080c010902091003050705030d0813021503071107080703021c05030906220e0f070807091203080a05090f121e030f0403030c0908070e0402060d0617070b030105010c 76
    0xe0608030b20703080001460748125800908840810b44110802c0a942e8000b8020300005006032402007804400030903015010300c1001d40002001095041c02c0c00791075824005540310880350103440c103d80f1b20840d07034900e401c003c090042e288559001841d4421040041a10280002c000c0d081e603070010450b485108403074030705010710b4080d040210b42d6400180700e802540d07103d00000e4a480b55002609207120100940b20500c4500e4075804442d42c64000c0050101c580c00e482c07100ca8010f030b80351912070070307540e1800401d903100c1b6580d5020b9100b1005880840b41810340c041000c500401591034140100d445000102c1e5484103c0c00044000b6000102103c40000c0c02400600800c580764284408065803200c3d22030064100b107440816290302c0d8010401015894810340d54980c03e1402c00301e00c411300705920303560f540d4100e0003580d0101c900f40d00032509654d40e0b1016600c40740c401080c03c0c4100e50b1101c0440c5803a400300035000c2c8e0305100d82d180220f0000c0e458400d49060307a1040e9504503c031161601d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 406740926 1250 406739676 406739693
    0x30204050a020c0105100305010c170c0714120408060c090a0b1b0d0e030c09090601051003090602030a090203120307020d0807031b0e0a0509010506030a09080d090c06120b010c 77
    0x51400801c00d40c204007043c260f2400380260b500c98000b1540e08501a461404d00c1429520140b002030304100040801e00c1c0704929201800703400411242c141620b5045a1030020404c01c400d10312107601d4801d02d50300c2c1c808509048010000c0c1c40e800d1003500c400c1d031aa506004514000c1081030740c1d100940081c24440460f082018002204540384c240d00b50711420341c903290038001c43c0d0140c0e17400542e0301c15102d01c0600b003c008143c10043c0036503c44c031117403403c0108103403580010300070180b080c13803007024a40748144641c1001c444c0c982c01c814110f47d2405c01419a000401191004a00070700900c04000d004940320002e580c8249016005460700e02151081111007490003444c5405050380c80d428094908440c164215403142141c841c410500c00f1031040141009895020a2282c00e80d4001803040b0b450391b070305603504800014404a421111450540481e02844403000c42152070103020070280a180c2c51218204c41c081e03103e42c054000c40c035003201c0a56a204170744034045210035503018000f80c13040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 406742176 1250 406740926 406740931
    0x60f190b180619080312090c100f020a0803131a040c0537060801091118011e05030f070903030c0312060f06030203180d020d081009020d0203040c061803020405 70
    0x3c0c0003151202c00b00101444040c181c0d00b041d80c6680c0b002c104141c901822600345070b040880178006202c018081c80000711408103000160f020803144440702c1c1c5010703008000a0b004240e02c54982a141d2505d04140c403610b10320403006880000176207145c2030750103015034015409103030010603d41005090000340f000c1d0741401030049240030480c0b00f2080045070342d001414400600e581e41d0900301032030300400074108101a081000d421b442c002c510501407c0b140c040b501408480c11030413072600e643c00700680710b48a0000810414901c0f4a4200300300ca548200190320458490640c40c0031511180000c032480204c0303000050100c1e611a104030040382c0610503800103201031a401003045500d070544816519080d511160120360080b0a00030342c1c62480140b8000c0032a00c000400b000d00105a000f5603071101c03591140c0900500d84041042c007600d040666010740b6a000c01555030f00c203410800710080d4001c0ba0280d400110780314000c01c1c140d100301400c003841074003c040244800e00755000c000003484003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 406743426 1250 406742176 406742179
    0x90606080a0c021e06041a060109090f0e1e0607031a131b0e2d090702070302040204180e01060513180f05060708010617040f080903060f190b1806 64
    0xc0e83c544445004440c5001c00a21001d03002818860a05181582d00c40c80081c4812850f00c7c80c4908002040c1d80c8001c019084448540f0041200c0d58079802c2c000c0100303002101910a40691b90024100001402046200c030880da0100d8516607a88201101100d40440307072040111504001d801683c5401c61078008c0522081200080c54401e128880108185c9410400c2c00704980220f0f80501d8944440b034650f584255100d840c2e038500815210203140307040c0140992003280d0180104a049200300300000103942d016000311742c1c49031107001403403100e0b10044a0408aa0920900c00c2c80003106000700000c48401400b0644003c04c0880c03024041e00700c80604401e11449002c591001c00c0c0500b1080311038501601c00b920b00c908084800410100381600618107102001c0000c900c1c03c0e038408101540710b074004540000e0010545045c0d04030744140e103806907041c4034800a010344000076844017401011040c0c4200e4801104c603064405541c014445076504c030408201580b0200c001d0f44095600450 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 406744676 1250 406743426 406743433
    0x607050c0a08030c2116020604050618070902221728020315010501140c0c0910170607030b030106061209060b0d03050a030c0804050c040e010f060b090901090606080a0c02 75
    0x31440b084405e0800d4411007100b54101e13501b801001203613409620306998080c8090480361415840b1a660b072078010380b0200065002c83c109050240342070200301c002e0103c0c604259600d502da08414094035804101c0d0041c0241440c000191050203440780b0802a40201c0181200714503030095091188900406201031910101c00500180c2d024440e04528080d41d40d6068125410400010b19010030101400c4400100300100c01c0d0180000a0b180c600346000c40c0d404c80345c1e642d00c01c50a20012055804030303406054103424908410400f0035100c0c842c0c0c072555800c206400c4d001c410107007a103020b0711401c00403039180f0404000c5140c043d08080d15250099802044c0e4201100c04550700d800e0816003500010400b1804100e1258940541c80b00e2200030301c1c6c010740c01d0802d600e80c140c03620f25440609114680d10170807500c10790001c2d00204034012940c10108506584c0c0c01000507154001a025881010400c0005c2218170491041c2c0c000d4682d29550400c41d80d0b581000070b0f000380010345000c0103520 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 406745926 1250 406744676 406744687
    0x907020d08071b0b0a110a0801091503052119030c0e09012304140118050a061401080a090606120615060e121911190b09040f090807030309050607050c0a08030c 70
    0x4801c030000c00e0b00c11003230303954000075600d050b808030111810400030032101003031101c003007000c110b000a1092524407130b45c0c3c01d20740403400705403036100ca0b11940b0308402102405481c43c01e00e4940544c85a2621180c41d100c4c21004100d00040008000d024000c0006500001b140e012440b07181c401802c00400007e00000780f407040701007608403001001d90002d91030070003800c100203400a40e40201500b2170b03001c80007400007606121000b02c0c9481c00401d1281000800c20008201c0c085980224039810780240040060035242c56032121564801c1c2801d5034481e0500c01280f2481188002c2c1800b20340d020340d240e018490030002049945054010001e105200e48000750030000c50210340018000c2c82040000401c400140074040e00c040c1c2402c00b0f50f06607040b000300b008580607100803154103210444000880c07000c1d081400300140000c05001d8403280021851004141c0c056121172a220702843c211505a9500c1c08103d03103d10444000c0d40f245d400c118404400101d500e80a5904060814125801c01e03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 406747176 1250 406745926 406745951
    0x70f02100509060105032103041205090a0905011e030507030201050705031b0307030e030102070b0601030f020c060a0c11160e0c040512012918040206090907020d08071b0b0a 76
    0x2641d007030314401c0d543e4000900400080c43c0800c44000e2204414280e01c2801c41500c84408240c040140090120f2503600900c40c42a803040341150b81114006003d200e6442c2c0300c90500c00188800d020302c1c1c0c1e403013580207000340c5030140c080d01c0e040440394080018a20681181e004550320303040100c0403221071206115800e00104110081b14000c10000300a5480e21001e04005100d0072041000c503011341d1040240101054454100c3c7d03034040000e0902244543c10355204000a11035242e440929028140912101071883e400c034440292032640c1740c0c007190200c141745070b440380403100441c080f0fa0f040c82d030700700034020b080c080155004088000345800c2583d10f6012500960402c80c0310701c185d955401c06030140404680c40d0170000c0741c035603009a0700d0700c10001c08541c0f010308940740b079040390110000040840d61100c0481d42c400300054001031650601e184069030303a1031580c00900c0801c1d00740000640b040d2003422242010f003a07900c090070356144107490380c0410400180418900e6911100d221605 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 406748426 1250 406747176 406747181
    0x3030f0d02130e040507091109090603190515011d01030b0903071e0203010501060e030a060b030c030d23091e0a05060406050a0e060901020304030b1306050f0108010e06090303070f0210 81
    0x41c003807034a40a086141c130b407400303e042014030b412420b9000c0c40d0542c018070b840008801c1d6504003806850781d481c2c1d91074001c00645040380203054100075540441d50642008808203490400c4402896407005907600c4000a1081034148860417541074100c200400200c1d52512901da0401c000c64240c83ca800c00640b55400d501c0b80c4500507403140404c54605004508007442402d006100703038a00368400c0819a00002c1e02d030208624054134454481710b000d0895a003e200d40c0010340381c014111000304000d8400541241d2a0750944004242c84c19450201c01c1c860104490046030001c041c14035001c0364a10740400701c18442c050542000d210b40021815480d0400140050441c0b40c95140d2202c200172001011481d008640c580601d006000d01001030b600042520140daa00c5400b8607899a1081010040d04c8003400c0050941400c2c8410310840030400707040301e41030700c0b1400c0007404202c2ca03113409907230740c0d00050300e0004051b441080050030040c03040280a00700d902510540c3c0c070340008031104005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 406749676 1250 406748426 406748429
    0x1e0b01030609120305040c12020103021c091e050a03121b0206090106060216030b07050c0102160b01090510140d05100e0618211c0608010b060903030f0d0213 69
    0x9280e076442100e60b00340726004802103807034101480e041c0003c0c900350340d940421800a102d501c81129244111104581c0240c0546007603d00b0700090411411010b86000c0141a501c20151520b0840040c1800d656440401c180350042d0404000c10f0161000e0343d084418080724003504022a0f51014503030b12941c40e92491060b044000c0d80200007506141e81107500711900b96208805542c040c1d12100c020f42e81d030680b80c90450b0b401c4424554280e03600c0405491620a40080c007000b54070005035141114401e1444498082c01403400e0350b0503a807207104000c22100181c43c1e01d10a207070300c00c2003000216100c640b02810010b015114000d10310550b038074940b8203c1c540e14411071045c0c4500c80c24005440820130140e2007450540341000040b07032458800c0c3c41e03407512410b521408080d03040305a110882c00d401c4466003000c1c03120447d81045000130050007007000c0e01506007554200300f5540d08900e032a4041d03c1d1030720002809140340210001440e911940b14040122000340c0a010a10000111851000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 406750926 1250 406749676 406749683
    0x9060112090c1e06021203071124070f0e130f061410030b010c320307050f120406030f11030412020609160e061207060e0406080309030a1e0b0103 64
    0x211183c1840005242e40c80840c0600004000c5114200007a80c4d0001e001c0000034103000b140355498858444c102c501d004c02d0b00c40000c2c50312800c610740e24520840c40b59202d140102c20004469a02c17107100803504d00c2000580500046e103d001680040d1800d521601d0034902d00000c00100c0a20814a40b004e0b0349040d440a2381c024038015901e121130500d041207050040039442c04100d0300c0007080000c0c1030a42010030281001201c980ca14000e44081c000c800d000c0301030407448a80c11000d264480303a03a90b201c042c080b15a8042c14044d4040187c00003403824140c8800d6003c2030a05080c520304030010b08070003c0078444503807911080c00044090000950140e4028984e04603550f22070f9602070305d44080035111400380d51015407c4d00d80903042c142c2c1241a90b0582c00c000089844140029403c0c0341d24204c1c0740054062044005446604a10480040c3c1e009980605c11240c4d2242d0040d00ca0060140d955095006030204000145408084c60410344503500450701c0410540c42d8008151030981084 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 406752176 1250 406750926 406750943
    0x102190e010918020901140a080c0c030409050c0703020c010f0e130609060312080708060f0603090307060c03022508030109021303140102040e0a0203060d0206090f090a09140d0206060906011209 85
    0x240c15950b0301c07d8003000b050701020401880c1c10344800c0b0082070003100402c110116900411880580032041c0102e900410700da0f1801c1c042c0d401d00300d801c440d00b0741c06000302300d000d0302c500034114000d0b5011b003610203201007141d19824401440402440f80040d201c00c10303c18140c3c0d03510408148001c0303a200711006035001d84400100080b1664000d0034000000d01124248007c06c0c1c01c000c0c0702d658500c00da0000581c180c0e891503d076202c3d8113001c0c0c40c5005400c4001d01d2542802c4451440f154540e0180003022000c4500071540d80900e860300ca00c3d000e00705000340c403a0f03104100501801358075030010050602000c40c0182c0903603680d200c40d0900300c2c1420711507516940010301080300640000300300b81c104840400451039414848009055486d14403c000c0c050140420b00140c06c7d6034010403c0e249a00c058030207025490810142002440715650880e04007504c6198401030523030001e40744c20907135125001808039442d80b40030406000c500400c05da0400c0100a0000c00715055401030524292107696507 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 406753426 1250 406752176 406752187
    0xe0907060f0207230a0b03040605040c150c1412160c0b0301080d0f030b06072d02010804030c050c04060801020307080606090a06030203060a03020a0e180102190e01091802 75
    0x41c0380041c40d1100008643c070980040c4071409218150070404507034080802e135005551004100410030320340c80342d0344100c4088100b00c01c2c05032030341040d4403880c4506502081d068a64081c480d44807a854801c00002e03603030f0341c0e51200090f45000e40a001c00350390300803288404400c14440805900036090b5810f1400100000c03c05c000f1045654801b910080886034115810a8401d1783d50768192136210041103d140c041c035000074002d901080a60102501107a80d9819509142000d5041d20345400c0d42031510801c07050203580c44071040c1d181c043d816540c0c2c81180c0c803291806c07076602008500595442c0505031092403a59140d10900300103200310b13400561640f074500000b4019080080a403400340c90104100386041da119075292050340c1107800d00603142d0310f45402040c0a02402d81000790861850907011a04015010040e44601d1030081841c601c4400c1030f81060a03400381e45000c0341940309005018416501407a155001550185051b4440f103903911a066503078040d400800c2051640050b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 406754676 1250 406753426 406753439
    0x803071203060302180711190507230d141506010f140f0d02040810090213090b01090b0103380d0b01090504050703080f04060306051c020105030603070e0907 69
    0x200311408a54241085000d24540200f0701c4409581900c030b2105002200046200e0b00419280c140c0d010744070101c403440c00d80110100842c500c603101c1034540b032103058000680d618042000b400c2840d680160035031155901340c00e000d580340f90700800300d0704036410f0b50b1107008890040204000c0100c0801d44039025040c4540003500500300039410b40104990f40740d5050311a03100c0011900710505002d03c1d81d41e07889000600500902498004405c14091010680d500703803200c0c2c000300300030390007183d15405e0180e081e040c2c0320403906240d9005005015820040240c100380e0745c03007544450018140031503c00c1952080c890402c0c00c138290a88400040484030003d40043c83c400511a00203850344840c408080e1920944ca00d03051203134910b01529000010100082441254019680015402c0e03d9524110f0800100d41240c0690800a8602400081c280c9841d404d680b01e840f8444841e82104449034004540d90391005001580600c608a00014400e1150307172064030501b518005012920704011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 406755926 1250 406754676 406754693
    0xa090302090603060f041b0f150e090405210904020310080601060302090307090c05190305071218030c14030c0705090a2003060103060b0301090507090f1a0c0a02030304080307 77
    0x2c00036402a88454100806100100c01c3c00790055000780301d400a078019101908501400e075086450a002d01a07000959413074044c1c80042d0801654481a01025900d81030041c8518200c170060210790002c00100405502168500d0160901e20842407800921501040680e07005441d01d0202036030f0139108000041e014800d15000d40610300d410340c81c1c6620400002e0792031240d401541d640560b903400008400380118121903440c01e202c03a054003c1d0301260801780050104540200c0402d000240031800304002e8481c1078008004030140c0540e900942c2ca00701d81d1102003010880d85182507400c9010002c07010400b4005050114004254403824030050001d142c0015080f071102900302081031070780e450500710110219141c40b04051b01c070358035040100e001c0d0240340d0145007580750000000c60020710350707040b01d8416a03550f101c24900603074441818041c04510704c07030b000c540f002500c1d025501e035080c4d100a0500110003011503056401c543c001034107582c89a800648103a01c0000c80808100a80 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 406757176 1250 406755926 406755931
    0x60f021605060121021e090709081b0a06030b0d050304090c030b04021e0c0a08030f04051606021c020f03030f01051801050a090203040201020118030e01090e0c0f0a050408030a09030209 81
    0x80c2203d00d0b142519441061041c02010b0000d20034070020480d0300401c941c60094403001b20340105205002d040261020f011200340703025459aa000d810240414000b82c1503030709189800c09000300c50303182d00d400002c4000b05208100d00d680100c8081084010940400180001d40ec84110010701c60804007005800c07500e0305c0b032107503000398014487d4025004106055858000008405590354400304041904042c80c1c5003008000300c0e03006c000d018004000580e0544074034416401c860080c101c05060300d0131400c851003204016444a11000100d1102a00496507540940126001c4e00106003c10381590821520481801e00b40d40c0100880c1c6002c407013004100c01c08581103816541031001040803036040b8050001d660350000082001c59100354840b4084441030341c80304164144078500286134415203040140040d07250310010a0f180d590b00c006070b0044203e014039604e03280340c9a06100031034002401000034010103010010f40c1c02414401092a8000c40d035942d4034041c1144100013248002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 406758426 1250 406757176 406757189
    0x71701300c0605220b120c1201051e0301020c030c0106050a3501021801030b03010218090a24061211030a0905160b03090f0a020616060f0216050601 65
    0x8022020380400c105640e41000d40e01185020759880c0440711841540034040c00905a282c004070100040c034a003460003504601d8444001c820841d202ca11b04410140100056070800c004120010071140ca0440740c3c038214060083c0120020121010000382241c0003806843c0482d0000030721034207140c43c00c1c4140d202401003180e034105038034103220a40c101d0a050101031074079001d0003015107100070070b8200320700c040d044107900940d9503035401c1d03500814001107116010b01080c1020b01c9001c0c58503042c001d849003030240c41500e40791084800c041002d005c0002e0520007050365500c1d1079104483d50b04060540c110703035039450401e544e441d0000042c6400b21501da644d036000d140c50203841032240182c08a0340c2003450041c01182c3d80c034031801d10030300b0415040c2c0d52990a100b500000191042d87c2e00145108081c1c00b416542c8412000290503113803000f01c1e50096210b1700c1000226182c501140312180403902074030001440d03186030400c0350202d80c001c103000c1c008580d000c0451400c1040410406026201 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 406759676 1250 406758426 406758509
    0x703080a11070f060b0102010f09030c0512040b0f1602040612051c0f1d06031e060d08250b0705040302031b0319050a0b040c0338071701 60
    0x110f40f29100c2c020449040101803548a1441c586144c0c400d420200851607084c2e42004080c0052a000e00109803420040780e07940294440b22850400b8902a2400c440d403402007a440e050303807000d0181140e80700b001c808801c90802469900035848030300c0b960000e00120107400d9092407250418501d040b003580080001c073f80d0020384071640c085d0701c8010340d0694442802e00280301d114000c031041c1400324001440b500001701000700038107405865880d0b0712400604000c000700303440302c009107c0c1115104401406034a81001842e806241201003084000206c0c131649400070780642e01c0713625600040e15500009400400d06209500d13042c4a442c0311064000b0030002c0f9400380e80e02107616140c005a040d144421a030300500c051100a218958070640c1c4a850b20210b4a071902d0a5021440c0a001c103442c820507030f803078000d283d100d4029010820108002070610002c0c0210206644500042c2038008008024202c104900080b401c1980a04030341c51445030000f80c2014080c04021a00a9441c03200c103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 406760926 1250 406759676 406759687
    0xb090112153002030703030809030d0f051902090f060a17010602030a0f020f0a12090b030112030e0303031b090f060304120318030504350a0203010b0907120905120703080a11 76
    0x713800284140451307506090484066403060f00c0c10b803d5000d010700309a00941000000342d064070041d800181328980e440c61904485054000403c100d0080c00810764000410466103039091a102e0040c2c40380c102c452a01c5606202e0b103051403080e85400f80e01c00c43c007590010031550581c0350407036050041c2c0300c4584010b00d49030404007100b555441c0d2900d00988040c3c0c0b181c0700c2500c03140c1f18142d41d001410410703514035500c0d40e44805c01d0129100d1400f0540028a14000031243c0e450044100c074014403da560400010f5001d04082849034417181c103a80d8401d20203805811103842c1d00740a9403040780107a1020300d80820b009800b9007525810305a841c500034500003428000786c2c20030155403d407107140004003898491950140d007100580540c60951074200190114041000a0049074061083d0300900101544d101448036000064840501046208040b0f000c0c10086030300804101c0c0c007031402c403034180c5a2110700b0b840691200b203054001814110030440c107040c0c1d0f4010038860f05260140c903460032 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 406762176 1250 406760926 406760929
    0x5010c05060a0905030c0708150108030a0206071d130f0617120711030604080406141305041a061606051e061c0222050604060b090112153002 62
    0x2a01c0040500c10403035a28002c40091240403c140c0319843c3d0050f049a01e55034403441e0303660340e0b040804076080035988100004136201c503020060303542003c0b1980043c01551515007003034448031507d5102c0d98501410000c0c614996541c2c1e40020101f040c140c00c00151501d070544024280c60f000d0b003182680c0c4613920440c29640707100282e0340c01104071000c40c1988844603460542c1422144598482e89403142006000500c91844000d00071582c45e903c07010750700203010780c0207146030144500d80c1e284001e90000c20130050405030044501500c1c1c0c0301c90309a681c55100d0000701142c0100d100c0284041d1280c1e607101c01c000c0d0600c80d140d00035044c0400020b1208101c0d240c41d92040b0700038600d5000d0019002c0708008200c81c83c88203415079500604200c41e2030f144040784a100414040c160107035030b0a05011411505043c03042505a417a00c402181c5002000001903a040172840c40c120860386d03403072502c41c500ba48400083d0b0090003074017a0444400e0031201d1040c420010759164010b4010540380e1b0100103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 406763426 1250 406762176 406762183
    0x206070c0c06051b010c020c0108100e071419020304080f06041106070c0f0e06010807110709021c0906060501030c0207061d040603050a050622030507081b03040e1005010c05 76
    0x4490721894500d6032030a05410342d82c004d40701025410306541c2008044585240c021400c41e0190000703aa07928120b6680500c0c103554062684200400110300e480800d5200784034150280110901c8002e0340d00e003100303d01803625003090010b02c0c0d03001038002140510015105012000ca600302d07040061485040c2610f03152141070110b102c043c0700f10000603210080004030a91030f801400b80c5a4000002036548994111882d02124804c1c00904400002402a030054045a800140c410f0042c6002c50a244030360b0001e40c08100c02a00304d0b508480e10000c8040c0d1030054207001c600c51000811050324060001d802d0703403c50b04843c4255048480305001c0e01d54840e0b0f62084560940c18403000c00340c04000480c1c014000d603000941113008081c014410703c440000c5050080443c210500c4450000c3c04100407803240500000f00003d80412080303001c035142402504540c1d001001c0c62001c200c5052850386140c0c0260b001a88500300e40c810030441c0c21303a03005a00010042800d01c40c894484641c1c0785601d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 406764676 1250 406763426 406763429
    0xd050a1b0b0405060a0903020604060201021305060301030f15060909050f0706030e030708090a0b07062307021b040621140c1807030902041d060105190621050411010206070c0c 77
    0x2132403000c201011024800d8914400440d00034003043e680f6903c03068000e01030b6100313001e034480040f81001c3c00655801c02c1802c8034126034000c000480c41039904e58401d850844000c100d03941305a00d445000c0f4035002a03218880c2e42c44c0c81500209025484030041c203040045542c48482890310703290001078070b20000b001300c501c041c2e4080d07034132a030b5403d20340d0015803e03031503a03048a02d45150202c0d0201c00c01403203a120071002c0a0700ca0f9402c656000c00d2a803250100d408503041c3e4010703044100d010700d03040224003160440c260020000308800d600d501e60090b444c0e8400f075061650302943c40320307c03003800f81c02801c00b00101c84142c090400d941c0500041030095203400c560081c500621b070f0004400a20a40c401010b03581e00600520409411aa1302a0f00e544100f44915180c000c5a000080c80e29243c0135114080007100b1000000354a006801c0e0341d038a40d03400b840b040c040c124031007110741d403e49403282500c603c3c07150012603040c0c14007070300081c0307042c9008003213405000c40012501e0118180d414000e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 406765926 1250 406764676 406764679
    0x1050601090e07182705070e040f09081206090f01150c11130e15130f030507080a030c030608030c060f0703111c11270f0d050a1b0b0405 60
    0x2910303480701442100c040441c0e81c480b01e80f613082c00b5400303e45d090401c2c038804142c0d445521307214400c1c80810030b6501210020349503000810035001c0e0221b0b1900741500409250020204009455040c9d61591003030380d0300040011449100c00406c0204c1d030700e04841c0d8140c101407494520b8200358140320589203070040c208000010301c05c0c00e44d4042c08000380c40c00f5070a0124000b0349000403442008907910081c1c0600b071000c04882c001c1a060071441036074481d2140c030482c3d001e00c1812500455403a20810116140300c15000c01601300300035400704070b001008000807942e655001031000f51102c4001c0848080b6000000341d82c00400c02e42201c1440002c0103500840324041407616611801e0080d00100303008451641d100401258221280407a0091405000c0b0074400a115507500c3c1291240240324108511002450030090214102c45050200c007140c8006085484031100c418001941c2c66400903040320181c0c0020f150801300f1244291b80191040c0e060164583c040c03c1408050392400b0741d000b074a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 406767176 1250 406765926 406765949
    0x1704060203090118050319060606050c0616030e030406050715050105100806040627060906031a0709031505091c0c060b0d06020f0c07120305030c130806010801020711030105060109 79
    0x10300d940705034044d44000704401800c6410b41101e500c051305000e1160001610b19034640400064582d00407030884481d0800d6801400a03a84c504d618203c0c0d80341c5c87c0040740c04240d510300300203003011020001040901803a03254a616400701c2c1c50b08400300c8180001d80255181000010070641d2a500580700100c80d884c2419242039942034042001031505900041403900100064510400180b0200c0c2d901c1d0344114042c00327040d1311041e10406039516072000428015032040324009680340382c11603903000601450004070a907a43d458103840301407503d52400300142c5e200305210590078100221400c02060401c54403081c481076001802d03100d44004042c08040e114443d4402680d185401e0180d8558802011911044401440f100d103401c6022210442e00c909840490710f480007403003906034194980d13205841c6071740303006120000e80c000c10702112100c4c00400340403840807000e02c2050b000c3d1050400060700ca59040c2002c0041c4400005460300070b03494541404201d90340200c81d401610083d9080c1c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 406768426 1250 406767176 406767197
    0xd0209030a02060f130e0709050d0507080607052503080a0b0406030605090a051509062205070603020d0b0603090a06110c0303040b0f0c13060f0504030605040b0417040602030901 78
    0x80303400c050007400000c0d401240000d0102c2c0c404130000140880103d02c640404841d9121310340700c4103858041c0c49090208000d03030002c002c2d0b403400714080307103941c0e00c1346003a100d281d5a02c440302d52400c40b058400d100810004100c90f00d80c600044134014041800340214544500d1a4402910800026042428054443c03d40c121603840b01c0c3c1000006560103070080206190080c0c1d0542c4517240c4110440d1680903032500060001003500181d0f0142e81c845001c0c00e11510740302c80444045003001c440c0980c0c9290f036403601c8003180041c00003000070403081c1c030b0240e1740700109168003040b105541211480389c0390a0045c0050720030000713901200d082d0f020100161510031100c0d21201c50042d258170038035a00c030000400c800c0202200c002c81c001c40c2210072140442d12000c402c80030034020352a2440c154008120100300031841180d6160459500342062071400351641c460005651049030150385c854184424441003100c400702402038135170031103005414542440c0b1b000392070340b02d4035001c981000540c200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 406769676 1250 406768426 406768429
    0xa02030408060411030d020a11060a1707020a211407030c0206041401020d0309080702101e030b030f01020406020703060b010306090906050603151b16170d0c02120d0209 74
    0x100d4000e4200401160818906403401959114680310503900030701030250b030103c8060000414140040e4400d1a0300c9000c0103040c240903071500182c00c40707070030004c0500d9009811412850114020f417a070794040c0003196140d052104103000d0030388541200e24070f075006854119500441c51094614a807082c0e41e55907205040498241164840c041c0d031003a00040c000640c60740224040743e04500c00c1e000d8070000300101006404076801c0e0840513004240410200c40107140801a107a100c2c03800e030031320101012000c40d100414404001040c80400c0c1d6906030031a880c0f4003044100c0e1540e60600003546000e05040009440e0000303444010000e0340c840b406000140c1c02504040094441c80c1d0081201107a5420014080d02080d103026000307020b440744250907001c807000000c0c032598617488580c64013407035017440b500540d208020030180c664041002000150381021a1300d8540d02c0000c00c2038032141083d844508031001040c5540039036020b000c020740011005c1003652a10038400e040142c903010f10a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 406770926 1250 406769676 406769683
    0x21b01080c04092a0305100308070c0e0a0e07080a0c2105011a090a050f01062a03110709090308070e0609100207090e03090a03020904050a060e0604062409020a02 71
    0x300300310303202801c00382c11002c1c8020541450014202c040d4840411001151058007213800c10341f200785006214100030f0000c200c0301001804040d1041c5c030400e25456071100d51008580c02614200c2486071140b505070300c0030208024810180000b680139255440e40c41c0c0c1c1c0d080311440c00b40715041c4100170610440718038002c011013031800309803c0700080c0508040381c3e150081202c3c402039071030701c13910042c80401c040a025202d0303184140482c20803034010746d0a003581070341c03d03084002103203000244561041d103080405180c50070100344241c85041d500e60a01840c50304020032900308602051505402e20046076000703d15a42113a0700f03080c585520710a03140800d82521030800b50035046900600303440140ba034009200c05c00c60f4481c4804002c103140841c405500c9118202456610200004c3d090003d0b2400722000c1e5046031203541111701541d569941e410503181e2159135100160415030800c03040c040e090040000f01000700c40b0303901e0390103004001c420b0703100407034054449103e501142500082d4000c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 406772176 1250 406770926 406770929
    0xf021e09130c3f0203070c081e0c030702010f08040b0105041e1b0806010207030b0a050a06120c0503011104031208100f140a05120618031303060c0206010501021b01080c04 75
    0x80d85400c500054035109400c00500043ea000041010300003501d14000f100e02c280d9009202541e40d41c40c0c0c1945545520038950041d03403600e480b4048602411820b00000f500400d509541a0041d54031071043d80009009201c0001e141e00511404c84100000038000e0078515055400450700010101e00000e5111034010300703c40005901c1d803820a03284c84200d1a1055030380c15400617501c0300c1d070554403140120303280c1c1030901c0010902207540d030209030030402c65044141e0141c0040c01c00902c3c40c0d038810316000f00b1103507000c0030fa0751010800c800f4081c0342001c0c042c0c103110508082400380b81614603504c0721150085c01400600f04024440442d401c03d2295030790100420340c44011650840e1154118022601c01c40344561044604200c00103650401c01840503110340180c0107000d6903660400803061503c65034000c01c0341c600040082d4981450684820009540540f200242000c41c58801a240003c184c022605545c02500c420b048120180f0445008413002c0c41d0286054881700307000041806503 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 406773426 1250 406772176 406772207
    0x703091707150c02030c010b0a05060f0f0f12041a010e040b0714130503070e0103080a0f1e090612090209130201030b030609391011010f021e09130c 65
    0x900d0b0040f54107035800006003603c00c0d4040000c11441a0800801002c10424440e103500000c05000000390241e500003d0440f142e9020005c902d45181110590241d41c084940d5078501400741042c0020b010340c0307401500900084a40ca2090355060140f80507074810003c000801d1044068005050340b07200311400c41030700b00b80c00361840d00e40000c9801c0c800038090b00c3c02081d00a00c5800c2002807502d40345d042d010304807500b00380444d26044030040100c07544a070700c01340c1200340440d01c0e042024100c2e4014803a0840354440d655181801d04240d030003003403542c0003003080042504000f020740150340e07800b03d201d80023108008180008001e0b0b20051f005005580e2840e50b05004031400c2180b40c46000c292020814024002c5011030400c1004c69401024154154840c1e03140305d03121800c90b410008841010081c1c5030130000b031301000c1801c640e0f00f0351703040c003103a10f500030b4010460030302d0164180c540d07514152540610904109021010580c1819880225a46144c43e040c807140e0180c002c1e914024050350 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 406774676 1250 406773426 406773431
    0x2090d020a03050105011401210513050a20041a10030e150f0f0906010302010819021603020f1506090a0b03100c091a070204110405030d0e0306070309170715 69
    0x1982e00f401c9000748400d10034081d14216075140da04003507104441c048110a080e06030790f88070701c4904640710010840100f000c400c0080c1c223005800030030010090031006078425003200841c0c0119880c99061020351a0b056401542800541ca41c100841607070800034280a81d00006500c6840104802800d2111800d0810740511700e0200200b121340e110581c0300311520450a1a01c2c0c4405141092003241200c0029440c0c0103000103100641c490038485030040c14602d4490590070580c0d00c4003089038044500c10607003908a00e054410160107103c05824a0404000785c1074900c00111300b0480184002c0410703204d0040a0009100141e103680702182c09035020741140c0d4100c1209103050028035030410a0004030308502400103c54a11040b507484003000e07a0101da060002682c203000140910308164808140e0500020440b034608201d9460115020303950140780c03080b20301c149401c0c154041c01c010201401c01205002003210384040c1c03020b20340341424441c2e80d4825410b2200d5602100ca250741c2c0401d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 406775926 1250 406774676 406774679
    0x732130e0304150503040506160e1f08090106061b0602040803160b0c0708070303020903102c060601020705190b030f010e0f240109080303071107150c0602090d020a 72
    0x100e00002078030544100240980c59216110300549150004450050040d404000010b0558040d040b20f402c0c84429800d02c501c5e10241d000020301c058500e01b484451080010600d071240650000000e0340120400d00204007050a0120080443c1d018154200c000101031940704100502941124010302036401640e031076030074038030710420503c640003815075030070005a000c00c2e02200c522040301d94140c0d04c40038103450828980da06501a41101507000d0741401925a956111035442c016118030b048140d03e07002400b05148030b0a0441f1500b1a925925544000d04200450340c0010360b110a407201100d5002014480360032042d4001900c1d0400000b81d2008001d00429150a0300f055060740d200c01e6958460307503910411007a21420072200c41c0c5804101c500028595090810070504240040c9810710030941c43d040c07036a00e99031050780c022000501c1c1441a020a84060080d840502203e001c1c09544c3c42414800070400d61010342c0103002c05900040049141e6109800c0d062203560160810200c1d6 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 406777176 1250 406775926 406775951
    0x4030302040503060702012919091d0c0312030c0f1204110d050d030e0102040806180606120d12020d0e010b03010e011401030813080a060c02073213 65
    0x75007151062034007901c10140445d40803030042c000d48501c0001441920186149041c900d0500c1000105050308000407480301d100b9101c082c500b130805003d1101d00440c1000e1154410b026900308507158400540250151041982e8041545156002a80419600c17074070752040b401b1051141c030142a11940e07000070380205210b00c0c0079200b40319602450b9003016a04100091094032200c5920040142d00b00e00c40d2540424082d91201140b5a4500001810701ea110703c401450050240e03608200400b0003c000d00044a042014650080013613034900414010020015a035450680c0d03020140000e150a03003c030303551650705030b401d01c2c03240080c14803642d1110090240207041c0c4410044c029421b20045003042081402001e08020400c8045001c90b131941d150542c181d0010ba040640c42040e010000801c64001c000030075030940950b000080040d841d60001e403031b014080d81301c016640032080b4101801403040d100f4001c41d880c00004c50503101d0b810070005138035039400c0e249245000d107080310381c4a00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 406778426 1250 406777176 406777181
    0xb03190203240a0c02010e15010315020705031605030915090301050a061202012a0c090b0f1012090503040602150903040b09010f030b13090302010f0c0233040303 71
    0x1500075030955240b8041d01c161050700200500311652103019610102d40780c05482d034055072541d4054070002400d2411101d4050501005070a544da01070071901c014018801e00c909283c0040156013000c5113000c00d195561a264080c2c88034200f450111982940e0030702906000301c0740303404402018004821800081e002c1e007508030b010560301030361a010006030702075074030b00c80c0380c8c2070340d50f000000180b000781503004580515802401c4050718480c06001161002c000421100c0c01b4803502c1c1d000030079420150752108482228500c03910901240351410300b81d489602070501007254526040100e80e00c48584c140182c20440401445440000b50000c0c12607404189502013000080b5540300d5500e0350204a40d4034000c2c1d003d82030a03080e007000700000a40c05425208074407112400c01041450001e400101119400804000d10302c1e1969400c0e41050741c2842510341d110a07415041040802e4407600a541d05040841c0060f50482c440700e5407070b084001a0b00005034940342c40b481d20580fa003407900602 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 406779676 1250 406778426 406778473
    0x1203050a0b01030501030b011413050f011d0c031b09180a0e0a0b06062b0204030c050108131e211803050d030b060702060d090c06090f0b0705010b03 65
    0x100361900c0740165480d032203402410f0480360011000b94059081c0010412199820764546a22004030704080009510381d0050f03d120300305e454445c1c640307985010641e100b580700302040942500c400104001f00317820800c00303030b079006104250102c1c84114407060101c910303c1020400f6901020085000b031031802c5030b4107a0780c4030b810000002e101100d052002255140ba40250040425001d140041c0050078060041d140c0c498108240901014042c50411303000381d00369810914464000a0510500000d2601e01009000c2841c0001d858070388040000a0544110401001c00d50681d1105000340d042c00c0c0b4075500581c01c400d030303c2e686841e0074603c1000610b07840c3d4400301066135400549150141d1780704100482c1c5d0040e01402041c84201300c100e000b0320401400d1a07010800740141c0d00980c81d00c80103052041484080020003444609082c00d41c82042d51103442082001c10301400660710030b0241104031000c40c00503507224802450600d0140120324801601403140e146079240c07504024148a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 406780926 1250 406779676 406779691
    0x321030c0d09050a060b060f1210031a010e0c0903030703111c03060906050a12060203061906050703111903030203040606171c0e010e09061305090c040e01090c180603120305 76
    0x140080c48007d001d4203000c4e41003103480a00b001d00007244038025000840307610032680c1040c0880e2940b00d81d1880c00c04940300d0030b841d140c410b4050040c0141c00540e004140c210000d844000d082c4070b4102c00080c2e49115946004082021400c0b04206400c3d040001c01aaa0101c0d0444202d2100044c0010001c2006100720341009050440000d500c1c100714149000b91851102c10041c40251600e580001c0d60011341555004000503159881315604407030900c000e001180d80d00380c2d0313030aa1400c0060140620440c030910a402c107040701c8420031902101c07004107a48c107040c0961240c0c1ca40c100440204601d074071090041084c2031054408820115080d1a00c42c1e040c440c28000b400128412594030131405405404201070310b1501003a0f2500c1c010060b4007200c02040108011982d101000c01c0c1c40d4181c030407010313943c040785d01e141c4245041c2c000c411043c48104001c10821026441d10740407403c0c00c2c86216480d034280001c41514024940100c0061a00541201c81451009200800600080b92000e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 406782176 1250 406780926 406780931
    0xd02010c0204090b131109010b0306060c0a06020403030f021e0601120311160e15010e040f0b150d0e030708070b090321012c0703050903090d060603020f0321030c0d09050a06 76
    0x3803a061508907c268180c56050402c0340c215503802c000d00100368400400c012241c41a62030038000114180024405180300e6610708816440500d8040c1c9070480002c4100c448200c51150030100501c002016030449403030002a4030200b0007802c007991150b13080501e130a00e6020b0841c01b4003000c1c1c041c015140c211900303a240500c1503640e80820340d900500f201f100500042030716120200300d1034039400c140c1e01d05002c200002046000c007030003e0354501242d0351307001c40407034040b800f00039907c45032150b820000e04440145240c03000341e5a80004500c1b601d0b100400802140c0c021a010710300410540d50480c58011040901a002441200401200344622000303040403ca00d01e03800c280e0070011162b1840510584c009035143c0d50000d48c041e2034024203040540c4018840b0030065641c60b8501c40d24036000740d00c0011150b0030742c0184042c0308140c050950190380001c1c2c01c0880c0c4902c00703000c008203030481ca0003943c40e0345403030207455100c1c800c1002c0114447d04001601d4280040441c1101200d880b0341000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 406783426 1250 406782176 406782203
    0x901090905010b031803030f01030807020130050903040321170703020315041a091f1e081c030513020402120601030e0705011b060608010c0c12030b0d02010c0204090b13 74
    0x4070750320300c03089580030340152304040100006808480680358107881410700c900010140300110a8030024500c40701001c030255200142c0c07a010b01c3c80360350703007118035807000c0d607c9c00e030440c0c8a0040355440100140c03241c520000090300b41c9071240403800c010201d00b41c21410740d41800380c1c0c010301a41050380c0400000512200c013003004c0c41c2a105000c206103e20364200d003908605800c0000001d0014004e65450700c208039800b200d6840c035000640604007407040707144491440350042c600246103401c14002c59002c0f20b0f001c0302105810030a50050002c924011480b980d070ba070003958084101420094015001044040030448201d12071132099100703a07401c00802e00d0f03440045a803503c0910a080c040f174001910011500e01401602c0505402188041504c82e40c0722000b508507032420300e04000107000e40c01403404100d2104405410300d6000c0c603062108400c0e41c000183d00c07000c1968001d0512100200f40c00440d01c1e15042501d82c590856019111481c01e04070300c02e85001c1d141011200301c8456238a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 406784676 1250 406783426 406783471
    0x31c08061018031419030c0519020901030201120b031906050f0c03060d1e06020403021e0109061b080a020d0810030b010b0309011b0e030c01020a0b01050d0510020a020313090504030e04020901090905010b03 90
    0x1007069860340c0080bc5000580d00c0c5400540c3c0501d1107480c010380c80c98a9480c809041c0c3c9040051600031003010208503028162800d007c011035101410b04040068080d00744443c10301e0700c03030a8a41005c0101c0b90306c0740000e581d240c240c011654950740c25200a00205120052007403070f9002e081100d0090700c2c4502d03ca200d9010813120641c440e040d20b40421002d400c01d000c00ca21074662802d026501d80d54040704101207440e0b0000c1d0b90003440000700168402420fa07050160300c4a04682c12490703100341481d03414156a50340d041207005019034441d0b52808800942c442c50250842d0010340080030740040c104d8a000e500526468070b51550034080d2140f1a8a40312a520006000401507003128240b003141c1d0a10041046024540c00281d4282c41a00d100b2140c1240c0d80c8002c0072070800c6500216a585052083c0d520940f0341c0e07511940402d80f40c0000c120200ba0400d0400d00481001c65006a4440185005032a100d0403904095103151800c000492407a14100041d80035102d00311220702200d84088 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 406785926 1250 406784676 406784713
    0x105010309020120010b060309070f0b0c0a0b100b0304050f0d2a0203030f03010e010806060d050c190b04030602030402030c04021e09031c08061018031419030c05 71
    0x1000030f000609282000042c2c1c1640540c0c1580c9a107a180080f41105400c40081c403a41c0003650850516008244100074008848005070010103101e401c050804401141d0f40d40c9541401c1d02c05800301507214001804080c1507c0030101805003203404c184c032801e250400c00e6a90b401c03011207140d244141e03100702400720b0055800f0840c00d0510800311b8000c2c0402000700000032108141241c1500c400d21181c220002c4580c00345029080c0e880c14622079601d000c548a180074406003180e4051040024800040740d004540300c800f00d601500c001f00d140d20f4001d042c80c1c4000b03d6134822165660301040100810a00750000c6000318022003c4500b140c08010400c41244140c541074410b4002040c101060605144042c085440c03006050b1440141c1100707030094500d012a0158001400c180c0030030078a032920410b61100316010345000080c541d1880000c0003044290300000e0000040b03400f0344001041c0070001c54281910b0b8100b440380c588428074014060201d00c1d20200c543d802040c00186904a098 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 406787176 1250 406785926 406785941
    0x150b03060d02040b0a09020f0307020d140a0e0109080706030e101a090c070602041412150601050c0109052e05040f060e15010e010f09140105220c031401050103 70
    0x9280400d801c110b41d0810000f071030a0200181c020500090001d0a114144060030822038120806540c920700000020704160320740e07414009203c501e8004250650300c010035140d41010f182000c071030710000d40740144c0e410402a0310a40780d45c8110780001c6034541c1d15400420f101140d080031907145074002040b010503103643e446c400ca020582008200310f640342c65103155400c001100801032034404551240000d9a100340c001056100120b181c006040c02c08072206c0010180c0c400c0a01040e030305418010300034200181607241080408207291000705e0081d0b1115600540c088c0840da0400b102d0f08500d6400c440c1c1d03002c0720340040c1002d42010a048403030700440e4031030303a405403d481c0030440f00c2daa520024458a00000b1041c4070326031000d0001881ea111180c080c10001c00700000d150701d808900c094019061b0480d1070b2407800c02e012442a4a009820305041d00d00443d640c2002034011818900001148800580d080d41008402d02c8030701e41540c00300049466490b0340c481240c0e240e00064050f65500f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 406788426 1250 406787176 406787179
    0x102210115030506132c030a0824040e07050423060402070f050f0a051606140c01110409020309010b0103090201020c09191d19020303040e0403120609150b0306 70
    0x95410300290359200e41c3c400b80d80400010801e880302c480450308907084030b000124000094000c40311007548804642078242c4001007600041d03181c0030628000801149018050001802c407e0300c1108a5481c1e00c080f1010b8203401a10401c1000800c0b200f041c0d40e2080740c0305880c004c13460400780268820040b5040700c030840800c5442031080c2ca40c0ca0900c00294071111040d138240c4201c100420020303006100c0d40320350b0b1845c0c07002030280b13041504009041001d403402000703003140c0b42c030313003c0000e660058071943c1ca4121111040303480b2007411441a01510200c00740305d2107080000350104805480d44d01640c041c1414000800c03c0d10007400c010760840340c0164000c5e0250340960361045940c6801143c50b0b80c8446a8140c2100039104608500c09640114840360200000851010704401040204014044541c404c94900702c400e500403d859100700d0140c010a20444000a024540a20003812294036070020800c02941d440d1003010040502c81000e80c82c032280071400081c0981d4140680303015150 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 406789676 1250 406788426 406788449
    0x114060406170703120e130504030206070801050d0605090c032407022a010c02090c071b06080c03180d200f030a050d0b04051005030f011107060e1c0201022101 70
    0x1503440ba1001c01c0001c01c00d05c001c0003000650354030562550395941041c4940c1c940c020800d4101441c0c064200203004183c482002408401000b45564882d80001c55607000f07903002074641c03140c414807818112044002c4da0180310350010602d064201140c90b818940182018007695112444102d031500050711540f40610300702c0010f01c011021550060200d46030504101c1240348040d0b0100b43c0c45402100c0101c103000c0d0100d515420300c1a1044010800d00c18010030f068005d0070701102a100c0d840192041d4800000440064072400c44c1100ba1605107a4600444810060001c0000d00c1c4425840420368056042c030101c0484620020300c0c006018141c001035030a2001c1448111003940019151106003034554041e11250313100c0307205803402228510800780505003400141440c00c9580c8180c000c141e80742c903c0044002e103144054035031169002c00c020a03001c0d9400009072134040036641d15040109100c080304a119015401440548108281120751003152003180600d10000d1084484421 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 406790926 1250 406789676 406789679
    0x30106081305010507030204050a060302070c03030c1406091e0d02070b03090127020406061b080306040204090c020a02100e090612011407020c030106051e09150301140604061707 78
    0xe015031800d40d4088201880a501000642c9a8600f540c10a891400100b80e0000c1c0902450419140340005400709040c15840c19003030707940314010341c240c1c1d1001404200c00401181c08010740c44c10b03d2509441014200c810307609001c80c0060315100d1310309004140f030700b07801141c0b00d4400c008101e000040549801810b580780c5042449101a44024002c080035545c90700580d100b80a203480c6120b0200c0d24407266100c611061051004803001900400103001380420001c65204000541800710340c0d0004501d5103d0311640c2c00300b0040d0060342c201512031420400348294840e030001e88000c0fa14000c8500d101040031510040e06c144803089855604039846000040a60514580c001c152001003000024618a4400b0000c001401905c00a005800c0950129000d00d400d0040380702514048802040440500044944841d00d82e07602c0c5026504560010b800c541c6041c2c20a0344d032500c060700910450405620040ac5040111401381c840c41c98403102085000340c00000d4007015407d1001884205d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 406792176 1250 406790926 406790939
    0x1050f0d0203101406310207030512010305030a090b0a0e0d05071d0f0109051017070f0b0715050c1b0c060703050d0e0c1e01030204090e0c1f050301 65
    0x400461030990301440703040c00207007200001d4400c51103001005140242281020070401030f241071000c120319841040154280c242100d140907000c41d056280e80016a907070918034055450b4052602100039070700f1f080c80008240319021009040000c513903600d00200c0350322185002c1039030013002c0c220800958640311215140c24910320b10110f1034000e608803032000d03030b540c0701010f860140762207641c000c00010418484202119510301d80501000300c030501480c5007001c14614410028807881c90342c00814502669507900070f000b2000a4111118540c03c40da8540e00010b485a01c408012108a1003403d200b4a00a485204450054041c3c101c424580044508440110081045000300b140200c400e00542d517510380c2c00030250709100392a031948a1405070189000c581c0900c6611849800000311442151341d5603201c0d803244034140441d8080c1c520540b0040f8024001d5401c55444540303071112843c003910340040c80c440320120844040c4c4079501c10b041100760220a1281c020f02185081c40144200e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 406793426 1250 406792176 406792189
    0xc0406180305030a0f170a020405010f03140615070605010602160602030c071202030319120b03010e120c01060f03061b0f0801210b07030c0e0324061507031d01030501050f 75
    0x1e184040c0707000748407601024401001d106d02510003c02e05035001404201958001c2c2425a01d408507090801c600203c07500d9031a03607000010f0440d0f100b02c0076500c0c00e0b04461080400c1d110040d4010008008542c1c581d0000381d40c4812510302940240144400021054400004c07680700102d00c0c405800c40619106081c1c0581201100032a49030000b80000c60380010081c01c107010307158441d0340d124241c2881015000c11554501d03070050280c0d04104d0342040c562000680b0356000a145010140e44181c103141c09070040030150041c00244d008410300000740714254100000d80340c0014200c000c260b85071517007910800c201d0360418020030710003001040f1501c07034135001c01d4041100c21500002200a80e55409270b042c0300b15a05800b1940c0c1e58420300c2511383c01601d8601c0c0d0b4606800501d903100c00002d00c01c56810182d41c000c000300b030a00c2c002030000d45545a0030b000f10016045285c0d200d00300b529014001401514070390010080c0d0340c0010080350300c24081d042c1241c102612a411780c900340e2013800704 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 406794676 1250 406793426 406793447
    0xc0304051203070503030c2706090f061b0a0c1d041202030906030c03100605041a0c120703020d020105070804020f0906010e090c071e0c0e040512030c0406180305030a 73
    0x7100c1c08140400404a003003440150310802e200000960b580b82d810008044c601d00c1a5081d00e07031106000f240034013945070041225000e00f01110800000c03c140c00000c0c950388140740c6560302030a1141c207007100060380090490a0306116441c03450300c0507110480c2c1d04210024040344d140b40d04611002c2008103501d207582c0103580d269031054902d000b940b0804039540303034025185600d01403000000c10241404030900d03200645060b01d0300902e403070300c0c1c01d1002c2c0c40e1100030b43c8250302c042800140e000c03203800304010a09807903c10070001c58450408d07003800307034954410100d0b080155007003000003580c0320300c1003020138030032075000300740d00c0b5611000814400800b1700242014180001d2184041083d915149940c2c419100340001d240d680f0b000e4600441b4884e0650003000d80070105140010006100c56000819a1804055041203641d14184540340008010000320140400403e20907041c00880c02001a59929150780b0211074400e01d201540c0c031800e100107003050b00180188490786104020042c07 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 406795926 1250 406794676 406794709
    0x110307021e100204060c05010e0714040209040e01060602060f0f010f090203070513030c09060e040206041e090c0206010311030307120513080f0303010302030111030f01030b0402061c200c030405 85
    0x401880701c40c2c0a1104a9200303800020114130031024150420409028800c003115591025003055031a00b80b10030180415907011a12440d000314140085031116484540a901017200074024030b5170310304004e910f0321020790348000260384440c0050903c2020b07401440c104d036041030f000c500340352610042c1c070003d400c064542d43c01c0003820452141085002c0100074080c5020307020380c001103450031124034200c1d00a0b41c04001688502c101300b002690f10202134a040350089031041c400b02c660b01100c003035448000d80107120311a15126035158129400111325050740d201e188407801341240001019074034040d0303000090010880860b5541c107507114401800d000b00f40400b8407101d5a07100c2c0e102c6401c0c81050009103640b680040010000c0d4542401600c2c41c0312143d802031071660030011800c81036420705000c05410681d110300800c086495000c1180c480026040e0038003124111380c0c3ca81005080c580c008000800c24112110405440c50301c222034081c82010021031803c3d00e4102030040040d1881c0409 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 406797176 1250 406795926 406795933
    0x60f07050909100501090609080303310c0312050315040c1416120504031e0218040b09060108061e0c0c0106080d030606050a09060c170c0a020301110307021e 69
    0x8107803034075800c0c5a14090410200001030190400c000102141060780c01308003040a1361380200280c0e032001c07040701e82010002111011000c001580304281300c21403e604072192440d801c0000500c014081500309684c40707802c44021120f00810b0845082c042a10003400070400080344c20082e182c07545c0010181c4491781400c03298413030700c2881100317a50840039410502103444000e2000304106409103050880c0c1c14100716003402c0c110703140c000c0313403018200720104400105100c810565654402d1280f1600c611842c1c1d0481389014079004016030030a6a02e90441c2c130802001140403440410154032500c00320f007003043c5802401205840c1c8441c0603148000b940c0701001604510203013030182d072001e4280b0000401540304c07441c00c010b08070f07200703503005d50b0800c80140502d15065901a18590480300c603407a114800803501d040013a200310071401070345440c4000042403011600c0214540700d00c507008500030031441002d1104e40a0361700c0304484280050f040b80c545010b20862141e074210041031001c048 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 406798426 1250 406797176 406797187
    0x30718090f150f0b04050108070203040f09020405030c032e0b1309211e020118030207050406060504122303040617461103040c17060f0705 61
    0x40c0c0e400c0380d19201c4060071040d1034007a854000300c03501003008024107034074a40c10345281c0350000c0b20301d0754000c40c040c260401250002007400303103100b001502e0103441951180c1058954801c500f0009500621540b8000e0152401d01d0a007450041400160203400d02c05203405141400b18029000511070750100c4850360710001d4042580b9295450041842080b50000d14010541440000c000016a07a00704401283c3c02e110b8816038021800c0c00d2010002d10031800450103c2d6099003d0907100032480e2010244d045d4010506500084034411640240c4080100c01c0c1c41781400c40700c0307110320f000b025075207201c002c000030020302583c28107401c0080099101d01010490b2064905540c4598440c0002070a030003080d540c070f01c030800394031034000c0c1405080b41469000031103101e0301c0001116503200c0e0380c11503800320203118a0f010a02216106041400c0101d002034101d01c0806420550707090f525110044004a250800c40d8980c084001500300141841e554900c50007a03241c400805140030030406114 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 406799676 1250 406798426 406798439
    0x302120117072705011502251d1603090206040e040317090106030b0c16060c050d020703051c20090406051e040f06061b0503211801060b030718 63
    0x1186410460780388061030307054030840d0800c4213607401070300003020980403900241400c0c0e40001d9841c007c1201c0e01222a40c07403600000c80304806500b41c1c419024405c055040b403025605000141c0d1003060b1440780507000c190a400210102e4210410003508020108414020054908000381d0701c40d01c00d281c601803501e03113244040740480d815114030205a444034030a2040000c000f03070321540f021140505071308040e44114030760140810304001508407640c8051510420344500129405948510360965a44d001480e009220b139000e14074996800d10842100ca01d500751074007c5091000001c44100c90000c406803260305158071440070554017990700c05000130a5100c413909080a4050b0130b4003c40128030b29001d00c015100341079442100a8a401e42c188542074201010314218000d0303051041001c4460301e00140303503100e40309a210740342c0380f0003e10142042d02c11f00e0030b0744600303130b50342c6009401c0445640c40360a88440d8010194070741014000110028802c41035036505a010030f01042031150f41d001e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 406800926 1250 406799676 406799699
    0x12170408030c0f0c01030504030e09070309050102030709091802030a031101023f01030503040b0c03070b090d0908030315040c02010f141b040f0510053106030212011707 74
    0x1810901c0b103070021406010071180c20b01c8040500d40302070805104c2c528217583d00030000d40d0340c0030743d141c4a401d001b404201194480e9109024803503220b4021942ca0922035000391824207244a0035045a081c0502c1d000c00c42c11480c03280902039030190007810756202c03035a410740c1c45a000c03144100880d0341c01d01c500f2010441920224209210001c0504030302083c07030030403140b416039034500c03003105100ca00010800240000100c4003119041560a82c88001800c90503066208564000d4550b0311184180b01d003605000c5002180d6031040d803500022142e4480750280c4a00045500c4005100c02040603052403d0a81281c3e014040d42e00c000501400c0d6583c20408540498040d120102e8400d42081301d8505200921004d844101c0d02d07450602d8a840b0b819040506180600c501890f141c0c10340409940c041e4080c0d031a12130040c86644100e542c0305004845c0003045000740d103202d0101900003e05140a13108803001c400380c2801c08403540e030134a240341c2b41d4500b0000c0e80d9829071041100c009103039040303032 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 406802176 1250 406800926 406800937
    0xa0215071707020c2202040e0901060f1e0509060d060f0606080601030902060f0f070c06050c01050c030f070809070f0905011806050105070b0a0617030c010608071217040803 76
    0x2521254103101c0502201d8101001c000c1c11003042d9809000b811646070f550748682020025001011141c000c91329000c40041d025a81c8000c0c001c0d68080240850861f040d0410000e54004c004100a1550b0f58500d4440040b4101e8195443c103400b00404d101a060a01c2441e90140010744908081c0d00d081d6036407400ca0f42446803400800c0d90b0703180180205c0e548500201d070440800d20f0144803004950700014640e11074000d041b0801c050005a0007040302d04201a20602500071044000d8140d50b0035020b0039a0b888441c00c4d0401d54a84000a040a0104401d80b03000324030b40404070411760759000382501c1400028020f5085481461000101c810032102080054078990030b0101d1154980755808080e07103444001003c213103041490038040c0340d90180503254078a41040c1c660b049501e513205d0b4140200202c0d0000c840c040041c02d400301e000300d4008001e007a0065401c00070400325640b900d0701500d4208502880b0410301000c0c0c1c03058081a42901e043d61a881c03210f04441c034290741d40020a2655002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 406803426 1250 406802176 406802191
    0x4021905090405010503030a020d180519030b1b0d0b03100c0c050c03010203070509010c03121103181b040f0b030a0c030507141c1401060b03090c1c02060a0215 70
    0x210481c1d036003018007419006010560045040001a580c040d454054040f0f45608200351740c1548004a07400e412100010314001c1c000c402580000c00c8202000b4215000030780301c0c4020000030409031806822025003e1840f07080c00c1d410701c0c0c60304e88000003500340030100a1f8503100b42c103500600f41025214036088904680c44a00c000d020030714066080101d0b003004240f0030303441401044a041e4028089400702c070801d01e0306d990300000a15096a41412803003068858500d0004800d0030f40c100f0400860042c2030400d0030801000045580c03e80d44e29003548201602d8407001c035480381c9030030950480401100d1001010a00201c0000440e180c40c2c0601c01c160740750882c141080041c4281404084040c200c038251007140c5155103400309001201c1e1055040b090003134460440700b4000c01a990141c031525540c0240000c9588108140c026003041c0c61484c003500070f941c41c44840f45081c0070385240300030020710580c44070b07035907038003044043d80141ca0341700d00358058480d80700480c8540c0c140c101c0c4580d24 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 406804676 1250 406803426 406803437
    0x60a0e181905060906040b1207061d0d03270b032401020607020d05070c081009060606030606020a1401090503040806160c020603040b0403030204090903050408010e16030b06040219 79
    0x10880c51410050078a000d0039020540b410080c0150754840d1042d06030b20000540d00460364240c200003090520729a21014041070084040110707125034802141000b0414007110054407042c408104a00850b01c200c00402040030310154002d098800714180c0c005c07020740c844c0103161568130041c51400d42d100722503464484c1c405108251041c18000e40c5075400342d900b84010080d902c2d0003c0301075540c0303d0044e04441030100110325001041008542c201c05085120280c440e15080981c00201610011200b201c5440c201381010440d10f1007881940c04994090707000700710003001522000300c415a000d480030119500c50b00c0c40ea0125104000030001840c1c0c5100824262030300d500110080b030346203481d241c10030035810120405a43d54805481c0c101c3d400c22410f0544e6101c0d4a41075009115590000a1003414400603106054100740a002101d260800038440d805001c0c4a041c1c6402024040c18094000b140f4140007207060280150707408003000c0c000500c0c204c100e107419644810750a021000044 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 406805926 1250 406804676 406804681
    0x70602030c060c070503030106210603030c03141e0f070f0c0311030a0c03060b01031512150501060c0f0c120f02180c09010f020c12010608060f090309060a0e18 70
    0x200c00700310441d0b000c9030a00034982072104a545c4c0c10346a21044c821041080101c086c4035001e03115144075140b900042c01c0040000d99030324500540003501c03410054000c03460350380b0a030665540040456442299503507066840b49224002c14501ea0058814020862018031040000890708038501c05000c0c0144646210390b40742d4548800f1018007401218002d8214122041c000b42d0349805401c1500c0c5d00c508041a84140c182c012002820103d0882841000d021400030b20151a0f1509000c01801100100b402d850512049000d4038402c2c4100d01c0005d881244c1d03c0040396008801901d043d1241300001c250590b0740ba40c891010028280c20750b004d2400d17600100440ca000f021400d00314806940a611030702c0c00e40103507100e07400b41c0070596040c0040c02c04100010f83c424880050f80000042030484283e83c049070703072802401c3c0f81c051048140b141c1e40101c0c103035003505440c1c28450350440001394500302d9402d090080503040384085000303028440c82c45020070fa58031450f031545404410340e080b202b807 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 406807176 1250 406805926 406805947
    0x22a0d0501150f0b1812010906060503100510060503040206120907150806090a0506030a02040204120507050d12141b0f010c05040509010902030403110a0f03170f0414070807060203 79
    0x2814654001c0310070071a1043c04104089094082e1180302880700c0342a59a5010316000c030354584502a80d18400b5464514180108a081d138004401c1d43c800b5011907650000c1d40192104a400c140c8146012202092003005110320480082da40b00d44003078840c506007038015500040c44907098038000504c0e003005030140500240041d25034a01007103490320441ca814803d0120310000800740c15100e95540f5200080c2d2180c4040044e0000c1a84c090011541d0303580d83c01074100b403040181e904480c503014411000805192116940360b5042c0c100c4494180d11000c045c00342d805000c800142c0c0c8017000280300c0318441d001d052032001520030440000e0308040020010080c216a0f10400c16001d2240a01040c0001e4542402682c19140c2c41400103990340c0b100d00f400d803412011048004458464000e0b04401c11100c8440ca00705540710340c40e10704c1800e04205604580300c1c0110b5003100103540c100d0003c2d01003101c2c0d07410040510352850980d5440e070344900d0910b0400444c1c1c0c01c8600903a00c0065103a189 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 406808426 1250 406807176 406807211
    0xc0705030d20070b130501060b04060c020a1710051003021c02040c090b0d020f0706020a0504090e06041502070f080c03120105030a020a06050a030605090a060321022a0d0501 76
    0x89214140b040d0345032021a81e02d49854540191640c98804520118030040060035800840a00207030254180c0307856071920024811108072108a005071030084001424000c2400340c40d9039568180c011300040c40303501c0c409000600005003844210090414000007580700c0800768800c0070780d40000305a203d01c20f40140425604460421b170700300105070404220111600e401e0304c45d108849000903a8134160841c1c510320700d0040400280a0520020300c1e42802c9070040014022107038440030a101c000e1202e08055121181200c004c3c216100da2000c41044010560003442441e01c0340743c41c00d68404a82e1035050003600001d88800c0783c0d13400015604440c016043d036880c0106011401022369540c00d5012175044c10f0980f0a02040c0710380490310060960180e00a180940406001074165203448065a005041030b48001d4440300310750400e1144c01a19140f40e0070f0714030b9280e001064602100141031030800d0780001088402411005141002d40e102900748401d140032318008541407154080c600039 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 406809676 1250 406808426 406808471
    0x9092d0a0c031817220806060a0605040815041406010602250531020f07110103090f15020715090b0916060e040b03010921030204030b0c030c0705030d 66
    0x202444000c14400c0007a490402401c0e1403404d003504070352941c0555000b48030114619036021540b1841602c00308821200142c643d100b15011110113081c5966103030142c9451150303004590351504900c001c0d141912409042c08d410510808440e55810a04d100d034a050203420303088040160070540d0407111901072481c8880d181003218488070f0004c0c1c0b52a0008148003030888034480d0300c20700c0e0f4141d1342074901c0c0f8480541590160030310a42d9150010380c00031040da441000c007207400c8442d00b2007841c101d51007403144d1080c0c2d40d4410100000007000c0d454140302c403c2d17805401c8907015003c00c126070000d060503000101380d61807044040707010030707842c90240155800140300408170b41c0301c0c90a803200c05110300c1c000411513140d410100c3c0d800f84060f020074050800c400300c90b03806600b0070881ca010044030f40c880000038180359000416055524004070207a203c0d038440980659034074404100041c1c002002144c20220000e882e600d0301e42103a58681c00c40e00104105602d8035a20114056401c0c0225080ca8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 406810926 1250 406809676 406809701
    0x101215170624030c0f0a0819060501090b0303030a090507050301060902070c08030f0d02090a0e040f061a010f11010906050c131202010c140c030304080c1509092d0a0c03 74
    0x4145448010951314040768401500c500340d141c81c44281e40d01c50004040240006506403071601851505080d091103844c1401c4664610741800040e8810030b5119100c80464003c0182d481c503158444094090b00d58075a06542030700075000d00103440e940900c80c500090040c008050307181c00041c1070280c0e0040c3c8a5004c070a81e500b08010000103842c6401c102c42c6015200c1e00c006840f007201401003440103141e07401c00418500140c0a2005110a110403d44003510541040c030a442c5d268104441080e80d1030201030201d040c00203005d041c40d00603012f5031201c0c040e51000241d51695a02c4e01006d591003030782d044042450000d914850101d2240c1a1405060f85441903a440002c2ea80000d20364030b9015006810000c0c240c19440c01c0c4542072190705894400101243e4680e41c542c1d00c0c840d1265200c46405100d03032807030b01003030500c40c2c0540107030741e88607800403d2000280d54600c20014142d2000c0b40001c1d10140900407010080503450116004049442000401d0005000e000c2e007118242c0c0c5079507 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 406812176 1250 406810926 406810981
    0x608040615080f012412050f031803011d1c02150c09130203010b030604111905090301060503061b0a09030c03030c201e0112020d05151012151706 64
    0x150078520602800608850700d10088201b4640c8a05116052240003504500756000001f4000c2d2403004c1c9000510500340118020004100035030038541002901007140c0e80c0710f4000b00701c440c86103a8440c4054001110500583e4451490600c0001512004a0342c1c0300c010100803520300018101425050644618400308600d15410480d08412a01004007424801c1ea10741c1160001d0706194410380704400301c0c500800040b0102d4100240c0150031200500c0e000e98a00180003601e80341c00115a03000c1d80280707000340300400380101100c0607a400347c080103080c000c1680300000052060045000118040d0b528200100668a400c0b0521054a201d9007500d04a160680300716946400350520500c0031060443c26204440c0010f9500300d00303083c2140700301880400d10f03200c82a01768010030b21440180c0303107042c10800240100032a251400e2603660018641d1681c0010050403a444851031452142828841f140e071100c001d00748201c071f0032440c2403036000039051005c03807104041e561281a490b41d401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 406813426 1250 406812176 406812221
    0xc09151706013807030e06030a0f0b0d1e030918050906010b0a0e0d050c12100c0c0c0608130b01170d050a0c11150a0503040b070207030c0608040615080f01 68
    0x500c1d010008820b00c03021400010303801c005c140c02074200c042c40c0c001c003404843c4c49250001c04100203002d00e5a10311b0203d0304000a460081c03400341c0ca10681d050b8800c0c803000000202411003102d0700c07105032045080c041440c001086802c0da21050000b030340c4003850041040e00c0d004000714100784060380152441034081c081e20803050b0b080404441d136900181c81e2080d01c0b140b03508009290808051800d500034181c40c4101e100d0316004600c0c4010703030b05506014030080455500c101ca45a500e144050042030038544140902e505c02e00d14942c2150054081204c2e030a0151980c00c5100740030703481400000480007501c07000203824007004141c000075081150500380b068002800342c0d1802c003001400b1800c0f00300304021710ba403442440e0030214041c40e006a140c005c107000203004ca0b401a5419214402c1e100000740c0781901c00211002960762200003040318624000003a00c20000203842117801c07030741f00e0345610303404000d41c1c5003c0020311240c4014903803040c0f014005421a001841d0b11040c900c031803031b035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 406814676 1250 406813426 406813499
    0xf030603080d0207030306050a090903020c0d03051b07030203120903060615030109020a03060f0306020c060c16150e0624030102030f0f06030a0501180b130c0915170601 74
    0x791202640a00000b503034400180c54206d0040c101da0f0000355100034041d034081820700c596404540468440c5d0210340045041904000d01c0c0d982c3c0c071200400250042100c142d15507400e20b01b0b8004004814100c45440381c8a0780000d00744550840815001344001c1030081551404000194105000703480100104160403800c400350311050103001e04543e00040c0110210b4881d80c4004001c01025004140994032840c0c080040d41c803403200c03904248078000c081041500424101d904050754121000c2080c00250395074000110320b100c114881554800039003e03801801e06c0f646100f40c0301071807410782c55482605c4110103840520f403081e00030b80c414400c0018015081041c16004107000d0610755541e9a1032000914140341c0ba40c0040040d420a100c03200c9948600c1084004940314100744c82c6c95665400f1170700e60b444240350707003c3c2c1901c4c0300720010018007006074840902d044211560780305c919140c01086001b511940301484569018000400c680f241600280c1c58034038030310708940c038003000c0d442 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 406815926 1250 406814676 406814693
    0xe0a0501031b1808030c100c080106050415050f120105031002180d02150d0b090c120f27061807060828050115030c030b03210d0203160f030603 63
    0x86000184075140000c40e42c0c074041000f0300e10040041100b200c3c2c0d11000c03a9161500c0d0038110041e844020f041100c8400b80c280200f9155058611030381e140c030304151410400846a160300a400402d00408102000c10110303414001c0c2803c503841c06180d10194502400e05140c00320111907180c2241c810700503004450182d01a02e030040004070354103400c4002034000a44150a0640407454125000402e01070b01c00707958111070800541190004410340c0d4000e1103480c940704042d44107114001c500002035048000720203807600324801c5020f4503403202030500001c941090840d071715161940708608000f840306c06605280c464603213000180c003049282200241898401405a285030f02030040c802c0170960341c44026006d00c45051005109a5035500074404041201850300700c0024100611190164083d0086074004280680200141404412010a41142a03200c080c501008022081a0f681140080c6005680910400004009800f8060000600d9805c3c890038181803a204002250194 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 406817176 1250 406815926 406815971
    0x50601050d0f020d0c0207080d0801030308040308150319020a0b0f0403170903010f0615020f0318030a020a06021518031611040515010201060611070302010f120504030e0a050103 78
    0x351010a1a40c041a11100640941c11000044c1c41c648100509000d03400900d80e0b0803100200242c90300802d00d1902122415403d0201501083c00703c00442e00080c4038819042e800340d0400020f48500090f200000d023402e64a031042c0d401151728040c0c44041d46004003c03680102a030100170b518240c4c5012008100c0d000d503210142102c000e41d950484260f481f402203502192004000f00110101d03804040b0003044a405092100c0101c4558102514000a207650321352015400941c10000c110451a00d280c40e84c100c0e0035014010388000c5401622681d0619002e840e150300605020510300740540000d400050000d20380d02105a85215400d10102c1210800b54090b0124940d40645e410010300c648001029142c200d0f19100821104020f80055109010400d80c001d000ba00d980d10b508031024114804400c1451304110801c000545c090b001000403090786040130180000440e0b10070003110004c80d01035012407141c4031244041d1403c80b201002500d400d0030208841107400003000958580c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 406818426 1250 406817176 406817197
    0xf1623132403110d0905010213080a02012312010e0f06030304060903020d0f0b100501030b03030918061503100303090905090a0f050106080a050a06061406030703020d0b100e0306070305060105 84
    0x50f18050590080f402080b2074103031240090a120300c49040c030300103000307500c003c0307800030703070707110f601c4c40840d417200045400c10400790140d40707441404140c0b5954510f40d0b840e5101c5628030f05001c102c6464601a4442207900134094035154007180e203440440020558002417036180320750070400082c80001d40041511058a405039902c4664903441e140c0f082034608442806410342e0082001c002d10001d50201c4101620b07000e83e001d00144c1c5004c0c0038150303603000d204031107076100c2000030203140c040c0808898075a004900401070605c0d0f20010b008220180c2c030a66040e203003500801d40c01d00900d500000704030014402220100090f10300881c0181d120801210020881c641c11040c00b82400025000724000c4c04014051750f07240d590b5032074002d60360140484102c1da02810901c1c00030390342c1048050020701880140a65103103540301d0780c0440095200302b038020003007aa508133180e001d88a80038005031081d01a242c005103400b040d0101440e114004004400f014204010080182d9002c801e441003103c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 406819676 1250 406818426 406818431
    0x11060c09030a0c09022101080a030804020607021017060d081801170c0a030501090e070b0a030608060f07030e0f03190509060307090515030f1623132403 67
    0x251400070703003400a01c000142c5001c0b0700c002e001c2481e074078aa00400207526501c4001405004c29800e0080500c0c0c240b0450a0f5600510f0480001c6401080d40300d5000303100414680c501074082d0300040307030000c07005007040000c1c10141000c0681a21f000d500f6804c4903085131800413041c0303035640d8074842c1e100d512036011040002d4200000700e41d0081040e07a0a00700203552580c601d25082043e090a6045542c000300040c0c10071000040d50004d07449290070200c5642c0c06446102e0034400d1003001c41c0d2121141324201580c50300c0004006c841441128001c40c640e21850105040405004007607030f041c6500301c0c0380350304220103011185800004460a000c101c48a48180004169082c1c450b80101d03071095400c500c00104110020744e00064603010f940d41101c3c0140e407210340020f80c8016000880e03904008049110200b8001d68490082107516030042c0b03404e400050013401c000741d009240e181103005042c40802d805005c0c11855144601601074464485c801101c403000c2e034440a082c0d207403d00103240d07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 406820926 1250 406819676 406819687
    0x915090b0411030c09010311031219230403050c0405071706010806010212120103031b0308010b030c09030d081005010201110d0c02250e071d12010f110c060711060c 72
    0x4409000d10b111403d801001703c1203079a500d00b80b80b000c90380d40c529960b2003402001503102c80000c1000c151114007650404103c880000e1003015a8400403840c03000c801d8a244107000808019041300402c0603603c580054070342c005400303052006450019080c101801585103801c0c2204800c510b210f54842c4003460b082c81c0c541c032140c0040c1e0800e01540b12041420000054071085a600c20403c05e0413a0700c00d5866144800d5118800c034064141c034440100000d075160010805019450b01035500003009419151614a14500107887c110440e4118000715080500300810003c024026034002e0400b800280090402c1410b51041881210f8040b200c2c0c1d6954442030421610030050751004603c2401a410404081c20000c000d4080342c0c424040e03607201a000168403079103c2c1444880f0360100048440c40241200d00300310b28101d0402e403078030640d07584041c100709012103070103103240700290304100590341c61010bc3d4046c01d200004040da810300040d5411814152400180542d1104000a1882d10346 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 406822176 1250 406820926 406820929
    0x10b01260a0b030307050a0b0a0903020d05030915240405070525050115090c0f08040f140d18050303030f06090703060e0a1e0606050f0a1b060915090b0411 68
    0x10044020030b2030301407102240c2d03071003041400100243c009000740d030142405d41c0d441c00c105083d2007074800c00500503003104002000450086010315041075248082c0c0d40f07854020a00b40c4400482100c619a8040e01d0116202001445c000300c090b51034810b481c00e0143c1c5c5450100909244204007682c2003181c9200c42d500e14160002c9813415a003035104d0024002c01c0e9004000c1c15803c021402155901031424a46540e004d0164900300c0100d80d59407580302040e0780700d4503800055040c0481c00d0303038900c44450404403100c40900110b10000c0e01911501c0741040050750380c040036000c0340c108a00039402002170200d8070760b500b50116030240c2d04542240a541d1281d500f2070107050154001c02c929014032081c040b40002c241c2241102500207408009403400070800d0905598980c0302d02c0c008580704012401449054800130302a004650030320401e004000214002c95120000c019075400d45e940c0d20f624104000114290b40490000c001800000050344850900e504098002400400c03100003d000a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 406823426 1250 406822176 406822181
    0xa11091f05010c0f0602031003030f05160809060c01290405010308041a04080723010c2411070c0503010c091a0a0c050102030f090f0a03090b0904020403020d050d02010b01260a 77
    0x13991040080d03440b414400c280e41700b442001d02007100450864892100420b00c58000e031240925100304443c004803c54070785d0308403503210b03920700c603048039003004074440b481000d0259460861b01c02d420450040e2608584600014801c00070a10072801d000040011810b0142580c0503910111031540d40b881e07511407000594440c5078804581c0307001d011030000c0e040d0702d140481c036000c5030406107080901482c2d500455400321000b40007001c01e10724081e84c000b580d03008402c1e4040c0711030541001400600c111412031694014442c00c46402d850b180341440340341000e000d0840c12521508001040300d0820400c0d01009a0000c00c0f8004980c002c110505001c0c411061007a8558102008555030b0400c1d003904071050900f203e140b0101d00c02c0c0c48000e21108800174801890541540d541c3c05054200032500308654440c0d1115944640c0030301020016a480c0c002c10035405100310000e080c05040d17180c0207400d4074140390b990390602208104500c100040143c04021540c0f07603004080c01d03983c464040400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 406824676 1250 406823426 406823453
    0x21e0a03060f0806060918150703470d03110304050a0b03040212030406020a0605181903020c060a14070302120f070203070816260a11091f05010c 64
    0x32042c1112000902c0003404a40a4040c13041610340b500182e5403440c03028110700031181d0317140090b4418110f816114140040850300580f1520707010a044800d40c0b03501c0700c0380c40c2d0050400303840310300c401841d91800d5030340d4165210a20000c141d450710301c4040d0000b42c12031410542c09024440308104a811000d02442118050a0b000740b000d18500d40f00e501154154204407400c9000350b034900e0809850880c0041501e0854040f0350091000304100d130348100c0070384400b0f84611403480503500b6a0982580c14406100c2c0640030003c101c610500d1800c0c003c0c03604255491b1030340100d40800180200a0780501929403010f5095401540e4594074501203103480500c20f8000c02d814004501c0300582489480241049402202120400341d200c0b200d142d00c48103040f0f10100c0c00301ca100c0c8104041800d0345514004405003403e0204141a8603030090300342810b040c0704030707140b0045018150a0340b602aa080da04050715008503200c200042040d400324281c540201411b00c9606101c181c10003014440a04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 406825926 1250 406824676 406824689
    0x1206012d0e0d02030606090a0f18050d090f05010309050a020d030f230f071a010b18040b0a170a061104170613140c0d0c08010c08150d060b04090f1401021e0a0306 71
    0x407945906d0ac50740600460034000403200c0c0e000c3d28801b500d040e07120711081416110b100103582c8a5500d04070040d4010702e44040210b42500602c050f560259407084852010140240c9a082800b1a41417008010140c4d01c1010b000384000400100824040e0701c06071182c4900c08080c060b0303104080d0501000d12994482490994401c0c040041016045080a841900c2003002143e5200030300400304005d03a00100c0c0c0b059000403c486003000074001248070310003603140c0c0030305985500351942c0302c010907980705107645c02032500002020480300304201b1510f041c0c942520b002d0074090805100025a1820181c0041c2c1100d00c08641c0001402e0300380311500c40f902c8014100e656101007440e0038103456025100340d00c0c2075443c10301c00e80e440300d024180701481071181c032000c5d2002c020390004000020070500d20a55000f0b0780c414544805403034a100720001035024020000702d81c40c0c90300c0c1a10187c000b020000c3c8007030340180000039402d06510426a00403c08039a403589410603860102c001782075560020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 406827176 1250 406825926 406825931
    0xc070203010e0a031e12021806072001031a01031508070e0f15310501030812010b0c0705040b0d060504080c010c03111206012d0e0d02030606090a0f 65
    0x1100c0d810b100082481080f8407030b8881c02444420a88040000392210f4514030114600c200071800750740d240d0b030041404580710315036101800d082d140499200d80100b14119000d02c105852113040710740203000c1c190065000d1800340306907400c44900a40c884032801c00c15060603107462038007800304050425203000d07028040c11261140e5130381c2010340403a4406e13a410b0120002883c08201010500524840d081801515103d80c01904040220f28900350341b6a05907240c902c4900202904d080d030160500950140c20100d44407281c03040280039011044e4088428102c04000ca8031107800c001c10b00748106d82040300c4c005803946000001c00c04050504070020151443c02c001c20040240366030107420007141520080000e1206100140c1c1155690100c0c0a010002803014800b1081c100040a91180042c907014405001c240c14001c4e10700c092003656211520503400003428180e000c00c5403101301d42c00700d4a00c0220352030741d004242c5030300020784083e0051011400007004031301581c01c1041003041a5508 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 406828426 1250 406827176 406827191
    0x503030703022703060403111c2105190903020f0d0302071a0105010c1203020c01060e0108010b0d0f0b0c1603020c0f0d2a0801060308040e090607080a050c07020301 72
    0x40c000d41c0a5000703070143d4490395404445081d42c810701d0004070107000c1d000740141d071100e4905840039a01d003000a201403040780003000d28034115400c1944000c642d600c852582c800ca100a20300f8014401c182c0c40d842e60b1074142040040800b40050544103406c40b10b002580f0091820224101100c40801c1c07080ba00c1000150446e8a5041e0700418099000307002040104032401c8881031010428071646000810400c7d81102080011794002e101403541d040041c507000321071484074292000380e40040840088000100849442800780740300f034040485004001080a5071584003840807240054960900e02c00000d4201c04810222001d01e40500740f0341ea501101407800035610441e11a4132401090021103a584604141c2c55803010b096010001c2c080e0a00d4041006251104c2400000c2d0b0107507519000241d2440e00707200e6000a135000e40e02d00703a036841c205400c1e816000c0000d4481d0400341d004404010b130310b80d800820282c200074100700c0403c0f07946903202105418010b208010b540355280200 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 406829676 1250 406828426 406828441
    0xd0c0605211524070f2609090a060e070207090f0b03030d0903050909010e070e0f060d090c17010f060605070f1e06050106080414061005221e0f0902060a030216050303 73
    0xa45c207003514840c07558038402420400c1002501140048000103c0006010555481c948001c080c2d5129402540008031143d0700c9105464100c0155511000b5801c1250140603904071070150214a94035982d080c001500380c2e0f0003081d0b036403141c3c1c18811940c6585990000400d4403900031641803120040003403100796180c024000c6a1003043c2da8427804110003803a480e4240c1842000e02801d104024216410300380340c25102c00141004117030444012040080124990001600c0b240e5020204800058218031081882d030880b0555000181401404d2000e0700028500b6404212451f622141c1c1c0380c054410319090078210b80c84044018803490800b40007165017684034000c540303d94050b07035050715003843c22110075480381819210320051580b4070303038244441c3c1407100000503800100038401007076028420501c02251200b0131840450445480d149503400041d000743c5100100100003045104401d50008e0014400c481e12071092503004903012403520203400000ca003030741d040000d07a41d8174501010f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 406830926 1250 406829676 406829693
    0x30e010b060c0f100c080402060315040c020a0b150a1e1a031504090803010614191106010f0e070e0415030b0613090803010509060d0c060521152407 65
    0x3d4000203441507200d1003000c00c40301c0c0690307070720304000d41c0b110407141c1c8407902400440e0b4030062140160302ea0741004024952601e00c00c0d50b04031140740c0e018101c0c000c40c500c0c0c02d5510201c003604501201d400300400e0711441c1d99518008044038545603021041030505001035140504a6002c070f0088043e0901500262501c0e1008601c50300303a00c415488840d207494100f00c00c440e00b0315001341c90818180014007440e405407191201a0f2154001c02c0e06240c0340a24078075009025410b41c0d000644007038200b640e00c040802065024080e0602000c16240c10f000102c00c603d48010302040410401c03404144164855510004400b6010781a039000140c0301d04008420078024cd448a0159444039110342002010f4490314100c5940800e0891442e4603000400110000c058101c03544095225101c0f80000c200d4001e003401403840303480d02902e44411030442c1d00c2481111251103901040b0b0360820071440e505003842000c00d0003c45098864150b040d00b4080b00d681d4103800ca00c5540c00000b220004d006c41031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 406832176 1250 406830926 406830943
    0x20102070e0c0a031d0703020618060d0b04050121030c0804030f050d09120209010e1b070c060201050a060302011e020f0d0810120210030203150904081b060709030201030e010b060c 79
    0x207803405e0018040380510a80660888500e00c07407650001c034420300c01460040300620042d00340035442091954004005441e035032020600d8030007596034003035250081c1018042c19004060444140028003040c44c41082e02d40350201d002070030089000c64190400054130195406590000004209060745203415595002641c6112000c80d80481e000581c2090307404038210402e030301070440141e43e41380c51211100048050034001c4030207400523240311030992a41c045c168042c0200c40c5180c0c0385290a07001b03070840d40080c18084150b41419010700140c1d03000204401d501003826100000815481c80172401c2c034911400d00101c40c0a0540300740c0d0000d82c0211064020f034407841c410b0328000c0d40c0c5d59080415054022000390420321745001030341121f0103a80038540c004081d807409003116141383c0000b403684404403012a0a00d6011030084052140181000348030880c10008041c5c07414a01c802600c0c0e420136200003410591a00340c01c1507100d40079006040c0070750000d480f041d110440041419102d807001c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 406833426 1250 406832176 406832197
    0x5030412030e01111614040605124603140a021f05010303140703050412030503011403010603050c060d06030615030212030405060304080906130e150a1809020102070e0c 74
    0xc3d4010221300d000003155204401c45180301080c40700c1d140445450b481c05004c440e40d039010360745a80008480d141c4451007051780849002400282001c420100114014013a080d52500c2c10580c440040e00c400140001700030381183c1d2865113200302860205d41194103038101514210011030b80d554425000030b0315001e02944803050310416410700c0690411201c09110280008511031004a2011040e90041418600901d800da1410380c407441813402144403c1811400103500100400c100c184590a510001c58120028842e0b81c0c51620f0f490703a102c059061240c8a071500058001d516030940e8440e4005540c404810b005001c00181525010a600d01c401e0340a0407003201d0780c0c042100d012045606580f0010006800c640391512001c075075030002c0480c0c0303421072020440010720a640f1040c01000708080c010420051038400da085071040c00c402c0c407550203050025024400c0c610403003901507000e6420100020142d5450004134600480c1e5404045540c6650301440480310922004107146040c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 406834532 1106 406833426 406833437
    0x1111813060e0612010903080a051305071205010b09070f0c020d140109050c03030c030d0f02040e01170712030c0210050904020c100b0d081605030412030e01 69
    0x20303a802001148000b00708009940c9800440f008081c0110300091001c00c0d6031f650080c0c034658000d058020459212400600311b0010350300c2701410300390440d04840c001075403001800c80800d09544140c9031075091581600c0181002203c460160305542e4514a1040b425103007151443c5c03140904130790100004869001060002c6150300e8501030b19030002490604605e800381c07030070465405440c001d4100344880902c09102006031041d0819040c0c001c90021b801e11800802071080e50072200b100189080040f98a08000c036072042d514180800f2609015110854001410052a03000f0005880807030b00c0c5005040c80c2004001903c0e050800e6410905c0140c0040e05980104011000b20f50161103418800140f5015288040905448180454040f510b0341a114440c0341e141042005212103c5400c0000400c111002088046520301842c909032900500400000c02c0c414000345 = true := by decide +kernel

theorem cover : BRFrame.Cov 406654676 406834532 := by
  have h0 := BRFrame.cov_init 406654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 406654676 ≤ n) (h2 : n < 406834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
