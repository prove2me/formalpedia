-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3373
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:28:25.468345+00:00
-- url     : https://prove2.me/submissions/a89268ec-d6e9-4135-a2c4-c3aa6d99a32d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 606474820 ≤ n < 606654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 606476070 1250 606474820 606474839
    0x8150301091505130302030403060c0909050421140d021e0d06030c060e090a0b0a081509060a060b0d020304020402090a0602010b03060604051b070f050d08010e0c1e13 73
    0x418082c8101c64100c2450302002800045840241c544000200103200700d00100b81c0c0042943c003542d8204400013964016184255400c1000d0b9200441d540c2c10103042109010005e1041c0c890010300d40d40b14901c80c03030804000c90388040c4513030840c2c3c2401814400b9041101c0194054040108406404c0c150030300304001c0c0641d59040007442c00c10a680fa00424810031080c804c00600405842c204041d28528541c0010207000c0001d000034085070741d030456820140d950301200f04c01003c1c510705850700c0c4040c03a0705046c4142c60803a445040e03841003001041040c00703944108011203444610060030038044048040113544043d0060364020b40a001000301136640059910051506030000100d0a51075400d05040c401c00030b1240e440b552a060801000a128660103041040f00800d00c0e99a01100d1601052182e030721940a883c600c07540c60252049608540207034161341c11500c011040d996108c4500125104c1c000b04512100b880910601e842445c10700a4a481804c903140d103a0401c4d102c05028 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 606477320 1250 606476070 606476081
    0x90909020d170d0608061902030405011103090f12090307061404051e010807020a030806040e03040902070809130606020307020607140a20030307020a030305030c130801050a0b041a0108150301 84
    0x107112941c00210f0595003400c41c4074603001450020044c0c117003032800301c52003111a4442d003808600c81c3d40000021b82002420350040307005c0200007400a0b16400c01180140d81c58030003100e40a51071092550700310401c546001a903005120080c02810303254101082100c00d41c2c400440342c40404001d10000c42d8a40e02d00b000d40c071410181040c0c10010b01d10600005080c5c1c1005044042990040c04408012a078000c91003540301c0c3d41078a0100d00001c04258061a6118690000701e00501c041980c108100226004201000085490a0003440d89103441c0045a940e40304840169008100b16001801c101c40942038560088000307042c9040345d5200349007414034418085811015480292042500c01244491510780c150b006604100030f55001c184c0c6560180805010f0240c0440041c004034010011900690480d04102c44101d030b407419030343d02910040d0354445034241000c5c42c000c00381c2894480d01c1c0110a01c4c885103400815120700565150b0702c0074201035140c00442036001c840e41c800f40a030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 606478570 1250 606477320 606477353
    0x141e1908190509010306140901141203030a0c090806131704170109050d0e060412050f190302060a052205010f0e0c09010801090302060c0d090b010b12010f0501090909020d 75
    0x20b441d0784080400005084031070301c2c0c000c02c001644608040d50103448065550307040d9108a0032009200200340b00260b580b4034000c200d4849032000008120030801c0c1e0b500501c44c401419194000300c0c5481e0742065071100c00031075140004000340003000002c180b00c0000e140360184032640b001c0c42c1544401140c0c0d00500882c0310310090740c0d10354003804d04001c410800403421000529180805800e040b000910500c0f0310702c41c1d01c0110240a4401e0f05010707007403102d02600e44851084071a5881d842d0300213115202082825009806040c00081d100c11850241c0da01c04c2c2e001d0692845003070900e07036000186800b090703001c1d25990741e40d101c40b0082c81154425562000500700003050940180b504100f84007405800414550b410030303141a00003500000c0c2c0c285c0000c65003040c03a4846c050503001c2c8005150300503018064541407030000030180d20030402040610f440c030240546d01da0300c681055440d18090701c255400039901c01808c00111025a204a828174801040e01c1d185e103510b501d4003590070a05145 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 606479820 1250 606478570 606478577
    0x1b0111160f020103110c39011d061b01060518041407030605070e03190308061e0604090b012d0f050403120818060103050a240603141e190819 62
    0x5202980f802c20b02c0c1598450384450381f82d10401ca101c065458601106014140700c020303001645014500c2d21a200043c1c0c020304100d80b00c040b000300c1d4000e011520030f4030042c1946803e5001c1003c1c10001040792110441404034005915180d48036205001d4107070307010080f070254940100014405028441c081c105695610300400040e50815007410a550921107160035074096100000350003910706a4480310440782ea01750f86195902c00404800e1403002540e11141c0020041041c9039140d010b04402c1c00280d8801c1121503400035152140d040071120180701e001a0190024035a102301b030444010302d06d6103011030a16640b565243c0f01c5508a40980000c901241c00b00301c038007480c11400040c00c004220060000d5455a00c400c0d44801c3c0a2002034218103602024803a400300741d6441d0030140500401c01c11030250f0380e040c1000c11181c05442d85d901e6006004200c5185601c0100b0300810210800c05000d075154000448081d02000c0c0e103044503600002e0020445d4924072507404120410740c0d86 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 606481070 1250 606479820 606479833
    0x5090d030e09250203040305071502031c0212010509040b04060b0d290601050f030c030c070f110906041505040209010e090103030e040f0624030e031b0111160f020103110c 75
    0x103280c0b089940741c3e41400d808652050100704085040080e9100860b01401308042082e98044012405c5224121101d4030440c0903080001c608011a03004140304a00015540d0591741c8940420009444c142c0e400b82c440d800c0c1c0000329010551a03072008054072002401200c0c509444e91f10b5498451303031040c0d000c91008013103d0414201c15040e40250b4410000d2230054030744180882418020b0001528070b504580d400302c0012100c02d0100c08444005401a50018040c0f40521306071000c854090401c6003e964000086003450400340101c21011508901401036541401c050000035001207034403174100256180f50072500e0f120303041c0840c00703540682d44066920107400180416900303510914003101c0c2c50424100105c00120710300c0c481d04521000100d002003c1030354101d010385842c41d090241c0c4c0c000010900841d03414911620354190b56840244000681c1c4150710340c0d070f4040c4010790742d020010030501400107a09a80c031802c1031131050400007280140034441428507004110740c600140c0c00034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 606482320 1250 606481070 606481111
    0x9020307060e01020d11030708030903090102011113120218160e192d080c0307080d050a12020f0a050a030f050115032d02250305090d030e09 62
    0xe000a2001e0081c504216542031101c0c80000e40d01c8141810000412010303100e0311110070018011180351981000700e490700d901b0882c503559180e80c0502e41d514059841c200c0b001c0c01c0c4440745815941202e4441c2d1a901c0700030318202c07008295450411089074802c030842c1e000e101e0580000b9059005010701c0c20f1400242c401c00380041c0c0010001002c0d84c0c8510210b502c454070504901410b103080d0b4401d510140702c081c0880c1044410307560396034180c1c890010301c50b8010884400004800035075031412000c8856003941d550506441d10341c030030a0364000842c200010100c8038081c103c50603d602c0417110040c07406041c1c1c22002d62a4000b105048005000000c0400f580c07903160050118249400904000a5240103c2029243c0d081001d01e02030607102c041c0c1c001d020206062088801d01d44100b40381c4071025098948000750700c00c001c2c0c001d0706100303079400f003100c419500035040602d503041c1c031010314100c06401040700036018200e0440800440c0c0e24819625255003012601451010483c000401b00c1c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 606483570 1250 606482320 606482323
    0x31c0e0a0308012d0302120312161205251404032004051006030b01050c071202030607081b07020f180f06120615011e1107210615051201090203 63
    0x520702582d041a121a203451040d0a0131280d81040305d9045405415508542180343c3c110300415401010b03810f400020805c881003d0803c0a0301c8003020b80c0c070511680ba001d182c01c3c01320740b000c0c0c03074041a40c18181010240c0ca5000c0c1d83c1301d4070110080c03c0c001c000e80420362800c00242d01c940c000b154090700d00315611041e1990410310b00b42c41c410445050104d0300d4908110008401580702c2c010130580c481c10b00d4191a401841261616081e0381c05860b021a11600c14441e10500ca0a007240a44035000008058074461501a4094460001301d282c640c010900c00061036000f03c28281d900200340401241580e0319001302c00004911529010030a14140300342d808250402410035010307820b000d0001c1c0e4901c80100300c0d1507124241084c1d1180010003080101e46c84c00d822080d041c0310513400003800703800a0304040e03081e00c0c440c503c000f21404c044d02da5922002c19403040d6400861640f07034904034800950640c101071401c09812100c414169501c0700040c10390000c00c44401030996581c0c9146095040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 606484820 1250 606483570 606483599
    0x303190b0406051c0c092a0807081506040e0a09021908120c0106080105040f060e0c01050426061608130206090d030201020702060d0c031409031c0e0a030801 69
    0x2260104640b618110104040610707003142c600b522a80401c0610802400d090041c020f4000303c2000c01c400d04a803401c003080c82c2c0c0807001c0c58944405040704c00b01020320905205104a030a940c1b00052034071130783c0c90506411444030425603ca00103200c0410009113802d042c0384166100203002c100c5510701d0062049400281c80d2001400c030f1040000d200350b85001451803c0078030002c903601d59414403601050300400258000c0009075080005000c148800c0c40301c2c411605005020401130074500c25145661601240a80350201d8010310041011050381e0000000b1800144103060a0301100001e40341858011120040660f403400c0310481c890354440c4800c4d610407221100c00d4188121034001490a01841c081d2612550589100c041010310031b40648001a90142406844900400d202000381200743c4035540020700e844076015600042d20070390f600540448c0095454032014071042c41019041c0c2200f10b070000d885840380c2c2010075041100c0e504035400703681c9510281d414442911010f18 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 606486070 1250 606484820 606484841
    0x60411091308030c09010516061e020403150f09050a0503040f0603110405190e04060f05070318111c05060a0b0901030c050103181b050103050705070f0215040305030319 74
    0x1c0d424020540019044070031640c11203000d6114646601c0b604004903254411035103002d0440404003024000c105c0e00c1d811008065000c0079942010704100c6081e0b104a008138440034115034104d004115008510f0f610482e02251012404140001c1a4071024034080c0064001c49241d400018208034081c0442104809072844d440c05110b039030a007400b41c500c54001da000d400d11941e124940503840043c00001c183c02041c002020403010328180c140000141800c41c1151081800c140014060510920981444542c02c0304180e116500d07035140c0e20384858242c081c09070400b10600c0c548011440040c240c424251241c8003d0480d403030440110404e446100106034019960a001800040c619039a00300c25950280303000134035400c903809600a40d4082035406046d000300c4240b072000c200c803000f641c001900e20030388050041d41c44110381282d86110301040900704007100008040185804408c2131a840a441600da05040d103075200c4138215801511003401d07440641800010b50300190242160b000d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 606487320 1250 606486070 606486091
    0x120f0e0103020405011d010908100501080114060d0b06040213030f14280507050604121b0b070f11120706020d0509010c0b0a0f060b0c160b1c0e06041109 67
    0xc1c6850000380102601b50150300c40034918500070752099103e24181e000070150344c422904200c07014850350300200800e0003502c1c240e500705680914420603071440140a010054a003100f88540c0307488648a00e40c000e03000b81e40c002d0b001c20000c60300441503618140a180180c0d00e011940ba00d6203844482205c1108a8840d2030b0400c2c540d0005020106101c45101074020b005244107002d2413501509180e5142c1141e40e11110108000c95914100303409040d0091140d424004d20b00d00b8103030382004103074080c4140e07003038048100600301c0000c04540c2c0c40d80f80184120488903403450000b000640c20b000c12070b945401c59114243c01c1007129410840e03101c640c14142055031900e200c0c040000d20844190710068509079210010884806d082d034400405102480020864551289280c00780c60780101d525403524403505680000c0c12a1a096803400ca603900c1c150b06140c00ac0c5030100c00300e501041502015825555110071600c1102400500d00ca62301c90529905400380c41070800410130303006004040750 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 606488570 1250 606487320 606487327
    0x1806042d0303211535030a1805090106030e060c040605030a2304050105092a01031e0603060204051234080a0506060907110c01080c07120f0e010302 65
    0xc40e8001242042d01d03603c9a00c280d00035100041a1000740003000320120103500c0740200002c02200070b50384070b420480485200d0907035111410b954a410811042d00140b02e0b04204a1146a140541d0300002e62a0140c140e0b83e25442e40d400000715048002da2005012980310b540e80385405071700703010315540884407041860900d0b0400e5401085804014180014140c0c0c4901c42046159604810301c1e0150303040041154501e8185010f40c040c0400752000510740c070800e4800d2581410240040314500e406a00000803800d0840c01180509040751300d8404c44d450903003056200f0009401000c001c3c50051001580e41c502e001d0a1202d020a1040c624440f034012902150607600b00702c05030074040200c403d940340d8a0344c05234400d9030f03800000d03440b040b030910030029030b6002c1002c0030500034407452044030a00056605e00b001a00e030a15a143d01502d503400c00c3c0c070800042d60040b01c50340d8001e2081100da80c1400f001c4c1e9103201e0304488000407a404240d42c082c492154541c010700030150103000b0f180540c103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 606489820 1250 606488570 606488573
    0x307060f090504050a090b0703090b0604090215070c050303040906050a060c02060d0528050a1406100f20030903061f182406020d031407051806042d03 66
    0x114001d0302503688aa915003021803080b0b8001e4000d44601d5070098020980703810301420103001130140110454038110f2440c00280c8a103041d00c22250100d8014004500081807085981c03603640c0101012030304070001c0f200120b51618108042c001070210901e00080d500c1c20441086078080c8c09602c2003041151a400d8080181c68910039984100007040010490b40c0301c0011f0b11100c8141c00003022103000390020081407041d000d0b0403042c021010414104480c402244080710100d20445240b44c21207200b81c09840c0c8244502c60b4160000c0d0907250440c04a090b10445d420000e4001080b80d000358004103004002c0c4c82c1c00e00c020f603013040c010401f04460344440301e03000800c0707002842020950381c0c1c0d04000510000c82c580100041007603451111501d8000f420b11401c0450b124080c180040c483c2d0240d2000d180c2c0079100d08808005a56040c10f0b143d500c0c0ac10440d110750029886800341028041c5103003954598070080c0014044c50448111200030003a441800c03070095201c50f1864010340c040810 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 606491070 1250 606489820 606489827
    0x31101060b130302130905120d06050f10050703091203050c0f0604031407110402030c030712020a0903170c0a0302060604151a07031b110f03030c120306030703200307060f 75
    0x4100daa061703829200e03442c6805403100080003582005003030b0b401000a510071036243e803001480385580c0a20108081030321803081c03200022040303641c130ba0401c0700c480c4101c00042c090f0014290a91291909441c91a00d4030350400e4240c80c0c001044000c10404640300e5071250051280d800c00c0c5080c1c400078035261900791001461006000342c5110740d007200003059410f00542000c03210b40024083c005655034149108001c3c41644112203010000d40e21120b45044001c1e10700880e0000c9010b40c2e02c2011207800c1d0b42fa018080b02c500807a410060b141042000c3c104001400b0b40c411fa1806a009403420345070071410700c42642d0000c81d2003049103070302040c24007400080e21108a44d200000600c261100420701e02039400c0c0401030740b07070038000083c007601204202c02090703044e000c0c02040d603071003880e030b0b0040307040c0b503a2400f481c0c1c000c0c0b00700d03080302c4000d6400c645010003440d80144001d044480030303a600d80b0b41c031801103151684250740b55020340743d5092600b400c204c03400041c000c91400aa1400c100c04008 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 606492320 1250 606491070 606491107
    0x60308210601020c041a0d0f1407030f11060c060f151804060e070815040c091b0305041e0302010506150325030603080f0d0e010209060403060513050703031101060b 72
    0x61007143d07078803420705128420606900300814041d00b09004e0380c1142c02c00c02181c1d064610101e4a603c065000000102c0300070403900100c0733601000c10316240b0119910803c90081c0d0013809070f0094014808114000d808118550040b91311a85981c102c0c201000f0006500c0d1410610a001f8000c0b103032030500c0c0c000c0040200b98000e40103039002500089401a031400c012681d44501501e00c10010000843c0d09400c036520f0090388161161305c07500766220404401d03140307420b0400059407912258941240d0081d0040c1764002c2c803030402d1420850a1444200040e000000d059006030341d940200407036410410450310103000c041902504614001c41610903001004111030400a5420305080303a1134041e42004d00655844203080f80c0315110140601c1080d0400c0348203035000b42c1404c80b195461541807007100c0304142d029180034905402c0d510b4020140001a002c80e20401e10401d114010440c1841580003561003940c0c1e40c499568144002402e50b65a504020101c05041010140d00f5403030b154203 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 606493570 1250 606492320 606492343
    0xa09050c01021906090618210c110f012a020f150712140a0806040b01110606010f09091a010f0807020604021314010b090103060905012904030606030821060102 70
    0x101e00c0c580b841c503041000d0b121080c1c1d840043c6d80e258941200b00b2003003001c01e0703210801311808801c02c6400c000080b89c542014042c0541486040240d400160518051040d000c41040c1048003520030403407001e41d83c404034885801190f010110401085103004032000404030710445544144107464074181b8024402d0300c20003800e610b0030030781d00030055010380745d107003008805103040c0c54565008020150014004480640c412842d11003880c000d5801050220192039082d0003d200c280d99410041d1264601030404c41d0034801620000100000b80d070042d10f0b440312004441c0b80d205048800050610141800e0031410710403104100400d256000441c00d41c0160110391448040c03600348942401040310b0711154044590290006c901600e140d001884452000c0e071781000403075901c41c4c9800c115039003802903107900b500c10800542d00341004800202c0640246a440703280c565a90b031213900702c88040e4011590340602042c2c0562606613001404060030b400d42c1314000300e2400310f000139151800c0d8000d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 606494820 1250 606493570 606493583
    0x118090b0a0305031c052815090906020a17090c04020a030b03010f050610300212010e0708010f0501081602070f1205010c0201020a05040b0703170a09050c010219 71
    0x8150003a6a0303460001e0011030300442629520b000030503200b4000028010f00d0600b0504080118040c012a100510300c043d200440030b002a01c0441140c0028080c15103401540e070b101c034000824080340c6071084034a1548203c1d00142c3e03030800c002c80a404001c01054691456898104000201d84042945040004126801030303980008170070660090a602018a4140d0320f405c0018046404961260b4000c0d6030071120081c460713a10a10840351840c0b4822140c008082180c03000e1201c0205c0365803152101c0f207221002d4281002ca07010504100400d9200682105111090180860300b00c940107014200e564521401541054000307080c42c1c0c4098980c0c0a108248882040f22a00c24090070000d0103695214000450b915801880d25410a01054960354607004054140c203005208071014442d643d00c685042501d070984d03041d0680c011080a034180441924000303c6c4801d900d1526201e00019a03001400800c3c41c10322518102c5039410082c19540860b0800300e4901d44070345501d40e056444039 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 606496070 1250 606494820 606494831
    0x70305010b04120c030c08060411090601200304030206070302031c02180d0c050316060305150f0111030d050f04030f0e03100e0c0d03200712020402030c120420011809 73
    0xa004d0a00d05900d50025007800041c1601280d002c0c400318015004034003500b1403c2c4202800010030010f10350540b20640410203c400820032403140d840345c6001d4408220a582c2400d40d030341c01059140c0d1110104900682000178044070405101c13204603540c4143d01401c6041040c82c1c009416035180c40b100c810301c62281581110104201c8441e800e000c2d1034090f00b50350128000c0303c000980480f00303001c0e200100b814100001e40c011700440281c0020500109900b00ca04110001550b030309030040f84083c10b50104020404140f4894004c85016404010501e15a80b515003030040107502c00740c00c2c000400c9015414080306a40006603402619842140040c0c41048502550700d4045c81484154001100c41052001d243d00000b41f94040c0240184076000004000c103516115405c5000741c2d8940b9002108500150400794051644940f0703682c409450000c8882d50512902811141250b9850440046030200c040b81845901540003c1c20041c00d08007150382c601a450201d80900880560b070b58 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 606497320 1250 606496070 606496073
    0x51e0a141609020301050f01110c01050313120e130905061512010e010204260307030507111e0a0b1602190b04030602030105030706090b090f03070b21070305010b0412 73
    0x14003001d00612008408080c41980e41c0404034041d400034032440f8880e048038920050305500074560700e240031000302c0c0905549111300b001951590806080512013050b00208400001d040030380b500c981c040282c94804402d10351a041045040c01000e40c0100700e802d00c2840400904000713441a0031110048a010501380d01c400850354000318a1052500766003811812036600300103600902c10b40300300c01d000302e006844141100c240d03561034921500540d801001980b000c6071050029100a6104038a28004d07005031400240e1a038450500301402080646e007100054940b1110120050a414000600301041030380f050700f146c2410175004c0e01402c0803060100281c2c000349003846c003800c81d8042e21900c076500ca003040c4009400034007038140240f003440804559203000d110b00b0401c40301200980c92030080c3c50743c2404032031090784800070f0301071050b40c0021451001c4140a00095600b058405030810f4201084495580c40640300c5801e0504d4500140082c001c28012070381030b03508218103108102c925 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 606498570 1250 606497320 606497323
    0x702030c0d1410020d060b0903030415030209090405010c27030314070b0c190c020a0b09041d0a0303181a150904030f0e041118060405100903051e0a14 66
    0x41c0303000b00169010b0041c004401c203400d030740a000f5030036240c0020801d10341c40ea080c41d08140302e005155a85607000b40800c02c82e40103480400465418a89800341c205850078011491b44401524100d44a9440f21a426101d640c41450081400d05400d486d0700019114240c40060151034000a001c110106e005c00401440b114102c6101e0380d4040000c1c00246041180c0f0201da800129008000c407a2001e2160f0400d48642102100f0a0b0001c040d2030b0b1a9140810b920303200e6103c5040103130031588509103203942202590380d0411b0007070600045c0c1004d02c0715180040480300c60510b1488018024103005011070001c540d2543c823416004001d0380130740c452100b0340c540164402d010715803150300c0c40104020554804c8030b4414451045c1c581c1185602c028040000359550000e410011840030f118132000b0082e43c1c0403021a0340c0300984028a000c2d120000b0803a11080000c24402040019504000b00300040118984414002c0d544581020f80615615103a0034203030030140c028030390001c0c100101d050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 606499820 1250 606498570 606498593
    0x21c050f03030124080108100902040f0f06062033070906090b0903060a0f0609090b180a05190204062114030913050403021509031e0702030c0d 63
    0x6034103044a03120340e980c80e400403056400305070380c91802015042c1e01031084d00070785949050300c1480028001c03444070f03a100c00c1c1c02007090210503a80309442c0c0c07003500703138076003085c0700c0c1c210300c2c2e080d64902055981c203002025107108004c1c41ea1240003200c0030030100354050082103a00c80c0418030718555891071181c0d44c0c00c0200404d4a4402044a07000c14140b0100c02c0c0c10004c10300440e1090340f100041190b9a041110082c0911051941c05402000010314900031513817120880352030141c0d00040c2c45071640a02402c5409a000441d130703184083d001d024002c000c140c20b5902d55450380005009000e03007950703100e8a400e455110045800c0c1c0252111045645580100c8042d00e5501c0d881551482ca0810401501c401903105444801403803100c0b038240c2c1c4000c0200e03005000007030081303c48401944c3c005001441d00500a0b411401a147c10a12440d420b81da201d0081504400550301c03041840000d92400c07110307803603881c07908104000705001610040f4059103041411280c50080314160f05000c01c0058 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 606501070 1250 606499820 606499843
    0x1030b0d030e040c1e0903031b0b1305031312050c0901031a06130c02010c11010c300606050705061302011d040b0909150606040302090103080c0709060e0a1503021c05 73
    0xc0945d4910550390004074203080307034003d60f039448050030b40c808c05428200c44000f014120301d80b8980001c51403807846424400c00c40c0300d5000c807403030400a0090782c20481c016400c110106801e8101203802d020b0201f001124250040780c1e038181d99450b50741c41340c482c05d0070141e5620144618400040080e0346000c4240d00345840d00b070040c484c41154000084c02007080390381c43e1000c100c6401080c0100c0c4014840d080450070b46488801c0c1ca586401d01100003040c0c0d000103034415684030544600b4007400b80c05508010a042d80fa031a450740100c1c60080d0038a1380040143d01040008950840907030b0f441101c06401007410050300090782c07060408a03014210030414250041c04540038000302200006400d10075032045041c06110382c90315001c028080c0320314070019610084e01d0005101040d0518014462911032904550a083e500c00e440030503100789602c0401c02d00381c1e40c020405175100d207003c3c800080016501e078000d002d04680c005003036016185a801120400f05452a0412408000e44035030074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 606502320 1250 606501070 606501107
    0x7020606100509190518061c0f02041505010207080c0307060c03020f071e06080f0f10080a0b0117031905090a050d06060302010e031506010f050702090702010b01030b0d030e040c 78
    0x100510801000b0b840c034103200d224046d125100c2d2500da101810346a0500a060041508244100010522a8420090304141e900e0080c2c0b4440d03600503591441200000d550184400303410a1514001900300601a0311490080e08600d5001d90310340d401141000550f03c550802040f00300880c10102d03d0065803038680c82151003030107c0070480e1040041c203042400900d40c0c1c3d1032913282d110302c000c5946800a5030f4a40d100104203002c9950042c10481e84c0350711980041001040319030311450b0618090469030160748a04083c401403100b101c054121513191107400c402507142058000d001001144800c0b82d0604209000c2861003103541da0b464404001c0000a20701034292845082c494014141071004074081448540780c807980b03040114801501c417442c07100040c410b607945001960010300714000070081080130403070440180e03a034101e46402040a98000114400c1000000d0b040314969103d2520810001c081d82c00025804400107a24090603600810040c02c1600140c8880480204403180d4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 606503570 1250 606502320 606502339
    0x603011a0d0f02121f080703140a05150402030c040b030309040911030102070302030d150501080109020a030b101e11120903030906040b12010e190b011106010906030b0f07020606100509 81
    0x4148007070542c1401040c131120070390460919a05c030355600030040d101b0002c6c01d40000d502040411001d400000c0d88544441c1a21640c040c9a40c60324140076280c492208540480300a000540c10704015010100c0d20603102007004202c030000180d40e0b4082c0403683d41c4501d480781c4a410820544480d1501c0500c1c002e4025074903082c079881c000e5140d0b0404884601d403035140680d071031400850749000038215081078446100d10703424601d804020303601080f00b806c107041d00d0f086461500d441e05602c400e008449566010030b0190348128030100b1600c145030b031780200b250850020b100603101054104038011140121941c81c0b031000003190440c007600d451302754000c0700441c00141c44900880101030b90422002d003580580e032100110303401c005081d42c491050000c615024421643c82d039205501511050508124554101c10a9443c006098104031242501d68030104104024070a029800807205018126140780a44c0c00942c1c1e02c030020243ea208043c010700e00d1000d280600b086450000d0301500e907421 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 606504820 1250 606503570 606503587
    0x111120a02060912030402011101091e020907090e15011b0803040b1006090608090c09040606090b010201020715230708071b03080415020d0f1a0603011a0d0f02 70
    0x805410910504000d401200b0024245190200e248105088440119425610340d44c00450380d42403040b0342c8107030666880c042400400c3c5e00481031030a23820414a4110a141907106221070342001400e14800e010040d9814455842504200e541c03204200525461031700c5c0d1400121403200e14015062014150411b001d42032180744002540700c2e0f8091041e024036a2100e03e03040f15111b10358840c4800260314140e0070700c45180b01d0201c4581001c5944100d54946285000003000e900c4192800c442e080c0c1c2da01c0003044401c0190180b4117a01c2800d000850a145064544003001c2c5202408552070300c0d9101c002c0e034580741034841902400b140a0203802c44a207000100908100000c2d1010400700341030005010f00d0140000741c0c155565807540e11112161561b540d40c0103480402803030004003940920000300c21003014410b5040ba500e00d01d001041c1d100030296002c404c0785d001c0d4025400f500041005000d031100c0c14411614402150000e180e4590205804a00900d5900351500c8500d00000d50542e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 606506070 1250 606504820 606504853
    0x120619182307080f1507031b020f070515030103060f0905032205123705011506050322030c06020403030c02090718090f060503060702060a060e060a12020111 69
    0x80501c598002101d640d240c0728072039141d4400c1c8072000a407103980482003d2500b94602c20070300e41c22410f54140031484030010181e071403112201d007407074500590043e820044049010841103008010560301c1d00a69480c5550707000c140e200500014181c592108980c080e520002c1d44035081d846d07041001c0e02d46481d10400096543c4000000e4442c03100510a004603a03440c00d1100b01d910800c2200c014020b02d03181002e00c800c18200e940f200561280a5640384c13880b80c0c1255800040244035000009a000704462810860724090b00300408000b000e0082049220600c5240c4c502e412184141038660480c515003210f1a078182d01008101c036002280c00410950050441c10074940300700c030400030640c0c801004070744e00003810440c41107400120100300304071003c80d80719003c0022101d1002c43d500e40c986020a184c544c00b80d4844005034840c400308406110548182c2001d414852000701c80f5043c10340004a54140b140100f400c0d0182514002c3c003103a00520311840a0300000341500c01c8411210600e5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 606507320 1250 606506070 606506123
    0x30f0106030c1a030f040605180f03040914060a05010809071208070b06010305060307091a03010203100807080a082a01050c0a1b020d0f0c09060b040512061918 70
    0x25480302c0290300c000400c0c100600781c4c2e104941c801c011140d1569140c40789000303004d015003203000c500410940c0c3c1602120501c4000342501d10f0b4402155203078548100b00085601c449500700303501c141e0030f061200790382e52452402c0c2256000d1030304141607110030310101d080024650002003000861243c200c20800d001d00a46031142c02001d19103032503550a070055080c0c2d80200e440551580000300d003400070841a92005070005c0ba078400360804007201001081c2260700030f80da03585010041101c00c0003100410040d000c050015000584642006a540c141c0319006d00f0300b03171200e900c0507a542003104c1200c5100481840704940000d11203810401019403199008410200008a007441202c4c5a031480c0c111500801d039002c1e216454008103900c1d50300d0082c1041500b1519990880c4000881d10360306d00449001e04003841c40d06940314600300410040001061516200e600310f5003c00c603442403100d00c02c0f0742e445c01e110b00109403451041155400742406880c0144089424640712a06020b0300009 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 606508570 1250 606507320 606507329
    0x7090c0e0109050612010510050c1002091c0f0816020d0b0a0c1701033002011b0f0f030905030d0e030304060b04020906030109020a020a0609030f0207060e0a0303030902030f0106030c 80
    0x100c02c41c403520760091203034610070b61a0b50b202640400b001000729040144d0003076000300b903500d002030510b048180040c1c00c101520700e10010468010481030442d141107000303110b6180c0180030302c014080a135511100140a0740300003510588000c07c01c0310200864a00c0c50918507401042008031000510345074a040383c00381c83c0c040c2000d140150941c45540208070b41040d80c1100c02d02404242c1c80c6039a5251292100300504402d508a43c1c0b0005040d801241582802c5134140c0000c1481c01c400c1e4000e2094080606d15a4200200e042d041c1c10f6158005020380340c14542440e000c1884c3e840c0742009481d6109643e41c0c3e0f040350340780800c2e00001c1e01010003c0e41c0200d1140c4014443d019102c0700f000283d0040c408903940c444410401001080345681c02802c10120340c0c01900c4141040e80c035540111480304c0b0341600810649400441e01e140d060111310090501800c100045e1180342d40442c6610841d408000e050503900d8078078400b0f42d5010004881c0e032041e00341c003d002e070315142d203450040700140c2e101c0d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 606509820 1250 606508570 606508577
    0xf010215100e0f0a1505060f091813030e0f09040311071815140a2c070e190609060c05030f0d0b032b030207021311090f01022b0207090c0e01 62
    0x3082e07050030203905084000c8860085c01c00e42001003002300034225030300445e80554002411143c040111403c003210900c40d03103803c0c1c070031114800da508024281010540701c291041e40c04a04800e0955118402e1640040d01441d01003601c15154507103034035008541e041259100e001d0821182102c1490704925840b9020608030800301e17a44e82142c44080a94402c140d03800086140f0901080200b0060a2120030300d219124000c40b40e03c906440c031456082c0d0340e5200080d241c03042e03c0c400b4180915480704400d41e400f0004040c0d803910720700401204c000d01901c410414294a044280712040082d1030004400000040d41d4075070310101840240403d103240d134002c1c096010b000d1001c07804000100a1141003d5600718000b030818402c9009601800701282d0000080045e0600480907108045204005d2442a035446828408211008195480050466004800e8551340c00c1107001e003c041d809240114031112a410802613040800c107800611105260250410322941d0000166060354420388 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 606511070 1250 606509820 606509831
    0x1906050c0c16081e060106050a0c0c030c0311090f0c03092a121c0c020112180201120c050f2109070f0906080624032a0f010215100e0f0a 60
    0x4d1518001080706249440c4a400001c0100001c0d801600103007003007460740c5840c420402d065542c504061080750019901b54002e4603007442000300007060628800ca044602c030203240750103804142000d0000b001701c3e002c09c00200201d00010305c1005080320ba10401c04405005020170206001c9221100102912808000f0b1104100e4040031034030340c207072032460319540f20380851200027941e0405080c0001c0381040703415440c0040e40c42c541d00c20340480d941c2502e010070b1400c1c0b09000040c159041c0100ba001c00515100e107100341c450b0010301302c40102d40c0c4013040c0c07030b10381400c0c0c009040364290169481d80051312940800c00048008190081501c004803452114030b521392170341c80e08407142e03030003a902035611100c042100c410010081605190f2100340d83d04a4000c11004a418514006419109031881350b50512183c958502540100d0500340d0350a2808001040000c2d900d401e905823036586070f90101d02185c4800031882c002c5014004141081c0100c1c1040c1492003440002210318420407840c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 606512320 1250 606511070 606511093
    0x20d0b0a05041b0e0105090406080f0f030903070e0a0b040c0807020622020d21031a1503070c1103063102010503012c0915091906050c0c1608 62
    0x144035014164204002e20fa000800420090b00c4184802c00c400d810300600384519074071640c071802241c014245410180c4401d20400031228540b24186030401d030300340c00600601201c0c0d200010000200d03071031041000141d85500040c40700621020320f07101d0708242001110005907420840140c040d60f0613508640450341c074141000c1110311101c50500d0182242c0345000054075028101800c0140141c50b0441001c03030004030200c4960710340001202081d110307495504841203a20400d031001209680f0b40100c520001c807004561704c4024000418040e44400580030310050020306c1c0103081c0c0c0601200c0395400e1984081d50101e0070741c02170b40c084144101c0a00180c1e55030b81c03000c00e0140d50603103820341581d0801500fa0260710480c08904002d00c1000f4240e00c400c10a00ba4442c0216080710103003840c0d95900070f50142460300200380001550041880c00090713844071038001d02c1290401d100103460303240e9410703180c5284589031b940b85040c0324111184155840a090700310803150400111016a0400d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 606513570 1250 606512320 606512329
    0x10081911010f210609110c2b050906131e0501030912140706140417070c1502010209090c03010e01081902061b01020d1a0411120405120307020109030e0618130609020d0b0a05 76
    0x2811000d680d94548c4e03808803000b840c01900905410701005003030604050b0075140b103029503011540318112006c226031032160041449480040901802e18003840648456154549101d0721980d441d0f080004c030003002d107007856406040c0c48206070300610901c0740c01100c0b40c01116010041d14146c8141c030615080c0407032005020101e1b00720680c0090442c0c2c1107441e111030301d04000c5542c2c4040d400d554003003101a01c90703070700c00003110304c01d001040585840794100b034108001d252058000c0d11059120004a20300d48800814000c00d4940c12a070540c0c1d40d004100c02090710114084001c00958008524441c074a202508040c900310281540303031903024640c0f4100810780b05d400314031142c442400c200c1c208008443c0e84c42e566100c0e000740c0c00c85021100e18018038105030300454680380142d6550300c0042c1055440810b551081004607100303800c00780c0024101002243c1e09009502c00e107010303000011011642d4010038010801c00200310f45460828241c44090f20b540b0404512403603680402107540c0c0341 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 606514820 1250 606513570 606513613
    0x2280213020a410c0703060e0f06130809010215011211041107020d020f03060c030702010501080a080301170f0f01091118010e10081911010f210609110c 67
    0x903455560000188800e4003d58600c0c440c980c00d019200f00304248092041304108a400462142100003025400240254241600090010900d40100707043c4090700207a2030401c2e4800e600005415500c002500052340b0301190310381e010902a0407000005031100b80701d5001c10180d0b000701121000040554204012240c062090700c1c0d182d8030030311212004d814101c041d038481d00d00c090a600302c3c440c0e000c40000d00d812030032151821311b080004208803003d60b081c02414010000ca500400c0302c080c065803600300d5800140510003100141c4aa0180103980c1002030114250340c80044d9442c1e0700c061169a40078010b071110a590f42c52018000c2e5a10b13080c5a50250094001e0b80c0003404a642425172070310103180c0160065082c80c042c130801242c941c01c24007695182030181601103100c0d5515180100c8042c08a03015241407041800c0d8034585185c022501012108000701011202e80c11500c000d0000c00302030308401001c604e801050201e502c601c9004110488070a02112100c0f0344d9145407060b01d00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 606516070 1250 606514820 606514877
    0x4080d0c05040e011509080304030c030206071109011811090a03140f2a04050412050c0a0807140115030302030405151612080603030a02280213020a 65
    0x40010011064665000030140341191514900e403594030003a00241c00000e8222082e0150105c0d2034007090b07900420311000501c0c0d000003860034145980c444102c18582840068003810b0009007280400c00c5032100c10040401c01014100103503111100c5200c201c0f407105003440498549030004100301991404c1c2c4801c80300041010300c0c91800c1d0b40ea100124124030b030194420748981e504200c0b820005011000b0041040000c0030840c148010500409031a002c60f0036001e285001c052101140260581803c80b41c0c81d82001c59546004a000700e140244501c07015040f46070110f100390400806207480c6200d007c084009100c950510908603040100522004015030700c104010403060030508110b03040021405030a609040e00f01803044c5000c00c000f4001c40b0a00c50900e900d52450ba082082c2d0781e0014425001942029001440a03640c1c034450550054521004001401c1084541c0800c802999000d081c840c61844648005800780d000840030001041c0316030003402c00c08048481e00b80c00072 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 606517320 1250 606516070 606516083
    0x309020415141203271003090201020a03080c0c0307150605150d24060314070e06091318030f03110f0a080702010b0604080f0601050f1008090312070c0201020f0604 72
    0x2000c042c410049451200c229070034240c0814003040b010030200d8209420b01440c85085c42100c044c0540801101d5030703004003c20b080c90b244c20504005070340d0005240d24502c0c0c0c503081056054687c6a808103041c000d4500311034540c0b1002850608000348002d01084014034042c0a00c0307002c0d11801081071000580e20140e841d44030601507094016490781002022a001c0124482c046403030301c00741110802c07103401c00c1c004aa121080d40e0403070f02d038942d05154840150702c0d0514130040441d001a2040c410051458030580301a400d40301c0d0550320b903221070003140318121030000007840c4d40b070003070a62001612003501007850201c90340205560304084400381081056264030b003100721401581c894a028140c401150369440d8a4005500c0e2580140060001d941c01411880303d400c020b9454028140c0080303000f600082860700d03181d00c0c0c100d00388102c508079061102081d45e130800f0040c914081c50040c03c0305c03000d02c0c0090020480c2c101e403150102c18000c0c0c2c00d82da15006480240f613943c2d0820755004100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 606518570 1250 606517320 606517349
    0x8091203130602090406060f020f010b010e0f04060b1201030515010810021b060c040f09060812090118141503040b01030222090602090108070903051f0209030d0309020415 75
    0xc60071105680040e1842a1401070030f154101d03010400700c994a800010102d0ba03d10480300c5440d4041004031046480c0d880240011594400000e00807010f6116080c00340c41d0b40030440700070341c1d12600008040c1c9a0714006c16120fa00244a105100c3c07003e10060710039008522111301d8500090034094161040ca80003444940d2008410700002d501c42050f070211001020502521300ca0b0511000d4000c0c554110102e40700d40c14002d421014000c203610040d52103140c16002c000c5030700701260699520805900c4180c640e200a030058892102c1d540980e85d60100c148004604003070001000b180040040d01d04136090006120b2520646c4026180070307011110b4a0b00400052810222480200d80441d0b64038030296040600441611040301c41203418030307008540d410031542e01c01019036001c0c00b18541032000b6490b50322056199422826000101c000a00941295441a8045800104003e030896a03180702075035008000f0042100103d110b0790806040c0c41c02a90130340f41c60001e0f9204244800d12 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 606519820 1250 606518570 606518581
    0x16060203210c04051c150b0109181103040c08070927030207090905030301031b0e010b030718091a0609101d060a081f210213050c070308091203 63
    0x500c4000207100038101c0703038104030110b040c0e11500142c69440d90019200344d000350742e03403a1011044802041501010345000142981d23a0b0313106040c10200da001084c451101048011808003411041c802001c0c840c60000500c0100300714111220100d6480d80241d8030360396202e40c80c450940d8641c100820200c40c600b5000003122a410b1081d0b00c115100740101c03019a655030b40d031102076507160034080d10310341c0020004005010b018184034100612180600a0090500c2c0040c3c00c240e0040c05407804417070010002070080390048000906409044908504480d5078804c03e9000d80344203841d004955484406101d01418854240c41351500c00421503081c40d03104000885858100640c030b821308401d1000162807a80340c82d801807000a5242d41d642a99140410030f0314100d1600406c03032040300b02c1e0a0810056130000b032400c4006101420204083c2980d41d000140300241d0303d0fa0140a030342d02e4081403001c084440401030554500c42c1d12094400d6440c24400c5e611540c40c88100b24442004000241 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 606521070 1250 606519820 606519877
    0x50703023907090e0c0a1d1003051207060e2a01180b371103071506090c02120d050c120703060e0c03060d0311030c010e16060203 57
    0x18003048840000901d401d40381c10305107490015480301d8a180d5581000e00030b41041440ba04100020075100c4006107403426010001b5050004005252100010041088e411641c6c0c840d0f402150404100c903140b011482c0c0502040d408004100c50b030301d103042340d0715a001401180c00011200c03040c1045420100c2401720030505407244901ca81086550750641c10480084807042014001d0419195292180116040a200410021188100b040300b010484581e404022541c10201600d01a550050400d45483c43e6008924000300142050165460b01f0340c0154852402c07240d030709030f0500c4844c10f004000e903200c07005d5400c440310317100003084a000c284185070041c41c0c201030740c5100e00345811400020306200300b5003511003400098a1301c804005a0402d018181d800c00c100f640d00d0340c0342d4140400011208105500c2c0103090085180d00c0300702c5000c0a105a40031145020000d0044041d021482901c0304c2d0b86016100c8903144000e0b0204950f44000f0075a2601442041c1c7c15852080309882c21 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 606522320 1250 606521070 606521137
    0xb0f1c0c1115270115030210140301050f060d09050109170406020714210f0c01080f180f07030302010506090c0307080705030a020409061806090b0f0108130f0b070305070302 76
    0x14184902d02002540040f0092284003030808905154072900b1741584108884665205801c8040100c012014016a1851012241100c0080b0703001407040c0c14402c007140ca076009031006c0039505890060600c041c000107404c28070f0743c3c61150035070400e100702502186001c0d00850044200503406040b0510000300e50451266041d8001070020902e0054840c40c80008110034400c0203458021300300c05402c0d0070081044e0100000d090900c1031072442c00c080c20800004c4010200c0e81421900f608081c05042c1c00e200003403a41c1d5040c030903900420b40700d08010f230192505503203050085051400040990b015442540d008000c0c40d030ba0316140f074030350042c04c84480c2c1000d091112259420880040c80e00124441c3c2e8006104158500d242092b141851038100c8111781d0010780c40c40d00b0910151065501d90000705248542400d00301e01b60b85500e0504000101142c03002010406950706010500440a543c40c1c0b0075450b90380d060119030380d108d82c11002d82c01610b94007c0d0b104c01c84145000b42d0b001c0d15120 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 606523570 1250 606522320 606522361
    0xb0f0d030c02030c01050f09131b02160b030115180e100503070902030408040312050c010207030f0806010f020d120605030a11030f0703030906080402060c1c1115010b0f1c0c1115 78
    0x7041014050011030100d03100d400c0b1140140e4800d180cce0b2044044001043e90041c102c00f0b0381c850071580f60040c1024950100b8808500b0011403c60300c6400031600700d001d0014220401c0c0341d0b000c514066541402c500100c0c00303040e200c1d102d10000020031a1242c000c4912565018038854201860f540e41c0980c41418443d000c0c09121051007078914248007440036026040c040c1c2d8030f020503100c1200000d0201400500400d0402000040d502c1001d41c0005400c8640b103128900850b0044000d110500100559040306506004000740d44041c08003003c64801861401c80590b810b800910200543d115014840200030660700c01c4100107580c0228240c5922600103030889181c107440c000d0103810314200c2009001c8041c8000070010314264002348100c800f929a038003d10701111340240402130031905204000a140300080d00c1e00c40c400790031042d296207040100c5615280070f209810800030703000b81e0380b0300400151114400b444032540020200c0308a4203518a040098450b51200c900980b04000e6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 606524820 1250 606523570 606523609
    0xc01110a1a0402030715020c0109060806010c12030216050106080d05031614090301140916082112040b0601081506070312061d010807080d050a030b0f0d030c02030c01050f09 76
    0x3800071b5156031142c0c2c20711040c1e215502070116803c25600150141e285500318070b081100c02020860282d0f04000072a1055130019500314031802c034010b00718040d203e11410034541141a488440c200300301500140d0035200004140e600141401748112503038002207440d00301114812048128260041ca000da03070440144034014039109000000c40c1c00d5a01880c107111100e1190008c008904006004001495080e45203410019140108091307945c2c0d40002c110404d01c514816681c22415101d04440c401e00005800300028601802d2011501004450f400c0c0810500c03000988548500c10340e00c500700304010000ca0500302940c80c101c440410806a0514590380c802002c240c6285c0360b20564034003489e0000d14136031581854405418045a5805549503910042036203040720340040503a201c1103020701c1e000542441840014640d4200901443d03040920f0044075000c0c191f00125903c0300c5c50003501154000f0405000440c1c00c1d03c16000c000b200304c40300303100071019440d144c0440742c0014081903 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 606526070 1250 606524820 606524833
    0xb0f041a07060e0d111212060a03060608030d0b0301090f1104090206030a060302030c06120613090b0132030c010c08070501020408150a0b09010e0901021306020c01110a1a040203 78
    0xb62520304480c94501d5401080d0310004000314540c0d03000c00c02226416410024003409400c0d00c55a240701d010383d00f84080420415070006070303292103580012008540040041c4080c0360f440405548039031010030b030903101ea42801945003480c00e05000703100784907502c03904200e68155107445210048400c05107040d4031644410740000940d503008051800307904803000000c2d0b041d1651040615100740e1002180c02000144613984215101038403080c0d12a406481030781d100c11050481000414072828020040900340c2e0000c240d000c514141005014061f0528111030f02100c445102c2e1103490141081d816404014020400c3d44110024540307544524501030401c1029900d4a0076030300302c0d0300010b4141c0c0c007100e04500c40e40301c03c0407455041400290f0412a203d1120042503001c041406080764403020b01b80070402c24402503040300c03013081002ca810121692180402510743ca08484405d0016841c40a12a4554404a0101c200341e50046502410398498206800c05a0000f030080c0d03070600545 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 606527320 1250 606526070 606526073
    0x14030304032d0c14010c050303010504020708070503041d09030c10110f03010311010818030f091c12031a0d0f06060e0106030203041e02030c090a0e070603060f0b0f041a07 75
    0x8203051148584907030f102c140e50382c1c24101c28840111005145504100c400792600002c580044222815144103076000b40e62004142065043c9116504e0300520500c0000f8001601c044000ca202088000260090013140c54140c0195a01d008115059036140c00a400d03c40521038244d000840c0c440c05100054102103011410030801d806c01d91003600d500c2d07159048100c40350b90000d040c1780c2c0810340140c8201c0c00038949030340c80e95a001340c69100001420004691400b5613031407100070144140f0040e00e2075108031504d01003020211b00300e454404281040501c0c2c0b40105400f4003203600d03801c05003164210500e01d883d42004040d01605c280c0d0500d54400300841c4c43c00c0e0304102d080c041c190382d8901681d41d00702454611008048180902c48a0841c820f8410040e0303000b1490014030311080342c03684810745a990508000300b502c240761055070f00c01e81600040d40e580642040781150103078003005030f00b544c2c1e441100e8620321032801d024640c8581003005000c10381c480442c5d40f150010300c4c0251803c01026 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 606528570 1250 606527320 606527393
    0x1020c0d050c040c020a0b1303090b0a200102030105010e060906041d0123090705030912220807030822050910030210090513091412030f011403030403 66
    0x140c00300380e480d50400c0d4030410032800d050241010610f90361004010303900540d00e4101d145040905162080c0c2c8120300304209045c811491a0003511800018542d1010340d00000b4141403030241c030f50301d003481807120707056001c140c18800d89040703603010b03120080f41004070010040f207540621452580036800f4000403d00c1c0484040b03c9160341080c0c0c0c03001043d5418044800ea0744140144825101142c5103141030941e01d0b441c0140303130000c501d42082d17501c94903085140c07800e100c80034025031b02ca0240030410904103c2e141c0c04815100500342c00180b16039450b4140180c480000b03010241c01e47c901000108075070701c0e080105011300803a00e080700310b0302611100050381c40f00c8103403202d48078180348880c00c4c0103501d840c1204000202ca60b082210000d86094085401c403417608000c000c040b91b03240c074130806011041c0ea8000141c002c40d0181e5190210305040030300660415a03d951503c0d441c6400803482138003a03403203200001e071f00500850030305165540d4105041c41d941d210900d940d24000c0d03541ca91025 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 606529820 1250 606528570 606528589
    0x14060d0e0703052104060912020105071704140a140f0d0b07050901030507030e071a0d090c031205070503121e0703092a09050c0909090c0a050907120b01020c 69
    0x103c1e0707001e0000382003074400c1a080c0c40d41c400b0351120384003010002003009a401ca01040200d8010220000d08841c450005840c5c03400b4040c07002d001c96400400708180c810100d4020010b4943c0c1080d202410480f0005110f90070107180180c41c4150000c250941c21460810000c00c0c20050003080f03d030021f0040d56840c030020300240c1d080d01c04502d012400010303a40e0180501e507030110403841c081100d078170442001582c41400c1e1180b40001e12005d103d000001c09890b04840a404594805004007481031400041900b56448107880c4080440da4803d10389115600311030300d1541103402982480c00b103850750010410003800083c03128072a2750040803040088803c05108000e0b075180003401030020300b0149129020740c03146105040030040c688039160304664403541030310005040001c10b99910401c1104d00d04c01e02401d03543c081c40c03000400418980004035031050071400e90b0b54030320003540c03142403248035907069840e0404540c0b405040c9082d84004c1d07214041000f41441264122243c0401141c14200c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 606531070 1250 606529820 606529823
    0x40204051002030c010b09060d020f01020f150a0f0e03040e0919030309030806040612080708040b04150f0804020a03020609040b100512010b0309070303050d0b060d0e0c0a14060d0e0703 81
    0x30000700e41e141c0304d06020303c102e01c0392031400c1d41d00061510b440ea0000305800e00c2082d00034850051601d6094403640700300300003104110300c2000c0b1035040c0c40610280c541c940040780e012842c2820102c2d05240d24981c0e0003804000c0506000441c109420104030803218400180810a98420340b40c2244403482e0008440622a0080e20001070440060400818034030b40108030034011402c04400304001c1c0000b030102c0d11f403680c100c7e0803a5100c0c4550f00d40300d0103a05c15548601d07050b2801250100e032002c0d0900e1a900707002919180c43d40226404a4140e030380c4032080f40d0195000208d6842000942001c90051100440051000440040803000204007111880039840011000300d50301200032987c211881c0908003c01c88181985402240240d030b90f0f0850000800f00000460101100c0c00039810100b542d41009000700d40721050b0f49a140c0061204088001d05840345040001c00c81c280803840c003080d0703409454400409180c000512140360301500b40c42502d156a44040c0d460b0b42e1051200d4405103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 606532320 1250 606531070 606531073
    0x909010308090f24090619020d020d080c0a050d090609060e010c05090d06090c1d10051f030c1205090d0206010e0702061f030b1e01230609040204051002 67
    0x8203201c0c410300948541181940340120480041d0801c444c60780389404030060311409085540f035582c800881c0782d0b03000d009402e007000d1000b400201e0120b600407400b0300c0450300741c0c0c1c01c942050b880d03045e00700c920b0300060741ca6000d541d00c200071a2031598843c00080c24603d115407408150b500059440c0303011542c8440086c2c1c2c40c6540c407000b40a540c8400e0150084031031035480d040c0d003010454000905000100c000013017040c1d40d641c1003d002c1000d900e103404000d1104600814442c8c050144210102004441044c9401c040f514081800d1801640a00c5a0801c10051600d091f216200650041c507075031004030f00f0300800a201a64840039405140d1060441001a03c0107000410010381381510682041c500c5450704e00804c021183c1c0050110f0344401c0703074410250524001e10b80000840c00c4ca41002d0042800d42d020001e441031550fa02c80e83c0300714011070410280c0e0b40d891480c0380c90032440840548c0c000d158107a0140c075141c944060042e000300144010301c0e0030f0355040000c400b03d400796090b9015 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 606533570 1250 606532320 606532327
    0x31b0206100b041805151e01091208160311010c090302040c0c0b04060213120501020c0c09010503030d050c04090606020706081506072a090b0319030905090c0909010308 74
    0x3030800341072a005041c042d41c02c509141c1801800f041800e0b0191141007036070396490026411503c4400c405800340001b80140060842c11400c8600e40c029090178203010995003d4000340342c085054810f0740298201503101d007010000140883c298900788000c0d01048000825102c4000302841090701c06000d90b243e0005581c514810709c01a12104a115021301401036a090046148201000d50040d84010010391760847d0540b09950900f03107401c41102c3c40703012076009080080550081480f60720030b01c111140c0404a500300200007a0034010283c1641040c0060501c07441507410a40d00626012426800d0035220169041212219413000005a02c0450204078080d0410500c0360403501010103240e5a01d0102c000ca03109104450000b031003c21001c0104880180204020402c12a0002543d80143d51030300c00502501d0501c18461203030080300300900c00150f00031144211654076459822140b407410041013000700c4010844500c02ca802c0180000c1a42d801c40814065803296100585 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 606534820 1250 606533570 606533581
    0x3040f1b0e0a05060109150c15061707030201021e210301180e07120f0209090f012414030a0b0103061508030909061908011b110714010f031b0206 64
    0x390789014100380c00c0c4a14040500c03000343d078410045020341d07284000d2181e44030b2107400304032060039030298060039001c0e516042100c1c400150300098100d800350800d80220400c02c42070b42d521104c0390312000b800340c0e00c6190443c89440d280d101e40e030382561240c03064591456a1462072200000590390b40036901a0000040c8280c80e40b500054407400079416040210343e41d0b06503100e5658810b8083c401007013540c1c9040204001c00601010000307640075010164504007032004555034801402c144011f542448a4420200300380c00b510000d010002050544041c988800c0c0c5da611040091002e03018003034002414086107a8950f11402940f10315000a100703000c1040f181c481788020381100380359800400c54050a5901e0300010743c0c00150032a808040c3c501d800403a001801035517844640c05500341072511241500407400211030160315203030712507201880b0350f0450301c450f068060142152940306508007103510030070b9800c10750344103418001950848040d110035505c080b00c480400581c030401c108071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 606536070 1250 606534820 606534839
    0x1090611130303121116031b0503090910080307030c0b06010c08090402090d0503030408040807060801150e01030e100e070b030405060a05070c0b04051c08100909050a12090f05030a030e0603040f1b 86
    0x4000c2050429003230725070340c0c0d41070749911518400602c10390551010816540517508600c0003400c006045a45e16403440c0f030050507600d00b0400030b0303d1444079a030018240c1e5028114000c0e4240d4001c11152400030305034104002904281c0560750415a40402000054410001140214081c000c001e84039444d05a486141250541001082116070401081041460001e214403460300e0b0501004000d15100100c00620b8030041600391445040d4100403266806da0001502d00440000d07505582e0702c8880f46446880261001440c9911080001c0c1d03164485a1180c3c0d0481c0351454000070728080303520380c1d20b1528001e0383c0544103074110001225024000a10440c000d4403e410315141500e007543c40049011000d10420341031940f10498401080400d00c011084554480c05030004043c10301c07030003043d10080b809600c2d80c4080c9483c0104251500080702180580c0c903954526096680100344a00380d08007800480391003183c1300d580000a090000c0b06c0410780d07082580a51178918007180038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 606537320 1250 606536070 606536087
    0x50d0c0f0609080c1f0e0f06040902131401020a0213090206030c030901050618010501030c050c071e08210f0d0609050702010c0306030b0c0c0313080109061113030312111603 76
    0x1140300e4002d0141c280c0c8040100700310005c140c1200d04203594200703052804564200c40d20704d0503507440000000c010441480a034003070aa009081e000204001e51600c000d00b8818403e4081ca9015a0004021000600e0140708500300310350880c2000c50703da040c6a0118103150010349100c0e05000c00401082402a02407198650110080700c08124070022a142000030314418041d950415880d003d8010480d4042c10444234800508006c071950540e60742200f9240d5103440c040000c84003014040020300720800650040c00000352120840110310480182045600c2010000d03165081401640281201886880014030041a000c1441d2070010402401c540411940400381850681c0910200d018103ca21b0b910150368691142d45a403c01c06c0c07545580116004055458106640412106c02c103412010000344a01400d00c1180c0c0c40c040364140a0054030703002003038440b00b40e1701000402d11402003800800c245a10000c0c280a08441c01080c583c4428000908001030301502c80c1050340c00380a1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 606538570 1250 606537320 606537343
    0x11120702040e0a030c060c0302121003024b130f051008151315090309050411090d0c051002160918031103121305070603050907050d0c0f060908 63
    0x1a045510366544e001c0c2451446290151030b956845003000c04640c02581144c018032a0b054a2403000d2502490f602514200c0e0301049004031003181c100d444d50000f00300090071018564a0b601d4141c0c40a14007012030080120010005000c0c1d8204554241c941a4200200307121588000c156580c8002c00d0300140d5202a10121800d01020340402c2a590041055440521020304010a50b11112131046c00b0354040c020151002c08000c070f003800e00e01da0fa540515003052084e110180c4207640d034400c200c04ca8002c01c44941d0a641d080100e8003951612000400c019031240d5102c43c40c80e80c41304d01191003807913124140e0300560702c030210b00c1801d1051245e5102c01080000420301610f211180072044074400c005c00201400300603051002ea81d8001d00c156405024040d000e100c691401c0a0150b82c8003003100c0e020f440300e0145000100f905480b90184511134000c0400900c00503241400b40301d119640c407030b416668200d20403808030b00f2203c00d44000c13004203020313902c20300d01d01c3c01c0c00c2002d410300840090 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 606539820 1250 606538570 606538573
    0x6020705030307152a0e03010b060a031e0c030b03061303050405060729011502070f14150d15080d090b0f0702090f090d08061302030711120702040e 65
    0x1010440d5560000c2100c0680341c0c003821003032440c14501e640501804c0070b04071a1036103d981a0126265800861000f85c0e407900030342c0c40035046601242498201c5142004c81d540148040000320300150182c0c001800b118007188010404101e80b000300b600f05c1d2143c896100010345c8840c11001c031031800b0401c00707400a1030200c070354542000300c7e0703400350240c0700340e01c1018040c00021a402e4240412290103603000b07210103a8105c403084508000b003544074403d01441c8030400340000302c2d819451001501c201500c101403804080c83e42840701115401c3c0d0220200b44d48955010507400d046403070000030300901c8041c0c00c0e01180222004410a0071030125801c611820741c403855071b4401295229a161041f05c581002c00b40e030312803c00e100700c480b92203800800307074110071001c080c046041d04c0d4511b420303c40c00c0c405007550000018035000301e40304941a104076502c048152128140c80001d41e00942d008081401c000780300145004586041007117007500c402c00110b01144210035410140140c00f5645078010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 606541070 1250 606539820 606539833
    0x1090509060d061d0703240e0a1103010e0f0f060105091e0601030f0e0a17120c030601050c07060903020405160f140d1404060b0402030412030e0c13020703090602 71
    0x404604408108100074001c261100a218104c0c18807a49a1050031201416205110344a050100c042c004140c8210b25a1a00149a00714881541314030404002d500001d0104480a6151072183c0c0f6401506503502d5541c640c0c14a24004003000703140712004e00c2b02c0141091116805006e81001016400103001d8076000c030400081180101540e03001e40000b44004e09180c031100d00480c02440c02c1c0c02c45a031036904d0410340c007480c00400a85a543d59228070042981c840c0301000341409030003000384005581000201003061258004003450f0300c80c2e4180740450414081c000b10320702d0624203a0100011411400c828400e5003402c2c001d1550184a451041d904468880300086c01072307095031444030400c64061111301d44180214125015204001010b210104038414814001c050a50701194075a240c1460440f041c141402a40e1040d90000105c3d64400020b020130f4019182c4042180d01c1c1e0700401000000700e50310382c03072040703040501c91a0043e1205841d01c1d003c0c0080031190000342c00e550141 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 606542320 1250 606541070 606541081
    0x1204022103120c0f07050c0a0801060513180204050f040b09030414130e06010603150807150c0f05100b010f0201060510110f070b071205040e180f1b01090509 69
    0x45510000080c40b05040c07594400d10440d95a000c0e4108040e403a0b2400a185420f01c00300181d04640c00000322203040d08240e03640c441c2070803107a2512801b03401c54481403400c0040d0202c0d60000d4480c0070050304010391903103158000b0f811120120b80305c1c900c00d07204006100038031001c12030740c1e540311206000851030142842110088007404a204512410703050446072900d4440f81c100000c642c05550407540701c0e5840d131001a01400e001c0602c981400064800020325403c001034250450f080c1101003084030b0b602940c125003000201c0e0069a078413003c14260000188100139105290800d51030008403040d03000001099687e5410034842107a06044090101d40d82c0d240c03400708041894141010f9613020010581d00701502c401c40a4082d00511038001407241e45c2d04000c00c9000d104505030b109190203000241c030341e80214000d00c03410003044c00000781d0440740c50382c01a44000d040b5044a00103001100002c0c5044649920785450b82c180710703088011540c00070400c3c405808110707020310681c03604 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 606543570 1250 606542320 606542323
    0xd080c0f04080d0f1805060f25200402070b1b161208060f0306061011150105030106060f0903030c0629090106020d17041a01080f16060203090d1712040221 68
    0x20280800500c200000d0300c0041406180040708907241600720303040804600cac0c14210f4910550106a060045000b02490f496217400c1c802c85001580c031a0000540b0b80300c640003c40d215200da103814401000c1001a00c2c161140c5564603441c652050342e640401c2008072a008110610251020f40600d220500400240e0340c00303d0456803210080d01c1d40741400344086e40484240d01c0303843c8007004501614411031040c21040e05003074181c80065001703014203951400100d41034860700c0301300000104030f60b0b000e10020744a945403030511801540b002c1041c4e0140c001482d0360f0b0b16040c00080e804c0403810280a40b5042203404c4900420340e070f0005d0010003204540c0500000c401c10600c070306400360400014100910041c000d003262800203003444c165030b1600d10061380c07001c8140c80705403180b0805480b14107010b003498a06003507609a601031410004644103114803580454000c13591941d80403601082007a03e84090300300140750030110103030750a00740103000c141650b10000030b40d801c00c020f4003c0e180500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 606544820 1250 606543570 606543577
    0x6060f030b1f030b0a0612140402150c07180902011101110a050d233304020a030e01020c0c04050603151303030e0d03020301170d080c0f04080d0f180506 67
    0x30005030b203003009454030700300c008180d2040b48a03402145000081031055000c140703141104140b070f0040103840ba0200e4240c0581c0404c8600940c880c42000d404050719981c0b60142c42483c90607400c6030881500c9034102040071030140d00c6040385940da02d141c1019903a00c80340c0380e000700c80e100000304a1050100c9a00b00a841601950030900500042d0382e420a003480e804005c1d44070801c90562a500200091010a2a4160340c50010b0200c1d11824691010000425003200074102071f12200c500070b440c0520000e50090003170101403503911a801c041081c001c0c0004c04842c001007004e0440101e5490400c021160b015122500179405210642910002d0303414603074000a8031001d01c00e05c0d01380c43c6001c6014017440e240c140101d0085a030042c4040e078154020354145c070309045003d0007901c0400030003652240d50810180000d103c0901051003480400020070101d0003114691b4503068a48100c1c0e894044140240c0d0001a04d07100b134078007419480340702441c00c05843d0038400032091411001070b25500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 606546070 1250 606544820 606544849
    0x3030c200309100504080601090b2106070c0809041a01030630050f160f0605070b0601031a030304120c0608040515070c150501030303060602011422020d050106060f030b 74
    0x52203038160f481a14000c0055900400d412001c40308a5a141c3e01030300c0146c0300040f200703170051080100c007590280110b40708440da250a000203164a5440401c04c941c40503000700f040e02d00d03001c10004008552100c0c09016645062401103102015180300010100d50f010341c0415040010441403031030741c10a0003059807803485682070701c0181e8404c1d0b0912600705640d00c5034442c01c81c440c541d42412040360b01c24185040f556280c121201c019a60b0000755101c0c403a582e4000d081601a0000900c0380d0b0280d0300540d10701500303c0704410700300003241c00700740780d6403160300a09400d6142d50700c1c100030402400d4506016124a182c10546030800340e031003d64501c004e0782c500e0758101c901c900113000c06109010103107241d6080b48000700035041065111005260a02064000038280b1601081d454014010074103803a00400341400c03aa5a80301d03030346944151800e2162180001c80f0360f00c0c00940e88001410701b0a038000d03000002c10605d80b10300034040303200d598000c07018141031030082c10265486184400840 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 606547320 1250 606546070 606546079
    0x60605010f1718150106020a050c010c021c15020a05030604050604090302070e4201030501053d08010801140c220906060e0a0e040f08071a010303030c200309 69
    0x40c0540e10b040b0b0130851801d04112000c1014800060b200e5800980641c040740075801b0364840300301d00001142c0441c0c8060713000c2d42101e011402c03200001045002420018010460820062003200006090f60700c2003003a180001d00110a00c1502d140a01ca0345401070000c50307040290f0310b001d5901945406051282151820705680000c0407241d2004000750700700c0c0725440040242d5240954525501100c0d07604081c50320701900a1480e41d4024440c590617600003c106c03243c0421000c0c2465008240d10185120b10607045038a20150310840c10640c154000b982c40f01c884941c141b560140c00c6440d40f400a03242e40081c13505226010740a00212900c2c00403110f2641a2584040e04103107402c08254414051580f600e4000518143e004200c81c2c2941000c66a024070355a80f01d00c1004444010764015103c1d11811445c000010140001841403a01c07441c00c2c03441d001841c40d0019080d6800360b20680209496901c030395401e17544084800c4007141710b085c000c423801c1408009143c0d01c1c010703884000d004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 606548570 1250 606547320 606547351
    0x31b0f0b0a060f150807030606020601170102040f0e061201111222150c0903080a0804051204030818060304050c1c15200418020706090807060605010f17 67
    0x90a078942c01010180c110780b508038000c1a507511380c103422109112002400aa80c003404961000c2c400e0042108540042d0b00401c040c0e4280100d44200011000d054041594208000501018811602801000010394140541c5854024400501300c12001208075074035100e51194017504d8142603560b01101c00040c004141e5881810721b1006c500742c80d070901694555100102001200d820119078034a1020050013442042030040e1441480780c0002018080709000100c9024400d00d0540e0340140103208482250811405075081c540c00742e0420b440d5490b00140d00c104030203170b08444a9030782c5000c0e5030292651034113031180c1c0d0301c400e01190824414008071031a0071090b07206c11409190310b40c010b010010495803481280000304800d0307018012407026454000700855418040d6000c40d6030311503a0508003010100307481c0096100a80c102d82c0c6a07030300c2c803605010801e00d5014207a0303144502d8000501c1c9003410005841c0c6026000320004011405840c2c6074900051030420380c012100c0d242c004034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 606549820 1250 606548570 606548581
    0x2205071202131b09060c020603040b0a111611010906080f0c0408010c0e030105060102030403050a0b0c1b0309130203010b0702040906140f01142b03020c031207031b0f0b 74
    0x16402205202401d200c0c00c08480f40000004101c2d03908164800352100048a940c454040d0368040c51104065401903061000034080b840407002c003540014010f80016003841c0c04210503001303070070065600710000c1000003040e04100403c49d80001d5050242043e007000340c0780090060007027900811403400d0400c5a030100e40304410326819600545400f000a00141d07001031001000e003a528a0142c1c03003903080078040f500e594004000c03681541c0c0c00c01d01030b1040c0324294541c0011010003904500051a04010955001145071841000701c01804041c41d40e95a610040040701c000c0405242c010030f204000400c51141480102c0b0221581030ba4089804212814210700600901c0d8208012031049c90070803130014208490303d03040e1074501050604044041c400d01030450a400d409149101c8010350583e5154205044840490f2003481101e000c0e44440020074203020f0507034103007640204042946c008060700600000700d8500842559100d0108175250b10341c8030b014aa101a18105c070500120700c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 606551070 1250 606549820 606549829
    0x30105150d0902152101060c020613120b0a0507030509031b1f05100816050f120a0507140414010e041e050c100302030402010206070f262205071202 65
    0x70b0105400a103d074070680105002c072801e55104894012000d1184807016a007008506031140c11f07696641c6e994204030304103500b40022039101d00c04000c100c40006600044500d0406e01c6001c0c00d0b4402c2014a880c2d003802d00820003a50307005001e50050609010400064040000c19104010650000b0700d44016503001d5141c20050103034441c40d02492254154512a0b80c90780206010b101c04404032804030b44e03143c00190b102c0c00071107841c401000701c3d05020891031908800e0020002c1006002a0b44000c1100c0c4903440d10f00401812602c9401107a0308001d5000c4a046843d07800d242500c05204d81440d28034103002422050251000340c48004000c1001d001c1e0764641010440e040030500c206d0b079004d909209039104d002401c032074400da803241c1c80052894071130700a0724001c40e4107070024021900e6180080c3c50070050058102e04114950242141b101c0c05a21002509071400300c0c11007050402c0c1c5811080074010b0b0100002032000040d8610006e0000504401150842e040f9101054518800203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 606552320 1250 606551070 606551081
    0x50904050c0123031302030706050f0d0203100e130201021c0801090509030c0d0c230a150b210c010f0212030411180a050f01061706030a050111040305070803030105150d 74
    0xc4a0f00301c404810080c0003003400c0354099409008600725070005170740b0700c0200d40c01d02c00d07001e000540641c28420010072030070a801860b005038104040e116481d4071410a00c001c0481201c4a00039610a00280b50555805119240c0503c880d40c0c084503008201c0341c03003d0451881803045c004003540d15000100e40610500130f0303911f55582082a200344040085c0000c041101001096829005058604c0e0070100b29081d945030121458001d84120079aa860f000305520500c43d41001c1d03161140da200d803880da070b45c010b04064000340821880e102400703810854504170041710440d05000f0b0721900e802485400003500741e0b102c2c01c190f14669482e40e90340707420303001d07852070480c2550040c214020750040740b40d41c0c042c2e051090183c25004c000696a5000004030307a0000c1c031440d4007007880000101312080030640e400c1d6024001904a90400b05903603035440c00c4440c4030303003005032514010405004215080c4107240c000c04481c5d000f90300f50b5040c0070004d00035580750391420f03c1c1003a0005800c203003a42660040c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 606553570 1250 606552320 606552377
    0x501261302150a0807020a030f05070f020901091a03030306030346030b04090c1a0910090e070c110918010510050f0d050c220c0315050904050c01 64
    0x4408070585400703242d4103980011254070041014000002d100074400585020b0a60f0969269003d03400440d030280c4899102c42016262030000789107201c00740c1c4842d841e013070080024120005070210151080010300e07151004182c400d410030010701c60700707541c0041139483c10030303401c1c2540300200721400b20000c6030b41d800080b07210716080c0540540003000940c0c1c0035840480240d05e05028212540040004455030210000c000741c4085400703018840d01c0084c200d021030304891041c1d2504040c00c1c0000d9140d0b25185450300000d190007000e0000482c20505c45411250303e00f8003000c8510300b650703802c1001c542489014040ca0326540000c484442020100d05240c2003407000300301a0034030141c4040582e400303009990141c1d102590b490440d00300390104240d03150300030002e00b17041400c40080100740c10354000c1d43c82c03064000c22081a81ca0703d0364840e506050082d80c0340020072450701241d111144209511143c42a4012400c0001007400800e806140b0340007442c02000c641d22400039454003111400d035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 606554820 1250 606553570 606553579
    0x50d05040803010608130c1a0906040e091204032616030c0b160e04050a0603170d050c0403050a02040c020708010e0a0b2a0c0a1203090c0501261302 65
    0xe000a100d4503000550681d030060340c40c81c036180d07681d6245805100301508001c0110000050801a555600c9500504007403136100c25440c040b5420001180c40e005900302c4000d03104da540070301040450070450700401c2c2d268050300b41c1c1031a14607100c0020340710002e100c00c1d030070140c101c8240200d03403404000ca41c0314020400e4040c00d165001d0400030000142e0080c229840c5280c20046920301880014000c0302d1140d5984411000c5144d90606c00a003030f01078000c500013602ea40011000500744803c22420b0b080c0340e0100d0b92640d500d03054010564001a0190261700c0d0200424000710344d0100c0c10100e4142c0507900800d4070340c15400200d03e460201d911000840d441c00346074485011020680700c2d82107004003100162130700c1c0c00581c20110550150380c9141c5441d41e4941c080f440300154094030309800960103542c510001c5446045a4a0004440c0d800090f66101484100018440f080c80904800e01c0e01070006035004183c04d0b0b00e0001951200d484660b0344000a0030551140d08090002d80c3c00392 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 606556070 1250 606554820 606554831
    0x40506030108010c020607050310120203120f0c160f05041d06270601120b07260a1a0616020d05030f0c0d080403020a02040c0519020304050315010e01090c050d 70
    0x3003502e402060040ca0010050080b103020540983c4184150381c01400c00340c141d035070503601c1d201c0f20542c90310500c84202c0c0c04d8000c0c1c1d03c500c5020740924003e8490f540c50f049c00e01c2d540e246443c143c64200744001100307900c613501c8803000380209034910131107c05442040c2c8001640928407518600341001d5000c03101c5140c4216810000c3e5051450f05007503100000343c4094080520014200da100d84d02401100d200200c80741d0a50301003005044210307001401d80c240501c40081021102211510280c0041c08502d1240f05000324811540b00303884448804245a00d00710360004002070003407155200c02c0c20b0742c4001c01000c3c42956511814400c1d601e0780300c000c072544c6440715088000c0c1d0f5040490224064043c0d041c0d0803812034040c0078860310070755041c0d000d1b10302d0803101e40c00c0000410380c1210b0081006402e201e00754440e803001d0380b01242d003c8180c00540d2200e28250402d8a411040342c1c014400c450703020300404c00c000014040030305492002c030010a15614054084a5030f000c1e20324102250b90a01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 606557320 1250 606556070 606556079
    0x6140f1c1508010c0503091b060d0e0c01110a030f0f110709050a0509060f043905190501020c15090d030c020306010902030c0306091f0b04090b0405070906140405060301 74
    0x541882180c40a40013801080000d040c243c509000c1283d40c0d5403180c01c4008020710748151358800c42c04841c0c004280c28101000c07000804210b030b0310b860b007100407540310403058280740d0b070031201e551010520500103784030381135a034000b04040ca01003948400d00c00e402a044100b1801900600314009401c0700311403145035140b2103040580340c00c0c0c0d049400c15180601041d030921010502d40d20500d844e401c010110b4440d42c0e10702c4141c8802e83d1140440c0383c42c1280302052000070844041c2c000034000740c0a10340c1c0f400c000030130841598038a0894020b0554217010091b698021618440300e03181129001e500c0c15802c0074004503480f40c1c00c5210342c080351100c800300815401140b40b8014a0080d02224103580e21005290200e2000740e4180c1202c0d6003e1001440c3d9160401c841940108664001c030300301400d04040c0c1e40700f07080e9500030b00500700f00401e09200440881c032560740d080030105d800b4845410a00f40c040c05030000d074002d0104000340501c0e0b104685200400302d4004002c00b5007845d6403580e46 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 606558570 1250 606557320 606557351
    0x509040302101d0109061d15010b071a010305030a12150302060d020408010e06090f01060b09061305040f020a0201050907050a0605030c1614010e0a020a0b0a0c06090303050601020706140f1c 83
    0x515495401d841c2c01404807d640040005502d0300c0c01c01d98131030b070780d0240c5d081035101d15068125080480d40300102ca2030211102e4081070189000394401d4006503140c1504070310182c400c000611640e003885203801c010085041c5540c040e0f20072690152100c6540d61404040200a48940c0d00109500d40c00c001c0d1211a81200184040c46010388809541c7c030300c5645510b1900366551481000da01c41402c0c0300c2c0c4201c81c903180008064031855010318480040d510340218069a800d000201d80040c0e011448000054080c041e85920902c0040a448058149000a0ba01280d240215130030000080b001511098202c0122044c41d60742d00d5040c00010044d14040c92601c1002c080760000d5400d05d542002c90b0403000921810790340d4000c044006690900450012913080481d10100704580110500c0100c0c0da00c0c81448001c0340655804a01850a0800a481c000d103940c031000412450300303410030000b12003100b41d0706901c5000c50031030360f91380f440b48180016450021000703541074034040202004400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 606559820 1250 606558570 606558581
    0xa1a130b0a0f0f0e0906010501050a0c0c090204170606031005060a0905041203270312060e1009050603030a12020304140d0810061d060c011e020a090509040302101d010906 75
    0xe1041c0e00d400e1903a1a401e040c19241820341781006280c1c4010014003096005070f0192180307038203c1c13820f541001d0041e2211100121141c0c400400180c1c0000c003802080c01d1904030078502c040c4403000b4411130401201280d9100781004030403e02a40e281c010078669905c1904d031100030605401c0071b12850a05041003200112046214800b2928280e0403020344801c1c0030803a40b21001c00030901d030101c416510265100300e000407030100c0060b40d400000c10a91901205603000d8200303081c0044149040501d000101c40000c0d000a203c2d500c1880841240c560080369000786000e0020056220f4441c2d1600748085500a104402640202d51810b00030582c400305040c030510304022402d41103996250140d80460704078030003407080b03091081c01c00c9103800c256004101c44001100006001da03000b008180481010b80140a0b4098001070708040c03184c0d01041c0080541401c460911950400ea0360282d0740340c00c3c9450691031552542182100c4026550a00503281d07580c1e0024000c1d100c2510b8a0b800410 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 606561070 1250 606559820 606559829
    0x4030207140405010e06010c06060b0c01061d01030f03030902030c04020f090a0603112b0612050706090e04150e0d2d021e01090203010603030c0b0a1a130b0a0f 70
    0x1080c424000c011480c05001d1a070407a00200704c02e01c0d058039184011600c8c0491040e0940b81d03d03413a1680007425001c03100c001c108071205d0307000024490341010014170040c80700c2d51207020508100001400850150034407590a00d41c075040c0002c94141e1032002c6400e10103044407541c1d000c2d1001c5100445100c290004007045030b800c4604070b00c015202c0400ba41220141e502e0141c40000074003241000406505502c40d404640d189600014586101004241c4807990400c051aa040c0310000080101c02c0000c0006030816043c41c02071541484c40c450402a0000e0000c0c001a512a04459610341c0c9a030001803201d800c0e1007030320041e80d400c070005030080140c100400c040d5002e04201c42d454813954100744030085400d501501c021220b803000c00200c0b8400d4140e24181303559070020b81c2c00580d824403a0300c00840c07003a198244c4051040c20303c0d24180000400c00c008050030016110750504104c00c059400c40f004841c01ca25144040700f15400405d01c0d015482c0d003124981c07030040b90500041146500702c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 606562320 1250 606561070 606561089
    0x70b0610120903080f0f0907150527030706020c030a02040b06070506010b041a09150306031c03050f06100903030503130606030503040509090d0e0405060f040203040c090e0a02060405040506011704030207 89
    0x40d240d6403c0c18034480e0742151941408d400c08001440344804031a00700400601900d000c44c00c08491442d425940000ca80100304200e1440600304007900702481190000c0c94640040c110802e030380004070343c98038415070000b482103580c0c50602480c0d90300c010a40c0c006e190007108454940d07844041d51449980729024030022165540b5480744080d081600321040c0140180024283d130218103d02500c82d00701030b092541c14000e5060040150942e000900201402903502080900f41003110794010300340544000c3c050b4104100f100520764102180b01e00312a4507190035562035541004540d4845d1032250020022420008001300b4014004080c0041e6442103400a02d00d48400c88606c0d070742e024194584c0e011404d00c20485540f481c042d4485580420082c200d429010078400000c2c040340d01c1100c0850796802c07400020701415400e803048044070070041004168540300ca400068440c0900e00c070b11413050740c5030380014160f0f0f48102000d1520800d4a420f561035400d1514000c0e49400c11030003911003c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 606563570 1250 606562320 606562351
    0xb0f0f0a210c17220b0a0605010f0e010c080d061206050c2a0c060703050a0f1115060607050715030b0402120a0e0a080a020c030606030102070b061012090308 69
    0x120319440c455409140c80070b031a140c8468158099055240c82c00514030403648164003155080d40c044060b039290030074883e45c408030340c07482c022036010200c84da942c00940c100000c5801204030305403c4a25825941c600342024402c03911103190128003480b9410241c04083c1c2006400580d031222003030382c1d120482c460041808103070348035003605645014038020240703586886080342c0c0f600000340208038a090744200603100c03a155103c01140c41d41e44140310480000300c0000707a00130903561005d4800d120142d14a84031741d00000004009984641e82d10f520042c0780d200b200132036041e07501c0b241207860182d8003030190b419441c2d5135006d01c00c10f14404c011b098082400d180340340d04c05250a100300c2c0e405064100c460b42490b241e90900c10300a1000f65030b50719081c131900b0082c0b80803030401c0010b4030820200f580200200c81d06101498140180a0720b02070290707005010313040000b0301201116034458004e54220860005840086464980d070024000b242854641307400c041c1076002c07c0030352088174194140401d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 606564820 1250 606563570 606563627
    0x10020307021e03071502070b0412021903020609010e030703020909032d0403080d090b010306050a180503070b060a0f0801050610110a0605060a09050c04080c060c070b0f0f0a 76
    0x58100c103050b607a503415044140d00703009003100710044e8150078040d031044030441c503200c007002d03030311944650090700741c4814070411301e01146081c81e4141000c80141e00810b500915503404103000303014408205041c01203255000d501d40d241040290001c58008013560f030345007800d421a945903841600c0e81612081103001c980441125180604500d035130300303401c01d032a01d860b544582d43d003a04002c116858403034413100d5100204040c0c204c40f5001e140a054006007504101402c01d04540050b80e00b0101301284125901c04178401205a41070f464024018659a9603404005071900c091a040545031000785040400c07150340550005110b00e80a4501c0c002c11031403500117584885002400d548513500907902c0e60001240c0380c2001d600010050440d80445499489080a0360001c039113552030420041420004400b08001803c881002505d00e240b0305180803044980b621101c1c0204280000c0c0003030b440d81c1d400d085004503000780c2c00d84c2010549904000b44024003445810f02820302c51040084445c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 606566070 1250 606564820 606564859
    0x1c05010602060903040b030a240e091b131803020a02030c1c060e1f0905060a020f0f070f06020408010b011101060807060e0d050715140a0e0910051002030702 69
    0x5000b1481e503c0114103081c54003014000560005204c0301d0907540f034050354140010004240e030102d03c9060782c4c500907a42000908105648001d14410b201d501455002c161000c040100921a2105854100c3c0c24541100780d40c001c1d0840c502406c00001120f0030700710034580e01044c802101e52080342904c24840c000f03010420801e6190605a110a064039000700c001010382d449074819500e80c8007030b69101c0d095100880e803400e0449214502082e1034001392000c01c0801e110107a440f4881600850070106504002d004c1401010050308180e41c0000d40d01c3c09102c0c0074640f0030341940c0d120b0015950340e9103c1000e58013074030b00348440d40d0224500b00c3e6642c0d4401e2040c01104c007621502c0d8014811985403510440e903401f00da2044030780003261002000301050b001e100001c09001440d401282e003080c4440300a01d070007040001544001001d1100700b0300c2c543e00c42d00c501c014100032148445a07807035410450304a140070394065a13100941c2020701801da900400070b89034842c000c03641001595070307400a05 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 606567320 1250 606566070 606566083
    0x18090c0b1219020421030201060b22080106061403070216030c0e090a150b01051207050307080709060c1211012f090901050111070b1804060611151305031c05010602 72
    0x200c107501100502d610107040819005c21144e400b81c030001c560306a40b104811207170307071001402100503500b8051444480003160720740c0c0b004104040c000c010452030450011700015007541c06a401100000219880742d208129200c0e0841f942002e13010115600c0c90512a040014814141306901c242d0028038801000303d000c070815034000100321004d40204000800500d5528805070501c00d0512642284854000348184284c503180c030360075643d081090010380f0038880149100c0411083d000280200c0c0e5101482110195101c3c250280c250340030102594410304405103120300c0c2d80f03080e200c900410001c0901c0c1c003140a560f80d042411010100c00b0041e144100491a43c00240c800010045948070b103511014000200050f626401d403180b030942000d03400b024170507900c445010301121943c90300e0320071000141003d0a081120394030030340401da2150310808000552842100014035003000740c0150b0341000d6405801d403641c690103a0352902c3c100ba0a10400b01640d0f01e06000418800c0c00007512 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 606568570 1250 606567320 606567329
    0xb18030a020117091005090d09080307030f140f070b04150902031b010c0b0403020a02030d0305040506060d02031c0206100b0901021b0f180403030e010618090c0b12190204 75
    0x140c8900403075680021000d03503405400013446200309030a40007920f003d13200d441d0142c0b01c603101410f1041c25102c0000c0407114581c00c003003110f030010086100002d410245249000303003142803a804051480004000d240140155070702d0407040050820300f04070700c0c0305a8520840c401d145141c0d00c12030182513081211120f6100a400d588120b24444424418400c85101c0301c0c1c0c140750092915540e40e40301110b4100a0ba41200541e10a000103030451030705020703809010b501c52504104901c2d1035216166500c001401e464050990700390030005544047c03107a11503928101c2d030481c07401144031100a540e00c200702c2d1070030030540e001030001c286440390004641040341d050f03001f49459031250005200d20404420120340c04486040c040c1c40b186c64810050110120b502c003054118541400c01800340c541002408145900d003120078031002103611019103011074000301c00200d00640b03141210541140d500110804100071480d411202e644600c902c2c40f035070540441d00141c8106a80c0300c07060b40203c1c003c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 606569820 1250 606568570 606568577
    0x121104080a0b160f0507051915140708010e06180c0a0801090606050901081801051006110a031d190902031e04020604052e030f0e070b2a06010b18030a0201 68
    0x5002da00910172800f40116500580c00c0d1840c0c182c26054500c0c049102e500110f8081c0c0000c411101442281e03c260381c4080e080000c61600c0d40782c2183d00800c0018140100481a04d078a004240d068440c11030380300624905560255890500c81c3d140491504400207040000b100c990000c1060032850042108031002d40e200d0b1401d007506d410054802c3c04c00100512188024001c031900b00369800d0241600958241c080321401c40d0400c180180022102a11222144e1010000c0c1000992200f80006c20300104180c66040c400420006035525040314900c1080143c070940c0421408160350041d0302901a50201d0205100e6100c00f4a8001c0390454010354441d8040c4010015414510b114000c48450a540845044150280108028044002e11300065a10040e41c00f150780b4070311807017060842840003003d03203915014030f285591060029507010034801042c48860070005148605010707051340280e809940c1c44251620454011001d20b119101d1030340700c01200303810042103030310a03a60181e4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 606571070 1250 606569820 606569837
    0x71e030206061005280516030305060f0909070b0a05071b050111060c03161202030f0103030905040b0303090d0302240a0501060e090406150b0708031602010b060703121104080a0b16 79
    0x11010b1411789042d0541d0050007000c10100e031280342c800c10036182080c46034800241c2800c1070818400c0c00100210320502422103a0103002c00200c5c001588030490317040b007004030758071891000c04880c40d00640100804080a00c0144410b41d80340c01a46030669a003070741c13400b81c0610101041950b40c1ca05444c40b040090701080802d134018402c0608001c1c04c1801c1c207019084800c03800f03003041268412a02010742c0c40c4400c00501c109079006004000415040300e00340054071940340003a880388503184846120b0482c0c1711030102014024030422000d24041403650102a11428010500302012250707070014074582000031031154094a0b03440000c84000c2c00143c400d548954818004165200c40350319041c40450300011003c0002c8000c024282c8204034a603200c1c02d001542190803515480c00809590610500158940714103007507900c159010301c0e288400364807000381301004102180e400c2100020010300454812400540324003050703c50942480c5070359600081607050f12403880c0400008030701c803 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 606572320 1250 606571070 606571117
    0x50705030408120402010905210c0a140f0a17064317010b040311090708270601060c051c080601051c0219080f01030803010308071e030206061005 64
    0x6403c02540300b031041c1441c04015480e0000200820403044884002c00407103000c08410b9031701030003c0c0ae0389076070984600041508201e508003a45006000050180315686194940c640c0c1c0c140320640105141030303c041e828020304204944564045610910204510f80c83c01c0101c514120443e000c4104611003030004266408041e00141d910b40c8103600704034001e0802804446007007555402018103844d0701d030f900c4d80385240c40024914007040480c4103900303190400c072049801206d2203030b2103001c10340840b070091a160701c807420217004849c540b0701900c2140f0010416a4012030142080e5010307608070ba000c10800c0c180c0c0d038a01190180d40e400041d0b0080040340710303035000390003902c400e585034502c1c0740c0c9a5405203440000c81e000200701d142801d601d844401801504040c503a5000104809040301941c1191144001403206200c01040c0010000e03c12041c4982c10401c0c05002c10302e030003261001d103040c0c10000e50700c0c00107440003840b540000700e404160600520032240d41d04410502a80f0b11540b8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 606573570 1250 606572320 606572347
    0xd05120606160b2701060b0d090c03050709060f23090a0b04090b1f12080703050f0a09080610051f020a080a0c0308010e130b040c1208040504050705030408 68
    0x28991400369408210290000074089407915413180040414804a811440c2840b501d201c40c4074480c680f4507450070310140102c04101d0300b10b074403a44140c0c10101b003031400c0e850203d0300e240e92503001801c140990b00010903500260f82210048540700341c070624002d5242c00800700050058000761456002006907042581803010415038003001c0000c0010314090302201141c00e44420705002c40b50440390804014840211616041c00d12103064a0301e007805003072440032281c91411001c00b03803102002003400400c0604c80c40480d4080021030040c1601c03030b002d11801500f43e580a0151414a000e583c0008104010410789001240c80042240d01443c20840101c0c21045110090200b1401841002c20205900c50700034048a0b045075034585070b42c0322904006001c5281078102240d0411103038140703d03003800450703c4507444a412082ea01701d035448034a41111a01070992002d80350b007080e040300c0000d01a180001c1c00440d4402c0e58113200c2682c2d0004115034520044030000c2c4804d00c240804142c1030341 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 606574820 1250 606573570 606573577
    0x10051c021504031412070215090d080c03071401021c020c10020304080307080106020d0e1e0306010f05040f11030c0c0705040f020a030b0f010207150c060c02010c020d05120606 77
    0x341001e0807019001c01c034800180d1042c2c0064641801c5800d818000c10f000300401c040e84401a80120b0615035940d000030100c280752041c502e00103802159100ba19603034880307484552a40001410755443c0303081a41c5459400100c4181c032070641c1e0102501501c1d106008559443c10111008409101c614602c000290031002e00000300b44691452028401547e02c029070185025104084d12031605520040640e10160403840c1103400001c401e50010350012041250745000b15890b101ca0f201e010310000c1c050100900f801d07452300c200780002a1081c102050681911402d030f034180000c0c01501f0340341c02990242d000c9142c507007000700001102e517600c0d00090080b4076040420340c1d042070381e41c500180988141d07604c084d603260350004084c6401601842072002c1c07100e05444405030031400d900041d40b2003480d84035003094004124450f844040c4104411404658043e800300641c41c43c40b44000d00800e1800725000151048442c406981e50048040e2405806003410035442550b500c0d044c030100c1d40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 606576070 1250 606574820 606574823
    0x1b0f030204050409061e060e0609150907091505120c07020a0906030c050f120c090a0e120c0d0c0807021909090b040203010f0905100c021e03040e10051c 67
    0x1942404040b6a503900c3c0c0c0201c103107543c028580800d2030382c05907542c90000d041b1460700030300c01703071605e03108002c40e40160401d40d0307010104840f48000d6548402055044405501d041030317028003a170080048040c0c00554580940725402008981c43d11030f40c0c81942e2500c01c0b001001c4105040000007444440188000c1c51454030207131524000b655036100d81001d030786054000300d800b090500401c3c0074605013850440001c50003294850b0045002071041600d6a210b14411405080381c4400201e000c80160044003031000d502c0c085810a11320f81c541c9041a4021040c03101260080e03110002d40c40340b15021150317507941c10220240c0b8015242c0d003004080000500d41320241e20007071100080c02001d51062040040c083c6100614038501807040500311540c0d008041030044c80c040e2400081080050145481c0ca000030000600d421080e0701681f501c40505454400e0030406101410070302c0000c00078008491700c00680b0201074035000303c010031900040c05590381010721545c06520201c02c6000c03020559 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 606577320 1250 606576070 606576077
    0x10603030e0316120c0812040801140606120402030c06180f0315010902070302010b0a120c0506031506070f0602130e090601182a0c0b220f0611030117101b0f 69
    0x5c43c1d41e01d84540c1041c0000c000460300100101c2e08100320442805030000180b0307401c0c0700d1903040c41c0a10002c0c28601508410394205002800064110f44080003012030554000348138079141c28072000361100d01400c11120f00e000d0440700c0c00c5c4001504001404654840716011000070507801c02070750900a40021506908641d25080d03071003071a80381c0243d514081c1c69045102e0075401c2c080d0810a50662041d806079001c0c0008001b0040d04500e103000c86a5056022289503a0f1240c9905001d08110311420f030291803144000b076001700c03441c4d00780c0303a68040f100e000320400b0303159943c00203068492009110300c10405101c482ca030b1895490300c0e8800c410042d030382d102817044141400312240104038076010542c040350b0038001060511091403003040d4030070341c1400031094444030212044448000030740002c106080c2d108090041008540110700e40d0041c007150075450790794079220750b0048469840128094080c41c5101c10321440c1038000c05061a6000340c8280141054100032120000c4001404041 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 606578570 1250 606577320 606577343
    0x3020a14041a0102120336061f062613020a06081b0904140108031e030103020612040f210306050102150601080606090901080313050612060f1f02010603030e031612 72
    0x5400071038440030541f04041110380c0c1a107442482c0c640c80d0140241c051822000c0d100340e00180c4204410400091718040c0ca132010703030700303031914130401050507010386075481d0780c10304001c02940c4100d5003018003086000312040080350b80e848800780c4180b0403e0700c07030b100300c00c544c40d0350907641005540080c0f04d80c4401410015151099010001e0380300420f8100d40300e19000018900c03050074985501203419002d02a403546503524560000c2d070b131440303054503000c40151003600003000d01c44084000c110f1240c01c401c113441101c90001e02084a00003010241e004130703181c4100895194400100b005a00c1c61401c00b4100070344400c801550042030050040d5440b90041111842a480300c0d003032140284240d000035512014581c0c82410044140d800c041d01400c81405036007080c0d003021900d940c104100707940581180c141d100c08a07884000d1504400c2e40c0001c000005c02400d0f5056200004903070007603a410008050200070103454446008905186071000c91051102c0e10900681241c0300340b02d4003800d02c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 606579820 1250 606578570 606578611
    0x102102030607020a0b360c120304030c1508040b06120a03020604050c0d0305030a0506060d02040b031f1202060903030c0a21080106090e0402030703020a14041a01021203 74
    0x3610004503030b0a401600304114107002c2000910b83c4d0358006842c1441c2c40d5a20031044044083d00c40d9103a0020001e60248010380f100300c1051007402c1d840580900111400c180d88144640d4a0b8050321040318086070009000600c014052010614240d0b0342d0345a694a031261b0b1203240d110500540980d5014011080c40ca07400c850030040c2a49641c82500a0401481c1a04065090050401032140110401d8007484000b80d80281241c2d4000c2140c0320000344c54a0310b09c04504103000c0c4e480707d0045c40f8400240402d48108410141d8480d81c20b4034111400d2680004403882c02030108d100d050314880700f0281040051510102038012000051b04403810421008001c1e45061100d6406032401040c0d10707481801d0100d0403030030802101d0207040c0800c03203502d02000100708081d103105a001004941010400710b660902200c4010760700102522040e50702d80c6090214460900c10b140e20452402006030003001200d1046400198160003502c100f0318406d40c00741241c0d04c020042907041d452101c1d40c01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 606581070 1250 606579820 606579823
    0xe0a24060c0c080105060d02091305060c030406050a0603110607081c1b0e4005010504240b030c040803120a050606070f080d0609140403030c050310210203 68
    0x100030810399880900c218418140041d038000070f6000502030364101820031065850700c1d05d61103181541503420b00c00580c0d0711841c0d1080c00900c0c500007402401401c050154040b82403025602890041c00c08001c26102c0b51002d80442d485440300508041f0035030f94052072480c0200c0070300020382c0100aa135150807410020b180720b0b804041001072480781d507031155403030b0030592a0943c9405c9680341050034001a070b0100040364420003070110008592203c4464403440c0b0b43d01d40c0346480c010304044800305c01902191b01d02c00b07014240501401030b86400c90345060314580ca83c3c0c62f190100890402d90400b0b08040030305400ba8001405000900d400700000a0034810400060106150140c80d41e442420281102d4081e60406081a44a00d400703100e14404078410900c084c1440394003058003603403854802042c030040d152135031092030f61500e41458008882d03c240c0347e6130b1103240319a50803c40401d0160301030742c0a00041c2c1d00b481001507014010b1010205030f8502806e95011488404a500544c0d400039 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 606582320 1250 606581070 606581141
    0x110409020c01020705120703080c0708040e040501050109051302010801030803070c200306011202030303190e0106061805030d0f080c0405090705070312020a0c0b1504060308071202070e0a 82
    0x107076a5000408600f800024401c950203000c501e40360074645001c54170000c04a0002419004040200041403010800320b03d04507001400b160242440614203400d005009280034410038019a092100258444001d0032035802160303416114588541d00b1a1900701050708001c1c110410300c443e048510000ca281230131800c5d4022500711889207590307840b1040c1410300078103034403540303480d25101d0100c40160f4020042e243c1c040350125001c00010381100d4940050042d88090365141d500e811703c0420040e6000c0305010403445009442e07840b0a07a0749080c035940c0c44900c40d503800040e901900205002d4461a521504140900799070380c10191210006411041c4c29039000010400c0009d000c02050307001103014880b00590801103050904801c0090168142d900d002014400c00e88005040c0941e401d03070700e40101c3c1d409030042001d162030b490020174903803041900396102d04510b0007000010344000342083c256220818008a05d858400b594001382010b4040405003a1040e00811281954040c01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 606583570 1250 606582320 606582337
    0x290903181503010f1a1e090d02091f12020901030f14011a0301150e1302060417010b010206090106030c03020d06140c19050705070e100b040303030b0a240311040902 72
    0x10f40c84154907000141703820b040e11024000e582c40b801c0c00740310f00c0d0000141e03291181e03135071000f001e070384e64041100050441240d283d4000e51284045c0c00380882c0c1c0c010714041120030b01411001c520590b480d08071000b0581c070389000c000d60102c003440051001899001d0b10400b80380c8510651100007460094203030035152080d01004951a16642040d658a07007409602c00c1411201107180840307003080384d22110141d00516407440f40d000803540c0030440d218101294010032002d0082c882962400a215001c1e041b82c100660052017030f580860110901841101d045030760007509040031614543c2070249800e0006000d9840b03ea40d40c420314010342e0381000e410320400c54051110340e00c50010010195000d45070340c40108000041c0007000c00510000f4900741510707003907180301c0480d5840150680744000940c0244196180100c2c0020800d034154005a400a6045400c5c07001240c40d081c032284841e603400e044100c0088800325003107185010fa0300c40308480280903030161900740c480c600d603801d83e03000404 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 606584820 1250 606583570 606583589
    0x19060207080c120315060306090a0c0909021204050705090c160201050d050a06050918030414120d0203130b09010c030f030b030d0e040509010506131505040929090318150301 76
    0x400150304e80041d0a00b08400045406c00d045003400b4010810680d001811020240e40e18881921100c2c0201c01650042154034019076880b1000c10541d27421030802c1c1c50450f058802d08001107850300d0400d40280c8038602d011161802d2008081c6000f090805801c010b0741031042c00c01c10000361080c036016441c4110010140400d0307a9142405203d890040100f624009107a00809500c2a010100407202107403914641c103d101104a40001d40c00c61803000c0140c0306102d41c41b1155140c7c2d070040003801c00d0440581040781202da82d003e12070924401e10507d14001501e6062000004e4000e00711070510b00d00b03038a8001403820a500100303180c94a000c03607032404181c000f90000010300c0d00d0b0040b6680854010b0090250b400e010001c01c01041c090230981c04100d4403956000600700482c00158020070001740b0601103000c0c1410043d0024280c0b03581800e140413440140080c00e0401d040b103a0003013501a00462a2400c3c0051310700d052115114a60b40c04240d620300540800c10f10006140078196440 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 606586070 1250 606584820 606584827
    0x40f020415080a0b1e0a050a0f090501060504050105030a05041109270714010f0c0501021b0c0a050a05040b04090f050d09060206011404091104052719060207080c12 72
    0x41c0c05445000b0041500d403103103040101007501600c5204040588900300030b2511506007561000842c44e50080c1c00154101020a000041207640d407400d10701140c180390000c014990702e502c1304942d1032042e030250902080d01000400d40c41d000326400f0a61140c02110444007410124001510185040d00d6000369244800040082c003100d4581141500d0036003002448101c0c94824620140010180480d0500150701081c45200380100d10801440c1c0d845402155680c4210050041c0000110700c0c0c140c843c410305220141c03608040c4d0070f1109581008004d0030803545003100300310240400030300058000f40c451203128002840c41001e4541c4c180b0900c044c0c82d15800c015401010750010b0741c8404115030140004115003402412421030b043c406403004182c03c0032905044000081c12180e85801a10700010000b8100c08011b421819800d03040c0c20a2901800c0c4041a50340c07868500e1100c0d0002c2e140801000082c03296004007032030761041d4142410980d40d501341ba030800d020195414441c11000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 606587320 1250 606586070 606586109
    0xa0b0114010c120807140304050d09050d0312020c0307020303120601030e06010e0a02092d10051c020c0a021e0f062a011503030903060c052106040f0204 67
    0x440c51409050000e00c0d103440501c0c942d441d0040ca255842c0d5020b81446121004140f200380b00d81e404008040e8542c0600d962401c0620700175946800e0320a0303000000340404004101e03132810350004d84989405581c0ca11800100d410020002c0d88852080a0b2a20007080f8110060f101030000d0407440000f03299012003403030642c00140c10303101000c49600b01c5401050061001900d58401140c000c00c0b003410068030b501e40d134004150030080440526079592203c907400c402c0030300000d00341702e40b0180507116800103545210303041d602c0d40184403d02214039812025a10241110f03400717004030320303001e00481e0303992400380d004a12004034050f030540918078144070084050030034101d150b101080907a1081e140001c210b0042d602d075500d4581030f40020080020a40e9260401d400c520354ad281107003000d409960352484c0140840105200c201ca02a081c0420f201c103003401601960420010107070b070072003075071490a010303025036000034003070b591059480780301010b81d04d51480684050f0505d07606650108510303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 606588570 1250 606587320 606587339
    0x80106050f0303030a0b0d0b09060a0b04020c1b060f13080d09051e12030d0902040b0d020607080a03020d060b0406031a060414031f050420030a1101020109050a0b01 72
    0x5981100740900311001d100c14203910004100c1e07a00030a640ca000403505446d10000352000d020140c01781c4500320ba8410302610050108215002c3c08010a0410550f002c00050000b640181181800d44d41c00c085240b90107042c1c440c5043c0f080d100014140391603c500b016003d00c944d00324450428030407440b94414061284c2c10007852820395040d04100202c5ea140a0008251a903117017040102005080c0c030b030544c5501d42e20b1460404070149001c4c0d80c1c980f4508030040005003105c0a060b84102d0419444000c0d5040140310304400702c1c0c001d003242e440c28885403904644c55011400c07010402d82d08004d070031608a0f02d8821180030b020488891035a40d460300a0050035074624410000001d80c20104544441c4d031103a04441c1290303056140b80928040500c0068140091500086c0d40409031030b501c0c0315100b03002c0d40070510442c0b01d80c2c03002c401202400705900500303c0404c140c2ea015840300e406000420040c0c80300c0a407120b8140300105a8489540d02c082c02c00901800c1254036044c0b000050110320710 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 606589820 1250 606588570 606588581
    0x7111f0905070609080d1209141b0d1505041406090312070f021b03030d0f021e071e2103050f060d021f1b0f0302070504020304151a040608070801 64
    0xc1920300082d1035410420055290076280c214481400b86140d007890010050788c12450990340c1001200b00380300301070369090340c5914030301100080c0610490b10f03d000380e1500b4810400d00c5908941312408a0a11664910003008050029600350500743d25100c103070f100c108005480b030003c14002c0c43c1c54480c0c5840c590710701c10014080200340a0200b514a1400380e000407200450041c26641c825500d8501c03000c2401c610a9040b000e01443c28032200c8003201c000c6800801c11041c83d402a1541e00e002101000110301981100500401003008146030700c91034081c5040c9418020312402d1b000085203400d0003020001701242c0008240c850040000c018102c05980b07a20200544054543d5100c69000621072010030210a020804060b15801401d1040c14044545001003a803640f030081d403801c00041d92145a10300302c0040c40340c807002280e14180b40c02a00d008542c002419140403510081410280c440f4883e1094526900d80c034014081c0e8a50107a00001c20400b006054110b05001640707003501c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 606591070 1250 606589820 606589829
    0x307030e030711100c02370b09100906020703080705070b0a0e0102010b010801180914061306050c1303080a030e030f07140a080a0f0509040c0e012607111f090507 71
    0x5c504c100c01c101507110032020000314001d8080c2c0d4010351481d4081c00c10310a1021350845440c613000c0401080b000090350082a80080440307001c00c40210304241220011514085e50b401600844010170010302c500c80a407030600d125509543c0041d440c0c0304c1072010b54101c00103900c00500821040d420a580a00c03c451b11400c082c03800344459030500d00c00c1310801030117040d601d21103036403580350105111103104036009a0352030005503845401c00400103001c1004000c000d403541d500d07102c003040040c0c9680c01241c50f4568140c4080c0310310f6180d51070700c0145412003150390051548072024990503401c01e00042c88040d0510000035107921850600380e038404e2070b10452140369444032a02c81d000c10344034420394601c48694500348220081d02c420407034660090580d2150407504024980d081103402460644d180362007a6039800c691314165440c07004081c810a41c03a541d0800b40004118441d100792000400c1c500361004640000c4084180305c411103240000c81401503640f840108108882400f5007030082 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 606592320 1250 606591070 606591077
    0x161707031404291b0d02040302030109050312010e090d03020c030c0703290c0d02070212060702031e0a0f030b04020405060f1305030327010e031b090c0f030a020307030e03071110 78
    0xa150908180307000ca03000c2200300c04450408901d2141605c4950111000b4641c00fa00920a1283c2071422aa50b034018652a00190016900110741c42601080c10740c883c05c40d1a0041c011844e56900580086d4007208171143c0701c0c04100464520000304002e0b01c4011846100004a100d8804100d070402201008604203640c055200344070b03c1c1081030040c0e424120300420700598603405880040c001f4883e0b890501e4240c01194104210030303802001403c2012030100320668208056405159244035a40c0c1510209404000e09151070f403280e4010166204050b000610702501c56001034400d0300150524680607500140c0d650400404000344c50041400340c00460904211400f0004004c44803814101035020385004c3c0d0040743e01c0f4a9540740e002070041c090740e440f0541403d1207180000754903e228000e01c0544089100c4104c810304564603104036040c003070704585071211b8003006984041c0050007055103c001150f1b01000c1030004000e81d0b4400d4210726030314185002440581e106006003803003030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 606593570 1250 606592320 606592403
    0xc06140405011a01050702040f1b2706080f181b0a050405070525060e0c090105120d030510050a0b04181505130908030915161707031404 60
    0x3c0340d0f004803c0d03505c07417a4111804984035207038070303030031001028041041e80803809104610803006c4d030000b12004403542d22049070381e4031a1111055250281c0c8512070000014a030000103108030f55000091600003403181d5222400e4035072184141e2070550203917901e9103d01c00c1c0103413024452815004141c024001943c0521081c94900390191182c040d01850040740501020b41c80c0743c0302c031102c04007070b140d070741c05941003001c01d031b82102441d5584843d040300c07070092508000205091801c5074408040030300c018014078103540c004800318003a046c007a12003484c500c501000400c0a6941000001c090a42c0603180e5440d0345c40c01034440c1e21580b860400ca00301502d4104000b50207036050780c81d942580c40a550342465580c03d9072240000302141074025050603800300500c03030080c1020442e0085240c4041e0f02ea908c1d5180c4000303480442070245400000701d01200c00101c020700d565076105502c40c2ca01e09000401202e6051841420070341140e045500820049502000154100c5803020706401c95009064 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 606594820 1250 606593570 606593621
    0x60f0504060e0907030f0305090303120103050105062b020d05060406050f13080d0221010b3f1305030706020d0e0d0909150b1305211504030c0614040501 67
    0x11144e0303460001810b00c00d41c141e0044289405141242c840070741c003408480d6a100f031041010b81c40030b4203010444265090001260030781c034000b070798803103451100c030b032107009401400c3c010f0312440900b031a04070b0704180c80b800000d01041c07061007401d1241d4090302020030b9a103800b40c00008080d40041022401c0c11095074024045101001074502d0f1146002d00180d4500904d600c5205507001b49001c2e545182101d400271410131030780d1000c2c101d140c40380da08108000d011590700c0300d03102483c030f284e50304650346a1108158140c14400d516401410b2902905500c44051f11800d0940e07000030b40036120306030006a408104089441408441c001d440d01074201c2010303045005101c0c0e042407080c4e150982c2c0b9071281511044004038020f0040400300c910b42d50310840815032166001c810310500e80320704464400c1ca420035002020b0802204007040c0941051041c2180c01410490040c5c01541000340741c1010500140c2240300360b141c194000c0c11a40f00030b14180c946a03095800610284400250341d001d41c0c039 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 606596070 1250 606594820 606594823
    0x1050c1e0a0c050111150a0e01090606090c03113c180604030503070b0a060906180c05040b04180906020a030e1c021506150304121803200102010906060f0504060e09 72
    0x19241c6c00d0703962400c800c0d0385407440c0b008003501079104a2100d5500e00450b44041140d01e61003c01229002c68061019a1181e18144c08882190890041039078041004440441a010b0f08540100403207000240744403194030b60032510814030101001f008c00c00182045920744150b40008482c03811542d0502d0a41941d0f42c01c0d8890003180401041e852408012519002141c1c02480161001c0b2008100081e5500e414900070079540000e852094582500c884040344200c04a609551029640305c1c50305151000c540c0800d103103822400c5105039204014800600c00c1d0004101c1074034203590109220072003409036414009031450100480407461050009250003140384248c3c1c10036544901e00c1c40c0d481c900441c00301c14502000d10b0003030b1800410401040080ba8809440c14110390f11a40c55104425801d44400c0d402d001c064040046102202d62601c450314111540d014188000700303040119640d40d030160b90b05a00010410f680b00d04042c4081c0c10300303100d04401480700560559480c00c0000d8102e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 606597320 1250 606596070 606596083
    0x100504030c02040518120d0f02030c0a0c060222050f030f0601150207120602040819020607021e0a2d140105030702250918030e01050c1e0a0c050111 65
    0x70f0040741c80ea00050040c00c1e240b0404186100c2d5201139850303400c440100704100c0e40c401e0050040075480c000007485109528801d5038400c0300c1442115291044010741071f210000d102c2d00444085800f008411a541172031181c0701016540345040c4100355040c1801c1000030341d10403480c0b501230303446903403400340d50180003a80301d0464074650881c1c088164910000ca0500006401084020640c140b081d010094154000c00490310038800b520107c800b00700c10f6012a10f07904401030f620500a0000c071000d454001003109038a080702c0a03104454450b4408503280004980c80040d5108495010a81280c0c55211000c14882011860201c072828820700d241d50a40c82035244e4108400440000c0459000700144c5050550a031005401c0c0d000c480c0400000800c207003c1e8080710b5043c0280c020326102000e02094620b5410784810503031907403c40c01140c594000c0700302a402c610034454941d40d20900c034688a64590f00b03010160404a51b60b05004488840310f60105040215409403030441d0500030520 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 606598570 1250 606597320 606597323
    0x3030e16210803151f020601030602090a1707090605060f0708030705130321030507020c0906132301080f060112020103021e03040c09021309110d1d100504030c 70
    0x4800c0300c00e01918161180300c104400040c0080c00000c10700c03164041207a00e130008150211180059100350524941140031103d0558016038006c10062000030320907009800c40308000f03401d41c005950b50f80c81e1104070f10003540c41c42540780c11406042c01210401e009044c0034145c1174450758507000c41c41e200b003100740c42000e030042c003440c1003c0003150619214804076401d6081500001c201c480d140d0801c008003c249030f40c40c4161000750b40f040c0d44030078020700030288a405160040c101d00000d00c0300307002ca0400d0061071643e0120340d030403108002c2e03022407059140001c800d980d290703007070317901e000903a14601c006801c4029954000420001c01d4200010395038190b4178640f845c5da0040f03070b080c80168064014410b041e030040b003146001c1c4500398185000340d40700b00d010395060021075503a494604120b110f441425800c5841d5401c00b4881a8010380000175921101501540f80c45185a1103e08991180c00040e054140307501c000d06240000300701881604000710000c20150400b590060640c4584540 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 606599820 1250 606598570 606598589
    0x2d03171807140d0c080303070f08071b11031b010201060f080c011214040f15052a070512040302210304050d05010e0f06071d0901050d050319090303030e16 68
    0x810481d01e07a0706140300410b501c04482d450709034172000d0f10303516600226500740014072030010b0105858800e01e82c0340d00804154031028041404001800c00c0f07038075006070548000790204610200d03610b04002d902942c4400c980c070b840f060040b09000a003991250747c400d4020711272484003800314a40108500301d0020b000d0a1241b06d84411582d0130025010650607400d000d0080e1040005102c41c0311005001d4034840c401e47d9030b2200d42401c400c01182d00a80780403a450185480203c2070006000c4215100200901d4072030a00380c0541d901c034a4400e44903034140d010340d00841d04208504011a41c01003440000c1090302c00302000e444010f40d40d000d107110711449540c40c8488001804801c0d4002420118000162696440e4000c680340c5e403410140e4a0800040d010020700000b0500a020a110300724002e100302000e07464035081019490420708151200d010400480b050429031480c02401210a070b111406e19610314100a001c0350001d0f042203880ba0040d440ba00e0180d0b22180c1d410703040c1e9001c40d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 606601070 1250 606599820 606599849
    0x30f2909160f0e0f06220504061113171e0721080d050c04170a0201080109060308030606030604021308070302180c091203040803040311041802010c2d03171807 70
    0x540a045181c0d1a1b99070301d40d104009031041000d9800903031044c2e01a0805002410090b9003424003031003581000c1c0704070315900360140200400f120142c0c00e103da0f590222801c58644400050b601010342d00c100300998011442040481840e124200c009440d51107100102e804680741d5410603c180c0e800403448641d9100001c030034a482006503000390140700158050b00c60001840342c0d692400b0502a404110000000940342805006502c01d89034007898203811a110002070010540020f0485688190203100141030482c002c21048020184800103081c0c0500d1801480704084074440c40c2d200d011500d0040000104142e011528503020a440c1030703d461034408565411401140c01541e130b1030000080001c103009403036039002070390102164104000114840c110b0068001920000e0100d007210340010f0205820310280110959000d8040b4441015010b0710154012442822030218107422000d00134000c1c2028120f074804c080440701e401c0d1102c44400c40d5130310740182c440c0c82811107454 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 606602320 1250 606601070 606601081
    0x901110703140d09031d060906040b03100504051003030f0e1507060908030a0e07050409020109120804030b010902190305070519050c0303090309031204030f2909160f0e0f 75
    0x10b012070310040810307031040007001043e20f4001c110122490b045030803218040001c0401c2d2411008a810355030004200c1840c3c00d2900c094000310360002080a95a4041d0110000d407584850054502c2100741c1041d07905998118074014220400706441d072010010f2995020019481e03299105240c9080f2054481e103a48072494290041c0c00001d20040c190708d40841405044410707030700441824580002130391040350700c1e9014442141c0328294040d000821030103082124100b0b01c440400c03468002c007030052901c1c4c3c0344c0d240c0d200400000e03404040903a600240d000219018001103080c0150640703410710260402450081190069803d0080780c00700c19104640001c1c05502101c0106103d1000d8a480c0d240c4200056220b030031140105000b4000d00d00300071800710a041c2180c007a00e0340401c100d54000007586404403000c502075440c085142e46070004165099800c48218440c00d0030a008150010281c1d440b11200806540032145155406205000e01141c002c01a9030121109228000700c1d502d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 606603570 1250 606602320 606602357
    0xb0c09060c01141b0f09010c021206090606040f09030806060a030204120f12090b041509092a090501020a0210020a020d0f0615030f060c09050406090203010e0901110703 74
    0x601920040940c80c0103011200286140740c030500c960012180c14013200100c0c00150300902c180c041c00c4160403030030003102e00d55601070000040c165001501e9450f01c0e180124415240031070590352101a80d01c4401042604c4c6030500505403200d482440a200515007540c01038150b10014000741e104980109040c1d218900c02c0d4103880040c100200c3c0c0304406025070600d1080380c00c544006548081070038601a40b59070103500709a08441040d895246003501d407040c05401501003207014030400c00034003c00652100e00c0d024013030808143e8031301018030284480c548039512540c606135500f40a4042001c2040d40e030003085403503405405884040d15000c003400d00701e01386100020001d503c911000440320078800c0c0038140070841c1c1d100ea07604010405d106468110040e03243d1000804034035205a0034400141903420a8000304c0181c10f0100e4045d89480008040e1a031680281600303e0b4003000400c00d0036000c080243d040030f1403600070884c003000103070717603244620074208050140007071100c4200c1c84006 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 606604820 1250 606603570 606603577
    0x18010f0e0409030e100804140c09041203090c06020615010912030c08040f0602030304140105010b0307110705060406030b03010b151207021f0605090f010506030a0b0d020d06022101030b0c0906 84
    0x4024508440c3c49502a4058120401618203030740c076405420523290f0320040058500110340004120400c036540f240c0d15003c66110940083c0201130301c443c2c0742c1e0006030120007040090711203600500041c0c0340640303600b2400d200301004141000324120f01040341c6000d507681001c00b0b41d09444e01103440016800c2c80300086c2720300c0c0d1000740c030443c40c0c140c001341c1d8960210240d40114460102c03a4034010710482194203803a000e01411103a12020400318415038055403001741000b28002c00d0314001c0c1da54000040701508190300c41340101c0d45130525149075260a20401e8580c007400c440f1011802905801e0a40c680218441034880e50380d28408124118001c05c80c000240d4281400c0b854800310030311020018000500c1713842d00600324200424100124910361a050700e601402e1a81569a000ca4141c003600076481c600c2e0b00003154a003200e0150700d40d4407142c0204d5000b10300c0036035291042794400040041840204081803181e40042c4001859894445d400091070700d108c6440341c0c0c0c2d5000080140c807 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 606606070 1250 606604820 606604847
    0xb0109090c0806011e170709050a140408030a15080c01030905030c0109030e0a060219110117040f03110f030423042a0216050405071404090218010f0e040903 69
    0xf01d0301d00000380c248004103902d40d0140d20380c68404541d6998404015042030030204101072a007001d1420b00c04c04001e07038411a444110f4400202d01d8403050303044071628801c10745083d0f40b02c0c1340000401ca4016154080c24008000360842051250b20300841561111114612581050380340c406010a104003007040e640907120302002000300e0300c050718014001520101d050b9000c0d880404000542600125007010303034010101e10801c00c40290360306c1c14003903841c244040d4103110b803220501100329014198244136604c45c1014004041d043d04004c0d22042d03175807609031141d07407000300c0d542c2c409032000c42a1000c80e0751045800c018007080c00d88000103c0310303d824050704180b4004445450782924482c688402301c640c034690740c100302c00c4e220072601c550343d40740403946412000504000c85e08169019961216440c54903002000041811040d01e600581c080c4483c9074000c02c0062104080c110400e9000e50f0900302450b42007184400604007170310035100c0c1c0b0700c10f5585000c28000e142c02552044401e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 606607320 1250 606606070 606606073
    0x906041b08061503011511030d02121807081504060b0d030f030b0a05010903080304022b0c1e09051503011803170f04080c030c030403060501150c0b0109090c08 70
    0x1031488060041c0081422214980700325000692490070240070000c0b0380c160307044840700c0540c2502992042d50090f180d018201050710080040d0044a0404d102a00c00391000d903c0c01036060400031050450100c4101842e103103030304042030400c1480300000c3e400b22200c01103807218800e5a1175040c58002885d0442c01540c021140000304030403d0307841000340400c2039494500f00319482c207441c18087d03e100d0500030540450043c50080c001f20380404051580580f0082291482502c290a400880880020000308554601507400c0c00c020348440b264018004035201031181200c4040200d12090440c42066100b550301c1000c00e002c0400061020100d00000d40248401c1c481d40d129140208000d20090f000150100b004007200301000c0030050164448100c031600c070b91030b1034480800d190300c03407101441a4842000b019220100a20140c8000c5016060000f15580360001380702505a02c1400c500801030a404c1c1300f40010860306140317040d100700200009108a1501c1e060b20b1220158211010a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 606608570 1250 606607320 606607361
    0x3021606050403050f1b01110c040609091a0c0a0e030a0c031506050d0f0204050c04120f060b06030708070e06071410060b040e0609071e27050d02090604 67
    0x40300d8100d802001141d1081d001c9400400506241c1600c40118210311103d6010680f040300c5550302c80c2c3c003ca88081500020707201c0301c0e03401c140054111500d0380d002c0318003c0d44030f00c0c10f00709006d00103104c43e01d085c1c000ca05a001c50300d015446e0b0313210351017405d1a070030900210f21005025920208100070f1050740c0a142400380e103442e0b0604840a0305001c4a8244035814500003240f142400c0790342881191f8019003004a1155550801014210040007821110018000051016010004581214054000246034030301c1d0b410030105030744040c030080b40105c804006000800354030207042c1da805a8039143c170302403007085000000d05602c07480310050300c0580600000403c0c1c41d4082650604000e001008009007583c50003c0825809144280c441d000a40000901541006000700d60321035414135020041c0188944d4005500c1200d12603400051070600a07100e5107155810070fa521800c1002054400c00c1c60a00025a1001c4803200213000d068210b01042c0140c4039a007184d40c9502405070314120 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 606609820 1250 606608570 606608579
    0x901050609100e0a0c2102130902071a060f060a050909010503070503060403030e07031217252d0f08010b030c03010b13030c0603150b03010807030b04030216 69
    0x60001618103a1299408002003150090388007468021610380050240300e9507136008542d030052000d000107006004c0808400413584003050420100c0c1c5400c06030050312000903030b40c40c5080c0201c0d60800303420f00d03104110140100381c036854504004444010100c9080c0c0e030307003001310380c15a407105007990300160045801d040581c2c0050151a4032481501c2c5950260f0380c0d03078201503030360b156031042039055009400820040780c840d4000c0a200000001202c044036502c0e86c0f8841000d1a035400311000036982c0306140c10207041450f015410481c5000300318181282d910945c800d00425408a6050108100102d140505100c1c1c4640070b40800c04070340c41e0a85076085002d8104880c003124403001851010001c99004d0f00d0314280c0303026028094905055a0030040010140d030f000c010301c0107165038200d10000c00a1807400441001c0c041603034011540c180c1440310204000580d41205881d0f500c18030060043e020001035000c22070381c10120700c41d900e80b141d090503402d08615072a170300c9103001c003c0004603 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 606611070 1250 606609820 606609823
    0xc0210020a050c15040807150b03162102100f120501031209090c0504170c040509010e07050d0809240301091a01030516120e011a030d1d13090203010509 67
    0xf04260101500d00c0420b0440101c4031404044400a28003a0203000c2c00010440d007a181515621100c40700040300d11000380040d180051741507248008025107501070099400c002d54410000340070120b07810204489034000703555080081907840c1044a40f40b0500d000c544201c040300c45039a8008020006542c41c0d0505240100c02c0410002c0030460b108800600700a0501c83c21031031415564401c3c0c10b25003000c841c0c41d50100e1280d44e0305014820481205140e40d11072007280d0140d003001000003004200070341d540e414003140352b10580c803640350008a500403501c0700e02250a54401120101d983c04101c45801c00301950242c0c0d0391026100200000c00c0d01201648100894103560071040c100f40554001141664400c070307400341500a03008810340b0a070b402035160400d0b54507070900c04182a007241d840c0d6070031692800c94050000710542144041401c092202c8501210306150511b100c030000c0602c40582d0704030b8400e0342e02401c0a01102d00c01c101c200e511441c0d8840c0c1c01402400507091600449 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 606612320 1250 606611070 606611077
    0xc0915040801050606031003021003020f0c071a040f03140a29151e04020f0706091406010803040b03040f12050306150a020706051309090302100606210c0210020a05 72
    0x920320343c079180c042600d600c0e20030700742c82c441c000c10400d1850700d904503402d0108503000f034111784060580902c44e00462222100c0544411900c05000700342640c900280c25004601c0c0000341c0c0003a0230100014072240d1b001205290a032500301103041d0188041011003860305054047c00f4181805001d4801082c12414003414003501c0d8038015404c207070b00d075404042403000010382055408901d804d442907540e00c0345100986c9100000b00010704007144144074880700e6011400c1120b50035920102c5d0b41c10052544071a1082d007116400401e580e40c102070103aa1b49205500622481c2c28001c80001c0c1000140310220620551004144002581c0d08070091b01d0b13a0030907035401d40704814200c4001505c00b24442901c1000382d040d401482144d1910205942c01d610444225041c2c0c50400303008a0200c1e014012810701d54441e80c01411003400c0f00603404111141504078200300307c60100e600290f401f811001180900c0c0302d02c1c00140d10f10350950103914100c0600340036404203001080354281c032038020014 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 606613570 1250 606612320 606612329
    0x30b07020d090602071409070c140c120109030f0c0c0306020d14060316051e0301090309050111030702030606130905070801020a0e0f03030a0c2f120a12080c091504 72
    0x5040c541c0f52540000c4e07850303070868000e11820100e4480000004d161030200140c02042da418500d07044259511a41c0c0783c6803009689051684c0170102c03007205400d01100b00d084080e00354000308880400c03690010400746041d441d40040003001c00300386062011620001004580c403042c1113540790f02c2c0d60440005042007240ba400c580b02030310000703606810045000711986000902c0c000317405061004210b80300313a618101d030b000007c20301c001602c40c1d00c1c24458a403050303010b52108201c85150030001040c00c4c0003015082a140c00500030200107072800129550040400c89003e1402c008005600b0300421105074081c3c101c0c032800d00c2c00502c5072419801000c0e500750607540c007000c01ca803410900583c1b20b0813649444d010313403040207102443c600c907215040c09103228080f10240a01e203122052a50001c020001003030303030449960031100f0b2406141d8039455103c05805070505108580f80c4070140d461048014051001a20001e4980d0018000712001c00500514a00100042190304200313a0818002c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 606614820 1250 606613570 606613577
    0x506060d0f2703020a0314130b090f0a030f1212020304030e19030804050d1a010308030f0f040f0f03030b0409030806031b1e041103191a01020d03020c07030b07020d 72
    0x9440300502d4a6058000c0301d2070b01500106041151944e0440301110a4503200e820b500090190110a540e00b10404005003805003550303407103451441c1003103450116200058883d54098070b040000581c8a80c000d00f1041e00200d02c1d000c03d0398041000e9a181203002c111450f12031000080100701500b007403055083d00010b4840c440243c0c103181900300405801e000c003800400e0103110410452a007103484001040c81105c0c3d401780500080c1130f00500340c8080e04111000c5030003000304028203010841c0142e0003551041000748030306007a1100d240c2d40301400300180c0707111081001501454020741100c16640800740c000c0041e04494180100b00311401c0e18050b119001e405207e0120700719800d042260a04000d001d40031403058404103440204210014a4015444610513880407185c034001d1071003507810140020085185421440448401660900f07080816080c1c80c40e041c0d0f40081c0316110074006040050307a0703070f80c1c9400d182e02c1c1070920b80c00104105210b07010081c41c15404140044031561549 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 606616070 1250 606614820 606614861
    0x200c120a111903060519020406110d020a081c1e020721080f042105180307140d210215010609030f0b18061017070b09040506060d0f 58
    0x101007140504000310070b1959005075560501c00304500f54402900050004a103c0c4407006102c0c1c584166003095200c500400c00b0703401811180300d018005400900e13550f00c00b0b05001580346e910b440c0a400b6828800c54203280543d00c0c004090070036400605140a0300000111448400c44c405001c1c0d44201000c61303c450041c580001e00c03000c0d02d04205000c22168494a50b2669030520007095200001c0c0103652000512a9030154001c2804c440755891b519035130358554619900c80d2003001401c441255a019074000b1104104030080c04412510100c0200c80b5602e6100c1e46e0706140c81c40b0600c1c2100010781c1070005105540342c03a0009003413a541c1c0c100394011856070707076995820348038540c140c800500165240310514000030f400240e41c40d44070308103a03484a11102d1551b08541703071007422180505100054041440280749001c4003501c012850002015020b0030010002d44501407050103a0050380c45401092880d078841c4280d43c03400c1c040460030015120010346180240041d40043c038420f10122 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 606617320 1250 606616070 606616103
    0xc090b011407080d110708280c03200f010e0a060b0306160309030306080f0f1e101109060a03021309111210170102040807090606200c120a 61
    0x40142e90075036401084043c104407038002d0880c0500b0b590008012940f100b08181400545420090700c0d500f40f494801e108030087c8415031803c004440c00c0c0d0070040c040c22500c0e100001e40d00c0444800300140c41c0f10000301481c0d20202e0300f45010860110580d1650901c040741800c0c5800040050901c1d008102c2404a111032034181500c0307980940310030090480112101c03080300c1c001d030012544540710b4600007515656802000f030509510255803005a00070a105c00c042000802c055406595a610390703821000122456542d15101c54456425030b98980d0050722581000105a03880c9242c0945010b0b41c2d240c00600c000d00a6100b0078441c150509403620215807000c1c14421150010b130340320b040d5403500c072201c0700d00307000210300078603041a40d0960203000c6000a2010345904030f4036920000980c0711400c0216150900d2900d4001420b0180b9256040004552000700441d203500d1260034403542004482034070f0300308030f403442c455070308005c0700b580310301e42030000240b06550180540042030b441d0103103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 606618570 1250 606617320 606617357
    0x5150904150b0a0509060d05070f1107140f04140c03091014060613080111120f060d0f1a0c0408061003030509060a0309050f060f0f012304090c090b01 66
    0x940c010800ca00300b05001c0c070f0310018003640042510500c010b01c0359082411400194094500440d59040010080c0601c0000b46400199030403003604140c0192646508044070700e01080c01e03110301d1611840461064289a03215580065090001c501c1d1034041854030046800459006076030441d05841800382c80081c42e07645120714884000c0300307103000445481d14001c21816402403010690091011b017400509100c00b44501e500d140c801160300c81c2c82c4d601e0b808145105104c02080c804412441c801085074654030f032501403820310f902150120000702d460920384038524861843d0402c0d211104144a540d07aa00005001103c851008543c1c0c25500c0c1244c64401c0d001c2444001c020510900c4070648500c2c01d030340601a01411864001032101c1035846051401c0142604804c40350000300a0006400c810000c49603c1003284201c0000c55140c00f0120f16440c2c0307180212010041c00c031210309500e40d5580c0282868940000310400d245454448139801488040112400f06500c4c1071101d010000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 606619820 1250 606618570 606618611
    0xd05011d0610090e150f1e0423030d140a0f0209100509042004050406050a030f020409060e0a0b0106030608010b060f0702030a08121b1606090c05150904 67
    0x1141d140e00c2c24440d1a2584040290582d101e81c200d01e80601d40001070701801e05240d0510500c900030009949043c1184158502103840e500081403403017100c00c07c0b01066040190000c0300f40d04000b204400d40d086080c0d24107500076141001481818110110b00304185804140d00a2a012008102030900c800f407410492080c003902582210580d0140008a4000c002070b000c00000030340045114101494407112007141d030001c1517110100454140440c0c102485a000030b408295660314005040d034031403019411480390001d1180d07880b00e030744400708510741d041040c125a2020456140b01030314a00100150024098040000d00e080710000d80d000050040d002e103100301402180c40c2c20f80b4a02158225800040140c0c0c143c86032030001800200f980004107101401c0c0c00c5900c44030308041941c0401032891411035030340c26005020004040d400b264007011203e520200000750303c500d130303d80750403981030030342c80341d9449000b005014100e4502c001c028070400004035070030040851054403c095245 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 606621070 1250 606619820 606619831
    0xb13020103050c2b020c03120103110105130e0411060301120210020c1003050a15080d080a06180209030a0b0903040e01050d08190905041104030b0f250302090d05011d06 74
    0x1600684041001e800008a007407200e040b200380076240003090306c0d1340c501d1588617141c1e0017a03040c402c500400c1402500d1240100c50082481d00600c1d08000350f43e480c6404116018a0080c0c00c080004070341003041000762160310031000f60016840390b0303580310700941e80e03030a0a009074003620000c40074110f840e101040701c01601070024030010303c14848640c120000c0c00000c1a420354507a5954030020390240d1311100d48010312607040203200a81c040100100b03480e001820884940b0f05050052048140c10000780400300b512000c0145c503840b180740006d01e803025421010340b010340d42000340059248007000500a03614914050002c59aa42080c004800c11440700503165440511640103000180240ca130320104843c505a41e026484100007001c0340c0054901c07501d4004006820020021801c00c0c3d11340c0002108504022072030039101045c0000c020459895900781c2000da5030103850b0096041d542107290107410040c5c06807041c07400c42d00902c071889a500c403011035041440d10114000510900c101c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 606622320 1250 606621070 606621097
    0x201120905060a0e0f0f03030403120e0303070c080d090605060a0807030b070516080309030a12090302071502010f060b0c06060d150b0f060d0c0f03090c030213090b13020103050c 78
    0x166034600340400105140300480040d402440c15a5031900300400081c5454506c28001c2c1d0743d00c0c2090314010b0800300c44d000d88807c0032820150420814480401500e0340480b41e03040c2550318414610b803000885c807507002d018501c2c82c504420702003071014036403001d40700300320a03148400c2c1c170740d2612b00c03240d0746107030a00c03000741070b01101d0300051a940d1113940a8890308040000c009d1106103e60703540581034108907120180c0340c0c40032a061042d02d501c40342c600f0000100f158200712500154a000351242c1050084000b0b05406021101074079100350b201d0410010040410002d440c0c85440a4003a40d003c16410380f1548a05004503d00e49040071800290942c8030760350384044681c01d0b0203c409009808540d0740d00980d0601005055290392000706500720001d1400030741c00c008040b002e00000e4914a800d404c05140c11498400144a605403c0969404483c030400c10401c0c0c1c003614000e0048482f004041350703151004e104a800c1c800346241d000c2c901c00d880034021540c483c4000c08550081c44141e0850 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 606623570 1250 606622320 606622333
    0x100609050901140d02060d0e1b010824130e0c040212040f0203150c070308070e03120c010204091401060201060b19051606060f06090b0703141305040603030c0201120905 74
    0x110403118209001034024104800001217500045e5032500845400c080c4940c4490696100000a000084512030012100d10300070308030100090503410004c1600064509402180000440090101e82d5124006080041c200344c55000f00000e04459400324605203da00682c05d02460a0700030744181e01151704400c81c16580329100c40c0140c1502620070ba8040c06083c82c0050f10050618070303039101e208001a242e950b042c140c9001000d00c0401000b080800541d0a00c1000722b99011448085110426881c0c503100d01c9030141081c02031203103030710150001d4503000c1d492201c48030440f841812a1250f030000c0009607980d00b04220079205201004600b23070f401c112604540f40c00741002d000b40441d030380f49a058182d5903980f14800c0320f500307401c51342d08405400410055250302c100e100d0301070031005001c0ca080000c65500540040e204103240d91300c1910110300140c0100c500f0700d2000041c507004009226195903030a014111080c0110300b0390010304510b08604000d0264000e0a04041d0720a009003030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 606624820 1250 606623570 606623579
    0xb0a020616030e0303010e0f060f0609041a03031204050d0905031005040f1403040f052706030a05101b020109050721140105090d0c0c061b05030c0105100609050901 72
    0x1003900c07034912060241a52442034403060b01c420809035010389681d42007140d041c246210194030b8004000d00d040e02c18030b0950400004d80e1512001e942c3d41e40000d44001c9100501902c1d083e00d403442c082161a018071012558990f030386903200300c1d58040c600400655800404601d012243c0301d141f8092545c03d071340314250120403d00d40303510440c1d001340910440300c03c1541d65550800c550500070440301103940049401c0c803030780b03003420b00401c014a011210140a034a0031808002044e2003910100d4012801c2400100251401d0001c080e410b54170070156010101d80740c0b1564001d04052100d403107801031805260ba46540140b0481c0d0390755400c01d00800c540c91808003805501c1424909850f03042000c1a03000c00007036100c004a0180c000c4d14400864645000d00986241505140e800410440d01022187c041401c2c045000150380851900700708489043c06011114000c0907001440d0b4480051850190790041d8041409007010143c00040c250b42d0700c104540c2641240035450b88070303540000401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 606626070 1250 606624820 606624841
    0x270a1b080c0322050706081f090b010e0904050601140609220b0a0305150a0b0a140301020708070f0b0106090819050c030a0f0b0a020f070609020103090507060e0a0b0a0206 75
    0x40e0300c16610380e0b10280c09490f41c00500604144400b08894603448004240500d5421030310706640404a05405c400070710381c800040b03070301c51070314410220515a6000c0e0340e42c569114406281c080c0034060480e03035403400d0901c2d009966000c02d2042c03410400b0b203440444054500300c001c03207540c003400408080c0b49004814282c035030000d050221240d10b564500d000c108a48807031084000039400340e00a06100e104810000d42080c90043c80c6200032031501c1c01c0e10415030f540c00d03003a2013929000c0c004000301134a51408a402482103c40280c80341c000031601c1340070010038504d050143c5228841800990342d81d04030a84103c02980075084594100714900d0800c0d41c400740d141c00d80c0b039010f402144d21a00428002c20300301030031040240c0d450b0780c00782400c1707007844241c440c6640c2080d9000c00840c940318071154060140d0041d010010400f545586001096a100384c000c18401034001013a5001c11351717500405031a0405040303459004600c82300300007901c160504d064400001d110340150490381c0d900480c66 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 606627320 1250 606626070 606626077
    0x121e010509240909070801051f060c0305040320030c010206071209050a1b06110a0f03050928060f020102090a0308070206040f320a05010e270a1b080c 66
    0xb18070449100c07405451660b0741c0241940240303001e5010f01205410450342c02c0c2981c100608084810000852034801c0e029070381c0c17490f0200c1e01d0310304d02004041d085e85030441d880e105607400a803022810300103010350030313030709200f0603001c02400c8080f100e20051900c016130303c9500807180c01c0c0201f0f6008144030b0103409190842464a0b1080040d1100485190784d500d40444070180140d40545940609001881d04503852880040c0c0c1c0500401c0400f0880c2d55010700c00c684070301c0040400c4800700302090384ea1039040c10414254408114000c0c3c2115500741a210359020703205050000d61101c80307014041c0e0061080341c4038000007900d6041d010f810350711601c00a922000b01241c010030108030010703106078294085005440f0348580130144009059401074130102120340b103590200710000441442d95441302d00e8040750002e0802000e01c204500002d40c040e0154000900b84543e00310411003210118400c25103c4c000d407000030418280c2d00e201030350492031000c1c1c104010402c2d120201e0302c0585680044c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 606628570 1250 606627320 606627361
    0x1e070827030919050117131e021806040b0a0819030e10030b0a05040204061e05040b360d0605060f0423011403120c01020708121e010509 60
    0x71245014000700c041074402d60040380c050540f04080350700340241d41e03021100c0340c802c200c08101c0b2045c03401d103011807035014125030f4002001090107090302071040784050b0205d806a50000c01c004049008a111300103c00c500719003161040745012101c501e01c0c6816884901681ca410380200005010039079581303d000c0102c4800e60074801d00402020b03040e03440c3c1606a48144065034003184940304070041c045001e94603000a4030441c0140010301145904c6448034403100c12807840c8030511641c0395401e0f682c0e0b20450f00407910327540000804422045007a002e1500410b16181103d40712245500001c81c11840610140c0d8050510750b200710100310300ea001642c00800c0100f0310b0001e00c030050b000408640c1c98004012007042012018035051031900002d034010031054000d1848041810700003929200011702e220070103040801c481283e1102541500d8160381d20a904036510380100e441c890381158203da13030f66039804101c0308444142c1045183c081c1203810107480c0701041c0e11380c2e401140e0518541c684c0d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 606629820 1250 606628570 606628573
    0xf030809030307080412060b040911010804020d0525080d0e2101051003140a030905060c1606050913060f09050613051f0501030902030705120708061e070827 69
    0x1003d404101110b0040008040b14140f500407031540389880e0303085d12181345805204624040100012406c0c01922100c140802d1030121f68568640c80015180c400d0080c2c040c4c203500c5100c421207059001c441b46280702c0300705400e42c4003001d990364036415518500e0131100c900003460481243c103e03050552076440c01d08901b261542d4502c018444840c2154030446000c000804504404c00a0001c00c95000e4511140c030300150000301d00540f03021f88501c060b80302d558001c0c20001940c403080b00b400c2c06488080901c0c034103032151680ea41d03c2c00802c02d0b006080b00c2442804d51842124540f0130300d20402c011260001218610395181801800041c48002c2580340c211440003a140d07d00310880c0304151141d2001c0c00c2b50361110240e041840da00c54140c0d00aa81814504449007000d1b950024003181141d43c202c80410171100449402800c0a41f00d0344124501c0c8644070502880d1180d028170010700340d00c080c803140001e0ba41d04004031400041a0f40c5082c1d14661440814096041030003942503242e8500b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 606631070 1250 606629820 606629827
    0x1404391406071205070c122303070204240f08060105041d01020304030f030b03070f0905040c0f0602060603150c070f03051606050603011404152c0d08100f0308090303 73
    0x2155400203c40310162103001034030004a880400c9014403030b00001e01840310360080300c9059603840510440d82c008003e0403a44410b0f60301c8400c5d040c2082192101c980c00707441840205070303400301c61650400b0078000603045c1286400c00306501ca642d0248008440580000300b03c141d1034842840000c00e001403144c04001a0b102101e0105d4009000940c0a1032117503546060120640d00010202c078400701c0c00902c03a4009903420448440010b0218003a211b4001000841e40c84501d00702129a440d644030030f0821040c442c0000da80ca40125100b4401c0b00c081c1c054484501c40307500d4241864100710344d500c50398907040c0541ca01044e48480030003486403003820610726082c0c119000c404a603590600413286247c5400030040d46060a001d46000e59059019484035402c00f03030340d00d2040004000001140a070303600f11400ca48442d82d03261265802e0402451a100c1ca00d000d4102c0e1070380c7e4103140e100041070611012034600c10070f00421104403150741241e242030908580d1000036a0b0b0200101550510061 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 606632320 1250 606631070 606631073
    0x10c060212100f0602070e0a0b0d080309010f0c0f1209051c0201140603060609041104090605040501200a0c03091703040609080c060d050a140439140607 67
    0x10300c01803902041034042480d2034604501010320722580350f00001030219806004021641d00010703500c040e02d40c080b8554480b9078456240b48020031040340c165030b0089450502e10240105600118040c0420f1002440f0408440c01034070181d075544c07036035100080d05800090010074840d21031503034003012211740450941840c1c1c5031185008001c54400c5441c4424542448807541c092140c4a4001c2400041022528200000039110540101100d0251030010002400c006245880350180341c002030007080078204c10b0030100014141220115031961804000c01030400001d6014411341502982c800d04c0e010615000f11000040c1e24001c030207004c05810040f503a40307490400c108002c12030000941d00c6e2490400000c00c0300445030320820f03050f08440114000c1f80c48403000c6540d89107040d980840d8645071a100100180132449280c1c1103404030304280020060f080c901021032810440380c01d40390214103114020380e14070000c1840d01c2c80c00600000c000d003c0524109030002c601c020841c60525019 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 606633570 1250 606632320 606632333
    0x15060f0d03080709081b010509120607030b33220305101103010806012105010c080a1a0105030a200406030906060906080a0b0a0f0e0703050607020109050607080402010c 74
    0x2100c8003140810300407001c0007410340d40403094000421181c3e005108628181c01d06809804a041c48107040141c0061400c040344c642901c1450518481c00840d43e0a1400c180018020202010002d11400c00100c08032076404200b101e00e11404d0144202c410020403488815005a204240c0d030802d100219800b0600e41094024580c0114041c0300a080600d140700382c6001150326061091030400e905000500c4119000902107042d950f0800d01d241e0030803140000c400d405406038800818075803c241403c824594060031090240e180f42a0500c81e4441980c042188880e0403641c0c0c50000c0c07010b00020b041c402894000c2d408203098911150492100c1d0200c280c1d0980c0180c2120740840e440e040040e081245a100b104000c2140341d4003005010b0400b050b840c3c0350461000050700c42307020b05000c5070322080950f021030003e401d10031007000508502e0f02655200d00c1c11340310030f41f414068100024100d60060103207039001a0300901800081d40c07401001d81c0d0410002d001a4104454460a05c000806 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 606634820 1250 606633570 606633589
    0xf080c19270638030106020a14070b0406051306050406050d090f02040207080a020f1501290d0903170606040e0a060b07060e1b01050a120f06030c03020306100815060f 73
    0x100780440c619080c61108050000d508000c1803180c80f203008000401009030702040c8250726a81c00908140240c2000358814607003c515005114107800c000380c0007860301c2c2c102d401840891500401e41010555680f01070765240114801c44001ca10300300b1410707088542940c89070145510680005101c5c803116000f1801302d8102c1c110480300c00100007240d084054040100e044881d04000003050510b2901081107010702d01807003900d14045107859014481c286464004009403e08a1910303210000e5102c00700140034035042c00c0e000700340ca42064110202c5450700b002d1080390040d0070b03607203440d00e0580042c51214004040c00411651420b01007416030302c890041407001d004000100300b020418000ca420484050304407180200e609000503143c1c1d80101c2503070502e483c103091207503044520740701343c1000e0038007041c07404001441c03c000032040020b405204d8003503a0080c2d04407540c51ba214502c0ea5011005800792050075031110f08441502c0c2e604031402540508040c1201f0070a00d03400010034801170 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 606636070 1250 606634820 606634859
    0x809010e03190308061806060a030e031210051810050f13050103260a080c030901090203100e0f120f1804090f02100315120c0f080c192706 61
    0x5444d1028410305141c41000700c03030043c0c4801c140b10031508080300051114400d6002000a040d203402c2084001e100600988101510843c0780000d18a840c07032080001c5002c03409a84d03c035252800143e2895040701341000d00c2031081001c5050124100402c106455604411940d4000c49500d40c00c50b511040f8018a8002d502c00c1800b1540741400e09040f10300328800342003020460340140080e5603c103520108142d0826901440b0941c0e0b92074240b81540034001c0c0c0240a9010f1091032075080740c590740d0351f02c803003035448500d010b0b16041000c2d800844d03129409081060080041401000b44801550b801040d91030702042c1032001c0d9aa8100104040c0e441039402610100b044411610a605010001c4003004021307181c10004142b101c041c0c401503a40a0040030840c14010903480c0070003018004541c007500d80400700c0030015594010150b40d400b4801d10307081c050342080c01c0400003007c010000101303407030301c029510007810720740104400040c058840303c1d00c0c21a02c8a500203500c0c01f48420400c1c00300c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 606637320 1250 606636070 606636077
    0x415050702030c060c190501020904060308190207030f060c0e0901060c0b0c030105150c03041d01030314071502220801020405040b12060712090602030a0504020f01020a0809010e031903 81
    0xd2045004140c10021403c9106000e0714080001880605000c0b5002101194200d5007600c010200c0c01e08038024041d10f04981d0304585408804002c0c010302c4006003540e2401c0c120030341011011988200d03203400940c03000074800d0101103401c030000b8002c1d40024128071300c0d624000382900688400520600000c0e8000e0700424049c603143d1040c04818900d0079440810103e00a103903500d0000801c0c450201140c203d050840e01040c0400a010203001315401841920041c00317810148201c40603030032100784000c03408568100c500da00d001c001c1c4010f136500d43e60004074004a42d000b0000d00c1c8041d602c0700b85407503072300c45202c0801c03403c0c00c2c21104090051b0802c28001600c070ba00701000e100071a0506140700b0f00c2035181c0782070b0200e03211000480c40d03800034591410743c0b08074002044542c040c121504008100c0b5001108104800303040d0382c40288a18022541c080107000c4050040e41c6828610788040c00399141000a9452940a24070f0144000400340031102174071744480701c0400e189100720084000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 606638570 1250 606637320 606637327
    0x2f070318180c08060303030c130e010b120a0902130207030e0901090509010e0a0c142b0204110c06010e27070806071404230d0311060c12040f08041505 66
    0x1074003451040c800c5400190a20303203814104040007980c0c0703000041030488014400560b02d0340380e40e039048854000b0070349111501c12a58407211a025240c100d480002c0340c90041500085501225006402e1000d4003e000459400650703800301000e54880309058050002c2900e04132495103810903405d000b8030840f00009400d00740003100c1420341e80c000c011145254400001080890300a40300e0f00c0444543c075075551649034a060200e41c3c0800b244100e41e01000800c0d09920485000c11241c0340024400c55080042c0c0c3d82d04024180f80e4041c080d0f001c58160700980042c0f140700c0340007241a03089415142c100c050343e1030352002c255480b802070402c03051b41d8100090402101e003042001c1d54004000d418802985925480548181e004c1c80c45241c07181d1240201004440c021044000110580945680c00c002c2d03841c140500408109205801c9502c1541e001400345e079000400d88008995140f035605058035542c8501010a0354800c0640d9102003c0100158400500ca60170318150b03400d480386a00e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 606639820 1250 606638570 606638609
    0xc06090f0d080f07090803071a10060503040b0a0605030d02030d150602060406050601090b07050f06011707060509031204061e020d09090519060602010f2f070318 71
    0x200020420201503503406608503140c02500300007031562041898106003041d65603440700311110741a607401003449010014150b001d1080030381c6500307822025031525650039110150795400a010354030030070340092030500128001541030b20144ac3c000d4212600894850f0f29140000c0c2000800c208110150384005200c40d0721980c2401610000c801001a5076501840c2c008065211a4024030040210390b0314400200a40e000d031020074060000f020b00c4075141c95892a00c56512144c50494400b5840780e0383c00021f090010340e50f800e4103121494054248149003c9040d502c1c2d40100035074940c58081c09a00e41e010503640c0c0082d10050200f982c3d2051404046900e10040304150b41d000011900006850400035030490741040484d00310800010306070b80c0b250115030300ca2400006a0764018203022001618581c150031401c03203003c4911f801c01001d8011000e20781b850f415a040c42d0504408a180007a0041442d00031f40f0300340d402820540d0700c030710314224170180001e40c54110310101c0041d68007596 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 606641070 1250 606639820 606639823
    0x30303011205010b150a20030d060314010902060417070506030a020406080c120423010e061f05091f3206070f02210114180601030c051e060c0609 64
    0x4901d02c003071700c2c0182c98004d02003a010310f40c82009001d5050100554280c400780da070003402103040500070000c1d00d44402d0340200480c0500200c3c4820396404036081042c041e007a1041c030503103050650080c145464a8074100b034001203140020b411400d44d0040d40f100141d203845401c0254800c4400b6480160b4490034440003401c0760b038015040c12200d000034403106082031002022141c1050304403032241242c00215182094142d584404040c0700d5003401c4400352200700c0010401d000750340c07207482e40e010a0b98041c1e0100c494451486079a03405401c02022420340100300c40c280c201c100186141d005259241c9681070030000705000903448440411020518440903d03200c8100500e0444015240020b281c482d0781e0410f0303000b44060300c500305a02d410113624400b0700c2580c0418071044e0007030108c0c410b8254001c0403480200c400e800d030100461207040c410200865058181c9038402000702043d81805c051002c007005030f103050b0b64400868a8440e44a94500002d8525494420020529803a1021009 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 606642320 1250 606641070 606641081
    0x9020705010204091529270a1710021605120a180b030411030102090310090b0901090c09050709051309151104090b180403050c122502040b03030301120501 68
    0x250070145000901c0440200c0f006c103c140e0524071030540100c1000c3c92400c20500c694000c0300031001004400800101c00c0413104030900d101190440801a62454402040444071642800b50340148900201d0802d25601820b01240300c20310340300c40c140c000c3c0d5a507441c0c01c0d0002c81300400c1d51008120016002e50150301c054200300c040400c00641840c16074880290b001c040c10080090b070415410341c0c044d032000d40c10b8a01c500001130803206500c0594a100c0014a04400c0584031070f460080000c0f1b440c401401003900031980310340e07160b910528000002004110141c040420132030b00c060300040760750b6030f88080110010001c01c006803100b014900040440e20709102c0403507160410107010b056104150030340c1c00b00c07031011034041030200224000800d1260448500210703018905c090200381a402805042c42c02d0040080742e800c0d01101035608014080c3d08491180c0c404444400c42c5035820440501940520240000c198010510002030454100360403e1000064040c0c085080c41404d0003403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 606643570 1250 606642320 606642341
    0x40b15092e080f1302060906160c0b07060e1615020a1502090910051c020a080610031e020f0f030a12110d030506031e190f03080108010c0206040b0c040902070501020409 74
    0x4c041d9074101580443d64601035034416900c24100420840284c11030200750054042d03100c5100d076441c91300d490100d8290f070170001064800f203107000102d20001c1800140c417007c80e5050f0451003255490f00d6110103184010070010801c60161000c03100000381c1d02c0e400b03108aa941d000015840e1380040f0188207841c10300900819078012940400c11098940b00b1800e1029450303241440c1c0c81d8181c0340040b4009800c0c640c0200d10703c0c402c0c4001c00c1700c0b0070048500e10050713910455502e0480c1980701c4031030820380c110240c00b07940f11503c40240c2101e46407101291810000240070703951000c040351200426404103803140c401003495099403040b140c0e0700344207404081d4020308041000d410910b0120b41d4400a106540d504554504192015028104145080817031650350409100721140b411507011a00c1c4d0000b1008901510004904500706014599500200381c0c01070250b6903c41d1610140208045c1600351a107204000c08101c46800d03000618602c0d008034000f594543c6084412000c07140148003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 606644820 1250 606643570 606643591
    0x17100509090309130213031e030206060619080403030b03030313030e121f1103040503185505190f06030b010e0d11040b15092e080f 58
    0x1109160740c0c3c04c4a403500255210100503154498002c00c104201155003001d80403902c041d43c0d000c00c40c8000141c000380c0e20302c01d5003941e4894445605005990060301c03401c50184180e0708803131170154881d4508581c858024540420404480c1012a00315031080c0ca0f10410003184902c6141455044502d44032043d1041e11200440c00d190703251681c0320b034880c0e148402d50290021202c80c44480c070741c01c2036441510104006590341001c2c68025903036880402c0c6640301c600702ea090141c1c0c44c54a10706028103c030f1088010b1140388980c0e1001110f610302000705040d03509121001c0c44490320b07642400300c0c40034490380d1804003550030441080540d5080040d860314103045d0420510090780e0402e1480c0480350507060128642c101c00005881c1c1003e00d000141d01702d107044a03418244002c0c0382aa450303041d42603030204030703013000c04c1c0502c802e01c0380c814101040c100040203011100c1c1081402001140110440b0080b90b88400c0700d13050035040280310400010b54a1004e009641c00c3c00800180c0000003040d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 606646070 1250 606644820 606644827
    0x90309040e0c03100902060910020d030c090302101b080408070501080c09030d0809010f0f05180a0b28020c010518010504030f030504081b01020d0e2b171005090903 72
    0x2c000b076621100d100c000c120454442803820115115002507421092008100030003142544170300a649000c1c100c4003400080c18200503a0b0320038003802c015400c0c3c03900a480b400000000315400c2d641c031a50036070026906c2100303080b180701141003640030307001070650903005d8040180313031600050100d2406000c3d000c105030100800c5c80c6543c0c00007000b1580b03466600707010680d0f5444075100e60060030050640000f02d0309205800c2101c03550341c1d110307911807a43da03081d060081c22640511b541e00e4400c0c99000342010720000c04a401c1d600c1c4d41420200b40d1896160021030004222400c0c02039030455003c013080d80c1c0d100d5080c407180124034824100203c000d07030300030407440ca00340c3c03402446000c124901205060343e40b8003103018001404111810302640500346452040e0114065000750700855516803d04d2821894121901010174104d400d1811227045514003009028a020590f0700e0100074010b014a40d00091360810074200d24901c6120181240749015107814107008002c0c0004005d600c0640042 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 606647320 1250 606646070 606646093
    0x61a1305090a0201080612060403020606010f03020a02060c0313140303010905010506070c030602030703061d060108012723010f03060605040603082a120421030504060e1305090309040e 81
    0x901603602c50b03024a408071141e00d03000007294030380d101107600c20304501902e0200000d0540000d4641e00416080c0e03120710126103c080304908900031509070341f005800400100b100003090101031a00192440005007079600326985003c030000340080c21003080e400100c0108085c241c2071148a00424043e243c90b85401c4d008c3c0c0d01d00054a006000040000d40d02001040400d44282d0210300a0040248024400c0c03402505070410380c4401c4031070380c0c0014000c2001003814044103607540c1850301e08068041c0030040c1064003101801c20094003440c642c00403603c0c0c010349401410558001d1801a00403000c0d0350450501d001a1490360700401d014900f8000e04000051982040f1222002c05103800904030f00728400034505440718820840702031044441151100d41c0c2603000b8022128030204000500c0040e4400310054605a18080c0109100703100030000c090242560344440e21000b01010680a24032000c001102c07403c1e0381c41c6080d54070204074001d82d424548200c1c210320311400c00604450408 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 606648570 1250 606647320 606647323
    0x250f060219030804031202030a020c0c332107090509070804030509030f030a0e12010c0507240f0e010c08010e1815072604021e030307061a130509 64
    0x410018100403c1d94005000d040c40707030303e00130315a2045c48015507403414080d50b080080c2d00a184581002c0c00707094445025450688005080a02880951b640b1003403900502178031072048200d440800320042040c1142d081100d8816960b619040f041d42d20036041582005200749103a400c0680110400001c0c0031b51540c000c1c84c01540554507180850340c0795071140101742031403c00500e20b1340b5071001060b1202e00c80c8e00829480140802611000d2401354580c0a690a0324400081400440d00030401032003c140c41009000d100f0741c98003440e8451000f07420101c01114031a28004030013035900e6070940c584403401e0040d0070124103145000e104550400001c02800800070b8020003a05000b10100d00b01036030148042c034500142510b0715a59860031400282c03140c00d0078001a04d052821011072070400000c00c200c140100c0d005450b2490100c21100d5811468003c410800d40c148414040500003501c18010707004180100c0301080b8058074804c00740b22031030941c800030003200fa04190401041000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 606649820 1250 606648570 606648613
    0x1703070b0f070309171e070b01050405040305070c0b070317060906040c020c031504120906050d051003051c0801052d0f0a0f140d050c1002250f0602 65
    0xc1d018141155100e071070050f801408610002021a4105182804040000300c058090700b00320701c5c0003801038848500c840d11b141c45241c5005251448a20042c411030034903920455019100341041464880d040c0c9030345003480307160740c0084503103840007841c4ca040691158000784048a0a140c032100b601300078000074003242000f01050f000703d079201344940c03500c0e10030081d402807681c002d01501d2041c0c0c040e54002c8400802141e054038130300104101d25804500c0b51141008540c101c1c2c3d079050504141c4550324000e41006060341460105501d00072011070710901c928100120a214003440402e0341140c0a44841d10582c402407113101c0c0580301480c603820000710949004032080d039020061841d440010380d60039182c540c00c0c0d006014080007080d2041824208401d407140e005402098032003da01f04070b01f440507050001c1191b0001485075280d418000b100c010241c1480c016151060303000d007213014101108003200c5003501c000304020800142e0b4000c1040280c2035520160481040107208a14480c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 606651070 1250 606649820 606649831
    0x2a12061203080402060d1107020a171b220c171339300809030a060c2f062403031216110c04090201030209040203010e011703070b 57
    0xb09a038001421581c03060200d612540c00000c007086408004c4010744103070f03044004128001e10020034003040d55201948465540c108003401410b51550740a04d10072840031000103140c200042c201e516a4206908901e44040c0d440084001010008404014500010a1078611100c440d035801e12014241c49051111a00d80004109190030692403243e2a50412484c0f5404a10b1000c9643c0340f80d94103942c80207003110550008848040005040140c484c94410001c40d805020040f2120000c4d02c010b01901c1c0c0c181e002001e807280610751384c90b0081601d02d00310103200001c400075150600c2c1c3c07000009940e088184825600c42e5070322511911540c0e184041c080e00305e040c0185400c2a030310b40001100c1c40c680903014003540c0c0c40f400d070524144e1407801c05541140e580ca02e207002070041d0510511081440c2e010600003000c1142204044c8801800c4100d8140c0c1055002c220340c3c441901c642c00294000c00320b420b0a902c182d850116910310f02414254803002503041000300101040e442e03250a40c000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 606652320 1250 606651070 606651077
    0x30604090201090e2a0c0606130227030d09150305131b0e07020d021e012c0105060102030c0a0201180e040605060a0602030c1506042a12061203 63
    0x4040600068400c20f0882d40050016450b250401c00c031501d20190600030610b0340c07020b44589017020751020301e5038011400000c1403030b03000e00002205860034148d4140040c0c421301005103032150304081d52241c6448684581000260a4000c04203401c080000034140c140902c0d1a4041340d003808500e042c41d0008030010360806894201045c01c1c02c5240902c0d000403940b080070052000081001028918030318441c204100b482100000c00741030022480c1600c0c40c60581c0940441408070744d041900110042062446641e20b80b01d080214480380d03d40c4400101481291070702a22040744c841c00c1d5000100481e0442d0018042d00c102014002924200d80b42e090030404c840e00d14900c038800b12000660b100341c08041321300e01030200780000c50380410700a00054580101183e02d9075410303a07591003034031108501a808046e0b02c8483d011041035054006c44000c1011420b8061485a03002c60400d000000e141c03c0e034517220035004650014482e040c8401080d805001c40c0f8940503880703100d004940006800d2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 606653570 1250 606652320 606652331
    0x1002070c0506070c0e010e0a0c08150108040c0918050c04020a05040e06060702090c0a0f020607020d0305130507030506190b0f040f150807060801080304030c0510030905030f0a0e0a0605030604 84
    0x4c103c2c039450040060b194486000200e50303911325000d02c0c1c0c9881624204015490700ea40c4c107000510030070300240719028142001c40c1101c581e0004513a8204010f00076940c0b000c0e840008661520740340a18080304920306c480514100c150300300581064148000c0f14407451040150252003034000c000c0d40c08071289400e89056a070743e42c1d0b0105085200f030107002940070605000b005405601034014210f40b0165a0742d81da586280780d541a070fa10003042da45403000d0b0303010700d100c2810144a50003069002c1880c00d03903218041c0045e5a028603020305508121000d412030b00030400f402d41c51300c3e5012307241d41d00d100e414081607142c00003040c0c105000d02d032124001c644494020300c0c0340415401a91220500004101c4201e40d102d51070b070b0310f0380b400c7e006580015001c3d40c000076010302d0000030341c2c040da50081052541d840c640700410085c0f0008084c0d810505440d80040c0003c0b0300d003072000e049460a2912510364039980c0348401418401f144004a115224546003400080e500030281d0303a00050603180044c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 606654676 1106 606653570 606653573
    0x21b0f070513020d1506111216060504051609020c010b04090203370606090c03020c0a06111c06030b070828020c060f0103051002070c050607 62
    0x280501035401c0c1401e4208654010701071010080c1e40001c85c3c25000004141a00300d940c00b640204848000d018031441003806034018042403681c42c0d601d004101e043c12803039120b0329100942b12941c1c80000600300007041242c2d4403030b01e00b000e100000041d642c0c590350000e90300020500c0b0265081c118140600d081c14001c0c10f0916600070081c0141c03c1c1c419455001c03010030040f4050704001841c444080e6840d01089280e0501c1c0a00c50103e10346080840b04d205913189030903180d04262040002d4040e0850104003000103550151002c01c160f81c07202454002406480c0c50308024010786010203142d0812a84080100c1e84500c40410310b0b5941d40300180c6415501301d905441c0381100c94981000c403c1c5082c20f071a02481c022400504148104d000c1b6460000100d6007448804201c10050040c80070821404c00b02c11170413030342946481060742d2001040c0c4028030601d4001d4401050100 = true := by decide +kernel

theorem cover : BRFrame.Cov 606474820 606654676 := by
  have h0 := BRFrame.cov_init 606474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 606474820 ≤ n) (h2 : n < 606654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
