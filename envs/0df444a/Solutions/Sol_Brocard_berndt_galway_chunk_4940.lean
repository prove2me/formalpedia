-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4940
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:13:31.581381+00:00
-- url     : https://prove2.me/submissions/938babd8-9fc6-4d58-854a-2ac0b9466e1b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 888309352 ≤ n < 888489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 888310602 1250 888309352 888309397
    0x7060c0609081818060108060105090d0b010312020c0102010501150818030703020a060501050105070f170c0f010902030c1c03030c1e11010507090e010b07050c0a03050d020c15 77
    0x1150440c0c40403980060b0403a5503095909030440d8111110f41003503003d01400e01c080001880034281e082c0c0300381c4060310307142e2250340d4400044a4541c03045d012103a0200322500094081003c441c10369000e14400d600507420b0640c1c40001a1500e98000140707411a0f041000502c0001c40c1000c4d105100451404d0090090315408080725402840c0000c20915120216800090550015021b25424003840b41080703940d0307c91307004542502c030f402c5000d07000d81628904e0f60b0001e041001c0d5a04018180902c46040c0a90052102d040664241803152207a450b01d240c041989802e108070419030390b00304c0c1d440072207080b203804455034000c420344083c040c5030303440224039846406880700300c26406038001064000d1500d40b101810340d041d90310680180790328101c005200d96000788084010784500440f4a071003a881d00e1040d02c4c890388003800460b01e134040c003003458a83d61078008519000d5403041001d480310030300520009161500f408426446005070314130944a610640c400c54442c81d80f400301030301c0108130 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 888311852 1250 888310602 888310613
    0x8160e06061213022d010c050304260601060804030c080a2a1b0b180607080412030f02121215060c030a120e0c010c0c0b1c050702070807060c 62
    0x2034500030030400050a020482d41003a409221441e00788200ea581d041c040c184205a081c0507450340f05d80c098241c0117140502d107503008a040700c40d550b201d50201e07443c06880306042c540024a40e02661401c01c0e02e4280590b1040052051502400700d47ca40940f0302d18058a0040c00c042d81d03d0b1014107003207400115488814412203080b5a24903003c0c1280e0140d101d450015216454101d500340c455500414614000901c2208058100c03229000e5603806d06c541c07070f2201c188098a01700d201d940400c040060a0000719414040c0c0014031030258550301c05241824084c01c0d8042e072440100464012501864064000400350b4102c110305c0510920300f65100300000305800d401c070003a66400b0901244480c00300760b0003c01040034120b240d440102c0c26848240c034000341c2e81c4240030f00700c49030403020717a80c5019413181d065980720302e00808a11040541d5014040c9903584180002c107403e00c1d040c40952404102c0b401095045000792004100c4586030480e05515000103001c1c800c100142c202c0d00209108 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 888313102 1250 888311852 888311857
    0x9050411010c0f0f0f02041a0a09020d020d0e070e010b07020a0911120a05070e0307051e0102160801151415090f181605030c031609030506090607080108160e0606 71
    0x1640305070941001066828905c188040444089111314205428100300700880100248444c0740505038140d4942410b90380c0c00690412035519104036400d2100c5031500500c0d014020307a4212041c003800c0420b040500714017020070160007200c41e214003000352000503101e00b01950704079074480d980024003440300d40507074480d0f01c1651481c41a54010000348140d4200561105005031543c2c0c41d0f01920204407020f15444003800c2c0700349507201062480da42c480d820b41c462404403c0605106803902004940f110700c11011141d00030601981d55408034103051002c0c410b040000d03200d0082c0c0700c8100110140061410ec1c142038a101400c0300100e4901c038980c80d60701100c00c0c45480145040507848a1044400003842c0807101625103a0007140310101260144c4200e134061100032583c4d078910360b2015211000c0400c05c2d14030b47c0400c0800c100000126205004407401810305070043c04180c141408001c1560a06806c0300d00b9507017145c9040c086600384000c00800310351050407810354680d600c00c0050003a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 888314352 1250 888313102 888313133
    0x6061419050723061e0c090f0d0302151510030e0102040b041212050f0414010207090c11010b060a0f0c170712030e060112021201062105010609050411010c 68
    0x1c1400241c0c030300c421100007032807540c40d000c0401201c030b603641d4041181783c80541c0324403c00b0951a40324085102c050028000f00000540500600007445d50f135400b20b00544070200044c1c0040c2c02c80324182640140c1d4a00c4c094102c8482c0110700d0f40700c103807000010b0380852844481401d15a50300c0d0480d1040c2401c2d01a200140399030482c0644560741e8130324100340c4840341c0600702d5101c0150003241140500036002c0c0c50321140c40c11912030400d81081010f002c0464010307811412b5114134440000c82e400c16010700704003a141c99642071558420000003500751a09034104078429041840a01c180c1c55001404010462903840c04035495092820b20301020000300500941d42000000c42c07200b03208948a01040c086155601004922840e543e0a6113514083c082d0184444040b0b400c0c6025150090b0481c6082c003280c800040c469644000c0980800f20100c188107020200080c048207001c400c0c4540b900401d042030042c402032030542d54141400c1d00c801e0110303052180410118082c00211140e49026 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 888315602 1250 888314352 888314363
    0xb09010f0c140c0f071d340e100c03110d0807050d0e0708070e0112080a0f0e120718090809120a05030d02130b07050703150e060f0a060614190507 64
    0x407281c03035000200901c00c0d03001906d40c0e082c0071072000c1500207150314140360841e10004910241d50100313100300c65002d070700c14803c9010401400c06407603141e55000c1007500c100c6081e840b00c2400090618003e0135001c014074030464988c000202c0b580c001c40d00000f42c0c0f0343c09045460101d91700c0741501c09450080080644045a920a408020941440025000040e02c43c06441080907a0b610300c0c0c2e030500e000b01e00d01d00030403a0000388580304410780900c0e2411880c2c00c850820110700a501e2022881a4824041161541c1e00c81c120130804d08044120407402d8800c070705414007031507103d078a481c1018880d011080c0c0c0204409103103071a90a0041c01442009075003c0c0680b03590740600e0079400c01035085040400203640b44ca040c0082c1c40920502214206a4020080d01c021031940d1540c1002100d5150095503840d02d6a90101c501d07181800307800c0c41461080c684002609001c100c0d401226840c0c0c0203201480140c1c19000c003404811000e4600c3c4402c60502c6148800031032904603040c0c001d55000609 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 888316852 1250 888315602 888315613
    0x140115030602040e060910060c020d021f0e030c0913050304030209100f0f0501210f02040b0711010809060c2805310b0313020d0b09010f0c140c0f 64
    0xc201c0650000d10407182c0c07030b06001d86151135000400004600984403418224a0a00300f000503500414401c0d15071030004081003640784164001c90301c2e6112400c0540050384045140403185604803484031103044007a40207180c05018078000c00d05030680580031030142c040e000700c110204401001104d018580c00741901c000d81c1000d00d2410062803d600a88048043e8220b000c02d00550071078210044450580d1003011407400400c403040c0e224201c48a01200c240c41d44060744507038040c0c0c0000d000400c160001c0d59a01c0d0f006040402c0007801380c407800d60401c04d09100b4050718413800149107420011419040755200c0610354000101d0001d511764141848040010012403904500074040c0203400200a0b025400c80402050795181c0f10a000040030781c60f0401030000c19040c0002c2c581c0b241d01c0104002c10f2240f42c0e000661902140141262516102004c02081300d1003030080d014440e081c0a010301800c04402400360091014540c03020b405d07100880c000a01c9072041084550751805042a0784 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 888318102 1250 888316852 888316859
    0x1324140406050f04080706020c0a080a0c1106090607140a0c060906020f06070807110709091b0e060f0f031903050d061d0a021606021204110319140115 66
    0x190425044505903501071800001403405043c1c8004207100f2980410361a26107246130b41d68500941040000203020303c102e0041c600003450060003405001000c0d101c10f00b80031740d0703458440c072941c814200c9103000708414403e402c5141c941009640c1540c2d44412864195011242c20718946500c5401c058035025030120001201d5820100309010740b00207500b62205640d00c2080995145000c9e5240c41c0040c28480008005c284139105200711541e640080da030005903103010700400c1d500e0112064812001e00c6044585102c080d858400080061100c00306141c070780240010342d181803c007203090050480d1090052a40d400f07106034408101c83c64040f07180180d050a00510640100400d09003c524104011519a07010016424100c1250103500e40707554a010301480650040b240c0d100c08224400c041c180061868009060740268909490515160034241310080007101e004050290708040300c9001526500c1c41240302680c0c00a00c2c9403980340035880c8060040c1515103000411400700d04011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 888319352 1250 888318102 888318131
    0x211a0603130b040605060a080a020f010819020d150512070e06010e18160336080a082413151d0a06090c050a0c0c0510261324 55
    0x143c05664187e40c0c840403140c60351219590748644500103940440c54902d8000150b200d242c40f0343c2e2040d202141030440c1ca004945520583c0c103c607060300c5040380c80302100c0b00e081c820100110014a000c4501c13600801c900540192a140d180c002e0490010b100c0e40061416400f50b06200030b0f2800280c1103520285203049824070000e0140c505005483d6800070010b02c05100380207140030a9000111580345004030103c9210488078588440c000c0521040c0f280003085100000d007804068944500e0740914100284000c8800c0f17001c140100b0318460201070b8182e869082c0f0098550402c51000501141d0b00d614001d80302034107620001d103000304650300350f2030b115040c64200d00034203003140e09210307560300c502c034080a03558000544000607070b09011a10362240b29041c1d1030485400398100031181344c3c81d80c0102d2401c510711144040030581e0760141c0c080340340c0c0740501004c2c5000b50888040755401c1074010380540200705076020340b800091041c4480c030000002001c090350300d01d0107402c214180c10502c41 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 888320602 1250 888319352 888319361
    0x11e09020906040501150c0f02030312180d0807030c090504180201110f0c060d201207021203061009080114040c120b0612010e0d211a0603130b0406 65
    0x224000c641d0640070035200c0c101400340c00c0c180e444c20164a80c1d070102e103040441c5c0c00e4030904419244040350b10038400168909200038000300b00e40700d0300c075015890510f41039400e107114007940001990108100340150ba234005c804da50007440600e004180111412000ca8003c0d180d0341000358030900d0807500352444501c4512490541e0b100ba01d428403504803207142940c80c2c0040317007070054264000d401d200f2103600d4280000c0080c030fa50a0320001c0c2444052404210318402c0c44044411204006a4410045440821140d022440c0d20007454501d5100468a0f52400b001d443c0c0303030080c4024004140c401d401a5001030160068200820203a8101610030255800030381d400da80c92039441c00040b0b5610f40c10304107002c0c00f64200031543c10301d0f10b549090148a14100d800e142e89556684401444600300340950380c1c003691369075601035948505c1400303081040d81410214805a1501404615090350a079004900800458001d42c807661031031510b2043c240703a00b8000b00032112060412040088541c403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 888321852 1250 888320602 888320621
    0xc040518010c14030103030f090306050a051816050f04060b0c1b010f0f0e04110d090303181e082808070e060d0b03032205030607090501080a020c011e 66
    0x80c0402c2d10341e64400d544038800c485860074003d40410050020034000ca6240c072100450b85020144141e03030380c0785d400c1110800d5407415106619003061103001d080d030105004070560b001020300b51175110551941145202072107814040ca8200c8214030085e5510380c014401031888801c0c9075510300c00c80d0a080d49684085294a20030301c2101004072107548282122055442d030b03030300c825106126110003a00c1d014852141a80d102e52240c040c0c0c6200400c7c4806051b07540482e160119080d00c162502804ad01d5402e8a8044580d900d41c085001240d001c180c1c0a00e01008440d100c90001640e0030104dc203842601e11441d8070400c800c10f1000440582c0d0021013803070400f80d4900b0000e89810200f2181c500c2c04508903580000140300ac0010300500c0d51020352060030081c06c03a850400701d1143c510f10b4461012841840785c40241c030400071410284a0b0550064075464600c0c01d16041000181c0302420103410b480030140e02141800b01c15400354003141c1114001410304d01070100d40c1c190320000e0f10b140c80 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 888323102 1250 888321852 888321901
    0x15030c1e030c0614090607110108090c03070308031509040305030a0e212b06090b0d080f0d0b0d08040305191e0f060e0319020604020307090e0c0405 65
    0x9880d052440448000081940c0c1e10030701a00180e86040c1c001c03180030208540c0c103d0020010000060107688020061100030322403400907c80d0750440c00090000580104644107907041803800300c03100d5501103544c0c003d0b0303584440520340340d4840c3c101820550082880c1c2c1500070008c04203001c10705810001851140c0701a1a09000001044940645512002c0340311000c1446150400701c410300c11401520190714140109008200e407652400c000584422181c00d20a540f004240450021401030117081d44040d00d80803400c0b103560340c074240244107010268aa40350041107814a00000317800c81c00b040080107000f402c40f000d035402d084e6019401880103c403944a40d4202c2800719203529502405560044c07140c2420110b40c8240004010b00c0100c112440c107404110000007a01d0351044c0425002240000c3d611048220105554200361014040656200380f0412005a0300043c01e40151114040085542081c1d03034190707071400c80f03401c4c80540d009052100704001c844600324150200500321 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 888324352 1250 888323102 888323129
    0x90501080a0b37062304030f030c1406151e0a0b0304080c030c0102090a090c20030408010905010204080c0114090409080d09060b0102190b010b16171804060803030402040504020415030c 81
    0x503194000030784170b075200c0102300c202c0300c8100b180802e010342e04d2900d00e01d001d0302400ca1641d101000d041d041072401c41d0a10344021100101202a08003101460301c19514102d602862101000c0020f0301b06c505032040d01d091000c0000082c08100740102a10020101e50040701c0c2c9550000150a0103034000c07003149800344001c0c400020340c5143d14064510b0320940354071641c0100440d409081022a140f1008482c6d91008010000e2210024440d8a5840307024130700060b100e0781000d0b003543c00d042c0c41174070a904202d241c640201d00e640010040307a02480d41290000b50451302e03032a15102c81d000365034141000b01d28140c898810f1285c59040165900b400341e003a500e03041c80d01001398400c0708800d240a09a144c05200502144c00075000400c0030520b03480d410002400f840d0703203080b01038040307125804280002003000424111131a1145400c04000c580600c811030801003501e46d02d0000403c0a88100c0e01c51002c1800d5496a80c04080c8001c01c0c410b91500440e280d0070540102c0b1030920410340d050007413 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 888325602 1250 888324352 888324407
    0xa020a18050f01030b0612030c070e0108071a03070309061e09050105062d030717030d05090304061d04290111030c07030b0702030904020307090501080a0b3706 70
    0x190080b55050340d602c0490000903440780301c1808281d0500ea01c03105031902c020441d0f907941d01010042240280314140356060650305100c5214100540369004094000c400306896845000c044240d980c400b0030351070001030248907828101c1c0034040e80a95140400b01070051403158401030340140104a02940080c07240c0e80304c610500081d154070507041029115140c6041d516003c6688003101108001800c5072000e41d00c0c0d00144088003030a04404041d94400201c124021055010b096030110340c901c05181000c0c0ba080010b4220b0307412224902c12002e00d00c00c01d24050340d442d80208680d800f07107048070807610144130410301c070195075074500c6001c90340401e055440003030004201c0302502028000760029515695401481400140030703201035010510a48050741c0741c03072014611400c84c0c1e98a0510483c40c0c64005030944001074000f010aa042c01049284d0303882c2c136110541184032a94541c01d90010f905010803494021900e044c5554945581c005110359000031950505240304003642500f400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 888326852 1250 888325602 888325621
    0x20a1b031e08041e230315040803011205030d15180501030819020a062c1504081b030705060402032e020a0e04140411040204031703090a020a1805 64
    0x300e010003891490100014041026034a1040c3c5040e044100c0004030503498500300ea0a510a10026a405494170344100c1d0710380c0f038104001e4a42200b6250081c0c034900b065203441480384414001d2103201a4005801e00410000b0421900c0030418003000300b002d00041d001000043e4503a100354411551801c0d01154464518818141240da000c4103241c41c0208041c80c40441240c140c0346a41503000340030b41700d400320b2458014550f0580308031901a040401843ca003e841c4a440002c00710107134080b40d0b0418013038415400f4590003070f422820203a122003400801d1402500e98503d6035200c6c4c000483c010040100000c0d6443c00340340300703c003540c2c1e01072146440c0310b10710001c031505132421414003040081402c00c250b006140044240c94904032081907000414162a0708102d451100e514050800c420b000d4003040000c029441101c0c15441c0c00d18540b510740045080c0007407108148000008030b940b029007085500c0c1c1380c03030b80600101222a03984503c80c0e413600050b240100054100340c0026950341 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 888328102 1250 888326852 888326903
    0x1c0911040c030e3301030305030a11070f0f140a050604140c130c0309140a0302011b052b06030b090609070302011b020d020a080d1d0a0510020a1b03 65
    0xa19140003490b0303486000c510000720101c5802501003075080d80620751280404000b13044e000e0b60090b01d90680d00c0c01d020b481142141e1003200c1300051810184024070000304201c812403446500100c0401e054182410140888599440741c0a014451098120308002001c1081442140a444103095200044100f5074460742101c10307080d4884c05401064180303820541c013818081d1664a00041c3c820a19502c000004651894022003076002d01e0800c4105a070901441e111401045458450764200c4d80707010b400c90084142c100310780603514504180f420100b46e9000c2500e90404c100f48030b403ea4a0400d030386412816036821416010384d4000580c20a4001007800031254182e480c0302852140612031010000680c004a91100c2d220b8a0407001d82d0760f030107810300500b4100c0041e00340c42c00326080203400d600c01031002203031545c1d9445042d40c0f1342d41e48107034a004a80342505e00d2003840300d0003e8100d0900c010f07408001c124126004082000c4200c40c500e030401c1c1d82c41400c18940070042085030001d4035 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 888329352 1250 888328102 888328121
    0x90501060b03070c2d0305210c0403110109140616170705070f030803040b06040207050d05040906050a05090a1e180209010504020c0d11030403020607050a230c061c0911040c03 77
    0x685e201318204001910a400503d242010402e00b0481c9040b618000c4042c1c04080d19403104543d0003140500034070444081362040140e00742080c403892454858013004c0e400b0401a814824a0007107200140242002c0ca4040a107512240081500f4003103030210600d07400034107042c0d403940700c1c140001c0740341050805441c0650340c001c28610309540e80d90f42d0307060141030018502a0041d03002d001402c00224108042e54660500d601c40070348860030702c0e0420003160304950102e44124100801013080b62a41901c982d088042900c0c0810780e411408403007039824485a45a42145241c031040c1e000511311130740307070050740f0f80700704ca207140c644c2d9807101088140d0243d640981c0c0b040c1c0001d080c030442c2c03501400c4000d181514071000d5030b04040d81c0c0d40000e0a41c0c0c110340025245600645002020810480008580000c3c0000400840c0e00401d440c0780d90752140504542c083c000008035554005000ba52150080c0c802c0101408080c01c18038050140d44402e03008540110f003010128200070b03000c0d0203030001a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 888330602 1250 888329352 888329423
    0x14070611150a090803070207080c0a0b0906030903071e02030607050c06070e03070909050f0106150207270501120201020d0306120f1401060f2108030a090501060b03070c 74
    0xd03560303400020350042402515a01030b19941e202c06100061014016602c01c0045801801d00c1614010000d41442c0032070395001c2c4241c201d00010700618a15a058540d00c9a0564000780c0329602e5810280c0303076224065010f04070800f42c6100c09100c081c0000c0c031401903403003602610010b0b00e502c501502e0300d002c0c200701c070299504284009282248134203605d00b0485070041c00c480240741e46165407002c4810074002500d007a0000c04e914201650f0900a442c001e0440a03859000c000c1e180d107000b9155480c50061000035400003800080b404aa11000c00b601e015805041180c5e5a50b43d4161030320b4403200c02c0807070245c0180071000c802e881c0644100000c68011030b032070080000c03050790781d80d010f940008801c844c40c2c0f21580c41c00303004450034031509000c1c00c000600500994244260b0030454410403040c060080241034040c0c000455100c00d494011b151020702103103501040c46e000f40506030301d411650b00340001208018100d680b01e00b2052085010b0016115085081076501400030381320700300c480c0c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 888331852 1250 888330602 888330613
    0xf0b090105040e010908030a06050f0a031a07090807060c020316050f04020702041407020c090c07080d0905030702040c030b0120030a0806271e060a030305131214070611 74
    0xd40e0402d504061100c40704800001030b111542c1d034842000790000e80b0f2171050159206c40c14055070510046001c200302d0221114040107113182d88070440b102c1c003003002c061030108882c045286a40107039090b502500940e41660300305a100d07c0700501c2d90400000a03442489080160444c07448101012025558090000c0d1411813040d03003400044c0d0320511080781c01035500c1004002d20650081114080c070002c0d801341001240940c104146030700c018110345095242080f807000043d202c0001c550104c0700e07803007007c00c0ca402c45003001c5046000303045010f074109040041500341c07683d1562005003101000d0302c0703140c140c0c98052542c442c023020010030a50740b03900402c9030707880c580c1c05a041194040c0004084c031800060410020143c0746d4140e00401c24021a4010700072030a8040300764840700e03007604441031141d1412500140d1100040d10003d001d21400242c07040307140e149240800c001c0c0015083c1c0c0c940d42030051425125030000e80490000e54080c102e008640c1c503104104404010054000420 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 888333102 1250 888331852 888331859
    0xb120a3e06130e0405030a0822170d1401230102121303240506040b091305100c09090e0a02030d052503030212010515040608040c051f030f0b0901 64
    0x2401c1d440308100014042141d60b0004108254490f01c602c01e03441900510b0711420048000340c0f10240c090042070041100e0300c0c2842024054822401c1426000300d941c0704580407020359151240b0075040302c03418803401c103003080c04981158100c682c102c46140201d4105070010408031461108070000b0700780181c10064000c4028016440507000c0e0884201d9144000f590307980e1420a0b0090203424141c00080408114003070001500c25564031020603101400a00c5941c4006494a50014184c240383c107024000802480700030007852940b0b043c2160200001420340350003608225052061030106c9040c154801001d070800b2601d41103260303010700180f01b12140800b040e5401e4001c540c0140805208599250070b80b2100c50901e5501c81c02074900503503c501d07070030403407170312a005030041809034500300008c2c2d1070b04990000329801c07521030303140070040b0742c9861420020310012a800643e00002c180c2c405030714011400d03800d40302400503803070801400b010b1288410a07a0b5500d42001e030701142420040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 888334352 1250 888333102 888333109
    0x1510140703030b060d0e0d020105010609030f032001061d0a09050727050f0415060501020c21012301061409010e1206270705030606040b120a3e 63
    0x200f1028000038240c2e414000c0d4264900110fa40b03601c1040c00540c811440850b54607020310540e03015220a140400b03145080d80c41da109110100a0010100091903814684244a0b80102c41010070520020b0081594541d080c9180440d42d4160400c0b8212100114800c00c17828407d11a2107075000f0080c114451406130a0700d070240801c0c60032480813003403402c2014170702014070a10340b0035641c8c02c5101c401d030f040a06056400c0c0b44803081c0001c416103032400c00c0c041aa000140f42024402c2140c0c400100420381a00100e2081402c404200a6080070200040072020b00e50300c16121401c030b82d405180380e0f0f0381c003400c071515281410010321403502000074041070352065a40e07024802025000fa642c140c90ba121041c5003450480700203202000203d40c8002c2c800200301500018860080100340290500000907221907018051b54410350741c600c2410700507102c01e041c20701e18881020030349511020303d00700030729601d007624100075401c181401080c05900012824240c0351403a4107486e5844201481407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 888335602 1250 888334352 888334361
    0x4050c04080c011106011a1b160617040209060111060c071208010f030318080d110c100206060405061c08030609010e010e060405090f0a06060302030d050f1210050405151014070303 79
    0x120102c0c26042155035200300611a50b40c0f1901523440c020206607150f039012034887d40d1280c0010301000244003a200014030414103c03608140c0498010b0015240c0c0001070700c110110400a200c070303024401c01c208103050050301410b10345010708817101116024143c200c4806209001340c49050110b440240080307842a00c02c2400a8080750700300003a10b858240c5d0500d4201a0301c405000503e040302200440e00051049503002e4000ba55451905402418040c0d19a84020f16080c000c551b23501c00a151a95000c8140d61541c504d01039002c010740e540e040c510b10940c011114240603485040c000180440d40c100c1c4103040f6041d5105800d52511040100009004050300300211071081290310a00322000b801800304091180c02c0008809145105150410746490032603030501c00c06100411020a00c5005c840680c40000f011400303594612040000058454011940081ca0001000300080300307035240c4440a00e0442d0f080e048507201c0d00c422501000e00c20400c900c0c01805120000000780039410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 888336852 1250 888335602 888335639
    0x5010c0507240b0a03050c0a050619050706020d1503033009050a02040e0a150209010807050a0311030a0f0f0902011b02010908030f1c063204050c04080c01110601 71
    0x380814a8140c45000444e4070000307070001ea03113039004800d1240244c50108000d4005000648010b4180340c0000f004980388402060518140000025043d0412025504031800c560000e8010400865800780302200382c01c00d4007044001c0b40070368424010380300040810140e008030700c0c401100300285030500d00026018001080310248511001d101c01a680d0f400340312241c0408074014011540c480c02d00c0f004410440580502d02441001102c3d800e0364403001d41c40e1302c00f0f0b00d410141d81d910200d40048000f07000d139050311307801503401205100101d0310a070080701c0406a4100d0130b101c102458407010703048a0398001c009011802086007d03608003040102d20b0441c90050400146407a640d0440e5070850b0312040d840381041e00000340c928103940b9458006441c005a181081051505001445806641500300c4850a030703251766206203281d94804003c5074014000d0300c1400103007000074030090740c1c0e00580515401c4e070050f0740301403a055104594280c41851800001c0c10140d103001c05c0001c510b08090f2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 888338102 1250 888336852 888336923
    0x30807110411180429220b0f03030901091a0c01060902030403021c050a0c061e1e0c0c0b060109030f1b0e13032a0f05010c0507 56
    0x200380d4405aa202e00c1020081c107011040e003079a8220b008504866080070320001c0d031103a0300c2c000785070b4403002c86035041d0804824010f519140c01c1002100040890804140401020240e0122a1101c01c01e9801200d064401900d080880c6420002015103d0103054145030008418010400c0940d0f0540c21890341c030b4000302c480c2483c1c403042160103401d44907a60042403c4607000400d01082503410048113441d42da0202644503086c5003580014020311846d46c41c2c800b0000301c10701d81411700c01c2d1a84406015100d04071030480010701940d0000241110040c1001d055000301c00c00380d103801c60750007030800220856980c040c48090716034400c0b1840c0c3c00a071241e81000000344022001030101d0750411b02e50390180d22000c1c0340713155201d0011030f01d0200d5000039070311407a00740603c0490701c211002d0b86201d9a040c01c00f00c15071721004110030102c0f50305500e00745202c0d5040340f00720103000c0c1440301d08180310301400090003420445a0195050b1080007402070500704124070103003074588150100b1912001d5903 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 888339352 1250 888338102 888338123
    0x1f140618070f051606090c0f1203050d0b0a12060501060e21030d020a0512060616080315100f0908070311010f0e04050a0e2109120705060708030105091b04030807 71
    0x1244030080c1c004441012520307075a550506c2c0041c04011036141c0e0090504030f00307104103d42801041c540c400c6980c040141400390100f03007000e00c81c900da0405010b00c0f40c09095110095668140e90030700d051003400695209207064008508244a4040c422071810040d00780d02c0250b0041200d8949070908810b614100e01082c00302c2c92001c1628002001d51407450742e51746469a509201c0079a05410103411b0501c00e01042206c41405001c80242204180e0802c426607101d60303540c1c1039201c4040d0800300b03466004016480710f0206d0f54200208184060b580d60b20003014589070100300d1381d290682c0c00f014080100c2600c038110a5845284581d02400072403501d000e038400f040700484c06403041680e02c00d50075512403a18901c001420001180107440724280040711082c0440300300303582d104911180f4007445a15040610009082200b140180400390800da6640000d080010050700280102407040000c000868400c40300d150358184003c16a5102e58036051556035040002e82c41003808940354600c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 888340602 1250 888339352 888339367
    0xc030501181a01200613021c171b0105010b030a1404051002221d0c070b06040c11340e01060e0103091406070810030503090907021f140618070f05 64
    0x2070150b1401044440a10b941b0401d031481004088101021844440c91b0b51b00441d2010034030b415900381840301040305c45551440313040c011407569803401ca45440c0d00d60070f040000407a6150320004621030b0100c924200258080980c44030007075042a40c000d0401d0b03210345101130710841aa4000c1c030b800855140300a00008020100204850503580000d0f449038040c514455101a080031080d4020380949001e071504802d03a6a03075040c0324018116901569889248031049401902d40e10044203058003201c103c54140220662010150b440581c542d845200151256180d096101d5051782c10704068498070340e08001c0212241e0340c0040d2280c0c105501c406128001c00c140c420141014403540015012030329000c2e00191510b140986511076001c0ca07044100081040801543c0030050300301c07109586901d4190003240741005160b10f404809842c51040d664000c41c84d801010a2035945001010356601c42080080300b02c1106015001c8030041030000c1d0403503104008004003040d66080c082d00300620f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 888341852 1250 888340602 888340667
    0x20c030706080406110a0225082b14071514070f0f09050a0b130308030c04080d0c0305090103091430090a0e1305010c030501181a01 58
    0x200c0764408408100c0030810b2009128841c081c0b0001e56030340120052400b10203401c005d6032051124058982040307035110703001035201d4030b00e98980204400c03c1240c2d1441b0a0f0000000e0307940a001100009030101280c3d000703014010302a0040401402044909050300ca07258a000c004078820300711200d1303a0700c0c80410411000700403002e01494045d9030b150441c4000e2400940070a036100840301c02d000080c10200541e907200c010540c2a2124104419255080180c034801c0b4506241c00052042c1c0e4003004001c41c00b60f4071005001101c82107400c64601070003004c030070303101001d1004014000a4081044804a5001e60000e64829114910300c01c10103442003415030401584422980c5046001c44d00e4101886141c0c034010000f4911340a0940740c600440d0004000d00018800d1040404603040052050341151600c15403154000c002840003070100a002002041c0901075000300c005200c1c1800c40b0b8016501c5031207102e22000350f11810f007281c444011f403410000100700e08000450601010300004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 888343102 1250 888341852 888341863
    0x61f050d030c0218010f051017040f120905010912030c0209090706021b241e12010608060d060b0429010207081501140d06050415050a0b0604031101020c03 68
    0x81c000e9440400ca004144100444141d000e039206000040354001881940702140030b100491324201c50703940c01d0703e0150505690818801095203803070711860307080009000862b02c440004030710448814440d50202d420986000003123010f480d001441009081c48203a50158861400318020b044c40810f501440e4001782030880101c6007091141c1102c0c204101031070f0108142d55290507a4003810862403162000305a40c1440d8640100b400b04003008a8142440c130741742101c0c0311032101c580c144100b942e081c0c0c00703080c9940714101001c17560903f14000951280b03d000310501509005040200819175526100c0240c920940850740c42541c941c601841203c100c010500e401c0482050040e14008200001e410984a03600c02c2016400000070090f01440b50754102d4192000e190a40c2d416181840c082071070200101e4004110318034102c20b10041c404082010007a0178002c44040c8a10740e41c2e00031079402c1d5500f000304140c01040500c41400024035030540307a036030501d0602c112469480c1140000e803914 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 888344352 1250 888343102 888343129
    0x120c05210304260102210a0908090d031e0305041a0702030706050406021c060801060801020a0807080c070c031110110d03050a15180b0303090d1209030501060807061101050702061f05 80
    0x1000c00c0c240c1b00340900e00b1100b01a61080c805a0100051940c039205d8000f40d201c0c3d08001403052a180c0d62403401c05005d60203c1725010b00940c921586518178000141c0100310942d01607803038010b00c21104004010300e0041070700c50030690740914102101c0e561544c000d4200500101c0d42d6540a100c5a80741d0040d90a02410301d043c00030020031018900000d0174211a0b464025041c1c59004108402030207800c42e070000c1d0008030300d107031207c035641d21002c916415000307107000201240c00d80e520020912940170300020498908540c42c3c00351800b035440650b28106410090303c1140c01c200c04201426011f0340c0210b901140044010601000e038110b15988003649400208160b080d80b8002c4c2005403a910400c99000c005600461a01c2103101c0021800c84d48000014140003050301e090380424801e400240041d40c0c402c000780030003030311092030030784544183c01000002959240280c02c3d410701401480d004100300d4001c3d180135140d100700f05990260845160818002c02390340014640c841d01150041c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 888345602 1250 888344352 888344377
    0x9030201140c0d0b10080f04030302070516171f02090a0504090c08060f0c03010b09030319021c0c0c09020a020a080a080601080f040b011707120c05210304260102 71
    0x90b4a9070300070540445144c540315070700070141c0d00029201c00307800005541e0040819449022580e03594030f0100d0191241c0e40008140e0301449080c1758000000f05880000c3d1601d404840c44100d18143d031856803200040346444400c40d107c1960300b03130f582c4280d00920444c103000c1c0858803210b0700c1e00042000d4801c803050844000326410b4040040500c00d21209400c1024502e0742e0f003090074908070014041c00180030744000000005118041583c042040b02c14100307000508012210000c0c001075190319981000ca0500443da003610745045110303400170220b2942c0038038444805420f10034840c0c000d4010303509203425840740c070a07003001060203907000e40300c1a46650b4032076085180140004144140150100700350a28107803c0c00300007460300c05802d0550b082040c002582040401140e4038101031070340711040d00210811030f10284106458004241c500031343c0c0e1318080440c500f04020b0020000e03100741500350028407060103020000d0350818a855a0717140d000c5c03c06280b070042e1a08a03402144403418 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 888346852 1250 888345602 888345607
    0xa060e010e1e090f0f1006051e070b040c050a05010309200a0e09010e0c0109151805060403050f28141c05030a0f060b0703051b03031602010b0f0f0409030201140c 71
    0xc40c04441c13a05c26a010002c880705040a41c9010006043da0107003810740059641c03415100400c00519000350395005401c5504034031542018180905900c1441c01144e002d055a5500418154003e0151b0381282d07074000910f45040201245085090b20300310461644040e0104001070001d00c0780382c00341d0041c607a9030000602602e103080104d18011a030030321507041c401c0300c10f41009600c507000b540c0b160344d8200341807400500c4804504603003101d0f615000554002c00101b008014004001040e50107070680c40100d40000039010402e00313180380310b451400e4060040d2021500010481021000c0c1001c080040f651004806000c0e01c034080d810031000c6000031400701c100240300c0a640901c415001410004014483c180b2114200303a04c00c0010240900500081c100c5289a0300c0702042040c40e034403070a0703075260f0074290040707188010780750342450041d800c0c031000050038a422042190209001030041042d00703203500c00c0c013010f030000030006e9065542e200c0c2002c10b09107428800d6031050303480b41e0840b40e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 888348102 1250 888346852 888346861
    0x31b06070c120302031902181c0f020d060e0a0b041b0609140d02040504081c0507050d0507030912090f0602010e1b0316090b0a060e010e1e090f 63
    0x24505400101200c0820412003114004507005030061444429a441d0269a9a4820f041e031240c00d81112503000f84284001107854505117921291444600212008418190340180e040f80051440320301800307114a4501510051409140002c84148200300108240e124049a41d0401031514001d88800d51802c04010401901813030541d450740f0100441100c440c2404001041c400d81802420a0101d0703240042409644d00c00c00200403641c0204244080d15051420456540004d109151103c0c5113a071205184500c0f809180d00c01c614661f030b2941410811070340d010280c42e02a00d150300b4903070740350790b01c41c04618211049000c0f19001d45400d0300f194606074600080159540c092011645030440c103180300880424140785039403203241d5112280e940d84002070b00742103d00000310365032510b5010000390007111b030f0007010907010200c40311050303517a03100350544175840070340c4546000403101c42d807006452a0400034a51080078005900900010302c0002c5200d098003980e503030140015500030403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 888349352 1250 888348102 888348157
    0xc150e0c181005011b0206270607080901050a120c020c0312070c140109150f0f03090b0601120b040903110c040c02210f03010b1206030c060d0e0f03 65
    0x200c0d0000c08000030307003070745481c6210100b1038545000d124100650544400f1521010120f901c0c44a50000c04071980d620038074005035500f41c0c0c02203040c100b0400c001c0c03440925260500c00e580c2484d401280c050b24180f054401150706502031710044042c0040080114001c0304d86109810700c091703180d0003c000c080c2c40c800030507140020361768121101784803c0240b41c0009505512210841d80d100090940310341400300142c1e400800c4e90000ca90b0a04411210031301c05501c40c070300c140810b500741c603955281c032012131046050300c80f0354002810030340c4010040b88455201e0000040104140c600c00186400d100002030700b03988900300281d001440400d080032820105104c0304000d803078100d400700b110100c07024010791070340606184480c01c0414403c1c0e20519406060858127440d5050613107036030f40c0d82c5501c80c510668108010341e4182c40c071450006545814005501e440d01000104018180800e2000301030141040003081500b41c0203a40707480280010400103030480001401902e44060206c082d41e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 888350602 1250 888349352 888349369
    0x60426120703050f0c0a0c2126012301021c02010b0f04200703050d060b071209050112020c0129030d0206070c02040b011809020a27060c150e0c 63
    0x108111030586060050b00d10000080781c207206c001c2c0c181500301251500f07110050b204840c2c1481c030aa40f20b22100001d1030740c0310760125212050140003001304600e60594640380352007401246402c61111041004000d68419010700c50841441190b0380301c2108001c480c410710b5030000110140c1c1d112030041d1a545005000d03100f600d0340903201008082c030b0844400890b0000c40782c0c1008010000143c1506044c0719404840e408680039000344565651044140c0496100e10811780e5014411100703034032054850101d10301210016595803a41ca41d050314060003c0d07021480507101c80d0f50310810451205040038030f8240080f01b00b8102c1c1c002c0e42401c0c0c289402e01c0140364004c03086400c20300401054981102000584540680d40010b50102010043c1d804c652200c106004110000c500010000c10a4000301001134060303451488003464903014055209807030f0032000a4103880707207041c402e140c86000b50a40e03507805550a83d41800c4206a4036040325200700c034155094008500e1140d050805055 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 888351852 1250 888350602 888350611
    0x5060a0911070b0429011a07030917160b190504120f15020706090c150e09100e0a09020a0f060e09040303020903011406040b0f010206042612070305 65
    0x801d0007070400051004595225009009242400210110b014403525140201c44d203941c1070b444921610b4036440c0c80243d030409103d40c1008020030700700e44040200d900c003655219945034403282211030801c00c05090035207100c0b01600c40380c41040640d180c041c4020003020001e01e001040e40380d6409265419080750074551041c00140401080200304051f03841d540011f5040c0c206001c1522070845140042c2403d020b0b20489240c180081012820301c40c85501150500b8896550bc00320203580d00000c1107400c0d03000c04410b003c51608c4842007000d0400c038044a9004c1500d4000301d8406444950b25401d8950a60341080c0503035560100c1421810a001040b024000b01940c2c079460510780400200420740f10350300f283c06481854003050805020b40c041d6100070030300400a0143c0c40c03844e81c03194114001146c1541c070803070411004e0711040c2049007416a0b0250b040c5c0c007401480c0e07580d840e050008080a004040c010341c007400784149503c071440c0a0501c808400c8001110b0741031030b040090a4520140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 888353102 1250 888351852 888351869
    0xe102a030b1003020f120901061203020c040b031b09040501020c0a231c030903120c050c010b0d03080408130f0b0406020615010207050f030111040b0a090b0a0804020f210105060a 78
    0x4122501e00070440242e0380c0c000e84d8444417640b591f94075081280036041c2d552101c000e0300e01016507202010f03000701d20191015004d039030400440800b03074101075a90900c031724010b500c45001940b103102804c1005080da4010b00802c00035180480c0003207180c0c58191105419512506090b491002d1040310304280b41c58048410f0081c2603408040114040304488902440d050503038a407540380806000f4040302c030080900e40706c00c0040045c403000181c210740c403494110040c0d500e8080128590300c1c00200c801103254040e60b481d80c039035071603554030011944100d03508021891030079400601080041010300203018100403064450380b62442c042d103401c0700a801c64002410f420321210b501d9a0005991003124011100140c0010341c0e00c000c03034010074094400d8400c10000203400709030920000020040050315564900200b81d407100f5403805405040492000681c01c840801d01501d0b00200e142191040140841c000e07200810303018840c2c0341600360740600d507516081004070f1840c0105110004001c0803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 888354352 1250 888353102 888353107
    0x1b03030c0705060a0c0e060723061e010e011412060c070b061c1511031608090712020d2a090c050c03040b0d060503100f06090e102a030b100302 63
    0x101740140543c1d12681006001d180082900070505c401c40d0080080560540b4240500f00510140c080d00d81000b2240481900071040e040c0d00d01140704040903040324500e411164441c6d0804a224034041c00030742a09900509850554134085000d21200d80101e81c1e041003a5a44d12407840c002011000080c201ca1240f6501c2045150b001c02510030817500507844002c10104070b88101f031000003001c0740c00c0e181d298810044104030034000c6580c1000c0361034107542c0320b4060b0ba5a0307590034265103641074001da06a88491080e110b00508001c00c0e0308840600ca551920405802403d41450f15040c0c1210342400c0c1101d04420030000c01d0500c2142018003052424501e0544001981c4e941c0e03200e64410400280c40005001c206c02205d5444240907050081c1541c0c0702c1400d0042c8100540103054500c4d0700d0a10304400040c50706007602c40c1102c00a240c8003e4040c1920480f8002c00502e21800805103222502440c5030a40f2000050032044801c0ca40b40002e008489405015480360316080e80300a05104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 888355602 1250 888354352 888354371
    0x31d031b041805031201083d09080918160c020f03030a090816050a12150203010801020706140c0316180306020a020c041b051b03030c0705060a 63
    0x49008054114400d4500c0c03014841040420028000d00301c0401801c00300350b2103101046008002000010078034500c02031181d0f2506821901e82c0b07142c0c1143c01922880c46500000c1c92440c03281203115020304090392883e1141c290754134064a5030031404a4450000080e103014a1410241d100c0d0124010301c0b0354102031070280c0c40b24120507942d01700407081c44182c0d442d4404540e101c1781c0a001c1080040c0aa9440e10102400178101c3c0201d4041c0030b81d94007a501d1000060001c5008490032141c004012100c40d03803402d100f0303054613000d01c0c0c002d80e00a00080800c1c00050030310300095000b01a21400180c3e5180c99041032030849201c02030204a0b52014402c0c4510281068140c9411503442c428686002c0e00501d010354884140c2238048904c0b4004010003c14442150301600090307403550291600401d25404101c11200e031110045442e003482140301c1c0b2001e220304058403640c070b105002c1d002181310000c0c1003455504222400d4101b13690002d24034040050502220303802403148601402030240 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 888356852 1250 888355602 888355609
    0x1218010908090d02030705060a03270302100e01020d061707061b240e010b010305010506091003020a0315030501020711091902030712050a0506031c321303031d 70
    0xb1591400d01c641a040c12100540d5400e000358070043c040201030940d6034081c45000b402611140004100c451003c26421199480c4002d201910b95810b42c05010307100f00a9601000800710341b0911212036509102141914800d44150009824949507402d072000d65403c0242c40e0541640004c8104240b0f0420407a0010340c00040d04400c581c0860310b170b28210102550104a00a030118801d9480d00303041e883c042c00366040d03100044040e001c2e603050046a80b41c1084c05018401d001001e40c000d1100000610036a20950141189903a146800704105151a07040d0303508103125001501d0507540001d0501c1001104176003c00311440c142c4501d00146862034042c05002c01208441400321780000000742118403d480f80c1161035652142009503003840c0a0320002840e0440e038490192240400700034070001e070b00c4011092801d04d0364650410310030060000003448034000081c2a918401000b03c000314006070043c01d900b411841103100010319504000348150f00b80300014100714031304407240b82c0586 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 888358102 1250 888356852 888356857
    0x1020f0405060c15040309080105010b210901060f090501150c120e0102150a0c021b060d090c0506030f090111040f06230c030913151a0705031218010908 67
    0x410031202d05440301012800a8240014140355524402d4400108810903400c982a001a80c2101008020a0380c9a1f00d40752114070501c5003001b101c4440c503916003444000681040c2c1c0c0f15604800100ba0142d54014805178090039400045040341c0700c00051091501207101740c88811110301d0030311011411901c0d058212000b0203004020001c0495406038964020084c0e2507060400100703110741458000d10403401420701000b441e00501408011600c00700340c07241c07082c0360004000d100624129404d51080d008000c00c210441d071403080360000294130355400c2c3c09544501c1c04002210042e1916500882c00c5a09502c410382d12000306100501280310489408025140b40d8280400c4410b001d2000d04125141e0a455a0100b0000541c80031400c60100142024003030075510340040700c0c0500e4068060310403e80d6480c551035640d000800c20f030402d40e140e001c00310f50800c0805103000400d071941d60550340198500200b20a8120038007004007880300f0400c81009624000b009801c50a9032078a0651 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 888359352 1250 888358102 888358109
    0x9070b040302060c071e061101060311040e0118050106060f08070503011502010e070308091e0d020103020a0c0807030305070909140f06031203090a060b0d05191109180f01020f04 78
    0x10903010079260307104c0100704074043c041c02c400141c1c4a03500807600b4205070a02c1c83d6000f603000042c404505003115210501418056940c0805000d0f40c02c0440c00c184401010190110758256481d100d8014030300900008803d0300070300071000030134107504201002c1d0280c801c003201ca800b00b05101040250380b07a8003009481c10b44440103a0350403c03810609040740901b40d0a42c00500b14001d04200000700201107005000c0c02c102528405a0f03211000c1c1c02d210005012000981c100d20315000c4000103612030340c000d1041c5041c40c00e003a40c40c43c1298542861035000244109d0219544030705000515401190020080c0008001446200b000c0c0a00780301d1540080c1c400b40e40c80a480021501943c0c0c00d00203c0300b03c92950342c040d40c4a251174a8919964100d841d4252501407070200d9018580c1040d07200040c6907904000100041303000b0b00301d80c2c40510320108042d1148200310b48141e08603956402c0705405020001e0b14940c40040130309501c3c2c1820800c144400b0640c4c810850b8000500004c81500c3c110b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 888360602 1250 888359352 888359359
    0x180804031a250804020f0612040b150d0f022d03010f020c0307120509030d030212010506131a0706050a021e09010e0d0203070305010e0a0303150f05040e0a0b07020c030609070b040302 80
    0x19620344e8404242070548902186601c0783c030106100184c0c240d0600581c0c07040e0b004540b016869180c0300140c201d07a0801d1280c403a00105c03501005000720304000f48c2140410b10180052a41c40c0306600290141e2048440c1060440003100460000d46401d009041800c18003050451410b405940003035920f00c11807100925504504040600e000c5c011403e40d1409000503040c0c1d443d403006244010003c0d400b4910341a1420540400440d283c200201550412840050803944041c284501d02c6450300030381c01211901a001c00c010000074071140160390041011000258076002a11049140740454001500700041e003031000645603030780814421384074002602d00340404402030002c6800e203c25900050601c0d801d0500728110908001801d1801c00c0c0a55820403030550a040c0521102486108a520140c101c1c80e0501251400d588012000240341c011115220070a6480c10203601c000c6880785c015801585c1400b0f542e0a060221a0348628942c0103042201d060080c0c8840a01440c0000ba02 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 888361852 1250 888360602 888360617
    0x4180605010801150905250905030f070308040612020403020a030b07080f061c0f08070b01060f053a0f0c03060902070c030b040804030b090d121a04180804031a25 71
    0xd002143c600060482c1700c1c500c4d0844200900b01070280c02401c02c9d110f50741c028480c8140703c6031484004661002540c2c1e00103c1a0b00d403034a4144100e54242041c3c03015506681e00300400001681c80100c0c07400294030038020f1114600d803410015250f204010035914406400d0810402ca60ba6180030ba004109490368400801c61220309066268150b4000014100c0c0e50000300081441407501d0028126580340d500c0000c0c00700100ca0440381030080480740c21585540c200b9101310401e800e00c440030510024806400d5040e5162a0b00081da0310b002a604982607035008200481503045c01410301401038100d080d03240c030449a5401d04240da444c80082c01d4203003040082020424801c003110001c540142c50340005080900c0410f48421000c041e0b1300202e810402c02074030a29841c02503004098040c003049c0707011a40d1105200c0600503048550903000300c0030549200050840001e40040c601943d0000b2241a88000e40c4001d41400303040950f041603266420a0f14000820b800c007039801c1c3c280780040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 888363102 1250 888361852 888361861
    0x91502070b1303020409060f0c0c120c11060a0e010e01021207020907110a0b062b111f030207050d0e0d0f05010b040c0f0201050106080912071104180605010801150905 73
    0x2d6011030540c200950180c10071107a40148150303230b00701d08141201d11b0b008114010900c3d130280c99032603d04500070604d040c1203100c03115080c0a180c844880c076000e00d01d0840d00c0c1c0440000109070342d0051110302c02207a1000090b011950f440006111658400c0c0001c0031280b4140c031110b0003500504034000e105006500c0010203051241c8281621111028101c2c0c102c1400c1c0e00c1c1542c07841404031000c070f0282c0d003030401101240c7c2c5009400d0000807040320150000340056100c3c60040d540007200242c104900c101180205904402040c08400c80341c1c0c4c0040e11400e1920f07090f810504480c02200c01c120f0300b00341041c425a5046400d41503107034407419070400d00c0514542140035005200d42641d00900c3c1894824200c2c5d0000b001d401d1000300703540200100d031303282c0101341d64883c0c0036208050030754000c4000104548001f40100882d9000d000d500013403280703a030001002e0300e5410050869816a5103030100400c000d500071306015100d16002442400205d66000e542006284035030328180d0703100c3c00804d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 888364352 1250 888363102 888363127
    0xf030b06031011210f01060509031e0703031202071e0606050603070e09131e0204020409060f0806150928050c0903151b03042d03091502070b 62
    0x1007441000300700052004401040b4004007607000061404001002040c0c251405031001045600c2024030302c000c111140d00b40b07c0101c9090300701000e0a900740c03040410444400c0c503000e90000f006016480105891404e614000300070b2903604c12811005030041c0400e0002030004144143c00c0c51059840c1c101c04511810035401420045d400550030a00020600038015448400150203410698070300c10661030f14440348180c007880710005040d2444204070190380c3c003da00c9521030709a0004001509054603101400200d415580c401c00b00e50400050070043c50100f40700c1141e0046000703041c21081031030400071070f2580100425803100c044580351840d032942c1d0b892251074011000004204002d00e424004010300d58841700700c2610a00c2440605100c540010780c10903c22507080d41d00080318120704180d44040e0304041c01c12200103801c07115000d60b180b205c580300390f9110a140002c0403224840e05000c0d049810b16004542d204e00c5200c000b11040707070002901400c451090103010740c1c5d1410321481 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 888365602 1250 888364352 888364363
    0x20321090a0c06080a1d061603022104020f0603010f0e0a0e060f06040b0a1d040f171201150203161112012304021c060902040207030809070f0f030b0603 67
    0xb4044480304101098a5a100c22041d1151740c506070100044492000462070082d000b03026a0f0190303100000180300740d2140b1044900d00b120703d040240c1403914030700500140501e03c0c40c48000074003042c010803040d840e01030146d006200c8280c541500c1c40d41024103801750b2801c18010f445905400102150403803200ea88566007044440041c0e0325107081c203040c09503444009448581c0700d1801c0c280d0720085454095050b600b262011400900152880e880303541d20f203080188191080a20014810b020640040700700005a03800d85000d86c1d034091000d490804074030180c200348441e031104005410f04a030000200d40c400906038000c1d880e07510307a602d002c96541c84511081c682101100c032002d1520807054122000c4100740c510a4207251394002c060300303000f650454020f584415800d03080e007007010700021642001b500581001c12104603603000f00d0240c1e03103c1a000c40006406078100021948140031041c080c003c1211100d112a20f48445404001c0840c003018002c1e804040c040b80250341d04011 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 888366852 1250 888365602 888365623
    0x405010e1e07021c1d0a0b04050409110901180e01020403080406211b08150d14070e01030804031a27070e1008120f070b06010302070f060606030c02032109 68
    0xf5907421300000c440d00280b07280710301014415000300300312003003c0324070b841840f01090780c540e90b00d89428180b810b000c100241c8504103050b40c500501c03100740700310780d2652a80c05003e0305a00c5c0c4d40b00d1521412002200c116104100b0072006a44180014030004015404407001c4400c586021401c41e000c1003800d4000d080a5038000b01c401c4d103800c0002c00f1180001111035120f6017261100c60017503031452410040e041c400b00e5a2a400054031680d032000401840c48641c02c08203000480e000c00d0380312807852140400c2078200703940c800c00208040081007a440668800585c050144001c3e81c2080c40c040071400d00e12005008080c076150310614100760003080740000500c0f8402240a450504003070700e80310b8407814058500240035424500d00016241d00c00c4030417501c40c0c901180c0ca0022a42c0321400705000281c42c0728101a002c00900f004a025601102650703070280400080d414581200601111501e04101080d5082440001040081c111042d546402480c080c00344030303503c098072070382805a40030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 888368102 1250 888366852 888366883
    0x114090405090d0314090c010c030c0501180212010b0904170909340519031404110103060f050604120501110307170717042d08090405010e1e0702 64
    0x100700b09542c0c2c40055210b00300e074603940307040001107401495801c1c459021524154294810f00d0500e07900d510400ba00020381d0f00a00d8010740920160b5200343c20b64140016a000c10705500442100b1340c41c1c03240101940c0000c07800200320030604d000110300c0001f0000e10240640183d000780c07160102c801c00c00c035039415000820400035172410800c20034030f03c001c1c44a920440702c0010204105501080c15100c02002140c40d0179080c05011350f80700f0104001182100101911098400c0c2100b8414081c903000d24422015a105c2241039000182140c0540d44980100e4036034440800c03158941000300e80c00d41e000c0d80380301c095000342800c00d01d000d020480001400e90400004000c50180d20039880c00d2094000d159482250729440d00031200da4003604071410301000140041000a04130783d60b255081045050707501c1c422400c00d00e014541c160f071800c0503030f41c0301c0c400185e4881c2840c16110f89805001c8400800e41c55003800305041000000d4807101c0b1460000c04004192450300810000703100c41c0016 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 888369352 1250 888368102 888368111
    0x608030a02011d0705011403040c090905030901080f0114060702041404080403050d08060f04090507030507230607030c1506090203100914162601060f0210020406080601140904 77
    0x40300024000e22001c1c1c42c0c5000482c5072021924038440c0810141d040380d4050355102140300340b485011610340e20140c800c03580520390840020310245180500c00085000c2c502954076072103240000340c0800750013003124417a11142001806280001070038169824000d42c2c400e501d400c12480460021b01c2c0041c44894040c1c1084100010412207031300400c241c0340700302d0036642c60340001c00040c1c555010946e45260300070801d007a148611b040c00e5000fa0307221802001150001035890f00e41905241e0550403030703542c8500d840500c0103c1000c0d4400c1c40c59083c1e06407602440e0940340d0302c0040110452000060076101c400d0303c2c0071480c0c1c18030780104c03010b003051071f00840d540d090480715040043e13110b11802800702d0401d440503500c0c0d45141c981910070740c070f10300383c01d00c0c409d9210004030303040f09070300307a03a100c4840031034491910070030304d43d586240078103040c0c0c0b55529003850307111000e8500401010700d0001030340100b00c14481a9489224582c222500707007441c01c404140c0d0100119140901c0408075081440e0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 888370602 1250 888369352 888369367
    0x206010b30010503070f23130e01150501091d0c120c07030f02030a140c01090b0a0209030f0a0305040303030b0111010c0306050f0a3c29040303021e01060803 69
    0x9505807412184110100c0c1d017069598086a00c80070850f214109400503165a00d015401172072641900e000e00042125881c8a82d462003c0120f440100402d501c0f0ba564581c41103220b130383e1002c082c01400b003d00b0660306e50303450a9654201600301e41d100c101c400f02020045002404090140d800010342014171800c41d00d003c0001c40f1960308005402c0e800140c00d51000f02c7d4040c004412103c9250140e500d40f10104803440d0295030583c040c107001000d96584103031890208040c403d4133030181e150381c1c00150b038420368035040624006812460383e160350004c04000340000d400c80212411682d0508000c00e071980381c4001a940611708544088117542441c1d02d202d240381e070541c003500a403502281d5a1301e041c4109000d2004142140c02049100c0034110030b6042d106d21a0300c81400c1e440c0c801111450708012611134520314000543c4030095403107d180c07012024606503030403c44403640400b05075040605d1038900a6031145141601c0c5120303070b0b0020215074044000e410460141ca40301c0112940d4011 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 888371852 1250 888370602 888370687
    0x30b0a0e190204050105071101090b070606030b15030613050109020d1203060614040902130506041d090109080a1803081b06130203070303122304030806010206070206010b 75
    0x49801c08124051124080303990380075031090b01c2c00e82d84107039909400c002d000d0341c034015034019010b85941404107004000501c0c03144070300140390543c803030640130030b50710b1651078480e540c140058803001a9170641000189151030008a0b5688040b0070b00126100030340a003481401001500b030041c4d0041d440c00740403400d11900030082c40c28000295000c1000e1940d500c4200c443c0d0700b81d10301181c0503200401c42000152550340241c101007070405040e210350703981d07200001c08551265200800c55243d81c1880c60945281c0c0d91120f500419520080c0310014a542d103280c510f01c130703401d031800070321400c00500030003080b000010f1005140d110031203503643c0c4490304100f40030308104610f4021611a040000d006240c060700001e8a05501a009011040c116078050780c0010315900c40d10311882d0f075455490851501503004018840824100603640e08050800804c1c400d80286910f05540c810f07418440030a9000071541d0442703a007122000d0721194403990b440742d19078015000c10882d80810181010014 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 888373102 1250 888371852 888371879
    0x18090c02300307080906070305010f05010f02030c1b011704080412030e040e06060a0b0702090c03060105070f0b0610030902090a050c13033005031f12260f1603030b0a 73
    0x55505c084400c1c0755159001101520001d0007011380015085000308903650158007101d00340041c50041d00e0500341c82003d407030b19003141d604922904140e40000c80f5002e5030448215080610700e40642c2c0300510b401e4440300b40900c202d208400d041e0341640100c40a0510414114070070200080c414000c4100c01c4a64a5a070036040d2174207481141c941c0b40c001b60b00d44421045030135403980075102020558030401e02d00b40380d400c010040303030521030100099400a241c1e0038902c808a072107040380040380d082010604c0150400c842030a01803501d408850b00260b40c1d0858510b90091420ba0301107001e0b522041c480100b0701815080b4181000c521002204000d01c1d03400060010355030844000c00c0083c1030103070003442c2c18489c80d0203010800800201d0950b240c010b102d155061000810140130666980c0800a40d00f845581620316901e1203400c506084661a450600704246040082c02c100d1480c0620200f886614900700c800715a200c401c0e0b0425000381c11031804e0020040640d14083c0d0355250307891010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 888374352 1250 888373102 888373111
    0x240e130e0105070906172a070303051308072006040e04140d0f0305100f080c090c18090a091205040311030d0e10030f0c18090c0230030708 61
    0x25401c000004008130b11880e50354007125107581d00e4000c17076003403c10400001d03400500018a07625460b071652410042026800c400c0c214445500c42e03503082d0604005003260409002140402207070101880450a45401c2c1c84086070000041450401040d00604144500018003a003000340400c0005030080742645a5200d01c1c024610f461018083c0524281c880220a91200200d140c0c000c0320b403002032103540402d6200603070703105039180607840c1c1d0740c0f00e011045150300c0610168001a01a10300c0d0800f040200c0d040bc1010340b6442c103086c0310408140035003090140c00c0c0d01031555207000074401e2119402c030300707030203500b00c07030760a41d1646a054014565409408181c404c840d6000c294010380c10005001415541d40d45d860450040d5004104010108c000b0048000c05842c1c80a0200c49403481c03044085520300ba4807000588803086510218417100c6030300a00003503280c09441084c0c1c640104890b2504600f0055001e01d0910044440740c0d01d41813090b50031005100801088041d84d0403102c4540034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 888375602 1250 888374352 888374381
    0x1e0206191e0f2f040b0705010b09330604140409020d0c08120c0c0111010b040c0e030d02060c030f0622090c0b0307020a06020c0c18041a01240e13 64
    0x4003041550508000c607030010300320300c4460030001007240e05c072044003901660788900000f01e129403c0c00c000443c8484c056a41e040c000d150250104130202500c4d0140d4881c1d203030320f100b0008190701c2c0d00000349107006074480c5060300303580d54240351920b035203551201010950051405041040504008140c1c210f2400703000c0c407a00c1084104245101c2e404281d078083c01e0602d0090281200f8000111b9960100441504556480b10085030703040da104c1c05407020002441e0b0b2021581c00c807000c1014600321441005034159081041446607000c11070003201c0e401202e9140c001881d4468a011070350300c0c10104200302d00ea01906501030ba04058030b401007411140550703101d48010f038403610ba08100d88410f880046c0581d201400d584006041c40d0050a46055900150340d180f1003a1700c086403501c00741c0c0e070346101030508110070001007004001f000540501640320310806981407500524481e0701c02e00e4004841041c003d190b030304180c1300e0840c0001e0a070010340754003010320384002c402015200c0807080351503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 888376852 1250 888375602 888375641
    0x30a05030708130503070807030602090a17061b0a0912030c0209010e0a06060e3304030302032205031b19060f02070608060105090405040606030b01061e0206191e0f 72
    0x100c0b0b05c0d00041070004c0e17a2101002d07120161841c0d0710480254401141643c011104500018840090b00030b041400500940549928642500d400e5628007170344000d000308180600004a10980c4114502c041d03544a40000303401e4480f40c241990058200303000254804110b070004586914a0281c0b01e00810070350304140981c0d9242c10f42034032000d504620a40c5c10038607810840c0c0705e0045031568807200d410154001200349511486290556029420650259000007081c00311102c00100180c509162641011425070814001075154440c07a10710740b6541c0d1080d1403018403950703002c3c0c00340d914102800d84101c00c555501c601030729030070a03c04440054004d00d00009449401110000e201d01016902c5031716100100c01040010f020281080c0c3e20030303a46440100024028190403400f81c01640c03075002d4851000800503c840c0070b80368003201150020801e103c4255600e000700e88500c05003503400300b07403614240a211040d100c0c003080c0000d06d0381010703041c0d4007104590f80404000200107070041c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 888378102 1250 888376852 888376859
    0x27021804080d05160c150f0c03020403050c0f0a0324050106030606020c0306010e01051e06072d0b0114031006061e0e060d02071a04030302120105041811030a0503070813 74
    0x20040f0340b01195002c00f19600c03c085000261032a46c2400c86034a0001c00011a0741d1410780140c00c4401c0d0035002c0001c81e42c00034080c0b0074003400300b101c101041c1c0300304d4604c444000c040021544003140c52000070b228100415585c2c00c0e000c5a00c5000c44c1d81004003508011540c0d43c1c03c40200545130300e00c00c40000d1700901032071182c24103011803142c2c1030f240e4071444001680d10309400c5c40b0f1400d40902d0035885482c00d400e410011991104002d1901a0084a007405a1a07801e18002c00414400114040c045400e03008200098400c120041c1100c00d521451180c003094900402d0400205445082c681c501e094800301c0c2c1190090340b4a026040c480a030701c03480100c0c10b00f080d0391807804548195400300c010302c1110214251a0003c0801c184030348a803044007e411040d0005110b000e407811000b00b9000700d51405604090815140106000c403424054282d20b11204045000716520150083c10ba40708580d0701520100502d890b820341c880101d940d10689400d0424035508030074800510300d9141e04001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 888379352 1250 888378102 888378121
    0x1e091208150f0f13050a05060108060102030c060a1509020c0f0d03090c03020d020607080c06041203092a080d02030d0608060f0c0a02121b0d020127021804080d05 71
    0x5100c54000500442c00021001080100360b140c2d040d4280e034080c8260041080300c0c41580146801803a0b546408034050402000240114500070a0603045600034403a01840200004200360000c101c400700017a002c1d0a0303500c0540045058101e04540d41c000100950310001c0080d2a01c11001e41205440d00d11130b0b003010850075140c02a10240c0070465008040c40545400741144442d140300070031803464400c190345c0e41880c64004049400190308814100024056030f0115025612214902088034400c1c954440500c403013115085400c00d20500301d141c0ca00d0030f9407040346002d088520216035114400030720083d030300e80c0f00a8060f54440d00702880061643c0d400581a4041d60524640b12401d59038070f11401c4207031b00181d03c1c1d04214410b0842009501c003041c402404c0300400c0b1131440800110f034030f20203454214140a004110fa2402950301c00040181004007420060340c50000400c0c40e4500008240c1050f8000580c0010040420300041000000c010580b0b034080c000107110365030360001ea4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 888380602 1250 888379352 888379381
    0x6090c02033601050c010207051e070503150708100e010b07060b0a060206012d0303120e28030309120e03060705030c090402030a1e0e0f030702030c041e091208 70
    0x54452403000c2440ea02050f6004501a102c8030704008001401d18146849039868400034480180d4098010043c224101c641480260054036003a4014601d00c400d0b00210008070100a10790020880507402041d03000e5800c10040d00101189101013441d96102c12540b403203544041011115540f0381190000e2a00f04203020740115a0b4a0300904110ba2811010200d51401c104804d120100456139500850004c1140e0030301a602990382c005824a0024a090071101d8202c0d0a116a600050301e0418040e42c10405428200c083c8c0001d22803440780e89005d0b0040c000d0154000d140e10780000c24000c441e03601142c00c4181c03841c110102e900325210004250303920300c000e440f81c6144000c1004802a2070034030b034000b10340043d0f03a4200011407000740b41c0c0e950742043e550b103c841302960701c0d282a0b07021181d04004031121900001c1c003071b43c80c12240703600180d0b850903282c1a07540100d84547c44003040d4080083c0c030740703141c9a01d2a020700c1204824038110f15003041e0114060f01084055001c00c0310710845101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 888381852 1250 888380602 888380677
    0x2160f15020a110f01090902030f06120f0d110f060f0916120803180f100b04060b040512120f0712092105030c010e0715080c1c06090c0203 61
    0x60144103a03483c14040500e136412140f0741400400180090754a401d440154400c4030380059400c00790038040c0030001c1008000c1c1c50710b40a60300500e50900049808215452219210b00341401d001c0d150100980c06c182030003030515181e005203402c10130040c8004138014410040b10054880c0c21040c80281401c401e403e0180e40c008c034441660705400100100700454008461000034200400c40c9540107141c904030241c20009900242038240c0c904034680107204410030708a40510815052100e044043d0240b071142610820b640c0058200c0b5210a00c0326003203500ea104140e580c1c510002484446d103074044001294156029410028854441da0b40c441c10f55650100c0c480407241203003410041421654030585650108000e51038060303400b44030305002500701c040070300342852511260740880150306d6074030300c14800420304010728050103400701c2e000c03484040c20b1001004018851000209056041848401d190100600c0e400781c00001a050350003010f245003507030b105da55003109004440d690 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 888383102 1250 888381852 888381863
    0xc09050a0504110d0f02070b010303022a300106080d120b0105090d17161401140403080702070803030f0a0b0a0b09040f0b040f060513020c1c02160f15020a 68
    0x2804640991030300901e17001049148054104203880c1c4941d06440000c0e8412005030344010120032908041404250548035072090340c055111519010481551300c280d4000440000402070340c211082042540c40da407000c91008001441d01c078540e0036a2604404121000b052601000422610840c01103418038001a03544a04000f00e601c00c1c000364640b6218100c6410703c0d404194500e0350400006081c10f00000e0175520b0604980303007414010105c80e5030451501d40d040801d1500340c1d40b03d4001c0303503401681c5072820001540e140c600890512409800c0356016000010521511040007501e85005860200040002d1641441085156401c030300c140c0c205008240040000391416500640d41140b41c0b0a02084982c07580c8000390403126003400c0c60000ca0f50f42c2c0c80922480c105803170a03440f600d074518411890103080d0004a139071400b03110765a8203c5000e08040c007404078402c0c403000240300f40111a41c6c110307607107502c21107240320b01500802641c5078460710610101c0344001460190f50380c124 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 888384352 1250 888383102 888383107
    0xb060108091612050307140607030605190501051308010606020d0f110d032003042a0f050418300f0518041506020114061e090402040b03010c09050a050411 68
    0x10280f803419200e1400c261103d02040c0308003000300340c4001d10541c0d4a000c000180ca450b25000c40040c3c1100c0c03080d0489400390362011a168110000360140c8401e4a40900f402078440b07182284204082c038998110800c1942003020000c1e1a603000552551481419154901601c04604040f81c9210507110610910351014504441d451300a03800450604100c02626500b086d120081d104517034410b40e002c4032840103000c0d052500c1211030092515050f00c66291005051034696440e9600c0740c0d900645104550301c01c4503040541c540789500070f0380c0e03a00012040440e26200304c031115440711603c2d13410415018260700384900340300712075107041c41699490b81c03803c10651603a540d41441ca00486140c00640d14880040d01c0900c1c480034100410040d80003060341e10a2184c1210011000b628141c000c0e800720602044c1c0c0c0003281c0c540d0740d680070180c072981d04580c5c59000040280c101c460744c95405500e8580d030f0001c2d59900c4080b140568000b40c0d01c0f003100950300c2d07090004848001c460350f9090b9005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 888385602 1250 888384352 888384359
    0x15020f0d0f0209120f07080d08010b0a0c020d030804110a080d0302180904080c0d05090f0d1b0b0c0705030a030915230405040b0103060e150a0f030b0601080916 70
    0x11940441d0301c1c8107540030014109070024012910510b04410140c4040d03004070340c0a401803400308809405421220041c1c44580c1a1001c00b070704024060042600d40640481c09400ea1407003800c4180321701c0e03001000155800c426042c05400083c096405071501500c2e4074840713841e070403ca03035404119207490000700010543c1d800100c0003500007414609140b4800104400c81d0f5442d00708086c0620300034640a9669503008403c00d1a00c00a11600070501c60140210b0010b517507048020b040c4180d054804024403e554030b07040d0560089000090301890640101050802c43e44d005000c00c88050307000c4415503521582056640c03032803200000c00007000c014080c8180c0000f02e100c1403502007030f030412018020342480701140c0c1c19800700502034006070101c2e04000070b20b4039018048402d502030078200074a82c02c0420f2a1030102d001821004100241d440a511320744682c000c04009054051110710300548a2030511040c16054804900081d00d440c04500031200224051441cae54a149403204490b14 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 888386852 1250 888385602 888385627
    0xf1503060d060e1209190e070305071b080d0e03040506070219180b0108010e0603100c0e1c0c05060310031707020607050601081009111201020f0703030915020f 70
    0x4021802c03140300f5141d007200018510100414000c0d4001d81c0b070056141c180810600c030114440000c510b01040907908104194498000015040500b07480c0104241e5120681a03460307659401854041c02100d0f03080302d061213140320192854010169052103458540c4685503940d008601415074001000c024040044c50140030f14006603200300b03044912640e881085000d00c218403101600c002d52640100c01c440d40cad0140c200c3d805058040451049418010301081d42c1d0784440c02000b450a41c0e5004021455000d000781e500100c1000f41200b40c60540d500c11410315151381c002c00c0302c040d4008480402caa1030558166480f540c080b100032408503296848030101c0d2200000c4014550900f0414a000343c2c075944020718207540107200034100341d454101c041303144c501003030111110b0501c1c148020001a40310032240610310400c40d21a29040410300385940284124001080410000202c0300201a055000712242c1030080a1494282151400d154241d1090303040b04440100200b118850317591 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 888388102 1250 888386852 888386869
    0x3120e0706020c271e0703020a08042616050706020d12050a02041d09070501030b0303090918070602061504020a050d050a06080303070203270a0b22140f150306 70
    0x44218090f101c00e450308000e40744c00d0100a45140304150003811214001c2041180c00a411a006260462600381c508900600b000300c0680028051720b500a00191129043c403419060010001c8000e41e41d0307851442080420a1125401c994074020b14000040c040d0020441c0e90315800191070b0380c2c0951844815078401408005e042c502015420b000124001040c03010404a4041e90a8902030500781504003900d001d030681d0040e4101401c01010803020307100030007520308000c1c06561044094580c2c0217881501078421042c00341d188612000024501ea0000c3e080d070050f40144040e080050f07120052000f60f200c1e04100c07001107501001511035070b0003e1b030f014692000411a0000e8550788860015045502c20303581480140d0010800c0000002d042401c10043d0703602d43c6201c030408076a0004641480242d110704841d17180e0110380070328243c03200c0024245150000d0360050307240e42ca4072081c85800302d9201945000315060085c1c000c4d80c2c10400c1c00901400290f0000a08543d0391804205046 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 888389352 1250 888388102 888388129
    0x90614040b13031b0609020f0f061606090b13030f0509012102130b040603110310030602030912040801050f0105031506040b010210110a0e091902031003050a03120e0706020c 76
    0x1690002c0080d80002d60004c41c00418450741d400705015841c0c0c0104030400300550b45084c13040c00781c586854007994503070040350b041e190030206428002e1441e00b0420014105000702800a116500c2013010680402c0716802c0e01a10070344076140c4640d20940700721898000c0401090206022010840001c000c1c84504805030002410245c40c1512484141b0b002c400107600840f003012010500b8441543c06014024504c1d983c0c003040d5086103446904001c50100d02e100107000d440d4004080359070004c1c1884a605856000c043e07099903140e907019183d00130002201d401c180c0529200000c1114603000c07403c0110040e88040011440e29900708220080c40d02c00d0041c1d05511411513800c16095090003040d41541844592070340741c419408014102d15414280588201218002c1100c0c0190300f41c01c090791046100001070701e80d40e07000c1c44000d4800303c50300b024010340b043c02444401c06900024282c00c206001000388010025090a907550b616a4041c450260f007040c2c10300451070825078201e2088 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 888390602 1250 888389352 888389357
    0xa150b1215060706091103010e030d0203070c0b101d090d27060206182a0103020d020313210f05130b2709010e0a0f0e060703090614040b1303 62
    0x220441d840009840d540101e030f0032070f1201d403100760b0032084c054000b68800d24100194006c0c0040030007a40d48688a110f030201c0003091030303404070200b03c9462060b0240200c082d8820070380d080740d00b42403c60001441c068440d4000c01d0b01d00d9501d014a80840018150180e40031100414081c40d21220950302d114424100c51a261041256080411701c1c190820008004580142c0b00e0340c18800a03046101d00c00d803c2840086e03010142c090000d1034000d50340e1000c20803130000b8050038241400101e010780f089611041400d4000f1061189414071118100600c0d481441403828850711480c3e460940030f01d540500d0082a1551030801031a401240100700010341c044c0e031102034641300c24858146411200c94400465000c1001d060600410111181202c4040340c01c01c480390b162002c52030440c4002041da141440d2030350750140081070380ba081060108020750039100c445c0786c04400100101403081c4166155410440d40302654030541e0b804a0155030040340b00d03840c0d9580d4403010303400744030540c204408 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 888391852 1250 888390602 888390631
    0x4020418050d0f02011b020601210f060e0613080306060705030d06080c090702010614060c0f070603022101050a0b070804030b15040516020d1b15050a150b12 69
    0x1e80c02e0021403010052900c440502d071108620080c00c4400a2044001c40080401080540c2d47c00085503811107410a40d80c0002c203500b20101d15103503420000003003079280069960001c100103600300c4981d016007141120079654500821220800c00c1c14005498100200b01050180c10326000619900e8040c00407a031500e90b000504508980e500d41c07002c0703556002400904444d1900094254100a15200910000341812400d000b0104001183c600c28a40020540c0c400300050205014911881c415110000d03a5a50041c02950000c40340c198881c50039800321400c1d811070004a81a03030707005015107020364241264105154459201902c4804d02480300100146010b2100381c8103d600b200c0030150300c00c19200b030109540018200c22445060000041e6506600041c4010812400c0c502810025020311110000c054a1031020b4041c018003110f101014986400c00303801079010042c100030b82800345508480b00b4480d4012440e903041c1c100005552604260221500101e40c1c0000c0364 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 888393102 1250 888391852 888391901
    0x60f03150a1a091603051e040b150105030405060703050415050709090c03060812090d0c06030c02010515010f140c191b030201020304090908090a080a0b010503070501020a060207060e0708070801180308040204 91
    0x2d18800108e9044a060103104104900ca02d00c60410010004081c00e010b411400d007a40e0f03464894200418120426560f070000a05001503c5502c3c0041031a0800c20840b134108808001e04144080c01081401070402105451441c80b0f4030a240848007241c02500c2092543c1e801e501882c0d00100c500d65000700710403c0d403404a40040c0d40d0b0300060440c2c0c0c0380000c040004a50180c00d680c0010066951a2025191015a039070480d0286680c0103013841c120b0500c1d0328803250b04903140249041290b25101c1e0700d5050004500018030580c0d650300850b0f95004807099040742014116803030100030f0041c4c20520040080d02134a8019074100d5201e5100b1382d04091000c030102d588070000c2e5215030400d80c00701c0e290400780f010051710940540019000b8010940c14800081e42e01c141c4e0b0000280503030f60014424040c06800c0d4010303100c00c06500251030034682c1e201251980c45c0441e0180f0040b80d40303003c2d540b0301030019460041d841d40d039144c2c549100d02d0765981c00300401000d451642c14a81d80e0040d6002c07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 888394352 1250 888393102 888393151
    0x60412110f120f190b060904050a0c1e0e010609120804050301050f04060f05090d2109261204020d0201050c070b04170c0603060f03150a1a09160305 65
    0x46000e080c240c003c10200810280c8189480608080c0d10703042841e1485950200b412034140c15413040c0155005031903612240b42c070307518040d120340001e0054090a9030201d0700c0d2004400860045070002500c52070192149500c2c00350340030a00c58a00031407460300301040143c81e142d04000b8080d00030000a801d150b40c690109094071070884c4d036807440c0c0b4008000c101c108203952003400380848403020104081d142c040300017641c48042a00c1c41d01030002d125082c881030142d0007030f158403945441c1000d1001d00382c0c6142000e08030728104140351913031201c040c0c1c06041c1c100c90006e0700c01d03054010001075065120b035000c1c8852507240342c80c142e041000802002950300002c001ca6001026002c0b002c40e900c0f49488003001d0140e0b4504030b103001e2604180007208265991700e0540740c01040450341980000c0c40c03200001c0c900540c0140041140608004100300b1400d5640448000d104194944501e80310410402404102c00c40341c0f900c4145907003589011881c1310781e00055100c0da004021261542507151003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 888395602 1250 888394352 888394369
    0x25111b0d051b122113080a0b06091f120804091503111206060402090301140114030c010c03050d1e090c15080f041407030b18010b060412110f 62
    0xc5454000798050100d01410803600783d80103400c039003001d0329410310a0b004110000b40030550003229960042401025561022900001003004600321108210b280c5803580c00f8110442d81248200d22050024001c0e400000340034860f440044903016100d0704241d8010140c1154100c1681c030080240070100350600e442c41100e294168038100c0c0c60000340f40d0300e0041e0311102119041030152400e0310840f014240000303101c81c0c100070100da001da1105443c0000c240180312a0171106c4206201c0000050b1000c3d11000c049100e2400b901680c40010b170481c019a850074480d400140024002c120400b40306105500030054028140703510400941a03c024400380c4100313100a9400d0744c4904010080d103120804883c0e640306242c10034490301c0c500084d052000d61402400540380150080319038266840c00c0c4803110103107034000d1080e01d4a0070600c00ca0303c00507000340f500c4000c0d5860f20380d200420345001c3c02900c0856204580c442c10300d281c155234824400c00c0d803100c815000407000b903e40c203555507400f00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 888396852 1250 888395602 888395623
    0x605071505070809060106020d050d0e0a050d09172a030a0b070f030501081204151817010f0506031905010e0a0819030519111225111b0d05 61
    0x103c0d540306044c484020341c1040e5042c0d01903030555200c1c18280c201207803c401a504118801c0d0000250031070024130050030860960304c028a0340c0125038000c042107400004103000d403100480d0412074801880c103100d40d074001518411902c0050390b10440c420711180100d81400d02030143c10b450002081e9079039155507440070782d071000100f107845008483c02a454440c0d140140750000017410604000030200781944510301850780c490034120160700540c1d0081e020101303003260003880c8003803c542d2016105102c0c0c6550070b040340c0c25402d0403500790301042140581c03405000014041c007030144502c075100d1203036601082d084403107548400d00b120000700281701d444610350040c4001641e801d201d03074800c010300300d08180990034503241000b072040808801104003141c680710840020608070301c000070041e502440030b41180500c9448100b016503040c40c081045600041b800c00400141d00e6442501c103030560108035900c0380e0150300e00b80d074121041c2c0880c8900c40b034050400315454886440e0716082203048803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 888398102 1250 888396852 888396857
    0x506010c02040c021c08040f0f140303190e0607022a030f010c03050f1312030612051b0a03080f0f0c03030403020a110609090a05060f2d01030213060507150507 70
    0x4059881e80344d004260f041443c2e440c6c2149a403605a440440f40c1c415014040c0600e5000880c080401101c4248450119800e10032030b44c40f454001210311100104d03400c03018a00e8148940300c41d13030000000d8800e0103140560003030f00f9688856440300e210300b00340341500ca0180c0900002a161500d0a01c100b44211007600000318a02c90103260250a403103002d4008000240300c07604001941014a041d44402544610b010803500c21150b4214050b241c160000a0b09640d08801501000b40002d40803044401541d44e2445504030403003040740f65441c03403101410310360040101d0125400088000e00103e1041c0380100d05000800051500c1c5800c00ca8007100582e10544201d4103118508600c00c1142c141114800d28100300107000c60f545410140044100c10344445c0410007685c0d84050045045001502c0600ea001d410380400c0c0a2807418180d90000c40c0001c44a0200c070b520034002c5a201c090441c1461a901d03261890803911640b280d82c01740c070412a10f21685140002d28060540035030380c184d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 888399352 1250 888398102 888398113
    0x1b050109020910060c030807121a09160c080903010207060c09030501050c0a0c0b0601020c2d030303010311060d09020d0606030201120e06061012020d02030702100b01050d0506010c02040c02 83
    0x784180406800b0152440e080032244010812a195004d03400c88a8a60b0524100a15031100201620300b8141507102c403020744e003080c01d90041040e602c800542942d0049035104040d0700c4041d8003800c0d403a103505c0c00c0c00008804e10143c0300420750b000001c180c01d00c3e015000520b03040340b5890b00da0844402c0d0854400040400404005101c002d015190300800901c0c07407140f401d4028080580f8662882074020001941e140c0002d030746a000b404140c0910001401d0082c40b080206400c0302400d4100040c1c0d04440c408406040c0c41d8100041602d060b0390740030200702c01c900084803c06c080d0390040030200c02d015441c1c0c44d10200585034068000c0c0c4030f510414000c07508500314400506850086030214044501e002d0001d4000c000c002384251b0442c40c01e80310701c1103803c900034086942d80b40c00318401c13401724000104a10079030a6503000b0f5100703482590a03200c1d0018426945403c4d19501001e05001032410b200280400305682c0c8441d41115050420400407146540860241ca02003d06c400258102 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 888400602 1250 888399352 888399371
    0x605010909020405010f0e03031e0c010617060a27050c0108010b091e150f040504061a030a0c0504120c030c4103160609060c1a071b0501 60
    0x4031000041c107451002941003c0c1400c000070102020b800f0300d00200000c0c3c1d840e4400340e0310148121543c294101002c109440f021058582c0a5400b078120f10020f58039040c1d000406119001c100078241b10390f03c000e001a62606240301d0080c240b0b0074946841d0351501c90061a07a090801400070000d482031002c1d101c080a81e000141c291103051f1f03c06000201c0400110542e5521010326680000c2e65180a00f903d52225003c60903200d545250346010796000a0400d9a10103200f010300111a8129003e109a64941580c1c1d520400103030840070741c070042480440e141003410341000c00518254900306007010f550b8150406c00d02001601916815445801031041c400041101c1c0c001e441100038074030681020504c40c84034030580440301d01c141d00c0069203044500a10303610100300d4080003002c5801000400e404010301c4a01d502ca81008200903607000140d150051410801c0b03982c01c00842e00702c00b40803500f000d000c10b000400001c2080049041156007140c3d00c0061803509000d1000083e56164 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 888401852 1250 888400602 888400607
    0x10080601080a0b0a111e0405030d09030611070317090a020612070f080702120c07030c0b0307020106050f0d0f020a030501022d0f090d031202040b03093913020c01060501 74
    0x100078001d804e0540c20300440d0702860032031200712501244150558103d902c4480d80030005406181c00c00d80d458012901c2807181c044e404000c40c030503603008902c2041245c88040c0341d440140318000c001000310f4136000c1c2020072414818003195004c00c1c5002038450700c1c04a9400100603134081d81c0301d52582c0e02108180310f90b071544512030b120010500d082c1020b090030520400b81d03440c0f500740e00381000154000b0b81e07441b084d2010300c404001154040507614200d6121610360310f241c1c000326180c00042d880c0003000905440c140784a1154000f000d0002c0f540314040e625401c2401c1081082a600150051000400240244010140c000e440c04801c0385003000301c080d8003113052507000c0720316030881c082c48100020034410040b20b0b0030f90301c111005807020b182c41c9401d45003600c2c4490300410040c40414002508014400158824075043d000da034034080301d030032403190080c003004c859010918480c1941d0020300000c00c103c0e502c2c0c01005051100514603100401d0aa0340000ea260403903946425040102d0358 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 888403102 1250 888401852 888401873
    0xf060c081f0605091207050411070b070509010e0f12100510050a032d05030d0614010302030f012607121101020f1009020a0b07050109110414060910080601080a 70
    0x145201620301c0d14a14080303000b07000d80110042c40e44110000d400702c0c012544200079100c001d1001820a004114040500305101c0d04104801d568000b0204009801140b2034000c8910803503050f150072115034101d0040c01016840700032002c3e040481c00414401001b0200050f0f04041040c4c50007140504e01400804222400d581c0158081c1e034000744240001030034451004440f0b1540d1540083e545d000ca070004001400400002d482c90000046c00d511102007900032900361001444003601c21401007004500701c2c40210b402d402c42c0d602d6000144060003462015038002040a0b1001980b4601040507a0620009501ca8155a0141c21040f402c2000001200c45284024000b504099601e204140d0721a422044640625681c50b40342001315511011860050121101c40b59100c0442c3c1c989240240880e50095038a00381d400e0b02c120803480c03c0e008081a400d06c3e140d40c1e208584034401130080c0070b4005400d1145c65186410003082c40c0400704291402010305100500b0961074034146080b141 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 888404352 1250 888403102 888403141
    0x1909060605092e0302150a0207050a0305030d110406120c02031b100f0b01091a040e070f090801112b181403120f040507031e020a120308040308040f060c08 68
    0x2107a2502c81000946e44d07510080031000d69001080e941d40c00840400c07424401e41781c008030352241001c1000b01c18828008041d000031030101d0000c00001801810f006910300451040c003001072440045950b407031107181c104c4007860005004a03814010201e20800d00451211445101035004221442c0b0704400303401003a8030002066420803400031a0320000f4030b0740c101070045640c40341d102c945040801c10008125030082160440d072080341e080c8000c0003080c0c6240d00302c0075000100e1500c1c003c220600f06100b203501c40b0401c9480c1d9450105c510750b00a40710002407600032210380d0348221008a440c51802009080e40c401c1c3c01c8003881018610f40580b46c840201c00b01001c40d17009002981c3d100300c964506640010500901c211640d03201c0c84c1203407030681a0740008060366041c4032714074028a5082003c18580e0310031181564202d40715074201d1207000256002500084040c0089008280190040c5400a0054030b440450f044943c42e907d09075a401a1180d001030103000410144010741441ca40c2c40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 888405602 1250 888404352 888404431
    0x20a020a020f0a0f03021009080109080a1706210304030c090209180c030403030f0b03010e0106051008090304050d02030a121d090609040b06040b15090406060503190906060509 77
    0x4460030f03c0c0050316284c01d02e0200a008251206440c000c141c0943e10601c000d080d03001c02403007424074a20b803000302d50708142c01100102d0300c80c1482c4006600c451603018400c00c40a01041d000262201001b015003c0c0da0040080f1808108004400b1404400c41036000d40384946c005a615040a0240002100742448404404031030707005018011120b04103d0303400c04c0d010310b030104030403000300d94080003025040d00c01030307240d840c4c90080c000e40001904108220b4200320b98480035144216425951400101c510a441d43c00c2000240030038507000340c441d508640041c00701d50510b1800e03a0740e42540005602104c2c04a1000c400c203d8000282000b1f41c80501d2065039008075906059001c00c44004010b04010071405120001a415840710b40c842070ba808030007004612100004001c5800c07070343c030141c40c20b801581841c0010a44a000b4400c032401504800201440c00f120000e1880c0142a200c0c4120b4410382c407044001003d541d03202d240b1340203401c1c2c2c2c40088120f002d111401c2c400c0c0d44e42030440001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 888406852 1250 888405602 888405619
    0x415030b1008130f05070e182a0607060c0306050402091804140a0809040506061207200d08040b0609250309060615030e07060c0308090c09010e1503010b0d150f020a020a020f 76
    0x130000c08a140000d00000182d1041c0c0d00e449c1c024003400003900c0180154001c00b01141c49410b104490300104503240c2c850304e0030040d66441c0c6044c88140c0c0b04042010f40c21402d00641d040030310240c20075003640070b80613000081044841050a40c20519098030549000c140030a50045610300380c071885402181c116a002d20380f803030000c0c25030b90200000b00ac550500103001540506901c10001c400030900800040c0c40149081c1c03032000d071850206a40c107445825006c0c0010710700e420010319807030085041d1100c034003080c100080b0f02c810065184400f2000c15494168001c0055141e01480002d4002c1188a03003003454285001801c840d040711040c01107034480b64041001303507003244504ca200398152600384210740c1d0300c0700843d11b41014000e6164100326840d00008c0c00e550360703064040c005c00404494100002c0d186040509035091a05015804800f01c0c1c51030000070180140005100d2070300401190f480703411341c0703c18200c1e044101220302603080840038104501c1c090000b003003400c004640c03581 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 888408102 1250 888406852 888406891
    0x71406060a0b2d0a08060d113604030816080712090819080a0209030d0f0e0d0302060a0e06010f0b091201050c0415030b1008130f05070e 60
    0x242903541a2181c81206500003444002040081031401c004030300b990340300502c0c2c40f40500046110352060f40c0140c000307100013000c540c0c43d2a040c04071001241e00015001c0070710300b500c020091440d107443d552013207603085084000002801c002022040103944507080c030840c40e1609000c1d0000000030000000b4075511010042c00c26001510250085103500e0002c00803003000d2080c600410907a00f0143c541c54002c10380c04441324145c00c50340f000700c0c1c890340e07400074585429100800341d009501c05194140c000c600c96101140c411062090789580c0c074602500c0042038000401d03035800102038180c00680001c010801d1248281c000d915050003007070010172040d0f01d4104d01d07449450b240d0244500015001902066035a58000c3c44004030050400820160801d0180100c2c25031203403003030a0b11700703c01c90380701800280280b00760b01401708080e000c4032010501d00804c40d10f000c0c0080c0103e61901e035801801020440c015100d0800a00c10001445410304000d8005a8080018400c0c1000b44d50500081c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 888409352 1250 888408102 888408109
    0x51602060f1906090f0b060a0203030411011412011517010e131b08010f090b0a050901060803040905060301060819031805060f07120216030b10030506070507140606 72
    0x96500800d441c4000030310b5100c1102c0e1011002c401015585000d00300000490703c00000d6100070341c01000301408021350b5101784203120090050380c1c0d524016820500021317002c6541400700c8000a50140352109182c0c01c0140f403c2c0340c9801a0340c0d0301c1c0f085900c0b44014405062120300070110169981002000c4a100300c09150280c031050007501c441d8400c0c1000300360241d0a501451001c9944030115540c01c190034080e0b01020b910b148640c117440d608001c0000e0340c0c000308e071003500241a04050208150f0f5a05141c032805070801501401c0c1c0c640d41c0b100f000030b030b8503402d1010700b002e402d4615011445050080401d1300352480c913004000150850031040100d501c50082d603844a50741401c0c46070104900882c40400e100b030941c02a1b400140c0002d841c10485400030040c200c0740e2044802c507410741c013211000c0b83d03201c1001042d460403064265003032001c01c6081442650150152141c60496a10b039980c2d68200082640c080000c01c60101c8c4000030400203490048909905034001d00c010300d0300304d000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 888410602 1250 888409352 888409363
    0x91a060d080f070c0303081522200315040b040b0102031608040905040305040815090c0d0f020a090e0f24070e19080c0301050c0a050c1609050a051602 66
    0x2004900e0000d008020380b0716840640744030541140400c4083ca80d64100500a00c0302160020a4207002d54040b412601d05031460007807401540030010300f03e404030301c0c2c0c034402400d4407407110508800ea048860340c800c9a01303000b1442406041240b280d80194001440f055a6000c507005120b54140511042980da00000340e0354030710383c952407084c00901c1905124159101e1500410426070408042100381034109008204581e1032108581017950015106108203c055039020416000000224a0340c0f5010036059511401000e44500808050740042c00368621580304213041501c0315004288483d007407040700d00c5440000050702d103d040d04003143c9002050090514003545050020a9a0714801e054840c0d0460029280c010001e071100c03495a50251207205800d180d115400c0c01000ca81018003885004034010101346041c00001a026183c0c0d40102c0100445840b40d0024001203d411420020040400c040005002d081200100701074800c010b01d103652050303c00200c03422a43d4006903 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 888411852 1250 888410602 888410629
    0x1034206170c100909110418020a02070e0a110c06070201110705100906020c011a0f01020726010e060c0c06070c030e1203160c090b0904050703060507020a15091a06 72
    0x442200800d8030f4001614041c400c0c0c0c20035241d5a291968050324082904018400d645071242d81042c0320300200503501c180d1103041014401a00580400c002c3c0c204003115982d042001e81c000070500c3d00a00c40c0d03000f140d030080e010048069000780c042c408955021301c103c1040c48011108180b070120151951a40c83c084021009140f55840c018001400496030540705035405180003031019170541e503900304c11001e8034030380c892240e25080340342c2d0429800020361800300d41c10300c5080741c2c503c603440b41111011489071050b0300482d500c910b4220315241d400e0085a00c03841c002d504407074880f01c03420700480c41d0204c002c001c81c080c42040c0d680000400e40220410741241011900c2108001840c0c0405056001c0d9456214100300141018006c108c2661140000c0d101403000c100101d401003810015510b00541d0047e0260b00b20710300900100e0a1904600da00c5040350041307450189080c1d940a02c98a1004d0040003100d548180c524104907035640710700c2519038001001007841c1070100000304004441030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 888413102 1250 888411852 888411859
    0xc050f0304030e0d050303071206140402031f0605040305010501140f0f0d060c050919060c03230f030411090106050a0c030c02090c03010609080d050301034206170c 72
    0x41c1014440d50641c000484041c00700c90700d1036814a0150350b281c005840d01d03004145030402d00801c001300b9101d4442140d03800b440001031800328a06020003544090060f02d01c0001301c002600003000c038910b08a0003014240d56840d0303143d1031800e05608450042c1c01413060294104000655507880000001081101f110030070211140d12001031034489a9920013004181090710408505411001404182a06850018400804142c02d40641303025019040110f00c0140b00d01000ca072003800d07803030369445008500c2d101e2070704042c2c03080d046a00300700152020030000204110800032042d138090403910082e1080590365051040141081c046e5203c160100107841f18070809040c482e00e00a0030702500908401030781c0c18140101e80496009004450200c3c50001d1300080d0400006910302580304260f940c0c90035030f401c50f0b9071480020342d034681c41e4500046c2d0300141082011007070200c0c019000c0e00403840910344055602e480544209901490079240c140045141d02000803070b09080130034044 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 888414352 1250 888413102 888413107
    0x80f150913140708010b0108010e071404030b040b06010323010302130605060d1506020a1145070e01080c0c120408210702130e01020c0307240c050f 65
    0x1d04030091129000005055111204120411114040f0b074501c00e07038100000a108039202c90006496880c001e1003401403030060107001a040c02d1050b2054003040da0b900b0ba80720302d0650350340c40f443c06c10720091714181d510340b5100c42448169030705481020f850513400030f041d5048440d00c4010329030b90201440041d02400244e0b07520100ca6015500600103404020451600c83c080f511442c1c0042a9900754110010b04081c0c3c0801d0381070002404d9a18030f90300102c030301310030a103800520038480f007038005d20740d01031400010318104010441807109205410400900b8108803440c8111444480a410f44041c48519003038145240d07480071110383d00c01c0107040000d0307641c1010440345291020410002402c1070b000309001c15074402c00300d50488000640c490301004d2040d000c40c00090b6126610000b58080c600c045c010f042c0f0040f40d0840b50b00d01303c1c6d05000505000b44e22180c24150360140c14221030b290304049072407040904107280c0490890000c18100802c000b01100503190b881110351508251002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 888415602 1250 888414352 888414361
    0x9110a0f0306050411070c090b090a0c180e1510050d02031f03140c0919181e0b010b0f0405280f09050604110307031107080c060106080f1509 62
    0xc0c2c10071070003080054810031030042245007514454020900484140248140c0010603041034010200030040c014000e51007500c4100139a0001c00750f080000041c858445002001c10700c04c0c608c40c900030840408151110b01e48441d6400c0c3c0c0107211503002e0705c103210a06100d2031055000041d40d00c800c0c550300005035642c40d83e103188201030400e004804070030b645208010040000403021a000103202c1000c641422003520200030121404480444074510f03000c0403a00400c64a0b00007403801e84495103c0a600e42d0350341c45981c1c48400030062400b0ba0200000a602004480d40c0c9503401002007603405418001c0a0550741050b2195101d168880c8804001141e68103c514180c555000700a400e41d440341540c3d03408420747c0101e00e100b400340e00d40c90440010f000c0d09190086032111401030120303916565400e003040d001402064541c601001c2d040c0903580002c0c0d400801030183c5c22001d00104a0780d03141403402001c003200140004041d0303198405011001158500d0940c40020444840083d40d49 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 888416852 1250 888415602 888415607
    0x50d1d0d0b0a0213170a030f020f030f1b100606110105010f09111215010f020c0306010314031b16330e03030a080402210c060a051b03031009110a0f 65
    0xc0b180c110081c208178925800c46440710005804189a100742c80700c1d010306081d201c00340d07107882c107417808210140c0041041103519031a860041025003040ca507071004000f00c0b02d5a0600d41550610440c00c1c569032a0814800c1c66003201c0340d5200c3c0c0b0b5401c8000d2001d50305000c5401807900c0300d440307400d810940351060f07e181c5440117001d03240d140d2000f00c01f6100e21315003101c1d00401c150f000ea9015011440081c140802c00f403010a600207501c8020300105182c1e483c1d0355a000995001e03040581321400240040c000f4086c08007000c4990200b80c8000302884c0d080000110341c10403c990040b1381c03803140420034900040e6400c07009100b0f00da20310f103000d07000160b01100b6681c940d045a0b1055050000141c550103054014410501850003516103841c24a012600307150352070015810810b00c0d60002c8403e140c1440e10710010410034440e0b1400c03604101e412106614543d100205440b90340d04003100300840c0614890180d002018090400e2080702400350514045120b120f26540c10041c41c03002e44c084460 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 888418102 1250 888416852 888416887
    0x201050909040303140112080702133c023f18010b01050a020c09090a06060308190c080f03040201090b1c110406140c0a050d1d0d0b0a02 60
    0x500944010300360b00d480c0c80c0040051104101e90b0a030070a541e070010449145050420510171b43c4290301500e0025941c08000482c1034903c8021340d0309803585075990b6242c5a980c014000d496021909031044d05585880c15640c03001e182030400b807580b05015140e0308082d03000e0010807051120b262000034805100940581e600701300b50716001c207203281c1e080c0015521511070055a1141b2100200507440440004640c24420000303400010303405a01c0201c80c038a000b0f401284c00a990004440080c03000e80d84800c2607a20079401554400c0c0081a6004401c4010000045140d520702d09012001e40559402c04140034507509208000008400907045901962426001e4000c041d400d584800c0303112074001052181d8144604110309100780c0c40d081c0801070b0162015036a2a8890300c078600f14080c4d0750a810f0b001404c0644443c800d40143d400804c01c1401300c1240150700755138560200040c1e1445400d00d90038070840d68000d85030794881101040d810034040350000d17001080036a480c0d1b1001505070109 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 888419352 1250 888418102 888418117
    0x7021005010b0c01050a06230a080a21051321050f03040f0621180803041a090d0206070f09181d060c09060904020d0e07030615120609020105 62
    0x1403400002050902100d000b6011005042d8002d101a0356a1010b442c241c60440c0304e1119003141e003d4040351007550300105904240d001400f074218040da036486140c581864408299010107001c3c41009002405030980c280313035052814800e1802c42000c2500003c6200c5216175000b4040030034500500c42c0b803980c0301540036900241100d0046550070310780d40d2a98003911401d10603048c4500009200d6008000d104030464a400f00003a804400d881e40790082c01414003411600c400c600c107a0000500b001000e14043c0e0f01a07038400720190180c42c0301c9054150b024121103020761207a101002001c1e800581c065100070b1926210001000110040d641e5101540150040a01c601c4044d00092540d80c0440c0b0404900502826034034500c0b800d264a408094640d54203040040000000c1c0b81000e1005041c0810090b000528003064403000004075805203010030040d8101c45801c000b0300115004480b8a0382824804260300c903d441c1001d81003030302d03030360000b0a40380e2160b5181c0156030085003504c551 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 888420602 1250 888419352 888419383
    0xe091606080a0218060a170a062d18051005041404031d0d081e0703020d0c0c0e0a051b0c0d1419090612050f06041503022701050d1106030702 62
    0xb0f0b048486000340609003214900d500089005000410070108c40c000d8800b20390450300c0c0050045007281d03094844c1200c1081c0d0701520212079600203040a02895818543c5080150004880c2411444c080e410007656016510460500000070844115a541c1c150090350504168600d0180051807050400d0340400c0c82c0d50001e4400c06c0345d400d00c103c0c0b00003080c0222560018442d0006660601540f80c051a40007900680c030054000c00d90600035041840180d000780300c0500c50716665001411200c10440c9c210030285d44a80034004251030381144400c2d40100c0500d002e00b001801400b0139a034810200304a81003084111000c1b6400d0035120440385180790300520288902c808a00c007134081c46841c880c6400042403418078510400451182034019010409042d8894858200b00400341a040509400d4038a4402c400401a0b460040305049644854031102c1f4440c14003500d4160442e05910144c003070002c4409600c001a50030700d102c46155012079155072252181c2200300d10302507035400080070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 888421852 1250 888420602 888420607
    0x5060d060801051b1b0304030f060f0c080115031e020a020d0809121606180308010611031201090c02070e0f01031709011d01030e06010e091606080a021806 68
    0x11040515009003003074810a5000f480161520a02c021180c0302c500c00d041031200d130610a0264010b040b6214004206554040700d0500d910303901c0f2881d060102400803550640d580c01203503e0380703249002e1264000005c3c20142000d41c580505003600ca01130800110415642d507040002c80b8061902080300c1ca60309000c1151104040700c40695591030860f91040494071a00014106000c0055030b0380010ba00004402d007824403010035004150042c81040356903580317443e0000c0c441d103000307015081d2031b47c0645c0c0e500144e03515094000d000e510480c58404079a820030001c440d0440f0000c10214110381c2582400107040356050700490031720f1aa50803074230219241006126402005c0d0300d01c141600e000e003020200210b002d211079200351040c8420140071881c0d080e0303009042a901107210460714010b040c08142c0c081030400c40e0303042c20800d80120051403510414040e03000400c000100501054010541d0f1650811901034581840248102841d80d000600b515030040c0740c612804106038060300c0b194 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 888423102 1250 888421852 888421867
    0x509010f020c0a0b0606161e29090a0803061c02030a05030304021905010c0b0714040801051509060307090216061e1a1003020f04051f030b0102160b090a0506 69
    0x740c698124007404e90380d00010a011841c1444c200040b0340d0381c45c2030018140b861003907030342d910f480c26024842c518601405045149000c900102103894840c2c1ca18040d14245060161011a590f040070302403294a601400400c1c0004030720504503500244200e8080c110505030481803426a42480300007501805015211020440c0000103580070703502c200c032108111881c2c1045912405c0302ca220702400601004003140100714002003654201590f0720300324180c0340640c0310b000f040d40d03c50b40c0000016035460042041c56001000711a4804000311150289420304600203aa01c03690344c02400e10f503d40c00070b149843e08050360b200307050301350b030094007030254207604101c92911404800720b4908640c00c041c050f225260921507081c080b040010720718002c4055080b001c4000b900310b07042d203110008040101280c2c85d0b49500b507820f140010b19805542010703400400400b91102e0000d4035055501804920315001d81c04c0d040441a42c000390b02081d01e4080c1e0f04001080e11000e944442d17003002c40050001d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 888424352 1250 888423102 888423127
    0x120312110f0304060c050310090504020f190509010807032102030904060b040e0f04030f031d0a08070311030301061421040b100b0705030306040b030a050601080d0f0305040c090509010f02 82
    0x6500c501c4c0140310030041e030402d9481c180e0390b13480f0440d907040802c85070300d0041c8401d000681c0590341180c0041c0c00ca0700f49040c1e450100b24070160002548080254074002003045241201140e03014011001c05414204d103559150000c1440380c1c4500c9d243c0001021602c802c083c420415a030b108440200103008444d9503020080c516803282c012130003401030400000788003403a148086c40c001d940c10b544000140e0b072001003c5004180c80740c0c1040095030803640d0ba64562070100440c044a50240c580c00c2e40e510a00c0c42d0140201807810324402184d003091004100158000c03012061049200c40107641d40c850080100e4840c410040741741859400c0007083c00700344032442c000544a201307100610340c41e903038030303804550101e000355000100343c1d900c2000040c01c0d900f81600410003148000c0d00b110b401d14855074031941002800d810404441e0302150704030f420b103603011005503d404c805050401150815890712502907080c0e0195603101a00c1d1404140c600740700750700440418800000071500c1d5500164030b07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 888425602 1250 888424352 888424357
    0x1d210f04032f1e0609090108030309010c08070e10111903320c120307020c0405070807022d070f090c03020306060d09020609130507090807120312110f 66
    0x86000744039904080c0c040c4005200000d1000480081181c00c2d141d0103550582082e810003e1441e4110109001c40011502e4915416004e00301c940051512403a19000c00c60844030081ca03480c0401c40301800344012590441107aa4003036030700750b9410f841c02c90a0881aa40e0019126507550300d1301c13500f051044400c080c0018090907910983d60b10b40c06006001c0901c1c50116181c150350412040b20b01c860401070282e00050080d00c080d441a58140d00c00004a0010380d0000c40d81040503030410320f40d0744c203185000c2c803901380d2000582c1024501424400b00096440c51200010074001e410054555018115400501da141d09a0012121001d86894a1b40a1000d03917200711100c0d24200a01d942209000b03001ba84d100f80b1000d130a0f40d00700480080d60102800e11400c06903045402040744000d2034030b03801440b0007100d0b15808042590705100200401032411075000c10415001752500780900c52140050384000383c4c0600d08403141140440c025801080e00046040c0019400140403400300c440c00702 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 888426852 1250 888425602 888425633
    0x705010b0909010e15060f091014060406050a08130b07170907150f09150302070209070c0203060a091106030a0e070b131503090b010b0d1d210f0403 65
    0x10400c4042e294a1003581c203071900c51000c901180c0000680382c1d941c00117502c1d901c1d80b2200051104078444c01c807801207003440400303482d080680b1200707400c14049650907047c000e19011042c1c645a145c280f4240009200307001c1c5040c00010091800d012681001c0c2e01881e01c1001904544030f40005d04203510051b000c5181d00000607444034002c40015130103a80400e4600484245003542c46003007000325801c50303030b401240b2065001d1085007000402c0340d4195000c0c44002c0c61460310016a102c2043c010414240002041c0c50104418201c0420058502050302508141c16140104502d989841c00102c1240c0ca01e4407140c0019001c01081404460b541000141c99404000e9414451321420030740c0852060350308460011407401d00401404000414035110343d03040f4a00001c4500d0303969500c02001304e007a0700040000c100414140b60a00b00b41c8114001c806845108991000e17607121500e0304c3e00d140c0720050042c61202c5002402400d10141104c16060008024a544035241e24044411444006 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 888428102 1250 888426852 888426859
    0x3050c1e1506100e060f1201030c140d02060d181505011d010b0a12021602090106020115120c0806070507050606010f0804140709022106040204030c030b1b0705010b 72
    0x30008102001c540c0e99207004500280c50035410100a00040e1246443e4000e0203400c1401005418042054013002d048440b4040f45880600c0d495400c00d001d00c10351fa90000c81100070711140a2185544003085603600540c140ea106844e4840910064001c0c1030481580100c2c1103000c40c424100215040d240c4001c9003001c004004907600c0341405404d20b00300c1c09000e86060007240050120565000240a45040518003078150304150142d050980c1c00c2410440d11080c0402c0e008011031422081c03c0c1c2c09081544000c20401c00d00c1d000640140e010f070b200f125001090400c01034180090f11500030003908000b4211801d905200d10010800c0c3c0c030404003550540103840c04100c00350700c11540d04a0064003940c1e160810703100c6482d80e10480102248004003403058082c00101ea040c4c0e800540100d0340220503444003181c00c001b010540c03c1d0003c0403180304034810001032000032074a410709420ba0360000300300140e99540c4034040003c03d0313004800590281c0c01151341402c00a05400c400d54121098 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 888429352 1250 888428102 888428113
    0x6160203131e0824040501021312021206090a020105090307050405181605011e0314091f050103082d04090209010314310f0b070f0c120c03050c1e 64
    0x20000c0d44d480d007600014802e00b002d03410070400303482100c0e8082d80303400c11700490005203082661031403902241d52a601c0781c030110000115441c2549014481040100c0b4440007404461506800c05a151007a0910090501c500441c8400c0a61030410800010b460054410002c60400e142c0c40311504c020008100120f101d40d001070381030000401c114500700c90040c0c503040d844150740e41305212000030140c50081055a034800ca00015910b81c105076009424450103001c3e0509088200800307003c0b24000e0a406074100001040040c040303404584009801c0c10910200070f0214002ca03041d051568901c4171900000704003c2166000c0398001c2080b840243c030100710341480c030b8003c80c1c4060012215004c0801d0002c0c032003070340041280c00010140c41c202c8109490104a42c3c0d80408022411000f9252410b154041201458005401c40540071003400c05031007164040c0e56a131000198a01610104100d00d9001404c0600a400351741c0085c09440540320401c1c8113110b983c40310f149040c81c400c8144900c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 888430602 1250 888429352 888429359
    0x221208012405070201030216052509050402060702091e070201062c0a0506010c15061a07120e0d050d030b09060d080435061f0806160203131e 62
    0x240c07484205400761501c8981c148089030300158000e404c010603914000350441012000148107206050416100311442e50340005403504220032074820390883c0341c2292516050002580d2614180d9121640c1151b001c640c5a0340d80c6805814103864442210407100e1600c24020000d4040d040f000c15548142130303030204c000c003410010020440505400e64012040d8010a130071400326002140d0002040c10300c0c649001da00d0f40d07800b2107100703007096600c80c85694000606c903005210b46201d108040e02949242000e0140e240c0381e0051b0039844110043c0a02c2072403041c40c640703643e5400301d5510703081415110300c0b0b14032150180182402056081c03003201e44200003615850310028094800c0d801001c26030600c9d04100010380ca42e084035081c0c08450303410242c5000d1142640c0600c0302c07007141c01c5000d8401c030708100403003884034031042c3d0b18407020044006050054038800640d555010140c1c0041440007246414182d0a5205000b100d22842d0b40e48400420001d900c5941c2d0314510b0410074988480e9130380c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 888431852 1250 888430602 888430649
    0x20102120a1b020f03030f0304050d0e031b010e09010b12070906170c0909130b0901020313021c0c0f05030705060c06310c0302010810050922120801 65
    0x85056440c0428036034401c00c4801860644080c1055101400030032120020134000b910f0764210b0845400340c020000104410042c091040c00d142c0106810109204110300c800203840b040710030340044514030f0580e000a40d41c1c0c410003241107400c102409840702941c5400e51562a54000c0304408031a44900300407841003031103401d42c1000c070f400c56a50500c0f9603010108000001c60054002002c00d03609100783c041c0c540e1858a49405000e240c1014a0400498601a240e004004151194591042c82080743e60032814480185044d03040781e0102c83c0007080c4807100c00b034443c4810050b250481c005030100300d002c12200c2910549100f20115034202d995a07041000c140f0500803040d1840d004007001c11038104800142da014042c442002a545c3d4030742280041c60001c0e07181003070301c3c080c40c11001002503507006040a908204000d00300b1004d02e09010101e00350f01000b4118211070300c0c11100f4180303410744072150510507950000c00103960b080380c1c207c0100082000e000f00241966002e400340520315 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 888433102 1250 888431852 888431857
    0x8150108010819060e011506021519050402121b0f060f18030703050f01050a0c0e0315070302160f0c060203070b070c0804090e10051006081902040f06020a02010212 72
    0x3814500209100705404041d07030f408035000701c030849880e030b02c03030b00e0520861401303000d100c0180247e8070402e4540c17480c0030350003442c141101043d04c1c050300c901c0045c00001c3c180c0d0b18040c16050014000801c90fa10f039071020850100180080c1082c0e4012100c41316144e01340d407911200c2c000800c85a010b111021402000305c2c078490840c2c0448444001c100010080b03080041481108100034180c56032aa07403030f21120300b000018202c04030280d55820130481020320f280704004030061039103045110130f111000800c0e41c0d81d01e15200324035003508060000b9207681c402c0d0102e4494022406141c0ca60f012241742407500b0100d060001c4800301e45c03000300410003a10020940329410f402080742012074544070b0059451399100541921601c0b1300b00000705400503d40100b03184200c4850040c00d05144003403603c6c1c00c8480160045040c00c4070312100300641688412869000710018906d404044603c44801000784070b168403c025949102e5030010306143c01044105171b80303000385c0998142c4480d084006d6001d2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 888434352 1250 888433102 888433109
    0x120f2502040c020721062c01050a0b030a02010e1c05010b0901080f0304030b070c06050f060405010f080a020f0a0302181803130b1309020d0c17010305060f0c190815010801 75
    0x11140800a0f2405c4d0451044000c0b1070790188000168107080c05546000c4680c09280d0348842405a40d0034400c2c00e07009202e03081e8000119501041040144000a6201c02440b01c0290402c41340b4213091081e5507c0d10900081c0d040440b00c850514103042c9002c60181408010703982c802c01c201000000c0207200882c01840065058018500d028123550b00d01c0340d82c1d00007808000c200700e030809000700012803a20441e0f001d000081c0055440b45804030030441511016041072140701966101042140300004042e0b1025604451082c1103070030b4640803078150940d6502c0654031a100c0600d01524000d4000c84c50300640c0c81800105c042c20324540c0303142e924800c18204090f402034203942007000c034040902900304c001a0031845e51010350340740c0d03c0320700383d801a0140080f6039a07908401c070350054110032a07c1803e040790284c00402e41c915110b00d910740800030100800c207012100040c038078000200407140c9101d2150301280c0b004000950060000742c003203480c100e002602200402066000d04400c3d8100e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 888435602 1250 888434352 888434369
    0xf0f0203130b090f0312041e0209010603020f07060609090201080c0f120402010216080d020c030a0b070e06121501080a050f1618031101031d120f2502040c0207 70
    0x401c0116622038511000050a000e500e003da280224440d5100b40000d04441c045c1e00c010840a0800c4c2c117004030700000d0303115901d8070301aa11080d58016140c03c500303141162154100141c4842c00d00001010520900f40000c000070300d40f240115400ea0280d0050700046d0003a80c441e490b681d0b4011003160a48134048510303403420700a001210040304404041c9600c5071041c03041d0b903076800e240070740c143c49904150008030a940001018514060381000b20740701001044004045d1002e0b1034413107842e1000040c0002d020040c600050607402e869000c126061548001507140c41d51070708008103003080ca540f908031400a494400420040700c034a0103014007882000740700c0500da440341e81400c9001d4400c03a01d8581400081441c179043c101c101c1a11100030f602405403d00e2090f0440001412224580c0038003159071011440d4900c1100b001070004650110706070425940c030039007005102c140c050104528590740c1848040180c0d4103105441d4445d2a2080d18203111211041d2405d9885004d98050401d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 888436852 1250 888435602 888435631
    0x605010c1e020a0308070b010311030a0c050904050a0212100c030e0c19080109060617010e06011502160b071a060f011d0603070f0801050306040c0302010507060f0e010f0f0203 77
    0x80301074003a000900c80340d10080005076501e6807603039410b0741c0c0e40101d075094410000d184010000c1c130401c100401c04411081300508200c581c01d9491542d06582402101d0244440800140c2000402c0010360f81441c4c00421994412040b000c2c070a9807003062202c5418420308094080f01da203070090040d941c050780f4000180c9200107000044c40f0f81c040c0d1184000d802c0a540382030004001800b803141d0305500f4010400850664100b6445100580ca001c6904040381c2c0740810503114400c0110b2100c2c103440c048101c2141100d61a00d04a281800708191154646480f440000d0443c0c0c00c2801400c40314030801c0743d01d40001c88910b0020454604a4400703412044408009420350b01c0707040c1201071460341008a0182d01c4011000c0381c115042154400d001c07401c090400032910b900100800c0c0189000c0700204680d1401d60382e0b802c000c000901c4020305100011030250100002904404119001500300300b001c0754003c11300a01030106146d07104282481e03c549440d0314807083c0212031007107101040d02e54 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 888438102 1250 888436852 888436883
    0x303041101080f280f23090303011205011509050619061d030708070807061b050a0308060301020706090309090c080912160501060311040c0e0f10030b090a0f0605010c 73
    0x4811000d4044c0c485000d0011441e85416004a1080c080d01c801016000506500000151046010380003410b000c51203140b8204829250000f04903819964500c000c00391018181c07030a6030240840e100300110300d40c6120b1003c5003200040e4030942c45820102d480d06070140c9410300100400d0941d008580c001842e03a00301401c03844041031019014580035084030600d9940300c100c142840c40c00d810440e04d035000000700f00002a4000050100042148078420103242c055855a5583c000d441005080c81070050014039030390b4080d0b054a000c0c6400c98414000f82200e46001800d400d05070003900c4900380740c03c620440451048021a100c0d260440050a951022182c1900b00390805015030080d890b034040c3c0100014400e005501c0203620558501c0c080c10f0a00e4200415291340601c1d000c100411304c9640358003551408003000c41070710140e40201015404000850141601c2d0b451190400301041c14440d00c0281940400f40750302502200304001500d5000441c1c0c54506031501410020080c0d5446 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 888439352 1250 888438102 888438121
    0x501180501030c0c0c03080c060610050d0b150307020f0d02010e070b070602040308361305041e050a060624120b0919110310030b06040902120303041101080f 69
    0x10b8280c0c02403404d0140910b000380d59001c04007280340c0c1003211000d0000c1038000848400f0848550448801c59080a40f844000c10081c083e0240c0d40cad00140042d19441c030001d45d070701c444013552200d4803c5080580d80746030003003001c1d40e41c0300202c6004080b44611940ba40c551031041c032944c1d20b04a41c0c0310251613410b180c6400002c80f03801a120544010380c0c20080000024010320081060f0401051b98022441a100c92001d00300c207604240410780508030368900e00c59803955942c9003803c99111002a0548850034000700042d4903103510402c0d407081c8030880c024420005402001d05201e00740a219907a19850101958400104190000848556a41100c41c001c00c00001049072100c0001004102000060014002541c0c81000341c44000190710f85c200c0c3c01e00400c1c1000d4400240d80c0c1c0345080c50b041c0c0b04100c94091102419030340303000d000b04070240d07541c0d0003182403e0f400900c3c0d040340b00b802d20034a5499a10555003100c0b9640702c11021076295004c0e012540c400c0c000a0440d402c1a03880c0b0015 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 888440602 1250 888439352 888439361
    0x50c0f150a120c080708010906080c061c2c01061d040c090c030b04060902040608072607200f03161e0803010509070206071407060e070806091207050705010f14030916050118050103 79
    0x10810b1114516110103a007500c01c1c441c0181ea00110754030920040b050030341140c6c1c80ee500d0506903000d6410b0190502078003200c880351521303800703503112443c400c0c2d80c0b40d0902c101c141010750090900030b820300306c840c890154141c1006a1003082110100401c0d0380c0c40d05088202e214a105007008101d1540001d0304080c01a40e84030800900600c869620001c40b800c00c00300302508540b0b0f000030421014101c002c0e1031440311142003110400e8010720760781d098a02c41c19a02c0c041d000317aa000c44e52060515004001c82e05030200c00d00d03158454021503a100764038202c000d642090080c036005011190000d549030303200007140307400341400e070300c400d0700c07201422540003011f901c004000d4800710f0711000046403150301045094014801030b405480c2c0c0e4204142141c1c20402400c0181c61205024400c5074045200450324034126402401c000c41190031000d400e85d55480005c07108100064044100440c40002140390550080500300d80300700f05440700015292000403041ea44c4061200520500095010307234403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 888441852 1250 888440602 888440617
    0x1d0f16050d030908161401030c1d0307030c08060402031501060509011b020603041a090d0203040e07030e0d0f0207060318110427050c0f150a120c080708010906080c06 73
    0x700400107a0f2034403942c0f031030308210b1780c45801600c1e4040320070400040030301310420500740c0c2442c05108190003202e005007401c103411040ac08010034942002c00701c1d44c0801400c001950f008031020b403500c5e5074034066030300c0e900c0464060703000b0301650100800010f290359609042c2d40554552134201000000116a0344e0b1150812090300508075004c1c6000d40c1d2400c020303610a41c89031802000020125040715407054004e8a50401a440060540345681e000303c2580c4c02d0302c1c1c6032a211051583c0c3d8110440c00380c41d0025480940307000c1c000058903542d900c0b4420245600054084801281c2d55000c2202100d2000081412807800c190489000410840c650880811700510100c0e10300070b10715803000c18070f0150450000380440710000f18204041440b207280006000c03198000020381002c0461000d02c4200e21a86011034001240d40d9003d01a000d0f01c04c01d11098041000b00010712030000c1c0c80840c040c0c5040000c030702444000030f85c40c2c815020346002d48081e100a410120b46480906c856a080b561 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 888443102 1250 888441852 888441857
    0xf07080a060b0f090a0506090307030b0406020405120f070e240d0c180e03070b04030807090b0f0d05100807050d02040b131512021e131d0f16050d03 65
    0x2a00194507074000d0042d1032411001840f20b5039401100081050211940d401240101d80c00c5c040c02da016a00440c2c0b4004494020150020554880c03038184024400d44d080160303c400c0e030001c004c511020000c2d441844110701c03422201c446481d10803584004204035074692047c00c001c0d4400040e000c01254204a4580140103c001c1d20020703604d1007001d0a0540141780e0305423003800002e002d240e050240c9464252080060343c54000652160020b2200c018400703418030510001082026200300805d90003017801c402080d45031046101c00007081ea00640c94850002d080c080414650305450380c0ca4000c56004a0040c4841031070a0140508000401130580e44155540031010b02a22608190f04001c15070780340005229202044003040f545854200d0004241d00445500040e00d900c0c10400c1c5032404031002102e0080c0400002e003000c1525918440d203142040ea01001c100c05085d089864002074000f40d42c2d0000c180562140c0e2225840d610343d0b2075a01c1482d0070403250a0807580744001c1c40c007030b2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 888444352 1250 888443102 888443111
    0x305010f05061b10051e0405030a0c140102041202040e0c0108011a0c011d0d050703090e04390605091809010e07032d121101021317060903030f07080a 66
    0x8440c2c1034240400781d428524105d444500b040030070042c0611210340003201e408020080d04094403616602d00405048809001040303c4007414841040bc0740c6d0081e0102c000255035403510340409904035242040c049000f40c1c1089105d90001001155000d101101a0349011681e880c03c4248a0400c5070145130501101082140001001d401c0c02444160489698079490012001401500d8010381d45146010001d05000e0340000951050440044907020491007060343c8940c01c0404410241600d2520302448035150600c050780080041e4080c01c00c4030500443c50350307460340c0a4545205192829a000101134018403e5807c1c0341e030441d8010724628000030310b1000c00000d0324a01405904260b501002c05101c3d030441d0040d000b0070f500848c1c1d20b1652400030040d55660410810349052519060021001590858103025419140c50300404403010b580103903104c5450004481c80e0840001d00c2c001c600004000031000021240103001d130758600078155503101401c0b96192406442c5002c601e496 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 888445602 1250 888444352 888444397
    0x91302030c0906010e0a030308060910060c030f05040b0d0e0c1c062304050f010e120901080a1410090f11040e19020406050a0e01020a02152805190305010f0506 70
    0x55441e406c01462003502c0c4d04015040010402c420454010b103201c0340d4084201d070030b10410390b1107506400425818289002d420300d04510070f940e18021904220007400000c2183d030002241034000c003c102c0d407002c050fa00303103410a90034007410400031034604030140c1054500c0400510311364441d06110410609034141042110004c001800c0260307410303503c5030700081004110340340038450904042c080000408070340c1c440c280344240500840c244141800408400a070000743c0982100022082e54102003009140006400e50444598020450304c81c0c41c10b4040c0c1a0390381d89200704592000c460a4603424646821140904244011b10741030b8503002200414032070084900160014104c4e9860b196100d400a200080545500741038241c1158091159080540c0710795a0f1245504200415107684504506499014000e4200b104203d00300744856007520b640d210b009402d42945401000d80f501034249802c50980700c082c000d0310881c132141c6004000b140352460080081c1d02d098107400300034084 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 888446852 1250 888445602 888445609
    0xc0b030a1e091e050c10020102130f06120f020c12041707030206040b070305040803070f060e03273d11120a0311070c050a0b07110d11091302091302030c0906010e 71
    0x102c40f1b00203170150b90041041c24200b070040c10700101034a40005002911850000c0c010003c9140c0120360107055625403410a00403104e40444040b8140700303040f1031140e00141128605075101d171090620241c114501c0300802840030441c1e4088a4005120703034205804d203900101d440e40188001c5040c8034040000054141c4140301900d0a5405207650300e0480e038950401c941a50300d04484081a07400c104164500001850440020708034400906403280c1d6044010036020703103003140510049840c400e022844032120b1596180c8081c00b464644000c4458850700b600c0c0760a00318040b022541007101003440e0850400c01600084803245804248038268012199055003c0101070310700780b2541038107100034204040040d00400f00b0101592424010382c81d01400b00b00c0007060588200c0001c160340082c0081002919a039020040c00220f5a003044120140701d84020301080740502100ba000402600c6030002043c4c0441c0c0150103050700031a01d0081260040c402402c160600c07000a41c0f0210304d0305d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 888448102 1250 888446852 888446869
    0x308090a18060905060d0210030902030c060424020a1205070c09050906070306060503090c0f0607020604080d0201110406171e070203091f0e09040c0b030a1e091e050c 73
    0x5401c810005100c1c1c01c192030f000c00d841c0b0061a40b80102540c50072140182c94894000070025014039000442909520029081000300e48606a101c84041000b0a5500705000c2400ba8903841c0c15810b11080181e060903a15829554400350449200b02117001e0940c0c000c0d001030003540e101c1c0030540c40f22130300c403040f40045500517100340c040c0c0d5029400300400c076078052160b2800b510320b5040450452800c94942581c80c80c0d80350881d4050b06c4154441c1e001c03502c0d0380064ad414294000c1105d9104d50301c410035a542c0c0c00246881c0d47c01076080c0405290381002020459081d00d40c01e41e80d048402c100c07448042940100a4584042c50300d880c400c107200c0f01c1f408080c80c0c4c0107281c0341c0d000c1c0d0b50f550b10b258104203d1004075894805412101000700d4645a040641407030300d40e40c142c0d0714102c00d42d55800d007030b45140c0e4035600054602800004101c4522025480344d04191008504006400e1200102400311007410701c0040210b500c00d01c42084100018102d041d10510803030448803165035200c04182640c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 888449352 1250 888448102 888448139
    0x12060e0103030903031106061e01020a0503030414070e0c0414280602070509010e0114011106011203140a0212090312070b0a0b18150406080d08040308010815010308090a 74
    0x16841d0b450138010035a0203034220804403145801008603041010000e4820500342d07141340d02c0e0399503030600c415142c2d00a01030714407003c1d040001c1c0d0723403a0b281c1414480840d180c10941c0443c0b90007148000715802d411411418043d1000f00882410b042c14001145889401003840720340c040788283c0e0b01c54036682244a880780450200a075030030b01ca86042c10187c42d000ca250400c40c840c549641c0140b0843c1100401a41120860500d0004442d0b10b8801620505c40c8221001214001d40002107014030310000189038440c8030356118141540b448403c0074060007100102001078000c001c08020100304500a412200d200800fa12404441c224128400d68891309044805111160412051040030710440034401e200f95081e441c3c83c0c0c0320328041c1c1060b01c4010480c00b0380c0c00e1511010140d940700d650200f07003e40300c0507003150484031103980081c01103002203804070006038441c0c0001c120810080341c40e0300000c2c9600b4500e040c9908603070325014103800864080390420050b00c800a28aa000b09501010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 888450602 1250 888449352 888449357
    0x60a031a0414100903110102040506070f08041703070510020906030f040c051305061309080f1809010311092a03060d0b07110c06070c0603050a060504050117160501020d12060e010303 80
    0x15041440d0180600300740c2c0c10354180302e074230601c401c004c40e13101c1030700701c900c6180c2c05400c5103c0700401d4174242c805805160031581800c24440e1a204000600200410b14a400f4608480c0305154100681b420ba1040e0030110750884020300109012244210790990030a104001030001d00e605c441c04215100c000c1c80e440c00300643c4940070301030b090810005030304002d4046442400100415100ea10f55031040341303401c8400780000600c49015000305958401d00720002001103146596a0900c40c00003180b0044541c40340880101041d1154000da0019100d20f01020207560b030160340904d0340110380c20007040b641d0884088050a0005008440194410300903600c2c1c1c0180300024017240ca281c20024060750740111810080314002c03c1c0e030f200c503100407602e1506c0d020038160b55003000c4801600b4107034400c6410a081c040045000c1c48242e030081c0304040c243c41200e450b810f205480b0303100c1503228414503015070040401203e2032071280021154911140c0c2002ca5420750300c2d902541002c0b0241d105400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 888451852 1250 888450602 888450611
    0xc02041d01050a0209091803040614070219050306070e10030c1b1a01080d050f16060f020307030e060c09040c110610031203022b09020d08040e060a031a041410 70
    0x1403034030300031003c42d030030481d071100061f0640c0030b243e44640d5074401c41c0540414810304801a81014690350211401551b001c1d084802900482119100010442c05280e101e4041c0301c00251aa6108210302403110350010075920203c3c41c401d0040d00202400c2a00400b00480d030b0f40c0360400c4d09030440300310004038400e82d5500030314691000241c4840c64180c011002ca5007200d0904e02d85140c1c41000ea40d1881d034010005955025a200c204082454034a40105240d040100b941d03401305140e0702552080c07a69841c2408a061107a0300940c0700e840403903a152001205209a00312801c259003c11000d99080c01e2440906054811140c03814100311810660418000701c140308212528a108844802c1401c055041c8031203410350404010130000c101c298030b0b02842e100301c80c0b007000e40c01285034990054024094099103007403541d01340d8403a02a4000f42040103010415505100b02d00b1000c0320341028104d07280d03a1109089408a040240042e100784070200003014040f001400400c0034500060070025 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 888453102 1250 888451852 888451867
    0x310020d11130f0806160806011106150f012105040611030c07020112020313021002160e060f0109031a04080409110c0c01110a0623010f030b10060c02041d01050a02 72
    0x11803140c1d0700000c000d45c00c0720742030000500760640443c4205d089810200200d80c0c030500122075000c0650300c0107100d440f410b8140a4895004803c1007040141541c6004401c080c04005495090303520058038040e280c411000138214025500507034015204038004202c240d11000620a03a41041c0c40440c030000c00091a03c045680054040d81c8441000800f5411882c08d082c0c00f41190446210181c01800610f0950b41351520902c28461960781c07140c9203006082c0c840314044c0078684100c942d103000d0001a216007001d50300072040d000440e98004801b5040c00c0c140e00707421046070030140c0202c1d6600c1003400003054500c000e02807104407050a103500b5807108200c0308064076240c4040305080c10f100b11824151036412000c129003640c140c01c110046074121781c01421a440c1042c144180b8450300c06440081100010325100001b02c03806190051741e540c4440b900c008140c030241c400d00002c1503e905802005080c141c01185000c480900b07100c1d4620040348202e400e4882c2200c528103543d0340041c0c400c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 888454352 1250 888453102 888453119
    0xf180b0c0303090114060d06020c0f071214061b0c1203070503191401050114040e0c03060307080712140312010f051206010b03040609140a1a150310020d1113 69
    0x40301010741d07141c050075905048007c1b82c2c1040043c08003908150300002c0c21601e42d10200f1400060a032000101c0740b00d40d6482c050a10f03804031441c4100e0301e80d0380c80c1982c1500307414005109401421240c601650041e6407211140702603003d050551154024080142c0c515013114010398880c05960315190350301d1412a01400ca00e41c0c08040f0803d81c0c5103030002c1b60184540d18032409040d0341080c00d001080c68004050b48615000e640e010b800c042d00301c0c000b081151080c6d1406540581002d03411a030900340c072101010348644050141c100c40200042160010400d003e000d90303071454007481603e02d850008514080240026008030111003c1d60f4010000d600300100d0702d20403440401c016060650521038882c0342440041c2000e0300964680c2c0181c8140300c000b003200440c24140801f1a80d60710312510340410308010310b2a90601c004002000940703c00040c40501a8418008024240080803040120000e40040c800700614507513454540600b0400c00000b04050746000b100f001800e450080d49 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 888455602 1250 888454352 888454361
    0xc08011502010207050a03270b090906010f0206070c151404020307060c0209040b0a0227130504020105030621070b070501060801022502040221060f100f180b0c03030901 74
    0x440d03046a204010081c080ba8000c1148a082c40e45403a0980d048482c101c0d140c55042654510040031000480002804441e100028106030340c0907211a00a66110340040d0323403602c40910312202682120001582080c4110401e180040c1710720304500701341d890b007400c02046a8000e031000307498040003024002986020000140108128503046118121940c082004608042d0006000d00355800100744159007a4040d6084180d1040c00680d242400d0b06a9280c030401200303a05000f0709041c01080c810004d2030003800e01c1981c040c0c480b0b504d075440700c03014401c0d5001c1d2624003000039039020008800300e40341405440d0040902c1e070780090303c0c2e40d1780341840c90031182e041e0301c04034503a0320400c0200546020759008618009489a0f90003040d51940040350103407061891041901107510841d05103603d100100c1d0703014100a54803000c400c041501800300070044c004803c004079030300320301003540380384070340f60320920f0500f1845a0140300d585d42d043e209154109640e00003280e00080208000480240318 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 888456852 1250 888455602 888455639
    0xc0f0f0506061009050409050a051f050c07020f0603100503070b0409050f060906011202070b04030c0b06040c1d011107031a101202010e01170108070603180818130c0801 74
    0x801c4070114000c4030001e40644060f224140c0101c7d00d40400c0010f004040c4075485420f60800d0550f00c42c1303007000f8400c1904028404182d25000e00d460b0108514001d0030040d00d0040354040e1080b07400090144c00c00c02c05800080c190b040c44018031002184035141408130100502100c50895115820701428006075200200303548500c82d42e203020040c0e1641c0d05645035810000c2800c0007481c00c2d420b140c542c0302034802d01e10003401500200041c80201584004140042c2e03000d00366002183c1c0310001004142d540403402070300001c01035042c004414900462086222105041156100c4a40c0f080a41402510703032080c1da1110510794004d40c181c426000043d800821aa07400192509124800003104900306c406030400c4040c64000f0391f1640225200b08070404001031541196075108005170ba11000c6020300d800203410100428001c12036410410b42d4642d00941050810707030240104d02d00d0000e0708003010fa0110034400850840c03001803155806640c60380d540e2110641c1084070418000e01d02c0c0c0f5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 888458102 1250 888456852 888456859
    0x11091f120b181911090a050102011a01080a021b011b0c05030403081b011d16121202030403121206060504150f0201020405030d0207080c0604051305070c0f0f050606 72
    0x40d0200340036034558040400c4210007000e0b40c901c80e00d030b20015030843c500d8550b804a981e4503260500c9402440c00001d071070070700303000c0307074070110349510782d00128241c0381405c99440080400143c1405590b010b041d8240d48a500a074005040400156920282294140a1030001c2c3d45d01c202c12209041842a01162212503080104040c1c060b5640c081da6480b4610029080850101d445e04082c000708030301401c41400380313009004085840c4e41c00c10988140170850360f95845900544614003050b4082c800481d07030b245503403030007010040d110442c4034207c904900086001c01c0002000007041c608a4034610301003036481d03801160104900404442c21500040306010f401c1c042003080c642074041019a2980900c0c1c0341c4034000c80c0b944183e019014581003250306000d60940024541e0f0700044000c111000201150701c4140c04100f442920320890241c60307001143d620004037440101d4004a4016880c1d1402014076002038940c1c25241c21120011145201c0303030300d070600a00c241044255000032044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 888459352 1250 888458102 888458111
    0x400509060612150a0914100f121401020d0c0513060c08070809041e0e1213061b06021245151e220611091f12 48
    0x2c4800b0510307000010071400d50006102070100094580403803500003020448000c1c08201c169524140c441c400858611500a40c000400129a1480c48000049545c8804000580e003115114010640c800f41d8034005070350340070010f44a04184038820809000310765603c064503402e21076480d030a100c425601c80010000700c0c2d20040e022450305400c03a10341d81e5000c55100c0da540c2e10348000c2006454100c036040c1351107441d0100944004810342140040d0705280341030f654611402f0882c4041c82c082c4d900507589450326502c09000c103601681c03101e48a5000c1c0c01e407103000020540d603035070142d0344541680c0079211a01d03410700144002d04009003403110303860410402080110811000203c1d03194007114421740b070089407981074200501c016009517200120b41c0c002440d080c1c0b01c14480b803a0340d6a18644180f103480020700740c2c2e155500761507207018031002924812802500c03000041c1c103020001c518a0501000107440703581c2c0f0300c8a8403500544003540560450f00c031070300c0900480d24080c80d410156040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 888460602 1250 888459352 888459367
    0x1302150f0f22080705211603030f0f030e0703020409240f0612030c0b1b070f1403070b01140111010c02070801060b0f0f1b03070507051f054005090606 66
    0x441c4809121b4060201e2911884101c06021518140c0400550a9404801e0b0300c08000c2c968401e50007000185151501000c103040c1120031805c0b580000026000790700224404c1c0300600e0f1540000c1040c9004601c9581c0182107074100c1c0445410200080340325a0380d4410b1101c42100d0342c000c0d01c1c01051800d015950708402c40d100640b0240a00c10000e000c04406d0000402c030314400107402c600d0018034424241c540400380341403600f0064901c07060301c3e69221506030556101001088460742640b222100403180d281c580c00700c1c8064100c0b041d0f54107000d4461990100d2420901c40c0d160403e24560007009410f1418546c9400c40c0c825804c45110340034200421484403505000b192001820022540d54034141d00b45001259500e20303116915034000020448180140002c80800750341c07013200c1c441143c81e0030321007a0084c40226030009000c180c0c2400441208092603115a28400009aa0b16016005040303000e400c04100c99103900642074a1006114608201b540c250f84138806641562400c100e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 888461852 1250 888460602 888460609
    0x20a021e09100602030910110a030809070509010305100f09080a021c0503010501020a0809030114090303070305151c020109030203070b04080c032428050703051302150f0f22080705 79
    0x4506030380703000340c85c0c3c0c0000104061240d51001401e41d102c2c0c8c25a203100780d0528000b448260160ba06c10317801d1144030004070f22841c00440140c1200e902a0041500108161105000e00b22030b2980c1410140c0c0c89e00361101150300e00300100030b00070a55002d0703c503d03000b03010300750340081c80b40c0c8680c0100482400184081c3e6000508107101036000b012854403003419400207400740401e141c512501c00b00362000d01020440000143d40501c00a44081c081691107402202d00482d40c46a6603030311001240000404041a4040b08500c1d401807601003031031078032030b00842c0c6082e00310303030045002d000f00003001c00208e4030a024490200b0022009084054400154100400034030b054113111a00b010000c43c07200f410400100c076142d440c0d03800d000350a040e01090180101011100368020a0400c400104030200c210700210384507a008044800710000d146501c40e241d04500703107682c20b401c0708011100089003100d024024a00c81e0100d50f50060f11701f60f8807010204650760229a583c2d001d2402031002d41e4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 888463102 1250 888461852 888461857
    0x602090319030516110a08010903080a0b0a05060309031204080a0f02030418240806160c120f1119051e07060509010e06030906071b02150307020a021e0910060203 71
    0x40f100541c00908082604005c907204001c1c0d4032440e800500344100203940d001c107402c1442040c1c080c1d15100e500340da4514a2078151024240610751104e49440c0901561400d02c01035a005207030182100e042001c04840325550450649040c0c840303040208112040e190700075102c155040051014504261611560072900c01e010351168050a4603066824003660014410701d40c031034404034018206c541d5845849407500015500d59068601ca00e5035032801c1802440316901c01030740900446245a0500c0c401c880d081340450381e4400f003000c604040d41e60f80008024600c03140c0102081065403894a00d03043e4a4000084807013504983da03c801c10640c030001141c9201102c86600f005076940080d400102c03170340d014000340154040070100130b01500d030034009819485001280c0348e43c001c4030740c0707001c116403041304400000754020342201741b100c80d68400e00091034100740c070750045031921b80c01c40d800519005039000c5210018080c0c0c6c03184100d0307481d1240d0001c2d0402188482130150340d007001c000035101d2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 888464352 1250 888463102 888463117
    0x6030204120807060e0703030320040b0a0e0f0d061e140a0b0612011e06030e07030f140102030f04060c050304110607170c07030512090109061107080a06020903190305 73
    0x49901248020a1120640040c51640440c41c251b030303495503c9282c094010090702010a458041696403085484104011142950032901009003804c4134007004403500828880c0075604040c240090f1080d030313191210148421403050b58082484900140301e1096035508062090f540b50800015240c1d00f0045000d00790412080c00010580140110214440348280c1d41f002007400494400001c0300c2001c00309243c007207107110700150001030742d41c00114141d9140520840ca540c00012040001500c213246080c0d0007441510041901030513101e0b02804c9030000c840301c910290215082000b080014031950040d00401d040490560601e5181c2404104039618a240122400a0741d0000d010f42e400a10050b900280c2c1042c0c1d0b079801c050100d645901c0544002c881505c100e502d000c60084204090f241000c00607502d001c8a02e141840494030500d01040c6007500f80146c50021034014814040003514074081c0d02c000da078580d030b40c805051401800710070075590b40000c00350b10fa000a9000b002c41e02c1d80c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 888465602 1250 888464352 888464363
    0x521061911070305190903020d1505090604051018080a0201020a200d0f03090501090c080708071404180614060a0b0313060c030221010f0828030507120314010603020412 74
    0xd01685c04410f94440c411504003942c0128040030b15000c01c240e50001440c0c09101c00c03000c2c40251290480c2d40e80c1d90b00103171401001e98001040c02d94030913500b503115466554801c41d8204a0554a071144901d941c442c0311584010f03500010344442d416000103d00030440006c540f0708422068071112651a6500042d280e030403c050015040b04480c82600070180058002d0005c1010480740d19000819000611480c0307d14003403071000003403403100480d094080f84c14544611215404450801000704911042ca0000c0c054648a40011600300d100e2824203103091011045c050410324100840c14445500c00c2c264580100f081181d00048041c0b00090154440d0012602d103e00d114198060f0042000021100508110042c03a10310038011090484143c25806405251149100c0d900d83c0c18000761600320543c261012554540a1001d4140c018000d190150900c0107a96441a08105031041103000989030540c0c12000e1032031074441801428141801c61401d45010900c0390802c4804402034503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 888466852 1250 888465602 888465637
    0x100302090604022b050c07150e16030501050f06040603080d0f061205030702101b14150f040507090e1f020f04080609010b040c0503010521061911070305 67
    0x4040d02c4980555a14121682400c0c140d52003580282c42c07264a1510300345059030a00020800700c5846600700d030040c1c0d8110f007400300381c1141e9041407000b5010915142c0300d9407050400c8180f850200f24052000f0314402c000204081c00c0c640d50a1410765000351807a4440c9142c4401040003c10000484411040000021810504034111400100407035805181000e0b11000070a0800c00c0c040001c000d418030031194150410b113a0302040b2801110320003102d08950300f100f6080040389680d0b4170044401c15241c1202d00301001d0303102d40313024100191000085192424240410408240000405410101000c05c04070140c070325002cac0e4030310003611124012003000c480c2100000403070301111118031104002503a80c954034800659224000c840d407144075464031114600c1458a40034440c01c0460179901c00b81180d003000104800c0c104010700d038640c4103406561740003014109118003480380e480986029030b03010009807004150748421520711a46001044052300194005050307840c2ca040c80101c030074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 888468102 1250 888466852 888466861
    0x1030308060d0602180a0b090d08180418211d040608030a18080303070507030509030a0c030c06030e0f2e0603200916270803070b090610030209 63
    0x30401c00110001070101400017800c0e541512082c3c01001001005a40701d1500d96034880088481d80900c605156000c0d09111900c000b24003030390042c155220402040b80030b83e000b0b150015007107513a2020160301c400c0c00000c000c0c01340600140b241d20302200b0344081c5100d00c0803c400003031081d0100c680055500000c400811900e40b40c0c0e0b440781011301000403c803035499182c054081c10a140e88040c0d580a220300729800b03d503400300402507a0246035192111820144203503011703100c5e5003000c150310740c0611402406102190f640e150880c000c1d07001d41c20070b0b0f038014284800281924a441c2c200d03d81603004c2081798650401c00907070403100c00010b4145800d80d44007400031007031070020641aa40b0090900703002200780820400213681448260507048201400c1c032050208160045603400f040000140c0b0b8088140c0c0a0020039481e19001081d030105105102c0f04185c92204541014203035510210f40c28040100d4003002582040c0b00000505040c9441c00102d4410070f081d0100a02580c1c034000400c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 888469352 1250 888468102 888468109
    0x90412050702030709020322050d0c06090204090b04020102010f1401050904170a09051e1c06060807171e06281a10080615070f17120105180103030806 66
    0x2225a07503401025600f80a41d20440303100650070035038050b013080841c107070b2103508040382c000d03c036126075400800f5160700d2011510a0f54103d61440c2c00b03540c0c140d186e603940c200607501c520800c64091700c5149040c020f4180381c00020708507a2054100000c1074034194221030004910380c0b0a5044490440c3c44241507a11880c00110507910803029170311401010402d080c8140d0840311160945500b503420400c45217030007900f902d80c2e46040324071b03039000301c04228542d280303c415200c1d140b0801d000d034074045281540d4000c003501e8910282e10000201400001880c0041400e11000190f05c902e800c05504c44062581899150702c406845803016034590f054102c122010200c3d0407000088600c000c000042d80c0b681003a17498010080e4851162103903000c3e070300445000c0c11300c1500807c00544001c55607004d100002080ba130001605807011440c00c4c416400184035030303070000d105107510040580c580300014580b00f0b0100741070700000c0c03003444c9098604810103690480c440c1102e804d07281c2211191502e4010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 888470602 1250 888469352 888469357
    0x15120114040f0b090601030c05040c020106031b050a0f030c121a16080a0c050a05070606050a0326040b2a0a06060f08010b060f03191401090b01050909041205 69
    0x22124500340e0501007200740602c4410840304907000f80d2410700ca0ba6544403001e6220202400300601050001c1024040d40c00c056003c0b60b8005d0319400002052a03ea4a51081c4020300100300c80600510000511141c100103104000404001aa00713409604541d140e41e0900200d000b251f00c40c0d41203502810611034034032074040d1000090f00100b152401c0004120700841180004100402c1040c2c012900d0754145124a41c002e4201e036603010f05059042c50700726801e50103081d0130780703400d500c401c0b001c101e82d034034110240025407081c00301c0b8000d0031041c620740c00641c80c002c4141d46d00d404203000400000c00e0860440d40600c403084002c1e1000303013660300c0e41da00c1103100036000704140c82242d00f94030410045601c01c2d0282c801c0d440452031070960b43c1d40c64509917401002c40303035000101401401d0700144c464001d10b41002c4500e040302102604005400101c2c2e10045504130500c220a0040040350401c1c0304001600c002803074031f40e19010212020803080000504010303d00f1a44105806d02c46124a05 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 888471852 1250 888470602 888470621
    0x31f02032707090b150a021c110d0e060d0e0a05012f0f2a060a0b060d090614070e090a090816060b130e0f071505030c0d0f150608151201 60
    0x5ca80b511003854210081d1f451601d030508400124441d400c41c2d40607401518170400d80d402403401401c007418950003c84d0f590080d1881c440e08404107118030100152a03000c1c1c0c042c40e4407001e008140d64138003801e01c142581c0c5015200b20b14283c0c24502040b0141528841c0c0b90706290a081d42c036580d0020496100c510703c100303109002103c0c901c001c0c0005640200d04403900011b10401251144c0e01e5410811027101c049088266118508002940c1c0528403604003108950250b10300041e1021044010100034800f210541c0008450841541d42881c040c820290468002035003080f44200c2aa6400c120f481800d98580c140117420407071104010341e64009500413040508001c40c0da803d1002c000b0041c103454a200340f81e42c003c602d045410f0700750004900307013140e0400300881c0f01d4060311502600e4542c0082d1030f244481c1c0c403c2100c060803182c24029604540c94100002661a402c14039501511321590064001c0080721405c0c0314903542425414080307007408661122810f801c2ca10b4a600410358400f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 888473102 1250 888471852 888471889
    0x6050a05040b071b0b031012060e0a0302210307050702010c06091205090a08390303040e07020c032d010204030219080d080405030711031f02032707090b 67
    0x300c0d20b0410008108900800b9404c000d4109500e80f030f02002c010500003110260224090608100300e990441444240a01e004280005506501001c11814096000c0c400d4000d68041000b201031b0744007e41d40000c401c0a40303258103085041c04074000f0102d01c203610000e810031039070f01200810f01c400b66100300501c030b070b0203410b030030744048207510180890f08060760842c801d14110f0f8000a00001c085031203851040005c02e5085510085071100410420040441010502c044034181454030104014400380051505200c114641810024034000d00e01001a000f40c01422842d100b541d00300d0744105101c0380401c0307030032007045505d1542c81c028050707940040d40c00119011310718084c0820003d82015598500e080d503150341c035a2002914013110584d0010500d520401c41440894510b07a10403221980050135940740d20a00b40c2d4400c0d0030345e002144010b6440d0700005100105802e05c401a41001c0c5042503c50340d21810103100c0e846c0c9001d441024803207a11a800c4400d076030344a01640080e880845e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 888474352 1250 888473102 888473107
    0x26060f0105010e03070302031e0a051506130c0c03031e060f0303030606020a0314090d060e07090b03071a18130e2103310308040c1d0106050a05040b 65
    0x200141404042031107442d0224481c103455001c60704000c100701040e070b0340141c0140820036142842c20300c0c142c80d8110038400d5020300f52421000480c288042a440c4511841c00b01c690b08014040151703007809410804c07002d526102c2c030001840d4002d800e09103440d405003030008100004504070b00c80304512489503000d0130302c0c04402285050228041805a0f8003d07541004510b88410003a60745002c00400900800c0e0001000748056000d0401020040303805410440348100da036481d0015141d141c5016582600701340030a000060062252038510038044008080301403520460080203920443c6c1e0413840140001c0c01080303040a4814048221400b410725480040d07041400d9000389412203008071140100150700d6043c00311b484020600b07000c9004218a035448021400507002154034284600458510b0540300208054103041c030118000c1d1521230300351401c1d01c0e0034802c5c5050b0f0740014051030611119000b070b482040300c0c0a41511801c0c1402e80e515540c00d030081d2154041c07544221a441e800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 888475602 1250 888474352 888474361
    0x513020a021011160f15023a0f0504060e1212040f17030702070602120405010305090c060d15170607111507030606020c0d0809041a0301050c0910080405072606 70
    0x10317440c3e40c81c501400c107001c02461820311007002e9214888605480100102440c8486010303202c09005916441c00c0303210704002d240c11840e040e40d0010860540e1160b40f03000b0031062103820f010f61903900030000302409151080301034000e514010085800310080160740045c04001e072004007280025003080c0c4030b03140003980402ca9010313075004854080060040c2c0e84d0002c0c0790b500004900c1c0e802a00c009406081a00b070030700460080c00010030405481c031424000c50b40c591150310040440c60038180d40424000c000850a00015007282c3c002f00c0550000c05400740d64000201e2555001041850714140c0faa500d1031801e0310741551020b041401c000040140b020f03260b01940500101d40c45a020340304905039613801c001d80c1c002148000752540b0707001c00502266103015804104500e9001c0010526040e8460100b400c55208586256054900007451142460001890b0700c40c001c640c0b07442c803101c0c3b03060381e40d03503440c0c0d903844c86100e404c46000b080d0001041c8491103000c4e18050004101c8506260 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 888476852 1250 888475602 888475613
    0xa02130e04050a031d1809100e1b1c06020a0c051c08070215040311072403060f0b12070c0f05010501030c05040911120c0901030b010513020a02101116 66
    0x35480710490105e4a41407142840d03028180499035203030301c002d2054611640200c202030112030010074118036801082030701404400644500c9034120440c0001f007c00d14942e50404c61081c100600480c81004a4000e40c034100c0590801140c0c40c80e13100b0400360302c8000400c41540d01e100506c0300180140581c0c1042c220b100180d20a04c1c41814141da1a8929900e580606076140c2505170b82111200400c41c0008002c00e018541000780100d40c58202c50300242e45205241800c07207503400c2c040400b40404070029070301e80d0500600001e011070001035000c2901c0d2410b4160244a0303141560707040c1d40700e00002001e1034018003ca005181d0030190301d50704800f8520b045402400240005c84080c04042000f050fa800c082c42454105584041101c103845030400402203107001070034400341c0500c40d02d40d03840b8543d110105002e00030740c4a000750701070550414040042e0400c03109400b031505032040c410b60030780319800100b030030120200f480b0015180113298100101d91080c0740702c4414204900e50868104071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 888478102 1250 888476852 888476863
    0x121c0302090405060109030807062007080717030106020a1119080f0609010513061d010204081b04021905072622050108010b0c01020409110c240a02130e0405 69
    0x1441102e00300250341c1d0300001940d20391a50700010b0054030041c0000720004107036070710a4000f211076034100c440d03110100302815159406090100c582110224032402040307201034010302e404020000311401d643c10020003e68807100c1840151102000f54115002d60700c0d511500c50300707101e0200201c05c031140c031030040c41d560f000118032a51079441480000780f401c1806108460203403c0e0007800d0440b41100c0c1c3c07503500180c0811850155001e00f040203c1d450840244020310050800d0070142152a032a024000d0f0300220320681280500e00420603007040c00c040c4c0302d2007640c004441c140151252810b0524101c0c8170050558110580580c0b2490200441030350302900b4081d41c1e028008881e40b0040b5015916003407103200c0c05000c80d03007100c01031101c0505140541403984808000500301540c5041060540b501580c80c1c10052200044100c02e110050040d0040303488146800341440c00301000e0a60403c50081c0494074107907010231180d20300040c1c41c0705080242050340481c1c0b0750b070038541007154882 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 888479352 1250 888478102 888478117
    0x607080406270203060907050915032b090b0405010c0303020d0b040c021c0c080301050405060319030f120e0c010e0409050105010906050a0503070e13060e0604030c060c1d121c0302 79
    0x740f141900186003186c000640d81c0565002402100054664400c000c00e11001100c203940d150040100101c281c910f01c20751110001c03402c452032030082d04c0c040000343c84507206401041c00346004000c01d00050741c100600c4e0ba540b0f90300d031600590b581c0450613088020240100b03070541c02420060403100c015070000300e50102c202e15407240c4602c0f9650b00b0b170a0b9200c0010140c02842281c0c02d100410036883c050740004e80c00040902070311b10300c01301d804003a20360b40203d54085010034080140400d40640c8040301c0d2648266102c2c0c1001120200c0210f16074604507508070f00d041140e0a040700446469640040b0000b5621000a10180d40c580000da8040c0c551406458003032040c2c00400a402c2ca0009088811601224160710399901e4000c0d0300c118042d034141c0107641054849a08202c050420010584034901959440040d000c0d14504181920303010b03220134040103500000400c180032210507402507004215140d607410f6001c16883c0c1d0806403c0105029800000c1c90701c5000a5090380052856 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 888480602 1250 888479352 888479359
    0x70314160f050703200d0822090501060e01110a0f1103011437180b01060f03050f06301e1203131e0206030a1d010c0206070804062702 59
    0x803000c04822001d20502282e49a000d106c4078400e40206404000500080c51401c0311030344c1c5940b4402406408031055804011007503500c40041081a030b001c15480b004a00074a0005145070302400c601f503441da000074010b02503100c0074000341d080110380b014107c1c036228060001e0080f8040d14032040001d82d01164100c10075201c207940c20480c0f20a50100603041c0d1070212840b038065003c2c801000040041c900c004c2e01110504220001003000744400341d009044681d039400940407200c80c0203050350fa020f01880d4801714000148007030b540e41c1d92080c4800c4a140516403441c28145031280040700e41e50541400e0500840d00840c03a0f04060240303c103074035113a03401290340b0301525940001152000701c4039668241c450b03c0002c00094001c1c0c4d00074020102240d00c034411001d15400003002640b007620348450b225034940d10316081c400c50150320709208000380300810001d641381d94041c0d190749000b007600f410003401c07400040030400ba80d40680c0c1c840c91010300d6503000040b80400c0b20702c8400848002d034030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 888481852 1250 888480602 888480623
    0x15030a120909051b1b030c07090203010305151b09130501150f050310060c03030207060c030203181b09040219030b190e0a02060c070306050a090b0c070314160f050703 73
    0x540500ca032031454190350391881e040c0c0ca03000340c406101c0002012181ca00405c1d020800001001d01030400c060800f402000c03c0041c2d4035451481d2040c9001251072144400c4000901040149051100c0e20b5241009481000350703500106400105040b4060700c028040f50715010001c1030820840c00600c070900316503180c0c0d00b8208110141654507000071211809800e00c2c8202c10300155118501c10009a80f0a007030241c20250310390350368004d595064203040c0c0000ea000c420000b144d84841464411405804058407485255280d2050f1307240c05001042e000d425080040b4045448ac1e611003402030103428880e4012903183d1a00075029201070340c4160b005c6c8045111600204440d100b0300300c0c141b0b107900040510041e190b00f401030740d070800070140c081c1d801942800408211203000f100c0c403c1c6890480094591001e01e003400b00407402030182c2400b500140440400290424500100c0b8411200416101d0641064010003940607160050044281442d0a001c0003000a015811340348910010035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 888483102 1250 888481852 888481861
    0x61318020a06020303191104051e270402060f160809010f0305130f031107081c02120a0c0f080c01020702031e0d0c0503040b0f0406030c0f0815030a12090905 69
    0x280d80b03020603203110096015010400021358480d521010002d010f00407c0d07410680d503103001440540034128101c00010340120351080300e29004c441e1042e04090002001800384180d18480d029140050000313000e05000509220441100701c1a1160480c80c90044860050545032001241d003207200d01c24041021142019103440c00307030282d58841d005101080c038041a1b91380300d141c1900e480a40560620080040030000c00205010082c0036006500c001d00303280c40740c1c0461a2000b0380d03243e81a003c40d005108401310f4141c0c0f44085036000c40d101e04e030008a118040c2000da180d0030303409900400c01440000c61610103003043d00075286840c001c809845000d207110344505268100141121242d42100c0c80b0010414000c0c405045070f05c2c051022a402c1c281c03a1418160750350b01c010741103180c003500800c0030420740351325002d00c1503034a019240603e00b1202d1080042c04200b80a081c6403900b40764604030039401e4604200c140310194020300300c00306000170302501401b054610b00883e80500e044c4030008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 888484352 1250 888483102 888483107
    0x6050c13061d090f0705090f19080c0303070507060807050c1b0111010605030309121014012d03080f0c072706120b06150d022a1005061318020a06 64
    0x214840d1071000c0c4c40000c036aa032410102c2e0143e112104c11548410000c0c181c061b07031303125440d050840751484903d040700e050408409926107040444000c0c4039a0041080500050011070300d10700f00c51a90500c1852511000700940c1e06010b1864111010702c1010784001010340c80c00b9040d0f000381002c0c1c894038655407408805609803903a5000b2250164002c01640806090200074040220010b80c01d4500071204103900310700b550702c8a00000505240c420044c44161880004419403556000801e4912100c0041e065200030061102810b404804100c0046019140d001c43d03100114410503103603100c2c1c8440f2045c1600e00c2d4644030104074083d80d0211405011035119100039100e0f031882c1d80c02d400071190348402c400d4500401079078001d400c0c90007594000d0352050245c174000b941d0740350140e1280d03428900d48011708040d01107001e40c0e03213201001e100c000b00041000401004840303004943c0e5544c010110716480e02c5541c100d1006441d0030b80110300321081081c41d60f16a0b1003107624501040d581c0508 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 888485602 1250 888484352 888484369
    0x212060f010c12050c030c0d020c09071b080d051009060b0c071206110c0c01030b010f0c2d031110230a181112030301060c06050c13061d 60
    0x980860380d00640d000103c0d0348801c0b407071100c403075524040c3d05c0c0104032a03007581544c10082500300035520038031110788a01d03014040e00381c150005590074062031402942c000c0044c1a82202c070500c0d661681940000d000c40d520480303024502d90b100c03e01081c1825655411811038501c03485c3c0b20386203460030200300c40c8100c000f101c90a200c160003c03c0388074107104904059210844c01114030300e50b2a04460720080003140505509007400c405094a0f4540c40300240940343c070504030904000102800c0200c4a4200c200440604d80204024010381d41c540c0c03400c50f00440e16000c07140081c10000083c4101544a4115035900b004081543c8a0741c1d0b503080c2803026140040710000500c0ca401d00102041400320052543c407002030280030840b00e03214003641e150001405c0d010307070742c003020310816a49905042c0403070007409801d130004510b1580b410303074003c01080c1c0c4400020303c1c058030740c1c0100b11081c82c07090a550320141042d44410b84e0940d244000b0f862042c084819041507141206030350000d2415440 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 888486852 1250 888485602 888485629
    0x70806090709090f0e0a0c09060503031c0e0129011e020a03120b0d0b01030614040b07030207061e020310090603020303090108060414090609070b07050316030c1203021206 75
    0x20b0308044142400790450203842040d00c0c03500016a6164541c2c40d0030001c02c55440400c0c007500b1107104841c200381801003a15155004240690b10400c400c0c85400100f4140e281c4166000600085401e000302c1e085014014040705540300b5580d0309041c000034011b1502c2c241188100340c850303441c480d03600191005000900540c560150308104046008039004403c178030303030500c0308100008a081c00100045c000d2422418150b803015040703401030080141070b115695980141c060401464581f941e40c402d120750006011400309034012498800700111a040081c45481611019680d2082e8500c0e0a000750000c4800c00d81b044070b00c10f03001a0180e40d41c8102ca040c3d980180c06145840c412000645501c0006000e2503000355075a41ca09195011307508205010f0401c4c0d002a21960510342841d40c5045640d800c080f400c0031040141170001000001214200340110310340d12a0748800d42811755060a858070050b125440043c02440495070581c0101043e48004481080984503407041c0500c03501e0000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 888488102 1250 888486852 888486857
    0x801180b010e130c180e06060a03080c07090f0b0405010614040302062b090308160e0f030109020919063206130305011e09020a0314120a080708060907 66
    0x38014440461024216030744644250100ba40702c030380c55a03d4821401085c1d2040da00a4003410700468070444501a03281c131100242e0050156091a10000d440322034140700007020440001a030b8800780c1b00501c141c200900881e042000358200e0301c0c0805005d04094048036101d64545800030507014003070185000c407aaa00c0212030704150441d800e10000e40c3c4201455105182000c10300341803140704206a4090518403e00429041c90500d4003812811001e403002035030400d031202c880b21160380030b243c0109446c01100c0c0e6003190110080840d0040c500380e400650002d60f010100000b1114401c03007103210501c031348410490181c1c0c0320080c05442b40b684050303950b42c4007526503580600c90f000030115041d4400410051421031041c121515101641e0303c101c1e04c0d07945402c0c1e0150000f5100210891035041d00c1801e06c801007040e400544080b0050000511051074102268521142007005404103458118801d5486101c280050700d07400d8125824400126a080010341c0d030f0400000c998001c41d21074 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 888489208 1106 888488102 888488123
    0xb0d090302070312021c0801060c0305071406040f05101b0503040201210906051302030a0b07021005181c120b0105270a09090c05010f0e100306080118 66
    0x217080d450507c80d203040100441038220500b0f086840d41440e103d59158154030704010402031b5840c4180d010b00c5030501300030400c482000400c0005004a007221100c511401e10f00c001d42d0821980600b030740f0035600d50500036a005002a5410a1050400b035410890746980008454000c1c04c03000c00450710303283d4035000c1c800c603441010f4101100003004c001c100361980100e03984d041d07148001007129001500003040c0c40e101f4000c02c90002c400a1081c07000c0e09008444401121031801c00c0c010754003030000301100c011281040f6001e000210307118164040b092003640030081a40d180300d6810700000304080c2d43c0f84000181c100c8180c442c49030061404c110300105111510765150010b020301071518049a01040540060400302c1d2401d10f411080300c0700c0ca00c8110392a4248590a5400042d18a55004c160f034064220400b51000640204980d2412046040a01ea842d06020700401080c = true := by decide +kernel

theorem cover : BRFrame.Cov 888309352 888489208 := by
  have h0 := BRFrame.cov_init 888309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 888309352 ≤ n) (h2 : n < 888489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
