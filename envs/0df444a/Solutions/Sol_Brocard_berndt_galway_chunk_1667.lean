-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1667
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:08:23.279304+00:00
-- url     : https://prove2.me/submissions/6b4aac1c-b38f-4b66-be3e-f88c0577a44b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 299640287 ≤ n < 299820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 299641537 1250 299640287 299640293
    0x31204031809020c01110c07090506150309010c2a020907120504120906110604020904080705100b1302040521011d0d031406180417040e0a05060a0b0301090504 70
    0x94075641c00d0a07410038010030340030a90b003aa50340504070621050000344410000703207035605403a00c215200941241c004410620a94815070040c80d040440685130a08890251b841e24503e904240e40004203a51a01c0400d03071301550040601e5030718620659080250320880390404401000540f00a0240f1f0200c40003807082c03401490b0380e403220b80030705409115a00c2c05203884601034003041c0901c03003c901c1035080442c1d05031191054101502f640c20007030100e5151a001c0042c40540140b003161404001c00540b00052410300247c509420781000102e441e013032b2041049101d100c15440c22003a24810f00c000c00043c0d440210310900f024002d011910103142601c1c0044c050505800341d01c020300b401301000344001c20002183e610243d501d07a010171050040c0c0c7d401d0001c01d4015543c05074000078600000d80c2035640030810f00e0300a031040e5510000e81c40000e10903c0e568000794490048495800300b000418540da010b0564407403800c48101da5900d0900041107400d010600800c080d15690324006010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 299642787 1250 299641537 299641547
    0x4110a0512250812130302061605070605090a051c050105130b01051906050a09081002090108010f030209012d0b1c060e0c0a05041a09100c0503120403 66
    0xa04005001400003201100d1426528040c040000d81c1e80050011010000e60961200c03500b40c070700c50f2002d0403980c801e038a41d03000f25420901042e1900d16480342c0000050b52020010443e0685050b00400c0c02215404e00c5802c0280301e034005424850100023030b82980e07039043c2039441590821039020b90000001114084507600210000300603610b03202c24810a038000b00c6e800390400c1e21030302c00c210040c4c2c1c0364018031200500c4d0b01c40c407035540c8194100505c050350003003002d40700d24609454001070903039603600780502d40f210310f6a0f0790135070380c0d0b001600c141d032560300045080c0542982844c40c0c1043d4516400710b10956414070032210500b4004004c0d070b4101c0d0b031219124016010301c06482d941992192590080c2d9840a0086510314017039416907080f0071607901502c42200d030f10001042080d83d601507503500c150721814415003004010040410340019008800e042c81c030100040315100c012034414401c22400041080052040c0c90f00c10000081c0000121800c0c0000305c0b812014945030341c40d0a5807 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 299644037 1250 299642787 299642789
    0xd03052818060207290406180b0a05010512010b090c0a0513060e011706090610030905061501090608100b1605030316021006080715051b0c042304110a 66
    0x3104003200c0c1c42000c14898070b9000307060690b001d2110414120414262060307003400007a669803480c441000040c010030710b9544041c6008040018a4104805543c1c6001010004440791001e00b03a848006005a08224401030b4070351032018000c0155403400d0f00000c125a400400140f0712840004092202c01d2240c010740e86a540500403810540341c0f690005018401c803c440503001a441081e600b041d641082203650044102802e070240c1c544800c03050000d06250100c000b0203042e2280031000004408001d00d501c07a04101420110b45410000010081d8640c0e6014108101c0e2500074040034804401505084810751140155102000c1c0083c807403803503011002502c0741c0004000c20040b43c2d8a506105255541b60382940c81c0030159104903011180240510790b4540c2c4a04010b1203502d80b08042c4025400c400d00700603082880c3c0c2b0608050304c3c038804403040d040f40c0080031214464205800741c60560510b80c0100c0240c01d042c0041c003402c404004001a0039520414010320550321803101400c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 299645287 1250 299644037 299644061
    0x2011e0e0a030507030524070804031e02061609060207060c0c0e01090c0e030f1002031e04120801091406010c02150a052503020606060714031b0d030528 67
    0x1420385990b400c03d82d8884100d444141d5281c00340d428030301307809400030b00741440210394100d030180183c6600d607080b2400400100118288030250443d5491400e09005070b1070241e0842d4006d0940345060101d10401035140c0c00c07a24140148040c003448401e4010501e1030658503240341076410790b2028201000c101a440d80100e0310840b031580040740d100310b147c0102c0d000101c603843d816205c0510209041d91500a507040301220780101d28106544d8265030021508400206900c45840e40c03035511100e0581e1042c4d070700302c500310f4810102640e07468002002e14014a04042c01304041c07003121100505a50004103d03604000c00d0a50080441d40d4044080412400000c1e50540b140c1441c0710207007c81d404441b4483d40414040c0790040e0714500ea4440900c443c0e80340d405010991288814019076800c103000c121004015030748401001749081007c2d00300c0c24495014990810343d0010194149036407801e00008150800b000c0245142094851070709030074012114221044e0380148200c01084120080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 299646537 1250 299645287 299645299
    0x4061b0605040c05190807060e040b060f1902030903120a030e0d0f030b121213080105160e030f120307050d11040807060503100e07050c0105070801140d02011e0e 71
    0x4881488410f0007250140c0740292084428510f00005002c040d003141d00c80c40c1400d6100e203405001d420b214544061f521400900041860440800001c1554000801601159802140c400302c410f180c81102d5400c11090300243d4640064540803944400e41b442d00d00c0040400054087d02443c406c3d4482c04440141030240c90060000f01d10041c00723a01c0f514241c4001a0030905d0b004243d1521440034465482410300520941001901c0b105c0ca40e04500c0d410308a00040d114000b0702c200c0203000d09807091640e025608030240045001400800241d006180240c1c41051802080c0f000010140348204021412a0302c3e903540e00701c2103c07030348541c48441e0a824107103004c9010341c0005801070000d07140000150b032035007600c030b40d012140340c0012600755409007854001040840c160300c91454000b4407524100c1e2034503400c90500ba080d10025201600010b503564010000d00d6118442c00000010403203184c40082e5854000810749200d8035011200d001c003548229240e82d00070318402d402818044e0039 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 299647787 1250 299646537 299646541
    0x306070908070803181311040305160905070804061a040c120e0309060d0906180b09010b031209093114010b10050702040b0a0b04082104061b0605 64
    0x4000c20354801807045004501c1454400700f00540b01000369042505800d20842c0e034490340004100b40c1a441040c000d0343c040d5604e48002865010f94021720203540250020081d1942c070b080a000c3c400807950000310398614040500101a074421401604260450004a0b45182441c400d400c180050b41a1a500600d08208a2201790308a8001400a401c08508010100800540079120704c2040400c1e540024204060400c0003000c0d40404000c3d40640d0000170070000d2034682ca00024035940060310049007d10400c83d2a050034000c68041c0d050540c060044101c20001c8081e141c0607174004188564102e00c0010741082a041d07804080c08100d10103070407941112881d1411002d8030b081d0a03600c00454004a04c03031000305010b00e03040b088003d050116010130080084400b6046017600f05d0b409501e42c1c42900044d9a004400030103080d985500c2da540380e04e4049824039103403110750300003407050344101c3d488010201e9406503801c44400d4100324804844821542d9400004448c000f494a131034441 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 299649037 1250 299647787 299647801
    0x1d03070906090b09011202061b0d09090c020d05030703020702030a0609060506010216120803190c020c0a06090f0905130501020a080f060118060e06090303160c12080d0c0507020306 79
    0x3100c0c0c100c2e00018070801140c0700c00c00c10300410160034041ca4035101e04c01c03801a001414101c1c001c0129544900e42e04c100c100d008000c050900320141c2e840d10005003140d00c28840350b85c8a1242c80140c000300d0004141441c40b00d4400740c620b000080101003410381c042000015914240f0801c44000ea001004111483d054034141e402800103643c02d0f8010b10416411108543d03980d06a803003a01d405d2400402c880a007a07035542e19550004003540b0400f40210a076001440703250080300c90b0201e4035000b0300500c200150030301030030703101d00d60000c0c00700407a10804002d60b103202d1890038161780310101c0200b4940d0b00c1041040c0c0e00c8a400c603008000e5803000882e1410349620802180c014024041a800f203612001c2c0115840340744400744203400b0288901c20003245000b040458410400645440e04101e140000641180c002d0480c085405600700b0780e20003041220342c80140900700c81e4400d085500d903145c81c0c10500c1e008500e49070402a40d0b0300c46043c41140903009441650758002d0440345a490001c03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 299650287 1250 299649037 299649041
    0xa0803031509090316030302041203020d0f0302040f03110102010e0d0905040f05010b1909120f0b062b0203070e010306021305150904051503060907080610050f011d030709 75
    0x7681145140c0000c0d00030300e95490222207143c0982040e0000307600741026010301ca0020020004201c083c982d0800000980c02d5000d04018003950280c1c01800102c00340c0f40001d062402480d86a2081501c1000140500820045050141c9170081e500340321512603000142c1c01000355849901542c820960b159181692140c4800305590303007581d007802544201103400050b03942c00e004800e81c401d005d0200301d000c0380744040441c4032a5035900d002c0700b9550360b5038074201e07540b038a80c0c1c401d43d200300181c0c110380c045c08500b000081d00705200341c440719900169800000c0401051000000f03154103d100003009540d000c1107044051f02000002c0d404c1c95960f841d115000750701080710103601c550520400030300b0385050b84031000407002d148201450102d51004001c000d2a0051008005940c1c0194075515501c041007218440c40000740103106007822f027000c6a14000c4000c00d85440229a51001d000d140c503103000e070740d1030b07941e080c02c002001842c03407820394140b5184030f4070b040e0b00f52160030400903c100c580c1e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 299651537 1250 299650287 299650291
    0x301150b1309110304060b0108191a06030a0c021606020304060f141908060103090b0a090f1e0c080a0c091a310902030d0c050a0f060c08090303090705100c020a080303 73
    0x46c2500b0002504c3c0c0800640e04094111011604800030704030310660b400780c503000020b400b0000000c1c2556060600001a000e130419921803007025074440a28441b20703010090b20b240b41000b5a40c130107800c1d10700b520080d81d0384101c0c0607071000c01029405504030207015926001c0e98000e1040b032262035040c10103850b20303142c410000d20000544400d02044055000303104a8035610380004c58244295118018103010385050310003210501903104211001c0340d4001b40f511121850350142d56502c5659040081c03900a81c0c1e00160619004088058001107046c081d0740100d882d428804035400c0d41100f1800714000c050030a06030400030200668498032030a001c1d5040342255460810107100b51031061008450b108c4d40001c1d003592203004403968080c0540000d42e40e841c400d008507410145259288200c024030100708030354150300c0c1c00c58942d8040d0003800d83d030b45c0121440003c50035480e29081c415603030040c510a550044800510700c606107403150b01180d0b0f42a802401e11803055942d014550350329401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 299652787 1250 299651537 299651543
    0x5060403231e0d26040305161a04051204060c0f03030603210207080d09050909071a04061202190305060303090604060809161208030c070f030c0b060301150b1309110304 74
    0x24000b014840d00000b44c024002d6038658003d03e03805a03520341c3c05441d19801524000d00400e422603503800000c0015151414089150740040c01c0c07824286452443c20000d40b2801c40200401d0000307100541d801035042c40309a41240c00d1042d28021030500350024180c50700003510b01428128000001d2030b241e001a019a1010740c21034000b00c4d9284034030394030b601010520100103810980304100500c5c0c2a840280c1110a01041e211525a14070801e004501c2c1609034019001c00842c0400c4029007010000703034451403100d815460300c0c030540c1481c0141c0241064203800d26039500c0103d10143c03010019504032800c0541016a01c030703200c2d000906aa0b00440b07901c50b1074410b4a50301007400950310140c108a44104160700700c002c0d1a6560746d03680d03810042c0f00100c0c003402480240b0102d000d100100c000503001ea1107003040400b01d0705040786206401071010340241e0500c5008140307080b0011180c1c2c01c44038546601c1d5158218000303900d07101c1041c2e500c00502c8c0d42c2060f01c07034010381c07801400039401144 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 299654037 1250 299652787 299652797
    0xb09011409071b1403040503070609090c0804110907030603060e0f070518040b07030e01060603020c0d11070b0c120304050c0102300c01150f090605060403231e0d 71
    0x265211040f196000003401190184822120000c000b4060158280030f4050740310940341082c1d150004246480d01c81c0d803203140010200300007001601c10380d21911203071122614000d0814a01500e07107800f03110b40c0c869135500a040003400101c10780d110307a200801859010000307005090428000503074400c0610036016803401441c80020b020315109500140001903810402c0c0c2c0c40e99242c6440c50260307001030001e000d241c1c031140b081141d90801c0c8200009001e141d00e00580b10b284183c0454688041c84280c9024094207280710404130344001030310800c8032082d4460550701c2d50075400060811442184440280c0c0010040c441040801305d03440003030240c2a400c903804010740d40010071142a5083d8428070660035005d0000c3c1da07002e071000801164600d000040b407881c01000102003131a2069100d480da20207030030b40501410215004410050200311501401e160440c0ca0380405201d0380420030301c81c45034082c51110b10b036100380a6003405015226004412240f001c014540390441a600080020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 299655287 1250 299654037 299654041
    0x604051c050717070e060312091c0f2a0902030c041206050f0708130b0403090b0a08100b0f03060915090403050405040b0405151012020a230406020307060f0b09011409 73
    0x140d017103418148210b0006004015159400d8401502c0c2da00c00180c03960800110110f480b00f98074034105820002c1d1181090501041c498103001d10000c80f005540201000309584044a01e54000604002c0c2c489a900059a039228400c464803903114940c049020f0444001c0c040d414402c013030744490f11813602c05141e00400d81e2100310031601400c08503414042c0070040f08003100030450040c0180c6d0f01a111f03060074159207031100700740380d1513801125401001030b1032501080240301d03d05400343c006240f031440c1641081c0740380204010b2400300400342c0c0d0289004000160f240e800c1c000b11030441e0200034106490600342810300500c0341c0d2003400b880c0c4c000c82c01d056601440341010301c5403a01ca91072403d1a01649080101044103205d2501401c20801c509010300c00050345d1a880284100c582a480e030000a0162000e000a078a20034244990f02000a1200b0810550088111502103502c1b0400240c1401c07404e00e020010000003648a80002c00000042844034007580c13450069503080720001d10326 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 299656537 1250 299655287 299655299
    0x100804021e100e190303090306051902030903030912042909041104080c091302060306040f0c0c0308010504020304120c0c0e0a0504060506040c020c0d1118060111010b0604051c05071707 81
    0xe40b03c02c5c8002400150b90301c00800c0880c070140c1c030280c0c0046d002c00681000d0504d2350035800c266001694944440d0f040003080c0314046000b0051f0401c0080c00c03140345800d040c07515001c0032a40f414800b680380e801c2000c4444002130101c08003100c1c07040000030020403106c0e00d00400d00816400c1402303481003603c41c4015101080c80c20000441c862404003104004044860b400d102864102412841d0059120203200004540b00d00901c441003c85946104604400b41002011000107a0059000d20703c1007051002040740701c010100740d41c52604006030304080d589014021000168410748021541c1024081c4848064204074007071405002d00f8840d07030302e1704130800c4112507519403c00c0242c0d011385104141c6007081ca80103c500d5000c2d444021101d0710983c0495a0024405240c2003424207000c01c0040035030b08000c01e4150714000c54000c0110010110200b81c0c0c80c031450040c2c510175210503d10001e44940080c01ca541140e0040c143d4404550b105003002c00501442c05148076809441000710389 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 299657787 1250 299656537 299656579
    0x30c06080f010f180c0e1509040c05070c050d0203150901060f170c040c0c1a04021504080c060702060c010c03090c0b0a080f06040e030301080a02040b100804021e100e 73
    0xa0714601e4160100c2e55012441013001861346500c408280409118126202d0755284081e1507992420300752180d0302c41e8a14100030440703a0303001644040c010184000f5010a001030003d00a0b10717026a130310500103001c0e0000038503100c01d030805903442d4010748040180206040d0007080840d1824215483c5894465802d0000c140400301900803da100380580d090a1600f074000b404c441449043c5214202016100c0f000082039100860810140240a03c000c5040c124040f041244541038400d060a042241242e00c0c0c079201e007882c62041d44049211415583c8020072180003160400080150540c50304002d070203003030298025100041a841c0003d0074902c0700b0100cae01c80d800d00d50349010241c3c0d529503400328652005441503030440d40e91000310900a02c00c10056001c0c4c041900148500c201600c1004283c68125803407d006504800d8000c40e81c41e00309040503041941120040125418201442040c0418510b113540c00503110007040801504010800c14180081e620300c03414907550300400344 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 299659037 1250 299657787 299657789
    0xd080a09050325020a120206341109010504060302090106121103010e1603060f0b030c0403082a03040506070b0a0f1e05011502300315030c0108151306030c06080f010f 73
    0x1402c54420404444e00345024004c03415401b1540703044402d440b48046140c6017002005204480c0c05018694ac907585180c01c083e46401414226020310440b4116404518410018030401d028000040310140c1402c00c145c11091050803840d0b041600e03980e445004281d010303402c0e0f801c05901026800c4400b12517210303004880550b4100c41c0020b03c240e02e010070800c1103500c0104001c51403e02808044005803e802c0104440c2c0c0d40f034168070045450303040a0f035020300070b08070198041d6401040100800d45580c42515203281d0095044185983d521410301d010700410f03440c0c10380c0b280c03030082c004410781a03546c007085582405010802c440d03a00c5584400285030105181d0007d43c0c4103031801d94580301c0ea0708440d0074070b00c0c2002c00d00910071240b608044554100362401c629544214083c00158201089440007119017460702410358100860800e1b8800d0074118858042c48050094081160a40d00000000c0d903205002c001055034440f03000309441c2e016030381110b40486220000844080c3d0030b103000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 299660287 1250 299659037 299659039
    0x1020604080301140607020a090b03060a090213091410050a0c05030f010b0f13150e0409030f18050612060120060c2a0106090e0d080a09050325020a1202 67
    0x36181d6404e0038071030310f19a0007403a025a0700540c2001260010b880c2ca4150b103001300f001c90700c042880c4040c0c0c5c0426041a80043c0758001c044e182038404009179540740b41070515440c0a20300040c41c0c40980c182110070028052801e1018821340804040c442c40365442584591081802005014a054001c50707480c4400d40300817002e4807003440180404806c0c00010510040040001d1349030120070032035a881d403911580581540c022417a5003444441d002a020442c1090444041050245e0b0741d4024040740740711903040c01041110951b0720035510486140d10007600c0010b043c540c0b1380c8110418503104040c11509e02d030000d1400e542c0d14804003442491030030310541741000352405650b8845944a50741002000745940c410340c107200300b4242c2c550610208a20380c00740000c140213003400b109000f41c80100c4014026544010842c41030389501041c440d4004440510201d2000541e08250b4918050202c40a02040141c801401440041540c50544600c245ca4200025030358a8900d0702081a4100c0a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 299661537 1250 299660287 299660303
    0x61206060c0a0c0305240103081206011b0506011a0a050d0b010201090c0602030316181202030a050d08090c180f0a06180905070b0c070b072d1101020604 67
    0x105a092418401501201a5031030460360201820384900e500301a003588103480507004902440c821003403100301890440328500042a139035141d661080320a2092070000050540b05070042a5142e214410320022030441124402c000c103010b007041030b2242da00b8070594401100b089040d100c4e0240c414151800c0149548131241010b090100e98070103040031907034081c119541c4048240000b81600324600c050803e0703a004589070b00d003035000328a450a0b9130f8809018060f1968080742da0802c0f081d16441640d1240c0454044203c40b440440e00c0c16400d41c000400c02c0c00b0b0a52100c25140e40140c2c498480c1c0001d408941401c822403003482034802c14481030044500940300084c0552158141d80c42e041240780c0800106947c0c0d0b0803200c2c1400800000c00da1180b52607044400910004021000107080100230313007850f180b003001040b580c45002d44645444100081140001e00a00762040070803a5554501c000c83c41c0091007a40110074445c110440d0811a039220b00300442d44002129440385a0105407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 299662787 1250 299661537 299661541
    0x2010b040b0f06070602190503010e06030c0a060e13020c1c03090c030b15030d05130915031b08060901020409140411130b060f0a0305090f030315040b06071209050612 73
    0x3c1c4400e9612012081c3e485640800c09801c100c0010904030030504659540c941d01d81d4105003c02603050009480f083c8a0752181c03040416a5481103104070840301c1c2d074206810103505034030201d082420aa42c1b92050144042844287e18070081100c010303c0701e007010702441c1030246203010f07011105190805004021962020300010716807030540b5410040300e1504d040468001400241340003221001000000d03000f2a01a01c0d030f0035102102001341048400c14814440c2c91954034483e00024440900707200d0151542d03903904145006134201400c01071f0b054540502d42021018040c2d4098032941003258905000c0060030500d10381154042c0e94400308420f00b200340b400400ca400b400c0c03420400b600907519802810b265035a5002062402c1e10010b8490315140c0540c40501140c8004010300080e402c40f002031044d0060100890368046c6000740941060100d800114004188a9404035006080004c51400780600d40c81e1005107901c090b5148000540c840080c407000307010b590700d40c800705810040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 299664037 1250 299662787 299662789
    0x1210c1103131721030628091b12050c04031209030201021c0507030e030c0d0605010305010501060f020a0b071827060b0f03061315030c0503010c0509010305070e0307080d02010b040b0f 81
    0xa50f0803440042445603c3c108182c01210100d01400c0c0c540c82d407101502041123400090700172501604a81009600040c4019901400c9140500410882030343c0e640002495542d40703600b52030145030031600d20001010715141c0074121100d1030000383d0241c42405459902e10b0345288410b8000d00c034076940c0310308002c820340c0d00b694421034464181ea81030041040f1000982c0350b0001d1000e01038004c10001c03c1551460074211300711401a0882c2003081a00d0607200001034001601000c4694052140e40c40783d525500100c1e07501c454400001302c9040f40190004002d60768250408450030915101c01080e40c4a000d840101c5800d803103440140c10b002d00091a03008884009503509c20400743c4105400e4010000c00710448850300d0707001e6070550070304000b0f20074811140781d03060160001360b000b041201520000a85503000340c00045040585030400109006d2007180098407031480907044448a41e11512140e4035840001e442100544c43c00c00000c4691500b4000c42d00000005007501c18900902c1c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 299665287 1250 299664037 299664103
    0x30c05060a0903060c090911030f1801090c031217060906130209030609030403030908120d020903011d010c02010b0d1a060607050316060b01210c11031317 68
    0x1c0704003060200080001000c01d078113004001d1a90304598407104082c1c00c004441d001c40d0092020502801818003c110b405401c13112115085034030502d0000290341003202c00c03030250808034001090b212050500104100d03c1c0550716414400540f0342040d055500403030081d04080446005078032582810124000b4204603c8424080e08404005407500142001180c41e01d8000d81d8420040c0d4030014040050551060500d0040c0c4498009401c2d9010700d8042c1450074001e40c1c02d032a50f010f0b400074401e41e0a1380d00b540f00d9074240c030700c400c03100e8803a04008070148d0080c4180c1c20504090750030000080010300d4010b0003810703480c3d8081c64400d80405190500743c4802e00082a56070003060411a00380410f070104060480250011315038000d08100b450150181e0701e90700c3c405411b000441e42074500c480c0074020461030540c101000018154511a0100c2d502c08850081c0764060200050000207202c07500756040903543e100d07009011049481841a13503031090307904011b800c00169030680c55451450 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 299666537 1250 299665287 299665297
    0xa02160b16200a1205060f16030b13050a0b041b080a020313050a06050411090103081602040b15040801051612090201020a021206090f01060f03020d060e030a02030d0e07030c0506 78
    0x242882e800c902010000700344161060303001404584460310f86082000401c01c0039552050400b170040800713003004c00d0380d031000c01000c004803000c0c99100c1c3c00483d910b44030452144001c2c1c130b20342018400c504210290748001c2c014495074900a0341408a00500d0844208075a80f07009401c0c2c0e604c0c081603a03541c4254009400c05022118075204000e1444042042005000005801101c1c00140c80c1043e20342020400d58401c1054081c6000d0f40041000c11480d8090310102020744001d00340070102c0e8800900207041c03070001258810982005520340d9406c5a0140007130783e5401000704003544407100c007c0c0050034045106000600c00a840748440d5196420010030540b040c0119401280e182d4000b03070010803044500c0c101a4455000c00050700c00800c00d0b1180c020f502c40c02000f4840c10a40714000d5044140000707406044004120810011268020751251076201d0030740f5150848001d009449510188950543c0303800d00d010189510b1303002c03179501c0444e076014031161203140c07404080c41480c0d00f103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 299667787 1250 299666537 299666573
    0x9130b060d090812010e0606031906080609070602011413150e0307111c20010212040806060910050906040914010c030b0117010b0909060a08030a02160b16 68
    0xc01d1101c045081c600d406940c112510035030341d181c1ca48662a10f08149000168009880082150180451919034004036a04806881c0c100e803500448032824001620032984594041d106070010088161070100d185400d86910354002c3c05580c0c203540c954001c04600755a440702d200b40360b075488800034a8200401518801421000c6000c07034041e0031090540d000360b1020385602c601c10900003440d15014044c1c08190300380d004280c84805054494400c400000009000c1c0c420b500c0d00e42d0803a0b80c3c002c1000a444c0100500d500d95a170b41ca58004075190f54041d0340c240d0144000078040b0f000d25044e6400d10003a0b5102410010300e55641200300700c0988000c1d0800c0e201401e241e00c00082980081c000c03804d0002c00c1b0780380400d08070041c0d40014a020700c221000004564290014003009840038110f4228140807100c24286403206e0001801602c41070b03002c0003007840001a500056500810070038003400000414002c3e9039a40c3d6030090140c80b81c0041d4104d0040404c0e10400001d02c00d582c1c412011352 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 299669037 1250 299667787 299667799
    0xe06010e1206040303050f07020a03080a1d030d0608070f080c100903020415030302060a02090904061d0f070603050a0b0607061109041d1608190501020d020307110705040209130b 78
    0x4550740d20a0704150003a2030030750020b621101084900c046034510381c1d800ca1400d100810600ca103030b4800404030070001d4414520241c40d0780e0070990151607030101d01c80040300c100031f030f0f075a03140215003900050655101e0075240303009100c00001c442407007030702e20811501c50801511038a141c61003000103c0540800700d8050110010000c409070304c44c1e22501411034034001c1004500e9085060191508500808040c9880d004000882080d240c0c2001c480d0095803102001c100e0030014803a070614480081e004403403920409030720142203803000aa01c02240e103291810800741d1600700c0044103030ba8403204465000b02080050100180003a8001c205001021083c642007405500000302130328417080c4060300d40300702d004e0251400842807141419014072500c2e4800300030316040c8180c5e154070a10100e0884512114050400c0c00801c0d0110758612503506811940c030310300340f030014100c403034083c0d01c5481a1007a8040415241014422202060001051034100e69000800d183c06481c15040090f0019 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 299670287 1250 299669037 299669059
    0x91a0606041205102903062a280f0801260703020a062a050c01050307050f1902150408030112020a0e0702012415030b0d05061815010e06010e 62
    0x6520b01c5800800c40d661200c4402e03c0d0132109201c2081342c17941c1c410034441d4100c0c1d4107001c440808030384403801c1140043e285030080d105613804240c0c0e900421480701c00c2c94101d0405a080e9802d440046040402c2e01c2c1c9429201948599048540401c00d0180d80303198408000070480b401084003c0201901130b100c2203c150035125030128001040540c040000303c0d44011800781800142c802c04a240c8185101c22000018941ca51580c9c0c0c02da00d00e40681404000404580c0b01c9100303108803409031180740006651402080d007a0898000c2c200e213444018090000c5081b50318805610a80c051038000c090700c1e00316420300000840e2001105001c907403100c12a50002910480172041c1446641c86800006001900140d155200c100f624514002c6280c03c180601c1480700d11b4088104402c51840c0004d1546102c80201d4001c40036000c002d000c0b84500c0c0b00b040402844184c0b44028250050305840c40201207025402c01517400b8019041401d9140300045c1d5254451041c4007a880c40051550501e4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 299671537 1250 299670287 299670313
    0xc061b09120c130f060501020a0c030303021323040609020901020715020703140c090c0f220914060f0301020403020117062205100b12040204051b0409091a0606041205 73
    0x9400480e0200000f00c2e254004079030548903510800000b00700a0001e0404482140d03030b003441d5000907010050074907a0100e2040c2d1859085040303c03016002105085050f500045424014806209140c0b44034a0510070086422481e500940d560500306800138404c1508140130b50011105403c10481140304154000020601c2c0b0000d404c1501c4000000c0c01c030035188034050242592006110800c005410840c1114894464040b0362060100715000710b0412402002c80d80911030a900101d4207504007203a2400c10100000302c41e0207841c1c22170707108200d60508020300d4240c1c0210302c006404203040a40000b000100b60f083c0380d0b0310040040207000c190555003200e01c1050140d140900d0026584c1080000c0303002000d180c1d0300038050050600303040c9841c541c0005200d0034010310090180391a2408281146944c50310280c0c03d46d0913007080340d01e658607a09610010000d1500c01c1c0d6040d14080e4004d030041c1c9000d407076140580000782041c2c0c5410b08095003100c1c1080e50100484182c032400d034002d151 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 299672787 1250 299671537 299671549
    0x5070611160308090f070803070b0a0603060f0203090d08090a02060904020c0604031e03092d0606080c0a0f05010f0c030908121b01050609180a15020c061b09120c 71
    0x1c240d21948404516051201c407070380c6403c2d8605106041e0394072103582440f4a00c00082540d400d075520240584803070b66640d40c01c1f07014120b254001015581043c0000c0180f0075290041c52081c180842145d61240170300300304450401040d10103048642001c0c040c0070150400300c0080010078070141c000751510300410040c2e403030312000701c40940010f80322020f1840322034049403011417070b000301d840c1c24000c1e41d016031120640102c01c850b1440e080941102840765090801c4000200355800000812100d17a46000c81034440d0050ba03205031240780704607408038560044482c0c0500b40d40040e582c100046040101c01c2d29044c441d0f54094092150040002900f44070400c400340c7c00a00c80c04000f62113a1089041040b03100304c030542c0b210164108401c0115030703181c0c00c55256009800c00b150381688a01e240b540d6080054019003d03010700112060542010101d4005040a4001e202103500d141d036224013468040d8421000d003031204100f0406018185040c08401c01c030403017048260345481d40c00c81e0004035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 299674037 1250 299672787 299672827
    0x110102090603100303080c090f04090524060a09060308030a0b01051b010b10050a0e091902220803130b13090207030309020306060406030b01032a0f0e060a03020105070611 75
    0xa26090f40105200f019405681c071600640707407428140c1002c000c0c0002843c0c940484801d1400355035504501d00600c00104400200001002c82510f00508400b060707295000d002c480c0c030703801a005c803240000c06620705c5c0300711000c807074100d900c00e405c0d610752111300300103419410506410071505000d00a118030500740c0006c00e0071401c40000500c0150101130042d2080b0004580c81440000c4c0485a04180c000c9860003040b4000c0f940704002c0d075142c60212542d200120b034444889440404c0c5205400009140103008460003840c15141903511149140d4038403030b21303c0c0355800b81c945081c20071400c1150b030f0182001d44840680ca4101c641c0760150030049800405040d000281c41e0700c201c40175401c0512600b03401003402d560600c6400c1c2103485210000b481031100900d050015401c0420600e042080409510000b00754654a944e80f0383c0c02c06100d003c50701400c5190401d140c0800d03442e180c070a42c91800c503541070311002d04100c1070307448520041488102464101c2c0c0704100048150217582c00801c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 299675287 1250 299674037 299674051
    0x20f0f0d06080d05210901020c0a06091103030c1b0d060e010c030509060709030f0f050f0d02060109020a0c02010c020a0e0c0c06060a080a1203180803011e1401110102090603 76
    0x381d80780350000952603c0b520072040000e00608000f101317a1443c1805c2c14403505860301e120304404ea110703510021b0091185c0c580307214041c029250004100700440d044942c0c0c4902039104064140c1340c0d181010340380c0c07145010403100c41d8013000f0005028100501e252401d184018010020050607807200c9042e54800030066490382d66403902d01c00c000380c040c800c4d1500003003d030000306524540802b01034251851400064080644001e0281c00c0006451060800b2035000301038502e42d510b9000080d41d584080b104903405130140300d0020030181c1c80da10030380c1c8031040307159595186451140c0042d1400401c1c040142d805c09251203001c149507155503011030245a400e078200d90b81d100c4010340141030250140649100b06298142007050b004005001d583c40c540244101e00c00181c0340e041035004000d400303040c160302c1c03002c4c172100030900c58642d01460403600700b480c03041002440162860403145940c041c0780055680c11120141a502c00c03100a200e002d100d00005240060620000b5056001152a8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 299676537 1250 299675287 299675291
    0x307030615090b0f1b03071a15030a02090718080303060f040b03060c130905040602180d0c090e0c0d080702010e09070e31050610140706020f0f0d 64
    0x411040341a14100a250041ca00d4a0300b801802c00400c035090348945111090380d8200031401051003400d0070700f11200d036200c14044079600c0c01d46140a1000c1860001884003908049001446003011480004080500107014051500296003003015042c0044e0015080106403000f21021f4059507500d40c0c090800780c2c000390380b030786000c40400c222548a20100b60103a414010005483c1d20f000460507089034400d02c441d07440f0ba031000c0986c45600d40d103a2000980314285000e11003446840d9004000f001c100004076000480e0110a0080c000c8000c3c2c0f0041844000c40e1040100005c1540702c3c0d0400424801074035100c20700c200001e581c0c6900c0381c0d001d580c803080000303c07003003190b03000804030390611011f840101842c58904000340a508590b2a01ea010b98864508100901e8104200105411072240c1c0c603854011080041002042c003202e4075030148544a4091840d1405415054008902c9030781003450300d052507071850040d4002c0d100c0c0c030105d401305202d064400ca402ea00941140f086800b80 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 299677787 1250 299676537 299676539
    0x30c05120709140a060e04050402040b06160303141509040201030b18060a090513080a05090d031e03060b07022b0b04050606010f1e09170307140c090708040507090203070306 76
    0x10f401e0404540c0560340d200c0c4040300d00401a117030700001c00b665804411540001c05030303168008100030340108100c19a0040c0001100809030744130a0402c54011302aa41c20814440e2001d05501c00f28019109030221410f4003501a18034030301001c01d1640140706150200e4061290008100c2c011035808035880407510000c104080c1e810300541840c000c01080b00203000600704a040e0001001000f00050b1000c070300050344008440c000c03401c6904509000c3c2c030720760300b049032030030003d0900c200781800403c180b40c14004050103a200e8095201621600d8034480d103080615400c11030b0140d1021403068108c0d540b1245900e4082502c4d80c9a0940c034010b1121201a00c3d052610074204440144500c3c18030032420ba40f800150341c02040c0e191800042216404207040c0907100303881840099014580b06e00c84004e5226609001002070103006104005109900d0786036110280ca0390000003046410243e611300052080f40300e5624a60458001d2052b01c101c580c0b0b80c5101420b0381d0003180c003c0d0119032181d02c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 299679037 1250 299677787 299677799
    0x31202210c0a180f1203050705070909061b0806010309020a03060515120a05030313080c060405010c030e070b030f07110d0216120c090507030e1c1815030c05120709 72
    0x2e2510b06081035054040d0880c10100c02101d10300711800b030101242021700d09141018000c000710307051941c12404480c011030382e030081d10000e00518502107079007500b04980803000d141040248011040035844100b01550b814004400034041c203003050ba44880d0b102d4001000c030343e0710311549010342c0380c01c0849540003003264144841510b070a00c01d1101c99020182620116074040141c0c0c2e0080c40044c000c810900843c10500c030140200100041c65010b904140000c01c00150f004601201d071a0324103100505035820f0140d210116842104142002007000030381c20b0140c508096400405820000001c540d1240068640409200950050380c4000d911250303a00e40450850000d241c2d007107001803070710300a94a00e99800a83d00c601c0030003640b9070b400300d4800c50194002c001e00c40c408e84203d40078903050704242c00c400e12103c0c15940114130904885801485c652401206507102c84103401311344190002d040380204421440002045801d05c896000408000c0c141030282c40d165641ca58203504280b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 299680287 1250 299679037 299679047
    0x219050604020901210204021b010c0905030127060b010c080f04050a0b031e072a1a2208090a0801050a0f0c090603090807020607051006080307031202210c0a 69
    0xc0c03c81146a05c50003042128802c1500c400f04060303505480261316112044619400680050602602c039401c09103a80203c2e580b05c00c2c0e190803200120024803c00d2122a1b0342000c05421408041c00c461070f212000700450001e80003100d6080c4185000c2400c103015455818940e00281030001d4144400101080185003440c00c5034090440d91503031340e145003080300b05210100800600d0203401d00c0c4000015503494056140c5044e0003400c2d000a005032545a01004600c0760440404c48108107a454001c10f00c460220685d885819041b0507591003d86049002100c072111347d41c201d902d460704001c40001034840d00360302c0000b03000d07000011585007803403e020ba0036035500c00e0165080d00c1c9489849945d041d8019039030021034207503040000c0e02020900303202c0c03139a1007800c0010b508040c00107031140401100107000215900e1514007003209503105d01001e902c9200ea100060b00103000f9003982c1000504a0b4001c101e40985264280407900d140100f4410411040302c01d0301c10401d0104d0012203084e046 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 299681537 1250 299680287 299680289
    0x1a040303110315010c0606090c200a02010e01051b010f06171605040e010e0a1b0803160b060d06060e06040f0209063a0c090b18100219050604020901 65
    0x2103400e9402c501d0010200781440b900490114100000007008006015040d803081000c1e06041c10103000848000b03002902d2944018450810705030780d00b04601d2009400f2035001c4180da4140e50b64100700d0041f00044660790442c0d49801c02c440c120076003c83c00f07503400f4814002090541200481c4540c50040c041502400303910350340096402c00a07034249c0b107040c403d401c841520000c40d40004d03a01e0fa00d090141c01000c0b002c1d80b1180c58841e0401072402d01c480c182c00401100c040149840360036848408454482c000c421030250401c1004c03c051002608410141358415030141268040c1f01158444406842d10303540245441801039051041c2401c0c203001d00d105100e400442036107805c02040c0440c095116601b0055038030000180300d613059010760300c50307410700f078100140d8980001d2114121720021300640412002250703852000052410324001900d00142c060100382c0d1700c00d951103060118403843e6100e0002180620b408a60780480c50303039a4004400c0c010b4000303081e289000c3c414400d84581c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 299682787 1250 299681537 299681561
    0x5060a0615080403050d0603020a0902070209090d0203030a18050313091a0a03021c1502031501080906060108040305040f06021f020412030e1f120507030515060306030a1a040303 78
    0x10088800369000d40000c081d070f0300503506203420765560f000944035900a1080b03400c0250700c41440c24000410302850380240503000c2c002c4540442586408604560703955604050602581003800043c10031462540844001000d1045000e146c0040d51b0324035013158403600910035110a000c00500258a0314403510060b00c0341038070390715044c030340d00000079280603660f1100074400d01d00129440c014540c000e036034410107036209141c01c110388140e0300c16030b000e03410444040110b1000c036191030405603c68013030700f4010351514000c4d202d2900d554004690581c401042507040c0182000002244020705410030010b24250b4050710281000c943c49611803044014525541030042c8014801e82e800810f000340c0301d0b03a1504041a5503030080c4080b81d5081d9040d20344850360f841d0106a5190240c11801c400b024400081c410030041d500d070b840690447e0415200808410080c0303825152a05080004541101c40201101c01465032a0358400f07406001501c0108004003660600c020103415000309421025 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 299684037 1250 299682787 299682809
    0x80706020d240e0c0f040b19030b1503040c080316060605060307200f1b0103241419090c0f080415050c1606150906080601090203040302031605060a06 66
    0x180c024040c144010700b5005407106070703074018003040003155000121409031543c102c0039034036030f82e8501400c41280c1100c03075040c11030b0403040c20703085006100e4810110fa048000700700c001c40a0071400c400044d900001c10464a401551401041c2810208090107401c0c041480c40b07031841c031443c0740c041c05643c0325610080c0202c80601c10f00c0b0845820605003001c10302c003400c0341c03d910b4881d001507600e070038816a80c00005020300c4182c0481c00c01c2d0345005507500c00080c1c800f44103079020403c403001c100450415a04048214500900c8140108001564150b40051030804001c9694001c078a0b031070840c0d8040100140e80d800c203080045d8126007242c000341d9860412044615041e10f911250b0603030030203600286540c0c5c100040543c050b0a0035507103041c500300404070030085e00786400b000800c04280c2d0262409100180006c05070954080c0c413013a2110350025141d903900e400001c0c4065040580204d040d4001440038514040f10b4100ba00d201a0083c001040d82e0304004820008540c2035402c100d660403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 299685287 1250 299684037 299684081
    0x30703061b0518010e0a03120906140a020703020123030108010207050705031c0e13020a03050a0b0a140603040f02031204031a0f0f060102070911030105040e03120f0a020403080706020d 81
    0x612401aa500c0f096828200340803100c06120010714030340c0780c81d08000c00d44d00b00c2e0b022a8080e607901005040a481042d02c801041c1c012071a0f0000544c011401c0000050307003c1d07803042c001035104181e0700307103c0180b1003000d600c4414680d02040d0203400980200509a502080c440203000040000400600c0182c015100c0030044245071003441007410303089410f001c1509071107181d5450344030010720340914800086480b00408ac0d4001c2c05000b080d148103281f00d040c5601a44117203060325010003100c2c4039200c3d0101c0c1403086400e0000c070390001007040d81d8607402c4129003005a10706004584c0c8000c0051080c070360303840c158508080300500e190441c0c2401d0024500700035540400000094224100b050030f41c0310b513645c0100403454100b10782c000c88152400c080b903201d0010b181c6005141620760854050020303a9441c070445660780100d030306a888000034840800c1c41c040b0801c0c0c4080e0410203c020142c68192651a43e244c564410700c1d0071600b482d40014030281c1c84049200c0c010284104c20b40c2c5581c08 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 299686537 1250 299685287 299685307
    0xd0e100506210a0605070c0b06010f0c060b040b0607050607080708060913060b060a0201091416051002030c060f070305091b060a02070905010b04030302061b03190902030703061b05 79
    0x244401004021006a481c0341c80c003544800f0458035a5580d8000c905001614010030001d245030391140c000c5608041070000300303600e9070203005a40038043c1a551000c0c2d950445803184070140c1164152907402c02d41d00d030040e1b030954a920000304041c3c1e0060001b44218100180010444040200540100086001400000d41c3c0b400c103c1174102084a02c504c400c0380302c42c1483c500504030195a40c1c0d1140c00014600140c03501900078581c0e00d03014018100c2c7c7ca091200c1c11f03c4d1140104001c081f500001c00e042445207282040185d4a403403641e20440381043d8104824a140950036110f00840c2d002501c1000300466150298030382c010fa6000c05081d441c108440000c45120080c0c03100e91090002055012045108000000c0100103204d03051040f540d50300341044c100c3d406404280c005002c0c510004240105448410154070205c421213841c0d55506003d81d00030304200b0000403001d2740c0703039401030b00035030303401c10170321020b540110000988600b10074130446404890044020911409018203c59 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 299687787 1250 299686537 299686549
    0xa260604052a09010e010611031206040e100204030303142401030b0415030f061407020a030c030311120709151713020306010b0c0c010e0919020c030d0e100506 70
    0x80b01c4201070366034071a021002881c00e10307801d075210342c603800441d80f0000050848824400d98100c1c0d14544a4001c20b10214000e1764030381c8541c8002103034507070704080480c01508003540708050a5210100742e6203400b46504070700003680c1c0315500075030000c1c0e212241c0a020007080c10545821044841402000c00d5a9840d030b661480790300ca178894141a601c0f1105402900c460b0011982c50a04150b242c8809032a403900e03100311442480c00392001442c010780c20f014411583c442c02e001e41000d40013026149001c0d581100e40d0304540604504042d1181902c505d403000e03c401904043e45070322148401031a02d4070000344065940d03804280c004c0e0001c0703940d03042150841017940c0781d0300074044194890360341c01c2d58618a007840e100b03000b5010700c076a2000165648003030010300443e00784502990785030150400115600b0300001340309176201c2c507194003184070036100e040044038007510264058200806041e0035030a40d04002203100d02c09885688030a4440020f005001a400aa00b410003c1d402c01f800030481e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 299689037 1250 299687787 299687803
    0x806070806030106120b0a110c070306110d02030a0903170c0d0504020f090705040e1e0f040212160302040f02030c03040f060204030501020a0302191d040b0a050a26060405 75
    0x1040c02048004110a52003c0d0409400f17042d1100c00b181e11002d1900c0c001014207011184080d01514001c2d20104400d00c0004580d401d031905802425618195203035a0024000400c54040c2d6410030809000a10101c2c005148a0140b8100c000b4084907542001303807006120740e480742c0201008408000c00c001001090f02c2442440e25800281641e491001c9448040020910740e030140888c020043c40d96400340060040e40e011110305805034a80071a2070400081c01d01e03100c100c0354010400204420b401040c0c1c2d81d031242c0010300c1c0074800322541d40705a09000e065001112404010003081c800c0d41410301480c0001d10028000310701d1443e082d040294140005480103000e6540c0c802600c0c284106a01a9005990440021035803403081000141c020b42c0712181d48922213a01d9401c1c0405030f40101b1100d54000f0181400b0600b23400690704000041060114180d031200300d088002c03e258071170b684498090310039000141d041c1d00d41d010342410302c68142c0d00c0c484040e5004400b000700223036000c203c4c25 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 299690287 1250 299689037 299689051
    0x1e0a1403010c02150a0903050d0203090c15070201090e071b0309080d0c0203060c0703050d02030f010303200c01050903120d050403020c0306371a1c080f0a0903080c0c18010806 77
    0x2406c0c0a080c5000c4845114001d4044003040c004800e2101400c0d02045c1780c00c620408680040b51010100c20140c0d460190140103400310781801e00c1048002100f2601652248051402100e1042810401902025a030340240d0000340b0b007000034403880c03000701721046204d202e505000000440590001c0e550311401010070010280c08210740b000c040c060300a80d42616030841e400d640b40d142c890305a00d14208248001c1d0001100344101002d800c2200700c020740c580e007102000d000c1e040064401950a580605100c54040c42942411205003c586014200e00e41503a2400300301030a190600038039120261140e14400e420800c180401c1d18000001e204288442c000016042d01c0e00d8803541c8481021006e030200950700305030000312a003403524640f51202800315620382510001554181e01d00c0c0031260f0041000e441080002c00c10200d21015002c14075551904694940d12076444c41c0d050340086908c80496448507001e00b210f89040d2330384030b82c070041144181d13109616001c00d595465002411123 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 299691537 1250 299690287 299690291
    0x1206060c030c0f010b03120a020c010804110a06020a140f0d033605160f120c030215030a0501230909010e06070f0801080a020109051e0a1403010c02150a 67
    0x1400400d062080c0e5402010640545408030300190426000c0c0001005952080c001c034596a1452003000c0c1c10790b10aa0324070b6000b07200104861005603040d8501070030a450803d012902c80d507039956501c039201c01601c0207034041c200e02070701840c1512182c1c4194101c0300c0300e50007104000d5929803000581031060034103490003003070604600d1030020011050307410346400340304400d00c4c1403c10380c0710840da4081248205e04844404458000c4031001011500410101a811600c100304e094801c0382c045008500503000282d51642c0c1368001407112410003002d4260040200800c0707402c00b03451040c50300400040a91302600d4880c58080ca44403081550010701c100c4259010a05c0200254802d05241c0040b00440f58242080c01002d031200f0340c3c1e80501e10010301c01e20f002140c1141c01240300c001207981a10364a000b14140b50802141c050f80c40c440054100341d441d052082a076442c804200145451911070f100090318a00f0705007501c0200c4007210a543c4528403064040420080465010401c0800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 299692787 1250 299691537 299691547
    0x5161407210c02030a0c080f0105011a0912030c06090d0e01020a03050c0a0606030813050d261e1305030c01080c0c011103040c050301150f06051e070303050402010206010b120606 78
    0x105488841400c40065014452030800380c0c1042508101d806c240c0e064035003103484100b6103007419401c0c1c400901030240e1103209460003803000c1208101801c07804500408030f031180014202c180c2d01d543c206a00f10442075102c6000e002d02204140044440082d0600d00741d514610442e0010750780d003010040050820000180c1ca040c54a0240448618154004428021180e40707091040858002d80460f503192810403100051610780180f482d01c400341d06c10300b84801e42913451321749100015035800083d040740b0204400d0503a40c4421609030500301900700b55a894513a002018145000c00c0c4e000903010380d000c4004150103a8004030b4403076101e581c0700000343d500c816a07a00c66000d401c00c03c420030002c2c8000320501003042b0210f141602910b82c2a4020014208000c0c9508510803e52041c2460750802034828031985108078010407075081e10020402200d030380c1c0400758620b03901007401640041c1d43c500034042190f0b0305000941c01844080701003804c181480c40d420589580240442d480380f20005a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 299694037 1250 299692787 299692853
    0x1112109210c0a0b2a0a121b081503012003040f1704030c06090b090409210503090d030603081602010c0f0b150f06090648060f0105041a0405161407 65
    0x45030740820300862300306880300110320000d0000c00d015185000d03001d1036200007040c90b0030140706400360301a4051804880401c0c02c4461030140d40040e0080d0f035003003444071048011900c2c082271750194541c00d0000581d55455030502d440a0070945d00315004015078614200310280d040401d665648604540c00038002420340b5004103050320049445c01e4011418400200040d001006107118095885c19242c0c11404288220b040350114000140850400d01440f41001d011041c0700d0211441810300740400341280d2962070781c15007420001c40325408500c0c01c100e4400a018042e030104442641e10101070f03144a0002400b82c0982e41c01c40d030007504080392280e00c090004941c42c01e2401e08506900d55031001c001e05003e10003181103200605034950385c4011003500000b8219200701c40450b68100b0590921081201074801c44254800d1082e00d0340b0000d0035a41d4611455006108400403241c41488080d000307001c00c101900c1ca8090764800f40b011b900880c82e402d10442250441000240c85410090 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 299695287 1250 299694037 299694041
    0x18020a270e01060611010903050a0c240c030b030f0309010309050114131b03020a0e0603030c01140105010207050306010b0304110a0801112109210c0a0b2a0a12 70
    0x303620881200c0c104074008204041c10b602080c103984903540e45104a03190001041c3c04d9130203a0301c0050014404005210300944102c2c805001c491041045004401461034800f00001400407060044e40e51a20344044154143c032911011903030550103851020341301a42140c0706e000e0454020305040e00e0303146420400c0401c0d4002c1e62101c004000341f2600d0308002280780305040c0c1c0904101da40200f10410309210104175843c0808580d4000d0213010440d0030040403404850000d05110341620083c00701f43c001c13010070700a000c4409044d8442034a83d40c9001300080c601341e401d62205009030404001030000552000c1140d521903000f00484812400c8840404d02d82c18480d80b0462180d483d00300700d00300f102e000744010102c1d1995402910740360840401e10107070301001910708194980c0171005030100c6126448194413181c10220030710782000c0c5900009824a002a101102c0210852040001607554207000c89881f19402c108154859854402c2d080144215010a401d101034060900c941018030303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 299696537 1250 299695287 299695349
    0x4120e04050c040503011d0601050f0111010504150b040b03060f060d080a0809101a150f07060518010203040201050711060906040914090d090311040f02070c0918020a 73
    0x1420400503860b00c004810070542060003a070b4469401c0910b80310340c81d12100c0320254141c0313000028007080d908c2c120170490428030700d40d2807605000c40443c10041e0f503c02032044a101d10302440c209481d00d0b000b11400c1d01120160410340e88034a150201c25a515240010f40541c046402c906039180d40d00c4520015801c50001322004058010014929207400e42c814041401800d0304400c41d45c2e1082c04019010685500c0034024403122500d015844192074803010b04e0100312103407105289003101354046000c1d10f9010352420345143c0c0e103034000e1141d4040315000024800408030000c50a50910b41d000034898070440c1c0c400340c12040700c10007005460303440e4002c030f42c0100c9c801050169182e5a03000303018040c0c40c024045900e80b60800380001d012460210300a0406103480d9640c203260b600710b944088517261142001600103580e8003424030307905158801480c5031801034403500202c900d407c21903000d41d800403c02e1403503482d40c0c202e0100103031680b0856070155005030418080c02c90703440f8a50351040e4a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 299697787 1250 299696537 299696539
    0xa0e010204080d0206070e0d02060703030605040f0b03240105100e040c03061d07050d0f0b03150f1b120613050123150a0e06070501020d0c0306140904120e 68
    0x1000034001500200003a24031683c400d0741d000d8803801d5a0744101a00d411510520180d0020034282e03c4000628160780107005180c4271341030000c1c22585034404181240c803181c0e15103030306540d076070001d525601d4104500781080c803180000e414643d15007a14003c980906218950103000c0318518400d03a140034030800c9081c0d1801a004003d0070f0600400100a400c1510070b1900c000c070140b06080c0194015044a0710400e43d54555529044d40c065032040100218080031220664805410900355000c2c055aa00b50030214641c144500700000044036950000c1c0c04881e180c2c8403030751107100c21070b440c105458068071115a885290340e100c201048102c9600703d000d44009240c00c00100c1d2001d03948070740e900700044654191020848850030b108240f59645c100519055040c007080d85401e12400361103480e854090000c50500d10250350343c0342640c009480c040140c580307603094042403e80c144501e0000300b1a201403511a00018004264218406080613004241a03404250064007600c000311248074 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 299699037 1250 299697787 299697791
    0x90503070615030213021908070e0a030b0a0513030f050a2007080f0a0b040209040215070501020903100614010e1203070f020906030106030b070810030c09050405070b1c050a0e01 78
    0x503400807882c0a5076401c0c002284600381c581c07031414039680035100350b854591041000c4003048041c61400c0d548240014200810800004406091902c0c0e0001d1100194464080700041d4101000000c0542d10300a1000c0c1990740c500060380c0c04240c1c00500519060002c0c00c15503a0b070020f80c40100e0301c2407540100350103034086070f901b044c81159000a5950440f5441e0083e60301010f01d481102da11a0f0010381c01030101d44900001c01c0162414558294000341700410301824920b41d902031403020381000000340c502d0395010681c2c038600c0c1000d00001a0020441d642005524203003d081000d08045070f00e554100b211000680e100ea0f120b4080011105001c070f0205c3e034482d507040c9841000840000300c1240a007002c41302043c11410140a9841500c0d440508072995555040f0b0440700501c5c02800342c000d042101c4400000b150702401c9102c0a0904080d011440d0b02d0a420039510740398242c1d210504483c010030040c1052035a031840c0c11007114156401050f551511200d8002a100d80d8031075403d654 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 299700287 1250 299699037 299699051
    0xd140d020415030e07060c060e011b020f010b03210901020109080d061802130605031b04030b04020924040f020405030d030522030203040302150d091104111c0905030706 74
    0x40400300d005a80b9103140e503024000284018405034031254144100800b1a058280c1000010181e4001c96100d44000c000010551300c0010002443d045802030320b00546c03c029102c9030380920a0040c0000e0a00c1a401003004495250401c80e01c0b2400f080c0c0581c0080c00030a0340380b8203038400c1d000084015004403c86840d00105034228009100f0351180e0928818100310044d07402c030660080e120314816182440003103074a060415030300b81d400107095062075907200904c0030744c1c41e00f0360010380061409503050381c0841c40d15106000c90000003401510181c2a00d940e003c1d44150015000038010701d0517075011aa512100d05043c1c041e010300c3d0001641805606071124001e98164080d0f0711032800b180403c1d000c514252010310248595541c041e005800821090015042181c0402c25000d40480311602d000c0010038410200d66100700100d82c0b8021600034204280b40c0f6000d100800700c4602e24003407034424090054540c0002205e8101d660544860314070013808414010b492021760800700a00c040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 299701537 1250 299700287 299700299
    0x1f0603050a0606031104030b041a09070509130507170a020405010806150a03080915040902030405100b030d091502030c06010e0406270b04020307080f15180d140d0204 73
    0x5814101c40c4100000d20380b0200080462090003482240919046510724140c25034543c400c030f8000c01441540d046841102c45107150b941c00001a10407000e202c00f6102560409040046030302001d003c8100c1c00d480c4095150114801142e950101c480141c00386080e46809030203030b410700c482564080d601602e441c0001070f5140e0f0204000b485a80c0701d15170b554002c080c03030040140d54035a5002c06402031809101d400300038200705150100c4040c3d010b100710b00309592084400142d900840c1c040b11076400c905940400702c0030a000d51420808107c1c00f404028519a000800800e82440380031802502c00d40c1483c2818001d008030b40c141e104100c2507034007d684486000f4080b840544048070014901003095041d0001d500405100c2c4081089000d031244081d145c8901d5040050403d0381e15000d040300c001150032042080300040e40c01d210150101070140320300c050700d0990080468170b039141020381b042e0004001040c0c581c489100da04004403621118202450640038498640c000148009004206 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 299702787 1250 299701537 299701541
    0x103180602090406062102090d02040908120a020405180a0209030f07030b0f0c0301060c02011205071d0303030c091309170304050d090b04150c05060f04210e091f0603 73
    0x14580150380c14810255a4541102c1880341441b221419000740c1460002040d000d40040c00d8072a001000c070400503110380c000070201e40c1c0341081100da00c0302c00078001c910f0308282c400165000f0b0b43c81c482141014908008184148082101c8403402118500040c055a415606a9a01050180458000702c0c0c007620141e42c0e030941d5000031395482512000085010a8100c002481802c4054102e8116440d0044c1a500713000c820380101e05001861004404030401d5209003841050b0980e42d1080f040c4003e0601808690034500d4280250000c10070040300c0d060b500f0844184540035a4800c85441456400d07100806140b4401413440031441d41c3c0003800040140918080c0e8003032001c0c0c81d07a1001800f8203603003680407840b40060020091008003e01c150907a02d98a01007404e05144810801a56941d801d01d4000c984101a43d401d017020b100a01000342091550414501c6240c840b00030343c514081c02001c02c001600f8821080c11000890b250209422100e0342101c038210112520384521010f40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 299704037 1250 299702787 299702797
    0xa150c030f060915150e220c050a030e070b2b0923061303110f0601080304060e1002030409051003120210180308011e0506030115020c0a03021309020103180602 70
    0x5524110b00202003114003800d48100d503001780e5a02c0340380c0982e002c2414000c02070405001450750303000f0b070802c1c1b1803000300320700a0100888a90f51000c0da14000141c0213411a4000d0050052690007508140b1407502d04800322202145d2200340c4904111200610403841240c40490002c241d08124101003004509803031304181c00c08802607001d0f48100160007981d11001203230740d15a540b5103100340c000032a0190a0440d21602c44105440440b00d103c5482c503d054402c0e07100d180250700000d401c01c0460b500c00480b0261440845410001440203040290387c1e010700d0040780f1382543d4900114107511882452407008640c0b00e84514002101030b04040c0d29210050355034820f441c10f000c0781d601b1900602e00c1c5145500d030701d0384651354503900b019804280d080449600307a04400462b000841c0720740e41c0001a500800103602000e10001500c80c0c0281881b2140c00c0c0240240038400007070005a5a040a1500c0c26681050024a0310b03154001200507141ca8424034075078003041103034041408001d400900e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 299705287 1250 299704037 299704061
    0x110616082502030a2d050703050c041401060305090118230705010f12060305012a0e010507020f040906020d0603020a151e03060803120906090a150c030f0609 69
    0xc0440c4520200103801c1c854039210095068000c00c503400006290301d1207004049040c9401c8400d07210b000340f40c01c585030f82100029a1140d001010030000c0040170001a04c4481d0240e50600000f1501c60181e41e4902c011b005100c20315417a90300068485809510162a110b0300f84480103881d0305600300b0460300d007001c030385c8036422495440c0980509400022840129541a51841d40503107001b032045412402d680b000000d01c6864000000120300c0c01d00582000070204666030071022288040c4c03505008801c81994184034402c80307940c4203aa04901910b00340394040e151040d82d069481c00003001060314050040003144081109150581944c0c031441c02d503031099844150898461458920403c42210f82c0d82c001250003801201c03020031190006111042801e003c2240c684030f070002d80c11500095144140704441d04100520940200403094000340303400c010300121440ca480324203240c81130802c61442039880d41101540075100c2c3d40001c40000d0901410800d640c0c85520b4500540480100c203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 299706537 1250 299705287 299705317
    0x201230c070303030506010f02160b0f0903071401080708090d0e010c0605070201150f0308030103170c03040311010807110706081f0f0306050601080f0f0a0603021801060206071b11061608 82
    0x80f10b2381c00052100c4002503081c0d407400c007a03072800348111080d500c165021008820103101c84107464408100c844081c0c10040340d80d0100c60000c8000402c3c1000080c019810004000c041c0710301c60501241c00c2e51410302034a084400c17648406c0050300c0310100e443c0e000f802d03946408100b000c4503a041d800280480085542003170780b03540d541807074070854015000291038084200010000281920f0400080107110302516080001500501d0300790b4029520603602e8070210410f0300710799070f0700c41006540003859086c20080410100c15035583d91100c0e00440040c030400002141c1d0948103200f505d104070402a0425a03400e0b11085580700f1160288001c072460f500300741c0072542640c026400d82e44102c2d030384880310506a4480310895151500580310500c200d03510000880562222103218515086014586031294904940245041d40041c401c108118080d509882180e00e03000342135000c02e8120300c4504500780e02c0720020b0b84500c102003451070640407044100301002030348400b902400580c2064 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 299707787 1250 299706537 299706557
    0x61b0705040c080f1b18040f050f13060e0f160b0306060a0c11090c09030708010e0c0603040204060b0301080f210409150f1202090109090201230c07030303050601 71
    0x140300507500000040404a01000005510400070f401100d9201703d8075001e4400d02021034a2000055021000381d01081840d110003c0c041d003000d015090000030f03000000c102515002d420f00e2144c40001e08041401c001144444040c00180d03041814000741c02410355240310084a00036030b0341c400c501002e0094452114001400c00c81003070580340318003009004d140c9003426420088803404003103a02155211101007204400340ca486031014442c58100764406c0d85c0d2070109040500d004010341c0115402c3e81422641e090303002001c201d4103004041611a0390b1030303403168400a80030b011a6005181000804000043c101c1e00000d0302120035842c10054400e00e118400d001d81214855451120110808000400061045900802142d840113105014a90300c40003c51918131041d0300814804410080780780542c60a50540c40c01420f4400701000f19135860b80c0080c0c401a50031850002d0908041e401040f450305c120125500f440c217220036101b2903a16071034080d00505050700d20b5030008000c842c1c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 299709037 1250 299707787 299707789
    0x7060201051e1602031201090621030905011d0907020604020a061d01050d0b0306070e041109092206110d050702030306090103110f0315070e1e090c09061b0705 70
    0x50880004650040ca0000540e1103507155104243c81488000071031008000c0c10b40c44024017441103018041820300481c025242080207440c2c42074800e100310001c000c0301b9940700042d42191818040300d80c04e081981d110600d03020003010382d049a8025540240e40d01003000b440301d40c085506407140d4400c680d202c0840c0c0d16104103c5194603a001000850116641401059801400a41100302c810f03100850581c044802190034690705885031004180e160304c3d0002d503440c0c5400b5064004100c00c031301e14288100070380000d5010030081c0486207203d1065000c3c200c00301d0070081070305201da040441401031032a446480e0140307502c1041000844c91900005c5403c2a10220440e4080c141c014240b900e039900f90340703821069036040302080c1da2020400c412030704652018002400002c03005440c0100038a48902c010702040240b094452080c070395182e15640070480d884a60b1000d01050352840c000d40d44800c00c0d60140d101d000503035684000041006011525100d031032010303003042c2e002503640c2966114 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 299710287 1250 299709037 299709061
    0x1180f0c080d0c030804152301080d0915030e0d05090901060c0515071e02070e060a05060f0702010c0c0b03060103140903040e04080403060e03180d080a080a060b04080706020105 78
    0x2030701c0040003c01000181c0040780c8078094494106004500e803a1002c0c103904041404c607100d5141c80c4900c422504074040d404140010200d0040280c14068140c071b08401a004000100074043e41095a5905c3d26070300390180700e0341c000c540304416201182d89444c2e0950000d4142d420056100b17208800c17030000411514403801303440e6840340d8844000c101002200024403101070000f0000000c01c60845948100f802040c41402004117641c1c0191202c5410109480f01e4140d000300100c1c012160701c00c0400503505c940c0102ea03494540c2d24003050320740c402840129040000d24002410b4210011808540d04010b0001076004034002d89080007218003400c0b061080c181c0442d020071468000340300c01c004400c04092a42c0c9d1080c8162841d900c0c041c0c40c0c1da9008102c1d40b1a1544a0b05640042945611a0768641820010280489004801d40015034444020b4498664040200502c0c07002007000072290307070850f001030426046403030749841c1c5641400380d460b603503441003030010b40c01c005c08079070509454 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 299711537 1250 299710287 299710303
    0x30510020901210e060705091305060f1009090504150c0306030c05041e24120c150c12030c120504080706020c15041b08240901180f0c08 60
    0x6854440030901250f1000844010a04000380c000341c03901103540700c0c84010b0051380d00c600c4441c1c03185500c49001905018108910120400e01c042c80c00c02030088980e01c800c86100d5040d811591140060540da030121504080c96201e02c1003181800240401c000300b00380d001e034491840d854100f041101c1c0e02c6046060382d0035444040c04003035076040c0602581c01c1c40e4105061501640060300d0b41d8042590340301d0102c0e00f00032981d08031051001460b181c40340c2000411030042c14600d1110310000e1568a981c0c403060554411349080596a0307a40d403130100c0c0180c014400300340c1c01481c0351026041380e54014001c3e0092080c41c000040080c0c41034086404144503460207070b60424011402c01034646c0c0d55000941c0680c0f04403480d44a14020113903103100c801c0a01c1d2141d44141040026080c24084400303036207400ba0484440ca801c07810140f90180c281d8140c8012900b01d81070654040d41b6840440e9004011403c6210768155070b240c26081400402482d200040c1e200e01c1e00011070310b5950404a40303070b92036 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 299712787 1250 299711537 299711539
    0x1a01030c03030314100b0906070c0b070512040b0f0a0c0b040501060e070c0c03120207120f200d0605150303040902030609070504030506040b0604060b030406140f011a130806010b040305100209 84
    0x40d40b0042c480360708100050308080e200909500d00c0d10400f80c0354ac1102c0320a13684203500c00c070000110f90040200500104101d14405006d007401d00d03041103420798482c05035191030414100c001c906030b00c00d0303445804000e44640c0c0040284080741050309026001c0e200a000d082d000c240a513011412140c130500142d00410b400503462031401d82580d0781d5604070341c00c0c40511401c40c801d118010907040d00c07160280600b94442c0d10144451196490034a1050f84a420100504d5001400c2c1081070b4448410000e01c0941c03244000446968040c195410b04158058494140c4004500402c0b10003050b40114003660003115003502d66925400216214421030000415a8102d031000c20001582c0c802c0d0903400c414014004140140c80b01142e1030315400440f026909140c9452440003060565040b07281c01210203600c046543d030611020440b0003040030711014004c000000d5409405c05000c1051000d014000c054071020b5940b04c00b0700c40590054042560343c2d01611458a050030550320888081e420 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 299714037 1250 299712787 299712811
    0xf0f0203040306020f040e100911030609040807022d030c0d02062d1818040506150409021020030a0f030b0d020406030606061103030907030f1a01030c03030314 70
    0x1040d81d8604004e900607240c41c1610010074040850541407200400e8450000041180c144501e0700321140c040ea44030541d1000c0f044002c105101d07107602e543d10010340c400d801c00700280e0384100d684003040000303040303014240480c886607005100b614400c80240100e140214211968a54000204001c2ea58101e000030760100c1d08100002c800301441040d011003405d030b4511b5489107484c03404180c0ba1944400d03003e160f45054016000c40e82e2034030f41c1020005501071480c20781207107401e540e00f550310200034001c6041124002603000060303031240c00550704a54050700d200002c402c000701c060400c007540e07a44503035204048410003200c2240042928403030348450303407032903460001d51030241c00810350580400e030000007807a035100158440b400386500961040b4000101245450001810319041a00648a98008000f0b11541403c000707035280640741c00048814040209103031850400e1054060601c030040b61500000510102001c02400c8074000e41b000e015a5450302080d80440e03000710307651803481d1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 299715287 1250 299714037 299714039
    0x325050312190c080d05071e09052404030503040302122a06040305150a0f0204030f02100504050a081513053018030705040b180402030102120403020c010f0f020304 72
    0x40e114a45008841c2c90904007840c005030070303803150000c0350701c40300d030701a9a551900d092003186030b030240001c02e0034007040e45407801c071104501000341255624419148100c0c1d001e5840a074070110804443c0510b01d03040134295030360340d980c60440d4898010b03200591161620b00800d910900020442c03640100406065001868803600d1410707403c0708440f07800d5084002400040b000034401c200c118840304410b480e000079441c240d40300b002542c001d035100c90079441c014003041001580781c0440301b240340c1c0d045440700040214001c040f5994000e07a801075900490f42040000e070580041064100f903164210a490030740d94011202e0600c03000390754024100d5006851074072124002e1008680d545e0b01c1d110500710008440500c450154102c110804502c00c802c91380038500340380c100401401007800361402e11003107010307000060b12400005074141b0001440b10006045540a60403942c3d03500140c000d501c028101420000e54036400d07945014003007614010035444c201e018026201a00000d0f0b4020740c031701 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 299716537 1250 299715287 299715307
    0x1e150a080103141e0307020306060a060906053001030302010501090207020901090c02100204060e030c040603050606150f07032f030a0e01020705030f062401050313020f0325050312 79
    0x511030794907001c0c806004d0010510000110b0542d284038100c1c01400560315202a80109414880302070300320b07845441c00c00030800c0180d0300709100c0f10450f001c5081503030700c4070700c1c2400141100c25078011002020f40100b8103100c00b40c0d040c0b6003090591740070742d0007040260703240d00e195030481c890100003079802100107004001400d00c1c0d4124401000c40d92068030f40c0300400c4180c2000303030381090300f1440205810705600140e5003810051024a030000302e80c248a41407440d11900d45940014000900030203484004114210001e801c4a40e40ca61000541d66075820900f4000c05540000d07805031000c00216008001c50400a04d03c6071150250b1805145413840715401a15480d03d001c81d550f0542c003414000150944d814000d513401c2548000180c0760b00c0c0b50940b1502050f00990100d2400359080010384100760b6031000c00e0700e0b802101010054040515400001c502d000d00b4030646d6410310400c12104c0c10384000202110140829107490f1000940710000c058403009881c154002c40a800c2c02940700c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 299717787 1250 299716537 299716553
    0x302031f0f0608030a1d0d06150b0403030e1002010c02060c03190204030f0b18070303080601030e01020310080c010c03140904090b0103030305040b01050a060503040f030306051e150a080103 83
    0x31214100000038074035056041c18040c0d4850f50710030011600085542e06405800400410106528048100c0803550400006a8803040284007522050795a4580d08410708600d02140140c042802c8598441e40d81c0d140007400c2c6003510394014080c2d0070000c00e00d62030900500902da42e04405401038011a9100b1f840240304d41c000400490601c09808040b00642c08640300410244d401944280c0901c20346003010000c90b040644072a10302d102601c00480340c0c0d0004100c0205803079051602010a490300c0e001200501005000d4580d294400024000740c8500c1010002c100c1e00040f003600c0c95450070900640b8800119440680862007404c088980c54010100a20205030000c00004940e4525122040042c100342c00450100303a490003403009100040701c109005100c200d8447e1b040b40e041002c020903034000074200a0140020800e0b0808060003500400060b02c4060111044806500405c0b412048840c24090152507481c80c482200316030303242100c8032034031180c40700e00d656469581e541c11 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 299719037 1250 299717787 299717833
    0xb0a110702061b0709090602090a381201060c02180709060503040521041d01050f04090f02040e070603140606160f020303030f04061406010f11070509040605040b010f030203 76
    0x54134000c004010480314040d1141441c500c0c010000140c940a2260a000e641e00868004800f04022403100310103c00d0700003030b00c01200160300e1445544900031441c3c0d0003a4000c2852000100310b1f07600003c54125030081c2940c410318001c56441e00c60a08021141d0503161041d5060b400041c503a060602980d0300800055400030f100f041100c0c9904010700540883d0714110040500380c6d9400501080b55044065171100e03070744a90090807409524080015800992240105004944654440c0c1c00e104000c421007410039009482840b103006011005516121517006210101c0e280c0003141c28041c03d1460050701c103903c09800350780342140d0140c5e41c008484880104580b50711a51078000c005840920203503005070ba100741240603604043c80c0100540c1c800401c1c0c4c8808066030700400c07040348c2c3d01c00380d05206281503040c0a120464034031192400e081081d0443e540000125043c4000c00c681680039a10984c0034000099061346c036044141a800e00e81c0c80007944c541d00242c0544000b000c0160350320 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 299720287 1250 299719037 299719087
    0x120e133804090201110d18080102040605040302040b0d150e012403020d15060e04020423010603050910020c0d08061c200d050a0501110f0403080310120b0a11070206 72
    0x10500b142c0c0c0182d200c2c40e241e9800c8111b00000c01034207500303003001034110740500980f100e00020b600705802e291b00200340703001f10710000c0d201d60340340d44694031103858001c140c6120907001442c0507650a40082503c000c4c01c01403840d1821586403c4981000411044140229130054583c10003514a1a0200040608982410744083d0031401922140781140d220f070b9001000000e039000303118500381c010802180c1c100c3d880b21103028840c880d24035400f11007041040c196451414002800c1c2c590400030351401c41141c0092030305a10020711001201e40000b944181d00c841a034603450709585000900181d940304009800da0840c081d2500d42c0002d18082080241950700c5010240c1c0b900d50900040c0010200401901d0a0300401040344c2840b9003030080fa0307180349404c0c00c080e2422600e1694180365203e60301c0043c010b2403003c800708403820268241c00000b0f08007a01c1e248589590f504081818000645d04198214030301014107014400000c203454a258004007428102142148410001203040000b8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 299721537 1250 299720287 299720297
    0x61b081617030411030d031a010c030210150e060f060a0e030c09070e041b020c040f02040503060717010f12080a032c0c030316120e133804090201 64
    0x541e050103140e401030761046006411580c015020070b400e15051190b0110702030b04040c108080300403980c03240100076400c0b0300c0a20f40201840c005080403420715200c804404116401c1c01c0b14030344a412940d00745000d40c1c1c3c5848456200e52a0f50040200300800c0c0d940c4039812480034007101002500071070500e130030f0080c040d00341d442c0e02c0c4003480014025001120108041203510440340300e03c0c00e142c4251055880f04280365586001841c401035a6a25000c2c030981c496a118000c20101595907010746005040250454440c1e08117503002401811400d1402400080010000500000035417140f6084418542103030040000586404c42550300411104042c50380b038514050140050005030542d046a500002000145950386a42091a4140054401c1e88180210180075440c11004862145d10080f040783c1410601e206540104071090b5450780020b0000010181c0f0020740c00540c000d4000c2e10b40000b41a50b101444104100e8480c0031405002c2009029038182c106070f805170b000079005040c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 299722787 1250 299721537 299721563
    0x50607050706180b0a152117030112021207210609020a03050c01021009021804151e0c030203070e10020304030f0f0209180303040303020d060b0a0207061b0816 70
    0x1250900550200c200c49540501e402c00c1009031192007406072100102c0e8545210b00d1030158104200421822001f2031040c11805800c100050b00581c0d0524460b004406a140e69651440d000800a4944268082e0141e28400c510809000c100b10040c0c0714284c50f100350075134003d40400f0031584100e104a0341d0660390890440980c2d904002c000003544690000d21249000320002030820910481c1d580816003001030080040ea1401546546580d0b061070600d0a641d860605002e074542200140310403525148803100340b600400d401c07c504911451051008035030800b011000c9210440d9900b00040c1e0b1600240c4262404e881e034031f040740c0008e1049038109074490322580344a0100c824100c1c2c2d0703200240c181d0b104604182240c6540045001c2c0c0c0420f44407102140d036900c03440014402810583e00152504180c0503c3d4031400150442850301780d1140c0443c0ca000c4d58501c8135004540200f0f800d00010042654502c506500640c2e01c00121402c0003041083c4081d0701d0b0303448a048403c0e900c0300314 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 299724037 1250 299722787 299722811
    0x8070614030c0d0213050109090207021302030a0612030c0501050c121501050c010c0302181f0509031e030a0e1207050405060a0314030a0f030c0c030f0e040203090102040918050607050706 82
    0x141056000b0300c5c1000c1c00e654903103400980441d4680d407114072518010311010000d6039402d0003006100c0903100c00540d0f2a66962410740043c1900e4002820b450301101e042400e0540c801e9011542502c590002c1007142c40d5001c965090340120003035045a05ca1040010362a018010308003200603106050290a089011504034259a1b200150720000b03503010500103800c0c070604030719002818081c3c54040c1d540306100038513b01c076080704c00042c040c090001044203031504d00f046041c0084804c803231002d01c50324002682585907440600e20500003a81d4080030245446c0c2020740401c241e140000070039400e464002480050200104030795400007030020000045507204051036000e00c081c1003c3d55036100300b290b020704030142c600e0411040524044513400220303040022001d4041d050f040c046600d141012044441041b0b5012284d081400030050040150f015005081a81e480c03172820303c136290b2000046100003440c984041d00691003c00407845885c0078000500840303004200100e601a03002e9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 299725287 1250 299724037 299724041
    0x72d0305010e100b0f181005040f1d0705090a0c02031b07080f0c06030f040f0f0c0503010c08060a03080c2103040606050909070303110f071e08070614030c0d 69
    0x442c045a00d41140120401200c0c482c0310340701d89440300312507242182c1c0700c80c0081a0078000880003020707010714210104030403d41841e011030003028014014030841c4440312132030b400f420940380684d54111003484400c0400c1d801191500544101408140c03281d55000c0d44900540786000f0404154001000300152102c20b250050400440500050503042d02d441405031a0090b007841d44585500403000810441e0b4030302040325003001040340002078580399030422607078034802100c0c014900101080c111040083d01d86142048079130072002080901401f80c003e591003501220b801d98011203c6005000055442018058a46800b07049907050b0404d42003142130b8090403004000f000c0804010802049070030700a51014040c02c1d039160449042c4803a60360750751442400002c0610900d0100d84604660401400c1310203a00181199a1956103082144000161304030700c1020500b80a80421640c1d0002048001c840721942e455482c0341c800350300040d5503003000c0e0107070203090010488110008514 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 299726537 1250 299725287 299725301
    0x9011106090303061503011401180e0426090603180f1009060501090b06120417040b0c0c1203030f0903130617010828080405060309061503072d030501 66
    0x141d0010b40da60706080c8100440100390f09040840e004003000188004100c440090382d0011007030800110340741c07040038034507500c514641000d190608658108000c0c0700c034200f039518890740030076106510004000c8401649125400e8080c0c2c201c9410004140c3c01005494408901540307242a0b4a903401d80e00462401c0c04e42d0b5458082025444d0440d042c01e110700703031048070300410b032001c1c1c100514105031000c01c485019481081c01d14030f084c04002002d01c03018860304030010105140c4070340d8443e2175003410485600120003118240c0718076810f881260600c02600ca01c1a28020700030741c110307030b07600450714406c400041040b0000d001c10303c128000201c039124000050400b5840305000300c4c2c1c224540c03030803005050348044030315440400790300a81001017041070703041010701d2a6a90000001e003801d862074030895000303c1e0803078400020004102404110300380950307950041465400142010150b84036124005c80e000615080c249011202003a00d6140d490303104540a0b0400c07550f00e4640740d00311495 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 299727787 1250 299726537 299726551
    0xf03030e0f090f0717011d15030708070801050604090803040f060605060d050406050714190c0f051f0b03031c0b0a0807080706030911010509060d0603050d080a0c0c03030209011106 79
    0x2843c01030050664000d900004494000c0aa5588541c9451100301080d20550815107a610760180461413020700c001090041600280c100c40202d65100300302c07a655800c078807520a040d468900841c50501d400c0c09000c12003170304000744e5230441cac6803a200d40c54031040c000000c59031156100400a601c0d02e40d02e0182000300148a00040c1c41c1c5001d0030b020050301c00080c414020801d048004011030611001913881d5208a042c00103100070280c1c0066660940c420406850300308980c0b030078402c100700028170315840c0c40c440d80b041403907a02d2400d03030409603200000c030f16503d5041442801103820140c20f20842300c40f103021000c0364019403500816103c44464222440a030400681403040d800304000c0d6400400300c51408100c40e0a00740c070b44034403940d0400304003410041c0c0000c0000e0a580d0304402e41d0440502144100a00e81e03491900581d2450200400030105401d04002006030030540310b5454100400c0d101c0100581341654102c00079407000c4a80e6050041c040065240b00342c0c100062445044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 299729037 1250 299727787 299727811
    0x20a1b0f140a030c030f020a02030610060e010536090411271311120c0108100501020a060c1b0f1505060307120201120c12060602070f03030e0f09 64
    0xd03604112401080d038401c4034019901030b000302c1c40003d0b440802c1d49072803070b01441c00340c0001c1c130300607800c80c1000c042e030340d020b03604d4421881071200c1120304203020300440c1d400c0e44a204500e900d000c010344560052201c20f08402d580105030450820781a98241807050b15070080d4081e912480c400519110400c0e94282c80042c0e00c001454440c5c02c0c010351078000c0700d080c840004000c141e0910000a12a401481403841d03a10080d0104100000c600d104e001c0c21000400110034003603180d500540e91106200702a000500034004981d1415003d44c080b0155681a0b000d0695a18540c6900340948902d010080801540c050301050003c12a11742c0241544104040f02c3c41361281e00348092005c04a0440e491000e10b0103003444907030f030350020b9600102c40c107079120326008172090300044c0c400088440040803540d0a21110481d03240d0b120351000032410f101c40041082d0b907101c44049039209654010740d08000c660020900209014809035003503501c0c020201040d80e00c0d1580400c441240581e0f0386400c02d2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 299730287 1250 299729037 299729063
    0x50a0b131701150504060f03020f0301231e04120f020c1504050301050c0306101b0206160506090a03080a090f17030714030f011203171f0801050118020a1b 68
    0x24908a000b50044c042100c05010b03050a02c4040c403490003007440000e11969540d038011b4010b0707c083d044042c900e5542d84200742e10006400c900c48821070100c65503007288080e0716040112400c3c80b1079550040c0c2d0000d150210713440c1008020759649075050240001d502c55030300210036070344d214516600b0718241c444106848501d44014075081d42da020301101101d007418001c000c447e40341c140030107158900b18a405030811903c06140000c04540c280080d40211001801c0860a00c0308183c6006081c41042180e1a03075648400143c1c40d0b65220000800265204002c00c02058540d0800d01c2414040c2010230a01211662440100303040d4030b1000e085003a020082125103500409010718061f440c00d081441c0d4179048005c0c520f80c50050191105000c018408081070510640780d034003d6407800008500c0c1403c100b003002040850075050030320440c0c40e40c4000328480006001c4d16049804051802e0001440140c544001e500198142810801340d0000301c4c507001e000c14402e400c15801380003000c400d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 299731537 1250 299730287 299730311
    0x3050a0e03010612080f1201030b010f0608040c0320040510050a081203060907050403140f010507020d02060f04050f1902040f0603200a1203020f07050406050a0b131701 74
    0x20303151511910300c6640b4015040204041140780c1516450703005010769500c034050040c20900f400340b800304a20102182002000300010329111a068540510309195050354803101146c4c0002d040324010708025000404100143c0c00308099507521000310700c10120501e041000c1411200b00b00c0382140c0c0c20100b01020801400c221491801406804001d048826201060005c4034071000e0442800703150070304002105580b1900548001c1d40d403001d4621088441041a140e407042070084075203e075441c01c000b04d080d42d80006032644c00204942c01800c91683c0e2161070012040c00200140e5282c041c210021400074001e01c141050190700724181700751880e41c1c4c01030104980344540d4541c01d20380341180501c04540341999101c80002030240c0443d091050b9000b00318040c14032b900c49050000c51050220030950040f0340300d1142440d40c0e04440107955600c04000948100f845440d0704105a2401403040e513100348001c242460301c81c1c40c00540503940c7c1414000407001402100c020f655180444001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 299732787 1250 299731537 299731547
    0x141c050606070203061503010f02040305010510172e0c02060915040309090c091e03031103070f020d030207050d08121008072907030908070905040b04030807020f0a03050a 75
    0x1000041d20400e040c1501507021079920440034024000f505141c010354016a035094000f1909400d0803041951034580c0e0303103011030203040e066403841841e4070500004583c02140c14980d140505500e0028200030200c081582c51340c4001c0c8110301144c1e0b03a038003421500c611240c05203580d20005580100850b14202081da410300203103440c1c0e10303800740411b030074080404c1e44000f101042e6001d40707400040d403140350a01590440100d922813001350301c005181c0348807010ba050a4038100c9002c1e84400104181e4a4919900ca10031100c008003c55088541c100c0035007007400300380900d58070a00480300201e40f9070000071088401540e0440300c84c07400203400b2200c403c3d484c2045412091a251508004e410003880e9925600e860068100a0340044a0040350004006420300301c0d00c20b068415958a21605000340940c0040c0141d6180340324440000525884500c04c131481aa080f411000c2a611039690445003070300042c0c10300c41184075050401a5000060000c040d04610079111a50384142c09180502 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 299734037 1250 299732787 299732791
    0x90a0807180c050d180f03020303090c010c050307081c0204080a02130e0a1b0306050901020d061208030f0a0902030d110607030e0709020f040f0f081614090403141c05 73
    0x4141c604041e001800160444259245003d075800d000c83d04464840556407086045900034101d030b08159514428140c0100c003e50040044000351a6943c03804401550201c0300c400b8024103d900420502010540c810054800600394000c0a0031804850b0301d80400da0f0460307000b043d4940c0001c11041c04601d016001c04009450b07604050005040741e01d409912404001001380500d1080c1c6d054800c50110f0700440350245d0f900c10402c0166003042e15405000390005040610086d2074140c02003240500440c52203550307503000e13055901c1e50b56491034014061030042c01e144805a220b601c1c103001607409000301404106144c0d6081c401c181d10903043d500e40306019145005041c503003405841003240104491069420f03804015039620f80e03160681400b0301c656400010b5641d021500400c0c4d181107032009404032041d18045580030400e21807808036a00e110b00c210032621010202d000c1541c2001d41c40c1c01e600c60300a0803c810006003c0301c0364a0154000099224107048800c100101d175403c84c41026 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 299735287 1250 299734037 299734079
    0x114031f1d06270303060405060103020d060e0612011e020904060b03190b062104020f0907050307021002040605030402040c11070b0909133f030905010506040e0c010e06090a0807 78
    0x1c8420001503000e071301d134440948414000c584980005070664004c0d0111469800300d0b070402c00ca002d50300c144001c9148400d81d20715201d8501440f00600c03443c03050181000b2540f07881e0400340340c0c0d0380d001c41d003100960010030381503082906c034500010055540409076124210f010b441c680c2c4101c500811000f181d040c10310385403149005001841000c01d201c44c11034903214030010580340c0d1b51160300001d403005c0c1d041607000d60f010240a04014016600401a600420b40da0302101c540540300ca90380400d83c0614014a000140c041c400a405403400e60052030024006003040c4510700d1400040e0703420400f43e81c02c2812085030000b450740c168100310403415405080b0b9200484050010382d0303140428051511203505030b0341001ea4041050101d0131001c032400e0840304611248141c4400050040d00e0100000e0b2140e500c0c1600052007414140901a451040d80d000b502004076110015500a0b61040000d50040018000c4c1c0480c0d880b0007081c071003c0c0100b840108800352610501c4810702107043d9a40d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 299736537 1250 299735287 299735341
    0x10912020f21070c050312040e0f01060e01080406291008011a071410050f09060403022a090c250c090504020d02030a0c050102060114031f1d06 63
    0x1014920702c06140c10042203103425105035503000c0500302940c1e001c1244e00b0940c0d01d4002c00418000302000b040c01030044440c100d400d614282c2c0d4031601800d491001748102004070b880e64121034050340c03060f40e07010f901074800c1000040c0081400b00301400d501d49010740b01c1c0b080b118181054210b07d4880c90750442c0380c8003840d1a0000350f040200c429280c3c1000c0b03509001e09640401c80c90100402c5051941d42040c0c20702c21105004044a040c3e4082c000a69882911550b400302090308a08081845072241ea01030f001800a440c0340c140750b060070391207486032a0401c03d0000b01e1040541c0c440140b2400382d2007002105885003201a1700d0329802c0c3c1a00884019800a500000c2c00100c6140b030002c201c0b07000810010795551180003044003900bc10000030b60600500f8144401c21840540c20b42c2912021303400c60303000340e0700d600c07401c0031048002c0d1503650300d40e0240d03940b10490f6900d16007101b41f80d0807000717002c9030740c0c0540680c1c5038555085d151a6429600311108100321100402d01d2034135004011040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 299737787 1250 299736537 299736553
    0x1503030c070b030912161b05010c0b07020304120503070c080d080117070504050a0906050a0209060f090301090807050d0f020102181311040b0a0e030303151908010912020f 75
    0x100e1a0344051034801e007a194900400003400d0a1003d000081c502031052041c2d90fa41c0003502c10b443c40000403003100b11006c2c6140720013002504100040c01e8203076841038582ca045003900740c5038000c1d10134006027030300d04501c002c00000c1154944000048600c0b44614011070702e424180c58504a8940c3c0c0da00120300540c007034101c030540c280d400f41c0100d0440742d5080e1550201101542201e060441a0b000203811505020601c5001b11080e8070220110b070045000700010b481d0364488006a00c00c04038415807040051001e0125441c11100030501140c1c020000911a407669903513403030b6038100c50300a84c2e0941140410725246600005600700052151000310314001c1a81110402da8600f0080c10307015004003900c11400340d0013039001c2e40c006224010101d4031681c2c1c0d1400d051150344411550800a1254001c80e0480d090000640340129451040410710a0b031010030705c0135061001807111424090781d000041d007a1001c0c031424248034003401d0f0b414507408944074062b242900e00749040c02c1652000d64 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 299739037 1250 299737787 299737807
    0x30b09010506101b1a01091b1218020904120206100b07080c031c020a0e09221a04030207090b030a020a0303110109060f02090906090f04020409030c050a0506150303 72
    0xf21000000025080041d4886002c030b500e01e00c00c4040110040810355a4160030359200e44400e682d904a80c0040028003441c6002c40b540d10404214115003804545500016914030815400c90280079640340010392050405400040d1071102c203440658540d60001c5913403120303ea040c031605508c80e54406481200350706d098510786103445540d230b0182140401041c10096200306100701d031550b1580703244002c001e040b078984110084d07000d16011408070710703100c0503500c0354204040d1980c41220b410603901c40000c034007500030406108002d0102c036224800100392104d00100f51a0f1070203507010b40d00400405041418640c1180c00710f44505109074002c02c070b92401a502e00d21a407003640c1c0d2500d800d0740d4941245148d00e0140c6106440105401c0c02c0484012200e51207501610081070100c860038882d84034001445401d1000b9624900706030a80c4c000100981020741184880901c41d140980d40c800094070380074141004240120f9007600a83c040c41a0035140c54a03415042104502452420003520 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 299740287 1250 299739037 299739049
    0x60a090b01050607050a0b0a09120e040c020d0519021618050708041104090201022e050f0103051e030403080d0f0b040b062b0903020d0206070c0c1e05100207030b09010506 75
    0x13206c020440640c08000072044103181d000321005a900c040c000d1840782c04030002801902400040a018614140c5a104458800140360780000c81030780301d051500081420302c83c041101c0100300001e500c100e80c2d070245000088041400200711485841c0c030209402448c540c145c40d030141c07489040090307036414800451640c141c01d0301d141604880c005882030382c3c0e2005034188015031591500038101c490032410900701c0c1014520706001c0c00c5104000b2603688505540410f403080c04060b000d80c0c880c0140c3ca00445491440d01000703071042d0708036401c02c0e5403a9a040d02d654000003c00300000e441d404400140707500b5005120400700121014480e48090001284480c002c0c1ba0751013031442c01003007000c0c44401a510403408039031302805041c41011000d06010355100c0e0781240503030040c0b2440000900807482141030f0b10780194003102c1c01a00c0e510300941c092080e584c4254039000e0300a408400141d541d100c2e8403a84c000c945a030080c0076403620314100846031130001005c08a503039050108000f8135503212 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 299741537 1250 299740287 299740303
    0x21010e0319090f0b0f03150406090f0e0105012d050d140d020c130c091e0e0f09030a030f0e010e061005010504050f0607080d0504060b1003140105090612060a090b0105060705 76
    0x1740c5c4190380325500e075052400140c4404181c540c10500d0100c011891072071039005401200035815050040e01d4a0b64019402c8a00900c204200071131408038404000301e0b008032071000c00042d0341c61024840c0c1c46034001044c106224608135031039982282100b070044014070040801741124005801d4007107120b0003064071261220302c0d00310b040b9941e104c4064010f004085500141c010307201203036000110962070307070a982514010085032011000010300a02074050f07145100d045600040c504011003054294090301c5484240144c8603281e41100c880008244070b0a41201c0032034004160340d05110b4402454031403640c1205042040803c402e20090f100c502c450348140c842501c1813980d54425041c400307680d0180c000e195191509284c107010600070b054001501d900030440d041140c50140200990440c0c12514100141c588201d004210510344039142d264040405002040103002c2940d04a0904038201c5443d51680d1765115090305010544403054050101a20a203140c5911615481c1d600e07070078 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 299742787 1250 299741537 299741557
    0x705180f01020106030605150a0807180203060d080d0903110a052107150207050106050906310f02040f1e0b070807080304030804030212040521010e0319090f0b 70
    0x45404022590b4400d5100da00156000340d010042c50034800544040f510100b103406101c0c0544440c0410b11100108000088030301100c40c213850f01a100c1c0710702d030294000504040e4064442214500070500c110010500101d248100190300c10181c0b4005e021045014220115513108041d082c00146001036082c0c0c40417865807402450100e0343c401d02213244903202008254448007002925002040e4010386030f01e610a5009018039621042805440369080707400c594400c01310783d51400011001611a88002c44502d8500407100413a103c1605076080d9900400388241c0c00203082005403080d0700c040001d09043d182c076801c84080d401c40c0b901c4429140c0505002448001a02010051000119100d060384004541e44074941230402420b00c0608880903070250003a0784c40511001520b00455044e43d0004051941c040d010601c0004034080000c020400d0707641c1d8004d00100d0f02000c002800d1501e513030102c10465100e034100000c02508280d401100340c4002c042042c400991440143e8001c811 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 299744037 1250 299742787 299742799
    0xa0809070b0435030f0d060b0c0d03050c07030905090411100f1e0906210c05030105010206250f0509030102070b01030312050c03010b160c0906060311040807060804021216030308070518 81
    0x50110b141001407c099001c204210303000100c07240340c06408101e007243d40c800764408010319a144140500107218090700100002c0051500740000d01d001d100350b9800900801045e04c12410760001306030786c8019200c200b404140616950070b011039000d05c09003e00b0f0b1042c0b070442d9000d440050701405420413070007404280704803c8136a0905000350044900060400c0c01c0a104266885030080c2082e0720a000d658014050071001415004940320140644020496001060103004a049a1502800000c1010054200b1400525035000d0011308070680c000ca14a4900394074502d0080d00c0f00480700501c0100f03908000170440f13031030349410940c0d0440760020311980d9544149030603a403000190740b100416940e61014080361f0840603501450980c0c407980c0701081040c02170041d0320200d0003a8480e00526a00150b02805070030712441d03a90350414405003041d605220142c4c101420944401201c0c0c0750050614803c000380360b445a440f541000c03050506500d82055549504262410503c50a0150b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 299745287 1250 299744037 299744047
    0x60e072007030c0905180703020f010509040905060a050f04082b05180615030309060d1b0203030411040e0d0f091509150e0102030a0809070b0435030f 66
    0x500c040101a1800503181034601c059100c0c50110030000700c5000e5680b144e032403d00001c1400c03910006880045561000030101d0a2441d401c201c60f543d0401d0407141000b80038003031142c05480e03901400d299030b0301c20f0b40600200d140c01e006240403100010304580000c00c2280502c00886c032140103c0700c5c041c1d50801521075280ca07580c54070240e44c6050b101c80c3d420902c1e000400c140a440481c10010400075a003c0d141180c4810300c800d42000c1c2c62811070b88d03050300104030706103003813900078002c04005074400400702da100d600c900c480d241c84184c3e514060260304000100030400c1440512141c280c00110f6081009003100f43d82c080ea280c0700d01030f890090011554600d21000d009189200041a030b5180c0c00001c002e10003001033594800c0e10945122208801c16951594014034842c0381d10001a40150305220700540c084130192000341c01a9031500502c200410800200001030020303082442c0030441c8480080d815003500d005450483c000b4508100961082d480003000300c0b401c4440c40100d507500c0c3c07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 299746537 1250 299745287 299745317
    0x30f060f0d06020a02072903060307031b060201050604021c1d03030907030b09030a08131106030103082a030d0903033210050d080f090a090b0f04060e07 67
    0x502403944850340480341c80004000c12001d82c00a1842d5640d0398290b0344440da890315500f40c06520301499801640e04103180ca2854031216010710751100d0001d040790206552526001c00e218030b00c0b102003108031108034044c040300d9024084e00703812141c16030307003145411454266080003885400803001c065846050400705181c00c0064151100c848800307488c2d90741400855107545801c50310044880609da580090268040401590090701684d203600903079682d6040c0300b90400044000485102c3c0119490351103d899050103180079500c43c01c400f81d641d4070852860011800c1e280b800003150b86e20302a081014034070110940e0074140c1c01003c0407541e000c45250a40203000030b40c0482c0c005000400385028404440b00b07624032f0098840c04d51a80649551407c04003584060040c141c0280c030780011900010647c0b40200b007200c0b01c02e465582000c3c401000629540b078954004440035445051001003458080c50302d03124071204803400c2140900d40300070b00700c032400010642014452442001a08 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 299747787 1250 299746537 299746549
    0x30207060302031914160507050d0c150501030b0f0c0901090302040b060c10062c070f050c0d2a1104050408070203060a021206010e09130501060f180509010c05030f06 73
    0xc0f003040c5a0f0300b840200c2c00501c04036280e00c012200308074042c0086d141244107a01407002c036540e40360000050118a24100000c2d5810038a80d10704a55103a01074040c09070303090340c40c45054085c5104504012550a01c41101100044043e040c110222400c10420720160b80004c030140440c3c0c0d050701c010079003444280c0000c149010346e0840c2c05e10350040343c80169040015512003c1a2400e510500c1e5130110a17941d1089035218062021005a03c41c60100c4d20035401000035020304200da1801618000121074640d08261613510071030301041994030010065210700240205641000e001105e20025580ba200104211011528051565079001c0f60038020900c040f54840c07038000d800c0b2540f5087c1000400002d5001da503801d020342c0c202201240056210b07072083c1c002d070840103002031810380b80c1040e007041c03a10303491108640b03d659800000070850441080f12000781008602c000789800104800410703248000d2140030903916242e6542e202c250400d050b81d030445824110026540d88060210310 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 299749037 1250 299747787 299747821
    0x1806040b060c0a0204050a0501050a0603051f08010c020706140a0503040212070f06030e06010b03010306050a0906111c0209010f05160b010b2115061608070b09150403020706030203 79
    0x1402031070000d03400155182c00560208070500c2502c080060355915411075048604c01e0059903031200d0342020400000784241c010310b4104884d000e030070b00d0b2070845100500703030048180d1048100f83d444454041856406010000080ca600d05062040c8034600c25901c18604c00c01c0903400902070040301243c20341d00c480c40c01c01d4400540f6001c844820b0344507000e100c1c40880034418800024285408c11071240008103042d03048902d034005150540c3d00b9580c800020300401081044c41a030394241000c041083c6002d2540d041c074a0b6208143e45041d6151644d01040300b00401c2100030f801040341269036603200e0f0010018a0325803a141c0d88540346e00100c0900b07030043d0071f0f0203040462228008075102100c60b00421f10308085e12491301d89400300c4859020081c208844c054444402c02612aa40b4200340c0c1c028000c0c0c0000e0440c0e4003031040c50b07648420140e00046020b4516850b942e08003c001182040b405011184d258106e603100d01d0580d03070085d9240b269004541c101034010010a15000482c0142c1c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 299750287 1250 299749037 299749039
    0x50f010f08132301061503090203100c03090204050f061206010509061207080f030a121407030b0a0f120c12080304020402070809041e05010501090b07140f060703021206010e1806040b 80
    0xa0004800100f40c0c0601003d0103024002001003031803005141c024403c4404c441d038042c0142ca00e80b03050b0b103950740080115003512402e041d1074100d088010f81e52441080d229510704480c804642c00e020041c49008994240180e246a000c40c005001c00d07a01c074044681e0043c130403203100c242c800142d0421402d024155100c103089205603101c1c1c0e00301e01c1022000e0420803031035039200c0d034401c44030220b0b920585070b41c2c8070f0750140070782680c2c081001944039805c0391000c07550140140502d582d9820328900072000690080c1c6601d00343d07003000350411074800102001071800c2c5030780703440302d070070640301e041d4281700c0604000e1041d0b2b4001005d0013040032603c15500d010303c000740101301e2102003180140845440c4060104810f1410340049469070003510044180d84034480f410b07062904580e03e05100198000b4041c1c1d0038455100c0c00e40500302c04110a038801d412a0b9005a110007420081004102000d4441030500041030f8081d40980c03901000300c005140c0304080003660b40c0b200c4002c500207200d148902 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 299751537 1250 299750287 299750333
    0x903030408010618110a030e0c100201140901020a02031204031206060804061104060c1b030b0c04080f0307110d03031d031308030a0f05180910050f010f0813 69
    0x580c0e84010b5010034102c031301c0600c000781101140091041285d0301d400740c0008a20003030090405903407007507005244502150f0304446251011200145002c0c91218903200140c1d114103040c2c0c2900e071807006182c2c01c0b0700104020750904000f0100030751240128880d40684040382000981403510034030018961094020040000985464006000c0403045806580142c10f00c0c518021081504e802c5a00300e41c51a130360030355020b00507a40c2170b010f180d94040c500804021140040003140302d40034618058280441205d43c0c1d946010300341414983c0902c01c40b50250020f0184102041c1e10000d4503204502c11907000070f41400c07520f002d500902a041e00540c1c0c1410000e62081c007954004010054100f01104000d5855075031000b00e80c0d6441180880c3c00010785e8004404017480c060009403003041191003003e507481c0102d0000c03461401c002c03502c01004000300d2038100161b0801d18075805a0803000c1ca0002e103008032031400a030441902510410061440190b04c4040c4a07400440d180a000040030b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 299752787 1250 299751537 299751539
    0x90b031b0f12090a030e0d05010e070b0309070f0501090302010c1e03050a0306051c0f0309120c050405160c02120102091908061003030f03020d020f0d06060807032a020309030304 78
    0x44031946400c6001c0c40c90000202d40040740c01c0c1d40d00052410b81241d07042c0c2c1d031000a4809a010300064140b2000c3c1140c156484403100008035009100c844050805420015164a040b0304401e2622a0550101c0c1040f101a141032000f070f42d00c81e4004042c1da03020300382850440c202d4948148141d40200c088440c007400c0d1001041015440001030034191175640c2c01b1f0200c07070344601c104030a1450000001d0082c54980140000003281c0202c1005814001d007440d01655035074038140100c503491100c0480704600508418045860710b4445c907a04030600c2c1c512002445003442c0b0261151100c81c002030312804a03051201907940094049032003441e03014100c50602c200c6007000e180006900e005040d039501035140001d4030740240407040e00c104d940543d80c405190140d040b003a402948081120000680c080008a0303807018070300014480c4a150420005400e80762400c01000c07444090b20500c1018103015107142e01342c0c90215901400c805c0c1c0366690303840301a13020040c2d1451280c8626180c141c0000b1078 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 299754037 1250 299752787 299752807
    0xb07350402010810060804230610080d050f0901030e030c010216110d0512090a0e010b13090e0a0305030a0b0a0806011a16060b0a050603270a0201090b031b 68
    0x20049029070300c00c3e02d0740c41c042c0d1950711010008659074000c42c4002210500001c001c2603180000c0b0821140005032410650032a09066041040c02c82d076880602c00410410000d40b0000c1000d6591a811841c006042006011120380d852003849500e42c100b5407141c0202034541c0c01030080b05d1002e04a040210366426495011114004500794161101035100541f11317410705044503a04101c5a00030041c2c40042e00301e042c84101900488520740d009503038804080703007204040341054060550000416190412400c802a008105802c8050180e007400d101051040e0002542000c159060130145c0e182d6640c83c2c1d8080c02400e090054030b51182400600041c00500030560032705a41c41035248040b41c1801c0091032100340701d455144e0b0740840707090015601007441039111080c180002008410015900e8001540503081502c00c0700c5c0298001030041c00c4031080c2c007072505049020901502014550307400103028038050b8440e00c480c6039400000907404018041000d4821120b5a52864440103138403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 299755287 1250 299754037 299754137
    0x3210818070b0423030d080619050d1103101505060705010f050408130906051509010e15031509010b041e031205030402010e1e120109020604120b06010c0b07 69
    0x310810707600d0303d0158000540c117011030f11202d964140c1d03c0303a0140d030302d8041c00c0c000c00302c207035580094440200942c0030072283d907600002800c41c5d00804090540494040401d400c256128904001c032034501400c00c0e0038601c8404c401c000304e440441d1180e8855986003405809000d10420b4117446524000401c01041301c508040c0100050f1100740111041d118031042c4104d801383c0c012164044018441d512515501500401d14901f040c90092851008800441c004190342c000480001c0000b00422880d11302d078028400c3e484a0407140100305500d800d481c01c1c0b99200c1c0c0d00030481d02c0d06e418840e0403c13520704c5000c004003c550102d250590b40c40d81060041c51900180c1c1c04074001900c2019028040c6402044c2c08140301e070400100409803820070402c6001480d8100d0080555280c004031805640c98201070720041c210760704048001d40c03d5242240c086040181018184444dc0703211001107465241c4940d0f00081d40e09000d140c88080311403148240b0380042c104940140d0140100c2500360f504 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 299756537 1250 299755287 299755319
    0x10090e060a031a010303030e030c12070c12030804110a0e0606031e01030f06050f01140d0c0f03050c040c02010c020709091a16110c01050a0507080904051003210818070b04 75
    0xb46d034108001c888c40403c0d43d07280d1007003c0002000768801c90301507240c92501d0005000c43c900c134140040340650381d4034010050f241400c1d400d80100300c14904100601504441c51068000e0880301c010405080c048200c0754400081c02070b07409014003000040d5210180c2d100f001400e0016040134107250703900c2c0303001000305400201c212901c034200303008202c021a034038040d036060f10404c0740d46112040303028041c020104001c02003601c0258610305d0004817410306401c0c21002e940694003511000c8800000c1c081a100c034000030b0011a072420b071103169039941c0415484182c3d2a004408210b080d4142005500c001070068414022440c1d04140800b03e01c6622039880000d6858440039200c0e003800c0d608a0301e8564040078540496402c00298861034420401002e883c1e1244512900b05944100480e0489604460101e5140d041440034814415041e504003e20010400301420503660440001d128a001034440c107003e401001d0703585c00745101480340402410041c6642c5031140d81d1000c00e41201204 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 299757787 1250 299756537 299756543
    0x2006090a060606080103170a2c040e0a0b16020a0219060216030b27030f04030c090e030d0506120f1f0203010e0c25050a1110090e060a031a0103 63
    0x141c16070000f006406900068122078000c1000303d04000020041c03070380f03a4000071f01b860070401c0c098081c0c41e003800e840f032603406a441d08a90700c4450600303100510046451090000d4900d40c41481110002044900c446d42e21200d406040e10b840c1e0b4403900245d28000807910025800040035a0f1142c000c80c007088800211462a0300705c540c00c0d04501da501e11100420b000203000701d00a20001030b421610f840b2030b2124903605813901c5c0d1200500000c03190071600b0000b403051040d480014100305010110f0319030340240041407810000d040306414200c0e40c91090780001d007a01a1620006a06035031410120080b100242c0705136074400c41d5003020f10381c444040b1031416030742c001f402885080c00061171007920705890010342c07548510303180c10400c03407416002800b010201040c0840034100605181f410840d841d48900c00030a512503052070268000715100921500880c0e00c5860b864899030700c0303003d003004c44046410704041500c4190100d100c4440c5070700050500c1096601d4555030842c4c030381c8514100d82c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 299759037 1250 299757787 299757791
    0x807080d1b170408131d0115020706021510050414250c110f030d0504180209030303071d040c020a02030f06040f0b060103091208041203020406020d2006090a06 70
    0x4121060354146a02c040c616800880300c0002000a00040300500c0c2c0342d6104200b40210503a03400c010404c10818811111032080041d00411402d0000c40b42c5a4500807240081e00d801414514000d503140200c1d11808042207061003c030304c101f0f0718504a44081c150103402402507001c0d200700c100c3c0c03142c02620301d030303403620b10240081d480d43c03035140c61408418640f6590460028117584450b1030181076a40c40e554400e2268291180c203680401041c240000e01380c031415111403402e4018800001e42c4482060b486004005820803036801004681d0300200768240412003140310410200d02400880729550043c0c5003003910341e04203400103100f0368040d10880449405c80f0200b841540c807041c05440051060200048480005440c0c2c000c8907804070041c900024155015160360103806040e900c44400720f5a0007041c8014441c81c010107141c20300e07075800c0951400340f502100035990481c2c010340710104088805441c00c4981e6000d000aa102124030407503426013446c49503552591410030301150705c14 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 299760287 1250 299759037 299759081
    0x31c1e0b012a0204090501140f0406050606040303200709150f0b0412030503040f0816140601030b0106050a120923010509060a0c0516080a1106090601050103090807080d 74
    0xc41d202018010b40000d061142410000c543c0c2440301400c8402001c0721155290920603d05482c0241d01511420040ba24044030382041c0c28070030308a56014201a0081c0c900b0070050010036000780d0b040c4600f852081d038055512605240050810120303810102c00c107810302d19807040040390011402d0550744110684402143e85036004452445a0f2107175050500c00301c10003001103402036000c0e50340031b401056001c03034081455840300000d80c00a4995140d00b180b941c401c01c28031103038003008685c428148000f0310840d4116101ca481c0c035001489014100100090602031041c8940503403801103049132000c0c08501144e14240b4086001c03c0d03990740c030090101400400500c014003500d8001c03000000681296280e01c064080540003c014100501100704000d52400c00410000c54989014600071921014241030040569150341403442985d4000028000403c0c400b0504a045407400d08000480d80003524041c0f180f4010f5440142805401203802000c101b210342066500c2c50340d1580d40c400388 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 299761537 1250 299760287 299760317
    0xf031606020106051e12030d050c04140105180909031b0303151c060c050415080403030f0b030c0d03090b030a1a0108040b07030504170f1801080603031c1e0b01 70
    0x9440e61860341712041000c500002400d09110a641084008120580e8030b86903112046c1401e448003520000340c2101d00050030132a610303502c6140358569200b481d0280c074010000c400c0d6407506040b015a144204080f00c042041070004008640c11203089051062916028201c616120f401c1224425420398270070070700000520300b10b00320a114094030080321000652035240d903002080301d20524803e000c0c0c208400b1030700b03a04044104900400300e42d0350740410b1916140003400c1d2259005505000b5080203503102c1581c2e0041148881001e0a0314503003440c03c41420b0484031400c0c1544540c43c01078000040c03105401407a000200100d600141c140e03041a16070b0300441d480e110444000e030070a480700d0040f8900611a800954220b401078402c1c2d48074601400c00c055140d03000400c2001c842c8000900c0036904401c3c020b00f5115144242040c0b94a0701d06000401d0310717032040c0340b0341c540b14031040c4580321540501503210411160385a9440c0c009248610030400c000d1440c0c030303040d5000c516066031170004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 299762787 1250 299761537 299761549
    0x1804051012141209130f1514010905060427090605011212020a0b070809070305060109200c06010e0a0207060c0f0809010c02030a050c0a0515061305040803060904020f03160602010605 80
    0x11380c140140041e810914080903420040c04400f40c1d145203207071110711455502c084000c1741d5010380941000b040d028170503980090080413503581b00a0182d40148402c100300b0f20000d05002c40e140300308000c002a0316071070000701c00030000c20300c0081449140400215841125014040f0032520680030708408207a940c0040c0d0b50384410410040030b000e81000019800341c0704a19031900b261680045944443d10f0b940d84a05281098121103040c6035541c151401c0740507030340580305a190b0706115003440c1040e0141d003551108014094142421080000b02d085075229504450319680c000c10304000b0341030b0030b4000802c1300500100403000203c1460214500307030018814017400d601203400851501b041038200351041d4000a010140c0c0c0c1c0550760034400840c006004c0c040b10000c40c01040c8180780380800800441c1e961a00d280780c0c0281c500350400000a2140d401c5a41002c012900c40c102503503588001006212032034032007501405003544100c055034100360b1100540300305400038005140c6035018091 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 299764037 1250 299762787 299762797
    0x804030c051011060417090a090e0d110604020105030415050a060e09010203061e0120030408010e060f04020103110c0118060b040c090e07032c011118040510121412 72
    0xc0f903040030000c103001509410f5180d0304440084a02030800c603640d00003c4c248903155000c0750f040d50322502e2144ca071031300a100549800102c0d00f80340c4c1048018041d203036a45c0364010802810301c070300003020a0a0089000c40c5400702c030382d02c04040c4520718140c0058005400300e803294016040101022a088280600942e4171401c0003400031040a18003400128120024602e6941409256851100001e14007404501c0d0b510001c1c2c01036544600d00302c030060031217181d15981400c6402c0501444041c10400181c240c02c41d809180104540064101040841c42146c40c0e40440e0741ca4512290803540c00d2020340801c0c60f0040c00c2c10800580d2201c14031040c0d42c0c0800c0f2100014181000600c0100c200c0300000303402004030320b030000d03200061424050f02501040140614650502c0310780080c2d00007400313803000c0a006510010706102da00491300418410000c0414440c90703d820009500d800085d10f964000e01115034a500000c4003070500c00c11414030601c86e04000d011f40e1600701411201c503003c0358 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 299765287 1250 299764037 299764067
    0x30215070510050c090d020f180105030c010207030c0b0c010f090b06090903030105010e0118120f060c0203090604030f02030f10020d0e0601060203030f130203060f07020d09140f0301090804030c0510 87
    0x14a03001000c5d040003a03035040d4080481e844802c5014004a9407a040d42500b484c100c0d14034440c907154107090030185864034a02c01241194440701c014000200075002d04821110989503e54864103820031460160910110501c00c0e549403400c200140b0031043c2c01c85000d408140c1da07000b901d480d1341040d60740f00e00c170901a1601042c0e003454482d001e5441039003808180386400d082d06d40b10b25156017002400b5003881d1000c0c0c0d2580100c207859010310901c0d02c21520038603170f5400114609050140861040d02403880040c1400341141d1040007507450502c800c8c0042d10b0502c050300c0841e810800020001c1d084104524001c3c1d1501254a00c004000500380341030303800507002181540c0c0c441c0340d4000281001805236a614a0300040c1c580161000c00c241ca008114000c20642140741c02c6a009142c07403e824a00700800c51030b02410004001104ca216009480a0b00d035181c894a41c640407038050244448020b1600c6000617001040c0440c1d1115903041d21011039804c0c102074500d42007282da40b820b1300084 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 299766537 1250 299765287 299765311
    0x804110d0317070f05090f06040504050a05010302030d0503060d0305090402070c0b04090f0207052d062d060d06020a0908070b070b100320010c051005090105072c010903021507051005 80
    0x1403186ca14140e9040800b001c0010841860315884001180945030251400c00c146503c8000602c1140350030f000c0310322038400c1c0703190403030961070b100e000503072154042e0b10050305000b00003580d11000d46032601102e14032600f00c126140982e584204404103a8024482c00400306d25015101d000402c2c00d0080740e1440b90040700820701c290398044d00c0b0700401c880c5120300001b00c0c40203519020440d401c2c0a4184622421000304480034011810000072040d40d422054011492030204401551922499110700c0d40013407005880301806102a18580c82c1c07a000031a00f03100d03c050009a50001800818450b8422040e0f0440c90325400550f61030880130f404001c0c680c000d5022145508620070b251003114400501d00065849650b8540324208250744480700c0e00a9100c0c0200000100700740a07190704482c41e807900c890341000c0d070029020303464041c00550b904403008200105882e84900355090156800524402e05404000451501c5921200003210701c0d0086a12a40c0e042c9004e1103054407603030f010800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 299767787 1250 299766537 299766547
    0x30f020f210306120a1a010504050106050d050408040f080609070e1003030507030e06030c1e09010516020a081204061107050a0306020a021e0c01031a010f0804110d0317070f05 77
    0xa141454000030300154028455880c0c4054104c8200543e2074035500a56018840c1c0500244a03000c5240c141c1102e4002e5040c0001041143d0740030040b40d402039081200001d00740c81c1d515025a40e48070359030005203801c03c44030b07010808000221380e1a000d10140303811115402d82d12600c0250041c021603000800812092080010034016002450011f00c246482e0785224002c0c00091807640043d1180e60300007402003403000c1c1c0c183c1c09620042e12050082449030a1103680000202244240c13851903903c541a81280411925103082d003074080c0c02d03008151407031780c0b0200a82c00340302c0e00b180c4154030000c0c280810000400701c01064a0058400107001d840c4440d0030354450b04003075440521030780c0440c4070300c0101d003d14410742c000044480c00e50300c02a00d1452102800101a6100300c0c400c40c42601d5030509540c04c51380c0180d09030400c92503a040c0f0400f140d5650412a00343c0341c01e81442500210040740000c101603108401c03a4030342600d005a19030984038501b003110a150503240e03000c00b02d1000c01c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 299769037 1250 299767787 299767843
    0x30118050703030813051e1504020307050d0215161b06171f17010e01060e130c03050f03090901060e090106140c07080d02061e0a050c070f030f020f 65
    0x2130540d014641e9582c0700380b80c04a07561030713a103070100c00001c408440346104030380174404405215201ca00c0c15900c240b5070203428281c0000303407074100902c200c40c0b1500d40501d040d421529044078803144c400c074030b0801d544c646488180700d0740c424192003021a1400c80800c41c907403810b1040c0824030183c5810395900c0d80d10100365a40706c081e40001900c10601d2683c1148041e45000041e580c0ca4040c00f010b003284204000100101405e40d0543c110400d09039043c400c0178000311104020b06603004041681e15991040d4500b0480b80c5920150405031260286654401c09103a0001c0113100c0b4002c113803544041340c1c1e42c071901107401d4841c042e0141d5204000200420900388220311031541c410303440c50001d20b000301c07541480d464444a603000c3d20303040c2c00c503020104005030140592507000c0310714440300c035003005991103050947c0402042040b0725a0b440700800c200d800d00d20191004180c0c04032440c081d0359014180a40403205c420f402d60014804d0450b0b9000c0c1c82c2c0045480b0b1090032241c0e03940b803030142101c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 299770287 1250 299769037 299769047
    0x1081b040f020405040e070906090608190819091a0406170405010b120109060e0c06120712050c0903100c1209020d0b07050d060b04150507060905100b03011805070303 73
    0x34118400d980903c0041041d03070340c5103e4441c12400000050402c0c6140604080940301c0d10b0380f0044405103884c102304091907000c203200c540c460500c24211455001031400c084039000303116031010100d44038603001e2800c07078000094100b5a6900702e44845000850110304020b44964041c2e0300c0091029048519015070100109070030601c240c001241c241c440030086600da03000e440c040340d42c5a4582d04900240702c48c0b807203400d0180c01054040d02d0010450004584a0310038110180c00c98001e450000c0c0c4014801c00c940e003003a0381c02410901c01400d01c0c0c41d403c403250308107d032494400c3c040c00e220503074000111b20401e50440201e84401005480d2091800d00030040007600b0798000751400030903000245d40f418603c1c4540da080e12415210703421050b415048038029004059445e104110600400e00700c103101d01500a46860030b02d9880c210b42c0751040141941400045c298800e9000750740c41080f10b9000061240030035002008200b21080329405600c0613004080d00030341042ca41071010038421 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 299771537 1250 299770287 299770301
    0x412020f0d0c0e0a06090207031b0213020a030b0415030b06011101060801050a060501080a050f15040e0f0d0906020a0507031203150e01080c1e0f01020319080402010e2e020c0d080a0801081b04 84
    0xc0c5202c829580cc0600322040c0d0f44814142c0000aaa038140b10005180c40c0c4504c41c8010040c0280f0040f6a0441d996994010805402e05040c00390b0480300d01200321003500a00040c01c0107900901441c28800d20a50281c01603004140c0400c00c08000900c03030602600c2080d20980d48070203050543d0301d961040d032040c18040c2c0e403a1070304141c070380b4000342c4400d0382000303860700c202d500400030240348040810040c5803c0c11508070a0454000c0d50813640860070026000c002e498021001d64481c10558000390010044420381c0541e44400c4d840c0040e0550110004a0484103800251040e8004090401400d003040300c249150040c9000202c000f58140340e40e14440c03100e810f0044030300d8544458021407155503c2040e07680000c0c000800c10045580c00058010030901c181e55048914140401c941c0b2228010744101907410401517004450b01d00c01c010b40c0c440344030064500b81d040a461305207105681e21403800304001c5000a80001640c62000420300d058041221030856038054160400c806440d40c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 299772787 1250 299771537 299771539
    0x10e04020904051911040b0910031418010f020f04090b0d0807060e01060e0601020c0d1b080c04110f0d02030714120712020412020f0d0c0e0a06090207031b02 69
    0x10070300c118121500c6621842c1d0003407030352000b49000344110450305400da541d07180200d45044003c1c0810080b03000060705498404604444030302016249660480040c14036406848022a02d0001d201c900b0180700c40d00044504250028002c6213070880c1340400b6442410641171540000f004200501d90907a445071607540c000810060b20480161a0f0100c141c01c1050103075190755469401040b00d980920a2100814102440c030f0001d1525400103501c410308901c80c98029001480100300700110784a041c41a040c007035401c8040c1c580c89200c401c0e03480f5048400d4500842c40c001000000c0710300c05007175a202640d000b980c41d151500549041020b0340024112006000c43c040703020b00300007220400b40054500c642649140d5140400300100380100b5850110b0003948100401e001600d8041803807409a80c040c0c81c0c0711380c00030001011901000c0007010207450038803450008580d01200c0854940903240099041c03002c2e9440e441080200c0c860140005c000c58090300d80c070010a03a02400209005e80 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 299774037 1250 299772787 299772791
    0x6030504080f0307050409050604050c25120c050c03060f010b0c0f1005061905031009080f0a0908100e03122707180603050307020402030c04080d0206061003020306010c02010e04 78
    0x15420311002c0d55a04140c8418000c03542c042014004d42d141881082d5001904070307014801e9041a00201c200c1b445101d190000c02c0b1440100b02101484181ea2407035840d80c032142100b0030f1045040e00800f000490203003240d56009508400c0c0c3c00e4500042c6060251041c00140391040c0d10b02850240e003544175009000c02801150b50680c0090310520004d40c0c40c1421100c041898904101003018040c1f501c00391062000207480c00b0301c182d4900051036200704961040c0018140e4032820b01c001c0c5801011800c0710410000201d82e00416807200840701118004001c45d021074002c0500c040560300e0300b10140d1055441801454000c003007034009542c02401d240d4501c400c0003410b0890304900da001e02e50240c01a17100d950100301200c442c1e10340c013521041070704007003040e40e0940c0e03220ba4803403203407020203845940c0100114901030303840c00880d0f004083c040b0880c2ea20340d0f20400b000e03480c1c0f502214550310808000c03801042c3c15000c2d008580c460035059444050255203035005403200c904104007190415 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 299775287 1250 299774037 299774047
    0xb030a15053d080f010501030504150507092102010f0206040f03030c0e040905070503060907230f090103062909040b07092303070503030a050a03020c0102160f02030c0f01090603050408 81
    0x8218041d40144101c03966980d0890391822418075003513400180d100038101841c100030030000c510045d040c0255002041d4011501d13403900141161600c1060300001c83c2d29851100300d5144a11031284046054800e803900100c2904064042c3e03183d69003128050854441101101c1c00a03229a0000d1419846401c0480d071071101d58004c902106c04e03909086800d903000701400c0c4424602000b00e2903100311360300d00601c45941003602a106551f449030044000111030b4400800c0340d070341c00c0c070694041c0700d005d8404034156949040410240003d110800b04451040c2901c802150180e5401e2101070780262010403a500d5594500c00c2081c0d0090039407081101c072440108120071fa0126102c1210b400410041c0c04070348100c105820510f0640c84144a54010048508030a4000054584803180340c100142c03240c55668485029101340c4d500d0100000140444400f00141c1e400b07900300190095048441800b00942170000040c80d44800782c1c08204030403410412980b09800496100e8410a100d40c100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 299776537 1250 299775287 299775379
    0x10e040614070305060f09060d06050612030a21140f09010e030a0e0a0f0f0b0a050d02070c1806050f10020102070c06050702120c10030209010c0b010b030a1505 70
    0x35180540c1c03490002a02d072402e1111504c3c1c507175440710320090215031f212000e0400c000000c0054a034010010041358440b030000c0c140b666408406104d00e4015004ea96540701c40aa00a110340d0f00504034401800d042030034402d05084602c102040074010f8803d4841039102c117030800b4010003004001105643d00c504482d02000d10502c0a4013500580d52640d100d0000c0f0b08040045417070040d0080d07032040c07505034010080644500f1084040350301502c80c0035510507002008540f28420000341e942001d0002510404120450680400f00d92001c01025280046060130800b9100c89201d95a4055103464050440340340012420704021214000146844a10340c3c41d1003514070b09501450100e900031443d0020350a00072104010b00b001100642014480c2d540001c1205242d004841f00f050f80c00b1600551603400b440c1080708070383d0440d81e0b82c0f585694402d510703074066004803142c849640c100204480030072041c003403500c10344e0310040c000010701c081442044100c1d102480703804a034100f101000107035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 299777787 1250 299776537 299776571
    0x6020d0209130b041d0c09060d0b09031209011b0f031e0b031207032304033207050604050405060604050a060201050a0c09030807060e10061e0608040308010e0406 71
    0x1009014030303808540d1406490070042200d50180c2200072445e008081c26a540c0d03c081a0740315603900846190500c0e0b100c12010884181040754000c00c0780c11440240000f280c03000024105058200c032000900c0e0740c07040b2009090350414090340001e600035104a40721035008603444810091a032070002448101b0560450a40018600c0c2c05c410f1540c910b00240a0701b001d203e4000152450350348a440c0017481e0360000d1401030440d9081c0104c03150b088541141003807400803500210b8000d8015080c065204940100e40104c2040c085402d41c0f50005410958501054160448100406103800c0c5460b11003403201901d401088c1d07640c044420440450290384605040c030141850381d000051328a0000d00300c0b800c46207220380900601ca003808003040001e28000403a10f016500c40f0010540c5417001d000c15140c00c0c00818400e82d0709042090203e0403000220301e0100030050901c021400907903641003900c00020540e0060b00040000e001400343d10748580703410740c000c1e100303010019070b2034440084403c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 299779037 1250 299777787 299777809
    0x200409020712080f071409090a0e0f010608030a030504150504080d0b031204060c0312060b0c071e1221090503010b01030b1309020d151b05041206020d0209 68
    0x2012650126038401807002c940b400894140403420210902e0801a000380c4114600500c20170801c1074a0340d003100d0b51102c0c2e506844e00c5040107040452a0704259241c0405044042d041030b6692281c0740060001040501503541104c1810001d14507224060204030050f204c014401d9039440505200145140403030f10072144201c0c01410843c0d191001c400302201034442070301119109070300c940591506da2001d08200e4007203810b507080561140a00d0302e801d0b03a49000701c0c017102110070314040002131140907000081c0020903201040cec0d80080d4070781900c8910545525010f807031200c102c4005000b1088625030880000b40505012140a00d0070207682102c00d0300c4003981c10014000000801c4141000d000b00400c05100b420240103186807000461448010142d260740c0320750321350200000355100c08100300f03880c98100306400c0c0c61560042465000e045240812900c00c6464006a51000e04c1b940c2a2400da895440682c0c400e80001d072500c6002c0d402c61b800701c0744600e03803c04c11039205070b0f00d280c6081 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 299780287 1250 299779037 299779049
    0x60e150a0215070e090a0914010507050d0b01030203010807030f03020f010c030f0f02030405120904060801021603020f0f25090203090109051605010e060703020309060307090302030616050d2004 85
    0x65107210090510b0a504040c051109005455018041641c2c60070a0141d000034461400204803009007062032305000406101c1030a5440c2c4000e100ca4546d10200801086182c41418080d00c1d03910401107049110034498014642c01c6214103100099410010540f82c601900c104c0d0186098116690b00312042c0e82c0348070000ca56030b000e070320b480391003907000d01c1440e481c1c0ba960171804d42c0780a03121241c581c5642009440400d40006902ca05c981d500c0e48200c000e00541d500840d261043c40d00801425030f1440016000b511a00480403410342000624180041d442c40c0901903144c5190101d030a404d03142d00c2d140c200c0c003200303c0000c5400107182c80510b110340c942c000041110341035414224200840c00319050b450b414000350902c00c076600304d20f129181d68003c2e42c2c441d554405a050480c150300800716000c0e403000c4000b003071001c095030144052050b28000c07000d03152280c41e00c1c8070781400986036009141c04140e003031100701a2841142d005400c0d0920302686032400d040c84203003010ba00d0340700f0b810007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 299781537 1250 299780287 299780293
    0x1e040221070e010501180b19120608061b0403030906110309120303060415060e010e030c0d0c03050c010f0e09250c05010509060114091509010906031103010b010504060e150a02 77
    0x4008035031340071b41e03201280031000714082e92050130016070384028454841c503183d0b544505600b03030310014820306100c0d102c6140050204030083d11a030050f40c03615010395071200840035085d002c03468646280210703012280d042c0c480d403c9051900340b056640301252101510036010901152019031a0500e80c2e02030914000081c643d64500300040100b10f420070642122140303103440303040c00260b800c40d00507001c1500c00d09001d06234960440c00240380541034580c540e0817140b07200e00c20b0100000341e0011402d0320702c0350703066a105800b080700441e40d41d81d81116040000c9c54031451492079040940382590400194403120b4145400101c0100034801c2420100c00090b2810b18008148103080c07041e981c2010510000d005039501d004481c80c0f0300176111014600c1807950f440491300000162046e4040c0311307000342c030001d95036955404501c010200c41c802a02e8003e03000165103190318040c031611340c00c100141c40e100d05050a005080f00d10b10444020580c00201e8000c0d40200b05445402400280b401c0c2d40c01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 299782787 1250 299781537 299781539
    0xc090e100902070807060c0207050f0d0510060b1b03070804050d020301092f12060a0510090f090209150a21050a06020403030306080d080103080a030221040204051e040221070e01 78
    0x101104a1f40303212070901c11500308100038001c80e034403075151054000e0110303280440d04441e81030560914404100e402d44072440d09400241c1155070030050a072180c2814084060042e400c030402d6180c0c400c118000b130030040e0070072041c019494180c0d8002d26060003e030000604085660322514012415481e271450200da603503901380342c0300701180046545001550381519185513580400e41c0c90101810742d000c01030b2600300180298003200b036200020000500144018418000510020049520f00340d000c0c2940000240343c1ca0000486a0349070350020303011480d0b491400180480c4d034450191480c1110350809910408582e040042d00001409010016030b154a54a030140841e4203c0e441225035811404070118400d4000c0c0b00e460449805c84082565002c0411045009228000c40c0c00c1c03a442403544101003104207a0400c51055109031020015900c0750494100e800403c0c010500c1c20038019400a4010f040c41410004070100340d26070480400c16421480d03042200d0b68020026101c10440 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 299784037 1250 299782787 299782793
    0x3080a050901090201020a02100c0f0308060102060109140712060f0b090306070809061609030b1f0803040b2209020f0307030507050304020108010306050402120f070611010c090e100902070807 84
    0xc40e0a030003100e090001c100d503d0182d80040d440360121403010744107828042c9640b03450750146102c0700c003150344406150240c8020b0300d0042e0122500b550200d005204510005c10343e0310b85407060500c103a802d84207a00349651070745821100c00000c0c80769042225100d5000042d800c6070440e000f000381c10450311140d1501018030916151000c010000310810003038405101c0da8810116681e50000160030702d4200100300c4003c01c1c0d51508031039000500c416014402c20800c3c000e00344600c4d199030400b0041000280d6600c001598901030303400348680f03180040103000401505e5980801103561585810941103a480d407003441203070050511800208000420042c2240d03040c8500760340001c00382001411810543c00003407166005000007003815640310041010b65403869000c0240c001c2444c201c0320341e03c2c0049115511580c0d580b10b0080818071680b040d034019041030280301005000741c0e07604003c5a14020b00b404259a01820380000c8580500c4040360044142c001031034654042c0c1001760b515084c0345 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 299785287 1250 299784037 299784041
    0x1e02120315030c0306102903040b061c0201140d150303020f2401050d02060d0e0d02012f160503070b100b180f0f040515030d05030c040b070804030f03080a 68
    0x403010f00d21030b820040401065100d024500004c3d62031502100b402c2e0398001206181da020050008950803001000f00b10400a4031560035200d48001c1e1040070150300b040c1d40c01040c0000594000780800c080f10241100c01b580c801c040c024100d40000c002c1090045000030444100440d003007540141c022465005102c24100807410070781c10700d1100e54444124040d809030f5500010b004461060700009045001c1d0b50321203094400c6d501203881c081100482104246a560450030f01281c09075080c44010045428000403500b4a01d8558800e402c90809030000358a03690b0002500d02240c4c480350712503402150b810006001103602c00ea0b6041e90f1340c10410701c4074443c0c80380c540c00f844603100d0402c83c6000344481a44400c0c80c03000159407602d0280303070000c00540031030900c0c5240c1d900907240008001440f05145030504241500360309541d443d02c0d40b07040c1210a0f101c00c0b110003c80501c104410010950b400004200c41801151100d01f419103d943d4000741400d5100705800060f00c141c240040c1c202a8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 299786537 1250 299785287 299785303
    0x60102070608070906052808060a05010c05100e010e1006090f0e030d0b0303250b070309020d0f030c080703020102030a05061e0603040f06020301181b1e0212031503 72
    0x14100440b2500d0004402054920540106000c105c00400d4252440c0c110f014150760004e284410a0881100100c0061004038111113a0384250b0079180002019401480d003198403a4003c0301821032088100041310140019800c801402c2d90b94034004c4842140a000702c0b501320340c072640c0203d0342500d00508c4005075040e41942c1d60000c0d140140c8000f030034030000111001c207544400d0100d041014100002e0560007007402941d115001e40c41d82e00411203128407044000c03440703201c4200013a103424004070704076001f20030002d4200d1141105140410a44481c40000034461b143c1048038010990301c4101d2904514400ca01503900481401900d001c503006141c1c0c0706009442c070030b03510b0103060604405540500708181c02503400102140501440c2074480b510103401001c00d554a5a4031b00321010250000c2c001008034a14104502804c820000c0101c01e807440303d07075501021400701e840310a81594082811006520034008401c008000d8074014500c600c003503020002c400c06a220501d07080200f2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 299787787 1250 299786537 299786549
    0x1407030c08070801030204240902090901090b0a1a0705011109240a0509010905040207031e050910030507030902030a1118090616020703061107030e06070203060105090703061d06010207 81
    0x15541c01c01c407800d40d009020a044940440e00412809100542c1c0c0c0880390124080300c580c47c040e6480410129029001001008020365031480d2603179032661040c0840c3c41114525900c41a026410048041c0214500f190402406a41460700392107941d13146c2141d41090b011055001c011402c94000e1800d0102001900052443c105c1a072a40ca2a0304040344610060070091103408644160350b6441184160302820000e00119620205030401071705445411a00d0500c03071a00d000400c2400780718600f9140d6029000d03203402c1802c0e8041341c081c0c018240041c101020140c1d200c2089002d6a010000b0074a01c1d030049442c01c100010000038000382c0c0c40100d100301c03440f09e000d0040c03015903000044c900758040780e650b00c50103007018102000c03400c080f02644080c1c40e59040094214000040c440203084031072298544540701d5160505221081c0260303113000e941368000f0001041642080301903150311044a20700021103580350402045a0103000d0910b0002c81c0c15402046001c1d6010403602002d001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 299789037 1250 299787787 299787797
    0x150a0c060515150313020a08010504061808070206031506030a1406030c031908040509071206051e010e01260a0f05060a0303120f06080c0102070509090307080714011407030c 76
    0x10640101e03d400200e1908400c600b800080001e04095840d0301602c0b640e5402040c85501a82d6801464080d040648003500e4052900158440c0c209058440300f00301c507805880c113410004950200003c640000308502d0003039030440091411503035210025032103200c0b1070304002a07500003010801000040100240d0082e408080506003590740010380e191219460012020021240c1c0340202e0036005990007903030044031030350621490f01e40240681800c8400c2090422030b0650351340800141880100e003142e00c11038840c003a150203501c14104040c44440c1810f120404149a85e00d00b400c4820ba100c00417154034501c2c1c107000103000140a02900c0800f482d80074445400d04200148904220744801014800541e92012489425030010700039014814810840d103551035007640c0c0c42c0c070040c00d101c0d030040c051050041640d19007121040d004220540080d0304004023071b80c0d11400c59009082c1604c810712250640d00c6441c900740900621201040e003a02c03c03501384003401605035070404220300d05002b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 299790287 1250 299789037 299789071
    0x7050c060c2a011413030203010c12110306060d0509010b032a0909030a12150e1608010819030309021002031b0c010e09131b0611010e03041202150a0c0605 68
    0x1c0e0b07110320703000c01c03845001c1499a651700e82624090380f01011130b03100a4040d403c0c1408210301c580c11001e075684040303111000384104044003030b54070454841141d1140d0b12803002d011038403000c0d15030b40c0840d50000204e400050202c113210000703840c0000c1e4640c0b907802407100d6400c84142e054604442140c030f1500b50396016080c100402240e40701e0042c64034040c00c000e0703900999020b403140b079000b11842204801841c0249a19242c0304850100c040382e6032858401c0920600091034071505000c0d040314a10805800d00c5045812008031860210609408060700c502c840380c09603a07515044001300599400456903042c0c096014981d9584807485400303507410040d0780d102030366003100044d940c0e9441203442d2946030307807945202145100000b9016000440c08a4025000c00800d940501501d20b81c0d1190007a220054031054203944500403007443c1d640052204011a820304103040c582c40c0c0c4000e08004900c80404d42060741c0750410700c090000502071a880f02e090103514401c00b5000f0b200c0c0d202061f061 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 299791537 1250 299790287 299790289
    0x80c0102061303030c090e010b0304030e09070e04200301140f010c030905011209050d03060509150a17030408030d091707020306060f0303090a0602060619050109030807050c060c2a 79
    0x4400c1c042d01800349130f00c0300c694000c05171041c01160f01904004100b07010a58481e10004200e41085904a0216100c528080c46a1504403041440f4101995409481a9803082880040c000709014214580c01c0201008522200c0030081c40c060060103100400d14203602080182030810b16000505020141d41ea103800b003a441711a180a980081c20003004141c2d205c10850000e00c004800a06580590400c0002d90f40c2c0c560000b200b100c00c12104421191215801c4466080000011030b50022070b0307990030844061914240c1d4400b8403040300b82ca0400c4c0d69402c480d800c5502c90500521002d0b5641190b000300010303140c4034481508a40c41444c1004450350100e40da1305805820603214011807c070070407140da810021600d4003400503040680e0140e44074006541c0700c00c2581c99038825681e0032280b1003031009101d40300046034416540c81a18601e9a00c4070119035012150a0b504d40c016010359599980700c4100030702e18404141c0c0104807424060105080815416078a84500403180307240c0090707 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 299792787 1250 299791537 299791561
    0x2190b07032a030f080709080307031b020a03050d020d050f0a0e031c12111602060a021501150f02060f01090c0309120305091006180506030a0f0c080c010206 69
    0xa169854241410481c8402003040910b8a01541c008500a03030002041c00f0160710814410400d0b40b1616900e0140c1c5a59005403800111030150004652081c8031201c042403140341403003000800000d030000c046010703030003007644a844c03030f003080d03030756600800001c8001541082201c143c0d01c40c0c1d10b00305080c6010903405440d180700b895060010086840341009256400b031100120300d81100200000751030224501400d242c41d080740d44601246060b1182a040001d54221307404400e0742e21986240c007040b030703080044903004541e0201c2103104000c1090707070108001000502820a20840100300f0b00008002000b0a07103951400741150032840a1141e07403241d114070316055480303a460208224615000450080210000107020311004002da030755156011350000f401b543c102403c0d41c20480544441d42d090f207010344540c41c1604017401ca200c160208680c0003c1c0c10be0320060969900350481e4861182c406040041642d132020140800c00c2900c0e0100281d0155400a0014210074600a0000c001d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 299794037 1250 299792787 299792797
    0xc0426030405010c14060106080a0606020f1002070317090106170c03070605031b131412060c030402210d12060e0c0705010e061003050601060e0619031d060402190b 72
    0x81449a0011180c082040402403100d2201d0454106c98071582d603030300c00810f680001d64855a001e0318009005c150035201280806420020b00010203902c1c00d2210188003c1d03010150980400c009810030066241c1505d4025003e40303078460020600c5403d2100203015541c2100794040c1561002c03002d2003060b00d02143c0f00382143c109080841c0c4030365900004582e0140000f051009076800040d00581404461680b401034980002617000c1e541c0f2402d00303000c146042103146510a83c0450300040390000d1260096512901c0604440f0809098240d026003501415003603002903044100b101c1d9402d58005100080072084400a1040c54030301031041100050142c00c501c140e01d0f00090020500c01c00750003411055000600712286407030031407110000003402e40000c5807607024680000541903ca4071540ba00003900400b054508203400e580c000c0d0304031440320f85c00c050544446010070044481101c100c2001000c501400c001d2415204008c2242a150a81414a602d101c01413001c0280c80c410b0f69 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 299795287 1250 299794037 299794039
    0x30406090902091c03050d1d0c0303030702060a09150f0902041b0905010e04090f081308150a150e0a0e060604140f0406150f080d0f050d0b060706050c0426030405 71
    0x4000d2040b45d0501b120a07208950105a0131414182a0700a01c0c1d04080b08140040080c81510100701c130318400c060700c0340300c140d80340c00060380b010010404044090348054800d83c45003103401c0a44106048100964012100c020026a80c0302051815400d06001d044000642071650109102c2c0340100500702a205000b654100154001c81d01140d4649a00040c202504001c4100114041d41b61808456101c82805800000304240004500200090304403d00c038042210001e103603503c0b03c3e844002c048050008038200100c44000071074590702180f44c0c1c010500790b02c010624090b0300c1000b0f0300e0410094240c0d4000d501c0d01d0303c1440702e0b00f05048070b650418030401e000c651684540c1030003009401c65404641d42c09840b000009501c01e20022000e084420100644044417041c84054880705a9090108007080702048184000240f5a0ac0600660801801107045c84150f0701c90008441c000c4030024003501c03000400b07014031100554090009401d41183d968880d0248811644a01681c0b0a035 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 299796537 1250 299795287 299795329
    0x40c031d2b031409070501020d030b0a0e0910050c04140105210c270108090c130f02040b1b010510060903150209040507170619152003040609090209 65
    0x1080800c0c0b2941010404003403000300340000b410310440030b039221621403141501510405c901300d03001c86d001c0d02038410105802420006000d1030540c6822440000801080c45400703140389000c0304801520a29001d900d600f404c2a4440f81081595801402008021414401709001400701580b10300c104074084294040300c04680c1c0c43d6061901c0641c06140740b01e02841c4d01b8000644080388040303209540306c7c2000d0303031a1601034686810343d036140c2c8503404010350000c0c0c0b0885130b420340c2e0f03415030403c0443c2500300300c00620380f959034482c0391800e4125007000508080c240c05480c910000900031241c01a042c50400c0c100c040c9002d5000d02207100610006100d10010703041e40480324500e9056a00b4880c000d00b0510561411a000504820480038404141c90488000c031b0b415051418a00d461100d074040c220075a0343c201101055a640c0004450b801c0200c002003a01c11031540305c4000f0a043e01e01c10007103459a040c20800360541c85030b0340011156903c1400a035400d980e031a0554500c641710503240c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 299797787 1250 299796537 299796613
    0x60f0412050304050303030702060f1005100e031e06060301050708090307110f0a0308030402042f0304051204030503031008010b1509040902093102060910020c040c031d 74
    0x1007a811405550301c0598107000120812810a4010641b40e2192402d1181e82e40c07959130321720390006801c2903401416045100d01e564884800e0180c0700021b00a01c00a0440b0401192200404081c52084030300e4079503a0002001c4c004142424028a50842d0f000d0030700c90500e181c500001c0741e883c081c008014001045484294002c4d49038200c000d810090054000c4900b50740328140514142c5c0207440407030056141108000c80301702003051a50724a10101040e042d9010407050110098001174415240e5004282d040b0300080c160340b00400003144242c01864403883c2001d41842c03202c00e154800036060341021103070b800603600c1122000b501c40030700703000d5501c44000c5c101060040440d440020f40001c4040244059090441501480001c142918802000720300310681c456405600c002904050244003650807403920350303288801d204040c030441300042070040010f4151031b1035060b41800300b592411090881598580e15138203070600c1d00700402c00f80c4000108040610400d0b004c0b20746031416080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 299799037 1250 299797787 299797793
    0x31e020a03082a0918010b09060705070b0403060506030709090809040507111002091005070b040618150501141c0605060a0305030d06080c120606090406020c01090c0e06060f0412 78
    0x71182c00060003090f00901c02500c2441c0c0103416840041030f81c0c404c0c1600c04015641da012101e9183c1a160031102040c1810000000d100c801d42141034100d0303c1c0d00a4500100c0c0314000c0340060070045000307030000b045a08095003490705210164100c007400c5070a02c40300d0404a200d10f0110b071030f400401d8030005071035640c545c0c00700c65442041c1d100071201d0051001940ec0c3e003000e50003400c01c85008a070503040240407070009540d24400c400c2c000386030304008070008010940c10360000048400140344405004100d640b902664595500700780d2290703a030348006000c604450184034488100c151000c9010307540e80d0070000300740708240d60000c100d69150000109243c9401144c4c400541d8410100c039183d8a280d40c01c62301401c1540902c80c01c0d846564101c03c4a0301c0c0550300080708c0103121000d0300c1d0310340381c1106000d00c010b4024015581c15800b0001c0c2107020200348a0003441601907199101003500305942c144052070042c1516126610611050b0500d40900b02101c0c122006e014805000b520303185 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 299800287 1250 299799037 299799061
    0x6070e04090b130605011508040f050a0b04030809070b09030604060b0411070c170606180601020a020d06140f07050a030e0a0f140705060418020d060e1003031e020a0308 74
    0x440040003141c00b0002e0194805014000300314a80c4103d4051000b6a00d402000e21512400c06102002805810102e0f02195401110fa1009805030003903900c941c3d05501c5449603c3d1017614120002020b01c003c00c01580c42c01d0000c000a00351024455240194040029503204001b0740040c0c415981e90380881125500c1c0e41c0540682100110802e445030500d08100d110300340305101b0000500d1000038410303c0400b0200d00e091158100074a01c481800001e00c000b003880000800150541c0300342410350001da80c0344c2d400911000d21408010070310100c24050f00c406854090513140c540b08041d0700b4000082e03001019100c00041518002412840c50281d9901d001c0c13040c0000303016250908100400c1c040074a0300500080c015404840c203030340c0c1d528140205441184600a94200644030702e0318010b0b45a00200010003034400d0108015886141e80c2180410982e11003a24a0704400c04008164114421180900945550041c10222500e019442c1c4251200081c10884401c0001d21090b084c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 299801537 1250 299800287 299800301
    0x6090f04050a1514030a0b091006240207030305030c0901030902040e0c09090a031202030601031b0e030c011d090702030706180c15020c060a0203040305010e07030314040806070e04 79
    0x3801481241412065100100512003808422040f5444081a020991303c031080076200c02400424009040e40c41e40702065101501c040d506008020008510307042da0702483c0042c14402032001c0c05003803006104403091406d1182c0c10705540000300104046908803054a80c005401d0040650301c1c10700000480080004000c020f6102c0e141444540200070000390394026503005488000b110303114074995a41d580c12008004001400744010300c0ca0943e420303000f80d90096810704000c5800e089110001020b10190303920791b0002003414000f10b580b840c04020b83d044001080c00d1002c02c1d06460a0040f08054034005028010220035000c40d050510801c121801a07401120811070340301d4010900f40c6015103254280e03018501c1d0704010a0150306110042d620709542d400801040e1550320a011403608040461000d500051000002050081c080c0030004620b82c3d01030880d02d0b007149000b034903940b036501d0b0421002000340000d11080b003000902a800c0b034950f080c50051524518000340c0945a4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 299802787 1250 299801537 299801539
    0x905010308070506010b1206060d090203061f09060302010e04090c2115110711120f0f060c070b150f060408030703111c11070b030c0714150606090f 65
    0x1404000000380540c00002e072841902c25000e84d0503599075543c1c0c0398454018100301181000610005c80c80b540340c018000c0134607000d951004501416507070002801e11404032075294150400f10300440b540c003114403141d00a030801040c2041a01d0a64000070801c95182d501e0500071036507008103134144000140d0314401800c248011020464000020001c1058402000c0b83c075a8101d20103966501a40d000794000310140300308250a1120079100c00042c0702038001d600c1d030010244218101668002d12910b0350800c251b9006080304000040400e00c0e242d0700078a09240c81505108000c0055959030a00f1f030414204402c010042011314001000b080002007101e60003500003400142542d0040090f200c00342c060345801c0c0000b8005083c85441d40c90901c000e03800c0d4000044400c0106015200705042200c9020889030703001e890f04600550f5a106940c00714400350080303000030402030071000a032580c414201c0981041a40c000c8030b030150721005021203100701e201040c0358440340c031025414215400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 299804037 1250 299802787 299802791
    0x8060a1202280f090c02060c030604020d0905121e09010c150b03010f1406150a05071403030106030603141204180b0a0608060114090604050405250e120f0a03030c050409 74
    0x1580f080e4140c0101d08a00c5080241403d0440c9140328038004100c251007501c00c41a80c80c510341e0f60104020003507006101c2c04055555840e4044007147c41003100b130320303898050110356644a1b407954404103148288070b80c200400340200304440321070364811705103014039a1048914000b03a0070400c112002d4400003441039010340c81d202d010341e1555210b42007103e000b666448283d103951100014400074068004009400441c10000c0001c000d200b00c0040540078021101216031122450712a400d6038001e900c000d00090b00d4810038824450081811540014904001c003161381c0864002403c50140b8800c0e03404224101c00f0b0505500c1c19500701c4060040010001759840e500c900c0041c001e01816a0f01724002172614a010182e0b240540448a030010010705d000e040514203010000074040c002c101018042500680b603031341d0110702072008011400d9865039001c8804a10a00c01d103044403003070450007940a6524492600f40114450f030200390186008202600141000d5529104590002004d40c2c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 299805287 1250 299804037 299804039
    0x110106090b330a020105070f0309110609191202090705070510110f072105090d02060306011e030504060c0c031d01031104080c0f090105030d18030204140708060a120228 74
    0x213039065101e10300c52019500c81c55214144041c00300c00300d0303112041c010259411001410254030740350380a071209110081c806a1030415501104042c06000d41c4524060001d11141000714603100700e01c00c1d03001c489481d0041c2018201e854203a03851802e5500e0040c410f55a100141299002c4401c54410118141845558002900d055140710803c091914240e04121843d038000511440c21100540f0000b040c14480784d050b80c003081703c40e5102600b40c6050054202d2823017448108039403155402151a10009034a103000d080c007000355000005141e08200001c0d40200001e07801c010030034003600a03e0520040d20700d02400603002440c5400303a20344141008240050364400000d11500c07803100c1034804103400d1058406100c0703440c400303004d0180e00d030f08401030500c501031248104203070010403800458031715996500030070304032100501c007410300c2d210550800c82d52903041001e2070b40003032007070700c040e6001c070700e030150426440014803c02440740380d40113294480401e03c0342c42c01c2404025001d511900d2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 299806537 1250 299805287 299805307
    0xe071a0c0c03030a090306020f09040608150f01030b07030e0a020a1202031203012103030f0908030406180308070c1a090303010512060c0304151b110106090b33 70
    0x540140004032400e10070150780c5001414048180c0340b20900640780c40c5005402c0d959183e020350040320035502858001d114074501c0b580e650160000600c4d55001604814125480000755088001c03c0c030703040e1280700700c01000080c404d805069840304141c43c001174209151429a42000568078002c0d41c020b00741c440120301c1078904200000c20354400c5007182c0864030004000c0c001400b092150805200405078500c039101b0f994881d01954910074940029100c10030603d100440701c6120064680d00804400c00040118038071031b4005050f580c02503003c0640640c0d5000b480c450b4003e004004108001141c4010080030404400700c808640380c950702c052500c01c00c203907a039400034441c2a124610a0508010f85031002c0391343e6000d410480109440c5a555440d0403207d40c0303042c80a02e000380d89e10a05840c0c1341c0d01c014144514400c103030752290322403c0c014900c01d09403901034000c0d5040910b0000309222665405d000e82083c0020b0b00500e64940250400b5108840c040c00c403483d07048d810004030f00f100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 299807787 1250 299806537 299806589
    0x203010b090d1b030b070e03060f130311070e1014131d0f030d050c030f16110f01060302040c1103270901030503090a0f0605031306021b0709051b04090e07 68
    0x708146c10390b540c9480f20329000400d41d03603c3d001e46100e8030081c05a80404d500301c0b841080c1d01d0b4010f020303080c580080d001c1e585a5502c0c2c00125403116030200d6403103050100c0c10b0441040f2200030711480902d9907142100300e00080004079000015001d2642e144408180c0c141038801e4070600e92501d10581e4080640700c1d104c80d03125800791003480017003845c1500090283c0b900c1e00c1528003038840100001901e54a4425040a2143c42c164510911010292416144004214a82100104d0750001c10341d240346206100580e51844a0f07041031251594400300e080314004150b840389111300c26001e4a1084400012500408501009420022540000c402c0c404004001e140030700c001d41e008681c40303980c0c0d0650340401d0054000c1e0b10018008001099a010510498824040c00303000e00500c0c01d1032101484400f08000c000c1ea2801b41c001c810b04104001071803040d15405100150040d52a040c06568900c442c841c9015064005584581c800a0300104219402c0903040580b0086403084c090000503207 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 299809037 1250 299807787 299807791
    0x31c0203070b180706030209060706061d070306080c06030c1308061b03010303050307050a0306051f090e060906190308030c030a0c0c03020c280312020d02010203010b090d1b030b 78
    0xc2c2e124003607000c50380b0601d418054504540102c405800281e04040c1c0840180d030000350381683c4040c042c004100400c105101d0000148903510045071820907600e0301c8640b038240100322000b4185801e90400c04014081109681550120754443d540d0740c403244072030b40f14064110708244000c2826000700342c2002c0000c0d182d01540c40312554000007140d01a4502040c4000d01006001030414408920040d008402500000c0460b04005c181140c0302c80105511096405202080c03030b501c40d00080c1820303040700403d4061b003480d610042c0c0c05c3c038040d80403404421016001d6030051003001c03144695660103820800146510440480d0b8130308003c141c40707a664100351039840c0e481c0d07d040f09503149503004030081c003622507264024061124941c001c1184032007207030001e004903d669541e81d049401180005201039071242c1107010049021140007450410056504004c0d6841000188160002501074a03815001140c1c0184090114681032000c80d840b10322182c2200000903010040102d4829814 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 299810287 1250 299809037 299809043
    0x1f11031201030b10121a0c0d09120f021606080603030c070608060103111603120209030a08070b061e09070522240509121504060903020c120615031c020307 68
    0x440315155821204036007545da034000d00d0002008144001c52401e280c071680c0c440c14408080e41010651401d00b4107a584d60401203a06d0441034800002682d040300c069030342070300c45100500700c00200700c201076821090b071700a207400d1044420026240d941d0410171101540002c4080c2e0348403d076181c901030020b060070780e0780d240481e080c9001000c4500f040340948400400841824456114903102030380d6a1040c0c5101880e169002c0080c2d0301c40e078504101120300d25100c6c048540d0307508007504280c0345004000d0100c81c810051440e10004107a04407803070790701c02035040f03d410140b91520700d41558a032240015034009074101003001d900c2c0d148225808401c903440e4920503a1442240740c07004034060700d405906000708405204951090034500c0f800312220f0070260480d02c2481200c028030140100c12642110340c50344230340312201015410701803900024410b90f030303106c03401080c00c0c4810744410000348070f0390040c6647c40140305155010003800000f121009104225080031110080d16940542416 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 299811537 1250 299810287 299810311
    0x51603050d0c1a0408040503030c0a02041104050108072a050c09090c0607030323010b13090605012a0209090d0305151807050d06170c1f11031201030b 66
    0x14881c503501030074030014415484441404040c0704102003031802e4102a10540e0900c005120109039030300c00300000c0480e0a0384000030001804680304000946482131000310a2010134042001305d80d0f00a0070032908603a2504091340d00c200440842001c80c0d11014600344803000341820102881404240c46102ca003007038030203070341c43e07525180082d540e0944994548d0700110100301c200c1c0441d11a40c005886400c4000c2e545a0781c0070b038240c148181c24004c0e08000e03101100001c020104240a81d550310040107401400d10403680350400184c4000611802d03e0076800051a003000a10072a2001520b02c56004206681c3c03410540301041c1d13900b005415481c0841d1401d008680d20003040340c0180e40c9528024007800c450f00c2051900080010054030b180103105061168880484050040e4006403118041a0990641c5040c4030b51400051011203405003070282c900300c81c0e0440d14028034401991505200b000e0303001c910300305072951103000d040703810f13280c0780b80008001c2004071180e10340100015451 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 299812787 1250 299811537 299811553
    0x270f05190501080c060903100f0c02190206030c09060d0507020102220e01030f0309120f0c0603050f0103080f0f0c03030603160608040b070c02030f0c151c05040f05160305 75
    0x860011a031080c082c06545a04c5104655020f16018006210b04036010b02552000f0300122802815110501e990441c1192103a0300082103039810004185025120030752966415540c0c0c0200c0e440b44801f91100451050006440341980c50390b10803039040c602c3c40c8104005a1902c408000d000790822901082141001d00c2c0c0c2c01100100704c100c80c010780340701d08400030780c0ea440c69480c010b01c601110703000c0b010f0103074905001504000052045404502510741c2072036041103032401c0840d240075504a901458030f884140040060544462419a5800106242c1d105103445426950380100c1e40b003507155003400a034040100b00044051400b80384254110350000d04031110324401c08455000d54000509902c00140104081d1074055030021914204070003010081d801113410060802150780c201d5216010403212414508102a0380e0051500ca1504240c0b0b186040e500c502126503540c1d10741034803100414188904040c0d0b0141d480d034020304841d05030044661554030010540300070340326400f9030b1032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 299814037 1250 299812787 299812831
    0x1b03030e04060503030301090e0a0f030c0312050705030402191e050a0f080a030f030615030c0906020c0d0201031a04150e01082d0703081b0105091204270f05 69
    0x342c4094880040145080d84e01780740804008003c1001d0315101c2e4030a028265010420329500825160701035616407425122038240503210542050f07100105a00d80010032040035404001e894110340d0445a480442c4d646000e41d14885a45400070503110040d00c2d40002c1c02e80155070b40800b26103040e02e00c00c845a69941d082c01103080b5134480c0020743c1c1c21440c41c3d0400030303100c2c1240102158050a001804d075807210b0700f140d1808891860f031400b0070b0785c0d03a80c03103140c0e0303600409140010265031005260740411175011448940300d0311002410702d41c54a0000300312501003440c02800d0f40d0058001c2245484044900701c01c1c1a151207107916021900001160782840403c0342c04844c464141050340c02038242441850314541d080c0502c4850240c03803c04800500340100a040600358010445151600055140d0860344050300c101290b5001420026016a041c002d0f5003c5408600c050701c0752400b240d130311403115034440c850701191034079060b504542440c8590180d400365403008280b03e140d80b0201 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 299815287 1250 299814037 299814041
    0xc0106050d0b19150311010e100509190806090304180506240d1103070e0f09010b2808220b0f060103110d1b02030403080d0f091b03030e04 61
    0x380700544a07030710250005030b446141c1d004168a00e038001000044e042d46400c150007071300880340c01c111340d03480102103201c8041da440103c0c03d803080c40c111a00b1040340103d80f4081c1492040112a40c080c0d0f0305942048500781020a10030300901500007036600c0c0d86080346a0b00d8482d8014000d032089a10b1040e1160402e14040c400c091040700c02a010b041d482c50308410b03180240721100c19030b00104d84108200700e6011b10601403504482c0c56051129102c0c1000380f0050900740d1004080c0f40521418004d034881c0b983d41081d51790469904400c0c4d1a82c0320801201d0501c40001945203c5055000c20707114203041c0d903c05242c0f03100d500000d070501304880100d00c402d00c9605466401070044000180495521007420f00b845070411814100003900c0c5140340110142e41c1c1007402400c2a8696400414544010701c001200c602c440500c080c40c1b4041c2140d8844207103010340c0c1c51003501d0380e80e9054246140c040540c040744002c0d8201c600a401ca83c2c18400b900008400c5000880024075104040ca580703003013138 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 299816537 1250 299815287 299815309
    0x6060203030702030421020d060501170d020606060d1d030316050906192715031112040c1d0a0f1a040908070f08030124090b130e01060201020c010605 66
    0x2d40d01440c030b054176000030100d001a03a15601520b039065800c40354016903d544401c5c64251141c100841c0661612407498924000c00400900640040c0713628044543d000c19600e134000b400301c9003161140c8140405c000107042e00810300c090758500b0820784601020000180d407140040003515148490108800c803001d01030301e03041c660002e105002c2961101500b10810301c10000901e8602e5041031100c2e202c0580d042400452180e0504141c010b022144504e500c0016030100385c141409030080e9480c02d4905841200c49001d061032502d004102049101d80040004000303404104821500440d80340700364800955911980515084204070342d114907014981c0000c1072a0113000c403c049030b00c10b00c07000d09071800381201c50040c200030b00c1c000203e420444100d003d00980c1c00c3c940f03d40c100002c8034186091407410b203045213000310015100a41c02644a401d6812881c00a0740710880740c03102c16282c520381d402080c0d0801d90400003054856055015200c82c24104000740101d43d0340d203060150003005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 299817787 1250 299816537 299816551
    0x906030b060909010e120d0b0411040b0f0403050303070e0108070f050315041e02070507090e070302060f0c0109031d010c0c0b0915030a0f1a09060f04150e01090606020303 75
    0x1200000480510b419000e503a40322070050000b213001c4203921442e07401d01c9040140401c21010100b040d40b4003089030f1041105600045d81d0400a0780ea070355441900700d0250307210f940c0c600c14000030f000d4034041b0710f00e0541e4010350b80034084035101e08042030f0182212040085c5540000c0c420300c00182054802c1c0c060000c0815280c65440c0f0b10b03240c000743d85007a0400c6c0b40003950400d13200c07030411160310b2041d040050381003a40c2a0050b21994a40781c01c1c2e041440e00d074000c1401c582051031800f030240d000310b03408003240d038102c610030b54880c268404070307406000e02c50200c0c0655280c02604070903d50030468411107501d60103100c0d640300d1015401501c194000d510042c1c0300405802040c802010703c1801440103c500419004005680141c9610f83d94411940c400e07840c1d42b11005240700541c18012420551f071041d07400e8150780340c0c20002c10741c90640140058450703403d0500410464071345500449a5002d12400088515203414000d48041c00a2140c1d2424914082000808500c0402500d001e848 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 299819037 1250 299817787 299817803
    0x40e0606011d0a1a030a0e0304060e0f180f010501020c0d03020717030903060106050d0b01050406050a080a0e070306140907210c170a110609010c06050a09050f16090603 74
    0x1c1c0c40050311880c1110694156044220b83c0f1003c1103031102e120001010403000c1c040c8079136928190916800b91000030201150f180d0083c40207214040e0040c00c0d111034440165246001103d8040c00581e11003509a604851140c0320310070702040070a9055418141ca0080c4c08440b0603803505001d21200509070030002c2e00680100005000391128001c80e100c44521007807c6030305065401000070f003400300a030310030350224a002400c1440032040707024217024014242000c07800d1070b24040001c3c02c40e01c2503008040c20490b1841c002003020005600080c034641070780084034405600e900d840e500034807000030380d00f120110394030001d10449000103000c4203807041d03100081c18a210040204044040c260001c5030759420000d004541038142728400805a0f1081c070080882c80c40c1c03070500d102c0b03081041008900070b2208206440e17450b608600407510940e132120b8001074942c0c6400000004001840c03006045002c5ea01300c0982502d07000443c210548800c0000418580d40e881c4d682046a00d10f12005210031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 299820143 1106 299819037 299819057
    0xc110d060e07030b10060c030806010c140a020102330c0f070605060108071e050913062601090b070507020d020406030c0f0902031902070507080d0e040e060601 70
    0x30b22121174406803a8140a4020300010740c200c000780c00d0203103a602003100f69110780307030030441942c102da1038107502328035030443c02e0b203842003004142e006108010041d001c4482c22003580c14040a5000c0485920380031150003100150b0040c20100140790500c001007650307100fa0006c0012503c90000002c8a24002d0005001407001070030a400f000b0f607524481c3d40c104000381440c20010703001d080030764582c01c0d0000040d28115419a89a059504040e80012982c0455040203c220b80ca120041700100c01044641e0880e00c40b0341000c2d2281c0c50304404900000e001d40c00804519001070688441c034005600820142c5180e50b0044034002100c407020048803421001c0e4001401c02180154518204190281c082011240012401907800074020041290410854004242543c2a61268100100094000311440254a00480c28142172208520340456640e200c1c4005271078041e070407 = true := by decide +kernel

theorem cover : BRFrame.Cov 299640287 299820143 := by
  have h0 := BRFrame.cov_init 299640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 299640287 ≤ n) (h2 : n < 299820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
