-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4047
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:25:20.206234+00:00
-- url     : https://prove2.me/submissions/b0136244-33b5-4c2f-afdf-4f5ecc63bb26

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 727697841 ≤ n < 727877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 727699091 1250 727697841 727697849
    0x1c020f070b0406030203060d0203030d1d010501031e140d05040512014a0d0206090c0907030b04021308070602190c050f190e10060f0e01050313020604082104 69
    0x2a00e082c2030030000100e009400c0248055004051007421501699042000d0507101e00050b07800325030310224000c2012084e48000d4041c9c510303814540140006003080d01e086c0382c610990107069108a0b0035090501c1c2d21890000c144009008030302c00c43e20b2140e44440100142c07042600d03106d003d81e00c80303600c403400c84007001d004d900307091031080c00d90400c420719000d0300d02041c980c1038290400c1c2214901c0c1244100401c0500d201950200804101140d01803003a03a90007103240c0050501c0074040303008a0342c05d0b0300c0100107404142c1c1c0e90a0b0180e4641c2c0d0380d07060355940404041c08070720050315200c116695510300d0250801601c9a07808c0042001c0e056542c0c080b41030303480380143e40350602d02814880000d6100103180d512030200c0c1d0840070103161030b140e0310313000b0b01040350300b429076040c11a5045810801f0350001810045034006006600ba00072031640c10a00080c0707000d66403980c07003000d02c000d20011910025800800002c0c001480307180042c0d2541c45850705604103a48802c402c061010034407035441 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 727700341 1250 727699091 727699109
    0xa09092f0a09090b04060801110c060106110d2d0c0510020a1202072f011407021806011412010504060b0a020a0b041b06030f0c0f02070b0d0e1c020f07 66
    0x300611846603d600a041c03503407005403020030025201d601d8a400e5a0070303100a21120301d0301066051000c40c00b00011401030a1508081886242e84200c003901e40000c686c581e01409000b607070b220104046c48580c520b05200030744039141500091000102100c03443c0340c003580d9a10500448460282c9a07200300d4031b04219030344a881c0e064200781507a80203074215490a03542d0450307442d0001548404000401140c5080c1c500102c450811134001404c3c10514104075810140d05109940c01038a60401101055a41284c8102245d035490012515581303080ca4000540901040c03016501c3e1225000c41c1c1a20001c0707509024803901c070360800040b4090400c510340140e0014483c0d10204841c0500786400500404100820300b141c915900c10300215640540d00003a91107a0010640b0141d1203058804112443c2020545200d1a0020350784e401c0d60148848500300000c00035596116980322201121001c0180c8140c000003080000f00e072810b807400180980a40f1858904013803020600e41e05890443c1c0d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 727701591 1250 727700341 727700357
    0x3020d060f05010e0d1a0103080417010603030c1e02031002131403151504020f0c211e1201080a050d02010504051203070e04060b180306090709020a09092f0a 69
    0x1302c10002c20b444182426914510311042c51050070b11642c081038003860041d60b0855607a40f902c001c03031202c41d10052040d40640d03d00201400001c0c0d00241500015800c02281d5401c0800500050000f505c103000095052140c407121400c4002c0980142c111214007a14020300c00341d4400c88803c901c0a2a00341c913078103812901c4024026801355402c0c80d045094070f0420120f0240010100e0100c1c1d00c02080441c80f01e001107140c44000800700926140c00060b00c040c400e0440c80c2d0b8114210502404030301c001e540f41d1b0500082c2c031401d180c00c1915080c01c030402c00c0d5201d550b510103950392034502ca183e05507042e00480a1800200d401405024090341c7d0102c000e0010002c50303891a042c6400181010080140f6584228150350760350103182c019100b040d4550707a40d00340004104070b0703890b810300c0002d002e074100e0020030031802804242c1c4401c4444445002d6a070300100d4030104c03400482500540b22045c9030400c0d464540d060003111003018000356540f40e403101c06034100480e841c066200130ba00000c0d042 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 727702841 1250 727701591 727701617
    0x1908220b070507051609051504021e0a14070609030906110a02010c081c0506090a0c050d0b0d02090705091009050f0f1f110c0d030c030e0a1503020d060f0501 69
    0x49000f096a2401003090f00c140080d2100320a08043c9642d00220100b07071a0020b010150541499020303c0e4401100c0851502c06400317581c064120705500c40502c126004140d450646005180704030b00c040460b2512a9102c0c1c2a24054000388681038054001400342c2d940880d016008800542c18010751100501c100f0100390f0045840d41c00301d80c0112003240c018002080031400101d005a075100e010307030003c1524600801480b0407181d0081541000508003d00540a0b60b001002c480c1000ca9030b82c00441c0205e000c1c404140c900d40307101c00094200c1207010030400116480405060740910032110911580f60031041151101810b00a469110704102c1090000d0300c0c021004042d200001b6081441c100080a44c405070300728141001c1021a20214820140c490107000c284001031084071041c0300b5200e02d840c02032424006100050030701c0761b0700b0384000c132664841811000a010702e82009281c0d0018840c01000303904018400b400050400d00003052502d10290749a0984a06940b0f680c400060 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 727704091 1250 727702841 727702847
    0x40b0d0b0d08071401110d091109190b03190b010e070503040809090601110303011202090603070b040e0408070219050f030c130209010c0506040807021206060607060b03031908220b07 80
    0x102d900340c049039944c41c050707103040044150103400c10600087c0005148200e500300801b022001501c01803041001c41c04000070308016400388681c10f400302c040040c0150444001c81d02d0822100d207a25001e000b459040d00c10808025910ba05a40000300c0461440d02c60351820380c0c0e980000c0e24003c110610074041c0c9803c500f00700d400690721120524103a8083c090039880603007954000e0300041c1e2110954440003040d400e01c12101030b004030080c1c1c0203052440c9014222b1905000758000c054085d0000303070201d418400900240c2d107406400802100002c0412111040005100c0c800d940c01050031804501c001d140114100d01c0c2c0304005070054520360503081c1c02d44001d501620b1304a041c040783c5212003001c1802007011034426841170842070303a40d403218010030100d080080840c800706d5200e2001c02c0540c1e200c100a5801c0c8550040c1e0214404442d100064114020031103280318041c2d2200100940c00d600c03041840c01403180d1501025101d0400310501c072100040a00513140d00000004190070f80c0c8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 727705341 1250 727704091 727704113
    0x501050d020a0513031104140c070f0309080f01140109090332271e090601090b1c06050102010b03031c090b090a05010f0506090a0e0106080102040b0d0b0d0807 70
    0x10a2904074505804209003000302c8a1640086d40c00000c0003104608a04080c800e80380500900d100703030005d514041020000038819a4001001c1a84140035041010b0054003a100501180030036103d42e00280000f40b030007401240001c000d180458000043d808451340700318281d240e0075941c0e280c00250f040700356001074629580e81c5000361070030044040e2800c02203400740c081401c141220207120408908241020302e02c02a1961040036000c40c6004940040140c41c6125003054680340c02c107076580801601d4819841d800311014400003e2400d1800704200c180a00354001060100003007074681c0012800c903507907800325075090b0b401044074408003843c1058800e120105108081110b52082c0d403501c01c010416a0484400d500c01440b5408202080c091030f40601c0100900b0441e80c54030702d002a046040140030050010769500ba001a690001e4000c1c42c09005407100955490703a40308841c000b80c1e80034244050300749103004140b050914100c43e00d40d01440c0c02c007001c10700300042a01c0702c40700340e4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 727706591 1250 727705341 727705357
    0x6030603030d0c0e10080603120c100e010b040906150801020a0909020c03040801060602030a17040b0a1503051902011706060421060501170c0301060e15150403060516090501050d02 79
    0x1010501365244c0e540303000464100700780903030322111641415420b062070080061441c8903094801e08c5a54900200068400300701c4c40c4207640400c0f007460f1420068018000c46000c0c0c0e0f0894103090781001400b24580084005540981c8a1440940c2c0c49094901303c0c010440400002411840200984e141d26005450484444c10589144c295280080e81c21a4056400382c0c0c00350f000450444291604415400310104280c48038280c44e180c42e51743e880554034014041da088580d01c0e4444c040700314109684c0809140d00004840341358a1848190070020810700040f4001840785114160940400404502172040a0811030900382041081c4109000107d02000c02420982000300030403054020700d4020a0b08024400f544281d50300700504012040030228080da050400401043e0200103801d5440404004c040d15206d40440005840803040c4003c0c0d030f030f039907c0410040140107640d4440c0d03010700c200d42000c810040b00000c00741c4043d01d8520810340800d005200c2c120f41103d031600245118 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 727707841 1250 727706591 727706597
    0xc040821090415090e0601150309020f280b03090c030a0c0e09210415110c12010e011d0c190603020304140d09050411090a03121e050d0b06030603030d0c 67
    0xe0b444130341d44c4049400c0e0302d441e05496407200c0d004205100e040e503050f1403c400b05190520058800741c02080c017008070000080e024000d9208062155030712903240c0c10350410700549c41413407160b40d4800c03d03116800c1625603542501514228500528001401c405d09582c41802017200700d28001d441c040c800402014103c90b4024000e804075101003800c0207040304e16000d0307d1291514244126036004207806800602800305241081c0340e1580001000c0094020840345511001000341c0e00398050500ad040c40e00d11036007400302050900e190b10900c2511400080104d91820050100300851001c003a0001d4200c1d400490b018414035201ea001185e1181c05511041c6440d411005043c6c130b00300448080c8800112440c005202519290040d002c1c2c24a4800655041045100010f1000c1100d40300080c081c4102044a44c040740c001c4017000802e0186c152181541080e001c4080c05030b900a40e10340340901d01d48124482c1b0352400809681c0201c01c0500198100b21031001641d0080c03c045a0302024 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 727709091 1250 727707841 727707881
    0x60609030312011d0f0705030a0e030405060708030a1103040c030305070f0c080c09072f0106030204060617060102060708061017100f05030606031c170c0408210904 72
    0x401503111003120700901c1c1e0034800c08485030140228440401019080d0110455600b091029180c2c0c007e05580d003229100c00001180700e81580b019295128941c8126000b072004604c0d5018000d514014500c61603641d0001c1c00303a0000300c03212029520003110000c1031154111410700201e807041024041480c8038001408099002e0744600d003204c1400e62121072140c1c052584811142840c80216400421608000100600301a036034141103c420384000d144081c0800d0884030310500350804c000841e009001001400d485010043c41c0000a440000100c1115004150340754800a5142e226441556814455442d420104032445072a41403020802040b030104005000c100840c240c007d41c20071141710707461490911120388800a5511551007900f00e601040f40a4030301052840070030b004004070741e01c41d10b04804261903d40e00c041c4a420040090020000782000f91070040c000d5441502c01c54260381c1b0040402c3c8031014000c0d00c1d801444100b403080c0d5441d81420b07003000782800309042181c80 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 727710341 1250 727709091 727709107
    0x80a0201080f1e0412020d030603030f0c1a0a02031006090f140402070b0108061909080307140f130905010503190b060d050a0503180907271206051006030608060606090303 75
    0x42c00c3e0380a68068810780708402c09010034a030104510700b0000000d090611201d0f2440d18042e01001c0000e00100501c84d103d4190010894a1880744080b1462005c1040c824184100c01000030341040300d027010007d9055001050040c05410103d01325905100c1e4040303584d091201d041e401205070282280c00c960203200b00e42c0000c01140c40b290180c02442c00404c41c5190407410950003012501c119282d40d450f03c2c10200100320700d40110313540702140e401d00da0001003200081d0326861041c000010340800c0c020405101c04641980d0b80012940a190107100b1640c03150205501c981d80200c4100340c1004801c040c6c000108811507140c0d2002005140c89000c1003103490b41400c1c0700d41104216000d03000001c1c2122400600c0111102c3c3d0141070307881a41c0d9241651016104000d150280036400295030518000b0107950180310016102202d00056510502d2408401a100948410385001c19004000c41c00520034880c0b0f03011142d010005080c107440e00c43c14007146501918043c2c1c0c241c002004600 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 727711591 1250 727710341 727710391
    0x603050f0a020f040e0a020f0f0d11040c08070806041a190f0602030a0203031305070b07031809020c07090207020f0405090307060c03181b180605040501080a0201080f 73
    0x2003110524601800080c0e2181c41080358200340380070002d00c42c503c2c18a0145a15500080d503c216950550321840c10050500000d881008521134580c0d00c072070090003001c1084101555507042000c184e0b41406074110700401036851000441d001000101e40e20005104ca1400b60080a00343e42d410b24103082c0080d84902140a0366201c1c00f02440080703c0c45005c0140002c40454400105280e202a60411003c00381c02901d910001d060030421440c07102032002440018003207100100643c001c813903500c04140c46e0180101a2440b04051282e02d003000008641400c1d0003110f14240d0100d018107442070030306030944002d4100d09001c2c0c0e08030a424003565115181c6104a80c081d02400d0001c64a80d05186080390079610114803441c205424005055102645060758200f025400004000b15402000f080e9072401816408803125031036001291a2465040e8442400c0c8d60042d42d00707000341da0300d410165907240112034009002682100c00526008010018140c20040614102001f031303140314010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 727712841 1250 727711591 727711603
    0xc170313080301090b0a3c0b0d0b130c021e0118030e1306050612430813110310020a051c500115140a050a03060305 51
    0x19040556240b0145d111407a100d03118a00901c108030f000c0d4400c14010780074580c507802113542c2d101042a13401c08a4030901151a805000d131186070349076600c682e4818000000703031103010a8540a002e1100d40296182a28000c91941a007940c0040ca158070100011345070003030742c90100c2c010359541c5164940580480c001441e0006000e503846c00003508800e8100403000c9400942e03082113a103840410049515984155049107924070000050f030742e2941e416051107071802e02110005000300b00750b94050356100440300c01d1101c15010684002c10889426660300109480c1418482c500084102c0050408492481100b00103420b81c0d909484914140707090f81c000840d960045400440c1210f0480301007403500c01c600858090920810008400284004a200408030034803030030380800084000010303041907544000e003607000800315031908400c0c64503202801001c42410104c417140500328803a85c2005a46042d403d001c900e0708040580c166115070002e002c1500b8551203450010109206001c5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 727714091 1250 727712841 727712849
    0x1207150e09130c08060f0a0216061d0c010c022d060a020114161704020616060209040b10051603141207030f0e0a03030513050609070311010c170313080301 68
    0xc50074aa202c646000c03500c2d01c0a903040421550301020400480180d010328594201c1c0100340e0060390f50b00d0001c1c81a0346616240301c0940010308140d5240e00c0505c10b41c1c02c00e4080321500055900300c1c1e000e0401100c0304516075a010b9440194050708460000c0031024481401c0c01d8440a012030240c0320000c034880d50460214078002d41d55070101504058412440c0d039030700610220100104101300440507168591400c03d841a04802c01c00080464840000b00c400c0b8a8404044070440445440c01002942c441ea4003203010f1424200b9502d0b85081c4411400d90000042c0c45083c180f54540d151000604c00b141c40070340c00c204050b850717611070046200c000c00e0307624420005101d5910306250082c050b0340d41c1441021120740380c1400380b2280c0d040441c00890840c7c1c1442c01085580350300201541c1c070242614041c0c49406030301d05000d094640025010100c0c0e00c0342d5810306a0440d040019034542041001c0580700003000450424201000d5004540c890030b206a203958200054848401540003604 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 727715341 1250 727714091 727714111
    0xc0a020c01090b180406052101150510050c0709060f03020f0303030c1611040f05040b09060606030c1305100504031e05030d0b180702160b041a16050118020109051207150e09 76
    0x420223a45010038028001c04503405c80600da260346c90000461a04414040950104034010840d6034030306600b80480c40c01084840810300c035141d1100203556210140b48412841800034a65001e103509012040d24400c1d00309090b02c0f8240102c099081c500c03084552002c90304000555a18100741d034a500c42c6000803c203880000416180500d020308038010050300480c40da0384124100300841e910801240e920200c51300b441501c800f0317019080c400381240ca802c095840b910045a940c04c0fa64804040c01c02c17207004400b100e040c400b824043c440c040c3c5481e000542180c104021685503124941c2100c1d80d01003010b402c0d444214600c244070200d1017825a502030041e0800a61034120000101c4010058000340003442d03d071502c0e10388034902e45000013200c10340a034400b154100480d8040b41a0300321184d04400213104035050b0504410b1000440b00b001ca000c0b40110700080b0709404c0440c1a50039083d0762000420025080c00b003200584003501c101002000106c03841c0000e540c44980340c0703e024a030108 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 727716591 1250 727715341 727715389
    0xf0b040326151306270b06040b040b0f0d090c060e0f0f091b0406120c1d01030b040b040207060204150f0c0f0203010f02030c0a020c01090b18040605 65
    0x44034610403000c0750002034540303103044052101007010b2200401c444641100c40c3c211000c40f81d045035000d4072013944111081209400300042094000d24984c0d0700c51030380103040103080e0700101003044901840c0181349101c0c40500041c00f6904242c00103013207008041401500b07065603102c0728001d4502001e0300b11542001080200442c54004e02c1300b8424040c101e51110410900c1e201103160703c1e0744248020310580004c1d021076240884a0010241c2c4010b4091040c3e5580c0c0f10030024008540c04620a40010b240c0840c044060303100d4007620711b8614103009180600074400700110b01030949104200c1d17005a480ca201e010966841c402490840d21408000d80c580340341c070718000d10301550490740301d01388640b481251007840d5005400a1082d03501c044641c440398424000305e0300509000360341c0401e880c800414012156404006020546007a42c2250000001200111940c0950f44540342440c002803220304042801c1c40c4c4c10340f81d02500900700040055803040040d613004039800c07902103520010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 727717841 1250 727716591 727716617
    0x15040615050109052b050a120206060303070201050a08091606120b0415150314040309031e0506010b09060903030a0c0b0f07051206030a23150c0301060c0f0b0403 71
    0x1030800c0100a00003400c2c40c02e040e61030400440c140d041c05405056044100d540418181d5205502400600713412074210380c0301c5203461804900b030300039210064000d4440c1c900044d10a190000c00c03102e02a50603175426082c0420414180d40311032000d0483c86960295100c4031b031039a944518041c0003010b882d6070b00c00744128040042d004850396003074154000d81c2810f4411030040f47c011810401c0304d0070411000a45400c00c00114014414401030140c00c844060074070047c540d1020f40c0364203403802100c0e00c408040ea00b0481712000036840900070300076044040100943c1c0f01c0d007006030022160140a051500d840900020300715804080510041052088013605000c0c5c1058040d0b03000300c007400c059104c0c1c100f1000140050080c02a40b10a07544c400e8000394107900d041c041501080c0c0d0000750038100c4008050124012200458203815522400c1c40060000c126100c40d140928a11241180795034284441281d69044074942070310414402a4410700045040c040580b02c1d601070b64401c2d0b188210 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 727719091 1250 727717841 727717871
    0x90d210f08130f2604050f0607020a060f090909120201050702030c03070b040221060718270e03030f071e0206061e15070501060e040f14150406 63
    0x32a404000421030128100944481d405400d50b0000360040c078424091042c0c0d04d40007060040c281040b0700b42d948100b03000b03502900c20038090001d54904460300c124130743c404014003842e4010300b000a07500401840d01000784a000314900309022140c0c1c50032420340d9454082180c1031790000d0404440302c1c00c4900da120412542845442d0308141d41c1d1001d117180090300d4030282d03983e020b082409402e40301d410cc0030030b0841d0b80b43c408102c517100c940c08078030000c4184140c03076984540e400c0f40d00c0c030040b80744074407019050001d014594042c0e5010b02d6142001d6000c07150cc21081c2000310200446140d9900c07a84010290104040c0d88070342015000728415240c82040148038400207520502d40d04100404015002c1e00030a00326803200043e52903004d681d0780300703072421081040c03420851380000b501d40d100e42c0e40704281da0042c1a0789004070001e104541d40c0c0d4000e1104940e081390054565110400900e00041c4c03600307049070280c0e400008892440c1400d621900082c90162002c5503950b590b02c0e00c040c3c0b080c030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 727720341 1250 727719091 727719107
    0x5090c1e0f0a0926070b0f19050c12251b081605180f0a06090c0c02091006021509030706110c0d090f050d080d0f0227030a08090d21 58
    0x1850700b00b070144100030084e01541c0c9a455015003050f0a4010503241c3c6400030303200070380d0300c20506070010f07001e1400c007101c2c0a030144e4041b03c01c05038280102118110740e42c0580c4201c1e0707402007403112160b0500c11202d40c1c0c00c0400c81801d03821241e81080700f03c6034549544a2801c1c1010740910400361801840000c210406070910780d00040c0901e00d07000d8030318180100160400d0f07001e2f0400c800c2a05540d1800140c0008203840d420122660307140c03076003050155038480b240d5030b641071003a039984005807180224030841c59214419400141d004020524030305d14000009a08815048100c0303040c5070b45591060281c590fa004208015500441d513054840405c11002d0140715003428540c80d490704001d030850b07505030240207140c0103c0f0440c9281c010019820105c44c42841400402c000500500320318402a50041e80607088241c0815481c00310701103d0200e00e0b41c00380c401401400b100e070075680e42c0403080d04118400e99014401131306100114054541482030481c0c02012003803a01020200074000074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 727721591 1250 727720341 727720379
    0x9080a02060906060a03030e030a0b0a020a18180c050436090f02150c0102040e0402030106060f17040213020d050a0615320a051305090c1e0f0a09 64
    0xc2d20900501c402e41c0c8417842c66005803501440d04c141d00d0480b40d00882d00d0800c1c5207100070300c252130b00410041303100803c0e0702405100c101551106903258000d0402c40d100c01d4240070f411060361001800c2c24408806900003054000c450410780d040503542e50b0011100c850080b501c070401c0115246580350503180b01c0c00c1100440003000e040111807010b0b00c0c2d000a02c000c18074002e010354604802100091440e80c01d40320725100c0a0000d540e5980c0b100c6c03005415902c00c4d18220700075800c2450100d20180990101509040c040d81c442c0e001000b620907481e00400c3c0904280d8000c824450001029400d074002031003c03401d000700108483c01c1c041200822031301c0c01d62020b0312060b00e400f0140300066002c1000c04401000d100310848a14416590360504e205030706125507200c0000820010040c3c00034042c207402c4503071440340b02000b50780c0d41c1840001d80003211b0304070f11940200059100e1814210606480c040504040c5050403403044070440503621080e245000324250020410040700c005c50100710003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 727722841 1250 727721591 727721593
    0x7020a081914070f0f0212010204080f0606033d0203010803030613060503070612060801090c183c180c090228020f07090207140604030914040f09080a020609 69
    0xc640e51a500241004c104008281c0c0406000b00000d655031780b5000b94132500302000031982c90b07603941c189079641c44021051205c0b80c01024000750107450040740c855150300790856007215020581ca40040746840d41c40a031140b43c02c06403030012004038248055400381c000743c4002d55990030001c1c00c20810000c041107400703d860402c4014440f039200032440c20201e84050034140e00b41c2c80641c1110000c0c11280e08050b5056107010041024040b050503d00304580081809c24480b01c41d108504042d9544240303020310048420702409858400e07559090903929800001d200341081806034541550746855203000780e0441c3c00800ba003070020300d100d10002090725a00031440c046021000c5070428102e1880620301a81850011008900910050314450b110006031f4041c5a144d86140000b03420185013650044c90145580305101ca0003d003007802a41c0689400c0d07a04c61422200044220503090a42d802903101e420203c0c6c0000b4602074200c2040c0308245440e191155040d0003441c11034021303d02605 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 727724091 1250 727722841 727722847
    0x6060e1f030c12080408160501121b260f0108010b060c0c1c06090812060f09040204050907180c1b1104050411030d1d0a0803030c0307020a081914 64
    0x10b550407103410100c8a0714411103482221508112003603005584c40398055000380f1800c5190ba10108210000381c6801341c80300b01138a1101078102007251441200c600640b541c41c05000c5c4594000c885102c917500307101404102e540090010040310103015129061540407000c014044000300b0300600344104c2003901e1880c01c1c20917000f00c0d03599030b2801c3c2c10450700419400c064088140800220040174503013010052284d00c0301480d00305140e601c228000440d22400c8000704806203410640e5081030700c030040c80c1030803540311a001c01c0f001300350142c1243e0b0a81315040300003904c44a030310301010703040b0b9004c3c5001454610900c00034203194242c5072150101c0452400880000c0d40d4204041d0741400c054070b0003c8c1070756403440c3c624600c000d040d00ca41d6151080031001d800d06035003c01286030389052081a59024a03040e410300903840800d00035104250000c1c000541ca44c3d207070401550703010200c0d20444441000d903071106d009990041c42c500318081c01011310360b008140c0207090050b030f0143d80516285 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 727725341 1250 727724091 727724093
    0xc09030309080a0c170703050a03020a17030c0307080a0209040608030c01140f041b12061508060912130509040b04140a02060403020103050721140c0306010801060c0f06060e1f03 78
    0xc1c4c19000703000300c82c0851201a075084881108000d10406140d00800320b80c01c018160401a54900b640081211803110402038182881564000c3da030181401c140564156240c4180030ba602c260000c20109480c0d03400c1c0b03e10001586c0309e0007600d00130000315000e56902c0650300015402c0d100c41e0030142d9211844002030051007404000c64030f90064010140c1076200f0202c6281c4100c0c94105c0d4042030003124100046020310000390b01c00803549407014042a203c81d500c0c00c1854580e0f9085030784220742d401075000300282100c140020400c0e9140b0060000480d5101c90010b03a824500b41d4003542c0f0130110004000400100380c2814440340c810748001c04060b02e544c0d001510310310903030000a0425485101060388640201c00d406084142c000c1412040c54420741400028401c0e40143c0001c00301e01d0300030441a00340d0208681c00b03174406035601c82041c0c0c00c120b01965131201d505400c84000c0f191074901004104244144800f6082c482e10014560400461044416030f8103070103000e01c0c0f001000100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 727726591 1250 727725341 727725353
    0x50105060d030c120909050c1b0c22090f0f120c080301050d03030b0a061d0f0f04090f080a0c030e06030720010204081606091d24040c09030309080a 65
    0x150003290310941c01c070580c0444104c1203ea0910365841080c5050410043c00510134440c000360000403010559480642d42d1040b00070380d12400700d6107c1d6003080d1440d500c46440340d10044409100324203500041480d01569480201c90b0083c1d070303000d503105500780c0c102400300301d020320340954100d03002e20b04040020300a454070b200d28031040c03040c03a20900d88402c09074100f6000c2c1e0000e4001c80001000ac2003041c0e901c2c0409441280c0d4200b42c0661500510041c401d6454400c10701c400c00100500030b103640305d130a18140001003145c40c0c01510041c800119150019404400030a218003035036540f010800c605240107041c03095010035144c401c42c024030400021a921905600da4032170804210011904100012802446160440c0d00030740075034001a0401c0402c252814221800d50383d4465455a42c1d550810b2a406010201200040704001007201001c625200c0100040134890032414001140001002c03100840c40708004140c0e2402d04000781030300038074001c00078126500a0310652120360303181 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 727727841 1250 727726591 727726607
    0x5040e030307020c040b040902090f09061b0702100302040b130f060f020c19081501080618070303050d1812020c01020f03391506030a0b010501050a121503050105060d03 74
    0x135402540d803031178444c50540d03031500016132058020389001c1039400c0443e84017061030001c82c0c1d00040c61080e1004100886080405107440d401d28100043c10a45281d080100300990540f8900c03c040d001c0c0004510040044000d0105048428150b45810f1605055040318000c0c4c0d402101407004040038150309503004285140240000c40d02480e46540da9107003003591502e03a0f040107941d440703500009940740000300e050b00d041c0d4005d0002c079155130740d0f4a1050004091080c15110090b04000700820000e4002d201a151280d8800d0000c11050780100c40d40c024181d49041c199401005601070034001c0741c052000808104084c03025001c41d0351001c0c09640e40c5d00c10410990286a2110101d030b8034076000601061169030800c92405034450404140b5541e0400340c0001101d00d448840030540c80c3c5000250905000d5101d0400b8134560b2801005442a030000c0ba4180144442001c10403500c01321071040d80c0500c002c0342c191030491415410700070b003110401080140580c542e0109500413035040310340 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 727729091 1250 727727841 727727863
    0x9010501030915020309010f0609050601230904020d021c091110030902030a0309031b061e0c02030d0207230607060c050d050f040311030304170306041107080405040e03030702 77
    0x440c00081510300500300180c01c0c00d025101c80d04c04820b01c014840190000c80d1209003e00007400210f8030381c00321004581d0f00303540c8240411074903c00c4289180e0b820700d00078464a44800e449042c030441034040703001d03684525031000b141c0390300081c0b02c040d280110386182c5000194003000c00c021109a5508070741004400c201074032500440c070303400701c541d4070a07040055510f40c00707002d85aa00100b0b1030054004003a07400120b070b1402e4203861004189400452580840700c40b541e801810030b020b62004200c0c031203250b071040c01300141c03c4d00010250b18100510040100d42e580101401803070003212015030205410650350050340981c1c080d206076541015150042d0b0081c400089048040c10b007502c041c443ea0318184009410003041201074200380464074800c5000b600c5940d01c202e2003010040e240d2004072401080807002080010045030908061a400000504001032085410f0102c2c06190000602101d0f11315001a0502c21800c05000b544030001107500158110704003400046d4803202c10607a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 727730341 1250 727729091 727729097
    0x807080c0f0d1e0c1103030a0c1b1209060f05070b09010b120a110409050a0f020f040905010e071208030f0403050f1801080708011215240f0501030b09010501 69
    0x2400d103420050741c01c00c96011801603107081000156008800300424411526614074519100002d46080e009802d4001c21192582c0610f245079540800c850040406070400010401820a80a02901680304004940740120401c030101440d440c4010b050714000d070070040070040d40181c00850307603400c030003078444440c2e0040d001070340da83c2c6199407980182011140f10b0b0303000002000c0c09500c540b022139039050380c41c0075498807240b0f181d099050200303071000f4546c0141198021010351004c01c00c500f241c40742c12440104200e03604601c500001d41030701d000d001c0a8965940d11444211b035908101300707100040c07147c0c84065203400150380b1041d1141c04000e103545183d65034400060105840340007110800c2c1050820f650712012828007045ea40c82404211901094030300b0049054640181c0c060b60486400d01500c2074a00c806a40760309003480d06000e140102926060300c0007454480e0031480b100c1c11061a9020040380c544840a04082c203640d00541c14549003502d40303000d070307100d030150141500c0e402e007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 727731591 1250 727730341 727730347
    0xc0b0711041d03040b2d0c1903121d01020a110f06070804150207060603140d03050108030406200a03020606090c13060509031c1d03010b03030403060c050d0606020606100807080c 78
    0x390741022a540f200d800180128807040312203030318046c004c018217642a0640c2c03c84071080d0940c401c8e00504030b041d000203000b042001d40800807100c4a0f4018845076288024420b80b441d01000d4034900303903000740090320701080a103611203402040c20040d51449049800050000742008030b0090091403019001403c40d010b2039041c1d18280d0304030b40403030b2496644001d0400c0071035500d0801e038011904804031a003040c002c0e0311800303500b1407082c05001e050f10b900c8006140781628003481501c004680540c50782c89004409400403081409005c100d007103034000d801500c01881d2610030421200401031040b218002e0910101c400d80b464034550714151a00390600560720340d0503d002031f142159141e08000803400741c0b540c00c2c29843d0300403206010600301483d1000000844420036083c4c4840304500d86d0140e03c103100400200e082600940c2e42181c4034141146007038420500d0744143e880030381000001d613001c00300340304040c280000d00700005c600340e290604550410800085c03000002400c0900c00c54004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 727732841 1250 727731591 727731607
    0x14010608011e0e0402041503080403051f0510050f18010e0414030a0504150507120e03010c020a050c09060616030201020a021e06153106051008130c0b0711041d03040b 73
    0xb04c47c00b020710707000300f20300d911640e903454026520021440300e50b0a09840e01c040341c51580b0103000320303030152420200304071803e418401070000c62480c0c10295a8044e900c0c441d212060300c0c0e8030a40358064030001003107115a00e081d041484680c83c2d14003a4510700c0e031082050b10421a40f100686095904151100390b80e100c0405080306c0310f005955010b0b004001100b41d00c4c544a03080000b26100007c00e0700244112121510140e840e858050703005442e94014a803441c54900d011412554840002801c1508202003242151800720540f03c0450140c0c0d4002030415145804201e100c0340d0301451201e6000c41025140126210b8101411005030b418003905108416a0344002000341c0c080c4101800c15000c006000040e6000c1c0b03905003407031400e480c007070740415282000302a042d0303104407a4031034540c0d40d140d071a83c412508501131410b171001210001c0100305469600002d00d0703180c0c021100b24882e0303107000040208407244100d100f41c0b41d610001c0c108c01010307808400d40d801c548810300c506480ba044 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 727734091 1250 727732841 727732871
    0x140a030206030a02390c0910030303150815190516050d0b03240c0c06070c1104020a030902011205060f0d080910050316050405031207050114010608011e0e040204 71
    0xb4203104506030301ca1400303140d1001000e1031105008900304e60441b60f42c40d032442c0912880a4040c0c3d01d0004501781d064003440400e0194001540c9541207001da00812552091094200766130100300c4442c1d08825000d106852010200d84986080401020007083c100075210703540e140d00d64400d240502001285a010310b138020741c044080c00f0380180030b603045001c0452009459a65211803107110346804400309101c1e01c2002c0a40f80c1d540480c2009012503240d0b0308007a10341030040340c0c080301c00750f411080003405500c0f180080c0c080103c0c241c40100707030624944000742c42400d28a1019030070510b00002c100a50b034840102c45020a81611408019039003400e10a042e4030801c18031b281c1042c68281203008282d40440198422000a16882e00440100c80200c803507208070b01c9850303410f0f0b1000d00c2e107128460349000101000c3d03106000001e405941800d844d42080c409034400c10110301c2c03020040000d0046171400c100051445d6450b800c1c00c9003005164402c03454003504c0640156954103c007140145 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 727735341 1250 727734091 727734127
    0x30915121e06030b060406060203070203100e031306090f06020c0a03030e010e0a03120e0a06080402010e06040915030c0501170a05060a080a14011b0c02012115140a030206030a02 78
    0x1c9039050501501e07072a07040801404c1070980f0000d00803480c100340001c810380301205a40c1c41c154014007900c0e0300f020127003866000d1300aa0a803a02c1c617000c20171020071785241000d541c2009142d643c456698551a006555801010a902c2801550031088000b80c02c1c0d501d805440e0166036041c02c00c4190140c400004a030070502107004076400902c0c0c9540441401402c00012094503e02e90350941055462014005000010311840000c42c040c43c4c0410015802134100701d500ca0700251015050560782c0100000381d8992411840501c00c40260510600080e0510280541001c1c01e0003076440700503400c0308080c00c8000f07002078142d503945c201080d200d0b980c038001c200003049090304491400c0000d04100d401c0d403006a41030708480d8603140e11032030328420100d0b016403400429180d41040e039079a0740054070034003501211800007042d1007105954000c91485428000641c202c2c1c5944041d003044c151a03041e840d095001032044070211010001662000700b100c0d8800d08414000da00d9240f001020038800d1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 727736591 1250 727735341 727735391
    0xf031602101d0706110a060506010c0b011d06060c251505300f1003051b150310120c080d0e0907090e0a2003070c03091512 54
    0x190510071000704050404112002c244541d500f981c1030540d40d803605482a180c0742d41c000001e908411000c0000c40c0090b800103601540c10304140c00d190825a89041c20300009030046009140c501607901480f0080201965000409540d01442c0c40c0050313111039540c06644e00046240145540c010b02c02403003a06404000b030015440611403104014000780264105c1034148240354a282d441c80022407410601c0f03146d45024030060101d54a40c1000c0c01a0300c0b00060200001d00d070540000400030310100f0524440c2940c0400c543c42c1c0c108000200310a420000b00c400c01c2c000f50600901031a900c0441c002e0003122501141040b580b0b0305031404010541e080c5c3e01034015401804501408960401042e042510085400071b4441d524620141c0701084c16019020f40c003009080062030a0071554000881c0e8654061400c40c02801040d048040c0da0040300e4000c00505441042800c0540004c460b4001e030980306004024281d031300c18000d01400382c034403440f421280c4400b000000d06002c0c480400e00c43d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 727737841 1250 727736591 727736623
    0x90905120415120b06070639020d032307021f091e1a09011d010e160305030319060e0702010902030606030c09130c0e1303030b060f031602 61
    0x2140c0d40c4800300c101240038807462021541c0c03005101c03003981180c0b284d82c071812001008181041e119440c0d1100500f0200c0c9031466401c000210300441e0b00c8902001451401c4c068040400703c103030f0700b5009084c4241140e0300d40526040141803101025010a003080881c20414a1b038441d42d10620100d10b45008504000c252620a80085520b8407140d003014142600802560003000d0032034079031070103141000a001d480c1c018810400b542515202e01c09540202d031000000c034590300800d1001d40740c144510182c88180c1e5490000c00c00d0010f0030301007aa6824801d00c10360707001d00c0c0343d91580303500c0b403200414021030b101007400d580d0f507002500c1e4408000b8180508581b080c601e070a150182c002c0c8050401a4803e20400002420781d00d4000745d19007151030064000901038076001030300d6482d10768240d800c42d0292845407001c2200382c0e00310f40345842040c91b82c5075400591202d09024040b288400112030050f2810003001c4a80f1504c0c0b01220b400c002d40880d282d0b5010140c450803070914161070034050070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 727739091 1250 727737841 727737847
    0x27060506030114040609030e2205040809061219150312030f4b0209060d050c070614041112070f15020c030f07060507030504030f0b04050f060705030109090512 70
    0x17404104d038003e41c01140b0070388603200c420a40d0002c004981160650b666010081c0410500346031400703400054005100c1c1203d1810010001c00107003107908035501da03241a08c04d08042040f4554410803d841655540c40d04120040102d240e0702245542400058201e1003100b4400c0c038101d00c80d9010500700c1030103207400c11000c9944800f58000d1070100d205c084400c0001a90381010010b104500c41c04244980c0d82c0c020380810045258000e504401d074041d0f8014001e01c00840102d066004982c41004500d10407691a0134620340003007100d0042c080d495401c80ca03601003000040c00702c0310844081d0000c450004204c2d42c94414a4548000742d004083c080c032900300e000032079a001d82911043d0b82d500380c00b034405142e090014541c0d102d00b50741401d00f1951001d6010071105019400038031200d4041d1408500c0d054403620364041c001105481103505000c10002c1200f40841405164642c3d0000c0018110034182190000c019001c1802504600d940ea1614801006820000c500c540d8080203100c17a1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 727740341 1250 727739091 727739093
    0x1c020a080105030c040506010219050a0c080d1706090601110f011a0a090b06071b210c06181a0c01050f040606080f1f060909152706050603011404 64
    0x2101000a10816001303106142480e01e2501e0300e80503d5200b100c040c4c5c0141442125401c544024460698042d5901c1c02030204100206640080c1718002d000e2820003030030307603070380c1624000c0c0050120002003010071201e17814000b203542e46000c5586c0104003480c2ca554526160a031450802c0110f2780b401107658a005445800700380001c00204200d0011200100c40a50310751a2000396007881b0310040d8402000c1200c000007030781c150118250002219904214192030b000111280400000c0003400d001e0244d40403800c00580015910150400d0300e80500381240c82d00b40034000c028140120a000300b45400c1d0464040203840546111002c0b61000388101d08003515841d40c6030100743e030140c6a0a0400b23101061016000400184000403100148000c1040c5401c03084803000281d1000f403d03e0f00c480780000d0032191401442c540d41e01401c8074a015100c5101c44404030790812100c013499180405044040180b00660540e0a5070801404901035942100003801852040d008080c4e11141c001440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 727741591 1250 727740341 727740347
    0x6020f03030a02030402120f1e0d0503010515090d0507091a03033c03010f09110d0c1707030e01050a18080904020702060715060b0310060e030f010f0e0c06040f05061c020a 75
    0x10b800003481d8500100a2405030300074039101c0e90ad40c0f90740310104400708010410303070401c440200e4502030156805810010700c040080e0000c0c09a180c1650349030b1010b131050280380094402c0ea400104030a03072901d1404280008203031a4042c040320070401001710781050100b40d601c215400714400740c50710040d80103c40c1100e80070082c0c001b8001c486e0003280340701000c00d02c00d000f0f200764201c010100a020b03003050b02d0030015034050040e54020703108105549440d203103000314445205004035107070345000c542c5051441290b821520010400c1100c90304110980034074002619500ea0303002d8010043c81d9072400d5103400300f00039204180000750803071400200f613000d00200c2c060140e1052341003003050140542e1800307100341c0c50100380c3e0310240404031404208076550080d610071024a1000c1c09545c04c90125100340c9003120307584041c007070403151941030051018605000e4840e42c007200b2a0194140703400c0101c100c12124090050f580660f60018015101c400c5c141005103c540b90792005650792943d100c001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 727742841 1250 727741591 727741603
    0x50703090501060f06080408071b030308180a0305030c0a0e0306010915060503061e01020f0a150b1f0503190c03090201080a0b0d0618020a030c0f06020f03030a02030402120f 76
    0x9a60725468600081442d25540c00d280003203440c1980d58034025100c544401c049580144c100f22200031505010400004280d501c250040d80282c860108900d8481c4c0d500601107a413003c034040b0703500314440e2400001c1e002400c2e01e030442c903000b400b41c0d00d0b055001c02c00c4d80c10402c00c00586a141c1700d49000080d01e106507800c800e030f20742c0c6109400c0310001e0b0303210320030345031400240c0b0601c3d440441010380c25820480c61410301400300051040381d0001016410050420640d140242c5100180c2e4000344002c41d4680220011058152160b89070610210900140c3e0b00e5a8152030080100000101e0f282880009022104003c45102085901448074010b0020003505004178040307140c843c000b81820040c0d2042050031800035001510400140c3c0d101c07802008070b0b081c040010802c100a100140e01c801035400b0195100300c1c1200d90321070520201c408426030561141007150f000303e1441d080d0210210a984d0032442c030300009a00c0703803210b1000661400950f80d00310036602c100f00061149141c00070310 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 727744091 1250 727742841 727742843
    0x180d0b0403091707140105092805010e0f040e0a050d050a020d051903051909050c04060503030c0712020d060c020102030a0c05041d0406060503121b0303011d04020a030605070309 78
    0xa0010003940c0703180594050107014041c035682c0d0003088040041140c0743c07045e00c15007072052500c0d5161040700b2000920031000c00c0e9980383c941128010f51050f25480019141c0501f80908100507040070080000d80b41d02001e0306d00d14000c075214400548901c00400c9030f01801a030043c25542c8121494000410581083c60000700501c21001d101c04143d00900842e01642020310000860b85030792a01980640b5014054280d030912030b103402d082c240500d03c58454014419006060755040c8441004144c42480d00018443d820800840c003110740b002421000311411514038015510035800041c103c1d58030401c02602d0142401410005960b0644c01548a154006001c01000a1441c0200d5042c0124082c0c051b0340c0c102100e16110405002854541c020b00c40e900101b022a140d002003418043d80000701001e030480891441c0000180041001248501070015801e40d071400700c2000c00581c940300140241126131000c542503440307110400002d5500000d0070b2082d8180580000c0c014035070000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 727745341 1250 727744091 727744097
    0x8040b0310050a0e0402040c0e10050a0216121401020706020a08010519080607030b03030d021321080a0e190f18060321051c050613020705070b180d0b0403 68
    0x50100d01d900e041208441a52812004c1880541d6694213110044c2452803e60090000441c0102c0941c5e54690030b007421050140d5a0b00e031240f0a1900c06480c04200c0d07607034070020450400d01032100182c4503a94400c0550800706241201081c1ca419500a2240b01c0740903000c81c1c00014941c0195400c003d0860484002351050804107459554440c2d40404901a1023102d81180c2c0c081002940709402c501840032009080d40d00d017050081c9440101d034411a40350504641030213040040c60042d00400142c0c00b511003070003544240a6803020214840c2080000c244241c16408514507203d480d0800601203100070031002042e11104204448000e41c0b09421201c11011520104261303140070b0309003226401070090150081c051244c1d0402d541c59080d01c41040300502500e0140c5000d03004500d0ada00e07000200207580e086c800c041c049400903103e210852140100500b5002600000c0d1030411140302d03085007034a130020309a03030315140c800044603240e0017108890300d0424008492000c501640c8261 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 727746591 1250 727745341 727745371
    0x30a022b390b07030b1f090519170303070c0b0a0b1801080c030f0601090b01050712030b0f01030b01050901080c040f030c0e070903020319150e0115240c06020708040b03 74
    0x3d811025108003a417100d401071207504c06901c03084100000c40a40100c40c0c200383c80c13190385490109424011421040f000c0000b8010104070003811075001000714080d240103186549003803100608100030703500d0001c2060b0381031400180d08001c40d84c04044400f01c01064211417102400441400b440e00780a2820b440c000c03a01001001d280c001600d007041100300002e00b440b80e18100e03210006055001d103960511604100ca24001500c0c3d800d20740d01914992800030303d02403444240000100c01c6240715040c94500880342a40c2d03a0000191204050b0918101c1140d5465000107207160255904c04440260320380c80100812400e000d03000e013175500a480d8215143d4503060100c84640e80c510001e9010703085400d858030540301068141241e540200315038410415100010421107412107220402c5942d540c8810b80a040c0020010004021a2421001c0444c80010b0300000c21340030f05501040c08891070344401000380395010389060581104e82640ca075650b0b0b46c03507003c040d0f00448a00107a0b01e144 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 727747841 1250 727746591 727746601
    0xc1e090a0b2718060a030b04030c11010801030309140a081606020114010e0c1e07030914030a110f0103110708041d04170f1b030a022b390b 61
    0x454801034500b40c010881182804509001030300e1100190031990001142c1d072022001c20400710b20940518405d9450b000a4000303418030505482014402c00c0c10003010a00420100b0340c803110000a454210041c09290050320002506095960348100414043c42011000707403081088050102c40a640080c411400c1d204560402030000340100c45415201d14007180c824840e43d8013408040d08401091400c00d80003549405098000034000c9000036240d0506000713003d13202c10441d28030382080d4000c103000d94040c0c0d1200d498030303625500a0f0285c40900080c3d6a0341e031090f0441001c801c01116002e558100c01d05080090741d002e070041302602200c06604080e03480040c014144a26040920345000c0e44c2c05080310070f903a6000d840c03c035081080500803003d5038407004071418204007800d4010360b602c11007890040c1c2050040180c4003820704030310342c03078a10f01da09050307a2000c418814503200b90510086040c00000c14402000302c0714810300e420781418920140002212800c3c015188002c0325558 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 727749091 1250 727747841 727747897
    0x12020105091902060406110307060204150306150c0b06030717010e060c0415050f0d05240102010c021b0a0b040609080c0a12030c050304050d0510140c1e090a0b 70
    0xb0b8450007504150b0401003007020510032100a40c0c0d043c5103100f40d900e001001d0300d600e8140c2e00180c1020403506d030280d01100b0003542510804009150740c064000b110180540094103056104201801016034507002400950b002e01000018100512080c0c0b8001c9040c000180207203101007030300b1190310410020034034407000103050b101160020100e030b50807100034100031996608914814005858144a2010a04228050203124010502c4403841c40c0c100300800304e5944050208d0b6905691529010461043d404030b440150080c0d007200005030072880c480403d045031900d41c4a030103c010045804030354181d0242d4441c04940c0c40d103089030b41c0312907160b041040c0c2004d01c2c070604030402d03010946140000e0007400f204030f80600a500b92410030380c0c2d9901082c1c480e05002c02c2140c0d030b500248101102419035115004107034000003499081860800c5014025110f0300350b004054070707020301041002080c02411540f0344c1d08003400c4203040c0c550318182d1a5482e0007480941c11101036815404242080c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 727750341 1250 727749091 727749133
    0xc1501081b0307060e040b06070b15221d1c0212120f0601030b281a03060904110406152c120114041109070905030606010305131202010509 61
    0x400280030300f0820346072140540395441649495a00a0307150b0b0b0012a840e034404000c0c140c100d004801c10a0300b4500750f440c2c482001e203080c0c1050300c00c0316541c10308810b142c4483d00752100d035031448400064100e48000f0100e22040c07080d042480c1e0344140e0640a028401c002c03030710301c014480780e000c0341da0003441100003c00034040c02c120b803003000c0558000a01580f03812107080e900694103050016005600802080d00294400260b90309188011016910f01020740c52071801014104981c00c11445c4c20402005244006003c0e01c2c4141e840c0400b00c2c0510105c0000301e030030104010002c02000340d0780c01001c0e00d0070a030100c2d01e002203810100307120403100b8404150b03d000781000d0b0703101c00d1598000c410080b1a094001485016642e50300001d0000380ea8030103007030301590080302400f044c1900c002c00c02002c0e881c001e015104001000301d08000c0782d100040d0640d0440b0090130007241d595104c0350348030070081000c0340c0581240004411802481d03010f502090203072200394241d0f000540c4129120714800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 727751591 1250 727750341 727750393
    0x190506040b04020126010f1703040b0913060303120b1212130b040b09030d0f17041110120e0c01050702040905030f070503130909080706110c150108 65
    0xa04a00001000294030056081d0320901c141001c10030743c00c01300c1c16040c4080800b003400d440c460b100b030300600c0b142d0811888035009062804100303080d03203c8660020b46a00032840b841c01c2050300801c1e007144641d10402000c0000202400400c2650350340d0800400403a4400c0b0302c24441e0b850701c0b495030341c40e0500744106224600782c10b00030000d0f1403068040ca0044e91082c044032440c0041d048000c10307080440c800130001440f140c002c4980341d4408208160500d4081d20180c028004c590814a6509800c0f042a00f800305441c030b1103140c03a0780c55017404180224100160742d0300c100800c902d050041d411a003c191815605201000170780e04041c074090b5105113917028076012681c00e1240030010715050700f00000c450311440590f42490a0b146069019030008903046030990000319003000c20b44080c2603250000c250110040c072a0f010b0f5600c503003440344035030b400213031240340c4643c2c2100700b0300c4140c403c6442c2d8113134000071a20707400f21110320820a0182070090709040c0c0140c3e0f8546107036002c100d804003408 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 727752841 1250 727751591 727751593
    0x110f03030c1c08061027060c210f0e0409080a0203130503010606050d02030c16050f010f02090d140c0603070302180d121101090b04060603051525200703051905 70
    0x2003085c40242c603010005260750404643c00540e254045854020460040c05a80c4070081c0840da1803070610156010248a47e008150100780d05001c9544013a0040c203d00d03150510001130a401c030702003030240805000140000ba0005031600303049500000410080415156048506441e0003c05090b0344280c032070200010414442031640189a500840d00000c1581026182443c001c64035506035204410540305034102040302e0300b580b5001e024071031400300021400c5103025001d50002e0305a0142c4080903045201c85120721803107020030000b840e00b24400524041e128a44503000402a62005110020b28603d00100d24014200b000940b69a00d9010140702c2048441200803101c443e098032201005640311400742c070126405138000d9000381d005480119040f42141031691600021038504404032201f20f0400106104030f801040321a44c4000030068082d03001d44003100d0220074140c569140c0c0a420040f0b4006450003e041d00450b441039090b41d030a01c400b062004d465a589203005000d07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 727754091 1250 727752841 727752859
    0x2202010210150503010e03190305070c12020102071a071206050d0f05120304050a0c1d1801020c062409071b060207051c0e0a080703110f03030c1c0806 66
    0x801c81141d04280c250000d0b400c90300040e503a0700c00c0020f0958840406885107900000394406402c1a108075004c1c50304541e04061000742424100200f501103400000350141e158101045442c51007074048801c002c0d00000030143d04848e550f91504800c0d02550341c1404203031900c0c1c14400c0c0c45d01c1070040004444009100440114098494251030208110304490501a0100c07920703030003594001442c0581e0064000745040c003038524240c000e460135500968003241410681d02d01f0000c212548543c4503801980d09154a07460940c2c443c0a030003103800c04a000e0268100700400c4034180c0e510304012420b0041c8101003101c2090501c1060b00003034402c200090244035201c8040340c3e18480241081d40b00e20f41c014502060340d100c8a0401034103540002d641e00303016282c01b04a80d8400e1881e02d01c0c0b00300b1075544d06946e09e4500d00c5a84d5444512004104018115040c40d40e69035a0b003103840206001f0702901c1d036a01e1a80350803070711000c107080c0c3c0c00391040c0840c0404100070b00c940b00c058414200a000044 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 727755341 1250 727754091 727754113
    0xc070f171c02010603050304081b0a0e1f2309011e120314120603010605030309030c190518070906020c0105041e2c0a0b01080f0903070c0b0322020102 66
    0xc840606111400b0b56484050000008404100030070040c28504090310004882e02c1c5103445011244c48090700c0b0300743c0b140c000d210144000e821640c21840700003000b1035130702103000120403085c5954084881c2c216080082810307641841c0c0d20380020750f401c03a05504240c1c4c0701ca2030302259549815008400b408494070a1144d0001c103015400c40c5030090502c94029045062200c0203540300101e070050050445040c40b00d18102405020042e2208901640c1012640004240e03102c0c503030b0441d10320802c0a961021242428a0a0b00c0301900c00645050400724550440104030142503034520009580c400000a809202081d401d2140d801699603610703251500000b4001615603101d1020000354104000a18400c0c2c235440310403070b018491401514040c0300040350503030303500101a500c4460405445006030b130b0307000c90020f07401084041e02000b140c443c140c80c20300e140103d000003800308070044008075071003207040040c600c1400d80507045600d0780010340106090420070780c40280503034003080703200d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 727756591 1250 727755341 727755373
    0x90c06050304030201060e070e040b0a03030e01030f02070b1e09011b0305040302191202010e0a0b0a0c110f030d0b030d021b030a021314010f080325080c070f17 70
    0x9030b0064024400858800d031160f10250140070306841c0701000c00d8120920385602e040c42d000c0d041c13015000b25004101c0a203151009000d840d8101c00d51410140d45c0c003141c10b85008580d0603205c43c01d0300309c1e52003105403510071084e148420304181480200b50914001811150050182d00c1d02c071403506086105100b00380406401400e0702800031402d501454200d400740b01071000080009a001c0c42001c0c8140c200d1000c06402c450b1464240001c0d50840184100400d0003c2205a001000d2843c0020b075050107034004c85100c0303c044008000c60017104241190340e0b4001000d0b00c00c040540785c040120b604c000013055070307886926107520050303080f014140315003106c0a000303000f0026019007550b200030442c5c2d0000b04a550355180400b52195920041d0004810091004d409450052004800c4501708903400f41d50780901100c44218111506c1c442c0308000d0740003040c03449507a110410580390029007c00d0354984489015a00140c0740d4409c00003505040b4210f540c1c0e00c0d240c0da0300940001c4504504003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 727757841 1250 727756591 727756597
    0x11190b0703050306060c0a0c06080c0f0f160804090e0c0904050c040f0e030d150602060118090317090c09070327050a081306080112021008041b1710090c0605 69
    0x136988040c050100000021060144040c028851250821038504110000d080e540d8040c101c1c81f9061800d000c010401e040410840b20b048000380409a2590443c40303d0500a28080d000182200f10202d000a4580c01540200151a503014292094400458207001090000302d0780641660f105040c5460241829031001c0d18418000001141c801c08100c5c4c02441c50380050b080142c49540c80c500e1403000c1710a031107190060002480a02802c1d4900070b0300c0300a4800c10601011500d555005200030103015400501941d0040c0700c40542d6450852070068403060000080350041d42240b0016442c90b1084c810b1901c2003200a000c025070041244490245042c3d45004a46500c6a01401008941c416002d0982c0302c0140c03036001a8a4240300303000f410748d40c0c1a80031805d0003210081c40001070399010342c5d10060400d50724104902e03030303a203017400802c0e114820300104100c4000d9001103045c0c1c610500c0082070852003c100d511001112080344111483c41c14080c00c00b0003054030500000d4840c00c01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 727759091 1250 727757841 727757851
    0x1b071a060315070e0306011401020303010b0f04050a17010506090103020109090e01020f0c061e0702030a1b0c030b060114090a05040c11150402100c0c05040509031611190b07030503 79
    0x4a640d25403070b109800d26480742c240da1160100e80c44500e04200741c0740c1044010f001d00440d000615005d9403900000c0d64030b010600802d00c1e003070004038103040704254100c2961b00800d4010102407141da925600b0181c0103a1140010300107508100001d01c0038240701c0100d0b0304980d07041c0d50b140c03045481c086507100240724941d4940c0e1255000c0000500100c811000703041c42e01081e50142c581800c00d8426044030910b2010207500402c810300030021025008800d403200c14145041c504281000d07003101d0075043d0b0803039100803c1114402408014080320004032841007a003038a0b2210b44003844124190f090140c041d100386d0144272b030101805a802c2c1500403911000c0281003940c0c1416807005881d040c10fa102d959840e01700803850401c003c0d03182c03d81c5051000f8405003814000c47d841c030f0f19100d04202040c021140034a44804c0810018030040040300c40c500f942481ca00ca01c04500c0c0307000d250141d9070204c0a40b18007000d000d0399181100d007404400859042c00800c0d85010003987d01903030709400085c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 727760341 1250 727759091 727759093
    0x709090b010c02041a190303050703030213080a06050a060609211106070b071d210c1e03060c0c0712020a3302030a0903020d0215040e1b071a0603 64
    0x5040b030016120b034003540c280c024030110415000d188400c1408500a00f082a5600311202c500307013000031a820104490381c842d0145005030740d4003010894600307901c5a580c00313441c091285511080901c40300c0c0c1d01c01070142040b0113007441040d0b030783c030001c5814003200d003e540340141d000f082c1d403800c0014614102c4420b5102c0c410300d10340e200c503180000c3c00a4004100136200204a80d0800883c03541c07000b01858203a4040901400c4400b00b01c0c017046290284c5800484060038414840c030580004000e21281014010240f00d400d4000784110300450105003900c500a02c207240c0402e00300e0040c20140c0b0310300d1821000510340700345230000b10100c00b051307008281d81159407442c1c00b2603100156101002c0200340e4584030500c00c10641c50188203000d1000d1003d0840d002880541d0078580d010101c7c50032a6011250b50409203841e00000c2c1d0004800300344000d106100081c00140100b00c101c06074820f07900c8210300c2c1d0040100044101c0548a10344000307010618030704442070f1031201408216000f1402070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 727761591 1250 727760341 727760357
    0x11011b0815041506080a06120b07020a06360503030403050d15060f080612190203150f0108072309190c050405150f0f0702030f07030b0109060602060709090b01 70
    0xd0041012906107401c4580d0f80c4400480c10703c14140c11032070349a00580000020460a4904403000e9202c0c0f0322180020700b0b200d00e031008503049920800801100300d030090410401e820181000c51200c1007007100340138100d80ca00c0500a10040280d800780c2d51550072002540c035640c0da90794100c0f5654808422401c859941c1c400350814005c405207031901030041602c501c1543c446015001e00b020000a2840d8801c1e1046401b1414078100441c1104000000c540840170000c01032000074209410514600c7d00c5c000702c0000c000035011402c0d6242d049402200550307030388a844903a082400307841002980ea141c00c001402c0b5000d81040701e0007540c4801c1e0262504d000c0b820545480c401d446041d103134030300040d201243c00d00881c9010b8108004690059000300e10380219070100510702d004441c0000e02170708001c140581551802d01042e03185e450301d1020303602059140d14051103c1d28081c0101240c0c03901d00034006c11641d0001560500600d110b484164081e4a000711910140202d003040c20304008641e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 727762841 1250 727761591 727761631
    0x30603030d02161506140f030d03270803100602241e090708061302010909050402190806070f051809100801110306120303010506030a2c06060111011b08 67
    0x414401010f041d504e0b0046074142c64402c0080c0b200072030040a61280b180c00c5080303400d590300060782d851141c20504001c1b41c142d07a048540d07007628421080003c1d40000c4185800100000140110712441c8040f4012001130707261304040f6075904600e040da44000c402c085850b9000802622440c0e4003803400b05820a042d00c0b244400045d280c1c00b41d580514907403020409100e1050309029090340003110403103021499205030002450710000e03201d01ea1046130ba0350042010740d26403045681900c1803650b0741d11101c81d0348419407a900c1500321861800511041102d5032002c0c0b0500803504240080820026040c0c440c0040041008000e0495811410040800500c0d0b900a0045001e01031000051584910b840b00900000007807494031552135810400040c81503aa44206030398001d83d2400c0700045003051111071407200585040c42c144407541c880c030506a1508000342443c492903003070743c602d08d200b612007144030b00340c0c1d540803510030703500040403030001860f8030944c0700c40e0f4801c8010225040c40e61f6a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 727764091 1250 727762841 727762853
    0x901050d0e120d1b02031606050c040b07150c030b13020a030b03190302120a0f050c0a0512030103031706090a0e010b15031b0a08060105070f0204050a05060f0303030603030d0216 78
    0x80031880c402c0ca0b840700c0e51411405060b020070a0784e03242c280051882c0c090208405906950100401402070b80d8030008903240c01e191b501900c0150140091550b503d22a81c03d0000744440141c06440c809420300351210143c40c800c1c01010701c07200340035020707080c82c94041d546000a50084005c0c5010503540d0040c0d800c05640c1000307a0216004130340c0d0b03a405018803e0170000e040c030304240d60b2196001c2d010841f80881715801600c4d80b1880c03d1600c0d28584942816489505089484030043e0052240c0c0c1c0ca0244d580c0000c1c0001c2d8100d900c02c1d1210070b0340d2107903940c01c103076210000c554080c1e010400b6400a010340311143c21501340307041034600014591000b440002d440410050048841c3c10740801049150070480446c0410302e006080224100740c0b00c48801002400c0081000b0b040110100300d80d010025405801141290700038010711241c5488417109004020486209200300b141d040d51902904010048038010140500a1840c01e03820441c548040c1d40130070b0000040d07038121078520740030a81e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 727765341 1250 727764091 727764097
    0x60904240902071208100e0f0a0612020d080d0b090a05011401021c0f0903141f0603030e0d02030c12010f0f060b0715020c01020c0a170901050d0e12 65
    0x41094100d400c00400440100030304045a0001c1c0c1146204000c01070100340304141840104486190241050ba14940c00c0310000c00645e008005c10a601800d1003c4d0961602d400b6208651780e6004000941d652619050654003101010f90458640c01150010410500c014500e1a545087c0401d50a140b5808070f1100407084400e03603201540e0b030005010b10354501450f841307034000c244001c00c5142c8246031141114002280002c01f8000e014403036010450007141564002c54020100080c08160744042c981c130740e400c14421907181140c2c0040810092681c1c440c00c8203882d055522021143c40007410300211212880b020703a41032089980b941002e580b260680d400b40102c2e00000300321041d0256041c01501d545101d11060306e810210140710806100013920301242d0050380040c400d60744102c445000b80b150b09400343d1103500000e80c42040000002c0e8441605100d0a03050804007040c80c2c2a08040c000c0c0c6a5003400508100302e003101c100b8060700b11400b01c440c08400d444042c242d0681d800c007158 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 727766591 1250 727765341 727765361
    0x12030302030603010f020f0301061b060e0619020408030405091b070807030905273102090c092211040311030d0804030e01110f0303010b2a0a0f02060904 67
    0x240c0000800041d401c0c00c1c001c081e00c40340100d20543c00c0115000b520b400710b0105000d102c04120b80c010001030f14160070200b8107903164128004024201c08900c40c180c4910b0121246035001c1d50f00401c06a0106030780c030894007241c0080e009141000d05203420000f0000c8090500302a400440b9031a101c207981c420300070440d2038032800d906c581d00c4800b8600a0080007099100511480c00c041d003082c5811034144a20440c0315540c882c010a983d00c0801001c032000d000c0442070980c240702e0144449400d403001c03162200034000c48061072140c0d5014103140c100c0c072800e165290404601d07607016a888484070040c0c14080500800402c59100f032140d00381c03054019500035911454080211072a03400d0034001003400c1070300c45c941101c0d641303026203029100c16801d0180e42e041010302c403061109000706100355040000c1c280181c0b5a01c1d6903503655019150000c1400410001c0003040300c1911401000307003c1d4100e1241000f40031180a59110841500100601a0380100c810030441c1c00301d0b40c0d1445908005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 727767841 1250 727766591 727766597
    0x6030105040b0a1806080714010c030509210606031b0d02012102030f0711010203061513050d0b0f060d1a0403030e061303180501121a210616050712091203 68
    0x4a45441c0c13401f4604440c0d1703403000080c0aa400f254044a907884060302007040d416041c6155a0301503030006c00c9108402000003440610700041403404400041010f80c01000200e08a03400c60711004001d0403c0b00440b4440c640c8400c8007003c400041d40280c2c43e008054610906102505000310003101c2664822620012042152020000c0164120840c220700084c0b0100850641ca001000300b0308060410320404503600e40440c0d0240039203130071a1134401800d00544040f0040300640f521072034107e0261841c1d45080c894200040e045d04014240049140c3c014905003841e0402030f408512140300504103400b01a154100b884a0354000c00080d4040c204000010b801d520043c10010a04140080c80307546400d1042000c200982c1c1c805444c0c5407449107068001040315580710181030155007440d0054010f00032000c014080402c180c02140e03020b20810070345855584004a040e14264040351590114105012450200d1410b0380c0e011144111403c040e4400c1e42c54070134004881c07169207422400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 727769091 1250 727767841 727767851
    0x30a1b2c0711030a27031e110a23030609150c0702041a0a0920090f03062d04150209010309020603190e0c1008090709020f0301150c0206030105040b0a18 67
    0x1492400c8404807203e17021034189944040e040d541d4400c118418240c4c0811a540710141d2541400050b08a08190541c010800c0311400c0e695001c886010200302106803080c409100d410b00b1f00c0c1008242c1c6403240300c1c1c0300080e0a02281074120f40d00c0032000500754a0b000340c006c0c0000c000684131803041c5182949105030905c44214038204202a04800d90441e64180d4280008144004804a00d1001d140000815a81c0b60710300400810302090300c00359081d51600c40c21081c130024801150342e04115440a4201c41c007490b6520074440e03200c1c10b040d20010425400d8003282c00011103a03902500c01c03110140f40c00300348003184d900017400c1c60f08255507201c00480506460b4545000c10301c5401d10514041c00500f0080a6603000240c4c0700e0b205403503d83c140300642000412050302444907202400c03e40e2411500c403030041e00b8054003078100340103e0303d42c01c64000c4d00c5041d240c05115020300d8198000d100c01d19581c2001c050001038010800c0c0d46030000c4064a010408400c8150000321880c981c3c40001f030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 727770341 1250 727769091 727769117
    0x2102061b06100f271814210d0b10020303060112090b0105041e02070302030403020901050d0f020609040b1210140903030a1a030a1b2c0711030a 63
    0x814010080c2c0803814041d2010740400c0440c80c040d6080301218601092805540038000380d681d04580808441541136141860050303d412405002c0010b103405400075020503032217aa0b00f195240d01c4490a1030300c4200d0440d4039541c0417081c0700142000745d40706102144c030642c007002060700d0312030000d00340c009070300003004101d05540d000003912101710600105006e0080e050304d9000c00c020040c080c282c000d6440c1c8844e9651441d001102d45100000c01504569525050034029180e400c40d0008a1140d05440b0000829181814120340d00c20741010480c2044a0aa070030005103034484c1551a8003e42c1751074000000340d80b00300c80003c0c0000c05002800c07292180001100840d01d0b250410b0324014000b030140541c940b800001c2c0da07809001c0303a00010750182004503100c540e1111184a130350621502159108101d140f014409040702d098460b400c0345a10b035802201c0301c120210403445030340452030940b200c180b44400b403207801c40554100070400008a00f8510700f160f00c40802007011a1108803146 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 727771591 1250 727770341 727770343
    0x1a04020c0106050f0d23161203090608010e0a0f0e0d0801080106091811030109080319050601050c030a0e06120906070207051e040c0e100e030c040c08012102061b 71
    0xf1303c2100201c6801d03000203025515200c41140000c03000b122500c8481d104003190303200300082c02d0181d40400010b8075585e43c0d208100c00003414141c02301c0019800402c00100d0500420803d4143c40588020182695500074030000400c0c1a080c00c0414680354000802d0b4002c051010240c044001d594100c450743c102031445007580d81a500502449280103016000300b000c49414504182d800003008004d148040c3c0000d014140c00d88019010807000014011111031402c85408900d0401609012582e25000199880c0c080c0391a1036182c0c2e0402c01100410313034890000e191a0000c018001030801c040d0320419000c3d06000c82e8106d800b948824103001540750108a440000c050131162004145d60020030301c002c40d956210124000c544031907490a51030700072001c031042c0310307c0038120480125414800502d2005d011300c0580c00380c02080d40c003510509007402a0038600c515501c071945284d1800c5039080101007100b00042c020105860401d0061391820300800c84150442607a51061222410782 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 727772841 1250 727771591 727771609
    0x13050c040617060303070f17120403080901113103080c12090a0b0c03120708010914010b031b0f041d010501050720040902041b020c01050408060a1a04020c010605 71
    0x500b03580c180301402c01c202a6030000441d09840d43c003644c1032041110740c0c505504401020304410107030800200303254603005072600c01c09128601a0f0365801d500e485d9001d41c2e900300c9441017826181d80342c0030003603005880f06081d001d0320307106500209018412401d00d801c0c02d0744c40c01900101c070341400005182c041441e003080080007100300c80a02d5032408000c00002611142030f03204165101202144084a818050044d03c0000c82410017580701d62a01c41401020700c036090069411051a0800c441c4550100000300340c16500034154192964a4440303038a0a04004200f8903440d0308420081118207088500140000b003207000700310703103151084040800000c80b05070030090422005100303200c0880c0f0a101c040140c0c08041d0102403c0c110350102040c00741250040103034116007469903c1401c04800480b04541025517420785180400d8680112002d1089101342d101c00d03804200400c0b1000d0942e4400c0260b007001081c00144091b0181c04034042c2c3c1c000c455484510396503207000304102c0c2018804 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 727774091 1250 727772841 727772867
    0x60908130b0f0301050f0616030c06230c031f0e040510090f0b041515030c0501020c0a03031b0b07031a01020d0f12240825031113050c0406 61
    0x10a500b4541c2c5000b900406000500c1182c0c4940c80710b040304a2a6180c503412244848d0034038a4203030200e007040c14081c104106041040f61114604010b1200001106101d05207a11103d48100403c0d1214500c4c15041e4101030065503043c81e008005030fa001640d03800341c0000f00425100000b00c2d14041c18403d081c1004820702d11000ba08000e4050002103400e00c0700c9017025400f45409010340c03a86c1c18564600c2e503680d0413484141e440e01010300550004888001c040700e10860456401644941c012601c0d8021010307100d400c02040c802c140002405640030300c10b00c070380710100041080b24640754400429001d40306040031a0b81e40300030036262480c540701d407041281d0a00080910341c032890f00040c00b1034045640c84040107030b031825001e141a001d03044140c0a101440c02a2142c54820004c40121400d91080380c180e407040c218503d440281000208015851075441003110030300d140c5801110450780c80c0b81d15840b90303400807030710382481d52032081500a0414151036600c5074206003001e8020340708002 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 727775341 1250 727774091 727774109
    0xe010501053106170105010206040c0e04051e0f0c061204080307050d0f020d0c0906091412160f09050f06061c1d0f0f0d050a050d090503031b03040f060e0a06090813 72
    0x1c2000049180d0401c8182241e484490cc1c4941e40c0c0d1b6414514180040790300b11015915400303400e212001b0b400140441e16003004030030354500c1050308003082114820001644500860800014086404c0b070340516441505420300924040020b5441021140d514641d1104954045201000005644101d00d2405601d0414000c1581040c002404802c032510540e07489001d48002e85001e0744407808442c0c0d141818908441d10b4a80c101e0038185010003030701860310004200345000034400100d0103042d00074a03520700d5032001a150642030105960000b1103c3d2004810404504602c035024418584403110240b1341403190381d02191983d09010801118240c140d11200001d80000004640c0640141c2207041840d558024480e080e200f40c061074a0b80000c01d882c0880d680c041c00350201c000c6200d8801c00102e01c060513030302440992140400e480141c9124000280c13200012003590140c54044d41e0031048803140ba469035103140a641d000b140072600c500c8041040d10b1718040b07100102002c0c2031420 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 727776591 1250 727775341 727775353
    0x605040c0b030403080426040e011a070c140d020d0b09010c02030c03090f120307080a02071212180503010207050f12030112031b060f0507090e0105010531061701050102 74
    0x2460045ca070302c41c003030000340841081a03510300c080389112020400034502816011b440c0c0d5681c0040701c040c0c510901c00c14030001d102e043d1542e000d60b00e0300104c40b03440d41d005a5480b50340e400c0081d5140741e050310121142d08109500d200a0247e950020ba40e05078034031550221080f8509144d17140e00f580d00c403421a405561050003000200031021055410146054a8441303403150f070700000540d090724801040400740000541d680c1032201100081490341210b40845000540e158150000740b000110017400415a501c4003960713103841a1a0032040c0303c0001d11040805846000003030899110050842d2560b00c80480604103040c280900c0030203000c1c6007112410341d80342100015803041c0b1400001c0821502c2842104c103400201468001c26401501c100569040255000000d003802d0f107071003001c544060030000d1040c001994140c1600d0040e540c442c2001c8007840c2d40c002c20380241c0c0c4846801d480d04001c0350f081e580010007020013000c5503039507030b00302c2d50101300440e5150740183c000c281150805 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 727777841 1250 727776591 727776593
    0xc19110f010810140f0603040f0b1302061c090501180b060a26150127050106050f1315080414120306060306120706020706120624090906030605040c0b0304 68
    0xd000da110031030b071300316084440c908200c000042c41526001007580d4030440c04030500c4140001d14440c0301800d4490a080348083c2c0314250004070181884000030350065082103a030302240d180e4100c3d40c18440c429013011544002d141d8501c1e095525003118103580e40703003814003a030a103c6820051604a0000d950700a600d5042c80c00020441c03901c000c141000404c083d07a0359101c824100001610f089011950b6903155845201c041041e00e03c5080c2003801552204154419440c02d00c01c042c100c560580715149030400d0986201d0b5140c02c1a5504c0d00708029400002441a0225121480c070b003049550b0100705190914041e41c082512000c07140c0d050b400822889001580002141c1d0030075422600551259641000900550090601080d0078002e4240002e50070790005000c0c0c05980355621403160060110600e05c080701d080b441068035291a2001c1e03007a00700c00c440c415444e0903149140c003c01d0756844811030700542d502980111100c41ea61000c02c018070441011b04401f509a8030503017480c504003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 727779091 1250 727777841 727777861
    0x20a0f0507050a060b0d08030c180103020c1b01020a050f06090f070e04030c15230a0e070b130e07020601030c1202010c0201110c0d0b0604050a0b01140c19110f0108 72
    0x8603c0740107004079602c82c1d1030003403583d03252000e81c20b2503070100c1001d580703281491800702e1507048144600c2e20b04001c00c071004450742c028020344820401d200300804130310181d964034400c0f07201002c1e0410b040d40101080d030b070301242060140c40704c03130700042009100e1424626001031921a40c0c618007904c0c4d422a20040c003441901d4800c0b140c000784c142c64160b100c0b181d40d042071040302e41ca4000b070500561406082403498162030a0107050080c1811060011b80c2e0340c03410007001c0d00c042d003040740400e4101e01c200744401c481c0380000c1c003507440201e03401d1081940c8800801450200640303182c005030b84190b004200b0000c0b5448038401408446070704480b446001c0d030010700056070124000341801507603000c0304441e8204208950f2100002059407510746042c1c1801d8038213050035941d140c015410b100002d140300b40b00307002d5049040010307503419403087e030259400402500034125404050062244401001c8001814946854040c0d811042103541402c1000b035001c0101100c0c50601040c00104005034130 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 727780341 1250 727779091 727779103
    0xc0d1401050925080a0209060d1a06030c040509130602030f25081303030920041d0303011e0915050102010c1119150212040506070e030c2b0501020a0f050705 69
    0xc42400d01c20041d4442107810ba01a0060200d010b41000d80031a0200e27030007081c1c3c1c00412442c0303002402c011103001d2843c10f1001500c0101c0c0e099541c0d00d000c0200b04a42e06090007803a80c0301303403540c0518052500c0d0707545000990780107942c0080c49042030380c14402141c442c0070814441c00c2003d00021704100a060f4090010080100449100c0e80c400545000340341c001d40216030700590007291b503015011500525980c1c3c01c0340c00d520034003c51900e02800740c81c252403012441149900d100460035a883c00e04c200c100ca8440c1c84560042c41c051260001d400117250140c01ca41a210002084020341004002403c4500c0090490100400003015821a01c000b0454203080a881d08944141d1851414010f80520200324074214003880080d9600d61440115980d5000324421030a40d1590b80314608101c4003414950100c40c4e2517008905018001e1030140c3e000c151030300550701d03056410184d074045580038880048080e1400d075000100c031000036608c503582900b080318030b04100c0e060040c01e031519643d41c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 727781591 1250 727780341 727780411
    0x9010f05090a0e0405030903070b0414120703060c1808010203180c0a0b160c0b1b120901030b0a240f21020d0b10020102070606050612040b0c0d14010509 67
    0x78102404138061090900c01c603441c105003d000c60b80481c2e914a4008490b50140c401c2c800310a00a80791601c0034a0b1140310080361112001c0180117042c215180c0e10014100b00c1c0205082c04030005480851380d40314800d0100903c00b1000050305ea1802d0408000842c031114840721007500300780c9200c02944e0344c4510010076500454210f903140d8041c42070944501a40d40c4014015600c180000980d9100c0c5400514040c21034000e00703d03032180030700401907440300141242e8006140600000d0502d500c00e40c00039411640041c101004982c1e03c0f405007200582c1c0c1340002900e400da680a042115402480015400c40c4074a000603500002070a0080c0070200c0c201c1240c0c00680000380e002c402d240a8104810f03980340284616219500818042d0003584082c00c00c44800d810900d0000340c0749400c20940b4840905098079404542d100d0b0345907031030040010982703e40c0d903105000c4072088000b180300b60740e80c0301964504503a807075040ca0108840000000c0260060418001d0342030095500c400c001d00541b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 727782841 1250 727781591 727781609
    0x6010f05130b1302040311190806011e090f090c0b191b050f030c060906160e040f02030c0d0b060406020d0807020f190b1302061912090809010f05090a 66
    0x294505a0000d801c041143d80007580243c008200031091000c03240074050b00b2242140c440d060908903d04014a4034014480e120283e0402c070010000c64844001e49150303c1583d90b0902400c64031050004100c03082001456200c1c1c2d03844400e01c041005104400004d407070300c3c11444d030810400c42e8035110720701d00c0c0108410412050782d0800030b80000c10303840c1d0b640c402c2d4404c0c2600c4400b070202007a00e80c3c9421007001c0c44001d00c14080031030b50216010803001e0046802c07903488120352000c00e0007940c5900d11b10003960340260b40c40c900026420010310282d4090803c1c0400c2c1943d03034003000c1e1910103403a01517401501c910f501f00001c00c242e0750005010f20fa8000c20742001000790b95407160036801c3c03440c0307050b1321105401050030f0002c000d0b012541c1a6903440c8910b466040a861381d1aa90320085902030380290401030030000c2c850000100d042481c1c4407180751400c1185103c0c003450b0801610340503a400c5850241c04600d01c1e81ea5030b0409140f04130b925481c82d00c2410b02d020240007850310b481c203200744916 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 727784091 1250 727782841 727782851
    0x11010f0e0603010513020c0a03030203070816080f090a0501050702010b030106090e060a0e19081213050c01110f010204031208061c0b0a0902040905100b03030a090b03070c05070609060206010f0513 86
    0x4181722a0144c4014107114403c1e203a4215070381c02c0103400b9501c02c680360700024003050002001e001e00d9000c034039410200c1c9d91300d420099640d0f4602030301948001d02017202c80c0c8504495400018024014148a03108550000c14000d0740242814252001d54210604281c00c002403481d030042c0006446600c00103801c4c002c584442c21701c92113030424401c444401c050703c00d40102c880600000000404c2081d40c04800c9c160107940d0398007070183e0010032a0b00208140c02000d0441f6017903224582c0c5c9400e07849450b05460300e107444280203e0032030f8065841101d40401500040045642203000603602c444151854891940d441244000e03ca0464400429214403080803502d1400d140e400402010360241041104034100e06109540741d0601c000410f00302e0404900c0042c6040200680da030364065922104421810302d03100c401e40d900014081000c020b071003000701d80418010071008000304101c0e04ca008840d82084002801c02805070041e055417407415004200039224400252070000324a8400a1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 727785341 1250 727784091 727784119
    0x2061602060f0a091b140904020105090904210915090e0c2808040507150f03091e140c0306010b0906031306050a1e05040201020309011b02060711010f0e06030105 71
    0x4041c0c0d03c1e0060704001d440b5200720040003140d10885c003501c400109040c0030b44002010060b804404a0380203000400600907031685060140b0b10070f07049403103010f42a500e81c5640da81c0b5a00b011280000800107010860100001030f13141481c003102500615100344d0150401001c5614a00060b1010310010000100310071402450a82c4840084070022504a802c2c3c0010009004007801e030340a4a0500440d140040c0c1c030800c0e000b00c1d5801000f40e4440481c000002c00040d402003071350740d00c00d540c411840c0700c074010780705525520400c1705481762000c1c0181000011aa500d400301e03080c1158000d2348140c0c01072151652403030076510494001c43c0e810343d699982500304000490a080020020740c1001c1c20b0000e04411a04010700084a0070524281009c0c2e40da004010b4440036140640540c20802c201d00c0d0755441901d4003013440c0600b07030003d1440c3c1e80541c0825010350001d901920386942d80440d040b120360b8011640b4000c000c640c40d110500003410310024200f48418400c0754415412000220 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 727786591 1250 727785341 727785361
    0x1206030b0c0d2a030e06091f0605180412030908030606070327060318080306120a0b090309100509090c030702160f060206010512060a020d0b1e0102061602060f 70
    0xc1c054520410408055083d4004520601141409038000c6401c1140107480e00400055481c4079105480003000000040b90321101c690405142c00c0c0764954450801107041e8030740d0300100c04615007100300120ba03481c0609014410302d44a42d25001050b00304070070940464030000c02c1d6074115008403001541c1c1c90a0746002e540345a405900e41d1035441c8061280d00313592400d100104102c6d005030302d09020a100031240c40d61060100340004009035002d101289450514200700c45407449041c0031102001d0040e260200c03180d20071610a83e02d54000240055541407441d101d0f40546481d0504a081050400004041074001000051229030110024914503c20884079101c03003600c03521088255103a8607004131500840c018000544603c07000040d250400f41c621090341520072001d40426140d100400d40070794040e59a8000c02d42c0c44640e10340032562039600e0a4905405a03a0641c1601c22650002e82407810041c13007526241102c150281c241500403c5065102c00480410300940d91044400c1c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 727787841 1250 727786591 727786601
    0x1407050315130504030c050d09060c1202070803070602130906060f0c210903050d0912060506040b0a0801020d060b0315210d081009091707020d12030b011206030b0c0d 73
    0x403542403c0c24244000d05400c12a6030b440d684c0100c094907206880d524043d255070300307648500d40c00503000c5413142010441c04038800d1403854091068500c480da4408030079156801c14401521510340c0014803040120072444d01c10010b005031719042c8803080c602113010b015002c0d04921142400307000103c5108001407080743d84c0094a082c114621009442c0200514440d40d6000840d62403050340802d0f030b042c0340906450400c4402141c0712489020440da00c54000e401e0240c050b81d081903c03018100e02595414449501a0038034100040e1203100e8415918255a481c0d400640c00c0c450030418080e40c0e001d01c013080b402c24241910006010207070b50004464001146114443c64054980416000c650040c0f2150040c0400900d01c0071061b203c0c224a1300310750903641300800e00e03050782c0c8070480c107182100094203506000a10704101084141c44810080074984020310000740d94901150056800c4500010102d00071a010800a1f0855030340f80984400030303100c00300c0c0f0880855800c0300c0c90030036008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 727789091 1250 727787841 727787869
    0x1f140a1d07060f020705031516021002040b19210905030d020307050702010834020102090301090510060e061809120c0a15050f06152b1407050315 64
    0x301c400003030380d40c0d0000f01403e0ba1240d18100500074410300245a01d030000c0c8110305120103c2c00b003200c81d2603014041494114800c000405c1d4001e401c4a480e01b0302c2035101800040140100c015a21001d000c0301054000382c035a051001d204000c00c0507550240c0d410020050142202800582c40c0c03c142425481d50050f0000001020300000801c0880b43d444005010141d100707803208506034444000000c04240000d254041c0a100d0b46038040c2008080103101e201010b5a00006140c106140042070a680c003801017501e140e40a50042507606c1503900c590070060105882e0751207941070903030001d0898140d40340740d003954140305c801040c1806021b0050306507000b0746600090b80c50041c6100306840e1680402c0c240d071054007c9124034072041490103020302c80c0070200d203810b200da9140c2e02003200e0f00b440048009484001402003100c00c00d424896400e038071041c85820b00c6a4241600c4540c25902c820350203880e4020780c82c0912014031b8115055070340100b01c84451000c41c4500c0d00104000300c1c403140d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 727790341 1250 727789091 727789093
    0xf0f1b0405090124020d020c0904060b0d0b190606050909061903050c04050105010f050714240f060105090108040b043f030203060a0315020c01050106021f140a1d 71
    0x100020304508410000110061300100d125010038070441c060b41c17034a001002d82d0001d87c110b8402c41111b0304d8914401070f4004e20551001039144464004a50320b54103003c81140d4913030340e000074800c22401100400001d1b80030050f0511046042c04070040c00c0b401004040c3c1d004104240c04580d00d40e460700b904152400010080b03240060352414070729030781d80f03507058400e004510b0440041200c0d40300d0541100e0b40007003031311014a4644075036109024021101c2542685004200040c081014104507200300f5940c12a241b003580c2c00e007181200c50310800549103d0500904001100c15640c000e00c0d05a40650010b41020b9a66213509011140b100b5200000c1219800b0341060b55184140f081e0040010301c029400003001c21810000350224801075548c3c90340540d070700c1010000101c2c0c0203403142505500c0340000d070070510001401c1c4d095900030380000f00580c0001d061409616900f500d45041e1341c0031800c0a001c00d002e5680380d40704032400036007511942919030b107144450035600d102105013030031040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 727791591 1250 727790341 727790359
    0xf060f03080705190f060f0902060418060b0a0c0302060c040302090103141f050f150a1203030f020301030b040510020316050a02030903060a0b18010807151e12050f0f1b0405 76
    0xc58020990020030170125101450002c10061a01440c03040340b465940c040d200e9407515040c10708684400f140c0d203055410030f98685101040d003119107409400c5040607501d402d61800101d14019061403c010940e0124074414081040540d0324400040c1c11070703030484071102c1c0540901d01c0c86401d08810f40302080354130380340f10345500640141354050343c442c4038509000307242c5403903c40f000b00a141c902800a079005250050600072a012030300303c03081480c4079090000b1000101c21000b81030b41c100342e000351030324207040c004c1006201c1c00380003c404c21409040f04501e10302e0000b200da0803010707951038410b040000118948811074020411034421450042c11111240381801d0004040c00385032194900410b107040280801a1100380300d14141d0310594040c3c0780031420620322203000f2030400e034840100540300c090000301d40c034010005000890240e0345d040c49505680c0404d42680d0025003400324900b41001044001241c01030b00d15080032403400142050003940d50310102e42d001e5500495403000300c0c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 727792841 1250 727791591 727791593
    0x3190f08031006120c020a03080c1605070504060501020d081f0503030d0501240509060f0415080f0f0f060f0301110d020c072c13150504060f060f0308070519 69
    0x1490030448440d03130b40b000340e08940c4c0320602040c1e5520750b181078090b038415215480042e00580c0341c3c66005e460345420900b03001c04902c0c0c1030a442a400410b880713070b0304240c0c03042c4890300309802000041c02082c0000d00714900302c450010809200149114032030010660400c0c4450111150b03a0020103005084035160782c440050320000380300070f2003003907480880711116034031600d020351002e1020780558403294204261300c0148507042c1d100141e0301480c0314007000301207100398503003041081c407005e1a03550320050b207080c1d0904454000054031030009a0030541c1007084844001c41c6a951000b0140c64600c0c0d900440008079014020030302058180300000b044098044010b94040c0410900100171500c0b00c0340d07101148115802da2120711044980b48a0035810224540c084180d04400302c1811131030148010344600f040c425000d00f00c1d6840320f03100d5050105001712805050a60700401c003080010700e14105c0d400030166103078400208040340c003103070305000d100e024003510140c1c40d18401c2014a1150b2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 727794091 1250 727792841 727792861
    0x22b1b0503120106020c151b121801140d020c0c030714130614010513030c0906031b0b03010603091104180b160c02120c1801080c06070203190f0803 65
    0xd040d001c0c6805002c000024166100103104100000040e099518010080700140c0c425840300c2d5003017445180e900700c1c2101e08003040060591288100c5100c1d510b43d00c4101c02c20800b119101c82450402c02110845102021400204c4961154028005a80d0052079006a01f4626103802e815858020b4540029100101190420179100d003111903d032008c00e0340f400c00e8112281401441122941141c0e204c107154010401000d00046a13001c1c0000180c0e00d907500da944040c0c80e000701e2580b540740c40f030030401c00244010700320385e1503036602c00d40d280c0c4e03401c05103400203074001441100b04241e1240c602c1e1080c03107410305207503c2ca0000030308140a00107124908840d0321440c640c089036980c1c070200004220612000207006400308170341e245000410a41c081000c02454003203001c1c6240900c00310401c0c1c41d43c414282480445410508612a40c0740c0242581407014421000c2d0084c1c804220704001a500443c0307422405015880303c2c20359620740c3c00c1c60303034030012102c0c00107015050000c1031000c4006 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 727795341 1250 727794091 727794097
    0x3020a0c0f05070f0504090b0604050903041a09120d082206050a06061404030b0f1b0316020c10090b07051612021c0201020d0c06020c011d0706022b1b0503 68
    0x851901c500302003555440071b1004403068010081c04542c11000071661515081d04120707048000c1e0000c40341040e444a58036054030314074031042da0300703600f0011388008a0705141c08042591444c40f8040c1c626480312000103802154020004903080055061080c5000440f968160485420078030400042c6000b80d4840e00802d92030241d880840d500c80c002e900c25154050840c4c040d42d600180d440c0190307c681d070342c202c04050082c01c035181c1c0004e00d0000040c0e44501101451080310180040140c151030981d0203806c1041702510350b4020590b0f00441d4800581150403a401c903196003880d240e43d58214200390b41041b01c5803074607880c0e69082d0080001e000e1101c0994001007802203a111a00c2510105c102e02c1744610007000078056041554031390ba6490060b0070401419020790005807411798100b58403800c5940701c000da94064500840400d2601c04100440380c081c0c2010b000505403140c030a0150540c01002c542c031902007100110b074180729503110f5548414045445511000180c01628003540c60360 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 727796591 1250 727795341 727795349
    0x21081302060a0807030f0c170a0e0d050309120c16060809070b0c01090206040e01060e0d020a050108100806180f03131e090507051801020c151810020a03080f07050a03020a0c0f0507 79
    0x35220344081074100307008ac0310f0300d114010342d0750003488507440f603201c1565250801014140e17a402442508102032601c3d400408407245118050103c00344100702c01030301c555054000200700081901000014400020b842d01659224030859844050022406015000d00e101c002d42009011400240445440e0403c5050b42c980da21081202c4080c1c4040c440d80075403440020390b00582014082080d94050715101d50030000d540e005c50211521000040e103071030303010b49488241c004861102d0340e07654814085c4981030102c0350080c5280c01c2c4104400c540c00080350103038401c0e011081411418100100340d00030010b03e40c00f0028172591500201c040c0c020f40104000312081031800c01245100d6101251968051a000344518445507505012881507000303403001c1c0e1145012201202420380e05e0560040d40c41400d98000e060115213403800510204000d0078000d044c800311010300078841d80040a50f06058070920340140c46154000c0200c03000c02e60358402801d0100f03000100340a00902149582c180c0d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 727797841 1250 727796591 727796627
    0xe0309030d050906041203030902030708031b07120b1f09091112150c0d020708030a1407020303061005120406060e010f0f09090f21081302060a0807030f0c 68
    0x10030700300801501c9512800c03480e1644124204814840303105501440100c040c00385c540081d0304c00c5a80d02107071804401c0d400c43c50f055800481c91040c0d95003e40014040c440c0400c01400705249000303040d4059044140c00100500e06000000c0c40c1410601040302c041c2e44d15400c00613215607148030600090070f0844081d05d010b040400c0c010101d05140b8611800121424000d04104500346001c1d54100d50241580300e80300c408004898041c181c2e07001030403025020300b00141d034a042010f00c440880d2030324002030006515401c1040f201d076802009407540a40c0c03d4450a14081e01c040e42114288500000c1c140c100040c80107100c144561381d03001400380d88402045003100e9894201c00240b2881d54454800c424421610038400406c40b60840310142c1c1c0308a100301101861680c0740e804800d04100c5c0c401c08905070b41c071861516503104c40442d03041007181c411b04000300140d4010070520320410802c5001e02c003160003c58072142c46a440854910007a403010000c407101c0080003010440b035003548100c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 727799091 1250 727797841 727797853
    0x30e0a03090e16082404060e06090609160e0f04230a05011206091707031d01050f2a03030106210b0607020904060609050c07051009020303040501140d0e030903 70
    0x2502e0083d5000d0203060040d03d444090b40d807500c104030b13044400d401c01400e255212202140403900e075800b0b4540a801d501940c020f007807601c141449582000104a5480365018006001e0a40800b03032043e01401c10703615112000c0031400d004182d100c042c090000c1d81141c9080d034500c0c118203481d10034124071800141850102c4c2c80300100d007000d40308280210203900070f0401c5041c000886960110804501c03444003d02520400b000c4841180c2020400758045844031000f0300d00d105122918807210002400c0007801c00d100b02c0c90205280c0103180001580c1d01c1004103545a00f01c200001854007004601242d039650307192500200f038140074480c0c14080c0b07a00c840000080b04c2c1340e40200c40c0c440300c01415560810321903800300141c2c000c01030f2003a25050340e51040404d246401b4040c092061403190030107699002e151070072501e484200c140201020f85449225001a9030100840d0119a000d1803c10300d4400e20307107800d10303140c0b05109008115074078006110268001c0800a4001d094088040d100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 727800341 1250 727799091 727799101
    0x6150e0405150106020c01110a1a0103021203030c030601031d0109150b0306061f140304030c02100318021e0418050105070f0c0303020a050c030c1005010501110a02060307030e0a03090e 81
    0x528036100313018070000740e0000d20700a883ca52040440e06060b6002608852070040b0507100d10100da0003640d4810281d48800c0c00500550030480c94040705510008029451840e0003400d40c007a0b400007808560406498942d080614450058049003912050f0001c210410f568a0f02d00c000543c015401c070003460502c0c82000180c500401c0345403046d68050a080030b681002881050f41074011b05207c001c0c4640d07000301d0b0308400d00d450080c501c035a1007078a1b19030b0601c607503004101d2101c1c0b001690b00708240c00d01851450603414010312038a030703550590702070103119540a0715451240e0300c6071807550414a809200130001038021a88800140144000c100c030307403203420b011250b81e4079105e4502c0c00310f6030410a900009207c1d5004120300c4800d86006420442e410031050705580c41254958030f594880d030128000010188282030043c1001d08040301030050100240d5101c4528800280c411078001c0300094606000b5000b007000041c040d0250b400c2051207180243c00300001e8050b4002d01d14000b40018 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 727801591 1250 727800341 727800373
    0x1e060a0302090a0f06030c0305150a020313023a020901050901030503070b0411060a02100c020c10030905070b1201170d0806090402010210050c041e0605040b0706150e0405 75
    0x8025690003400c00821a910301100740701405818140c040159620b21001010469501c01840a188200007402071b039048095070750001c000180c0b000c003240c0c2c130403c01d01414641c98401c0d0035809505441540e900c1140c0400840b030030243c03101850914101c1807054071214501c031510950b1520854a410031641c80d0801d000c0d18180901004251b40d00c03c02c452030104566481740c5070712030f114104650f058244040811103a4219801d00d40241e400703c05090500302d101c0c0510707003070b4410920081018542031030018803821a07d078206001d00d5510b60994040c0401440803002502055000380c0d030b00c400074403c2c074a02d058241314071110f008081d0002d103182c080115042c1040300d101d64070081d56031144410030101880c0540100d041d48145c000381201801d29028052181d200ca410039a110b0b0324008041c1c0c1070903800c0c05840c81020600d001440240e810400b40c806a8905040103504d901451500c1e900a0601c2031840843c07000400300000c1d5280d407000c040d4461803040c01030f5103280510b20100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 727802841 1250 727801591 727801609
    0x3010906081e0a08031f0b0702011106150103202101060203070b01091d0f01050115020309030318031216034112090a120206040c120c0e1e06 62
    0x2100103500400010f00108801c000a180c000d01d000c48040c52504102d2010400c41a407644a00d01e95140429584150341c3c000c00c0304050640031030003038001d0345440850041c5465030310b0031280c185079a903008010003c1c00d8540c5c10582403502d041c0d80356510140600c1c859204000c50552004c0e5040c2800410320074804000c0c1e88100d41d000780e0001860b420155034402414220b011620382d0006141040d1400208202011000111900006455040031414a2043c40c44280c0c5015944100071041090300d000045400040c00311080701108802e030800a4107207035032080c5503080391001003000300d18558030b070816180c014440e03120300726845039003080c05852900d20310482d0301e0074410044030000c0002141d0007a040c00c1000000c1c61901e481565242000107083d60100301c250700c0212110208484d101d507017984070a1a0006180030302d441d5489092182c01c5010fa541016030310700e040d404010072050390002402d80311611190510b0000569458841100651205004400c4c00f084141c2041c13509 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 727804091 1250 727802841 727802893
    0xb1e091903030c050d050a0504050705030a1a07030603170d15080316020f04020d0b040b01030b0d1712070f090b0f07020d02150403150c0504120b09010e01020301090608 74
    0x2105800d2591910160b005101c001112410f10100b000a0301041070203200d454401c8014041c001100d0034107003010748c035060841c0c00060290340b0494800020903200e02a0480c00c03040301070522010b558040046000e00142d510051102d100114a51400e0014101410310a860078000b00103a07201c0d8050303001055058490000103400c20094488600c110703203060b14031540081c21203110301580501080c120784c41500e506e0b001c1980d1314101c030030340d1605004030b685c054002d103003d12694956000040c02042075680050070b1569034030744141801e40d80025515418a442c00c1c4016504d0408005840e03c80c8900550000640c1c2d4170011440c009000180c441c1c0b070701e00580b40d40c06c1207002e42c03d2000c00750201000741c0e40011600004c1c075a15030303640d00600140d44150116643c26902e030f030b0381c00c080d99551314007a024081c0c20300c0700f0301c0031402d5410710007030203a00061141215218001039600400d0b41d02c00500305540000008218004150000800c68868a04070b440340c480c4403079200ca01c0110f4401c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 727805341 1250 727804091 727804123
    0x50928020901050108042102100501120209010e0a0608030304030f021e061f050310140106031103040b060103180605060f0109030c260d0c0c080d020c090709030b1e09 73
    0x30050080354807890640c1e500920a026070300050f10380007000d47c10341510349004030050388008099542d101e13480c01118010700d00300d01d4143c40c0c4074050780011039110050092501c1010307a0780019101c001c07280c0000d0000d04641b0266aa281814203004041814280070000036100d50301302d0b107a00300300000707208002140d00e60140440703031280d110180303008241107550460b100c07443c64040b580703a805003c10741420100201c0040d84d150902051040e41805078003440070f15107040d0b2145010f950600480f684203030310488804041d075035180103900600140c29080c4e00005d4140414041240d180d000a0250804a81107002c01c0c003004011030f840d045a0200400542103240200b006038202000030408500b02c032a4001e080c110035500e40e24000075100301d20002100300d46e21500b031055864020024086480184c0300030075681c040a541e41c0d211070480d41c021030720000010300b440c0c0700b880c2d00c0000c2d56000f0b0518207641000c18240443c506403000c0d000e0400c910102080f2201d0000501480402c1420 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 727806591 1250 727805341 727805359
    0x9020a080303240102010b090903040303270302040504081b0d091208121302031b04050c0a052208010c081503030724020d05130507061b080f0d05092802 67
    0x181640c43d1246881c51003506542d02c0d207a00d881a582c4d000301d25171141c4d41c244011a10f45185081c024200d120010611400d60b000d4000340b164103400c01602029240c041da0042001d860380e1500300e81520502074501c80703021100305075640003900403c0d00030307400049075214070000d61280401a403910540c540244021400c010351075992045280b1640d000341442e8800703050396169004241005a0101c418218a03010020003100b880c05120349a0071081210000e0300300103000e41302410602c2031140d84440711041e001c00c5030350600c00300c64000240110340001d016140000324044e10740e46040d0394402c03405007c0080084242400070641e19110340060503000b05030489002c0414541410864295040e001c0062522450240c010702e4000e40160200c100c03050241d00f00941814020341003c0100070921110060400644a0f18880c0c1034000006556480364001d090710366110342100c4246890901081001e42603010400c0a0328000e2a04221216030f422490b0025400b84603900a41c424250 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 727807841 1250 727806591 727806631
    0x1080112021509060316180e0a2a120b040209030a12050c0604110111120d0b060d09030504060809061e060607050a12110622020a1809020a080303 64
    0xc05100c612060500502d2400f101c000c08a0f0281c0d000b00c070011102441000203103d00707688034100302d00b40c250500d00003020b07600708200021000f0014141043c056100c681c80910985080c2900a182d44c42d600044008000c0c00f4000e00403400c0524a88020f91400740600503a08043c001c5890300a4010040c249150341966800011608034001d8020020306000941030f90b801084a10700903406200ca0b901038007881400108508245034254080b80c01001034000080030042c02d44032802009403020402c0020040415250b0107455a01070300c01d410000c2003c203240d00300005209a80342c9039540341c170301d965010f001a5525800d446400039483e250b51001180b80764903a2854100d000240f54514044058580c94070340324018034142c440c000311201c40e014058015805100a1460901816444c0746c2510b00101d14103c109811070340440400c1d145085550f0150b41c0c602905400304250030f0b26a003170781c0d1030006112026081b4020842c924021800c0c640010980f4851421145444076031510 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 727809091 1250 727807841 727807849
    0xa1e1a0a12020103150b03011214011a010f02030702150909100806060409020a032001080a0603200a0e010828022805040606111b01020d030207050304120807110108011202 75
    0x20000d8000303210005c9040206021100c01c0c0294028000140d0440c1800041e003810285960003660f404401e80c5004104442c2601c10f480051142200f420400c103000c255440c10b900314454007000070350000b9048072080080204070050f20201c00b081e2042c200b155201c1040203d018aa030150b140254054400585907140035000507a40078070141c6031000f03030341c1e42c0d03a60300140b40d00100b40d071151620180345c00403955a02c40103003039109079a40014004a440c640b94808141c000e0700c65041003d0198581302115212030b69001d008005201d202192981c0d41c00099403076124844018120300854160b41901d0807080016000b46a0002c0200081d200d804540c43c0c048000701400741180103428400141aa45500c5881c0040a040d01c400c602e0f14404280d1a0405a2003030552120001910410500743d0f8000364921281d18107050041e0b07100c8860400d1071540c0600e40c8240610849a20b01d182044500405440c840b44244c524031071800d8803000548000400b401105000c03100c0d82100005450 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 727810341 1250 727809091 727809101
    0x708030a0815060f0403030509010215060a12111c030f02150a020901030b130b0a1a0912030d060f0e070206070210090f0c0603060e07030c080f0a1e1a0a12020103 71
    0x2000416080c13030312503950604101030f0040d03441600402d00201e10311520303580500c613003000c00c2d092a21000c014946000028502e0200d402044080c7d117110003030b44100984441c0c5d00c05e009400030100402101701248400c000e5403100030840005900001071166a0b00010741007422001200403200ca0f96030b82000310000350025108903040544a2400303281e540c0300c0382c058040440281c071011846c901c52100340a1700500d41c0d80003440d203451805910725211500016595010422510310001d0075228502c60702c0e5000d174545042d0310740d01d031110014180340f114403c1011510b405000b90410707550204282d0701c5613000c56081c00581c105612040c8030080c0d5610043c02c1c40d00c55107a0603070070101601d8042e01210242c11140c04290349520a1191400060501e503000b01d0901d0280046840d40c0c10041000c1d0f005881c0c0b07001c0040140225403420015084070744800c02099091510041c1d030100d200c0034100c000303c4901f9450a0765450103250a200488030281c07852a040081e88540a60044000304 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 727811591 1250 727810341 727810381
    0x601050a030504030c020d03050d0c0e131503060612030e03010504051c0309050114150603040c0326120708060d0503040e15030d0c0312061809030302090d0b090708030a08 75
    0x80e203410000047c2d50301c099403a0424000e946494039083d8860b81602103550b00200031007444501c4026022076541d540504480440e10381c0040303800160308002803155009600f0052039142000004940788107806807814601d402031b60381070501030034002807500304c03003054a0151142d0418110203082c01704580c0011074403c103a140c0090003040e142c80d10340c01c43e403031301d6141d03000003c0030800d000924101142400480030308450151841c1030650f9140450851480010712440030810310105180050060000241c01101e5082d40c03488080e2016159490480d00040880e0303c0d10081a030358208012010025a4040f004615050901c5c450031030302c880c01040100ca0307441b9015518403070745080c081c0e0748200c0040d80b6009040c40f95032a001c1c00c040e62a5a400c0c0c1458500101041407510740c03da207907001c10640400080d254042d0408601a00c1a2508103400c5001c264000080014040459200c1c0d040c01c0c061701e450300d07180c55115849210f401d2401000488510200f030204254004840f00341e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 727812841 1250 727811591 727811597
    0x120109060c09062111300a0b090f1b04080705090108150a0c2307150e0a030e03010204030f0507091103240a090213091d032203120c1a01081207020d0602030907031502030601050a03050403 82
    0xa045800c0c03141480764032a412004245d00142410440c608002d07600743070302600c082d80152051041262410680d03a1004002c400c000d070710741c3e4641c001107000c3e69451012441a02e1000248140b03420011010392040208a034420710013032041c4800c06c4070340300d10071507107880c3d01c081d000254494908035001e5485d10a00d980c1950b0807c40080003840c1c2ca491028400d1003280030f041954a00500217080303070b4140150f600543d50400c01c002d00d0410151030382080310301d0400c1c100d5075603071140041070408949411580c1c030240700093750303085420049441b01c11140002c0b400c0c4190041d50880c8001204c0302c0155030a0fa900510403061100030041200c041511180074100c00d96a0f40e07202e451a031207107800700c04007203880c0c50480030600421400d08082c0052000d0340e0031455161260607564dc094071043d030030b6100d401145e0319007150b5900686c00c407903035000030f000e40d14ad003400d5000584a080030300c070850343c00e40d0f01454407504903114001c0c0c920a400c142c40703071824202c0601d016009001c0061040b020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 727814091 1250 727812841 727812871
    0x21f0c0e06040806071b05120304080d06180b04110901080405100516110d0804062f04060e0a0b0d0506120109060c09062111300a0b090f 60
    0x80c5403039000103031006280e00c60050415040956010b03003c2c1c6044603400704040d10321480b034400710f0000545152014910300e607469482d500c50414184901440009040c1107081c220006010f0134124051252038882c11000c000061100b0304002c1140c6071501c01c4441003030188841030040d8050404680c1c01350040c81920003200c130030742e4003000311072044642540001010150621180c0d108a130700415881d2700006002c0303507010312009403e05500070801804152183d048196454481c1c2900d52a2000140828001c80c5502200c0017250000e008000014000100c550306501c0c0c80c0600e1030855042040c80b51418107650340c80307006810010f021603000520003038041400742c0d0034400d6000c014020203000401c00188800108614040e80c0480e040064055083d0340300c400b03405100482e2a503e0b000050780304049501d107d214020500880030740084040301c1403503032010403108601c03451203c051a001d0f80e00c0054030000c4506800815400c545174800140640c0446003180d03030070642ca0061020 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 727815341 1250 727814091 727814117
    0x1050a06140d060b070305030403093602091504050909010b100f0e1519020705060a030e0c060a08040c0803030c0405010309050c13060503070509040b06011b0c090219021f0c 76
    0x2542c3d0f404a031701100000c100200b00f01c03e155000a030340014040b01010020006220a1205000301c0d00342c034410544140d100001005030003d50448006580183c05607805e5205507008402d580c1052241c640501c80700c0d80003070040101072051300e100820080c040040703503100c04801c8a00e40140c000400074030144001400d4030f903a403e0340b800181041c40d80c0d0f1b5956007440b07445101041c40080640c10640d8400c40091150360303600c4054031810f0324903150010320000e420354424a444031411520740c020030006400b0003800d40c040d03c800e1003280210301c0b510015903100308540c0d1702d2108882c2000500014407040c8400c5d80f003500540c918074020f404441480036140c00140720700c0100c807000b00d03043e030b9144801c1186003010b2003500700a24080341d0b811080d29150700c3e02a182c82c0020485070401c400c0300e00303c640c1181000c000340d0209402100ca080704944604c00c1400a5005520115140d41e007841c0010000d0b10004094210343c440c404030100c25100b210882001d00803400c20841448601c0c5880303c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 727816591 1250 727815341 727815359
    0x509120c030409050a1a0108010803030c07021c140613080912010e010c09050f0a03020d0b09030705011e0501050f03070e0c04080a21050c0606010503180312040b01050a06140d06 78
    0x40d025017a90305001481c00b0300c0c0c01c00e2010341d805101c41795040c48031200040091103008030583e540001040303140d540d20109440020821a40d06a00a1080c9a203041440510050301c0c43d5156100c25001103540586405c4100e88450300c100400a102c41004c0102c0c4106041c40c2151004080c20305001260b8800ca001070b840c2544c03600e0405d02d00007418410100114a0581900d5500c0941550082c060b03178110f80200b006482e01e000e000d41140c031204007281410504000b1202c19a82040c020000c80c030354002c0146d5451407449070124020f003024008141441c125010f0b01182d10010000d109082c600f046001032000024040320021744140710009100205100e220360703c80c45008400715040c1144154561220002c3c410402c0003428451111025000202c085d003250003400d0641e100e030b031490030f144040400c0700310b141707040d00020921004c07410b070510fa81400b580c400c8515003800c2e038031743c4144a9401407610654001485819550001410440c000c0002c80e4000d80c0125500d42c0354134002c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 727817841 1250 727816591 727816601
    0xc121e06050612010501030b0d050d0c020301061406040b21040f1a060f0f24040e0a0501052d0a03050c2115090f0a03050c101107021c15020703120509120c030409 71
    0x41020034330b400d08860443c5000e1007068003400131105100c0c0780808150101d0042c1c001c0b8001c84482d40000540030a590f480060702103020a00002449614030301791610712140c41602d0400c50f20744000c000c02c0c9501009002c47c0714805c00025000c10120041c84042040407103c503403402d900090100040404604090004001a855403050580ea42d20b0009000c2d100e010003064080d075203181c0700040c002680c1c0c20038840103121142c580c0e00c0c0d1060501b28041d4109d1520800e0b20b501c0403142030000200030740400d10a4103a481140d28000c2580b05509004940740300c040d003c00c098010507044801140641c0c0c0b500e8101242c0000c0710907c1201c2d44425213003518408080c0e011850110b140d00001030108643c0c0c0610000361814031254904405c940342c54052907c0091050520702d00081603030110f0550440203607005400040480500b424550007948840c0703054000484080f02130344120224007506006403c074100426518841c1080805140c0000800d018103001c10403000906032003500503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 727819091 1250 727817841 727817863
    0xd02030d030b0112090f170408030d0f140403091a0405060a090314030c210c070b04060e0409080304020d1406010f1d07080a0c121e06050612010501030b0d05 69
    0x14081c25120005080c40900d0441040102d0410950100161014207007000c03842e0f100069021100345040007504da8090303a00201c02c9d0b0303c00803409003541e11158002803882c148a14041080c4c01102400042c2e4072801c90300500490766504040007030210700c180c50341c0c8420034010440e090589910000c0c490340c0c0120604000502e40c40e5041c000e0000c03800d922030700c800369103001310b280c00360303088201f6282d00d14551441c050100c031040710184400c5030011079041d080c03018150303100c0c9501e8051007505900716000c0d100c00a8106103044036141014031a0103174460b0480103c50450b41c4035802c000ea440e20ad04c0d4100c3c0c2801c00018000034589040103450301a10703011320002d0410f03003804032514501000c1109404140000c4041c00b291642000207070303420049028000c01e0801c0c6401043c0c61806056501c1e2030038030f250280e608604010b4400308031021103d1103040c000a961a0100062400b41103094011108400010426903000e9885600440da01405105450180d07803070327031402c14400c00e00c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 727820341 1250 727819091 727819097
    0x70503071d070507171605060f070806120a1b0e1003121d091f08031306020f0304141807020a0b0a0507020c0906040207120203042306180d02030d 64
    0x40c00003640d590360503426405a1145003c0b420010551289664a904450038042803600024910310092100000ca440d964100c800c841560030444030700c10b007c0c402160b10302e0004004401240c2140750000503200c00c2c030403c80041100170304d2921542400d45c2110318811421900383c600055400e00381c0315052041605020b0682c90034030b076003030807a124141d00306c90904118490640311801812690b1028020905441203640d6541d20f280d90b08902c03407007501e03417880310606880000d01004000010301c1081e000d01c81304003410b9541d490aa907201000d1410303400c3d6800900c414881c01e900c5009507003041000401092003024000885070b000d00d4103454210058000004410a01c80181200340e0011503040d0108a145403d41c0c0c000d4541862102c854400c00c0100c01081c031940c0c03aa01910400c0e070f0040f003490080c044d02c81000e55039901c180701c2c03203640344000d1b0328680c9000d01550120549801c00b5040900d450500031090708807101e2401c4069000c000000c0c1c400240c0c40420101c0c4032034550791 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 727821591 1250 727820341 727820369
    0x612091903110c04020304080d05130803090d02011103010b0304030f0e0a0e220c180b09011403070602060c0405010c020315090102091903020d060203040f0b0721050708070e0307050307 81
    0x800c1150400d581c201000d07004900400502c00001d904d442203440c0410b0303209000615813500f0380da2f090250b5481703402609405c400310600c00500e0740411101c00c6901d141d00204016460398600c03084a001c01d00c07945c2c1c114003080c000a00031a00a00c0d038840f00c0c55140c60400d040d80540700008003440280d81120002540141c1007103580c6400c00403d00e400d0f008048044001001c0d5030b0f0fa15220f0300c2c00d000d108600e81c05004414090107031f80d0011030840700c0040c480e861642c0c5030310344501d45100908400744648143c910000e884c1d07002050544c09822640d00b40340c5481d04160041d03a21030141c6104a80500c84c2c2d218101c024652040c01501460310303100050f9590060500f0040342150182c13070141022039003401000140d481d900c04d80a280d60003000561290b5407814040f8000405240152005050b02c0802500940c0041d6005416150107000385000601f000702008441d011101000030500f2000032514450092155007850381c00241181c2005d40c9520200c0d08006156000b000c441240b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 727822841 1250 727821591 727821617
    0x280e0f07090611121c09061434120203070f02070b09091b090604080601090c0c030f11010e0f01020310050316140607020405011e08010b0612091903 65
    0x59186000300014a80710070005070b0250f4254581030030014603501d8003000540000807078402104108810b07030340e0701c2c02c00102d210b60400c80e01034030030001d82c88040c00c16100050b1074500c002e032440c141c0c0189030611559102d016451440001c0c21850428140300c890024210005400c6c0000d501c5500036540d1740322100e04070740c4064580501c1c4c4c1c2214200e03400030300c80d0960948038411802c0e880795101d19030304290300c000007030b4080303c0c405e4001e40f40e0080f50000e4003240321000040e54504031117503ca0100500b40a20604403070320b540c19040100010300c0020086041841504100390543c8010b00000e940300b212060689403400d030303910350011030b5004002c120300360b40c845c840b100c02030100703501424601c100c0d000d10640e203c6560280d480503d40281e441a40b07503c416017a079200a9005d0010805541c4400c00002c005c4400c40e180342d08071001400214038100180a2407503030a0003d0f08132810803912110001c20709600400080c058841c8182c1000314125101000c500d40b0b0098850180034005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 727824091 1250 727822841 727822847
    0x71a04030f0809031e0a021f0c03030b0406151e05040f03020d1b090606181d1e0a0207060b0f01050a03020a0c0b04030c0c14011409040902040903030516080402280e0f07 74
    0x5032324103540720f80e41c0d01c0e400381d06600942e8070050341e0352500d40010040310920006005003d290030424a2610f00300400340b04030380080c0000c2c0c101803a4680c0048915480d101100c4510860141c0c10312000348c59800c1005040ca55a40303030310184182c2802d40000c2400015250000e5554045080303d07464000410010b50003410804020010b140e4490000b414001c94451180f0400c091541e1039210703000145041c1c9280d54000900e048041303013401103041c084c11550203134000000c00ea0b042c0f4905000c507586c0740303070042c3c4106400f64180c690606000360300070203070005d4200200805c148944590390100054450000034449d6210b030311410f01c0d00f006d900f40b80b03020050541022043e0100780d0001481c41ea00a584c0c182c1d41200ba00c03205641f94000004076000d002401030084d00070b8140744a00d010140c050704035a10444096042c05c0c0020a042002c0300c14040940b0040d400024804114402c80000c541ca00c104a002c0b00c2c6507424927035180c5021b92500c10448000c1054800e41062090b4154 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 727825341 1250 727824091 727824109
    0xc0909020a4509060605070c03020d0203030d0504080909130b010501081017100c08010f030f060e160501030e010b0d061a0a0605090a050d08090111100c02071a04030f0809031e0a02 79
    0x80c2500d002410300c000346d5230b45020440e184c00701070710401d40079250070110760f0704004a07840110002c07007d1050b4141450150206c0c0c10500f15076210300c0050b030003d107e40742d042e84002400c80d0065104401a403034a8010369960071701414052003209050300c0400c841d01c1c202c024a124001c040020080d401200034001d04403000e12078804200a209401003107046002d05208064a8210007d07001084044c9011001010380100081450007445299511041c1c00340c680001c131502a2010701104030a051224201c6005400d52a408221800300c0b1020601c1c035480011651b010402030502000140000703242c0038020b500580c00114005554829402c0c4010001c0041c601681c03420480102652205140e0140b50b01c000d0401402c21440000d044041065200010745840100425501d00c040291a12201e0203094420008040102c02d101003600c12903040300c0d0007925003030b00a03c00b80ea95400c55440341040590510880c1207842180340041c0710380b000e101598000700b445401a106101c5041 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 727826591 1250 727825341 727825349
    0xd0804081006030b150402090d1b0b0f16061404050607110313030f02041512030311092103040518190501050f0f0103060314010c0909020a450906 64
    0x1030801c001000080c4d80100c42c19005000d48080403060001000468001d015040e003003a03014000c1010701c0103015244c0259007a6a0010b42002c0c035264649032615894410945103402488081100703180c0000303080c64030448a4032480000c2100341c41c50310360b61002c08081d00c080d81c61790400701c28405015080103c040542d0000d40145040000c100010b1510070018400906403904505035102190f590b5800000f00510007180741c9001c0e5143e05410511a006c070360b04801182c94990340d081010801801c0e02c00007400100724452411000201d825460544500c0c90076910081c0408611995210719078010b000d0092003100161402d80b40786ea4602c0c401100c4980302c14504401030007036468000031500e0800082e91049010050300e03004030002c000f2907101500e410243c0030b08519841c0190002c4114400e180e07500340256460384a0402203100782c0500101144041d10709004502c00c8400840032418800e000c10070800e00101d0010040c0e9410310b415040141e456000c1c011680383e442044094 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 727827841 1250 727826591 727826623
    0xb190903050601051c05010911030c091b07020d05011a28060e030304080f030304030e0a0b0412060615030c02060702070f09180f0303050609060d0803240d080408 71
    0x51441e203400c1d4840314180079850285030140d00c0700054401c00c1810800c42c17540b00b0f00800c000c400e281403217803050002070b681d41d2103030160090442c040d1911052290069030a41c450300440c282e041c2e142031003a8400c100484c1c118104244001c0410400e20443ca203110801400c40220302c450810013803c0e042900710448600b4420001c0c05409194843c00400d0390740741c2c108480107025150000e0720758001d60784105094800e007040031480800100c09580180d119864120b40420f10b04100641c2d600c080c0100ea08940d010300c001c022500d060751160070410700030080064996210910030717a888103035480c0100400e0b12a624100c0300c51303040050650001d120302c058211b031400c054a0070f00341c00280c850346140341c0c0c0f03c60f80480c13042451000428410b5010600900d0203840e440d021300506000c07918284901c0e040d2001524600b0445101034019901c031710003520350350751a003421144074002901c500d11449440900c8280e51a0b00424184241c000c02e60a91920b14001c009880c1011031440580a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 727829091 1250 727827841 727827857
    0x8270108281d1e120703030504060605040e0f07090e030f07021c0323190c031e02100b06090f010813020a1202010813020102210903070b19 61
    0x32640c4001c1841181c0d261110244010200078090711001d4460800880d4019941c042ca48110640010350180c0d915601501405100410481c441e00e030301c03a2000580c81c3c000c0400007200028030a52280d42d10501c52140000e90716180c00c04141141c10394030000344d0991100b100d58007003040c1080103c000b030100700c43c10301200c1c0701104201d440e40100512101d03941d0001c601f04085613a5031081102e211546460200403410a0074000c10b1840b01c3c503003104500d104003580072501d406000071a60140b0304d00300c0e1803001059600044940944807001603040040c4040001c400312180410201c8002e400d0f80201840d0031509520421100e81c2c1c07201d030b481100c0401803055503440d021480071011200b402c0c04032250380c0300c51a080d021410340400a500548014000c11861500c10122a40704d0003a40d481400c2e64500da60707403d0899240300c1c06409640982c0c01e00300b00e941c1c0039409010030f1400100e920304042d011000f0a2906a26400080c0103500102e03441000c2e101c030900320010100e9525100c14 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 727830341 1250 727829091 727829101
    0x912030721050f060f030a0c060f050d020f041e0308040317070501050109020901090f033903061d0105130206030604020c0a0507051018090203100312020a0209130519030c08270108 79
    0x31a8144507010610182b0b1107010360103406101990080e54650b4070640d690500c000721000c442d8458020340040d82026001c84d0380b5070b540002690705885c1d114440318500350850f2101c05001207001080c1c840d4100c2080004002502806411300030003c0300c50140e120071131040050040c011035001002c8407e41e0581c100301007604024041c412888503461040c0e2004680d600b04020724006450082950b022000001003110396407296442082400c5110351000700700a05038247c400c143c5400229180c910480d030003510b003040056400042c0100014030709032554000a08021840e0410764a07500400d1080195082c02084e0b80102c221614042d43e00a254004541045016001e140c064941c0032000980250703180080002454121024070715007407500b24025903500c0c40740c5089000f0f031491000321320b4204c403501c40a40c505500c040030b880400e001e401a0319043c1c1482d0826030402c5041e42011004c0b5070701100400080d0f550042003203011409011524024000348195070401c0b0703049013045 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 727831591 1250 727830341 727830353
    0x40f06120606032d06050a060806070206041a2401021c05071103012007020103060506190f030c020a060506032401170a0f1103071701020c01050912030721050f060f030a 74
    0x44c0d015901410015007078030b138640c001000f41150381000c5c14610400003880401d54001070502e02c620320030000c41ca0680c002c00c0840d000080180c920400f141c050b1100c480d84200500b054941c6880c06104a40240080c50720b8400070255050074240031402c002905818850480c8402d41050301c150001d000c40510b1303001000c3e580180112209000e80301140d040300f16842504030f44014000141140e40b124854101d040055050390000804111800141070040f800b0b03001e080d456a00c00c1d00030b80341d411102d03202c0c1c2005d4030009040302d07450300540c280700c0106031a0865070781180d08014030200300f5604004030500f0621510584604603400882c0d0440000d614084035211581d00000c4078544184d079101081c903000351500301d4900c002d811400f48803109815030145c17241c0b0501745c0080c40700c0c0e1070340401c9a40302c01480c8422080d046080000849150288190414282d201c4819019450721804108129402078076844001d91544051058601e44447d50741c0f9403100450280600180c2c1e55580 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 727832841 1250 727831591 727831673
    0x406031106030a06091a10020d08070513050a09020a02100510120201020118210503061e13020a0e040b010e030703030e210a050f0a050705040f0612060603 68
    0x124814440040068841103c0ea0400782c000c2109a4052207510101700a0f0700410045541a03030181b40380700c1360500490310006a1030041100e6407124510703511030b58400c880e00d03484204a6034003074120401c00a82d64a54440d070b40020000c038140180c55104105000382001c48040300c2c90b643d14140418002c000f4003282e001c000311403800c43c4669103029035200503800f44c0080316a8003841d00450001c5130502400151078884410700e00c1c508416901c1450058403140001d6800c40e811036070a941c482c28804100320106400440108404400c00b640701c0307000c3c142c2c0d1089110100003030303100ca81e0170741904140c007420b5480300d400d003000005298081c000c00da43c0c18085c4000b6040282040307101000d9126644482d849191010342481c104804054a554482c0b60900480da18441c9c1c10070320182000101c2d4020209a01101403d240f920380740c03c107c0500200403101c05501c1c0e803144005510120140071061719489000041807803882e500b0410312140820306100400300e00b640706400302d044074200c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 727834091 1250 727832841 727832873
    0x201150e1504180b0105030616050d020a0e030a082503120939060f092907030f030b062d070501090804090b0f01081614040b0711040603 60
    0x1541c150041d80014000e46000210f80724644480000303507003404500b450303c50603180c06904840071034440c0c0700c0001c440d920030b00310400015820301c44560180c1c5e441d001080142518070780b0198a42d00f000c0007070b0514001c504100e619520004140d00d000c4540728420030f01403148140c000e200165601d000d0842c0c0034000e1142030166071500241c0c20411556400c0c03080b4201071030030090150452016503c800d0035103281910115203104001051441488039844184090395504410340c6401c010f8031102ea5018200d0602400c0a210070502c1507000000d0200e03117010341d68511511498040160846038480040ea01840c070030410b24604480c45002007405404001643c0098100444010101d0099440003422035003410406014400068050400d1345d1001c6002c004c8400784108000b15000e03070098542c08180380400041d01030545a40c503080ba80194107100b16410200c010b0b000e2a580242c11800c8181000318051003804084130280d4140c5409075020880d450940d160706580d4410844 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 727835341 1250 727834091 727834111
    0x506150304030305071413080f06060a0e04030201111207030b0d03140904020d18020112090b0f06061c0c0905040e120a051c0501030611120703050a02130e070201150e 73
    0x101080c200e80c403c002c6d10188403001030f180e0b41c0f00c00900308444002c1c517440c455001d907840f4100d043d40d02c0d0140400c605000d503000411a040c480d1420754040c00001c03000b0000e8085d55a1070a444042001340b8004022000c00d0318090100707480c003050060200c0d4402900980140b01688a54000a802207400300d00c90b80742c10302d079944540545000801a11542e00c021405900b041d030100c1c94801450b4082818500c01d0b00c40110040802c40c0c80da04075448002d000d00044c04810104403204c1d42da062854111001a00362440c1c40c08401d811800603515428400d0b601e03507540403968010b54001c094401034038080b2410300c5903545000d000d541c2c0310f08141c50b9903169000001c4810005004404840c15911000400c2c0d40000e01404910000c010034481542e140307080c2081c0441040384e05c0122000b0b41c98440d1188601e840f81d01c0200d0080100034050701160307900b040103103520940c503c1d061008000b080c607500030318a4003440003420340c0c942c1c003028040e26000080521a28540c7c2c0d100503031051400c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 727836591 1250 727835341 727835351
    0x1902010506030d12110408030327150c090418020a0605070807143d230a020c010e0109051203100605030c0706060803190f1710031a070305061503040303 67
    0x5018400209000031100705400c03170003d80000e03102004400745104001e03400200000c107900c6641c240c4082444424021503030003d94261b030000c07203100710013600400c16594103414800c4820100d42100c85d41000c001221a01d86600011894102d0b0f0034406004540381c510f003008a10f83c0d4200d000d020b141c078002d00700d22074400401a0070b542085052003403a10842085141a00115050700f02070000d07400d244d41c503498508100c58070025010300c6102e1200014100c2444202d1303030002d10345070009042d148840e41c08101c990607601c400d0142c4003141c085c034030000034001d0282c40d24600d40b61001c0301d00d409041d001c1c070402c4507010401340c0c01c1c01102c1311414101d98079620f0402c00d1096119170b040c02400d4600d0702d480030640b403400001400815059070207201c0c407030505030380540d202d810441c01c960000318003070004140c0c04940f140440d00308451510a140c19034403075413260340c0c402541408140654040003040841035140c010f09400c80d0099940e166880e0001865402e01e100003400501413640325 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 727837841 1250 727836591 727836617
    0x406140609030c0405040f050610060804151506020304140d050c01230711130527013e0406080f15030d08101403060a0b060c121902010506030d 63
    0x1802000e20350f50b00200104030a18041c640030441e00c0c40850141c80d180300d5500069036014003603d102c01641e0581e02c07941000c5c0e03940d0f6207040c074410b0300c8105c000360701d07407a0081144507084032007865002c1c4c00581c01950300d070313030a04845402401d031111031588101c800300a208046800800c000a15030300070f00e800101075801d403e03809191500202c9006542800003040d100740040e140403a400075000302c0d0552450f10790001c403202541c2d01910864000f0010b07070a01c1003500103d20450001000180c000f15400c90110590011940d44458512400243c0501003140641c044511841d031412500070b83d042c541841001044124000c008080c6014680081010301c0b03101c0900001851000341281d213543e0140000078090481035442490040000c20f01090854848100044015010340100320039a54001c1c444007909250802c01e80003c010401000c2c0d0032028407941d4122101c80d10003a984c3c140b581c0c45165100b4094401400316450304007441400e80e0081003c1c11400200d1814030085848 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 727839091 1250 727837841 727837843
    0xc0a03140a08071101080115120b0d0f08040f05010507081210120c230f0d03110d050306010923090a06080d020c040f0507051209030d0f020c0c040614060903 69
    0x344100140c560301c804580d403001c04c000703910b0003410404280e03194403069070b880d00e103901040c81000040002c220507001e07400d42040c0940c0001d003620002040c55485200f242c403001c1b0040d002000644a04030009410311403145807038007400007031101b843d02519104294540a43c2801020404601d420381203000c1181c2d01c85182c55200648000c445280002103149006041022036105040c402440b5a034101c0103109115415416030714082c0c60300040d900c039042081000d8690900881c1400609254003003015010081070008511316250385580b81840d07030000d050503283e42d001c0d2000301e1038030700b01404155480c07840010740041a1088116625400b402401030030350703900485040e214000000c40d0855000652003210501690f08205030028104218140c400c00c0301d106020510030001403020811000c0441e13803102c020420380f41010b065480c500d00340c981402c0c01e07100c91030700440c4000c040d240c240f291a4800d5001c64040107118980701c5044141500b130741c402481101d010075581d0194034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 727840341 1250 727839091 727839103
    0xf09010e04020a02030c0106061d041806060e01060e0a0612020a091806170303010609050d051014091506030706030c021c080103171c0203060301090c0305100e0c0a0314 74
    0x8001c006540342c40f090b4400964940109000b8070f003a44c00c24200145041c000c22102c050700515120a40f003507202002880041c000f0080c1d081c03c4403500980f0100400c0da9445900054071946400e10301c50b51618000a1244501408180c41482141c41c02c01520360005800c240c45803140c1400350b2507016003402950200003d0740316405140c400f07006030100d91901d50201054600300700c612100c0ba01884984c550b07034003090080001081600c0d01c14442c600d00305c0c03101601c0b140700780219080701644018080583c1d0100811080700d1505105010320a5030910004d40f6003500d052003250140703020741c0007944d00e00d4070b4452442803603070764184217500030b1007440030702558080f1003144030b004034100c1402400700b41d091205031110718042090301d02101b8040219401c4000401c00306218140d55000314000350b01c041c046e1541507503070705921000500019420002180500083c0800b15088178400090340c006052610141c0c001001000c244d684204548040d43d0300690140401d42e00341e00d5180c9010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 727841591 1250 727840341 727840367
    0xc02011412010806061302040e01090203062101060905090a0f0209130b0c25030206010b0d0e1005090d170c0a02010b091503012304121b03180501050406050f0901 71
    0xc4601e0001003050074002491030b008040590318503682e0b8074609011412402240103c070f036195803440c010071180040740c0185812401c010300b0341445601d0212080b01800c40302c05415000e075140d440c10060503a1501c141a0f21151120241c810004141d90f1b007500b4040d1040002d00c10325011000c52503040000f0344100322650301051001007400c041288603082e400ca0000084644041a0300c181350b4a42800d40c80c1b0340c2075050b001800c0c20f07400c0c00081c0300290407003051085140c1c1c2c2c410b9240540001004003400c4484008000201420201c120320300b040d00da40d20b1001803002034a881c05030902202410343d400038091802c0c0303481d0400f0b060202d000d80440e01e40307664840c804a00b40111f50034401c0c01801406000c81c000c004220965500d0902402c42a20210300540381c0c0c00000c0207d01c0004030200c0000441c1380000081c000e80c1040b103a10f00884a090340016031032110b40106100300010740001d0300d02403d00328101440c08000801602c1900410000600003064801c09a401a00401028 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 727842841 1250 727841591 727841617
    0x10302091b0f04030c030c0b130b03060d020a060e211207080d0c090f0602060709060507060e03160204050f150111011103010b0a180b31120302100c0c020114 69
    0x1a50381c03400c0c00c0c10079032031700c0c0810b581c03c02c0910400142841303040b0071a503202140410030314056140460520054000a040c16041022a401ca07001603850012a802600703c41c1c5030802c0003484403060204c2c491200c0410841412820b1000d480403000145a100351741c42ea500040d5036900a140007141c07402080320002106040815842405400c064a034007070300c900c411200720f2550760700400c907076400040e2344c00804988144414041035110350010a8160301800c80401c100710b0b1011450700d142d10420003501242d081c0c80000f41140340502402d40c2005c03c07016001c0daa4145145140000c0c280d4649040c107224088100d1030000c8401c1d08000107010840321880d440e903941d1504110b140c1e016143c0c0034009175080e2030301107129800400020694403040042400c10480d0030040201d411030030f04402d24409100640c4042a0f05444180042c061440c00c0c40c1c110800e600c0c001c1d2604110a050360039250030211601c1640358480400810b107902464203011081269400030628400d4081032408 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 727844091 1250 727842841 727842847
    0x5130906060305010e0f0307020d021c12080a0605030303040803060405040c030b0903030a060501030c0c0209180109050d090b070f11040f150806090a050304090b042909010905010302091b0f 83
    0x500c403040d400124800407030010341d0b042162100c00c0b00c7d1688100b9000951164501c0d0b05100542058084500c120030410441d18450300309444d81c40e10001500c040c05d0004507600c040044000c15801070030700401055000b1819800c09a8030403220b40030041c001b6005a607039038001000d110192915000a681140390000b0340d092100005489900031599100c100381090800a2170354403d210303c802d8000166258007003041940e080140c1080080c1c226003442000102108401ca0203124082e1241d120758000c001c010014180a00510050f5100c0144603100307105c0200402e440d5420001c016622910003102103003000e000500038051b20034400046850102c2501c0710203070050018042c4e80521040b21200e40d00c0e07402017562243d1401c00103107a40c10500c010030070461150800710b40040d0080005c901204185981101820340f02002800d00d038034044902503900740404007034054069001c0c11300c015030458020412150019081c20600c021511039450210a804250341e010410010b41a507 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 727845341 1250 727844091 727844093
    0x207020a0609031a0c0703030902270a11090d080f120c03060f1e04200a020a140a030f0c061104141305100621111c06060504051309060603 61
    0x1c042d042c2d501003282c0240b1900030705075110710701140f954441e00064120300c0c41c00b466035504402030b01007c80102e030006001c280101c800503ca00c0c10548003605900800ca60345803402e03040c426110149600c2d41011000c1100c1241c64540b400a40116a044409a5a50780c011440104c640c030602c44805070400c0c03010107100d40607400030021406003408448080c0c0111205041000300c45e40d0704100f2005891100106032141403035082800c640c04442681154120b10700e480034104c1c1e10901880d80160020040c4070200203423001e03c03040d4280064000c00d00901e85a4006d17000842e184900c109200f80c80796150300f00300498002c031030704041c1501c1c616151035445220000081c60180402c1c414075035038000d07102095440c810244120082d4855040c202d1900c3c0c1e00742c0b1400850580704c00300301d5400d20f0315044034500703000b01c0c14842081d440c8070780c0e1f035603800142d105d132910050000244982042e10803c04550301c4000c1d6015600d00710380d03003105500d810191740024050800000c003111b0810b03030004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 727846591 1250 727845341 727845347
    0x108071a070503130302010e03060c0a11070f060c02010224040b04140709060801060603090f06020f0708070809010f0f120b030f1009020315190c051b06010512030406051605010207020a06 82
    0xc4d08980c400c0c0c8400700955030020805841d0201166094401102448040f0140d403242410b0020000c0700c0003914019034540340c0300049c0c0e083c250040c40204581101040c21941c0c104500d2040f0508401c4807140240198144404c0c000050009084131562601090900c440707011080c492514600c21540c820782d60307403402e10240c0458441d50301c1c43c0d46001400901c1c18060700400c040c241d07000109001c054a550b0714500250003001d48002110303828000c1100094002c801001c803e806542250b0712040c414000508400d0015281c60030022200c0d41700342401e8100a00c0082416181004600740c000040424039094054000e00c0304c41c89860303258103109070707281e0100a41c14002e500343d40009454a00341c0082101c141d40080c0e0320044207030344090040c003d81c00f804000745180382c903524003c2a0f211010445010b20408061500500010017092600f020401c0000c035201001d5420503240c00d03c050454050f5141d0386030100b03079807130300d40c401c100081d4103c0b41191b50042025980c41e0320340c1001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 727847841 1250 727846591 727846627
    0x2b020f031c080c04050a0b0a0e060a0509150c1b150d02030a060b070c06050a230c010c0e010203120910150e010902040e0402010509240d140108071a070503 68
    0x708000c9164031001c82c100e16002c0d422507042d100c000c1c180102007460426008a0b41c1e20203580c07402002002c1801e0001030761218000c10401d0750603620151196289010070944950a0310405a10481009a82074201000c20442c403100300504004c000b400d40c1c00040744401140c80f01905c01103400080c0d50010466603800380d0701070103400c2030030094a134442c800b8068500c50b0850141013040101810820640728000034800505103103000822000008000880034140c860380c021440808645400925000d2180031151040d030b240c1720210180d4600084d444c0c0c42a40c00042500d4110700001d41e0407841044041c0040b0319483c02040030940c011010000321459000d00c007841d0000d04000200300c005402070ba41903030108003000040b61100d60040d600e56004200035500300c61f5804d03000000c010000304000307030010300740c3d8080e0742c0320104203100080300c039140980025028000014007003103c0020b400b0043c2c82081c0d146080101404000b00c04c00d00461900070018440018501c441000c04a48 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 727849091 1250 727847841 727847893
    0x13020c030d0b0a0303051c0b060d0f05061509062d030103050d0804080d022b0b1504030f020111030c100b0a0602061e1803030a06142b020f03 62
    0x410400b40d1802c4041098051244c40090f001401c207104031074501c6161120310210161100002904404040100c0c190744c2290102c1031034507075a424154000209400b0341d96201804807108c1c80400030045845107640203c040d403601421011841040c0b00039524118103032041d9100c44600b144400403c46400381c3e02c240421201800b524840a00e500d014881890050354070903000b9040906181c8030600a41201c1000b0202d09d00300e0490b00325801640801803c0d01d50048004034039501240140b00c0c0b0300721010080c03c510301e0104020000702d95410b044514603942403030920480c4d4841d20b5018914010004910300d50f003c2c0ca00c1c2d40f40030782c01943c0441c1d8140c805413070104150740d0710300099807074010403a12000b0364001f04807508603000211151a50051b01038000f0301c641e190301e1016514540040f645111980e0395070b50b050203200200c0d000342055140c1100c1180300c42c4516602410325820003405260812185580b030000c40d03aa095022515007400303000c541c1c030b200d009503c1142640035020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 727850341 1250 727849091 727849117
    0x6030c03042f090402010c0b070909060b070203120a03290126070c0206040f060305060306090c0a1a12040807030e0a0f0e0a0e07080a12020307030e0f13020c03 70
    0x16044600a02c078071070002505050711110034101c503118041c0f09400c0c1000300200c0c1080b8500c082d0a00055507206801c0c020030b2650340b4140013a05000c640401c450b0b007500500c0410b0b009024420040e40c2c00504058450110307034290391100b0324020290090007401000c41006080f0030354003010081e07102400b110b040b03801d03a0380401581e6130782041c407100252072100b940d07241c5810380010a203038001d41d0001c0500d440904801d11f010355170001406d00c0a0141c01c4280002c1d240c20500c00d081c64100102038000c82803c000c2c088a02e41140040c02074520f500c10304c074064580c008080400f961540076242d01000305070400f034203480c1034503101c042503104134000c8020400301103001040d41800150403040d120816502641da40c2030070300e000c1200700b0042203404801c0c2c40e0792180301485070521801000f0000403000301525940c0345024a00040b080d00c1810865000703002c01c20100b68408600c134030302841a2400040280807201054518080e112541d08190000070346030703503c6600100420b040b800c124 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 727851591 1250 727850341 727850363
    0x62304170d050f0d090f1202030901021c081801060b0a0f031415040b1504030606180504030f0c0303020c120a0314091c200706090b03090d050a030b06030c0304 70
    0x1c400e507458003070504600030202040c01400c1650300541d2044948901402d00000b8161103030707403401103100c4101a0b0b200140c00208080308103580400865031a008648042d040580d0714440003845130b10002c01c01e00100305c0c12614051031540a501c942d01030b08a041d142a9140300012010308007a00341e40703064001030726002c00b8107240030804c5070f098000d1080d941032407410f0b04a6820000030785500865254001b190400402198200800030001107105a1010580c10320340145c40e00c221028000b081e0391681001c040100190b841480280300c0ca40b1410081c40f02080750030214024001c00d440100c86104446640224a5801c0b0103407465086590317042c00500380b1114098405034046d00c40c0812984001c9800e00003002045011611000600e054015240b80224400f012224100950315a400010302480100d50083c020400303803241a026910718103200d1049079a94044110101c00c06c0400300c1c04541c054070a820440b000c00004212607107074101840b00c00c180b9802910100d0b5002019 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 727852841 1250 727851591 727851613
    0xc05010507020a0b0f1312060b150a0309030e12100605060403030206040f0305070506040c0302030105070e1e1302041403010e0f060103060b0411070305070b09061006230417 76
    0x21401c540880c0e6010b01501030561504031114800e4104224070300c55890305000f8010500400d031140001007448014891010381c4906000049070b8429540c0c81c000d107051030f82641103158010031a40419214034000071002406d00f02101c0902c14a500281c0c000c001c1c0d502108045070024526a00848051041140994503410080302e80726511000b400b68005c480001d002c112020b2144513180d01a0400918040583c1c0e6014100a0201e5084036150702210082c0291b003400d2017601ea00403658103051a1020042001400700145030708090380e00139944031803100a4545040740000c0b8640340d9415501c417510769a01400e5542001c10560281d80f03041e0403103c0e40007000401c1d441c03403500c0002409080e42107887c0c40d005407106809864015032250191021184408024103900e07000fa5203c41d21203441d403401e000b0005002d416541503910003824020304a8100080204a40c4035080039000001d8401c150144070030fa03280190b681c0b0b8408900010480f000ca000c50101030610000d0700c03100a48 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 727854091 1250 727852841 727852847
    0x1c09020a06020609120f071e06060b041d070e102015010b0a02030405030615180105060d0207140604120f0201050f060d0213380d0b100b04080105040c0501 68
    0x40714507406039817003c04100c085640d040003c2c0302c86010000303203d141c4400c50701c84858004400d013a0701118a1401d03060401d0111a00c6400702410510305c405203441d01c2c090b2485140140045540300c0d054101000c280c000b1300a600700a074000000e0200c0692400451000d81080c0f03072403400d40a40c41039140d010500ca20041a8210307010404125a0f456908110329140f00b604400c000700150b03c020032000c500c030359080000c07a01c148a4008207180c2004407005000303520001e03483c1108a1109080140825500c15081d04e00c03c0421500058a0710302c142808042044042c0740494030780036000610040c0b090010b981a2244038503111941001708156049080343c008669441019038918046180303482d091091020071030009111403011911404c5510485001c0040d640c1042c080e200303000810825000d0f20f481940d90549500348100d0100042240a02030000060510020380009007403842052051300180282c0340c41140c45035203500c1543d0007030a003079034140d40030b07540e10100040d01e601c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 727855341 1250 727854091 727854103
    0x2a0129060711010908160504181a06010c02060c0c010f110a0f1403031305011a01090b03100b27120d0c0c050301020c070e090a20061c09020a0602 64
    0x180604038038506001a15240e05031000c44105504200054800140308403042081c1c048507a0410041e2902c51300d441c0030003003240d0b41070b8040035400008044030408120274034a00103034a086c40801c0c1e80280e59890040300c3c04244c9140c0203500081c041404552510700181c82e200f40002a02e9004185104060070744030f5601c003580103d403e500031a43c800015902e0050030b1042849901d02149265640041d10b0541c1c00484030f114414030f081820006021003401071001c01403254034092591011000001d02d06409401500c1190f90008007003081c0c081c04840d0303400103001942c1d415440c0e031100145804060f11400141d00681c04540544486180900c140e191300c0100c4002044a007060020a45680344002019120411442c0d800102c50b2401c4c001044140d20020140c04040d051200100c60090042c1200019038054410107001a0500d4920050002c681814003010502c000c0020800c0c0f0804120442c421090308400c00030301f001e5001842000c0c0b088484c5090183c03904401c9a441c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 727856591 1250 727855341 727855421
    0x190503040515130627120e011e0c080d24090b1f1206060903020301110309030f18031f1b0503061201090b0403080709150909022a01 58
    0x803144003643c000201540e003c2c4411500b08100042c01c94403005c200c00032055034403010780e1403241c038841042000c0c0d404181d2121005090a0001005070021954105000d80c041e40b8420701660500344403c0c0700c0d88005640c01801415400e00c100c04080f03420301d01c001d404007100108a2a0803202090440c468020341c2d03001a40a058002070409108180481c0b040340207809040c4030f8507103070079a4404445d0044602070582d64075034800c1c440c91841410700316281e000714908102c3c014402c0c8200b2840100c225040b15580c4080c080d268900080d0b1400f04e0280da0559585c107101c0c43e108101d801c5e480c140e8030200c000ca81c05042041c40380ca49d003c85080b03401d11a480c80042d100304001450782c580b8104040131140c070140005802d004542d078050004900341c4064010404e40c0040008055121070500c2c003810751541001c600d00c030700b81805860f0b010039018041180790041888000002c0d940c1c141d891114410407001c500c1030310f04404034000c0c020b04000300041c0e50301d1050001c1c03105285031141410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 727857841 1250 727856591 727856611
    0xf1502060606090418050318190b07020307080303010f0311010f02061f0509040501090c0815190f020d0609050610090b0a0201020c060901050a060509190b010302190503040515 77
    0x1540c0d403a410404240d03c08101c10713600c42d558010b2002c0c5540300d001100c0758075110381d004542d500345d100b001211000b0680c254912803114204800e00500312002d80d4030403184900300c00d40d103c0d1041d10001f400e0105642110b1054400840005000c0c07a04c40021000c50b40203a0110310b18002710307001110103412542005d800340c0d001402160b052062144c08440d1003108011078180c0c50345820000701c5050099505aa0396034642885505008e0403405034001030890f1401440340d15060031100a6445000b840c0e080382000303a8007007040700740440e004054484130034502150386441c1603c200b0001c061a0280610701741c940000182682003a66003540c40c505981c4403402e800385805050007807640700030100000c55400340300200c40340d2401c2240c04d01402c0c483e8008101d928100c030448080321000c1d0b00280c4960f49440a020900303030200c1040404122030000481c0c00540140103a010348610501151031580160328241425449409140258803800c1030303400320755441220590802c026502c0d5031030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 727859091 1250 727857841 727857853
    0x5130b0916092a02011508010510050d0203100510090c0c0528081606020417060a02070803060d020411040605070312020a02072102060d0203073903020a0611040f1502 73
    0xe48030f070b60300c444a400c2c8441d200206000c4000c45840d850204507501c00b000e140e4442091050340824010300c14044c1c030094521841d2002c0a070002503981c50038000e055041383d03480300481c40e43d60111600ba405800e00c1c4105010000c4080c50080100325080360948040c020200300101c17046141c1d1240b0ba404104494000c3c10740340581755513040e5400f940c1c14085482c4031681750310000e20640050001020281e24544000d030003112042d0802d800100f1a4801d14810410040000c4418007520303000481510010f050540c42d04c04200102100d01d0118a03564010078005030455000d001043c0540c4641d0316902d000f0000054038081c0d00032480c9810140c3c20120080c45022035210284010402207541c40c100a4840d4001c15055481204108c3c0410b070000108284540c000d114461003d240583c00032421191058021045500340c041403441c1c0d0491003030105061081000b80c1800d50811000c02802c00002921011940103100b1500103565400001501006041c0d080ea1002030b15006404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 727860341 1250 727859091 727859141
    0xc010c0507050f0d0605100f140303040924081e0a05060105090c0d02040306020a1d0a0b0a021f020d110307080109020a1e020d0e04060308040905130b091609 69
    0x403c2400200003107410903000844840420b240d0b0081c3c60281c8140406124805d04040d600c560440b21a001041243c8010b042d0311015180001140e046881c51500001c100c1500c0302c07882c00010200d60030783c010801821000c108090080b1b41ca503c511030802604c000c0b001c0c054a0980c5a2204290141041d0001e0004110381d050010507264400700c9a111203280408104541c002c80e00180c2040d42d186c2d0b070101e510000c258101c42c0d084141580d401c50000b0054013040014940f44050158465002011484071060381c002c02095000301303a0b81040141c5501d403804044000c1d040081070055441c2481020001040e580088038050301c41641d0b242c1d00da83c205000750f4003a41c442d00b405010006d00c698041e03a18480d10300c014801c0d822903030280c000a14895002411607440d8a40c2a100740d01c6c1c003508000140071801100d007100c1d00c541022440d56034050841c0d0703900461020162402209508111501e04041a0b0507059118aa010000641c03210022412103101400740001038108500c040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 727861591 1250 727860341 727860349
    0xc021f0b012c0a080610060305092a04020f0d0506090f0a200409020a030507020c1c0f0b040c080613080702010e12030c030c1014130f081b0c010c050705 67
    0x9180b00c078032005441d01d0040042c0420690420f9a00c804400e41110003030201c011059202e0301e00801c1d5a10b010311142c1085500c954071211400e040b015004990414030030b0300503400c3e4002a20140040c01151207155a000441c13055210601c05130215103000006041440c2c11000e850103a890034007406020365500d00e0410040c10220040752b5800d44031085048070950020091024001e44a000358803180c0404000c0d003540d4000d4000410b5410050300643c1d2511a040d0418060285000102410b2094103080641c0c4040d00e0003e803450010f00204001d100d000d40c10f035021102c25208540c51543e4800e0301e42100b8035904401801c080d01001054099031040140c2041c2c084000e0180010603001070010385154032910000a068201043c550b00728403051000600c000031410003400b81001e03000031001101c1c0c008068010b002c1d110340c045410301207095480c001003030740a6101d03503079040040c4402c900d0803101401110b00c1e1007003030941c5070294402e0b400d8441c040e9001d801411720a04000c104 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 727862841 1250 727861591 727861637
    0x40903021906020d18120221250302070305060a0506010804140c0904030210140907030b100b0403030305061003091a06040b040501120231150302040c021f0b01 70
    0x9440300368003440b0004c4103541c203105203910020f0403854501c859105160140700950b00c01c1d42c4a0554100010044001c1980e4024108400c00c1000300b0b5961490080031040241c0044804418062060003a0041540000c0c000301660f014500310b401907510084100280d603011a81103000a0000c40400c0004103250142514411001e080d588004070780300c04109074080448041d00181d00a5951964001540c41f0f52042d1043c0b2102441162800c085810780c2e4042503c0010028014400013403c4035206514402c0940241840305944540c1c9080c001d024100681d0b200384150b0026040c0c404890281c440c081800354080d0b500601c81c010238a00c0f900d4000b000b01490780143d20303504010400ea540307100300c5020380004c0c03c48112076074060041c481040858400d04881e60400b00f00780c001e010528242d1140b50003544000325811903403180840e000c0f5120b60000350020305100c2d03400c40b910780102c1c11101c0074081121141200d420400e2007001c0d1100d400140b800f0802c1c4068101503404020a4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 727864091 1250 727862841 727862843
    0x904020408190b1b09091302090f041e05190302120f040f05030d080a1a0904060c0e0a050604030f020604030c0b0316020102030f0105061c1505030c0409030219 70
    0x1420140c0c1e0300079060420000e0303402c880201c0c1d550960b8a0401a400342025080781c0f4821040311004c1d26800c0c01c0c0490710403100b6041c42401850001225509503800262000e603000d0841480c5040c01c0399110400c2400750381c200c074800c010762030b60300c0302d401705254100341704e03410800804a90103681002d040e14504484160110b000340e4844014100e407090081c459113262681c0c080d40c4038500500080c0d02c00441d00107500c60703044401111001d680c04041907401c400006000100c5502c0c404581001c48100b0f40100e070000c9803c0f00700000d0001c0c507880202c030295140ca4541008121074204032034800180030b030550018044c0001d001041e089000000294406030015240540300d84a902d12685a90b200703041a0100108018011100b80307035603261421a40000d500754188141c2144100d0014010700780152004581e412210b05011001148550141d80400001c8119180c0e900f040f01c160091341d00030321490441c514541030610804010f150142c0c09044646880d2a8000300e41e04a010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 727865341 1250 727864091 727864099
    0x10b040c1805180a0911030304140a0504060509010e0a02120f0711070e0c1305062209200702041508010e191203111b0709060504090b0411032a0307150203070809 71
    0x40c00d211b090700e00f00010b1001e4410003a1610003a12940100030080f400d6800090149051079810001134840d50410790544006581c00400d1380d5407481104000e00034144a6441c40e010002030051111403503c41394002d204694404801502030503040d81c3d0b88055100f50b9071602c841000003000c0c00c6082024103411084407210342c40c0d05070b035400000d0030b5420100e0200040b07000c0b00340441034415409240d000400032040b05004050341d1888640004207120320713a00e03032a00000742c401d04554444e40499a002e40a05000300c1d8151200c5180f0300070510000104014032880800d480350141000519004507840065011910030148003100a00b80c09800d11424180911800001c5100c00c000d0369a55100200188080303031601d1500400d443c4940d2040c1d00603854020b80401003a45200f078079910540090461300055196004240f030001038544d4107800c0080d28003110f4030564890390700c40d2144403ca040f5046a6109c001085c0070010704078030030015074000c01c4030070000b4400070007030310040100034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 727866591 1250 727865341 727865363
    0xb0907021002130e0f07031d07030609060b04020304050f06240415030c090203090d0903021305150307030803010e0a1416210203090709230405010b040c1805180a09 72
    0x4c0e0303030110700600b642c401c6141c910040800810720b82c148202070441800c00c030203030022280e81149079100e5a00d80000b5000350f860b43e1904052080a8100e42118070010b0801c55a070702c0d050401c682ca803800341c0904485802040301291014131809107072000303a03525000f0000219150010400107114244840c01020942640003000c0340074122001c00030300b01d540d0051394a28198500c14200b416804d40d15082c4405003800313001503141c1023503008110852903800616a03d8070791550103030851038400160b15118140b0301108100c42c15015504881c0c1d440941e080d6500c80a0882003518880b803280c40c2045c50080c002003100c0402110f2081c2c500c013504080d0200e04c0d81c0d44130405138070421201f0300040c98001080c05070301c100410101e0020441c40e40204900b00705003096211002d0313020342e5100802411004602403103000c3d801410010f8000f4000c000d030700219031014101c2c1d0400c0ca04125554055480000c841c1000b10900705603940080e61504199140e11390340c0e0041c1105e15056172850b04007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 727867841 1250 727866591 727866599
    0xe010603020409050f060606030c0a0f09050303041203090b0c0c01081e070819090507060302070501020f0c060f090706080a020c0f0a140129010f051303030c02040b090702100213 78
    0x1510030650144c0c01407010b8180d585110650314500b2401a01d05401401c2c100b0030041400400340a48200d2403107443c00c4641e4291900040f9000819908041e51500002400088084c1c4004140b0701c0c10344aa100c044290b41da46032071403018080c86502c00b01c7c0c0c1c0c100c0c030107a03901588594801c3d82d105d61402074071201141401404801208100d45044c040754000e0148500840e60039856542c29030044030a10804e0155a25030303071201407a218201c145600400c101c0c0030402c003901030300d824501000c0700540340c6403c0700b07543da519078003640e80004002100c0c001c51222400403407664113595083d00c5485e1103450f2071a000c3c0095101d80344240c0715000348514401d20784d42c140b00f0601001e0040c0b085209000d01c61988500b1200350b040c5030101000b17104009440444c1da8640181010002d00f0a6881005800310545680c892106505011f04e0f01340780110405402c101241c44850007501c0401c2038590341c0c0144103000c031054079040050303403140c890341071291959001068200741906003070005540d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 727869091 1250 727867841 727867849
    0x51006080603150a1409010203060102070302041508030c030d061e0e0403050705010c09140d0512030a230109142403240a0c020d120c02011e0b0f04050c09040e01060302 74
    0x64903550700711900ca0b00c11108145c90003420503000800718000310310b18108500083e507a00302d00c0c840280070311380341ccd035100144404000d01c01004008410680740d072100540d401036102d5110400042d2154604800802c0c01010000c40181070031106020003032803810545100070648004008a08201041048000042d406c0c090f15900e41002c0d150900030030700303014004850900e02031105006035200440c6101090000540203404044085044d42d2030f20b80a2001c2c02404108040382034075044407002c0c42502180c002001d0403a010140b00304075101e9801c40f011003464064442400601c03180c1f040e0000020140c1c40c41101c0c620003804c407040c02440c0d00381d440c941d924102c0c9022031655210104004490680107035030b02c82c50b640c03004d02001008064054050002c0502075100c056648850940c443d000354006145003411030840c01007804035480140c0a020252500d030f002d903184078040303c0130f07003081d0081c0382c007079040d2800079400d01c2600c0c13040c803004004800305551030750348480d80000503840d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 727870341 1250 727869091 727869133
    0x50c0708031b130324020f07060203060d0c060c03081609140d0209090c1c031707091a210f3108040e010f060206040f05010e0d03020d060801051006080603 68
    0x2c031407150003d40c0c214607264902d176100b00404200c00d55004028105500816000701c40e025640180e00503101c1c0c40d42408a07004070f140603401005840c01c00d1010500b40c0c1c200800000d60761007556a1005551540080d03060303ea925500d03100404c00b00c104c107000014408a10f411034800c0603001400ca54a1a000210307100000d5851a48982084e0469152400d011807000b818040001c00c0300d80101d25540c00514002d07404840007010149031f0082802107210300e80341c500404d0385810700050070710242d02010181d801810310804000b4280d1300e800742612040500c030300c03a0f0422040c001542d902d4181c000c41c5916081790b4001e50700c940500c806014600d16a00c6604140201000c2c2d03180d03402d041c5110f10080c01a0007112400001060030001d45500061555005900c42080922141036240850140581c0103884900380240c0f4180d0310041d0749036010300b03860460440d007480802e54030b004003401c0301c10a0341c44e41500e200f408024800fa03400354400ca03801c608050200c0e8409440300149240c040c1d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 727871591 1250 727870341 727870343
    0x50a020904080d1a03030d2c010b0f040b030d053601020d020343030806090a0902030a0807050c060711040501051008040b04111201020706050c0708031b1303 69
    0x520003203510b00291102e1310907034458041c040040d01514a40100003560b9000d0411a5003803e501d030490079961f41c0020205443c2000481030051203a500e41c0b426502030400c10305a94040c10034105030a2840c0341a0007044000740340034000e03003e0319000c450115504c1d440000c4100684003200070111103a03401e03801d000075040c800c81ca005401102180021706049401c0d00010442d0b00500264621000d4544044045414011142c80040c41840f041c8a03004000b071104603c69103a800d1041413681150b01a0b00c280011640b08041d55135100071f4000b1100c444001a4069114205100000d001e1100901c165030141c011501c40c2034401c00007484030b600c1050700f11640c1003d200b42c84c14a042030302910b80903040807940d0003c0030300c00c010024203000000f04081c1036489482c0208042c0102210010780040016040184200038580f90b507000c4d50042008803645480c0000003010320129205403902a94408182480c0d40c8400e90a118112030b903500107808182c0401c41040301c1c20702c040d000c100071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 727872841 1250 727871591 727871603
    0x510030b04141f051b0f0a0503090a0c060e04050a0501231903080403050d0302030708060127060905090603190b1803070c14090601020d03090501150806010e07020d1209050a020904 79
    0xa103044001780c2420042e03004080c0e5900c50070b000902c078120810040d030f444d8036124500241c490f0342e6900c2c60741c80e1042c604c6018145882c0fa0001150031039100318850003a000542d410700494458203100011070704244140303540728aa40c140075090881c08946001e41a000400c000400010703100340310f20350026584129000c180002c0c04008000041c400e4100300906410b045046261245002c1c24422008003030604004001c00002d01c02560070044001032a0031601000c51641c80790401780c150513642c003400703114482400005455250010b05903800743c0701d510183c0d2001c521603072002c0e010400a0540c10124203102500f09550500b080900544d40c02140802c007058a4903107116203000084a01c01e001da11020200702070380e40c0010300c1c04405812483c00040401c01c60900500500040781d02c24010003014500040306000050841d059030802400c50080340c40d4084d042c4e0b69011003081410110740d0b642010b02201d82d0640c0500c3c4140d00810a8540c84001540000e820083c2264110b1306 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 727874091 1250 727872841 727872851
    0xc14010606140403110f12010e1f1109010e180a05040605130b01051e06160c08071d0604090f06090c060e130506040905150a0510030b04141f 62
    0x6001d510a0603012003003211407905290038156100e020040d043c0e13a2215000c0c10b1400800070850f107c00843c501001d4002000304080c1c0d000220300c0791034040500052001e1258021485000001c502c0713101031700d01009829601c2c2103403c10040d02c480c600c40d200d0702d6000f0390000321403800c0018041001c1c8945801340c8001524602413510008541003e003041030441c2d11288604002506072612a05460040b22501030b081c1c0054550413602c4c903074085103a0880340104466110b240e2851000251a206001c06004a51208201c03940e452080c07040403c00010300c80c1010a01c04a00a0541c00c10360281000c03030300580c0394984d216440354145040354042e07039445050781400341582c0000080c0c0804e20780750401c2c0030a41d00203180606d00381c82a4001c16550004580582e4959002405c0c840ccd02c60103451840442c1c041c0021704100499a2a10385030601e0700103114581c0810002c801d582e8001000403003a10780c2d455240305030144810007100740c810140700403981e0011802070851400d040b20007080d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 727875341 1250 727874091 727874099
    0xc040b210d170c0919170c0907140f130306020414040e071206052e0311010807090306051302060301090c031a03032205060301030b01090b030c030d0c030c140106 71
    0x50305184000d0000003054120a0090f1108650210ba040140c200c80c0c81e000b011090b0110600d08106922482c0040041c4804403040c071404680d0035500c0804480079115680d40c0c00b400d56103400d0200c6110071552042103c06840136520002d0040c1a02e9000140f1110381c41f0356402c41203a005400484010210000700170103864039000702401500034030081d02c02c5c02c1c80d003603d030740594010000040c02c1c503849800003804141100d000d040f04410032a4043e00001d819424404002c203140400d41b1464460314132080c246d405504100c0c010001661500e406a1a40d110300c00181006840c07881024801602000540c0d01c4802070f50103031000d003400050100d01c0c21005030849040d160030014580400d411a0040d98000c0296040800c2d0f561404600078000700403203034502c100350040c0750f00000100020090052140c01c00b4140c2e040c060003003200d0350f50b040c101680c9110a0080581c075620800440f44c11500c0350140204a074800d003020a25110f0a46c4d58a540c1c0b03400f020813000503907580c2e000304 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 727876591 1250 727875341 727875347
    0x30c0e0d122d09090b010c11010c0f020a06030b030f070f030b0720032d040e0c0403082d0c071a040801060b030708070c05030703050906091801031202010606020c040b210d 75
    0x82c50a40c0c003404c04440c03825159880801234180a600541440016034880e81444044d42408840c40d9005051010203511014040d00602c4402840e5000e07204102a0111000d00020300c00280c0d030310b0092030b03003550b03255a80d1030409540040055040005490803c8140a1040301e180f41070424400550348561a000103480800c0441404d40000680701350106601d1240108803010f580e101900345405542d00856504a0b100b5940004c1800800080211b0555030f000c0280584060001000440c14007401e01d4581c2809440d40100744c90b009500d08100e140d084496070f803024404214010b08141d0f035405e40c61700b1240164440d0100e240004200000340d64008107050b400242807c00c0c4144038040e80300c40307590b0700a0300c0c0c004043c401c0028540c0b140350303116410368030040c00080030f400c4540500c0c20004100a021b20049800038180810700110078010301483c41511925801400126426004c010127810140c80e0180c0003070b0781c074030700281c0c050a40c5854242c0490200040075660f006480c01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 727877697 1106 727876591 727876601
    0xf081303021c0c0614070e040b0102070b07050f071208041e05090a0b04050f090c090c0d020a020313050117040201180e07030c0e0d122d0909 62
    0x42c02140c0c1d0101000c1a0288118401d115021490000380392010054818030042181e07601c000c8000c0c01c00703600031900d48405204031586556100080741d61940403040640306a080709203141060401000604001c010a560490080c0c2d05a295440b25000c0d03030081c41d5484e2884443c0e02c5002d0311004624010303100003088c84005050a0746580c0040590314180c9004504000001c1c0c007a28030002914865094400075000c0c1046100070401054802864800b42690a00c80580203544500c054030b032842c0641c000f1179642100852005500395554003c904105c13141c070400b0980d01d080101a500542c0c2800c045491442100091504400503000f90001034080710809c140154181c0206000183c6038581703500320003084092201e42c4250100261001e02d280c81281e2000d813145111500c2548a80742c0c68201c280100103090301020740d5042d41d03002580008051110781460b00c62 = true := by decide +kernel

theorem cover : BRFrame.Cov 727697841 727877697 := by
  have h0 := BRFrame.cov_init 727697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 727697841 ≤ n) (h2 : n < 727877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
